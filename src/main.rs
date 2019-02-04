// main.rs

// *************************************************************************
// * Copyright (C) 2019 Daniel Mueller (deso@posteo.net)                   *
// *                                                                       *
// * This program is free software: you can redistribute it and/or modify  *
// * it under the terms of the GNU General Public License as published by  *
// * the Free Software Foundation, either version 3 of the License, or     *
// * (at your option) any later version.                                   *
// *                                                                       *
// * This program is distributed in the hope that it will be useful,       *
// * but WITHOUT ANY WARRANTY; without even the implied warranty of        *
// * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *
// * GNU General Public License for more details.                          *
// *                                                                       *
// * You should have received a copy of the GNU General Public License     *
// * along with this program.  If not, see <http://www.gnu.org/licenses/>. *
// *************************************************************************

#![deny(
  dead_code,
  illegal_floating_point_literal_pattern,
  improper_ctypes,
  intra_doc_link_resolution_failure,
  late_bound_lifetime_arguments,
  missing_copy_implementations,
  missing_debug_implementations,
  missing_docs,
  no_mangle_generic_items,
  non_shorthand_field_patterns,
  overflowing_literals,
  path_statements,
  patterns_in_fns_without_body,
  plugin_as_library,
  private_in_public,
  proc_macro_derive_resolution_fallback,
  safe_packed_borrows,
  stable_features,
  trivial_bounds,
  trivial_numeric_casts,
  type_alias_bounds,
  tyvar_behind_raw_pointer,
  unconditional_recursion,
  unions_with_drop_fields,
  unreachable_code,
  unreachable_patterns,
  unstable_features,
  unstable_name_collisions,
  unused,
  unused_comparisons,
  unused_import_braces,
  unused_lifetimes,
  unused_qualifications,
  unused_results,
  where_clauses_object_safety,
  while_true,
)]
#![warn(
  bad_style,
  future_incompatible,
  nonstandard_style,
  renamed_and_removed_lints,
  rust_2018_compatibility,
  rust_2018_idioms,
)]

//! `neovim-ctrl` is a program for finding and interacting with a Neovim
//! instance running in the current terminal.

use std::borrow::Cow;
use std::env::args_os;
use std::ffi::CString;
use std::ffi::OsStr;
use std::fs::DirEntry;
use std::fs::File;
use std::fs::read_dir;
use std::fs::read_link;
use std::io::BufRead;
use std::io::BufReader;
use std::io::Error as IoError;
use std::io::ErrorKind;
use std::io::Result as IoResult;
use std::io::stdout;
use std::io::Write;
use std::mem::uninitialized;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::ffi::OsStringExt;
use std::path::PathBuf;
use std::result::Result as StdResult;
use std::str::FromStr;

use libc::dev_t as Dev;
use libc::ENXIO;
use libc::ino64_t as Inode;
use libc::mode_t as Mode;
use libc::S_IFCHR;
use libc::S_IFMT;
use libc::S_IFSOCK;
use libc::stat64 as Stat64;
use libc::stat64;


/// The prefix of all Neovim binaries.
const NVIM: &str = "nvim";
/// The path to the /proc virtual file system.
const PROC: &str = "/proc";
/// The path to a file listing all UNIX domain sockets on the system.
const PROC_UNIX: &str = "/proc/net/unix";
/// The symlink to the entry for the current process in /proc.
const PROC_SELF: &str = "/proc/self";


// A process ID is represented as a u32 as per `process::Child::id`'s
// return value.
type Pid = u32;
type Str = Cow<'static, str>;
type Result<T> = StdResult<T, (Str, IoError)>;


trait Filter<T, E>
where
  Self: Sized,
{
  fn filter<F>(&self, f: F) -> bool
  where
    F: FnMut(&T) -> bool;

  fn filter_flat<F>(self, f: F) -> Option<Self>
  where
    F: FnMut(&T) -> StdResult<bool, E>;

  fn map_flat<F, U>(self, f: F) -> StdResult<U, E>
  where
    F: FnMut(T) -> StdResult<U, E>;

  fn filter_map_flat<F, U>(self, f: F) -> Option<StdResult<U, E>>
  where
    F: FnMut(T) -> Option<StdResult<U, E>>;
}

impl<T, E> Filter<T, E> for StdResult<T, E> {
  /// Filter based on a f.
  fn filter<F>(&self, mut f: F) -> bool
  where
    F: FnMut(&T) -> bool,
  {
    match &self {
      Ok(val) => f(val),
      Err(_) => true,
    }
  }

  /// Filter based on a f and flatten errors into ones self.
  fn filter_flat<F>(self, mut f: F) -> Option<Self>
  where
    F: FnMut(&T) -> StdResult<bool, E>,
  {
    match self {
      Ok(val) => match f(&val) {
        Ok(true) => Some(Ok(val)),
        Ok(false) => None,
        Err(err) => Some(Err(err)),
      },
      Err(err) => Some(Err(err)),
    }
  }

  fn map_flat<F, U>(self, mut f: F) -> StdResult<U, E>
  where
    F: FnMut(T) -> StdResult<U, E>,
  {
    match self {
      Ok(val) => f(val),
      Err(err) => Err(err),
    }
  }

  fn filter_map_flat<F, U>(self, mut f: F) -> Option<StdResult<U, E>>
  where
    F: FnMut(T) -> Option<StdResult<U, E>>,
  {
    match self {
      Ok(val) => f(val),
      Err(err) => Some(Err(err)),
    }
  }
}


trait WithCtx<T>
where
  Self: Sized,
{
  type E;

  fn ctx<F, S>(self, ctx: F) -> StdResult<T, (Str, Self::E)>
  where
    F: Fn() -> S,
    S: Into<Str>;
}

impl<T, E> WithCtx<T> for StdResult<T, E> {
  type E = E;

  fn ctx<F, S>(self, ctx: F) -> StdResult<T, (Str, Self::E)>
  where
    F: Fn() -> S,
    S: Into<Str>,
  {
    self.map_err(|e| (ctx().into(), e))
  }
}


/// Check the return value of a system call.
fn check<T>(result: T, error: T) -> IoResult<()>
where
  T: Copy + PartialOrd<T>,
{
  if result == error {
    Err(IoError::last_os_error())
  } else {
    Ok(())
  }
}

/// Check if the given mode represents a character device.
fn is_chardev(mode: Mode) -> bool {
  mode & S_IFMT == S_IFCHR
}

/// Check whether a path represents a terminal and retrieve its device descriptor.
fn find_self() -> Result<PathBuf> {
  read_link(PROC_SELF).ctx(|| format!("failed to dereference {}", PROC_SELF))
}

fn stat<P>(path: P) -> Result<Stat64>
where
  P: AsRef<OsStr>,
{
  let mut buf = unsafe { uninitialized() };
  let path = path.as_ref();
  let path_buf = path.to_os_string().into_vec();
  // We need to ensure NUL termination when performing the system call.
  let file = unsafe { CString::from_vec_unchecked(path_buf) };
  let result = unsafe { stat64(file.as_ptr(), &mut buf) };

  check(result, -1)
    .ctx(|| format!("stat64 failed for {}", path.to_string_lossy()))?;

  Ok(buf)
}

/// Check whether a path represents a terminal and retrieve its device descriptor.
fn check_tty<P>(path: P) -> Result<Dev>
where
  P: AsRef<OsStr>,
{
  let buf = stat(path)?;

  if is_chardev(buf.st_mode) {
    Ok(buf.st_rdev)
  } else {
    Err(IoError::new(ErrorKind::NotFound, "no controlling terminal found"))
      .ctx(|| "failed to find TTY")
  }
}

/// Check if an `OsStr` represents a PID.
fn check_pid(s: &OsStr) -> Option<Pid> {
  if let Some(pid) = s.to_str() {
    Pid::from_str(pid).ok()
  } else {
    None
  }
}

/// Retrieve an iterator over all process entries within /proc.
fn proc_entries() -> Result<impl Iterator<Item = Result<(Pid, DirEntry)>>> {
  read_dir(PROC)
    .ctx(|| format!("failed to read directory {}", PROC))
    .map(|x| {
      x.filter_map(|entry| {
        match entry {
          Ok(entry) => {
            let path = entry.path();
            if path.is_dir() {
              // Check whether the entry we found could represent a
              // process ID entry, which is a directory named as a
              // number.
              if let Some(pid) = check_pid(&entry.file_name()) {
                Some(Ok((pid, entry)))
              } else {
                None
              }
            } else {
              None
            }
          },
          Err(err) => {
            Some(Err(err).ctx(|| format!("failed to read directory entry below {}", PROC)))
          },
        }
      })
    })
}

/// A filter_map handler to filter out the self entry from a list of `DirEntry` objects.
fn filter_self<P>(entry: &DirEntry, self_: P) -> bool
where
  P: AsRef<OsStr>,
{
  entry.path().file_name() != Some(self_.as_ref())
}

fn filter_tty(entry: &DirEntry, tty: Dev) -> Result<bool> {
  let mut path = entry.path();
  path.push("fd");
  path.push("0");

  match check_tty(&path) {
    Ok(other_tty) => Ok(other_tty == tty),
    Err(err) => {
      // Skip all processes that do not have a controlling
      // terminal.
      if err.1.kind() == ErrorKind::NotFound ||
         err.1.kind() == ErrorKind::PermissionDenied ||
         err.1.raw_os_error() == Some(ENXIO) {
        Ok(false)
      } else {
        Err(err)
      }
    }
  }
}

fn filter_nvim(entry: &DirEntry) -> Result<bool> {
  let mut path = entry.path();
  path.push("exe");

  read_link(&path)
    .ctx(|| format!("failed to dereference {}", path.to_string_lossy()))
    .map(|path| match path.file_name() {
      // If the process' executable starts with the nvim prefix we
      // take it.
      Some(file) if file.to_str().map_or(false, |x| x.starts_with(NVIM)) => Ok(true),
      _ => Ok(false),
    })?
}

fn is_socket(mode: Mode) -> bool {
  mode & S_IFMT == S_IFSOCK
}

fn check_socket<P>(path: P) -> Result<Inode>
where
  P: AsRef<OsStr>,
{
  let path = path.as_ref();
  let buf = stat(path)?;

  if is_socket(buf.st_mode) {
    Ok(buf.st_ino)
  } else {
    Err(IoError::new(ErrorKind::NotFound, "no socket found"))
      .ctx(|| format!("file {} is not a socket", path.to_string_lossy()))
  }
}

/// A filter_map handler to map a process entry to a UNIX domain socket path.
fn map_socket_inodes(entry: DirEntry) -> Result<impl Iterator<Item = Result<Inode>>> {
  let mut path = entry.path();
  path.push("fd");

  read_dir(&path)
    .ctx(|| format!("failed to read directory {}", path.to_string_lossy()))
    .map(move |x| {
      x.filter_map(move |entry| match entry {
        Ok(entry) => {
          let path = entry.path();
          if let Ok(inode) = check_socket(&path) {
            Some(Ok(inode))
          } else {
            None
          }
        },
        Err(err) => Some(Err(err).ctx(|| {
          format!(
            "failed to read directory entry below {}",
            path.to_string_lossy(),
          )
        })),
      })
    })
}

fn map_inode_to_socket(line: &str, inode: Inode) -> Option<StdResult<PathBuf, IoError>> {
  // The inode is the 7th entry and the path the 8th.
  let mut parts = line.split_whitespace().skip(6);
  let inod = parts.next()?;
  let path = parts.next()?;

  match Inode::from_str(inod) {
    Ok(x) if x == inode => Some(Ok(path.into())),
    Ok(_) => None,
    Err(_) => Some(Err(IoError::new(
      ErrorKind::Other,
      format!("encountered unparsable inode: {}", inod),
    ))),
  }
}

/// Map an inode to a UNIX domain socket path.
fn map_unix_socket(inode: Inode) -> Option<Result<PathBuf>> {
  File::open(PROC_UNIX)
    .ctx(|| format!("failed to open {}", PROC_UNIX))
    .filter_map_flat(|file| {
      BufReader::new(file)
        .lines()
        .skip(1)
        .filter_map(|line| line.filter_map_flat(|x| map_inode_to_socket(&x, inode)))
        .map(|x| x.ctx(|| format!("error while reading lines from {}", PROC_UNIX)))
        .next()
    })
}


/// An enum representing the different commands the program supports.
enum Command {
  FindSocket,
}


mod int {
  use std::fmt::Debug;
  use std::fmt::Display;
  use std::fmt::Formatter;
  use std::fmt::Result;

  use super::IoError;
  use super::Str;

  pub enum Error {
    UsageError,
    IoError(IoError),
  }

  impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
      match self {
        Error::UsageError => write!(
          f,
          "Usage: nvim-ctrl find-socket tty"
        ),
        Error::IoError(err) => write!(f, "{}", err),
      }
    }
  }

  impl From<IoError> for Error {
    fn from(e: IoError) -> Self {
      Error::IoError(e)
    }
  }


  // An error class for the purpose of being able to return a Result with
  // a sane error representation from `main`.
  pub struct ExitError(pub Option<Str>, pub Error);

  impl From<(Str, IoError)> for ExitError {
    fn from(e: (Str, IoError)) -> Self {
      Self(Some(e.0), e.1.into())
    }
  }

  impl From<Error> for ExitError {
    fn from(e: Error) -> Self {
      Self(None, e)
    }
  }

  impl Debug for ExitError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
      // For our intents and purposes the debug representation behaves
      // exactly like Display would, by printing a correctly formatted
      // error. This implementation is what is actually invoked when
      // displaying an error returned from `main`.
      match &self.0 {
        Some(ctx) => write!(f, "{}: {}", ctx, self.1),
        None => write!(f, "{}", self.1),
      }
    }
  }
}


fn main() -> StdResult<(), int::ExitError> {
  let mut argv = args_os().skip(1);
  let cmd = argv.next().ok_or_else(|| int::Error::UsageError)?;
  let tty = argv.next().ok_or_else(|| int::Error::UsageError)?;

  let cmd = match cmd.to_str().ok_or_else(|| int::Error::UsageError)? {
    "find-socket" => Ok(Command::FindSocket),
    _ => Err(int::Error::UsageError),
  }?;

  if argv.next().is_some() {
    Err(int::Error::UsageError)?
  }

  // Yes, iterators all the way down. That was an experiment. One could
  // argue it did not go too well :-)
  let self_ = find_self()?;
  let terminal = check_tty(tty)?;
  let nvim = proc_entries()?
    .filter(|x| x.as_ref().filter(|y| filter_self(&y.1, &self_)))
    .filter_map(|x| x.filter_flat(|x| filter_tty(&x.1, terminal)))
    .filter_map(|x| x.filter_flat(|x| filter_nvim(&x.1)))
    .map(|x| x.map_flat(|(x0, x1)| map_socket_inodes(x1).map(|x| (x0, x))))
    .map(|x| x.map(|(x0, x1)| (x0, x1.filter_map(|x| x.filter_map_flat(map_unix_socket)))))
    .next();

  if let Some(nvim) = nvim {
    let (pid, mut sockets) = nvim?;

    if let Some(socket) = sockets.next() {
      let socket = socket?;

      match cmd {
        Command::FindSocket => {
          stdout()
            .write_all(socket.as_os_str().as_bytes())
            .ctx(|| "failed write socket to stdout".to_string())?;
          Ok(())
        },
      }
    } else {
      Err(int::ExitError(
        None,
        IoError::new(
          ErrorKind::NotFound,
          format!("no UNIX domain socket found for process {}", pid),
        )
        .into(),
      ))?
    }
  } else {
    Err(int::ExitError(
      None,
      IoError::new(ErrorKind::NotFound, "no neovim process found").into(),
    ))?
  }
}
