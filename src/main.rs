// main.rs

// *************************************************************************
// * Copyright (C) 2019-2023 Daniel Mueller (deso@posteo.net)              *
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

#![allow(clippy::let_unit_value)]
#![warn(
  bad_style,
  dead_code,
  future_incompatible,
  illegal_floating_point_literal_pattern,
  improper_ctypes,
  late_bound_lifetime_arguments,
  missing_copy_implementations,
  missing_debug_implementations,
  missing_docs,
  no_mangle_generic_items,
  non_shorthand_field_patterns,
  nonstandard_style,
  overflowing_literals,
  path_statements,
  patterns_in_fns_without_body,
  private_in_public,
  proc_macro_derive_resolution_fallback,
  renamed_and_removed_lints,
  rust_2018_compatibility,
  rust_2018_idioms,
  stable_features,
  trivial_bounds,
  trivial_numeric_casts,
  type_alias_bounds,
  tyvar_behind_raw_pointer,
  unconditional_recursion,
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
  rustdoc::broken_intra_doc_links
)]

//! `neovim-ctrl` is a program for finding and interacting with a Neovim
//! instance running in the current terminal.

use std::borrow::Cow;
use std::env::args_os;
use std::ffi::CString;
use std::ffi::OsStr;
use std::ffi::OsString;
use std::fs::read_dir;
use std::fs::read_link;
use std::fs::DirEntry;
use std::fs::File;
use std::io::stdout;
use std::io::BufRead;
use std::io::BufReader;
use std::io::Error as IoError;
use std::io::ErrorKind;
use std::io::Read;
use std::io::Result as IoResult;
use std::io::Write;
use std::mem::MaybeUninit;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::ffi::OsStringExt;
use std::path::Path;
use std::path::PathBuf;
use std::result::Result as StdResult;
use std::str::FromStr;

use libc::dev_t as Dev;
use libc::ino64_t as Inode;
use libc::mode_t as Mode;
use libc::stat64 as Stat64;
use libc::stat64;
use libc::ENXIO;
use libc::S_IFCHR;
use libc::S_IFMT;
use libc::S_IFSOCK;

use neovim_lib::neovim::map_generic_error;
use neovim_lib::CallError;
use neovim_lib::Neovim;
use neovim_lib::NeovimApi;
use neovim_lib::Session;
use neovim_lib::Value;

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

/// Find PID "file name" pointed to by `/proc/self`.
fn find_self() -> Result<OsString> {
  let dst = read_link(PROC_SELF).ctx(|| format!("failed to dereference {}", PROC_SELF))?;
  // The link effectively just points to a PID, not an entire path. So
  // it makes sense to treat the result as a mere `OsString`.
  Ok(dst.into_os_string())
}

fn stat<P>(path: P) -> Result<Stat64>
where
  P: AsRef<Path>,
{
  let mut buf = MaybeUninit::<Stat64>::uninit();
  let path = path.as_ref();
  let path_buf = path.as_os_str().to_os_string().into_vec();
  // We need to ensure NUL termination when performing the system call.
  let file = unsafe { CString::from_vec_unchecked(path_buf) };
  let result = unsafe { stat64(file.as_ptr(), buf.as_mut_ptr()) };

  check(result, -1).ctx(|| format!("stat64 failed for {}", path.display()))?;

  Ok(unsafe { buf.assume_init() })
}

/// Check whether a path represents a terminal and retrieve its device descriptor.
fn check_tty<P>(path: P) -> Result<Dev>
where
  P: AsRef<Path>,
{
  let buf = stat(path)?;

  if is_chardev(buf.st_mode) {
    Ok(buf.st_rdev)
  } else {
    Err(IoError::new(
      ErrorKind::NotFound,
      "no controlling terminal found",
    ))
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
              check_pid(&entry.file_name()).map(|pid| Ok((pid, entry)))
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

/// A filter_handler to filter out the self entry from a list of `DirEntry` objects.
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
      if err.1.kind() == ErrorKind::NotFound
        || err.1.kind() == ErrorKind::PermissionDenied
        || err.1.raw_os_error() == Some(ENXIO)
      {
        Ok(false)
      } else {
        Err(err)
      }
    },
  }
}

fn filter_nvim(entry: &DirEntry) -> Result<bool> {
  let mut path = entry.path();
  path.push("exe");

  match read_link(&path) {
    Ok(path) => {
      match path.file_name() {
        // If the process' executable starts with the nvim prefix we
        // take it.
        Some(file) if file.to_str().map_or(false, |x| x.starts_with(NVIM)) => Ok(true),
        _ => Ok(false),
      }
    },
    Err(err) if err.kind() == ErrorKind::PermissionDenied => {
      // We could be working with an entry which we have no permission
      // to access. Ignore it.
      Ok(false)
    },
    Err(err) => Err(err).ctx(|| format!("failed to dereference {}", path.display())),
  }
}

fn filter_non_stopped(entry: &DirEntry) -> Result<bool> {
  let mut path = entry.path();
  path.push("stat");

  let mut file = File::open(&path).ctx(|| format!("failed to open {}", path.display()))?;

  // 512 bytes should be more than enough to get to the status field.
  // Before it are only the pid and the file name of the executable. See
  // proc(5).
  let mut buf = [0u8; 512];
  let n = file
    .read(&mut buf)
    .ctx(|| format!("failed to read from {}", path.display()))?;

  // One can only hope that the file name does not contain a space
  // or...well, just screw this brain dead API.
  match buf[..n].split(|c| *c == b' ').nth(2) {
    // If the process has been stopped (or is being traced) we don't
    // want to interact with it.
    Some([b'T']) => Ok(false),
    _ => Ok(true),
  }
}


/// A filter_handler to filter out all entries not having `parent_pid`
/// as the parent process from a list of `DirEntry` objects.
fn filter_by_parent(entry: &DirEntry, parent_pid: Pid) -> Result<bool> {
  let mut path = entry.path();
  let () = path.push("status");

  let file = File::open(&path).ctx(|| format!("failed to open {}", path.display()))?;

  let lines = BufReader::new(file).lines();

  for result in lines {
    let line = result.ctx(|| format!("error while reading lines from {}", path.display()))?;
    if let Some(line) = line.strip_prefix("PPid:") {
      let line = line.trim();
      let pid = Pid::from_str(line)
        .map_err(|err| IoError::new(ErrorKind::InvalidInput, format!("{}", err)))
        .ctx(|| format!("failed to parse PPid from {}", path.display()))?;
      if pid == parent_pid {
        return Ok(true);
      }
    }
  }

  Ok(false)
}


fn is_socket(mode: Mode) -> bool {
  mode & S_IFMT == S_IFSOCK
}

fn check_socket<P>(path: P) -> Result<Inode>
where
  P: AsRef<Path>,
{
  let path = path.as_ref();
  let buf = stat(path)?;

  if is_socket(buf.st_mode) {
    Ok(buf.st_ino)
  } else {
    Err(IoError::new(ErrorKind::NotFound, "no socket found"))
      .ctx(|| format!("file {} is not a socket", path.display()))
  }
}

/// A filter_map handler to map a process entry to a UNIX domain socket path.
fn map_socket_inodes(entry: DirEntry) -> Result<impl Iterator<Item = Result<Inode>>> {
  let mut path = entry.path();
  path.push("fd");

  read_dir(&path)
    .ctx(|| format!("failed to read directory {}", path.display()))
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
        Err(err) => {
          Some(Err(err).ctx(|| format!("failed to read directory entry below {}", path.display(),)))
        },
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

enum Status {
  Changed,
  Unchanged,
}

/// Feed keys to the Neovim instance represented by the given session.
fn feed_keys(mut session: Session, keys: Vec<u8>) -> StdResult<Status, (Str, CallError)> {
  session.start_event_loop();

  let mut nvim = Neovim::new(session);
  let before = nvim
    .call_function("nvim_get_current_win", vec![])
    .ctx(|| "failed to retrieve currently active window")?;

  let args = vec![
    Value::Binary(keys),
    // "m" is the default mode for nvim_feedkeys in which remaps are
    // applied as usual. See the reference for more information:
    // https://neovim.io/doc/user/eval.html#feedkeys()
    Value::String("m".into()),
    Value::Boolean(false),
  ];
  let _ = nvim
    .session
    .call("nvim_feedkeys", args)
    .map_err(map_generic_error)
    .ctx(|| "failed to feed keys to Neovim")?;

  let after = nvim
    .call_function("nvim_get_current_win", vec![])
    .ctx(|| "failed to retrieve currently active window")?;

  if before != after {
    Ok(Status::Changed)
  } else {
    Ok(Status::Unchanged)
  }
}


/// An enum representing the different commands the program supports.
enum Command {
  FindSocket,
  ChangeWindow(Vec<u8>),
}


mod int {
  use std::fmt::Debug;
  use std::fmt::Display;
  use std::fmt::Formatter;
  use std::fmt::Result;

  use super::CallError;
  use super::IoError;
  use super::Str;

  pub enum Error {
    Usage,
    NoChange,
    Io(IoError),
    Neovim(CallError),
  }

  impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
      match self {
        Error::Usage => write!(
          f,
          "Usage: nvim-ctrl {{find-socket,change-window}} tty [keys]"
        ),
        Error::NoChange => write!(f, "nothing changed"),
        Error::Io(err) => write!(f, "{}", err),
        Error::Neovim(err) => write!(f, "{}", err),
      }
    }
  }

  impl From<IoError> for Error {
    fn from(e: IoError) -> Self {
      Error::Io(e)
    }
  }

  impl From<CallError> for Error {
    fn from(e: CallError) -> Self {
      Error::Neovim(e)
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

  impl From<(Str, CallError)> for ExitError {
    fn from(e: (Str, CallError)) -> Self {
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


/// Retrieve an iterator over all Neovim proc entries.
fn nvim_entries() -> Result<impl Iterator<Item = Result<(Pid, DirEntry)>>> {
  let self_ = find_self()?;
  let nvims = proc_entries()?
    .filter(move |x| x.as_ref().filter(|y| filter_self(&y.1, &self_)))
    .filter_map(|x| x.filter_flat(|x| filter_nvim(&x.1)));

  Ok(nvims)
}


fn main() -> StdResult<(), int::ExitError> {
  let mut argv = args_os().skip(1);
  let cmd = argv.next().ok_or_else(|| int::Error::Usage)?;
  let tty = argv.next().ok_or_else(|| int::Error::Usage)?;
  let tty = Path::new(&tty);
  let cmd = match cmd.to_str().ok_or_else(|| int::Error::Usage)? {
    "find-socket" => Ok(Command::FindSocket),
    "change-window" => {
      let keys = argv.next().ok_or_else(|| int::Error::Usage)?;
      Ok(Command::ChangeWindow(keys.into_vec()))
    },
    _ => Err(int::Error::Usage),
  }?;

  if argv.next().is_some() {
    Err(int::Error::Usage)?
  }

  let mut nvims = nvim_entries()?;

  // Identifying the socket process is a two step process. First we find
  // the Neovim instance attached to the provided terminal.
  let terminal = check_tty(tty)?;
  let parent = nvims
    .by_ref()
    .find_map(|x| x.filter_flat(|x| filter_tty(&x.1, terminal)))
    .ok_or_else(|| {
      int::ExitError(
        None,
        IoError::new(
          ErrorKind::NotFound,
          format!("failed to find nvim process for {}", tty.display()),
        )
        .into(),
      )
    })??;

  // Second we look for the child process of `parent`.
  let child = nvims
    // In all likelihood, the child will just be the process with the
    // next PID, so we just continue the search there. However, that's
    // just a property of how process IDs are likely to be assigned.
    // Worst case (if that ever changes), we have to scan the entire
    // process list again.
    // Yes, iterators all the way down. That was an experiment. One could
    // argue it did not go too well :-)
    .chain(nvim_entries()?)
    .filter_map(|x| x.filter_flat(|x| filter_by_parent(&x.1, parent.0)))
    .filter_map(|x| x.filter_flat(|x| filter_non_stopped(&x.1)))
    .map(|x| x.map_flat(|(x0, x1)| map_socket_inodes(x1).map(|x| (x0, x))))
    .map(|x| x.map(|(x0, x1)| (x0, x1.filter_map(|x| x.filter_map_flat(map_unix_socket)))))
    .next();

  if let Some(nvim) = child {
    let (pid, mut sockets) = nvim?;

    if let Some(socket) = sockets.next() {
      let socket = socket?;

      match cmd {
        Command::FindSocket => {
          stdout()
            .write_all(socket.as_os_str().as_bytes())
            .ctx(|| "failed write socket to stdout")?;
          Ok(())
        },
        Command::ChangeWindow(keys) => {
          let session = Session::new_unix_socket(&socket).ctx(|| {
            format!(
              "failed to establish Neovim session via {}",
              socket.display()
            )
          })?;

          match feed_keys(session, keys)? {
            Status::Changed => Ok(()),
            Status::Unchanged => Err(int::Error::NoChange)?,
          }
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
