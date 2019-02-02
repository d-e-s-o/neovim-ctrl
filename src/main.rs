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
use std::fs::read_dir;
use std::io::Error as IoError;
use std::io::ErrorKind;
use std::io::Result as IoResult;
use std::mem::uninitialized;
use std::os::unix::ffi::OsStringExt;
use std::result::Result as StdResult;
use std::str::FromStr;

use libc::dev_t as Dev;
use libc::mode_t as Mode;
use libc::S_IFCHR;
use libc::S_IFMT;
use libc::stat64 as Stat64;
use libc::stat64;


/// The path to the /proc virtual file system.
const PROC: &str = "/proc";


// A process ID is represented as a u32 as per `process::Child::id`'s
// return value.
type Pid = u32;
type Str = Cow<'static, str>;
type Result<T> = StdResult<T, (Str, IoError)>;


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
          "Usage: nvim-ctrl tty"
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
  let tty = argv.next().ok_or_else(|| int::Error::UsageError)?;
  let _terminal = check_tty(tty)?;
  let _nvim = proc_entries()?;
  Ok(())
}
