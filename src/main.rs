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

//! `neovim-ctrl` is a program for finding and interacting with a Neovim
//! instance running in the current terminal.

use std::env::args_os;
use std::result::Result as StdResult;


mod int {
  use std::fmt::Debug;
  use std::fmt::Display;
  use std::fmt::Formatter;
  use std::fmt::Result;

  pub enum Error {
    UsageError,
  }

  impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
      match self {
        Error::UsageError => write!(
          f,
          "Usage: nvim-ctrl tty"
        ),
      }
    }
  }


  // An error class for the purpose of being able to return a Result with
  // a sane error representation from `main`.
  pub struct ExitError(pub Error);

  impl From<Error> for ExitError {
    fn from(e: Error) -> Self {
      Self(e)
    }
  }

  impl Debug for ExitError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
      // For our intents and purposes the debug representation behaves
      // exactly like Display would, by printing a correctly formatted
      // error. This implementation is what is actually invoked when
      // displaying an error returned from `main`.
      write!(f, "{}", self.0)
    }
  }
}


fn main() -> StdResult<(), int::ExitError> {
  let mut argv = args_os().skip(1);
  let _tty = argv.next().ok_or_else(|| int::Error::UsageError)?;
  Ok(())
}
