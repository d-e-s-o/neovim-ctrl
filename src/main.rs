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
