Unreleased
----------
- Bumped minimum required Rust version to `1.36.0`


0.1.1
-----
- Ignore `Neovim` processes in stopped state
- Replaced usage of `std::mem::uninitialized` with
  `std::mem::MaybeUninit`
- Removed a few unnecessary allocation from error paths
- Downgraded `deny` crate-level lints to `warn`


0.1.0
-----
- Initial release
