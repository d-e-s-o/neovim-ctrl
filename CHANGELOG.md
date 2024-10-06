0.2.1
-----
- Handle "blocked" Neovim instances more gracefully and without hitting
  timeouts


0.2.0
-----
- Adjusted logic to work with Neovim 0.9.0 and higher
- Switched to using GitHub Actions as CI provider
- Bumped minimum required Rust version to `1.57.0`


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
