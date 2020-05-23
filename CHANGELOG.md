Unreleased
----------
- Replaced usage of `std::mem::uninitialized` with
  `std::mem::MaybeUninit`
- Removed a few unnecessary allocation from error paths
- Downgraded `deny` crate-level lints to `warn`


0.1.0
-----
- Initial release
