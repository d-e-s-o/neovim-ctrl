// Copyright (C) 2026 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

//! A tiny Msgpack-RPC client for interacting with a running Neovim
//! instance.
//!
//! Only as much of the [`Msgpack-RPC`] protocol is implemented as is
//! needed to invoke API functions on a Neovim instance: Requests are
//! issued one at a time and answered with a single response.
//! Notifications and even requests sent by Neovim are dealt with on the
//! side, though we should never receive either of them, because we never
//! subscribe to anything.
//!
//! [`Msgpack-RPC`]: https://github.com/msgpack-rpc/msgpack-rpc/blob/master/spec.md

use std::error::Error;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::Result as FmtResult;
use std::io::Error as IoError;
use std::io::ErrorKind;
use std::io::Result as IoResult;
use std::io::Write;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::time::Duration;

use rmpv::decode::read_value;
use rmpv::encode::write_value;
use rmpv::Value;


/// The Msgpack-RPC message type of a function call.
const MSG_CALL: u64 = 0;
/// The Msgpack-RPC message type of a response.
const MSG_RESPONSE: u64 = 1;
/// The Msgpack-RPC message type of a notification.
const MSG_NOTIFICATION: u64 = 2;

/// The Msgpack-RPC error code for a method that is unavailable.
const METHOD_NOT_FOUND: i64 = -32601;

/// The duration after which a call gives up on waiting for a response.
const CALL_TIMEOUT: Duration = Duration::from_secs(5);


/// An error that occurred while interacting with a Neovim instance.
#[derive(Debug)]
pub enum CallError {
  /// An error on our side, such as a transport failure or a timeout.
  Io(IoError),
  /// An error reported by Neovim that carries an error code.
  Neovim(i64, String),
  /// An error reported by Neovim that we were unable to make sense of.
  Generic(String),
}

impl CallError {
  #[cfg(test)]
  fn into_io_error(self) -> Result<IoError, Self> {
    match self {
      Self::Io(io_error) => Ok(io_error),
      err => Err(err),
    }
  }
}

impl Display for CallError {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    match self {
      CallError::Io(err) => Display::fmt(err, f),
      CallError::Neovim(_, msg) | CallError::Generic(msg) => write!(f, "{msg}"),
    }
  }
}

impl PartialEq for CallError {
  /// Compare two errors for equality.
  ///
  /// [`IoError`] does not implement [`PartialEq`], so transport errors
  /// are compared by their kind and message.
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (CallError::Io(l0), CallError::Io(l1)) => {
        l0.kind() == l1.kind() && l0.to_string() == l1.to_string()
      },
      (CallError::Neovim(c0, m0), CallError::Neovim(c1, m1)) => c0 == c1 && m0 == m1,
      (CallError::Generic(m0), CallError::Generic(m1)) => m0 == m1,
      _ => false,
    }
  }
}

impl Eq for CallError {}

impl Error for CallError {}

impl From<IoError> for CallError {
  fn from(e: IoError) -> Self {
    CallError::Io(e)
  }
}


/// Map an error reported by Neovim onto a [`CallError`].
///
/// Neovim reports errors as either a string or as a two element array
/// consisting of an error code and a message. Anything else is reported
/// verbatim.
fn map_error(err: Value) -> CallError {
  if let Value::Array(vals) = &err {
    if let [Value::Integer(code), message] = vals.as_slice() {
      if let (Some(code), Some(msg)) = (code.as_i64(), message.as_str()) {
        return CallError::Neovim(code, msg.to_owned());
      }
    }
  }

  match err.as_str() {
    Some(msg) => CallError::Generic(msg.to_owned()),
    None => CallError::Generic(format!("{err:?}")),
  }
}


/// A session with a running Neovim instance.
///
/// A session is not recoverable from a transport failure: a read or a
/// write may have been interrupted midway through a message, which
/// would leave the stream out of sync with the framing Msgpack-RPC
/// relies on. The first failure of that kind is therefore latched and
/// every subsequent call fails right away. An error reported by Neovim
/// does not have this effect, because the stream is still in sync when
/// one arrives.
pub struct Session {
  /// The stream used for communicating with Neovim.
  stream: UnixStream,
  /// A scratch buffer used for encoding messages.
  buf: Vec<u8>,
  /// The ID the next request is going to use.
  msgid: u64,
  /// The timeout applied to each call.
  timeout: Duration,
  /// Whether a transport failure left the stream in an unknown state.
  failed: bool,
}

impl Session {
  /// Establish a session with a Neovim instance via a UNIX domain
  /// socket.
  pub fn new_unix_socket<P>(path: P) -> IoResult<Self>
  where
    P: AsRef<Path>,
  {
    let stream = UnixStream::connect(path)?;
    Self::with_stream(stream, CALL_TIMEOUT)
  }

  /// Create a session from an already connected stream, applying
  /// `timeout` to every read and write performed on it.
  fn with_stream(stream: UnixStream, timeout: Duration) -> IoResult<Self> {
    let () = stream.set_read_timeout(Some(timeout))?;
    let () = stream.set_write_timeout(Some(timeout))?;

    let slf = Self {
      stream,
      buf: Vec::new(),
      msgid: 1,
      timeout,
      failed: false,
    };
    Ok(slf)
  }

  /// Invoke an API function on Neovim.
  ///
  /// Fails without touching the stream once a transport failure has
  /// rendered the session unusable.
  pub fn call(&mut self, method: &str, args: Vec<Value>) -> Result<Value, CallError> {
    if self.failed {
      let err = IoError::new(
        ErrorKind::NotConnected,
        "session is unusable after a transport failure",
      );
      return Err(CallError::Io(err));
    }

    let msgid = self.msgid;
    self.msgid = msgid.wrapping_add(1);

    let request = Value::Array(vec![
      Value::from(MSG_CALL),
      Value::from(msgid),
      Value::from(method),
      Value::Array(args),
    ]);

    let () = self.send(&request)?;

    loop {
      let frame = self.read()?;

      let vals = match frame {
        Value::Array(vals) => vals,
        other => return Err(CallError::Generic(format!("unexpected message: {other:?}"))),
      };

      match vals.as_slice() {
        [ty, id, Value::Nil, result]
          if ty.as_u64() == Some(MSG_RESPONSE) && id.as_u64() == Some(msgid) =>
        {
          return Ok(result.clone())
        },
        [ty, id, error, _] if ty.as_u64() == Some(MSG_RESPONSE) && id.as_u64() == Some(msgid) => {
          return Err(map_error(error.clone()))
        },
        // A response to a request we are not waiting for.
        [ty, ..] if ty.as_u64() == Some(MSG_RESPONSE) => {},
        // Neovim wants us to handle something, but we never registered
        // anything capable of doing so.
        [ty, id, ..] if ty.as_u64() == Some(MSG_CALL) => self.reject(id.clone())?,
        // We never subscribe to any event, so there is nothing to do
        // here.
        [ty, ..] if ty.as_u64() == Some(MSG_NOTIFICATION) => {},
        _ => return Err(CallError::Generic(format!("unexpected message: {vals:?}"))),
      }
    }
  }

  /// Reject a request sent by Neovim.
  ///
  /// Answering a request keeps Neovim from waiting for a reply that
  /// would never arrive.
  fn reject(&mut self, msgid: Value) -> Result<(), CallError> {
    let response = Value::Array(vec![
      Value::from(MSG_RESPONSE),
      msgid,
      Value::Array(vec![
        Value::from(METHOD_NOT_FOUND),
        Value::from("nvim-ctrl is unable to handle requests"),
      ]),
      Value::Nil,
    ]);

    let () = self.send(&response)?;
    Ok(())
  }

  /// Encode and send a message to Neovim.
  ///
  /// Messages are encoded into a buffer up front, so that a partial
  /// write cannot split a message apart.
  fn send(&mut self, msg: &Value) -> Result<(), CallError> {
    let () = self.buf.clear();

    let () = write_value(&mut self.buf, msg)
      .map_err(IoError::from)
      .map_err(|err| self.map_io_error(err))?;
    let () = self
      .stream
      .write_all(&self.buf)
      .map_err(|err| self.map_io_error(err))?;
    let () = self.stream.flush().map_err(|err| self.map_io_error(err))?;

    Ok(())
  }

  /// Read the next message sent by Neovim.
  fn read(&mut self) -> Result<Value, CallError> {
    read_value(&mut self.stream)
      .map_err(IoError::from)
      .map_err(|err| self.map_io_error(err))
  }

  /// Turn a transport error into a [`CallError`], replacing the rather
  /// cryptic messages of a dead connection and of an expired timeout
  /// with something more actionable.
  ///
  /// Any transport failure renders the session unusable, because it may
  /// have happened in the middle of a message and left the stream
  /// desynchronized.
  fn map_io_error(&mut self, err: IoError) -> CallError {
    self.failed = true;

    let err = match err.kind() {
      ErrorKind::WouldBlock | ErrorKind::TimedOut => {
        let timeout = self.timeout;
        IoError::new(
          ErrorKind::TimedOut,
          format!("no response from Neovim within {timeout:?}"),
        )
      },
      ErrorKind::BrokenPipe | ErrorKind::NotConnected | ErrorKind::UnexpectedEof => {
        IoError::new(err.kind(), "connection closed")
      },
      _ => err,
    };

    CallError::Io(err)
  }
}


#[cfg(test)]
mod tests {
  use super::*;

  use std::io::ErrorKind;
  use std::io::Write;
  use std::net::Shutdown;
  use std::os::unix::net::UnixStream;
  use std::time::Duration;

  use rmpv::decode::read_value;
  use rmpv::encode::write_value;
  use rmpv::Value;


  /// The timeout used for sessions under test.
  const TEST_TIMEOUT: Duration = Duration::from_millis(100);

  /// The ID a fresh session uses for its first request.
  const FIRST_MSGID: u64 = 1;
  /// The ID of the request following the one identified by
  /// `FIRST_MSGID`.
  const SECOND_MSGID: u64 = 2;
  /// The ID of a message that this session never sent.
  const FOREIGN_MSGID: u64 = 7;


  /// Create a session whose peer end is populated with the given
  /// messages.
  fn session_with(replies: &[Value]) -> (Session, UnixStream) {
    let (stream, peer) = UnixStream::pair().unwrap();
    let session = Session::with_stream(stream, TEST_TIMEOUT).unwrap();

    let mut buf = Vec::new();
    for reply in replies {
      let () = write_value(&mut buf, reply).unwrap();
    }
    let () = peer.try_clone().unwrap().write_all(&buf).unwrap();

    (session, peer)
  }

  /// Retrieve the next message a session sent.
  fn received(stream: &mut UnixStream) -> Value {
    read_value(stream).unwrap()
  }

  /// A request with the given ID invoking the given method.
  fn request(msgid: u64, method: &str, args: Vec<Value>) -> Value {
    Value::Array(vec![
      Value::from(MSG_CALL),
      Value::from(msgid),
      Value::from(method),
      Value::Array(args),
    ])
  }

  /// A notification of the given method.
  fn notification(method: &str, args: Vec<Value>) -> Value {
    Value::Array(vec![
      Value::from(MSG_NOTIFICATION),
      Value::from(method),
      Value::Array(args),
    ])
  }

  /// The response to the request with the given ID, containing the
  /// error and result.
  fn response(msgid: u64, error: Value, result: Value) -> Value {
    Value::Array(vec![
      Value::from(MSG_RESPONSE),
      Value::from(msgid),
      error,
      result,
    ])
  }

  /// The result reported by `nvim_get_mode` for the given mode.
  fn mode(mode: &str) -> Value {
    Value::Map(vec![(Value::from("mode"), Value::from(mode))])
  }


  /// Check that a call is correctly encoded.
  #[test]
  fn request_is_encoded_as_a_call() {
    let replies = [response(FIRST_MSGID, Value::Nil, Value::from("ok"))];
    let (mut session, mut peer) = session_with(&replies);

    let keys = vec![0x17, b'h'];
    let result = session
      .call(
        "nvim_feedkeys",
        vec![
          Value::Binary(keys.clone()),
          Value::from("m"),
          Value::Boolean(false),
        ],
      )
      .unwrap();

    assert_eq!(result, Value::from("ok"));
    // The message is spelled out here instead of being built by
    // `request`, because this test is what pins the wire format down.
    assert_eq!(
      received(&mut peer),
      Value::Array(vec![
        Value::from(MSG_CALL),
        Value::from(FIRST_MSGID),
        Value::from("nvim_feedkeys"),
        Value::Array(vec![
          Value::Binary(keys),
          Value::from("m"),
          Value::Boolean(false)
        ]),
      ])
    );
  }

  /// Make sure that request message IDs are increasing.
  #[test]
  fn request_ids_are_increasing() {
    let replies = [
      response(FIRST_MSGID, Value::Nil, mode("n")),
      response(SECOND_MSGID, Value::Nil, mode("v")),
    ];
    let (mut session, mut peer) = session_with(&replies);

    assert_eq!(session.call("nvim_get_mode", vec![]).unwrap(), mode("n"));
    assert_eq!(session.call("nvim_get_mode", vec![]).unwrap(), mode("v"));

    assert_eq!(
      received(&mut peer),
      request(FIRST_MSGID, "nvim_get_mode", vec![])
    );
    assert_eq!(
      received(&mut peer),
      request(SECOND_MSGID, "nvim_get_mode", vec![])
    );
  }

  /// Test the error mapping path.
  #[test]
  fn neovim_error_is_mapped() {
    let error = Value::Array(vec![
      Value::from(METHOD_NOT_FOUND),
      Value::from("Invalid method"),
    ]);
    let replies = [response(FIRST_MSGID, error, Value::Nil)];
    let (mut session, _peer) = session_with(&replies);

    let err = session.call("nvim_feedkeys", vec![]).unwrap_err();
    assert_eq!(
      err,
      CallError::Neovim(METHOD_NOT_FOUND, "Invalid method".to_string())
    );
    assert_eq!(err.to_string(), "Invalid method");
  }

  /// Make sure that a regular Neovim error does not render the session
  /// failed.
  #[test]
  fn session_survives_a_neovim_error() {
    let error = Value::Array(vec![
      Value::from(METHOD_NOT_FOUND),
      Value::from("Invalid method"),
    ]);
    let replies = [
      response(FIRST_MSGID, error, Value::Nil),
      response(SECOND_MSGID, Value::Nil, mode("i")),
    ];
    let (mut session, _peer) = session_with(&replies);

    let err = session.call("nvim_get_mode", vec![]).unwrap_err();
    assert_eq!(
      err,
      CallError::Neovim(METHOD_NOT_FOUND, "Invalid method".to_string())
    );

    // Neovim answered the request in full, so the stream is still in
    // sync and the session can keep using it.
    let result = session.call("nvim_get_mode", vec![]).unwrap();
    assert_eq!(result, mode("i"));
  }

  /// Check that a string error response gets mapped to a "generic"
  /// error on our end.
  #[test]
  fn string_error_is_generic() {
    let replies = [response(FIRST_MSGID, Value::from("boom"), Value::Nil)];
    let (mut session, _peer) = session_with(&replies);

    let err = session.call("nvim_get_mode", vec![]).unwrap_err();
    assert_eq!(err, CallError::Generic("boom".to_string()));
  }

  /// Make sure that a Neovim error of unexpected format is mapped to a
  /// "generic" error on our end.
  #[test]
  fn malformed_error_is_generic() {
    // Neovim reports errors as a code and a message, so an array of
    // just a message is not something we can make sense of.
    let error = Value::Array(vec![Value::from("Invalid buffer id: 3")]);
    let replies = [response(FIRST_MSGID, error, Value::Nil)];
    let (mut session, _peer) = session_with(&replies);

    let err = session.call("nvim_get_mode", vec![]).unwrap_err();
    assert!(matches!(err, CallError::Generic(_)));
  }

  /// Test that notifications coming in concurrently are silently
  /// ignored.
  #[test]
  fn notifications_are_skipped() {
    let replies = [
      notification("redraw", vec![]),
      response(FIRST_MSGID, Value::Nil, mode("n")),
    ];
    let (mut session, _peer) = session_with(&replies);

    let result = session.call("nvim_get_mode", vec![]).unwrap();
    assert_eq!(result, mode("n"));
  }

  /// Make sure that a response to a request we never sent is skipped.
  #[test]
  fn stale_response_is_skipped() {
    let replies = [
      response(FOREIGN_MSGID, Value::Nil, mode("v")),
      response(FIRST_MSGID, Value::Nil, mode("n")),
    ];
    let (mut session, _peer) = session_with(&replies);

    // The session's first request uses the ID `FIRST_MSGID`, so the
    // response to the request with the ID `FOREIGN_MSGID` is not meant
    // for us. Only the mode of the second response may surface.
    let result = session.call("nvim_get_mode", vec![]).unwrap();

    assert_eq!(result, mode("n"));
  }

  /// Make sure that a request sent by Neovim is answered with a
  /// rejection, so that it does not wait for us forever.
  #[test]
  fn request_is_rejected() {
    let replies = [
      request(FOREIGN_MSGID, "some_method", vec![]),
      response(FIRST_MSGID, Value::Nil, Value::from("fine")),
    ];
    let (mut session, mut peer) = session_with(&replies);

    let result = session.call("nvim_get_mode", vec![]).unwrap();
    assert_eq!(result, Value::from("fine"));

    // The request we sent is the first thing the peer received, the
    // rejection of Neovim's request the second.
    assert_eq!(
      received(&mut peer),
      request(FIRST_MSGID, "nvim_get_mode", vec![])
    );
    assert_eq!(
      received(&mut peer),
      Value::Array(vec![
        Value::from(MSG_RESPONSE),
        Value::from(FOREIGN_MSGID),
        Value::Array(vec![
          Value::from(METHOD_NOT_FOUND),
          Value::from("nvim-ctrl is unable to handle requests"),
        ]),
        Value::Nil,
      ])
    );
  }

  /// Make sure that a hung up connection is surfaced correctly.
  #[test]
  fn hung_up_connection_is_reported() {
    let (mut session, peer) = session_with(&[]);
    drop(peer);

    let err = session
      .call("nvim_get_mode", vec![])
      .unwrap_err()
      .into_io_error()
      .unwrap();
    assert_eq!(err.kind(), ErrorKind::BrokenPipe);
    assert_eq!(err.to_string(), "connection closed");
  }

  /// Make sure that an abruptly closed connection is reported promptly.
  #[test]
  fn closed_connection_is_reported() {
    // Neovim is gone, but our own request still makes it into the
    // socket, so it is the response that fails.
    let (mut session, peer) = session_with(&[]);
    let () = peer.shutdown(Shutdown::Write).unwrap();

    let err = session
      .call("nvim_get_mode", vec![])
      .unwrap_err()
      .into_io_error()
      .unwrap();
    assert_eq!(err.kind(), ErrorKind::UnexpectedEof);
    assert_eq!(err.to_string(), "connection closed");
  }

  /// Test that lack of a response sent correctly times out a call.
  #[test]
  fn timeout_is_reported() {
    // The peer never responds, so the call has to time out.
    let (mut session, _peer) = session_with(&[]);

    let err = session
      .call("nvim_get_mode", vec![])
      .unwrap_err()
      .into_io_error()
      .unwrap();
    assert_eq!(err.kind(), ErrorKind::TimedOut);
    assert_eq!(err.to_string(), "no response from Neovim within 100ms");
  }

  /// Make sure that a session is marked failed after encountering a
  /// time out.
  #[test]
  fn session_is_dead_after_a_timeout() {
    // The peer never responds, so the call has to time out.
    let (mut session, mut peer) = session_with(&[]);

    let err = session.call("nvim_get_mode", vec![]).unwrap_err();
    assert_eq!(err.to_string(), "no response from Neovim within 100ms");

    // Even with a perfectly well formed response waiting, the session
    // refuses to read from a stream a read may have been interrupted
    // on.
    let mut buf = Vec::new();
    let reply = response(SECOND_MSGID, Value::Nil, Value::from("late"));
    let () = write_value(&mut buf, &reply).unwrap();
    let () = peer.write_all(&buf).unwrap();

    let err = session
      .call("nvim_get_mode", vec![])
      .unwrap_err()
      .into_io_error()
      .unwrap();
    assert_eq!(err.kind(), ErrorKind::NotConnected);
    assert_eq!(
      err.to_string(),
      "session is unusable after a transport failure"
    );
  }
}
