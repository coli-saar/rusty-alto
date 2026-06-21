//! Cooperative cancellation for long-running parser operations.
//!
//! Ordinary callers can continue to use [`crate::Irtg::parse`] and
//! [`crate::Irtg::parse_with`] without constructing a control. Applications
//! that own cancellable jobs can clone a [`ParseControl`], pass one clone to
//! [`crate::Irtg::parse_with_control`], and call [`ParseControl::cancel`] from
//! another thread.
//!
//! Cancellation is cooperative: parsing returns
//! [`crate::IrtgError::Cancelled`] after reaching a safe check point. It does
//! not forcibly terminate a thread, and partial charts are not returned.

use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};

/// A clonable cancellation handle for a parse operation.
///
/// Existing parsing entry points do not require a control. Callers that need
/// cancellation can create one, pass a reference to the controlled entry
/// point, and call [`ParseControl::cancel`] from another thread.
///
/// Clones share cancellation state. A canceled control remains canceled, so
/// create a fresh control for each independent parse job.
#[derive(Clone, Debug, Default)]
pub struct ParseControl {
    cancelled: Arc<AtomicBool>,
}

impl ParseControl {
    /// Create a control in the running state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Request cooperative cancellation.
    ///
    /// This operation is thread-safe, inexpensive, and idempotent.
    pub fn cancel(&self) {
        self.cancelled.store(true, Ordering::Relaxed);
    }

    /// Return whether cancellation has been requested.
    pub fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Relaxed)
    }

    pub(crate) fn check(&self) -> Result<(), ParseCancelled> {
        if self.is_cancelled() {
            Err(ParseCancelled)
        } else {
            Ok(())
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ParseCancelled;

#[cfg(test)]
mod tests {
    use super::ParseControl;

    #[test]
    fn cloned_control_observes_cancellation() {
        let control = ParseControl::new();
        let worker_control = control.clone();

        control.cancel();

        assert!(worker_control.is_cancelled());
        assert!(worker_control.check().is_err());
    }
}
