//! Cooperative control for long-running parser operations.

use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};

/// A clonable cancellation handle for a parse operation.
///
/// Existing parsing entry points do not require a control. Callers that need
/// cancellation can create one, pass a reference to the controlled entry
/// point, and call [`ParseControl::cancel`] from another thread.
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
