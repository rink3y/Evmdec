use std::cell::Cell;
use std::panic::{self, AssertUnwindSafe};
use std::time::{Duration, Instant};

thread_local! {
    static DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
}

struct Expired;

pub fn run<R>(time: Duration, work: impl FnOnce() -> R) -> Option<R> {
    let previous = DEADLINE.with(Cell::get);
    let wanted = Instant::now() + time;
    DEADLINE.with(|d| d.set(Some(previous.map_or(wanted, |p| p.min(wanted)))));
    let outcome = panic::catch_unwind(AssertUnwindSafe(work));
    DEADLINE.with(|d| d.set(previous));
    match outcome {
        Ok(done) => Some(done),
        Err(payload) if payload.is::<Expired>() => None,
        Err(payload) => panic::resume_unwind(payload),
    }
}

const WORKER_STACK: usize = 64 << 20;

// The depth limits in this crate are sized for a 2 MiB stack. The larger stack here is a
// second line of defence. The thread also takes its expression table with it when it ends,
// so a long-lived caller does not keep the table of every input it has seen.
pub fn on_worker<R: Send>(work: impl FnOnce() -> R + Send) -> std::thread::Result<R> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(WORKER_STACK)
            .spawn_scoped(scope, work)
            .expect("a worker thread could not be started")
            .join()
    })
}

// Unwinds up to run. A half-built result must never be returned.
pub fn check() {
    if DEADLINE
        .with(Cell::get)
        .is_some_and(|d| Instant::now() >= d)
    {
        panic::resume_unwind(Box::new(Expired));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_worker_returns_its_result_and_reports_a_panic() {
        assert_eq!(on_worker(|| 7).ok(), Some(7));
        assert!(on_worker(|| panic!("expected in this test")).is_err());
    }

    #[test]
    fn work_is_abandoned_once_its_time_has_passed() {
        check();
        assert_eq!(run(Duration::from_secs(3600), || 7), Some(7));
        let abandoned = run(Duration::ZERO, || {
            check();
            7
        });
        assert_eq!(abandoned, None);
        let nested = run(Duration::from_secs(3600), || {
            let inner = run(Duration::ZERO, || {
                check();
                1
            });
            check();
            inner
        });
        assert_eq!(nested, Some(None));
        check();
    }
}
