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
