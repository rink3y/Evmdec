use std::cell::Cell;

thread_local! {
    static LEFT: Cell<u64> = const { Cell::new(u64::MAX) };
    static USED: Cell<u64> = const { Cell::new(0) };
}

/* Work is counted in interpreter steps and copied state, never in seconds, so the same
contract gets the same report on any machine. */
pub fn within<R>(units: u64, work: impl FnOnce() -> R) -> R {
    let outer = LEFT.with(|l| l.replace(units));
    let done = work();
    let inner_left = LEFT.with(|l| l.replace(outer));
    let used = units.saturating_sub(inner_left);
    LEFT.with(|l| l.set(outer.saturating_sub(used)));
    done
}

pub fn spend(units: u64) {
    LEFT.with(|l| l.set(l.get().saturating_sub(units)));
    USED.with(|u| u.set(u.get().saturating_add(units)));
}

#[must_use]
pub fn spent() -> bool {
    LEFT.with(|l| l.get() == 0)
}

#[must_use]
pub fn left() -> u64 {
    LEFT.with(Cell::get)
}

#[must_use]
pub fn used() -> u64 {
    USED.with(Cell::get)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_inner_budget_is_charged_to_the_outer_one() {
        within(100, || {
            within(30, || {
                spend(50);
                assert!(spent());
            });
            assert!(!spent());
            spend(69);
            assert!(!spent());
            spend(1);
            assert!(spent());
        });
    }
}
