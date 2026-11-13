use std::collections::HashSet;
use std::sync::OnceLock;

// The switches are read once. Some are asked for inside loops that run per instruction,
// and reading the environment there took a lock and an allocation every time.
pub fn on(name: &str) -> bool {
    static SET: OnceLock<HashSet<String>> = OnceLock::new();
    let set = SET.get_or_init(|| {
        let names = std::env::vars_os().filter_map(|(name, _)| name.into_string().ok());
        names
            .filter(|name| name.starts_with("EVMDEC_DEBUG"))
            .collect()
    });
    !set.is_empty() && set.contains(name)
}
