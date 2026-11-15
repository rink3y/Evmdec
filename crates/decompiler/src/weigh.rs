use crate::analyze::{Finding, Severity};
use std::collections::BTreeMap;

const FITTED: &str = include_str!("weights.tsv");
// Chosen by cross-validation on the development set, which `corpus/evidence_fit.py`
// repeats. Moving it to suit another set makes the score on that set mean nothing.
const RAISE_AT: i64 = 3500;
const RAISED: &str = " Rated high on the weight of this report: what is found here together is seldom found together on a contract with no known flaw.";

type Weights = BTreeMap<(String, Severity), i64>;

fn fitted() -> Weights {
    let level = |name: &str| match name {
        "critical" => Some(Severity::Critical),
        "high" => Some(Severity::High),
        "medium" => Some(Severity::Medium),
        _ => None,
    };
    let row = |line: &str| {
        let mut cols = line.split('\t');
        let (rule, sev) = (cols.next()?, level(cols.next()?)?);
        Some(((rule.to_string(), sev), cols.next()?.parse().ok()?))
    };
    FITTED.lines().filter_map(row).collect()
}

pub(crate) fn rate(findings: &mut [Finding]) {
    if std::env::var("EVMDEC_AS_FOUND").is_err() {
        rate_with(findings, &fitted(), RAISE_AT);
    }
}

// A report is only ever rated up. Lowering a high finding on the same weights took a
// true one away on the known-vulnerable corpus.
fn rate_with(findings: &mut [Finding], weights: &Weights, raise_at: i64) {
    let mut worst: BTreeMap<String, Severity> = BTreeMap::new();
    for f in findings.iter().filter(|f| f.severity <= Severity::Medium) {
        let at = worst.entry(f.id.clone()).or_insert(f.severity);
        *at = (*at).min(f.severity);
    }
    let weight = |rule: &str, sev: Severity| {
        let key = (rule.to_string(), sev);
        weights.get(&key).copied().unwrap_or(0)
    };
    let score: i64 = worst.iter().map(|(rule, sev)| weight(rule, *sev)).sum();
    if score < raise_at {
        return;
    }
    for f in findings
        .iter_mut()
        .filter(|f| f.severity == Severity::Medium)
    {
        if weight(&f.id, f.severity) > 0 && worst.get(&f.id) == Some(&f.severity) {
            f.severity = Severity::High;
            f.description.push_str(RAISED);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyze::Confidence;

    fn finding(id: &str, severity: Severity) -> Finding {
        Finding {
            id: id.into(),
            title: String::new(),
            severity,
            confidence: Confidence::Medium,
            function: None,
            pc: None,
            description: String::new(),
            evidence: Vec::new(),
            recommendation: String::new(),
            sites: 1,
            confirmed: false,
            witness: None,
            setup: Vec::new(),
            observed: Vec::new(),
        }
    }

    fn weights(rows: &[(&str, Severity, i64)]) -> Weights {
        let key = |(rule, sev, w): &(&str, Severity, i64)| ((rule.to_string(), *sev), *w);
        rows.iter().map(key).collect()
    }

    #[test]
    fn a_report_is_rated_on_what_it_holds_together() {
        use Severity::{High, Medium};
        let table = weights(&[
            ("a", Medium, 2000),
            ("b", Medium, 1600),
            ("c", Medium, -500),
        ]);
        let levels = |found: &[Finding]| found.iter().map(|f| f.severity).collect::<Vec<_>>();

        let mut both = [finding("a", Medium), finding("b", Medium)];
        rate_with(&mut both, &table, 3500);
        assert_eq!(levels(&both), [High, High]);

        let mut one = [finding("a", Medium), finding("c", Medium)];
        rate_with(&mut one, &table, 3500);
        assert_eq!(levels(&one), [Medium, Medium]);

        let mut mixed = [
            finding("a", Medium),
            finding("a", Medium),
            finding("b", Medium),
            finding("c", Medium),
        ];
        rate_with(&mut mixed, &table, 3000);
        assert_eq!(levels(&mixed), [High, High, High, Medium]);

        let table = weights(&[("a", High, 2500), ("b", Medium, 1600)]);
        let mut rated = [
            finding("a", High),
            finding("a", Medium),
            finding("b", Medium),
        ];
        rate_with(&mut rated, &table, 3500);
        assert_eq!(levels(&rated), [High, Medium, High]);
    }
}
