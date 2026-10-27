---
version: 1
slug: "crates-server-static-index-html"
primary_target: "crates/server/static/index.html"
related_targets: []
---

# Surface brief: evmdec web app (crates/server/static/index.html)

Scope: the single-page web app served at `/` by the axum server. Mode: Operate. Redesign (replacement visual world); product truth, routes, JSON shape, and every function of the old page are kept: address or bytecode input, chain select, decompile, function list with filter, Code / Report / Implementation / Storage & events / Disassembly / JSON views, download `.sol`, proxy implementation.

Audience and job: auditors reading one contract for an hour; developers checking bytecode before deploying; researchers moving fast between addresses; a hosted public audience on phones. The task: understand what the contract does and where it is dangerous, with evidence.

Constraints: WCAG 2.2 AA; light and dark themes following the system with a manual override; full keyboard operation; no external fonts or scripts; shareable links (chain + address in the URL); severity never by colour alone.

## Direction contract

THESIS: The contract is a built structure and the page is its drawing set. It refuses the category's console (side nav, dark slate, badges) and the report-PDF arrangement: metadata lives in a title block, functions are an indexed sheet list, the code is the drawing, and every finding is a numbered callout keyed to a detail at the right.

OWN-WORLD: Whiteprint in light (white sheet, iron-black line and type, one vermilion rubric for callouts and the risk figure), blueprint in dark (Prussian blue ground, pale line and type, amber rubric). Hairline rules at one pixel divide every region; no radius except the callout circles; small tracked uppercase labels over tabular values; system sans for UI, system mono for code. The dashed revision cloud outlines a flagged line. Fixed-cell lists whose columns never move. The chosen line or finding stays lit.

STORY: The visitor reads the title block (chain, address, compiler, coverage, findings, risk), scans the sheet index, reads the drawing, and follows a callout number to its detail and back. They leave knowing which lines are dangerous and why, and can send the link.

FIRST VIEWPORT: Row 1, the header strip: wordmark, the address/bytecode field filling the width, chain select, Decompile, theme toggle, all cells divided by rules. Row 2, the title block: eight labelled cells (sheet, chain, address, compiler, code, coverage, findings, risk in rubric). Below, three columns: the function index (280px, sheets F-01…, selector cell, name, mutability), the drawing (tabs over the code, a scale line naming what is shown, callout bubbles in the gutter), the details (380px, findings keyed by callout number, the first open). Primary action: Decompile in the header. Empty state: the title block reads "no sheet loaded" and the drawing area holds the three example addresses.

FORM: Drawing set, candidate 6 of 7 on the grounded list (audit report, formal spec, post-mortem editorial, block explorer ledger, reading room, drawing set, safety report). seed:67b4e9518045227d. Raised by split-flap board: fixed cells; by gate board: the chosen item stays lit; by catalog sleeve: nothing labelled twice.

FINISH: unreviewed and undocumented is unfinished; this build ends with the finish review, the verdict, DESIGN.md, and every shipping raster carrying its provenance.

Signature interaction: a callout bubble in the gutter and the matching number in the details are the same key; activating either lights both, scrolls the other into view, and announces the finding to assistive tech. Motion grammar: one damped 200 ms ease-out on the lit background; nothing else moves; reduced motion disables it.

Unresolved: whether the hosted instance records history (out of scope).
