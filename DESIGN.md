---
name: evmdec
description: An EVM contract's drawing set; an ink band holds the title block, the sheet below is the drawing, findings are keyed callouts.
colors:
  sheet-white: "#ffffff"
  iron-black: "#1a1d21"
  graphite-muted: "#5a6069"
  rule-line: "#b9bec5"
  rule-hair: "#dcdfe3"
  well-grey: "#f4f5f7"
  vermilion-rubric: "#b3261e"
  on-rubric-light: "#ffffff"
  focus-blue: "#0b57d0"
  selection-blue: "#dbe8ff"
  lit-straw: "#fff1c2"
  band-ink: "#132e4f"
  band-pale: "#e6eef8"
  band-muted: "#a9bbd3"
  band-rule: "#2a4a74"
  band-amber: "#ffd27a"
  field-ink: "#0e2440"
  severity-critical: "#8f1a12"
  severity-high: "#b3261e"
  severity-medium: "#8a5a00"
  severity-low: "#1a5fb4"
  severity-info: "#5a6069"
  code-string-green: "#365b1e"
  prussian-ground: "#0f2340"
  pale-line: "#e6eef8"
  dusk-muted: "#a9bbd3"
  blueprint-line: "#4f6f99"
  blueprint-hair: "#28436a"
  blueprint-well: "#153052"
  amber-rubric: "#ffd27a"
  on-rubric-dark: "#0f2340"
  blueprint-selection: "#2d4f7e"
  lit-umber: "#433c1a"
  band-ink-dark: "#081829"
  band-rule-dark: "#27416a"
  field-ink-dark: "#0c1f38"
  severity-critical-dark: "#ff8e86"
  severity-high-dark: "#ff9d93"
  severity-medium-dark: "#ffd27a"
  severity-low-dark: "#8ec5ff"
  severity-info-dark: "#a9bbd3"
  code-string-green-dark: "#b7e3a0"
typography:
  display:
    fontFamily: "\"Barlow Condensed\", \"Barlow\", ui-sans-serif, system-ui, sans-serif"
    fontSize: "34px"
    fontWeight: 600
    lineHeight: 1.1
    letterSpacing: "0.01em"
  wordmark:
    fontFamily: "\"Barlow Condensed\", \"Barlow\", ui-sans-serif, system-ui, sans-serif"
    fontSize: "20px"
    fontWeight: 700
    lineHeight: 1
    letterSpacing: "0.02em"
  risk:
    fontFamily: "\"Barlow Condensed\", \"Barlow\", ui-sans-serif, system-ui, sans-serif"
    fontSize: "18px"
    fontWeight: 600
    lineHeight: 1.2
    letterSpacing: "0.02em"
  action:
    fontFamily: "\"Barlow Condensed\", \"Barlow\", ui-sans-serif, system-ui, sans-serif"
    fontSize: "15px"
    fontWeight: 600
    lineHeight: 1
    letterSpacing: "0.14em"
  body:
    fontFamily: "\"Barlow\", ui-sans-serif, system-ui, \"Segoe UI\", Roboto, Helvetica, Arial, sans-serif"
    fontSize: "14px"
    fontWeight: 400
    lineHeight: 1.45
  heading:
    fontFamily: "\"Barlow Condensed\", \"Barlow\", ui-sans-serif, system-ui, sans-serif"
    fontSize: "13px"
    fontWeight: 600
    lineHeight: 1.2
    letterSpacing: "0.1em"
  label:
    fontFamily: "\"Barlow Condensed\", \"Barlow\", ui-sans-serif, system-ui, sans-serif"
    fontSize: "12px"
    fontWeight: 500
    lineHeight: 1.3
    letterSpacing: "0.12em"
  severity:
    fontFamily: "\"Barlow Condensed\", \"Barlow\", ui-sans-serif, system-ui, sans-serif"
    fontSize: "12px"
    fontWeight: 600
    lineHeight: 1.5
    letterSpacing: "0.1em"
  code:
    fontFamily: "\"Source Code Pro\", ui-monospace, \"SF Mono\", Menlo, Consolas, \"Liberation Mono\", monospace"
    fontSize: "13px"
    fontWeight: 400
    lineHeight: 1.5
  code-small:
    fontFamily: "\"Source Code Pro\", ui-monospace, \"SF Mono\", Menlo, Consolas, \"Liberation Mono\", monospace"
    fontSize: "12px"
    fontWeight: 400
    lineHeight: 1.5
rounded:
  none: "0px"
  callout: "50%"
spacing:
  hair: "2px"
  xs: "6px"
  sm: "8px"
  md: "12px"
  lg: "16px"
  xl: "24px"
  xxl: "36px"
  xxxl: "48px"
components:
  button-primary:
    backgroundColor: "{colors.vermilion-rubric}"
    textColor: "{colors.on-rubric-light}"
    typography: "{typography.action}"
    rounded: "{rounded.none}"
    padding: "0 22px"
    height: "44px"
  button-outline:
    backgroundColor: "transparent"
    textColor: "{colors.iron-black}"
    typography: "{typography.heading}"
    rounded: "{rounded.none}"
    padding: "7px 14px"
  button-outline-hover:
    backgroundColor: "{colors.well-grey}"
  button-band:
    backgroundColor: "transparent"
    textColor: "{colors.band-pale}"
    typography: "{typography.label}"
    rounded: "{rounded.none}"
    padding: "0 16px"
    height: "44px"
  button-band-hover:
    backgroundColor: "{colors.field-ink}"
  input-query:
    backgroundColor: "{colors.field-ink}"
    textColor: "{colors.band-pale}"
    typography: "{typography.code}"
    rounded: "{rounded.none}"
    padding: "0 14px"
    height: "44px"
  select-chain:
    backgroundColor: "{colors.band-ink}"
    textColor: "{colors.band-pale}"
    typography: "{typography.label}"
    rounded: "{rounded.none}"
    padding: "0 32px 0 14px"
    height: "44px"
  input-filter:
    backgroundColor: "{colors.sheet-white}"
    textColor: "{colors.iron-black}"
    typography: "{typography.body}"
    rounded: "{rounded.none}"
    padding: "8px 12px"
  tab:
    backgroundColor: "transparent"
    textColor: "{colors.graphite-muted}"
    typography: "{typography.heading}"
    rounded: "{rounded.none}"
    padding: "10px 16px"
  tab-selected:
    backgroundColor: "transparent"
    textColor: "{colors.iron-black}"
  tab-download:
    backgroundColor: "transparent"
    textColor: "{colors.vermilion-rubric}"
    typography: "{typography.heading}"
    rounded: "{rounded.none}"
    padding: "0 16px"
  callout:
    backgroundColor: "{colors.sheet-white}"
    textColor: "{colors.vermilion-rubric}"
    typography: "{typography.severity}"
    rounded: "{rounded.callout}"
    size: "24px"
  callout-hover:
    backgroundColor: "{colors.vermilion-rubric}"
    textColor: "{colors.on-rubric-light}"
  title-block-cell:
    backgroundColor: "{colors.band-ink}"
    textColor: "{colors.band-pale}"
    typography: "{typography.body}"
    rounded: "{rounded.none}"
    padding: "7px 14px 9px"
  index-row:
    backgroundColor: "{colors.sheet-white}"
    textColor: "{colors.iron-black}"
    typography: "{typography.code-small}"
    rounded: "{rounded.none}"
    padding: "5px 12px"
  index-row-hover:
    backgroundColor: "{colors.well-grey}"
  index-row-current:
    backgroundColor: "{colors.lit-straw}"
  finding-row:
    backgroundColor: "transparent"
    textColor: "{colors.iron-black}"
    typography: "{typography.body}"
    rounded: "{rounded.none}"
    padding: "9px 12px"
  finding-row-hover:
    backgroundColor: "{colors.well-grey}"
  finding-row-lit:
    backgroundColor: "{colors.lit-straw}"
  evidence-well:
    backgroundColor: "{colors.well-grey}"
    textColor: "{colors.iron-black}"
    typography: "{typography.code-small}"
    rounded: "{rounded.none}"
    padding: "6px 10px"
  sheet-frame:
    backgroundColor: "{colors.sheet-white}"
    textColor: "{colors.iron-black}"
    typography: "{typography.body}"
    rounded: "{rounded.none}"
    padding: "36px 40px 32px"
    width: "min(100%, 760px)"
---

# Design System: evmdec

<!-- World: "Drawing set". Direction seed: seed:67b4e9518045227d. Recorded from the shipped page crates/server/static/index.html after the finish review (disposition: ship); refreshed after the ink-band and Barlow revision of the same page. -->

## Overview

**Creative North Star: "The Drawing Set"**

The contract is a built structure and the page is its drawing set. A dark ink band across the top carries the header strip and the title block, the way a drawing's title block sits in its own ruled strip; below it the sheet is the drawing. Functions are an indexed sheet list (F-01, F-02, ...) down the left on a recessed well; the decompiled code is the drawing in the middle; every finding is a numbered callout in the code gutter keyed to a detail at the right. The world refuses the category's console (side nav, dark slate, badges) and the report-PDF arrangement. Everything is drawn in line: one-pixel rules divide every region, nothing has a shadow, nothing has a radius except the callout circles, and nothing is labelled twice.

Two sheets exist under one band. In light the sheet is a whiteprint: white ground, iron-black line and type, one vermilion rubric reserved for callouts, the revision cloud, the selected-tab rule, Download and the Decompile action. In dark the sheet is a blueprint: Prussian-blue ground, pale line and type, an amber rubric in the same roles. The band is ink in both themes (deeper in dark), with pale type, tracked condensed labels and an amber band-rubric that carries the risk figure and the band's focus ring. The theme follows the system and can be overridden by the header toggle; both sheets meet WCAG 2.2 AA including the code highlighting and the severity colours.

Lettering is draughting-room: Barlow for reading text, Barlow Condensed in tracked capitals for every label, heading, tab, action and the wordmark, Source Code Pro for code, selectors and evidence. The faces load from Google Fonts with the system stacks as fallbacks. Density is that of a drawing, not a dashboard: 14px body on a 1.45 line, 13px code on a 1.5 line, 12px tracked labels over tabular values. The only motion is the lit background settling in over 200ms; nothing else moves, and reduced motion removes even that.

**Key Characteristics:**
- An ink band (header strip and title block) over a light or Prussian sheet; 44px header cells divided by band rules.
- Hairline rules at 1px divide every region; no shadows, no fills for structure; the sheet frame on the empty state is a 1px line with an inset hairline.
- One rubric per sheet (vermilion / amber) for callouts, the cloud, the selected tab, Download and Decompile; one band-rubric (amber) for the risk figure.
- Zero radius everywhere except the 24px circular callout.
- Barlow Condensed tracked uppercase for every label, heading, tab and action; Barlow for prose; Source Code Pro for code.
- Fixed-cell lists whose columns never move; the chosen line or finding stays lit until another is chosen.
- A scalloped revision cloud outlines every flagged line of the drawing.

## Colors

An ink band over two monochrome sheets, each sheet with one rubric and a graded severity set; colour carries meaning only where words already carry it.

### Primary
- **Vermilion Rubric** (`vermilion-rubric`, light sheet) / **Amber Rubric** (`amber-rubric`, dark sheet): the sheet-side accent. It draws the callout circle stroke and number, the revision cloud stroke, the 2px selected-tab underline, the Download .sol label, the error border and lead word, the emphasised half of the landing headline, and the fill of the Decompile button (text in `on-rubric-light` / `on-rubric-dark`). The hover-filled callout inverts to the same pair.
- **Band Amber** (`band-amber`): the band-side rubric in both themes; the risk figure at a score of 8 or above and the focus ring on every band control (2px, inset 3px).
- **Focus Blue** (`focus-blue`, light sheet): the 2px focus-visible outline, offset 2px, on sheet controls. The dark sheet reuses the amber rubric for focus.

### Severity
Severity is always printed as a word (CRITICAL, HIGH, MEDIUM, LOW, INFO; condensed 12px, 600, tracked 0.1em uppercase) and the colour only tints that word. Light: `severity-critical`, `severity-high` (identical to the rubric), `severity-medium`, `severity-low`, `severity-info` (identical to muted text). Dark: `severity-critical-dark`, `severity-high-dark`, `severity-medium-dark` (identical to the amber rubric), `severity-low-dark`, `severity-info-dark`. The finding's confidence is always printed beside the severity in the meta line.

### Neutral
Band (both themes):
- **Band Ink** (`band-ink`) / **Band Ink (dark)** (`band-ink-dark`): the header strip, the title block and the chain select ground.
- **Band Pale** (`band-pale`): all band type, the wordmark, the theme toggle, select text and the chevron stroke.
- **Band Muted** (`band-muted`): title-block labels and the query placeholder.
- **Band Rule** (`band-rule`) / **Band Rule (dark)** (`band-rule-dark`): the 1px rules between header cells and title-block cells; the 2px rule closing the title block.
- **Field Ink** (`field-ink`) / **Field Ink (dark)** (`field-ink-dark`): the query field ground and the theme toggle's hover fill.

Sheet:
- **Sheet White** (`sheet-white`) / **Prussian Ground** (`prussian-ground`): the drawing, details column, index rows, filter field, sticky tab strip and callout fill.
- **Iron Black** (`iron-black`) / **Pale Line** (`pale-line`): all sheet type and the keyword, type, number and function-name tokens in code (code is mostly ink-coloured on purpose).
- **Graphite Muted** (`graphite-muted`) / **Dusk Muted** (`dusk-muted`): column headings, group headings, sheet numbers, line numbers, mutability, meta lines, comments in code, unselected tabs, report headings and table headers, the landing paragraph and footer.
- **Rule Line** (`rule-line`) / **Blueprint Line** (`blueprint-line`): the heavy 1px rule between regions: the three column borders, column headings, tab strip, the sheet frame, outline buttons.
- **Rule Hair** (`rule-hair`) / **Blueprint Hair** (`blueprint-hair`): the light 1px rule inside a region: index rows, tab dividers, scale line, findings, report tables, the inset frame line, the landing footer rule.
- **Well Grey** (`well-grey`) / **Blueprint Well** (`blueprint-well`): the function index column ground, hovered rows and tabs, flagged code lines, evidence wells.
- **Lit Straw** (`lit-straw`) / **Lit Umber** (`lit-umber`): the lit state; the current sheet in the index, the chosen code line, the chosen finding.
- **Selection Blue** (`selection-blue`) / **Blueprint Selection** (`blueprint-selection`): text selection only.
- **Code String Green** (`code-string-green` / `code-string-green-dark`): string literals, the only hue inside the code besides ink and muted.

### Named Rules
**The One Rubric Rule.** Each sheet has exactly one accent and it marks only what a reviewer would mark in red: the callout, the cloud, the selected tab's rule, the download and decompile actions, an error. The band has its own single accent, amber, for the risk figure and band focus. Nothing decorative wears either.

**The Words First Rule.** Severity and risk are read from the printed word (HIGH, 76/100 · High); the colour tints the word and never stands alone. A risk score under 8 drops the band rubric and prints in band pale at Barlow 500 14px.

**The Two Sheets Rule.** Every sheet token has a whiteprint and a blueprint value, and every pair meets AA contrast on its ground; the band keeps the same pale type on both of its inks. Add a colour to both sheets or to neither.

## Typography

**Display Font:** Barlow Condensed (with Barlow, then the system sans stack)
**Body Font:** Barlow (with `ui-sans-serif, system-ui, "Segoe UI", Roboto, Helvetica, Arial`)
**Label/Mono Font:** Source Code Pro (with `ui-monospace, "SF Mono", Menlo, Consolas, "Liberation Mono"`) for the address field, the function index, the code, selectors, evidence and report code

**Character:** Draughting-room lettering: a condensed grotesque in tracked capitals for everything that names or commands (labels, headings, tabs, actions, the wordmark, the headline), its regular width for reading text, and a clean mono for the drawing. Weight is held between 400 and 700; hierarchy comes from width, case and tracking more than from size. The three families load from Google Fonts with `display=swap`; the system stacks are the fallbacks.

### Hierarchy
- **Display** (condensed 600, 34px, 1.1, 0.01em, uppercase, balanced wrap; 28px under 720px): the landing headline only, inside the framed sheet; its second clause is set in the rubric.
- **Wordmark** (condensed 700, 20px, 1, 0.02em, lowercase): `evmdec` in the first band cell. No logo exists.
- **Risk** (condensed 600, 18px, 1.2, 0.02em, band amber): the risk figure in the title block when the score is 8 or above.
- **Action** (condensed 600, 15px, 1, 0.14em, uppercase): the Decompile button. The chain select is condensed 500 14px 0.04em uppercase; the theme toggle condensed 500 13px 0.06em uppercase.
- **Body** (Barlow 400, 14px, 1.45): UI text, finding titles (500), finding bodies capped at 70ch, landing paragraph capped at 62ch, report prose capped at 90ch; the scale line is 13px.
- **Value** (Barlow 500, 14px, tabular-nums): the title-block value under each label, in band pale.
- **Heading** (condensed 600, 13px, 0.1-0.12em, uppercase, muted): tabs (0.1em), Download .sol (rubric), report section headings (0.12em), outline example buttons (0.08em, ink).
- **Label** (condensed 500-600, 12px, 0.12em, uppercase): title-block labels (500, band muted), column headings and index group headings (600, muted), the landing "Try" and footer line (500, muted, 0.1-0.12em), report table headers (600, 0.08em).
- **Severity** (condensed 600, 12px, 0.1em, uppercase): the severity word in a finding row. Mutability in the index is condensed 500 11px 0.08em uppercase; the sheet number F-nn is condensed 500 12px 0.06em.
- **Meta** (Barlow 400, 12-12.5px, muted): finding meta (function · confidence · sites), "Lines" links.
- **Code** (Source Code Pro 400, 13px, 1.5, tab-size 4): the drawing and pre blocks; the band query field is 14px. Function names in code are 600.
- **Code small** (Source Code Pro 400, 12-12.5px): index rows (12.5px), evidence wells and finding meta code (12px), report code (12.5px).

### Named Rules
**The Tracked Label Rule.** Anything that names a cell, a column, a group, a view or an action is Barlow Condensed in uppercase, tracked 0.08-0.14em, set above or beside its value, and never repeated as a heading elsewhere. Prose is never condensed.

**The Ink Code Rule.** Code is set in ink: keywords, types, numbers and function names share the text colour; only comments drop to muted and strings take green. Emphasis in code is weight (600 function names), not colour.

## Layout

The page is a fixed drawing frame: `body` is a grid of three rows (band header, band title block, main) filling the viewport, and `main` is three columns of 280px (function index on the well), a fluid drawing, and 380px (details). Each column scrolls independently inside the frame; the column heading and the tab strip are sticky at the top of their column on their own ground. The page carries a `data-state`: `empty` collapses the frame to two rows (band, landing) and hides the title block and columns; `loaded` hides the landing and shows them.

The band header is one 44px row of cells divided by band rules: wordmark (padding 0 18px), the address/bytecode field filling the width (mono, 0 14px, on field ink), the chain select (0 32px 0 14px with a 12x8 chevron 12px from the right), the Decompile action (0 22px, rubric fill), and the theme toggle (0 16px, 8px gap to its 16px icon). The title block below is eight equal cells, 7px 14px 9px padding, divided by band rules and closed by a 2px band rule.

The empty state centres a framed sheet (`min(100%, 760px)`, 36px 40px 32px padding, 48px 24px 64px around it): a 1px line border with a hairline inset 6px, the headline, one paragraph, a "Try" row of outline buttons 8px apart, and a tracked footer line above which a hairline rule sits 28px below the examples.

Spacing rhythm is small and even: 2px between callout bubbles, 5-10px row padding vertically, 12px as the standard horizontal inset of every column and row, 14-16px for tabs, band cells and fields, 16px for pre blocks and errors, 24px report inset, 36-48px around the empty sheet. Code lines are a three-column grid: 3.4em line number (right-aligned), 8.6em callout cell, then the code. Index rows are a three-column grid: 3.2em sheet number, name, mutability, gapped 8px, baseline aligned. Finding rows are 30px number, severity, title/meta, gapped 2px 8px; the finding body is inset 50px to clear the callout.

Responsive changes, both observed:
- **1100px and below:** the index narrows to 240px, the details column drops under the index and drawing spanning the full width with a heavy top rule, and the title block becomes four cells per row.
- **720px and below:** the frame unfixes (`body` becomes flow). The band wraps: wordmark full width, field full width, then the chain select and Decompile share a row, then the theme toggle full width. The title block is two cells per row. The three columns stack: index (list capped at 40vh), drawing (panel capped at 70vh, tabs no longer sticky), details, each separated by a heavy rule. The empty sheet tightens to 24px 20px padding with a 28px headline.

**The Fixed Cell Rule.** Index rows, title-block cells, code lines and finding rows are grids with fixed first columns; content never shifts a column. Long names break at `(` and `,` via soft wraps, long addresses break anywhere, but the grid does not move.

## Elevation & Depth

No shadows. Depth is entirely tonal and linear: the band is a darker plane that the sheet hangs beneath, regions are separated by 1px rules (heavy `line` between regions, light `hair` within them), the index column and recessed areas use the `well` fill, and the chosen item uses the `lit` fill. Sticky headings sit on their column ground with a z-index so content passes under a rule, not a shadow. The only box-shadow in the build is the 2px selected-tab underline, drawn with `inset 0 -2px 0` in the rubric as a rule, not a lift. The Decompile button's hover is a brightness step (`filter: brightness(1.08)`), not a lift.

**The Flat Sheet Rule.** Nothing lifts off the sheet. Hierarchy is drawn with planes, rules, fills and weight; a shadow, a glow or a blur is a foreign material.

## Shapes

Right angles everywhere (0px): band cells, title-block cells, buttons, the field, the select, tabs, evidence wells, error boxes, the sheet frame and report tables are all square and bounded by 1px rules. The single curve is the callout: a 24px circle with a 1.5px rubric stroke. The revision cloud that outlines a flagged line is a scalloped border drawn with a 6px `border-image` from an inline 18x18 SVG of eight 3px arcs, repeated `round`, in the sheet's rubric; it spans from the callout cell to the right edge of the line. The chain select is `appearance: none` with a 12x8 stroked chevron drawn as an inline SVG. Lines, not boxes, bound regions; a bordered box appears only for the empty-state sheet frame (line plus inset hairline), outline example buttons, evidence wells, report table cells and the error notice.

## Components

### Buttons
Buttons are cells or line-drawn boxes, never pills; every button has at least a 24x24 target (band controls are 44px tall), and a disabled button shows a progress cursor at 60% opacity.
- **Shape:** square (0px radius).
- **Primary** (Decompile): rubric fill, on-rubric text, condensed 600 15px tracked 0.14em uppercase, padding 0 22px, 44px tall, in the band. Hover brightens by 8%. It is the only filled button.
- **Band cell buttons** (theme toggle): transparent on the band, bounded by a 1px band rule, 0 16px, condensed 500 13px 0.06em uppercase with a 16px half-disc SVG at 1.5px stroke; hover fills with field ink.
- **Tab-strip buttons** (tabs, Download .sol): transparent, bounded by hairlines, condensed 600 13px 0.1em uppercase; Download is set in the rubric at the far right.
- **Outline buttons** (landing examples WETH / USDT / USDC proxy): transparent, 1px line border, 7px 14px, condensed 600 13px 0.08em uppercase; hover fills the well.
- **Row buttons** (index entries, finding headers): full-width grids with a hairline below; hover fills the well; current/lit fills lit.
- **Inline link buttons** (scale line "Show whole contract"): underlined ink text, no box.
- **Focus:** sheet controls take the 2px focus outline at 2px offset; band controls take a 2px amber outline inset 3px.

### Inputs / Fields
- **Style:** square and borderless; the query field is 44px tall on field ink with pale mono 14px text and a band-muted placeholder, bounded by a band rule on the right. The filter field sits on the sheet ground inside the well column, Barlow 13px, 8px 12px, bounded by a hairline below. The chain select is a band-ink cell with condensed uppercase text and the chevron.
- **Focus:** the focus outline only (amber inset on the band, blue/amber offset on the sheet); no border change, no glow.
- **Error:** errors appear as a separate notice (`role=alert`, 12px 14px padding, 1px rubric border, rubric lead word) in the drawing or under the landing examples (18px above), never as a red field.

### Navigation (Tabs)
- **Style:** an ARIA tablist (`role=tablist`, roving `tabindex`, `aria-selected`, `aria-controls`) in a sticky strip closed by a heavy rule; tabs are condensed tracked uppercase in muted ink, 10px 16px, divided by hairlines, horizontally scrollable when narrow; hover turns them ink; Download .sol sits at the far right behind a hairline in the rubric.
- **Selected:** ink text with a 2px rubric underline drawn inset. No fill, no radius.
- **Mobile:** the strip stops being sticky and the panel scrolls within 70vh.

### Band and Title Block
The header strip and title block share the band ink. The title block is eight cells (four at 1100px, two at 720px), each a condensed tracked label in band muted over a Barlow 500 tabular value in band pale, `min-height 1.45em` so empty cells keep their height. The risk cell prints `score/100 · Word` in condensed 600 18px band amber when the score is 8 or above, otherwise in band pale at Barlow 500 14px.

### Empty Sheet (landing)
Shown only in `data-state="empty"`: a centred framed sheet with the uppercase condensed headline (second clause in the rubric), one muted paragraph at 62ch, a "Try" label and three outline example buttons, an error slot, and a hairline-ruled footer of three tracked uppercase claims in muted ink.

### Function Index
A well-ground column: a column heading, the filter field, then group headings (EXTERNAL · n, INTERNAL · n) in condensed tracked uppercase and lists of fixed-cell rows on the sheet ground: sheet number F-nn in condensed muted, mono name at 12.5px, mutability in condensed 11px uppercase muted. Hover fills the well; the current function is lit with its name at 600 (`aria-current="true"`).

### Drawing (code) and the Scale Line
A scale line under the tabs (13px muted, 600 ink for the emphasised terms, underlined inline button to show the whole contract) names what is shown: whole contract or a function and its helpers with line ranges, the flagged-line count, and "Callouts key to the details at right". Code lines are counter-numbered; a flagged line takes the well fill, 6px vertical padding, and the revision cloud; its callout cell holds 24px circles numbered to the findings. A chosen line is lit.

### Callout (signature)
A 24px circle, 1.5px rubric stroke, rubric number in condensed 600 12px on the sheet ground, 2px apart when several share a line. Hover inverts it (rubric fill, on-rubric number). It is an anchor to `#Fn` with an `aria-label` naming the finding. Activating a callout or the matching finding lights both, scrolls the other into view and announces "Finding n: title" through the polite live region; a "Lines" link announces "Line n" and focuses the callout.

### Findings (details)
An ordered list of rows separated by hairlines: a callout circle (the same key), the severity word in its severity colour, the title at 500, and a meta line (function · confidence · sites) in 12.5px muted. The row button is an `aria-expanded` disclosure that fills the well on hover; the open body (inset 50px) holds prose capped at 70ch, evidence wells (well fill, hairline border, 12px mono, pre-wrapped), a bold "Recommendation." lead, and "Lines" links with 24px targets back to the drawing. The first finding opens by default; a chosen finding is lit.

### Report tables
Condensed tracked uppercase section headings (13px, muted) and table headers (12px); hairline-bordered cells, 4px 8px padding, tabular figures, 13px; lists are hairline-separated rows with 3px vertical padding.

### Motion and state
One transition exists: `background .2s ease-out` on code lines and findings, declared only under `prefers-reduced-motion: no-preference`. Hover on rows, tabs, callouts, the toggle and the primary is instantaneous. The lit state persists until another line or finding is chosen. The theme toggle sets `data-theme` on the root, persists it to localStorage and announces the change; `aria-busy` is set on the body while decompiling and the status region announces start and result.

## Do's and Don'ts

### Do:
- **Do** keep the header strip and title block on the band ink with pale type and band rules; the sheet below is the only place the theme ground changes.
- **Do** divide regions with 1px rules: `line` between regions, `hair` within them, `band-rule` inside the band; a region's boundary is a rule, never a fill or a shadow.
- **Do** set every label, heading, tab and action in Barlow Condensed uppercase tracked 0.08-0.14em, and label each thing once; set prose and values in Barlow, code in Source Code Pro.
- **Do** keep the sheet rubric for callouts, the revision cloud, the selected-tab rule, Download, Decompile and error borders (vermilion on the light sheet, amber on the dark), and band amber for the risk figure and band focus.
- **Do** print severity and confidence as words beside each other; colour only tints the severity word.
- **Do** give every control at least a 24x24 target (44px in the band) and a visible 2px focus outline; use `aria-current`, `aria-expanded`, `aria-selected`, `aria-pressed`, `aria-busy` and the polite `role=status` region for every state change.
- **Do** define any new sheet colour on both sheets and verify AA contrast on each ground, and on the band ink for band colours.
- **Do** use the lit fill (straw / umber) for exactly the chosen item: one index row, one code line, one finding.

### Don't:
- **Don't** add border-radius to anything but the 24px callout circle; buttons, fields, the select, tabs, wells, frames and notices stay square.
- **Don't** add box-shadows, glows, blurs or gradients; the only inset shadow is the 2px selected-tab underline used as a rule, and the only hover filter is the primary's 8% brightness step.
- **Don't** set prose, finding bodies or values in the condensed face, and don't set labels in Barlow regular; width and case carry the hierarchy.
- **Don't** colour code tokens beyond ink, muted comments and green strings, or convey emphasis in code with colour instead of weight.
- **Don't** let a column move: fixed first cells (3.4em line numbers, 8.6em callout cell, 3.2em sheet number, 30px finding number) hold their width regardless of content.
- **Don't** animate anything but the lit background (200ms ease-out), and never under reduced motion.
- **Don't** introduce badges, pills, side navigation or a grey-slate console; the band is navy ink and the dark sheet is Prussian blue, not grey.
