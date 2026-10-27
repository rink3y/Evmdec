---
name: evmdec
description: An EVM contract's drawing set; the code is the drawing, findings are keyed callouts, metadata sits in a title block.
colors:
  sheet-white: "#ffffff"
  iron-black: "#1a1d21"
  graphite-muted: "#5a6069"
  rule-line: "#b9bec5"
  rule-hair: "#dcdfe3"
  well-grey: "#f5f6f7"
  vermilion-rubric: "#b3261e"
  on-rubric-light: "#ffffff"
  focus-blue: "#0b57d0"
  selection-blue: "#dbe8ff"
  lit-straw: "#fff1c2"
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
  severity-critical-dark: "#ff8e86"
  severity-high-dark: "#ff9d93"
  severity-medium-dark: "#ffd27a"
  severity-low-dark: "#8ec5ff"
  severity-info-dark: "#a9bbd3"
  code-string-green-dark: "#b7e3a0"
typography:
  display:
    fontFamily: "ui-sans-serif, system-ui, \"Segoe UI\", Roboto, Helvetica, Arial, sans-serif"
    fontSize: "24px"
    fontWeight: 700
    lineHeight: 1.25
    letterSpacing: "normal"
  wordmark:
    fontFamily: "ui-sans-serif, system-ui, \"Segoe UI\", Roboto, Helvetica, Arial, sans-serif"
    fontSize: "18px"
    fontWeight: 700
    letterSpacing: "-0.01em"
  title:
    fontFamily: "ui-sans-serif, system-ui, \"Segoe UI\", Roboto, Helvetica, Arial, sans-serif"
    fontSize: "15px"
    fontWeight: 600
    lineHeight: 1.45
  body:
    fontFamily: "ui-sans-serif, system-ui, \"Segoe UI\", Roboto, Helvetica, Arial, sans-serif"
    fontSize: "14px"
    fontWeight: 400
    lineHeight: 1.45
  label:
    fontFamily: "ui-sans-serif, system-ui, \"Segoe UI\", Roboto, Helvetica, Arial, sans-serif"
    fontSize: "11px"
    fontWeight: 400
    letterSpacing: "0.08em"
  severity:
    fontFamily: "ui-sans-serif, system-ui, \"Segoe UI\", Roboto, Helvetica, Arial, sans-serif"
    fontSize: "12px"
    fontWeight: 700
    letterSpacing: "0.06em"
  code:
    fontFamily: "ui-monospace, \"SF Mono\", Menlo, Consolas, \"Liberation Mono\", monospace"
    fontSize: "13px"
    fontWeight: 400
    lineHeight: 1.5
  code-small:
    fontFamily: "ui-monospace, \"SF Mono\", Menlo, Consolas, \"Liberation Mono\", monospace"
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
  xxl: "32px"
components:
  button-primary:
    backgroundColor: "{colors.iron-black}"
    textColor: "{colors.sheet-white}"
    typography: "{typography.body}"
    rounded: "{rounded.none}"
    padding: "0 18px"
  button-outline:
    backgroundColor: "transparent"
    textColor: "{colors.iron-black}"
    typography: "{typography.body}"
    rounded: "{rounded.none}"
    padding: "6px 12px"
  button-cell:
    backgroundColor: "transparent"
    textColor: "{colors.iron-black}"
    typography: "{typography.body}"
    rounded: "{rounded.none}"
    padding: "0 14px"
  input-query:
    backgroundColor: "transparent"
    textColor: "{colors.iron-black}"
    typography: "{typography.code}"
    rounded: "{rounded.none}"
    padding: "10px 14px"
  input-filter:
    backgroundColor: "transparent"
    textColor: "{colors.iron-black}"
    typography: "{typography.body}"
    rounded: "{rounded.none}"
    padding: "8px 12px"
  tab:
    backgroundColor: "transparent"
    textColor: "{colors.graphite-muted}"
    typography: "{typography.body}"
    rounded: "{rounded.none}"
    padding: "9px 14px"
  tab-selected:
    backgroundColor: "transparent"
    textColor: "{colors.iron-black}"
  callout:
    backgroundColor: "{colors.sheet-white}"
    textColor: "{colors.vermilion-rubric}"
    rounded: "{rounded.callout}"
    size: "24px"
  callout-hover:
    backgroundColor: "{colors.vermilion-rubric}"
    textColor: "{colors.on-rubric-light}"
  title-block-cell:
    backgroundColor: "{colors.sheet-white}"
    textColor: "{colors.iron-black}"
    typography: "{typography.body}"
    rounded: "{rounded.none}"
    padding: "6px 12px"
  index-row:
    backgroundColor: "transparent"
    textColor: "{colors.iron-black}"
    typography: "{typography.code-small}"
    rounded: "{rounded.none}"
    padding: "5px 12px"
  index-row-current:
    backgroundColor: "{colors.lit-straw}"
  finding-row:
    backgroundColor: "transparent"
    textColor: "{colors.iron-black}"
    typography: "{typography.body}"
    rounded: "{rounded.none}"
    padding: "8px 12px"
  finding-row-lit:
    backgroundColor: "{colors.lit-straw}"
  evidence-well:
    backgroundColor: "{colors.well-grey}"
    textColor: "{colors.iron-black}"
    typography: "{typography.code-small}"
    rounded: "{rounded.none}"
    padding: "6px 10px"
---

# Design System: evmdec

<!-- World: "Drawing set". Direction seed: seed:67b4e9518045227d. Recorded from the shipped page crates/server/static/index.html after the finish review (disposition: ship). -->

## Overview

**Creative North Star: "The Drawing Set"**

The contract is a built structure and the page is its drawing set. Metadata lives in a title block of eight labelled cells across the top; functions are an indexed sheet list (F-01, F-02, ...) down the left; the decompiled code is the drawing in the middle; every finding is a numbered callout in the code gutter keyed to a detail at the right. The world refuses the category's console (side nav, dark slate, badges) and the report-PDF arrangement. Everything is drawn in line: one-pixel rules divide every region, nothing has a shadow, nothing has a radius except the callout circles, and nothing is labelled twice.

Two sheets exist. In light the page is a whiteprint: a white sheet, iron-black line and type, one vermilion rubric reserved for callouts, the risk figure and the error border. In dark it is a blueprint: Prussian-blue ground, pale line and type, an amber rubric in the same reserved role. The theme follows the system and can be overridden by the header toggle; both sheets meet WCAG 2.2 AA including the code highlighting and the severity colours.

Density is that of a drawing, not a dashboard: 14px body on a 1.45 line, 13px mono code on a 1.5 line, tracked 11px uppercase labels over tabular values, 12px meta. The interface stays out of the way so the code, the findings and the layout are read at reading quality. The only motion is the lit background settling in over 200ms; nothing else moves, and reduced motion removes even that.

**Key Characteristics:**
- Hairline rules at 1px divide every region; no shadows, no fills for structure.
- One rubric colour per sheet (vermilion / amber), used only for callouts, the risk figure and errors.
- Zero radius everywhere except the 24px circular callout.
- Tracked uppercase 11px labels over 500-weight tabular values.
- System sans for UI, system mono for code, selectors and evidence; no external fonts or scripts.
- Fixed-cell lists whose columns never move; the chosen line or finding stays lit until another is chosen.
- A scalloped revision cloud outlines every flagged line of the drawing.

## Colors

Two monochrome sheets, each with one rubric and a graded severity set; colour carries meaning only where words already carry it.

### Primary
- **Vermilion Rubric** (`vermilion-rubric`, light) / **Amber Rubric** (`amber-rubric`, dark): the single accent. It draws the callout circle stroke and number, the revision cloud stroke, the risk figure when the score is 8 or above, and the error box border. The hover-filled callout uses `on-rubric-light` / `on-rubric-dark` for its number.
- **Focus Blue** (`focus-blue`, light): the 2px focus-visible outline, offset 2px, on every control. In dark the focus outline reuses the amber rubric.

### Severity
Severity is always printed as a word (CRITICAL, HIGH, MEDIUM, LOW, INFO; 12px, 700, tracked uppercase) and the colour only tints that word. Light: `severity-critical`, `severity-high` (identical to the rubric), `severity-medium`, `severity-low`, `severity-info` (identical to muted text). Dark: `severity-critical-dark`, `severity-high-dark`, `severity-medium-dark` (identical to the amber rubric), `severity-low-dark`, `severity-info-dark`. The finding's confidence is always printed beside the severity in the meta line, never omitted.

### Neutral
- **Sheet White** (`sheet-white`) / **Prussian Ground** (`prussian-ground`): the page and every sticky header and callout fill.
- **Iron Black** (`iron-black`) / **Pale Line** (`pale-line`): all type, the primary button fill, the selected-tab underline, and the keyword, type, number and function-name tokens in code (code is mostly ink-coloured on purpose).
- **Graphite Muted** (`graphite-muted`) / **Dusk Muted** (`dusk-muted`): labels, column headings, group headings, sheet numbers, line numbers, mutability, meta lines, comments in code, unselected tabs, placeholder-tier text.
- **Rule Line** (`rule-line`) / **Blueprint Line** (`blueprint-line`): the heavy 1px rule between regions: header, title block, the three column borders, tab strip, outline buttons.
- **Rule Hair** (`rule-hair`) / **Blueprint Hair** (`blueprint-hair`): the light 1px rule inside a region: title-block cells, index rows, tab dividers, scale line, findings, report tables.
- **Well Grey** (`well-grey`) / **Blueprint Well** (`blueprint-well`): a recessed fill for group headings, hovered index rows, flagged code lines and evidence wells.
- **Lit Straw** (`lit-straw`) / **Lit Umber** (`lit-umber`): the lit state; the current sheet in the index, the chosen code line, the chosen finding.
- **Selection Blue** (`selection-blue`) / **Blueprint Selection** (`blueprint-selection`): text selection only.
- **Code String Green** (`code-string-green` / `code-string-green-dark`): string literals, the only hue inside the code besides ink and muted.

### Named Rules
**The One Rubric Rule.** Each sheet has exactly one accent and it marks only what a reviewer would mark in red: the callout, the cloud, the risk figure, an error. Nothing decorative, no links, no buttons wear it.

**The Words First Rule.** Severity and risk are read from the printed word (HIGH, 76/100 · High); the colour tints the word and never stands alone. A risk score under 8 drops the rubric and prints in ink at weight 500.

**The Two Sheets Rule.** Every token has a whiteprint and a blueprint value, and every pair meets AA contrast on its ground. Add a colour to both sheets or to neither.

## Typography

**Display Font:** system sans (`ui-sans-serif, system-ui, "Segoe UI", Roboto, Helvetica, Arial`)
**Body Font:** the same system sans
**Label/Mono Font:** system mono (`ui-monospace, "SF Mono", Menlo, Consolas, "Liberation Mono"`) for the address field, the function index, the code, selectors, evidence and report code

**Character:** Draughting-room lettering: one sans at a small number of sizes, weight carrying the hierarchy, small tracked capitals for every label, tabular figures for every number. No external fonts are loaded; the page renders in whatever the system draws.

### Hierarchy
- **Display** (700, 24px, 1.25, balanced wrap): the landing headline only, inside the empty drawing area.
- **Wordmark** (700, 18px, -0.01em): `evmdec`, lowercase, one word, in the first header cell. No logo exists.
- **Title** (600, 15px): report section headings. Scale-line emphasis and the primary button use 600 at body size.
- **Body** (400, 14px, 1.45): UI text, finding titles, finding bodies capped at 70ch, landing copy capped at 70ch, report prose capped at 90ch.
- **Value** (500, 14px, tabular-nums): the title-block value under each label; the risk value is 700 in rubric.
- **Label** (400 or 600, 11px, 0.08em, uppercase, muted): title-block labels, column headings (600), index group headings.
- **Severity** (700, 12px, 0.06em, uppercase): the severity word in a finding row.
- **Meta** (400, 12px, muted): the scale line, finding meta (function · confidence · sites), status text, "Lines" links.
- **Code** (400, 13px, 1.5, tab-size 4): the drawing, pre blocks and the address field. Function names in code are 600.
- **Code small** (400, 12px): the function index rows, evidence wells, finding meta code; report code is 12.5px.

### Named Rules
**The Tracked Label Rule.** Anything that names a cell is 11px uppercase tracked 0.08em in muted ink, set above its value, and never repeated as a heading elsewhere.

**The Ink Code Rule.** Code is set in ink: keywords, types, numbers and function names share the text colour; only comments drop to muted and strings take green. Emphasis in code is weight (600 function names), not colour.

## Layout

The page is a fixed drawing frame: `body` is a grid of three rows (header strip, title block, main) filling the viewport, and `main` is three columns of 280px (function index), a fluid drawing, and 380px (details). Each column scrolls independently inside the frame; the column heading and the tab strip are sticky at the top of their column on the page background.

The header strip is one row of cells divided by heavy rules: wordmark (padding 0 16px), the address/bytecode field filling the width (mono, 10px 14px), chain select (0 12px, max 40vw), the Decompile primary (0 18px), and the theme toggle (0 14px, 8px gap to its icon). The title block below it is eight equal cells, 6px 12px padding, divided by hairlines; the whole block is closed by a heavy rule.

Spacing rhythm is small and even: 2px between callout bubbles, 5-9px row padding vertically, 12px as the standard horizontal inset of every column and cell, 14px for tabs and the field, 16px for pre blocks, errors and brand, 24px report inset, 32-48px landing padding. Code lines are a three-column grid: 3.4em line number (right-aligned), 8.6em callout cell, then the code. Index rows are a three-column grid: 3.2em sheet number, name, mutability, gapped 8px, baseline aligned. Finding rows are 30px number, severity, title/meta, gapped 2px 8px; the finding body is inset 50px to clear the callout.

Responsive changes, both observed:
- **1100px and below:** the index narrows to 240px, the details column drops under the index and drawing spanning the full width with a heavy top rule, and the title block becomes four cells per row.
- **720px and below:** the frame unfixes (`body` becomes flow). The header wraps: wordmark full width, field full width, then chain select and Decompile share a row, then the theme toggle full width. The title block is two cells per row. The three columns stack: index (list capped at 40vh), drawing (panel capped at 70vh, tabs no longer sticky), details, each separated by a heavy rule.

**The Fixed Cell Rule.** Index rows, title-block cells, code lines and finding rows are grids with fixed first columns; content never shifts a column. Long names break at `(` and `,` via soft wraps, long addresses break anywhere, but the grid does not move.

## Elevation & Depth

No shadows. Depth is entirely tonal and linear: regions are separated by 1px rules (heavy `line` between regions, light `hair` within them), recessed areas use the `well` fill, and the chosen item uses the `lit` fill. Sticky headings sit on the page background with a z-index so content passes under a rule, not a shadow. The only inset shadow in the build is the 2px selected-tab underline, drawn with `inset 0 -2px 0` in ink as a rule, not a lift.

**The Flat Sheet Rule.** Nothing lifts off the sheet. Hierarchy is drawn with rules, fills and weight; a shadow, a glow or a blur is a foreign material.

## Shapes

Right angles everywhere (0px): header cells, title-block cells, buttons, inputs, tabs, evidence wells, error boxes and report tables are all square and bounded by 1px rules. The single curve is the callout: a 24px circle with a 1.5px rubric stroke. The revision cloud that outlines a flagged line is a scalloped border drawn with a 6px `border-image` from an inline 18x18 SVG of eight 3px arcs, repeated `round`, in the sheet's rubric; it spans from the callout cell to the right edge of the line. Lines, not boxes, bound regions; a bordered box appears only for the outline example buttons, evidence wells, report table cells and the error notice.

## Components

### Buttons
Buttons are cells or line-drawn boxes, never pills; every button has at least a 24x24 target, and a disabled button shows a progress cursor at 60% opacity.
- **Shape:** square (0px radius).
- **Primary** (Decompile): ink fill, page-colour text, 600 weight, padding 0 18px, full header-row height. It is the only filled button.
- **Cell buttons** (theme toggle, Download .sol, tabs): transparent, bounded by a 1px rule on one side, padding 0 14px; the theme toggle carries a 16px half-disc SVG at 1.5px stroke followed by its label.
- **Outline buttons** (landing examples WETH / USDT / USDC (proxy)): transparent, 1px heavy-rule border, padding 6px 12px, 600 weight.
- **Row buttons** (index entries, finding headers): full-width transparent grids with a hairline below; hover fills the well; current/lit fills lit.
- **Hover / Focus:** the primary and cell buttons have no hover change; focus is the 2px focus outline at 2px offset on every control.

### Inputs / Fields
- **Style:** borderless on three sides, transparent, bounded only by the cell's 1px rule (right rule in the header, bottom hairline in the index). The query field is mono 13px with 10px 14px padding; the filter is body sans with 8px 12px padding. Placeholders are plain text.
- **Focus:** the 2px focus outline, no border change, no glow.
- **Error:** errors appear as a separate notice (16px margin, 12px 14px padding, 1px rubric border, rubric-coloured lead word), never as a red field.

### Navigation (Tabs)
- **Style:** an ARIA tablist (`role=tablist`, roving `tabindex`, `aria-selected`, `aria-controls`) in a sticky strip closed by a heavy rule; tabs are muted text, 9px 14px padding, divided by hairlines, horizontally scrollable when narrow; Download .sol sits at the far right behind a hairline.
- **Selected:** ink text with a 2px ink underline drawn inset. No fill, no radius.
- **Mobile:** the strip stops being sticky and the panel scrolls within 70vh.

### Title Block
Eight cells in one row (four at 1100px, two at 720px), each a tracked label over a 500-weight tabular value with `min-height 1.45em` so empty cells keep their height. The risk cell prints `score/100 · Word` in rubric at 700 when the score is 8 or above, otherwise in ink at 500. Empty state reads "No sheet loaded" in the sheet cell with the rest blank.

### Function Index
A column heading, a filter field, then group headings (EXTERNAL · n, INTERNAL · n) in well fill and lists of fixed-cell rows: sheet number F-nn in muted, mono name, mutability in 11px sans muted. The current function is lit with its name at 700 (`aria-current="true"`).

### Drawing (code) and the Scale Line
A scale line under the tabs (12px muted, 600 ink for the emphasised terms) names what is shown: whole contract or a function and its helpers with line ranges, the flagged-line count, and "Callouts key to the details at right". Code lines are counter-numbered; a flagged line takes the well fill, 6px vertical padding, and the revision cloud; its callout cell holds 24px circles numbered to the findings. A chosen line is lit.

### Callout (signature)
A 24px circle, 1.5px rubric stroke, rubric number at 600 11px sans on the page fill, 2px apart when several share a line. Hover inverts it (rubric fill, on-rubric number). It is an anchor to `#Fn` with an `aria-label` naming the finding. Activating a callout or the matching finding lights both, scrolls the other into view and announces "Finding n: title" through the polite live region.

### Findings (details)
An ordered list of rows separated by hairlines: a callout circle (the same key), the severity word in its severity colour, the title, and a meta line (function · confidence · sites) in 12px muted. The row button is an `aria-expanded` disclosure; the open body (inset 50px) holds prose capped at 70ch, evidence wells (well fill, hairline border, 12px mono, pre-wrapped), a bold "Recommendation." lead, and "Lines" links with 24px targets back to the drawing. The first finding opens by default; a chosen finding is lit.

### Report tables
Hairline-bordered cells, 4px 8px padding, tabular figures, muted 600 headers, 13px; lists are hairline-separated rows with 3px vertical padding.

### Motion and state
One transition exists: `background .2s ease-out` on code lines and findings, declared only under `prefers-reduced-motion: no-preference`. Hover on index rows, tabs and callouts is instantaneous. The lit state persists until another line or finding is chosen.

## Do's and Don'ts

### Do:
- **Do** divide regions with 1px rules: `line` between regions, `hair` within them; a region's boundary is a rule, never a fill or a shadow.
- **Do** set every label at 11px uppercase tracked 0.08em in muted ink above a 500-weight tabular value, and label each thing once.
- **Do** keep the rubric for callouts, the revision cloud, the risk figure at 8 or above, and error borders; the light sheet uses vermilion, the dark sheet amber.
- **Do** print severity and confidence as words beside each other; colour only tints the severity word.
- **Do** give every control at least a 24x24 target and the 2px offset focus outline; use `aria-current`, `aria-expanded`, `aria-selected` and the polite `role=status` region for every state change.
- **Do** define any new colour on both sheets and verify AA contrast on each ground.
- **Do** use the lit fill (straw / umber) for exactly the chosen item: one index row, one code line, one finding.

### Don't:
- **Don't** add border-radius to anything but the 24px callout circle; buttons, inputs, tabs, wells and notices stay square.
- **Don't** add box-shadows, glows, blurs or gradients; the only inset shadow is the 2px selected-tab underline used as a rule.
- **Don't** load external fonts, icon fonts or scripts; type is the system sans and system mono stacks, and icons are inline SVG at 16px.
- **Don't** colour code tokens beyond ink, muted comments and green strings, or convey emphasis in code with colour instead of weight.
- **Don't** let a column move: fixed first cells (3.4em line numbers, 8.6em callout cell, 3.2em sheet number, 30px finding number) hold their width regardless of content.
- **Don't** animate anything but the lit background (200ms ease-out), and never under reduced motion.
- **Don't** introduce badges, pills, side navigation or a dark-slate console; the dark sheet is Prussian blue, not grey.
