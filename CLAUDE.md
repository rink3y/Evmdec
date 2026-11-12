# Working in this repository

## Comments

These rules apply to everything written here: code, scripts, settings and config files.

1. Write as few comments as possible. If the code is clear without one, write none.

2. A comment may only explain WHY. That means one of three things:
   - the reason behind a choice
   - a warning about something that could break
   - a workaround, or a line that looks wrong but is there on purpose

3. Never write a comment that describes what the code does. The code already shows that.

4. Before leaving a comment, ask: does this stop a future mistake? If not, delete it.

5. No documentation comments on functions, classes or files unless asked for them.

6. Write comments the way a developer jots them down. Short plain sentences.
   Never use a semicolon in a comment. If a comment wants one, split it into two sentences.

7. Use whatever comment syntax the file's format provides. If it has a multi-line form, use
   it for blocks. If it has none, repeat the single-line form on each line.

8. In settings and config files, put no comments between the settings. Each section gets one
   comment block above it, laid out like this:

   ```
   ---------------------------------------------------------------
   Section name: what this section is for

     firstSetting    what it controls
     secondSetting   what it controls
   ---------------------------------------------------------------
   ```

   A dashed line opens and closes the block. The title comes first. Each setting gets one
   short line, with the descriptions lined up.

Good comments:

    The service returns prices as text to keep their exact decimals.
    Retrying here would charge the customer twice.

Bad comments:

    Loop through the items and add up the total.
    The service has no bulk request; items are sent one at a time.

The first bad one describes what the code does. The second is only wrong because of the
semicolon. As two sentences it would be fine.

Text a program shows its user, such as command-line help, is not a comment. In Rust it goes in
a `#[arg(help = ...)]` or `#[command(about = ...)]` attribute, never in a `///` doc comment.
