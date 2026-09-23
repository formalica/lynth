# `Test/Grind/` — upstream grind tests adapted to `lynth_grind`

Provenance: every `*.lean` here is copied from the Lean 4 toolchain
repository (`lean4/tests/elab/grind_*.lean`, `lean4/tests/lean/grind/`,
v4.34.0) and mechanically adapted. `MANIFEST.txt` records the
source path of each file and why skipped files were skipped.

Layout: `Fast/` (~285 files, ≤10s each) and `Slow/` (~8 files, >10s
each, by measured wall-clock). The 8 skipped-failing files (7 heavy
algebra files where core `grind` fails identically in-repo, plus the
`exact?`-integration test) are documented in `MANIFEST.txt`, not
present here.

## Adaptation rules (`/tmp/opencode/adapt_grind_tests.py` logic)

- `import Lynth.Grind.Tactic` prepended (provides `lynth_grind` syntax);
  the upstream bare `module` header is dropped (old-system, like `Test/*`).
- Tactic invocations renamed: `grind` → `lynth_grind`, `grind?` →
  `lynth_grind?` (word-boundary, outside strings/comments only).
- Deliberately NOT renamed (the tactic delegates to the core engine,
  so core-side state still applies): `@[grind …]` attributes (including
  compound forms like `[local simp, grind]` — any `grind` inside `[…]`),
  `trace[grind.…]` and expected trace texts (`[grind.beta]` inside
  `#guard_msgs` docstrings), `set_option grind.…`, `grindSeq`/
  `grindParam`/`grindMod` parser names, `` `grind` `` message text,
  `Grind.*` namespaces.
- Everything is old-system (bare `module` headers stripped;
  `public`/`meta` imports downgraded to plain imports): new-system
  files cannot import our old-system `Lynth.*` modules.
- Excluded: files using `sorry` (repo ban on sorry fixtures),
  `grind!`/`grind!?` (no `lynth_grind!` tactic), the `sym` tactic and
  other grind-family tactics (`grind_order`, …), Mathlib imports,
  `#exit` stubs (disabled upstream).

## Running

Each file must exit 0 under
`lake env lean -Dlinter.all=false -DElab.inServer=true Test/Grind/Fast/<file>.lean`
(same for `Slow/`; the upstream harness flags; warnings/info output is
fine, it is not diffed — upstream `.out.expected` files are not copied).
One-liners:
`for f in Test/Grind/Fast/*.lean; do timeout 300 lake env lean -Dlinter.all=false -DElab.inServer=true "$f" >/dev/null 2>&1 && echo "PASS $f" || echo "FAIL $f"; done`
(same with `Test/Grind/Slow/`).
Files that fail are removed from this directory (see MANIFEST for the take list, not a fail list).

## Fidelity note

Since `lynth_grind` currently delegates to the core engine, these
tests pin `lynth_grind` ≡ `grind` behavior on the adapted corpus.
They do not exercise our `@[lynth_grind]` attribute DB (kept as core
`@[grind]` here) — bridging that DB is tracked separately.

## Regenerating

Re-running the adapt script writes all files to `Test/Grind/` top
level (flat); move them back into `Fast/`/`Slow/` by the >10s rule and
re-apply the four `PINNED` expected-text fixes from `MANIFEST.txt`.
