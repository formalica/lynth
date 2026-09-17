# lynth loop prompt (used by the idle `/loop`; keep in sync with TASKS.md)

Read SPEC.md first — it sets the direction; do not lose it. Then read
TASKS.md Loop driver and check `git log --oneline` (committed items are
done). Implement the next unfinished TASKS.md item (lowest number with
no corresponding commit), one task only.

Rules: no `sorry`, no `axiom`; tested proofs with native-axioms-only
`#print axioms` checks (propext, Classical.choice, Quot.sound);
update docs/PROCEDURES.md registry and the CI suite list when adding
tests; update progress.md (move the item to Done, point Next at the
following item). Verify with `lake build` plus every Test/*.lean suite
exiting 0. Commit when green with a short message; report what was done,
test results, and what remains open. Then stop and wait for the next
idle tick.
