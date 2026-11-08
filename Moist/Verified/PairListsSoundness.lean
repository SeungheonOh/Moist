import Moist.Verified.PairListsSoundness.Walk

/-! # Destructuring entries of lists of data pairs

`destructurePairEntries` first binds the head of a list `case` alternative
twice (`prepareHeads`, a pure duplication of a variable), then, on lists known
to hold builtin data pairs (results of `unMapData`, tails of such lists, and
recursive parameters every call of which passes such lists), rewrites the
alternative to `case` on the head, replacing `fstPair h`/`sndPair h` by the
pair components (`pairListWalk_rel`). `destructurePairEntries_refines` states
that the pass refines its input under every builtin semantics variant.
-/
