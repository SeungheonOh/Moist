import Moist.Smt.Syntax
import Moist.Plutus.Types

/-! # The Lean *meaning* of `SmtExpr` (`evalSmt`)

This is the semantic anchor of the whole development: the deep-embedded `SmtExpr` is given
a Lean meaning by `evalSmt`, and **every** correctness theorem (adequacy, `validator_sound`)
is stated against `evalSmt` / `Unsat`.  The accepted trust compromise (`z3_sound`,
`Moist/Smt/Print.lean`) is the single bridge from z3's textual verdict to `Unsat`, i.e. to
this meaning.

`evalSmt` is deliberately **total** (`Model → SmtExpr → SVal`, no `Option`).  Ill-sorted
nodes evaluate to the junk value `SVal.bad`; this never happens on compiler output (which
is well-sorted by construction, `SmtExpr.sortOf … = some _`) but keeps the concretization
`γ` total and the adequacy proof a clean equation.  The integer division/modulo operators
are **total** here (Lean's `Int.fdiv x 0 = 0` etc.); their genuine Plutus partiality
(`y = 0` ⇒ error) is carried *separately* as a definedness guard in `SymOut.defined`, never
as a partial meaning — that separation (`defined ∧ value`) is what keeps queries in base
sorts (§2.3 of the plan).
-/

namespace Moist.Smt

open Moist.Plutus (Data ByteString)

/-- Semantic values: the Lean model domain `evalSmt` maps into.  Mirrors the `Const` cases
    reachable in the supported fragment (`Integer`, `Bool`, `Data`, `ByteString`).  `bad` is
    the junk element for ill-sorted expressions (unreachable on compiler output). -/
inductive SVal
  | I   : Int → SVal
  | B   : Bool → SVal
  | D   : Data → SVal
  | BS  : ByteString → SVal
  -- structured builtin values: a `pair` and a (homogeneous) `list`
  | P   : SVal → SVal → SVal
  | L   : List SVal → SVal
  | bad : SVal
deriving Repr, BEq, Inhabited

/-- The canonical sort-correct junk value of a sort (used by total projections — e.g. `head`
    of an empty list — exactly as `unIData` of a non-`I` returns `I 0`). -/
def defaultSVal : SmtSort → SVal
  | .int  => .I 0
  | .bool => .B false
  | .data => .D (.I 0)
  | .bytes => .BS ByteArray.empty
  | .list _ => .L []
  | .pair a b => .P (defaultSVal a) (defaultSVal b)

/-- A model — an assignment to the free SMT variables.  It is **intrinsically typed**: a
    variable's sort selects the component it is read from (`int`→`ints`, `bool`→`bools`,
    `data`→`datas`, `bytes`→`bytess`).  This makes `evalSmt` of a *well-sorted* expression
    land in the matching `SVal` kind for **every** model (`evalSmt_sort`), with no "the model
    respects sorts" side condition — which is what keeps the builtin-agreement lemmas (§6.2)
    free of model hypotheses.  (z3 reasons about sort-respecting models too, so this loses
    nothing against `z3_sound`.) -/
structure Model where
  ints   : String → Int
  bools  : String → Bool
  datas  : String → Data
  bytess : String → ByteString

/-- Meaning of a binary operator on two semantic values.  The `Bool`-valued comparisons use
    *exactly* the expressions appearing in the trusted `evalBuiltin_*` denotations
    (`x ≤ y`, `x < y`, `x == y`) so the builtin-agreement lemmas (§6.2) are definitional. -/
def evalBin : BinOp → SVal → SVal → SVal
  | .add,  .I x, .I y => .I (x + y)
  | .sub,  .I x, .I y => .I (x - y)
  | .mul,  .I x, .I y => .I (x * y)
  | .fdiv, .I x, .I y => .I (Int.fdiv x y)
  | .fmod, .I x, .I y => .I (Int.fmod x y)
  | .tdiv, .I x, .I y => .I (Int.tdiv x y)
  | .tmod, .I x, .I y => .I (Int.tmod x y)
  | .le,   .I x, .I y => .B (x ≤ y)
  | .lt,   .I x, .I y => .B (x < y)
  | .eq,   .I x, .I y => .B (x == y)
  | .eq,   .B a, .B b => .B (a == b)
  | .eq,   .D a, .D b => .B (a == b)
  | .eq,   .BS a, .BS b => .B (a == b)
  | .and_, .B a, .B b => .B (a && b)
  | .or_,  .B a, .B b => .B (a || b)
  | _, _, _ => .bad

/-- Extract a `Data` from an `SVal` (a `D` element of a list being injected back into `Data`);
    junk `I 0` off-shape (unreachable on well-sorted `list data`). -/
def dataOfSVal : SVal → Data | .D d => d | _ => .I 0
/-- Extract a `(Data, Data)` from a `P` of `D`s (a map entry). -/
def pairOfSVal : SVal → Data × Data | .P (.D a) (.D b) => (a, b) | _ => (.I 0, .I 0)

/-- Meaning of a unary `data`/`bytes` operator.  **Total on well-sorted operands** (it is
    `bad` only when the operand has the wrong base sort): the *partial* projections
    (`unIData`/`unBData`/`constrTag`) return a junk value *of the right sort* when the `Data`
    is the wrong constructor — their genuine partiality is carried by the definedness guard
    (`isI`/`isB`/`isConstr`), exactly like integer division.  Matches the corresponding
    `evalBuiltinConst` clause on the model's concrete `Data`/`ByteString`. -/
def evalUop : UnOp → SVal → SVal
  | .iData,     .I n  => .D (.I n)
  | .bData,     .BS b => .D (.B b)
  | .unIData,   .D d  => match d with | .I n => .I n | _ => .I 0
  | .unBData,   .D d  => match d with | .B b => .BS b | _ => .BS ByteArray.empty
  | .constrTag, .D d  => match d with | .Constr t _ => .I t | _ => .I 0
  | .lenBytes,  .BS b => .I (Int.ofNat b.size)
  | .isI,       .D d => .B (match d with | .I _ => true | _ => false)
  | .isB,       .D d => .B (match d with | .B _ => true | _ => false)
  | .isConstr,  .D d => .B (match d with | .Constr _ _ => true | _ => false)
  | .isList,    .D d => .B (match d with | .List _ => true | _ => false)
  | .isMap,     .D d => .B (match d with | .Map _ => true | _ => false)
  -- structured projections: a `Constr`'s fields / a `List`'s items / a `Map`'s entries.
  -- Junk-of-sort (`L []`) when the `Data` is the wrong constructor (guarded by `isConstr`/…).
  | .dArgs,     .D d => match d with | .Constr _ fs => .L (fs.map .D) | _ => .L []
  | .dItems,    .D d => match d with | .List ds => .L (ds.map .D) | _ => .L []
  | .dEntries,  .D d => match d with
      | .Map ps => .L (ps.map (fun p => .P (.D p.1) (.D p.2))) | _ => .L []
  -- structured *constructors*: a list of `Data` ↦ `Data.List`, a list of pairs ↦ `Data.Map`.
  | .mkDList,   .L xs => .D (.List (xs.map dataOfSVal))
  | .mkMap,     .L xs => .D (.Map (xs.map pairOfSVal))
  -- cryptographic hashes: the (uninterpreted) axiom applied to the operand bytes
  | .sha2_256,   .BS b => .BS (Moist.Plutus.sha2_256 b)
  | .sha3_256,   .BS b => .BS (Moist.Plutus.sha3_256 b)
  | .blake2b_256, .BS b => .BS (Moist.Plutus.blake2b_256 b)
  | .blake2b_224, .BS b => .BS (Moist.Plutus.blake2b_224 b)
  | .keccak_256, .BS b => .BS (Moist.Plutus.keccak_256 b)
  | .ripemd_160, .BS b => .BS (Moist.Plutus.ripemd_160 b)
  | .serialiseData, .D d => .BS (Moist.Plutus.serialiseData d)
  | .blsG1Neg, .BS a => .BS (Moist.Plutus.bls_g1_neg a)
  | .blsG2Neg, .BS a => .BS (Moist.Plutus.bls_g2_neg a)
  | .blsG1Compress, .BS a => .BS (Moist.Plutus.bls_g1_compress a)
  | .blsG2Compress, .BS a => .BS (Moist.Plutus.bls_g2_compress a)
  | .blsG1Uncompress, .BS a => .BS (Moist.Plutus.bls_g1_uncompress a)
  | .blsG2Uncompress, .BS a => .BS (Moist.Plutus.bls_g2_uncompress a)
  | _, _ => .bad

/-- The (opaque) signature verifier selected by a `VerifyKind`. -/
def verifyFn : VerifyKind → ByteString → ByteString → ByteString → Bool
  | .ed25519          => Moist.Plutus.verifyEd25519
  | .ecdsaSecp256k1   => Moist.Plutus.verifyEcdsaSecp256k1
  | .schnorrSecp256k1 => Moist.Plutus.verifySchnorrSecp256k1

/-- Meaning of a BLS binary/mixed op on its two operand values (sort-correct by construction;
    `bad` on wrong-sorted operands, unreachable on well-sorted compiler output). -/
def evalBlsBin : BlsBinOp → SVal → SVal → SVal
  | .g1Add,         .BS a, .BS b => .BS (Moist.Plutus.bls_g1_add a b)
  | .g2Add,         .BS a, .BS b => .BS (Moist.Plutus.bls_g2_add a b)
  | .mulMlResult,   .BS a, .BS b => .BS (Moist.Plutus.bls_mulMlResult a b)
  | .g1HashToGroup, .BS a, .BS b => .BS (Moist.Plutus.bls_g1_hashToGroup a b)
  | .g2HashToGroup, .BS a, .BS b => .BS (Moist.Plutus.bls_g2_hashToGroup a b)
  | .millerLoop,    .BS a, .BS b => .BS (Moist.Plutus.bls_millerLoop a b)
  | .g1Equal,       .BS a, .BS b => .B (Moist.Plutus.bls_g1_equal a b)
  | .g2Equal,       .BS a, .BS b => .B (Moist.Plutus.bls_g2_equal a b)
  | .finalVerify,   .BS a, .BS b => .B (Moist.Plutus.bls_finalVerify a b)
  | .g1ScalarMul,   .I k, .BS p => .BS (Moist.Plutus.bls_g1_scalarMul k p)
  | .g2ScalarMul,   .I k, .BS p => .BS (Moist.Plutus.bls_g2_scalarMul k p)
  | _, _, _ => .bad

/-- The Lean meaning of an `SmtExpr` at a model `σ`.  Total; structural recursion.  A
    variable is read from the `int`- or `bool`-typed component of the model selected by its
    sort annotation. -/
def evalSmt (σ : Model) : SmtExpr → SVal
  | .var x .int   => .I (σ.ints x)
  | .var x .bool  => .B (σ.bools x)
  | .var x .data  => .D (σ.datas x)
  | .var x .bytes => .BS (σ.bytess x)
  -- structured input variables are not produced by the compiler (structured values are always
  -- *computed* from `Data` via the ops below) ⇒ junk-of-sort; never reached on real output.
  | .var _ s@(.list _)   => defaultSVal s
  | .var _ s@(.pair _ _) => defaultSVal s
  | .litI n  => .I n
  | .litB b  => .B b
  | .litBS b => .BS b
  | .neg e   => match evalSmt σ e with | .I n => .I (-n) | _ => .bad
  | .not e   => match evalSmt σ e with | .B b => .B (!b) | _ => .bad
  | .bin op a b => evalBin op (evalSmt σ a) (evalSmt σ b)
  | .uop op e => evalUop op (evalSmt σ e)
  | .ite c a b =>
    match evalSmt σ c with
    | .B true  => evalSmt σ a
    | .B false => evalSmt σ b
    | _        => .bad
  | .mkpair a b => .P (evalSmt σ a) (evalSmt σ b)
  | .fstP e => match evalSmt σ e with | .P x _ => x | _ => .bad
  | .sndP e => match evalSmt σ e with | .P _ y => y | _ => .bad
  | .nilL _ => .L []
  | .consL h t => match evalSmt σ t with | .L xs => .L (evalSmt σ h :: xs) | _ => .bad
  | .headL s e => match evalSmt σ e with | .L (x :: _) => x | _ => defaultSVal s
  | .tailL e => match evalSmt σ e with | .L (_ :: xs) => .L xs | _ => .L []
  | .nullL e => match evalSmt σ e with | .L xs => .B xs.isEmpty | _ => .bad
  | .verifySig k a b c =>
    match evalSmt σ a, evalSmt σ b, evalSmt σ c with
    | .BS pk, .BS msg, .BS sig => .B (verifyFn k pk msg sig)
    | _, _, _ => .bad
  | .blsBin op a b => evalBlsBin op (evalSmt σ a) (evalSmt σ b)
  | .mkConstrD t f =>
    match evalSmt σ t, evalSmt σ f with
    | .I tg, .L xs => .D (.Constr tg (xs.map dataOfSVal))
    | _, _ => .bad

/-! ## Unsatisfiability — the Lean meaning of z3's `unsat` -/

/-- **The Lean meaning of `unsat`.**  `e` is unsatisfiable when no model makes it the
    boolean `true`.  Properties to be discharged by z3 are negated and asserted; an `unsat`
    is exactly `Unsat`, which (via `z3_sound`) becomes a genuine theorem. -/
def Unsat (e : SmtExpr) : Prop := ∀ σ : Model, evalSmt σ e ≠ .B true

/-- **The Lean meaning of `sat`.**  A concrete witnessing model — used for the (untrusted)
    bug-finding direction, where the model is replayed through `bigEval`/CEK. -/
def Sat (e : SmtExpr) : Prop := ∃ σ : Model, evalSmt σ e = .B true

theorem not_unsat_of_sat {e : SmtExpr} (h : Sat e) : ¬ Unsat e := by
  obtain ⟨σ, hσ⟩ := h; intro hu; exact hu σ hσ

/-- "z3 reported `unsat` on this SMT-LIB string."  Opaque: its sole role is to be the
    hypothesis of `z3_sound` (`Moist/Smt/Print.lean`).  No Lean content — it is a *runtime*
    fact about an external solver, supplied per query. -/
opaque z3_says_unsat : String → Prop

/-! ## Convenience evaluation lemmas -/

@[simp] theorem evalSmt_litI (σ : Model) (n : Int) : evalSmt σ (.litI n) = .I n := rfl
@[simp] theorem evalSmt_litB (σ : Model) (b : Bool) : evalSmt σ (.litB b) = .B b := rfl
@[simp] theorem evalSmt_varI (σ : Model) (x : String) :
    evalSmt σ (.var x .int) = .I (σ.ints x) := rfl
@[simp] theorem evalSmt_varB (σ : Model) (x : String) :
    evalSmt σ (.var x .bool) = .B (σ.bools x) := rfl
@[simp] theorem evalSmt_varD (σ : Model) (x : String) :
    evalSmt σ (.var x .data) = .D (σ.datas x) := rfl
@[simp] theorem evalSmt_varBS (σ : Model) (x : String) :
    evalSmt σ (.var x .bytes) = .BS (σ.bytess x) := rfl
@[simp] theorem evalSmt_bin (σ : Model) (op a b) :
    evalSmt σ (.bin op a b) = evalBin op (evalSmt σ a) (evalSmt σ b) := rfl
@[simp] theorem evalSmt_uop (σ : Model) (op e) :
    evalSmt σ (.uop op e) = evalUop op (evalSmt σ e) := rfl

/-! ## Well-sortedness soundness

`sortOf e = some s` certifies that `e` is well-sorted; the lemmas below turn that *syntactic*
certificate into the *semantic* guarantee that `evalSmt σ e` is the matching `SVal` kind
(an `I _` for `int`, a `B _` for `bool`) — at **every** model, no side conditions.  This is
the bridge that lets the compiler's sort guards discharge the agreement lemmas: a builtin
that only commits on well-sorted integer operands is guaranteed integer operands at runtime.
-/

/-- "`v` belongs to sort `s`."  Recursive on the sort: a `pair` value's components and a
    `list` value's elements must themselves have the right sorts. -/
def HasSort : SmtSort → SVal → Prop
  | .int,   .I _  => True
  | .bool,  .B _  => True
  | .data,  .D _  => True
  | .bytes, .BS _ => True
  | .pair sa sb, .P x y => HasSort sa x ∧ HasSort sb y
  | .list s, .L xs => ∀ x ∈ xs, HasSort s x
  | _, _ => False

theorem hasSort_pair {sa sb : SmtSort} {v : SVal} (h : HasSort (.pair sa sb) v) :
    ∃ x y, v = .P x y ∧ HasSort sa x ∧ HasSort sb y := by
  cases v with
  | P x y => exact ⟨x, y, rfl, h.1, h.2⟩
  | _ => exact absurd h (by simp [HasSort])

theorem hasSort_list {s : SmtSort} {v : SVal} (h : HasSort (.list s) v) :
    ∃ xs, v = .L xs ∧ ∀ x ∈ xs, HasSort s x := by
  cases v with
  | L xs => exact ⟨xs, rfl, h⟩
  | _ => exact absurd h (by simp [HasSort])

/-- `defaultSVal s` has sort `s`. -/
theorem hasSort_defaultSVal : ∀ s : SmtSort, HasSort s (defaultSVal s)
  | .int | .bool | .data | .bytes => trivial
  | .list _ => by intro x hx; simp at hx
  | .pair a b => ⟨hasSort_defaultSVal a, hasSort_defaultSVal b⟩

theorem hasSort_int {v : SVal} (h : HasSort .int v) : ∃ n, v = .I n := by
  cases v with
  | I n => exact ⟨n, rfl⟩
  | _ => exact absurd h (by simp [HasSort])

theorem hasSort_bool {v : SVal} (h : HasSort .bool v) : ∃ b, v = .B b := by
  cases v with
  | B b => exact ⟨b, rfl⟩
  | _ => exact absurd h (by simp [HasSort])

theorem hasSort_data {v : SVal} (h : HasSort .data v) : ∃ d, v = .D d := by
  cases v with
  | D d => exact ⟨d, rfl⟩
  | _ => exact absurd h (by simp [HasSort])

theorem hasSort_bytes {v : SVal} (h : HasSort .bytes v) : ∃ b, v = .BS b := by
  cases v with
  | BS b => exact ⟨b, rfl⟩
  | _ => exact absurd h (by simp [HasSort])

/-- A mapped list has the list sort when every produced element has the element sort. -/
theorem hasSort_L_map {α : Type} {s : SmtSort} (f : α → SVal) (l : List α)
    (hf : ∀ a, HasSort s (f a)) : HasSort (.list s) (.L (l.map f)) := by
  intro x hx; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx; exact hf a

/-- `evalUop` preserves sorts: applied to its operand sort it lands in its result sort. -/
theorem evalUop_hasSort {op : UnOp} {v : SVal} (h : HasSort (UnOp.sorts op).1 v) :
    HasSort (UnOp.sorts op).2 (evalUop op v) := by
  cases op <;> simp only [UnOp.sorts] at h ⊢ <;>
    first
    | (obtain ⟨d, rfl⟩ := hasSort_data h; cases d <;> simp only [evalUop] <;>
       first
       | exact hasSort_L_map _ _ (fun a => by simp [HasSort])
       | (intro x hx; simp at hx)
       | simp [HasSort])
    | (obtain ⟨n, rfl⟩ := hasSort_int h; simp [evalUop, HasSort])
    | (obtain ⟨b, rfl⟩ := hasSort_bytes h; simp [evalUop, HasSort])
    | (obtain ⟨xs, rfl, _⟩ := hasSort_list h; simp [evalUop, HasSort])  -- mkDList / mkMap

/-- `evalBlsBin` preserves sorts: well-sorted operands land in the op's result sort. -/
theorem evalBlsBin_hasSort {op : BlsBinOp} {va vb : SVal}
    (hva : HasSort (BlsBinOp.operandSorts op).1 va) (hvb : HasSort (BlsBinOp.operandSorts op).2 vb) :
    HasSort (BlsBinOp.resultSort op) (evalBlsBin op va vb) := by
  cases op <;> simp only [BlsBinOp.operandSorts, BlsBinOp.resultSort] at hva hvb ⊢ <;>
    first
    | (obtain ⟨a, rfl⟩ := hasSort_bytes hva; obtain ⟨b, rfl⟩ := hasSort_bytes hvb
       simp [evalBlsBin, HasSort])
    | (obtain ⟨k, rfl⟩ := hasSort_int hva; obtain ⟨p, rfl⟩ := hasSort_bytes hvb
       simp [evalBlsBin, HasSort])

/-- `evalBin` preserves sorts: a well-sorted application lands in its result sort. -/
theorem evalBin_hasSort : ∀ {op : BinOp} {sa s : SmtSort} {va vb : SVal},
    BinOp.resultSort op sa = some s → HasSort sa va → HasSort sa vb →
    HasSort s (evalBin op va vb)
  | op, .int, s, va, vb, hr, hva, hvb => by
      obtain ⟨na, rfl⟩ := hasSort_int hva
      obtain ⟨nb, rfl⟩ := hasSort_int hvb
      cases op <;> cases s <;> simp_all [BinOp.resultSort, evalBin, HasSort]
  | op, .bool, s, va, vb, hr, hva, hvb => by
      obtain ⟨ba, rfl⟩ := hasSort_bool hva
      obtain ⟨bb, rfl⟩ := hasSort_bool hvb
      cases op <;> cases s <;> simp_all [BinOp.resultSort, evalBin, HasSort]
  | op, .data, s, va, vb, hr, hva, hvb => by
      obtain ⟨da, rfl⟩ := hasSort_data hva
      obtain ⟨db, rfl⟩ := hasSort_data hvb
      cases op <;> cases s <;> simp_all [BinOp.resultSort, evalBin, HasSort]
  | op, .bytes, s, va, vb, hr, hva, hvb => by
      obtain ⟨ba, rfl⟩ := hasSort_bytes hva
      obtain ⟨bb, rfl⟩ := hasSort_bytes hvb
      cases op <;> cases s <;> simp_all [BinOp.resultSort, evalBin, HasSort]
  | op, .list _, _, _, _, hr, _, _ => by cases op <;> simp [BinOp.resultSort] at hr
  | op, .pair _ _, _, _, _, hr, _, _ => by cases op <;> simp [BinOp.resultSort] at hr

/-- **Well-sortedness soundness.**  A well-sorted expression evaluates to its sort's `SVal`
    kind, in any model. -/
theorem evalSmt_hasSort (σ : Model) : ∀ {e : SmtExpr} {s : SmtSort},
    SmtExpr.sortOf e = some s → HasSort s (evalSmt σ e) := by
  intro e
  induction e with
  | var x s =>
    intro s' h; simp only [SmtExpr.sortOf, Option.some.injEq] at h; subst h
    cases s with
    | int | bool | data | bytes => simp [evalSmt, HasSort]
    | list _ | pair _ _ => exact hasSort_defaultSVal _
  | litI n => intro s h; simp only [SmtExpr.sortOf, Option.some.injEq] at h; subst h
              simp [evalSmt, HasSort]
  | litB b => intro s h; simp only [SmtExpr.sortOf, Option.some.injEq] at h; subst h
              simp [evalSmt, HasSort]
  | litBS b => intro s h; simp only [SmtExpr.sortOf, Option.some.injEq] at h; subst h
               simp [evalSmt, HasSort]
  | neg e ihe =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases hse : SmtExpr.sortOf e with
    | none => simp [hse] at h
    | some se => cases se with
      | int =>
        simp only [hse, Option.some.injEq] at h; subst h
        obtain ⟨m, hm⟩ := hasSort_int (ihe hse); simp [evalSmt, hm, HasSort]
      | bool => simp [hse] at h
      | data => simp [hse] at h
      | bytes => simp [hse] at h
      | list _ => simp [hse] at h
      | pair _ _ => simp [hse] at h
  | not e ihe =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases hse : SmtExpr.sortOf e with
    | none => simp [hse] at h
    | some se => cases se with
      | int => simp [hse] at h
      | bool =>
        simp only [hse, Option.some.injEq] at h; subst h
        obtain ⟨c, hc⟩ := hasSort_bool (ihe hse); simp [evalSmt, hc, HasSort]
      | data => simp [hse] at h
      | bytes => simp [hse] at h
      | list _ => simp [hse] at h
      | pair _ _ => simp [hse] at h
  | bin op a b iha ihb =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases ha : SmtExpr.sortOf a with
    | none => simp only [ha] at h; simp at h
    | some sa =>
      cases hb : SmtExpr.sortOf b with
      | none => simp only [ha, hb] at h; simp at h
      | some sb =>
        simp only [ha, hb] at h
        split at h
        · rename_i hcond; subst hcond
          simp only [evalSmt]
          exact evalBin_hasSort h (iha ha) (ihb hb)
        · simp at h
  | uop op e ihe =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases hse : SmtExpr.sortOf e with
    | none => simp only [hse] at h; simp at h
    | some se =>
      simp only [hse] at h
      split at h
      · rename_i hcond
        simp only [Option.some.injEq] at h; subst h
        simp only [evalSmt]
        exact evalUop_hasSort (hcond ▸ ihe hse)
      · simp at h
  | ite c a b ihc iha ihb =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases hc : SmtExpr.sortOf c with
    | none => simp only [hc] at h; simp at h
    | some sc =>
      cases sc with
      | bool =>
        cases ha : SmtExpr.sortOf a with
        | none => simp only [hc, ha] at h; simp at h
        | some sa =>
          cases hb2 : SmtExpr.sortOf b with
          | none => simp only [hc, ha, hb2] at h; simp at h
          | some sb =>
            simp only [hc, ha, hb2] at h
            split at h
            · rename_i hcond; subst hcond
              simp only [Option.some.injEq] at h; subst h
              obtain ⟨cb, hcb⟩ := hasSort_bool (ihc hc)
              simp only [evalSmt, hcb]
              cases cb
              · exact ihb hb2
              · exact iha ha
            · simp at h
      | int => simp only [hc] at h; simp at h
      | data => simp only [hc] at h; simp at h
      | bytes => simp only [hc] at h; simp at h
      | list _ => simp only [hc] at h; simp at h
      | pair _ _ => simp only [hc] at h; simp at h
  | mkpair a b iha ihb =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases ha : SmtExpr.sortOf a with
    | none => simp only [ha] at h; simp at h
    | some sa =>
      cases hb : SmtExpr.sortOf b with
      | none => simp only [ha, hb] at h; simp at h
      | some sb =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        exact ⟨iha ha, ihb hb⟩
  | fstP e ihe =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases hse : SmtExpr.sortOf e with
    | none => simp only [hse] at h; simp at h
    | some se => cases se with
      | pair sa sb =>
        simp only [hse, Option.some.injEq] at h; subst h
        obtain ⟨x, y, hxy, hx, _⟩ := hasSort_pair (ihe hse)
        simp only [evalSmt, hxy]; exact hx
      | int | bool | data | bytes | list _ => simp only [hse] at h; simp at h
  | sndP e ihe =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases hse : SmtExpr.sortOf e with
    | none => simp only [hse] at h; simp at h
    | some se => cases se with
      | pair sa sb =>
        simp only [hse, Option.some.injEq] at h; subst h
        obtain ⟨x, y, hxy, _, hy⟩ := hasSort_pair (ihe hse)
        simp only [evalSmt, hxy]; exact hy
      | int | bool | data | bytes | list _ => simp only [hse] at h; simp at h
  | nilL s' =>
    intro s h; simp only [SmtExpr.sortOf, Option.some.injEq] at h; subst h
    intro x hx; simp [evalSmt] at hx
  | consL hd tl ihh iht =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases hh : SmtExpr.sortOf hd with
    | none => simp only [hh] at h; simp at h
    | some sh =>
      cases ht : SmtExpr.sortOf tl with
      | none => simp only [hh, ht] at h; cases sh <;> simp at h
      | some st => cases st with
        | list se =>
          simp only [hh, ht] at h; split at h
          · rename_i hcond; subst hcond; simp only [Option.some.injEq] at h; subst h
            obtain ⟨xs, hxs, hall⟩ := hasSort_list (iht ht)
            simp only [evalSmt, hxs]
            intro x hx; simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact ihh hh
            · exact hall x hx
          · simp at h
        | int | bool | data | bytes | pair _ _ => simp only [hh, ht] at h; cases sh <;> simp at h
  | headL s' e ihe =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases hse : SmtExpr.sortOf e with
    | none => simp only [hse] at h; simp at h
    | some se => cases se with
      | list se' =>
        simp only [hse] at h; split at h
        · rename_i hcond; subst hcond; simp only [Option.some.injEq] at h; subst h
          obtain ⟨xs, hxs, hall⟩ := hasSort_list (ihe hse)
          simp only [evalSmt, hxs]
          cases xs with
          | nil => exact hasSort_defaultSVal _
          | cons x xs' => exact hall x (by simp)
        · simp at h
      | int | bool | data | bytes | pair _ _ => simp only [hse] at h; simp at h
  | tailL e ihe =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases hse : SmtExpr.sortOf e with
    | none => simp only [hse] at h; simp at h
    | some se => cases se with
      | list se' =>
        simp only [hse, Option.some.injEq] at h; subst h
        obtain ⟨xs, hxs, hall⟩ := hasSort_list (ihe hse)
        simp only [evalSmt, hxs]
        cases xs with
        | nil => intro x hx; simp at hx
        | cons x xs' => intro y hy; exact hall y (by simp [hy])
      | int | bool | data | bytes | pair _ _ => simp only [hse] at h; simp at h
  | nullL e ihe =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases hse : SmtExpr.sortOf e with
    | none => simp only [hse] at h; simp at h
    | some se => cases se with
      | list se' =>
        simp only [hse, Option.some.injEq] at h; subst h
        obtain ⟨xs, hxs, _⟩ := hasSort_list (ihe hse)
        simp only [evalSmt, hxs, HasSort]
      | int | bool | data | bytes | pair _ _ => simp only [hse] at h; simp at h
  | verifySig k a b c iha ihb ihc =>
    intro s h; simp only [SmtExpr.sortOf] at h
    split at h
    · rename_i ha hb hcc
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨ba, hba⟩ := hasSort_bytes (iha ha)
      obtain ⟨bb, hbb⟩ := hasSort_bytes (ihb hb)
      obtain ⟨bc, hbc⟩ := hasSort_bytes (ihc hcc)
      simp only [evalSmt, hba, hbb, hbc, HasSort]
    · simp at h
  | blsBin op a b iha ihb =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases ha : SmtExpr.sortOf a with
    | none => simp only [ha] at h; simp at h
    | some sa =>
      cases hb : SmtExpr.sortOf b with
      | none => simp only [ha, hb] at h; simp at h
      | some sb =>
        simp only [ha, hb] at h
        split at h
        · rename_i hcond
          simp only [Option.some.injEq] at h; subst h
          obtain ⟨hca, hcb⟩ := hcond; subst hca; subst hcb
          simp only [evalSmt]
          exact evalBlsBin_hasSort (iha ha) (ihb hb)
        · simp at h
  | mkConstrD t f iht ihf =>
    intro s h; simp only [SmtExpr.sortOf] at h
    cases ht : SmtExpr.sortOf t with
    | none => simp only [ht] at h; simp at h
    | some st => cases st with
      | int =>
        cases hf : SmtExpr.sortOf f with
        | none => simp only [ht, hf] at h; simp at h
        | some sf => cases sf with
          | list sel => cases sel with
            | data =>
              simp only [ht, hf, Option.some.injEq] at h; subst h
              obtain ⟨tg, htg⟩ := hasSort_int (iht ht)
              obtain ⟨xs, hxs, _⟩ := hasSort_list (ihf hf)
              simp only [evalSmt, htg, hxs, HasSort]
            | int | bool | bytes | list _ | pair _ _ => simp only [ht, hf] at h; simp at h
          | int | bool | data | bytes | pair _ _ => simp only [ht, hf] at h; simp at h
      | bool | data | bytes | list _ | pair _ _ => simp only [ht] at h; simp at h

/-- Specialisation: well-sorted `int` ⇒ evaluates to some integer. -/
theorem evalSmt_int {σ : Model} {e : SmtExpr} (h : SmtExpr.sortOf e = some .int) :
    ∃ n, evalSmt σ e = .I n := hasSort_int (evalSmt_hasSort σ h)

/-- Specialisation: well-sorted `bool` ⇒ evaluates to some boolean. -/
theorem evalSmt_bool {σ : Model} {e : SmtExpr} (h : SmtExpr.sortOf e = some .bool) :
    ∃ b, evalSmt σ e = .B b := hasSort_bool (evalSmt_hasSort σ h)

/-- Specialisation: well-sorted `data` ⇒ evaluates to some `Data`. -/
theorem evalSmt_data {σ : Model} {e : SmtExpr} (h : SmtExpr.sortOf e = some .data) :
    ∃ d, evalSmt σ e = .D d := hasSort_data (evalSmt_hasSort σ h)

/-- Specialisation: well-sorted `bytes` ⇒ evaluates to some `ByteString`. -/
theorem evalSmt_bytes {σ : Model} {e : SmtExpr} (h : SmtExpr.sortOf e = some .bytes) :
    ∃ b, evalSmt σ e = .BS b := hasSort_bytes (evalSmt_hasSort σ h)

end Moist.Smt
