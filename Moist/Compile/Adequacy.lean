import Moist.Compile.Compile
import Moist.Smt.Semantics
import Moist.Verified.BigStep

/-! # Adequacy of `symEval` w.r.t. `bigEval` — the core simulation proof

The deliverable of the verified compiler: `symEval`, *interpreted at a model* `σ` via the
concretization `γ`, agrees with `bigEval` on the `σ`-instantiated inputs.  Because `symEval`
mirrors `bigEval` structurally (same five mutual functions, same fuel, same recursion), the
proof is a **fuel-induction simulation** that lines up one-for-one with `bigEval`'s own
definition — not a from-scratch denotational-adequacy argument.

We prove the **forward / soundness** direction, conditioned on `symEval` having committed
(`= some o`) and on the definedness flag holding at `σ`:

> `symEval f ρ̂ t = some o → evalSmt σ o.defined = .B true → bigEval f (γE σ ρ̂) t = some (γ σ o.value)`

This is exactly what `validator_sound` consumes (from an `unsat` z3 derives `defined ∧
value` at every relevant `σ`).  Conditioning on `symEval = some` sidesteps the refusal
mismatch (`symEval` soundly refuses where `bigEval` may succeed); requiring `defined = true`
lets every `∧`-guard be destructured **without** a well-sortedness side condition (because
`evalBin .and_ x y = .B true` forces `x = y = .B true`).  Partiality is handled by the
`defined` flag: where the concrete evaluation errors, `defined` is false at `σ`, so the
hypothesis is simply unavailable.

`γ` is **total** (junk `Const.Unit` for the unreachable `SVal.bad`), so the value relation is
a plain function and the simulation is an honest equation, never an `Option` dance.
-/

namespace Moist.Compile

open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)
open Moist.CEK
open Moist.Smt
open Moist.Verified.BigStep

/-! ## Concretization `γ` (symbolic value at a model ↦ concrete `CekValue`) -/

/-- Extract a `Data` / pair-of-`Data` from an `SVal` (for list reconstruction). -/
def svalToData : SVal → Option Moist.Plutus.Data | .D d => some d | _ => none
def svalToPairData : SVal → Option (Moist.Plutus.Data × Moist.Plutus.Data)
  | .P (.D a) (.D b) => some (a, b) | _ => none

/-- `SVal` ↦ `Const`.  Total.  A `pair` is the general `Const.Pair`; a `list` is reconstructed
    by element shape — a list of `Data` is a `ConstDataList`, a list of `(Data, Data)` is a
    `ConstPairDataList` (the only list shapes the supported builtins produce — `unListData`,
    `unMapData`, `unConstrData`'s fields).  `bad` (ill-sorted) maps to junk `Unit`. -/
def svalToConst : SVal → Const
  | .I n  => .Integer n
  | .B b  => .Bool b
  | .D d  => .Data d
  | .BS b => .ByteString b
  | .P x y => .Pair (svalToConst x, svalToConst y)
  | .L xs =>
    match xs.mapM svalToData with
    | some ds => .ConstDataList ds
    | none =>
      match xs.mapM svalToPairData with
      | some ps => .ConstPairDataList ps
      | none    => .Unit   -- unreachable on supported output (lists are data / pair-data)
  | .bad  => .Unit

@[simp] theorem svalToConst_I (n : Int) : svalToConst (.I n) = .Integer n := rfl
@[simp] theorem svalToConst_P (x y : SVal) :
    svalToConst (.P x y) = .Pair (svalToConst x, svalToConst y) := rfl

mutual
  /-- Concretize a symbolic value at model `σ`.  `sCon` is interpreted by `evalSmt`; closures
      and constructors recurse structurally (defunctionalized ⇒ no higher-order relation). -/
  def γ (σ : Model) : SymVal → CekValue
    | .sCon e          => .VCon (svalToConst (evalSmt σ e))
    | .sConst c        => .VCon c
    | .sLam body ρ     => .VLam body (γE σ ρ)
    | .sDelay body ρ   => .VDelay body (γE σ ρ)
    | .sConstr tag fs  => .VConstr tag (γL σ fs)
    | .sBuiltin b as ea => .VBuiltin b (γL σ as) ea
    | .sIte cond a b   => match evalSmt σ cond with | .B true => γ σ a | _ => γ σ b
  /-- Concretize a symbolic environment (list) into a `CekEnv`. -/
  def γE (σ : Model) : SymEnv → CekEnv
    | []      => .nil
    | v :: vs => .cons (γ σ v) (γE σ vs)
  /-- Concretize a list of symbolic values. -/
  def γL (σ : Model) : List SymVal → List CekValue
    | []      => []
    | v :: vs => γ σ v :: γL σ vs
end

/-! ## `γ` unfolding lemmas (definitional; reliable rewriting for the mutual def) -/

@[simp] theorem γ_sCon (σ : Model) (e : SmtExpr) :
    γ σ (.sCon e) = .VCon (svalToConst (evalSmt σ e)) := rfl
@[simp] theorem γ_sConst (σ : Model) (c : Const) : γ σ (.sConst c) = .VCon c := rfl
@[simp] theorem γ_sLam (σ : Model) (b : Term) (ρ : SymEnv) :
    γ σ (.sLam b ρ) = .VLam b (γE σ ρ) := rfl
@[simp] theorem γ_sDelay (σ : Model) (b : Term) (ρ : SymEnv) :
    γ σ (.sDelay b ρ) = .VDelay b (γE σ ρ) := rfl
@[simp] theorem γ_sConstr (σ : Model) (tag : Nat) (fs : List SymVal) :
    γ σ (.sConstr tag fs) = .VConstr tag (γL σ fs) := rfl
@[simp] theorem γ_sBuiltin (σ : Model) (b : BuiltinFun) (as : List SymVal) (ea : ExpectedArgs) :
    γ σ (.sBuiltin b as ea) = .VBuiltin b (γL σ as) ea := rfl
/-- A deferred symbolic choice concretizes by selecting the branch the condition picks at `σ`
    (matching the CEK's concrete `ifThenElse`). -/
theorem γ_sIte_true (σ : Model) {cond : SmtExpr} {a b : SymVal} (h : evalSmt σ cond = .B true) :
    γ σ (.sIte cond a b) = γ σ a := by
  show (match evalSmt σ cond with | .B true => γ σ a | _ => γ σ b) = γ σ a
  rw [h]
theorem γ_sIte_false (σ : Model) {cond : SmtExpr} {a b : SymVal} {sv : SVal}
    (h : evalSmt σ cond = sv) (hne : sv ≠ .B true) :
    γ σ (.sIte cond a b) = γ σ b := by
  show (match evalSmt σ cond with | .B true => γ σ a | _ => γ σ b) = γ σ b
  rw [h]; cases sv <;> simp_all
@[simp] theorem γL_nil (σ : Model) : γL σ [] = [] := rfl
@[simp] theorem γL_cons (σ : Model) (v : SymVal) (vs : List SymVal) :
    γL σ (v :: vs) = γ σ v :: γL σ vs := rfl

/-- An `int`-sorted symbolic constant concretizes to the corresponding integer `VCon`. -/
theorem γ_sCon_I {σ : Model} {e : SmtExpr} {n : Int} (h : evalSmt σ e = .I n) :
    γ σ (.sCon e) = .VCon (.Integer n) := by simp [γ_sCon, h, svalToConst]
/-- A `bool`-sorted symbolic constant concretizes to the corresponding boolean `VCon`. -/
theorem γ_sCon_B {σ : Model} {e : SmtExpr} {b : Bool} (h : evalSmt σ e = .B b) :
    γ σ (.sCon e) = .VCon (.Bool b) := by simp [γ_sCon, h, svalToConst]
/-- A `data`-sorted symbolic constant concretizes to the corresponding `Data` `VCon`. -/
theorem γ_sCon_D {σ : Model} {e : SmtExpr} {d : Plutus.Data} (h : evalSmt σ e = .D d) :
    γ σ (.sCon e) = .VCon (.Data d) := by simp [γ_sCon, h, svalToConst]
/-- A `bytes`-sorted symbolic constant concretizes to the corresponding `ByteString` `VCon`. -/
theorem γ_sCon_BS {σ : Model} {e : SmtExpr} {bs : Plutus.ByteString} (h : evalSmt σ e = .BS bs) :
    γ σ (.sCon e) = .VCon (.ByteString bs) := by simp [γ_sCon, h, svalToConst]

/-! ## Small commutation lemmas -/

/-- `γE` is a list homomorphism, so `lookup` commutes with it on the nose (both use the same
    1-based de-Bruijn convention). -/
theorem γE_lookup (σ : Model) : ∀ (ρ : SymEnv) (k : Nat),
    (γE σ ρ).lookup k = (SymEnv.lookup ρ k).map (γ σ)
  | [], k => by cases k <;> simp [γE, CekEnv.lookup, SymEnv.lookup]
  | _ :: _, 0 => rfl
  | _ :: _, 1 => rfl
  | _ :: vs, k + 2 => by
      show (γE σ vs).lookup (k + 1) = (SymEnv.lookup vs (k + 1)).map (γ σ)
      exact γE_lookup σ vs (k + 1)

/-- `γE` commutes with `extend`. -/
@[simp] theorem γE_extend (σ : Model) (ρ : SymEnv) (v : SymVal) :
    γE σ (SymEnv.extend ρ v) = (γE σ ρ).extend (γ σ v) := rfl

/-- A translated `Integer`/`Bool` constant concretizes back to itself, at any model. -/
theorem γ_constToSmt (σ : Model) : ∀ {c : Const} {e : SmtExpr},
    constToSmt c = some e → γ σ (.sCon e) = .VCon c := by
  intro c e h
  cases c <;> simp only [constToSmt] at h <;>
    first
    | (injection h with h; subst h; simp [γ, evalSmt, svalToConst])
    | exact absurd h (by simp)

/-- **Any** constant concretizes back to itself (integers/booleans via `sCon`, every other
    type via `sConst`). -/
theorem γ_constToSym (σ : Model) (c : Const) : γ σ (constToSym c) = .VCon c := by
  cases hc : constToSmt c with
  | none => simp only [constToSym, hc, γ_sConst]
  | some e => simp only [constToSym, hc]; exact γ_constToSmt σ hc

/-- A true conjunction has both conjuncts true — **no well-sortedness needed**, because
    `evalBin .and_ x y = .B true` is possible only when `x = .B true` and `y = .B true`. -/
theorem and_true_split (σ : Model) {p q : SmtExpr}
    (h : evalSmt σ (SmtExpr.andE p q) = .B true) :
    evalSmt σ p = .B true ∧ evalSmt σ q = .B true := by
  simp only [SmtExpr.andE, evalSmt_bin] at h
  cases hp : evalSmt σ p <;> cases hq : evalSmt σ q <;>
    rw [hp, hq] at h <;> simp_all [evalBin]

/-! ## Builtin agreement (§6.2)

The symbolic builtin denotations agree with `evalBuiltin` after concretization.  Only the
division family touches the *trusted* `evalBuiltin_*` denotation axioms of
`Moist.Verified.BigStep` (the small `#eval`-validated TCB item, R3); the rest is axiom-free
via the concrete bridge below. -/

/-- `extractConsts` is a left inverse of `(VCon ·)`-mapping. -/
theorem extractConsts_map_VCon : ∀ (cs : List Const),
    extractConsts (cs.map (CekValue.VCon ·)) = some cs
  | [] => rfl
  | c :: cs => by simp only [List.map_cons, extractConsts, extractConsts_map_VCon cs]; rfl

/-- For a non-pass-through builtin, `evalBuiltin` on concrete `VCon` arguments is exactly
    `evalBuiltinConst` (lifted), by the structure of `evalBuiltin`. -/
theorem evalBuiltin_concrete {b : BuiltinFun} (hb : isPassthroughBuiltin b = false)
    (cs : List Const) :
    evalBuiltin b (cs.map (CekValue.VCon ·)) = (evalBuiltinConst b cs).map (CekValue.VCon ·) := by
  have hpt : evalBuiltinPassThrough b (cs.map (CekValue.VCon ·)) = none := by
    apply evalBuiltinPassThrough_none_of_not_passthrough
    cases b <;> simp_all [isPassthroughBuiltin]
  simp only [evalBuiltin, hpt, extractConsts_map_VCon]
  cases evalBuiltinConst b cs <;> rfl

/-! ### Per-builtin `Data`/`ByteString` denotations (axiom-free)

Each is `evalBuiltin_concrete` specialized to a *concrete* builtin (so the `isPassthrough`
check is `by decide`) composed with the `rfl`-reduction of `evalBuiltinConst` — **no trusted
denotation axioms**.  Used by `smtBuiltin_adequate` exactly like the arithmetic axioms. -/

theorem evalBuiltin_iData (n : Int) :
    evalBuiltin .IData [.VCon (.Integer n)] = some (.VCon (.Data (.I n))) := by
  have := evalBuiltin_concrete (b := .IData) (by decide) [.Integer n]; simpa using this
theorem evalBuiltin_bData (bs : Plutus.ByteString) :
    evalBuiltin .BData [.VCon (.ByteString bs)] = some (.VCon (.Data (.B bs))) := by
  have := evalBuiltin_concrete (b := .BData) (by decide) [.ByteString bs]; simpa using this
theorem evalBuiltin_unIData (n : Int) :
    evalBuiltin .UnIData [.VCon (.Data (.I n))] = some (.VCon (.Integer n)) := by
  have := evalBuiltin_concrete (b := .UnIData) (by decide) [.Data (.I n)]; simpa using this
theorem evalBuiltin_unBData (bs : Plutus.ByteString) :
    evalBuiltin .UnBData [.VCon (.Data (.B bs))] = some (.VCon (.ByteString bs)) := by
  have := evalBuiltin_concrete (b := .UnBData) (by decide) [.Data (.B bs)]; simpa using this
theorem evalBuiltin_lengthOfByteString (bs : Plutus.ByteString) :
    evalBuiltin .LengthOfByteString [.VCon (.ByteString bs)]
      = some (.VCon (.Integer (Int.ofNat bs.size))) := by
  have := evalBuiltin_concrete (b := .LengthOfByteString) (by decide) [.ByteString bs]
  simpa using this
/-- The cryptographic-hash denotations — axiom-free given the (opaque) hash, via
    `evalBuiltin_concrete`.  All `bytes → bytes`, no definedness guard. -/
theorem evalBuiltin_sha2_256 (bs : Plutus.ByteString) :
    evalBuiltin .Sha2_256 [.VCon (.ByteString bs)] = some (.VCon (.ByteString (Moist.Plutus.sha2_256 bs))) := by
  have := evalBuiltin_concrete (b := .Sha2_256) (by decide) [.ByteString bs]; simpa using this
theorem evalBuiltin_sha3_256 (bs : Plutus.ByteString) :
    evalBuiltin .Sha3_256 [.VCon (.ByteString bs)] = some (.VCon (.ByteString (Moist.Plutus.sha3_256 bs))) := by
  have := evalBuiltin_concrete (b := .Sha3_256) (by decide) [.ByteString bs]; simpa using this
theorem evalBuiltin_blake2b_256 (bs : Plutus.ByteString) :
    evalBuiltin .Blake2b_256 [.VCon (.ByteString bs)] = some (.VCon (.ByteString (Moist.Plutus.blake2b_256 bs))) := by
  have := evalBuiltin_concrete (b := .Blake2b_256) (by decide) [.ByteString bs]; simpa using this
theorem evalBuiltin_blake2b_224 (bs : Plutus.ByteString) :
    evalBuiltin .Blake2b_224 [.VCon (.ByteString bs)] = some (.VCon (.ByteString (Moist.Plutus.blake2b_224 bs))) := by
  have := evalBuiltin_concrete (b := .Blake2b_224) (by decide) [.ByteString bs]; simpa using this
theorem evalBuiltin_keccak_256 (bs : Plutus.ByteString) :
    evalBuiltin .Keccak_256 [.VCon (.ByteString bs)] = some (.VCon (.ByteString (Moist.Plutus.keccak_256 bs))) := by
  have := evalBuiltin_concrete (b := .Keccak_256) (by decide) [.ByteString bs]; simpa using this
theorem evalBuiltin_ripemd_160 (bs : Plutus.ByteString) :
    evalBuiltin .Ripemd_160 [.VCon (.ByteString bs)] = some (.VCon (.ByteString (Moist.Plutus.ripemd_160 bs))) := by
  have := evalBuiltin_concrete (b := .Ripemd_160) (by decide) [.ByteString bs]; simpa using this
theorem evalBuiltin_equalsData (a b : Plutus.Data) :
    evalBuiltin .EqualsData [.VCon (.Data b), .VCon (.Data a)] = some (.VCon (.Bool (a == b))) := by
  have := evalBuiltin_concrete (b := .EqualsData) (by decide) [.Data b, .Data a]; simpa using this
theorem evalBuiltin_equalsByteString (a b : Plutus.ByteString) :
    evalBuiltin .EqualsByteString [.VCon (.ByteString b), .VCon (.ByteString a)]
      = some (.VCon (.Bool (a == b))) := by
  have := evalBuiltin_concrete (b := .EqualsByteString) (by decide) [.ByteString b, .ByteString a]
  simpa using this

/-- Structure of a successful `sortBin`: both operands are `need`-sorted. -/
theorem sortBin_some {op : Moist.Smt.BinOp} {grd ex ey v g : SmtExpr} {need : SmtSort}
    (h : sortBin op grd need ex ey = some (v, g)) :
    v = .bin op ex ey ∧ g = grd ∧
      SmtExpr.sortOf ex = some need ∧ SmtExpr.sortOf ey = some need := by
  unfold sortBin at h; split at h
  · rename_i hs; simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm, hs.1, hs.2⟩
  · exact absurd h (by simp)

/-- Structure of a successful `uOp`: the operand is `need`-sorted. -/
theorem uOp_some {op : Moist.Smt.UnOp} {grd e v g : SmtExpr} {need : SmtSort}
    (h : uOp op grd need e = some (v, g)) :
    v = .uop op e ∧ g = grd ∧ SmtExpr.sortOf e = some need := by
  unfold uOp at h; split at h
  · rename_i hs; simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm, hs⟩
  · exact absurd h (by simp)

/-- A true `y ≠ 0` guard means the (integer) divisor is nonzero. -/
theorem neZeroE_true {σ : Model} {ey : SmtExpr} {Y : Int}
    (hY : evalSmt σ ey = .I Y) (hd : evalSmt σ (SmtExpr.neZeroE ey) = .B true) : Y ≠ 0 := by
  simp only [SmtExpr.neZeroE, evalSmt, hY, evalBin] at hd
  intro h0; subst h0; simp at hd

/-- A true `isI` guard means the `Data` is an `I` constructor. -/
theorem isI_true {σ : Model} {e : SmtExpr} {d : Plutus.Data} (hde : evalSmt σ e = .D d)
    (hd : evalSmt σ (.uop .isI e) = .B true) : ∃ n, d = .I n := by
  cases d <;> simp_all [evalSmt, evalUop]

/-- A true `isB` guard means the `Data` is a `B` constructor. -/
theorem isB_true {σ : Model} {e : SmtExpr} {d : Plutus.Data} (hde : evalSmt σ e = .D d)
    (hd : evalSmt σ (.uop .isB e) = .B true) : ∃ b, d = .B b := by
  cases d <;> simp_all [evalSmt, evalUop]

/-! ### WI-2 helpers: structured-value soundness, guards, and `Data` destructor denotations -/

@[simp] theorem evalSmt_mkpair (σ : Model) (a b : SmtExpr) :
    evalSmt σ (.mkpair a b) = .P (evalSmt σ a) (evalSmt σ b) := rfl
@[simp] theorem evalSmt_fstP (σ : Model) (e : SmtExpr) :
    evalSmt σ (.fstP e) = (match evalSmt σ e with | .P x _ => x | _ => .bad) := rfl
@[simp] theorem evalSmt_sndP (σ : Model) (e : SmtExpr) :
    evalSmt σ (.sndP e) = (match evalSmt σ e with | .P _ y => y | _ => .bad) := rfl
@[simp] theorem evalSmt_headL (σ : Model) (s : SmtSort) (e : SmtExpr) :
    evalSmt σ (.headL s e) = (match evalSmt σ e with | .L (x :: _) => x | _ => defaultSVal s) := rfl
@[simp] theorem evalSmt_tailL (σ : Model) (e : SmtExpr) :
    evalSmt σ (.tailL e) = (match evalSmt σ e with | .L (_ :: xs) => .L xs | _ => .L []) := rfl
@[simp] theorem evalSmt_nullL (σ : Model) (e : SmtExpr) :
    evalSmt σ (.nullL e) = (match evalSmt σ e with | .L xs => .B xs.isEmpty | _ => .bad) := rfl

/-- Conditional reductions (reliable `rw`, avoiding fragile match-RHS simp lemmas). -/
theorem evalSmt_fstP_of {σ : Model} {e : SmtExpr} {x y : SVal} (h : evalSmt σ e = .P x y) :
    evalSmt σ (.fstP e) = x := by show (match evalSmt σ e with | .P x _ => x | _ => .bad) = x; rw [h]
theorem evalSmt_sndP_of {σ : Model} {e : SmtExpr} {x y : SVal} (h : evalSmt σ e = .P x y) :
    evalSmt σ (.sndP e) = y := by show (match evalSmt σ e with | .P _ y => y | _ => .bad) = y; rw [h]
/-- A `pair`-valued symbolic constant concretizes to the `Const.Pair` of its component
    concretizations. -/
theorem γ_sCon_pair {σ : Model} {e : SmtExpr} {x y : SVal} (h : evalSmt σ e = .P x y) :
    γ σ (.sCon e) = .VCon (.Pair (svalToConst x, svalToConst y)) := by
  simp only [γ_sCon, h, svalToConst]

/-- A `pair`-sorted expression evaluates to a `P`. -/
theorem evalSmt_pair {σ : Model} {e : SmtExpr} {sa sb : SmtSort}
    (h : SmtExpr.sortOf e = some (.pair sa sb)) : ∃ x y, evalSmt σ e = .P x y :=
  let ⟨x, y, hxy, _, _⟩ := hasSort_pair (evalSmt_hasSort σ h); ⟨x, y, hxy⟩

/-- Every element of a `data`-sorted list is a `D`, so the list is `ds.map .D`. -/
theorem list_all_data : ∀ {xs : List SVal}, (∀ x ∈ xs, HasSort .data x) →
    ∃ ds : List Moist.Plutus.Data, xs = ds.map .D
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
    obtain ⟨d, rfl⟩ := hasSort_data (h x (by simp))
    obtain ⟨ds, rfl⟩ := list_all_data (fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact ⟨d :: ds, rfl⟩

/-- A `list data`-sorted expression evaluates to `L (ds.map .D)` for some concrete `ds`. -/
theorem evalSmt_list_data {σ : Model} {e : SmtExpr}
    (h : SmtExpr.sortOf e = some (.list .data)) :
    ∃ ds : List Moist.Plutus.Data, evalSmt σ e = .L (ds.map .D) := by
  obtain ⟨xs, hxs, hall⟩ := hasSort_list (evalSmt_hasSort σ h)
  obtain ⟨ds, rfl⟩ := list_all_data hall
  exact ⟨ds, hxs⟩

/-- `svalToData` recovers a list of `Data` from `ds.map .D`. -/
theorem mapM_svalToData_map_D : ∀ ds : List Moist.Plutus.Data, (ds.map .D).mapM svalToData = some ds
  | [] => rfl
  | d :: ds => by
    rw [List.map_cons, List.mapM_cons]
    simp [svalToData, mapM_svalToData_map_D ds]

/-- A list of `Data` concretizes to the `ConstDataList`. -/
theorem svalToConst_L_data (ds : List Moist.Plutus.Data) :
    svalToConst (.L (ds.map .D)) = .ConstDataList ds := by
  simp only [svalToConst, mapM_svalToData_map_D]

/-- A true `isConstr` guard means the `Data` is a `Constr`. -/
theorem isConstr_true {σ : Model} {e : SmtExpr} {d : Plutus.Data} (hde : evalSmt σ e = .D d)
    (hd : evalSmt σ (.uop .isConstr e) = .B true) : ∃ tag flds, d = .Constr tag flds := by
  cases d <;> simp_all [evalSmt, evalUop]

/-- A true `isList` guard means the `Data` is a `List`. -/
theorem isList_true {σ : Model} {e : SmtExpr} {d : Plutus.Data} (hde : evalSmt σ e = .D d)
    (hd : evalSmt σ (.uop .isList e) = .B true) : ∃ ds, d = .List ds := by
  cases d <;> simp_all [evalSmt, evalUop]

/-- A true `¬ nullL` guard on a `data`-list means the list is non-empty. -/
theorem notNull_cons {σ : Model} {e : SmtExpr} {ds : List Plutus.Data}
    (he : evalSmt σ e = .L (ds.map .D)) (hd : evalSmt σ (.not (.nullL e)) = .B true) :
    ∃ d ds', ds = d :: ds' := by
  cases ds with
  | nil => simp [evalSmt, he, evalUop] at hd
  | cons d ds' => exact ⟨d, ds', rfl⟩

/-- Structure of a successful `unConstrOp`. -/
theorem unConstrOp_some {e v g : SmtExpr} (h : unConstrOp e = some (v, g)) :
    v = .mkpair (.uop .constrTag e) (.uop .dArgs e) ∧ g = .uop .isConstr e ∧
      SmtExpr.sortOf e = some .data := by
  unfold unConstrOp at h; split at h
  · rename_i hs; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm, hs⟩
  · exact absurd h (by simp)

/-- Structure of a successful `pairProj`. -/
theorem pairProj_some {mk : SmtExpr → SmtExpr} {e v g : SmtExpr} (h : pairProj mk e = some (v, g)) :
    v = mk e ∧ g = .trueE ∧ ∃ sa sb, SmtExpr.sortOf e = some (.pair sa sb) := by
  unfold pairProj at h; split at h
  · rename_i sa sb hs; simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm, sa, sb, hs⟩
  · exact absurd h (by simp)

/-- Structure of a successful `listOp`. -/
theorem listOpNE_some {mk : SmtExpr → SmtExpr} {e v g : SmtExpr} (h : listOpNE mk e = some (v, g)) :
    v = mk e ∧ g = .not (.nullL e) ∧ SmtExpr.sortOf e = some (.list .data) := by
  unfold listOpNE at h; split at h
  · rename_i hs; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm, hs⟩
  · exact absurd h (by simp)
theorem listOpT_some {mk : SmtExpr → SmtExpr} {e v g : SmtExpr} (h : listOpT mk e = some (v, g)) :
    v = mk e ∧ g = .trueE ∧ SmtExpr.sortOf e = some (.list .data) := by
  unfold listOpT at h; split at h
  · rename_i hs; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm, hs⟩
  · exact absurd h (by simp)

/-! ### `Data` destructor denotations (axiom-free, via `evalBuiltin_concrete`) -/

theorem evalBuiltin_unConstrData (tag : Int) (flds : List Plutus.Data) :
    evalBuiltin .UnConstrData [.VCon (.Data (.Constr tag flds))]
      = some (.VCon (.Pair (.Integer tag, .ConstDataList flds))) := by
  have := evalBuiltin_concrete (b := .UnConstrData) (by decide) [.Data (.Constr tag flds)]
  simpa using this
theorem evalBuiltin_unListData (ds : List Plutus.Data) :
    evalBuiltin .UnListData [.VCon (.Data (.List ds))] = some (.VCon (.ConstDataList ds)) := by
  have := evalBuiltin_concrete (b := .UnListData) (by decide) [.Data (.List ds)]; simpa using this
theorem evalBuiltin_fstPair (c1 c2 : Const) :
    evalBuiltin .FstPair [.VCon (.Pair (c1, c2))] = some (.VCon c1) := by
  have := evalBuiltin_concrete (b := .FstPair) (by decide) [.Pair (c1, c2)]; simpa using this
theorem evalBuiltin_sndPair (c1 c2 : Const) :
    evalBuiltin .SndPair [.VCon (.Pair (c1, c2))] = some (.VCon c2) := by
  have := evalBuiltin_concrete (b := .SndPair) (by decide) [.Pair (c1, c2)]; simpa using this
theorem evalBuiltin_headList (d : Plutus.Data) (ds : List Plutus.Data) :
    evalBuiltin .HeadList [.VCon (.ConstDataList (d :: ds))] = some (.VCon (.Data d)) := by
  have := evalBuiltin_concrete (b := .HeadList) (by decide) [.ConstDataList (d :: ds)]; simpa using this
theorem evalBuiltin_tailList (d : Plutus.Data) (ds : List Plutus.Data) :
    evalBuiltin .TailList [.VCon (.ConstDataList (d :: ds))] = some (.VCon (.ConstDataList ds)) := by
  have := evalBuiltin_concrete (b := .TailList) (by decide) [.ConstDataList (d :: ds)]; simpa using this
theorem evalBuiltin_nullList (ds : List Plutus.Data) :
    evalBuiltin .NullList [.VCon (.ConstDataList ds)] = some (.VCon (.Bool ds.isEmpty)) := by
  have := evalBuiltin_concrete (b := .NullList) (by decide) [.ConstDataList ds]; simpa using this

set_option maxHeartbeats 1000000 in
/-- **First-order builtin agreement.**  When `smtBuiltin` commits and the guard holds at
    `σ`, the concretized arguments run through `evalBuiltin` to the concretized result.  The
    division family (`Divide`/`Mod`/`Quotient`/`Remainder`) uses the trusted `evalBuiltin_*`
    denotations (R3); everything else (arithmetic, comparison, `Data`/`ByteString`
    injection/projection/equality) is discharged axiom-free via the per-builtin theorems
    (`evalBuiltin_concrete`). -/
theorem smtBuiltin_adequate (σ : Model) {b : BuiltinFun} {exprs : List SmtExpr} {v g : SmtExpr}
    (h : smtBuiltin b exprs = some (v, g)) (hd : evalSmt σ g = .B true) :
    evalBuiltin b (exprs.map (fun e => γ σ (.sCon e))) = some (γ σ (.sCon v)) := by
  cases exprs with
  | nil => simp [smtBuiltin] at h
  | cons ey rest => cases rest with
    | nil =>
      -- UNARY  [ey] : Data/ByteString injection & projection (axiom-free)
      cases b <;> simp only [smtBuiltin] at h <;>
        first
        | -- IData : int → data
          (obtain ⟨hv, _, hse⟩ := uOp_some h; subst hv
           obtain ⟨n, hn⟩ := evalSmt_int hse
           rw [show ([ey].map fun e => γ σ (.sCon e)) = [γ σ (.sCon ey)] from rfl,
               γ_sCon_I hn, evalBuiltin_iData]
           simp only [γ_sCon, evalSmt_uop, hn, evalUop, svalToConst])
        | -- BData / LengthOfByteString : bytes operand
          (obtain ⟨hv, _, hse⟩ := uOp_some h; subst hv
           obtain ⟨bs, hbs⟩ := evalSmt_bytes hse
           rw [show ([ey].map fun e => γ σ (.sCon e)) = [γ σ (.sCon ey)] from rfl, γ_sCon_BS hbs]
           first | rw [evalBuiltin_bData] | rw [evalBuiltin_lengthOfByteString]
                 | rw [evalBuiltin_sha2_256] | rw [evalBuiltin_sha3_256]
                 | rw [evalBuiltin_blake2b_256] | rw [evalBuiltin_blake2b_224]
                 | rw [evalBuiltin_keccak_256] | rw [evalBuiltin_ripemd_160]
           simp only [γ_sCon, evalSmt_uop, hbs, evalUop, svalToConst])
        | -- UnIData : projection guarded by `isI`
          (obtain ⟨hv, hg, hse⟩ := uOp_some h; subst hv
           obtain ⟨d, hde⟩ := evalSmt_data hse
           obtain ⟨n, hdn⟩ := isI_true hde (hg ▸ hd); subst hdn
           rw [show ([ey].map fun e => γ σ (.sCon e)) = [γ σ (.sCon ey)] from rfl,
               γ_sCon_D hde, evalBuiltin_unIData]
           simp only [γ_sCon, evalSmt_uop, hde, evalUop, svalToConst])
        | -- UnBData : projection guarded by `isB`
          (obtain ⟨hv, hg, hse⟩ := uOp_some h; subst hv
           obtain ⟨d, hde⟩ := evalSmt_data hse
           obtain ⟨bs, hdb⟩ := isB_true hde (hg ▸ hd); subst hdb
           rw [show ([ey].map fun e => γ σ (.sCon e)) = [γ σ (.sCon ey)] from rfl,
               γ_sCon_D hde, evalBuiltin_unBData]
           simp only [γ_sCon, evalSmt_uop, hde, evalUop, svalToConst])
        | -- UnConstrData : Data → builtin pair (Integer tag, list data fields)
          (obtain ⟨hv, hg, hse⟩ := unConstrOp_some h; subst hv
           obtain ⟨d, hde⟩ := evalSmt_data hse
           obtain ⟨tag, flds, hdf⟩ := isConstr_true hde (hg ▸ hd); subst hdf
           rw [show ([ey].map fun e => γ σ (.sCon e)) = [γ σ (.sCon ey)] from rfl,
               γ_sCon_D hde, evalBuiltin_unConstrData]
           simp only [γ_sCon, evalSmt_mkpair, evalSmt_uop, hde, evalUop, svalToConst_P,
             svalToConst_I, svalToConst_L_data])
        | -- UnListData : Data → list data (guarded by `isList`)
          (obtain ⟨hv, hg, hse⟩ := uOp_some h; subst hv
           obtain ⟨d, hde⟩ := evalSmt_data hse
           obtain ⟨ds, hdl⟩ := isList_true hde (hg ▸ hd); subst hdl
           rw [show ([ey].map fun e => γ σ (.sCon e)) = [γ σ (.sCon ey)] from rfl,
               γ_sCon_D hde, evalBuiltin_unListData]
           simp only [γ_sCon, evalSmt_uop, hde, evalUop, svalToConst_L_data])
        | -- FstPair : pair a b → a
          (obtain ⟨hv, _, sa, sb, hse⟩ := pairProj_some h; subst hv
           obtain ⟨x, y, hxy⟩ := evalSmt_pair (σ := σ) hse
           rw [show ([ey].map fun e => γ σ (.sCon e)) = [γ σ (.sCon ey)] from rfl,
               γ_sCon_pair hxy, evalBuiltin_fstPair, γ_sCon, evalSmt_fstP_of hxy])
        | -- SndPair : pair a b → b
          (obtain ⟨hv, _, sa, sb, hse⟩ := pairProj_some h; subst hv
           obtain ⟨x, y, hxy⟩ := evalSmt_pair (σ := σ) hse
           rw [show ([ey].map fun e => γ σ (.sCon e)) = [γ σ (.sCon ey)] from rfl,
               γ_sCon_pair hxy, evalBuiltin_sndPair, γ_sCon, evalSmt_sndP_of hxy])
        | -- HeadList : list data → data (guarded non-empty)
          (obtain ⟨hv, hg, hse⟩ := listOpNE_some h; subst hv
           obtain ⟨ds, hds⟩ := evalSmt_list_data (σ := σ) hse
           rw [hg] at hd
           obtain ⟨d0, ds', hdd⟩ := notNull_cons hds hd; subst hdd
           have hLHS : γ σ (.sCon ey) = .VCon (.ConstDataList (d0 :: ds')) := by
             rw [γ_sCon, hds, svalToConst_L_data]
           have hval : evalSmt σ (.headL .data ey) = .D d0 := by
             simp only [evalSmt_headL, hds, List.map_cons]
           rw [show ([ey].map fun e => γ σ (.sCon e)) = [γ σ (.sCon ey)] from rfl,
               hLHS, evalBuiltin_headList, γ_sCon, hval, svalToConst])
        | -- TailList : list data → list data (guarded non-empty)
          (obtain ⟨hv, hg, hse⟩ := listOpNE_some h; subst hv
           obtain ⟨ds, hds⟩ := evalSmt_list_data (σ := σ) hse
           rw [hg] at hd
           obtain ⟨d0, ds', hdd⟩ := notNull_cons hds hd; subst hdd
           have hLHS : γ σ (.sCon ey) = .VCon (.ConstDataList (d0 :: ds')) := by
             rw [γ_sCon, hds, svalToConst_L_data]
           have hval : evalSmt σ (.tailL ey) = .L (ds'.map .D) := by
             simp only [evalSmt_tailL, hds, List.map_cons]
           rw [show ([ey].map fun e => γ σ (.sCon e)) = [γ σ (.sCon ey)] from rfl,
               hLHS, evalBuiltin_tailList, γ_sCon, hval, svalToConst_L_data])
        | -- NullList : list data → bool
          (obtain ⟨hv, _, hse⟩ := listOpT_some h; subst hv
           obtain ⟨ds, hds⟩ := evalSmt_list_data (σ := σ) hse
           have hLHS : γ σ (.sCon ey) = .VCon (.ConstDataList ds) := by
             rw [γ_sCon, hds, svalToConst_L_data]
           have hval : evalSmt σ (.nullL ey) = .B ds.isEmpty := by
             simp only [evalSmt_nullL, hds, List.isEmpty_map]
           rw [show ([ey].map fun e => γ σ (.sCon e)) = [γ σ (.sCon ey)] from rfl,
               hLHS, evalBuiltin_nullList, γ_sCon, hval, svalToConst])
        | exact absurd h (by simp)
    | cons ex rest2 => cases rest2 with
      | cons _ _ => simp [smtBuiltin] at h
      | nil =>
        -- BINARY  [ey, ex]
        cases b <;> simp only [smtBuiltin] at h <;>
          first
          | -- integer arithmetic / comparison / division : value `bin op ex ey`
            (obtain ⟨hv, hg, hsx, hsy⟩ := sortBin_some h
             obtain ⟨X, hX⟩ := evalSmt_int hsx
             obtain ⟨Y, hY⟩ := evalSmt_int hsy
             subst hv
             have hmap : ([ey, ex].map fun e => γ σ (.sCon e))
                 = [γ σ (.sCon ey), γ σ (.sCon ex)] := rfl
             rw [hmap, γ_sCon_I hY, γ_sCon_I hX]
             first
             | rw [evalBuiltin_addInteger]
             | rw [evalBuiltin_subtractInteger]
             | rw [evalBuiltin_multiplyInteger]
             | rw [evalBuiltin_equalsInteger]
             | rw [evalBuiltin_lessThanInteger]
             | rw [evalBuiltin_lessThanEqualsInteger]
             | (subst hg; rw [evalBuiltin_divideInteger,    if_neg (neZeroE_true hY hd)])
             | (subst hg; rw [evalBuiltin_modInteger,       if_neg (neZeroE_true hY hd)])
             | (subst hg; rw [evalBuiltin_quotientInteger,  if_neg (neZeroE_true hY hd)])
             | (subst hg; rw [evalBuiltin_remainderInteger, if_neg (neZeroE_true hY hd)])
             simp only [γ_sCon, evalSmt_bin, hX, hY, evalBin, svalToConst])
          | -- EqualsData : data operands (axiom-free)
            (obtain ⟨hv, _, hsx, hsy⟩ := sortBin_some h
             obtain ⟨dx, hX⟩ := evalSmt_data hsx
             obtain ⟨dy, hY⟩ := evalSmt_data hsy
             subst hv
             rw [show ([ey, ex].map fun e => γ σ (.sCon e)) = [γ σ (.sCon ey), γ σ (.sCon ex)] from rfl,
                 γ_sCon_D hY, γ_sCon_D hX, evalBuiltin_equalsData]
             simp only [γ_sCon, evalSmt_bin, hX, hY, evalBin, svalToConst])
          | -- EqualsByteString : bytes operands (axiom-free)
            (obtain ⟨hv, _, hsx, hsy⟩ := sortBin_some h
             obtain ⟨bx, hX⟩ := evalSmt_bytes hsx
             obtain ⟨by_, hY⟩ := evalSmt_bytes hsy
             subst hv
             rw [show ([ey, ex].map fun e => γ σ (.sCon e)) = [γ σ (.sCon ey), γ σ (.sCon ex)] from rfl,
                 γ_sCon_BS hY, γ_sCon_BS hX, evalBuiltin_equalsByteString]
             simp only [γ_sCon, evalSmt_bin, hX, hY, evalBin, svalToConst])
          | exact absurd h (by simp)

/-- `symExtractCons` succeeds exactly on all-`sCon` argument lists, and then concretization
    `γL` is the pointwise concretization of the extracted expressions. -/
theorem γL_symExtractCons (σ : Model) : ∀ {args : List SymVal} {exprs : List SmtExpr},
    symExtractCons args = some exprs → γL σ args = exprs.map (fun e => γ σ (.sCon e)) := by
  intro args
  induction args with
  | nil => intro exprs h; simp only [symExtractCons, Option.some.injEq] at h; subst h; rfl
  | cons a rest ih =>
    intro exprs h
    cases a with
    | sCon e =>
      simp only [symExtractCons] at h
      cases hr : symExtractCons rest with
      | none => rw [hr] at h; simp at h
      | some es =>
        rw [hr] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
        simp only [γL, List.map_cons]; exact congrArg (γ σ (.sCon e) :: ·) (ih hr)
    | sConst _ => simp [symExtractCons] at h
    | sLam _ _ => simp [symExtractCons] at h
    | sDelay _ _ => simp [symExtractCons] at h
    | sConstr _ _ => simp [symExtractCons] at h
    | sBuiltin _ _ _ => simp [symExtractCons] at h
    | sIte _ _ _ => simp [symExtractCons] at h

/-! ### Pass-through builtin denotations (all `rfl` — they short-circuit `evalBuiltin`) -/
theorem evalBuiltin_chooseUnit (r : CekValue) : evalBuiltin .ChooseUnit [r, .VCon .Unit] = some r := rfl
theorem evalBuiltin_trace (r : CekValue) (s : String) :
    evalBuiltin .Trace [r, .VCon (.String s)] = some r := rfl
theorem evalBuiltin_chooseData (bC iC lC mC cC : CekValue) (d : Plutus.Data) :
    evalBuiltin .ChooseData [bC, iC, lC, mC, cC, .VCon (.Data d)]
      = some (match d with | .Constr _ _ => cC | .Map _ => mC | .List _ => lC | .I _ => iC
                           | .B _ => bC) := by cases d <;> rfl
theorem evalBuiltin_chooseList_data (cC nC : CekValue) (l : List Plutus.Data) :
    evalBuiltin .ChooseList [cC, nC, .VCon (.ConstDataList l)]
      = some (if l.isEmpty then nC else cC) := rfl
theorem evalBuiltin_chooseList_list (cC nC : CekValue) (l : List Const) :
    evalBuiltin .ChooseList [cC, nC, .VCon (.ConstList l)] = some (if l.isEmpty then nC else cC) := rfl
theorem evalBuiltin_mkCons_data (tl : List Plutus.Data) (hd : Plutus.Data) :
    evalBuiltin .MkCons [.VCon (.ConstDataList tl), .VCon (.Data hd)]
      = some (.VCon (.ConstDataList (hd :: tl))) := rfl
theorem evalBuiltin_mkCons_list (tl : List Const) (c : Const) :
    evalBuiltin .MkCons [.VCon (.ConstList tl), .VCon c] = some (.VCon (.ConstList (c :: tl))) := rfl

/-- **Pass-through builtin agreement.**  `IfThenElse`/`ChooseUnit`/`Trace`/`ChooseData`/
    `ChooseList`/`MkCons` return one of their arguments (or a concrete list cons); the
    concretized result is what `evalBuiltin` (which short-circuits through
    `evalBuiltinPassThrough`) produces.  For `IfThenElse` a symbolic boolean condition becomes
    an SMT `ite` that selects the same branch the concrete condition would (by `evalSmt_bool`). -/
theorem symBuiltinPassThrough_adequate (σ : Model) {b : BuiltinFun} {args : List SymVal}
    {o : SymOut} (h : symBuiltinPassThrough b args = some o) :
    evalBuiltin b (γL σ args) = some (γ σ o.value) := by
  match b, args, h with
  | .ChooseUnit, [result, .sConst .Unit], h =>
    simp only [symBuiltinPassThrough, Option.some.injEq] at h; subst h
    simp only [γL_cons, γL_nil, γ_sConst, evalBuiltin_chooseUnit]
  | .Trace, [result, .sConst (.String s)], h =>
    simp only [symBuiltinPassThrough, Option.some.injEq] at h; subst h
    simp only [γL_cons, γL_nil, γ_sConst, evalBuiltin_trace]
  | .ChooseData, [bC, iC, lC, mC, cC, .sConst (.Data d)], h =>
    simp only [symBuiltinPassThrough, Option.some.injEq] at h; subst h
    cases d <;> simp [γL_cons, γL_nil, γ_sConst, evalBuiltin_chooseData]
  | .ChooseList, [consC, nilC, .sConst (.ConstDataList l)], h =>
    simp only [symBuiltinPassThrough, Option.some.injEq] at h; subst h
    by_cases he : l.isEmpty <;> simp [γL_cons, γL_nil, γ_sConst, evalBuiltin_chooseList_data, he]
  | .ChooseList, [consC, nilC, .sConst (.ConstList l)], h =>
    simp only [symBuiltinPassThrough, Option.some.injEq] at h; subst h
    by_cases he : l.isEmpty <;> simp [γL_cons, γL_nil, γ_sConst, evalBuiltin_chooseList_list, he]
  | .MkCons, [.sConst (.ConstDataList tl), .sConst (.Data hd)], h =>
    simp only [symBuiltinPassThrough, Option.some.injEq] at h; subst h
    simp only [γL_cons, γL_nil, γ_sConst, evalBuiltin_mkCons_data]
  | .MkCons, [.sConst (.ConstList tl), .sConst c], h =>
    simp only [symBuiltinPassThrough, Option.some.injEq] at h; subst h
    simp only [γL_cons, γL_nil, γ_sConst, evalBuiltin_mkCons_list]
  | .IfThenElse, [elseV, thenV, .sCon condE], h =>
    simp only [symBuiltinPassThrough] at h
    -- split the `asLitBool / sort` dispatch exactly as the definition does
    rcases hcl : asLitBool condE with _ | bcond
    · -- symbolic condition: first-order branches ⇒ SMT `ite`; lazy branches ⇒ deferred `sIte`
      rw [hcl] at h
      by_cases hsort : SmtExpr.sortOf condE = some .bool
      · obtain ⟨bc, hbc⟩ := evalSmt_bool (σ := σ) hsort
        cases thenV <;> cases elseV <;>
          simp only [hsort, if_true, Option.some.injEq] at h <;> subst h <;> cases bc <;>
          simp [γL_cons, γL_nil, γ_sCon, svalToConst, hbc, evalBuiltin_ifThenElse, evalSmt,
            γ_sIte_true, γ_sIte_false]
      · simp [hsort] at h
    · -- concrete condition: `condE = litB bcond`, pick the branch directly
      have hcond : condE = .litB bcond := by cases condE <;> simp_all [asLitBool]
      subst hcond
      rw [hcl] at h
      cases bcond <;>
        (simp only [Option.some.injEq] at h; subst h
         simp [γL_cons, γL_nil, γ_sCon, svalToConst, evalSmt_litB, evalBuiltin_ifThenElse])

/-- Concretization of an all-concrete symbolic argument list is the `VCon`-mapping of the
    extracted constants (at any model). -/
theorem γL_symConcrete (σ : Model) : ∀ {args : List SymVal} {cs : List Const},
    symConcrete args = some cs → γL σ args = cs.map (CekValue.VCon ·) := by
  intro args
  induction args with
  | nil => intro cs h; simp only [symConcrete, Option.some.injEq] at h; subst h; rfl
  | cons a rest ih =>
    intro cs h
    cases a with
    | sConst c =>
      simp only [symConcrete] at h
      cases hr : symConcrete rest with
      | none => simp [hr] at h
      | some cs' =>
        simp only [hr, Option.map_some, Option.some.injEq] at h; subst h
        simp only [γL_cons, γ_sConst, List.map_cons, ih hr]
    | sCon e =>
      cases e with
      | litI n =>
        simp only [symConcrete] at h
        cases hr : symConcrete rest with
        | none => simp [hr] at h
        | some cs' =>
          simp only [hr, Option.map_some, Option.some.injEq] at h; subst h
          simp only [γL_cons, γ_sCon, evalSmt, svalToConst, List.map_cons, ih hr]
      | litB b =>
        simp only [symConcrete] at h
        cases hr : symConcrete rest with
        | none => simp [hr] at h
        | some cs' =>
          simp only [hr, Option.map_some, Option.some.injEq] at h; subst h
          simp only [γL_cons, γ_sCon, evalSmt, svalToConst, List.map_cons, ih hr]
      | var _ _ => simp [symConcrete] at h
      | neg _ => simp [symConcrete] at h
      | not _ => simp [symConcrete] at h
      | bin _ _ _ => simp [symConcrete] at h
      | uop _ _ => simp [symConcrete] at h
      | ite _ _ _ => simp [symConcrete] at h
      | mkpair _ _ => simp [symConcrete] at h
      | fstP _ => simp [symConcrete] at h
      | sndP _ => simp [symConcrete] at h
      | nilL _ => simp [symConcrete] at h
      | consL _ _ => simp [symConcrete] at h
      | headL _ _ => simp [symConcrete] at h
      | tailL _ => simp [symConcrete] at h
      | nullL _ => simp [symConcrete] at h
    | sLam _ _ => simp [symConcrete] at h
    | sDelay _ _ => simp [symConcrete] at h
    | sConstr _ _ => simp [symConcrete] at h
    | sBuiltin _ _ _ => simp [symConcrete] at h
    | sIte _ _ _ => simp [symConcrete] at h

/-- The symbolic-path agreement (first-order `smtBuiltin`). -/
theorem symBuiltinSymbolic_adequate (σ : Model) {b : BuiltinFun} {args : List SymVal}
    {o : SymOut} (h : symBuiltinSymbolic b args = some o) (hd : evalSmt σ o.defined = .B true) :
    evalBuiltin b (γL σ args) = some (γ σ o.value) := by
  unfold symBuiltinSymbolic at h
  cases hex : symExtractCons args with
  | none => simp [hex] at h
  | some exprs =>
    simp only [hex] at h
    cases hsb : smtBuiltin b exprs with
    | none => simp [hsb] at h
    | some vg =>
      obtain ⟨v, g⟩ := vg
      simp only [hsb, Option.some.injEq] at h; subst h
      rw [γL_symExtractCons σ hex]
      exact smtBuiltin_adequate σ hsb hd

/-- **Saturated builtin agreement** (composes pass-through + concrete fold + symbolic). -/
theorem symEvalBuiltin_adequate (σ : Model) {b : BuiltinFun} {args : List SymVal} {o : SymOut}
    (h : symEvalBuiltin b args = some o) (hd : evalSmt σ o.defined = .B true) :
    evalBuiltin b (γL σ args) = some (γ σ o.value) := by
  unfold symEvalBuiltin at h
  cases hpt : symBuiltinPassThrough b args with
  | some o' =>
    simp only [hpt, Option.some.injEq] at h; subst h
    exact symBuiltinPassThrough_adequate σ hpt
  | none =>
    simp only [hpt] at h
    cases hsym : symBuiltinSymbolic b args with
    | some o' =>
      simp only [hsym, Option.some.injEq] at h; subst h
      exact symBuiltinSymbolic_adequate σ hsym hd
    | none =>
      simp only [hsym] at h
      cases hpass : isPassthroughBuiltin b with
      | true => simp [hpass] at h
      | false =>
        simp only [hpass] at h
        cases hsc : symConcrete args with
        | none => simp [hsc] at h
        | some consts =>
          simp only [hsc] at h
          obtain ⟨c, hc, ho⟩ := Option.map_eq_some_iff.mp h
          subst ho
          rw [γL_symConcrete σ hsc, evalBuiltin_concrete hpass consts, hc]; rfl

/-! ### `sIte` (bounded-unrolling) helpers -/

theorem γ_sCon_ite_true {σ : Model} {cond aE bE : SmtExpr} (hc : evalSmt σ cond = .B true) :
    γ σ (.sCon (.ite cond aE bE)) = γ σ (.sCon aE) := by simp only [γ_sCon, evalSmt, hc]
theorem γ_sCon_ite_false {σ : Model} {cond aE bE : SmtExpr} (hc : evalSmt σ cond = .B false) :
    γ σ (.sCon (.ite cond aE bE)) = γ σ (.sCon bE) := by simp only [γ_sCon, evalSmt, hc]
/-- A true `ite cond X Y` definedness with `cond` true at `σ` gives `X` defined. -/
theorem ite_true_def {σ : Model} {cond X Y : SmtExpr} (hc : evalSmt σ cond = .B true)
    (hd : evalSmt σ (.ite cond X Y) = .B true) : evalSmt σ X = .B true := by
  simp only [evalSmt, hc] at hd; exact hd
theorem ite_false_def {σ : Model} {cond X Y : SmtExpr} (hc : evalSmt σ cond = .B false)
    (hd : evalSmt σ (.ite cond X Y) = .B true) : evalSmt σ Y = .B true := by
  simp only [evalSmt, hc] at hd; exact hd

/-- `falseE` denotes `B false` at every model (definitional). -/
theorem evalSmt_falseE (σ : Model) : evalSmt σ .falseE = .B false := rfl

/-- `B false ≠ B true` (the `SVal` constructor is injective). -/
theorem Bfalse_ne_Btrue : (SVal.B false ≠ SVal.B true) := by
  intro h; injection h with h; exact Bool.noConfusion h

/-- `combineIte` commits in four shapes: both branches first-order (full `ite`); both present
    but not both first-order (the choice is *kept* as `sIte`); or exactly one branch present
    (the absent path gated `false`). -/
theorem combineIte_some {cond : SmtExpr} {aR bR : Option SymOut} {o : SymOut}
    (h : combineIte cond aR bR = some o) :
    (∃ aE ad bE bd, aR = some ⟨.sCon aE, ad⟩ ∧ bR = some ⟨.sCon bE, bd⟩ ∧
        o = ⟨.sCon (.ite cond aE bE), .ite cond ad bd⟩) ∨
    (∃ va ad vb bd, aR = some ⟨va, ad⟩ ∧ bR = some ⟨vb, bd⟩ ∧
        o = ⟨.sIte cond va vb, .ite cond ad bd⟩) ∨
    (∃ va ad, aR = some ⟨va, ad⟩ ∧ bR = none ∧ o = ⟨va, .ite cond ad .falseE⟩) ∨
    (∃ vb bd, aR = none ∧ bR = some ⟨vb, bd⟩ ∧ o = ⟨vb, .ite cond .falseE bd⟩) := by
  unfold combineIte at h; split at h <;> first
    | exact Or.inl ⟨_, _, _, _, rfl, rfl, by simpa using h.symm⟩
    | exact Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, by simpa using h.symm⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, by simpa using h.symm⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, rfl, by simpa using h.symm⟩))
    | simp at h

/-! ## The core simulation — `symEval` adequate to `bigEval`

The forward/soundness direction, by **fuel induction mirroring `bigEval`'s structure**
(the same five mutual functions, the same `(fuel, sizeOf)` measure as `evalFwd` in
`Moist.Verified.BigStep`).  Each case lines up 1:1 with a `bigEval` clause; the only work is
`γ`/`evalSmt` commutation (the leaves), the builtin-agreement lemmas (saturation), and
destructuring the conjoined `defined` guard (`and_true_split`). -/

mutual
  /-- If `symEval` commits and its definedness holds at `σ`, then `bigEval` on the
      `σ`-concretized environment yields the `σ`-concretized value. -/
  theorem symEval_adequate (σ : Model) : ∀ {f : Nat} {ρ : SymEnv} {t : Term} {o : SymOut},
      symEval f ρ t = some o → evalSmt σ o.defined = .B true →
      bigEval f (γE σ ρ) t = some (γ σ o.value)
    | 0, _, _, _, h, _ => by simp [symEval] at h
    | _ + 1, ρ, .Var k, o, h, _ => by
        cases hl : SymEnv.lookup ρ k with
        | none => simp [symEval, hl] at h
        | some w =>
          simp only [symEval, hl, Option.map_some, Option.some.injEq] at h; subst h
          simp only [bigEval, γE_lookup, hl, Option.map_some]
    | _ + 1, _, .Constant cb, o, h, _ => by
        obtain ⟨c, bt⟩ := cb
        simp only [symEval, Option.some.injEq] at h; subst h
        simp only [bigEval, γ_constToSym]
    | _ + 1, _, .Builtin b, o, h, _ => by
        simp only [symEval, Option.some.injEq] at h; subst h
        simp only [bigEval, γ_sBuiltin, γL_nil]
    | _ + 1, ρ, .Lam _ body, o, h, _ => by
        simp only [symEval, Option.some.injEq] at h; subst h
        simp only [bigEval, γ_sLam]
    | _ + 1, ρ, .Delay body, o, h, _ => by
        simp only [symEval, Option.some.injEq] at h; subst h
        simp only [bigEval, γ_sDelay]
    | f + 1, ρ, .Apply fn ar, o, h, hd => by
        cases hf : symEval f ρ fn with
        | none => simp [symEval, hf] at h
        | some of =>
          cases ha : symEval f ρ ar with
          | none => simp [symEval, hf, ha] at h
          | some oa =>
            cases hap : symApply f of.value oa.value with
            | none => simp [symEval, hf, ha, hap] at h
            | some oap =>
              simp only [symEval, hf, ha, hap, Option.some.injEq] at h; subst h
              obtain ⟨hdf, hdr⟩ := and_true_split σ hd
              obtain ⟨hda, hdap⟩ := and_true_split σ hdr
              simp only [bigEval, symEval_adequate σ hf hdf, symEval_adequate σ ha hda,
                symApply_adequate σ hap hdap]
    | f + 1, ρ, .Force t, o, h, hd => by
        cases ht : symEval f ρ t with
        | none => simp [symEval, ht] at h
        | some ot =>
          cases hfo : symForce f ot.value with
          | none => simp [symEval, ht, hfo] at h
          | some ofo =>
            simp only [symEval, ht, hfo, Option.some.injEq] at h; subst h
            obtain ⟨hdt, hdfo⟩ := and_true_split σ hd
            simp only [bigEval, symEval_adequate σ ht hdt, symForce_adequate σ hfo hdfo]
    | f + 1, ρ, .Constr tag ms, o, h, hd => by
        cases hl : symEvalList f ρ ms with
        | none => simp [symEval, hl] at h
        | some vsd =>
          obtain ⟨vs, d⟩ := vsd
          simp only [symEval, hl, Option.some.injEq] at h; subst h
          simp only [bigEval, symEvalList_adequate σ hl hd, γ_sConstr]
    | f + 1, ρ, .Case scrut alts, o, h, hd => by
        cases hsc : symEval f ρ scrut with
        | none => simp [symEval, hsc] at h
        | some osc =>
          cases hv : osc.value with
          | sConstr tag fields =>
            cases hat : alts[tag]? with
            | none => simp [symEval, hsc, hv, hat] at h
            | some alt =>
              cases halt : symEval f ρ alt with
              | none => simp [symEval, hsc, hv, hat, halt] at h
              | some oalt =>
                cases hap : symApplyList f oalt.value fields with
                | none => simp [symEval, hsc, hv, hat, halt, hap] at h
                | some oap =>
                  simp only [symEval, hsc, hv, hat, halt, hap, Option.some.injEq] at h; subst h
                  obtain ⟨hdsc, hdr⟩ := and_true_split σ hd
                  obtain ⟨hdalt, hdap⟩ := and_true_split σ hdr
                  have ihsc := symEval_adequate σ hsc hdsc
                  rw [hv] at ihsc; simp only [γ_sConstr] at ihsc
                  simp only [bigEval, ihsc, hat, symEval_adequate σ halt hdalt]
                  exact symApplyList_adequate σ hap hdap
          | sCon _ => simp [symEval, hsc, hv] at h
          | sConst _ => simp [symEval, hsc, hv] at h
          | sLam _ _ => simp [symEval, hsc, hv] at h
          | sDelay _ _ => simp [symEval, hsc, hv] at h
          | sBuiltin _ _ _ => simp [symEval, hsc, hv] at h
          | sIte cond va vb =>
            -- symbolic *choice* of constructors ⇒ `Case` distributes through it (`symCase`)
            simp only [symEval, hsc, hv] at h
            cases hcase : symCase f ρ (.sIte cond va vb) alts with
            | none => rw [hcase] at h; simp at h
            | some oc =>
              rw [hcase] at h; simp only [Option.some.injEq] at h; subst h
              obtain ⟨hdsc, hdoc⟩ := and_true_split σ hd
              have ihsc := symEval_adequate σ hsc hdsc
              rw [hv] at ihsc
              have ihc := symCase_adequate σ hcase hdoc ihsc
              exact ihc
    | _ + 1, _, .Error, _, h, _ => by simp [symEval] at h
  termination_by f _ t => (f, sizeOf t)

  /-- `symApply` adequate to `applyVal`. -/
  theorem symApply_adequate (σ : Model) : ∀ {f : Nat} {vf va : SymVal} {o : SymOut},
      symApply f vf va = some o → evalSmt σ o.defined = .B true →
      applyVal f (γ σ vf) (γ σ va) = some (γ σ o.value)
    | 0, _, _, _, h, _ => by simp [symApply] at h
    | f + 1, vf, va, o, h, hd => by
        cases vf with
        | sLam body ρ =>
          simp only [symApply] at h
          have ih := symEval_adequate σ h hd
          rw [γ_sLam, γE_extend] at *
          simpa only [applyVal] using ih
        | sBuiltin b args ea =>
          simp only [symApply] at h
          cases hh : ea.head with
          | argV =>
            cases ht : ea.tail with
            | some rest =>
              rw [hh, ht] at h; simp only [Option.some.injEq] at h; subst h
              simp only [applyVal, γ_sBuiltin, hh, ht, γL_cons]
            | none =>
              rw [hh, ht] at h
              have ih := symEvalBuiltin_adequate σ h hd
              simp only [applyVal, γ_sBuiltin, hh, ht]
              rw [γL_cons] at ih; exact ih
          | argQ => rw [hh] at h; simp at h
        | sCon _ => simp [symApply] at h
        | sConst _ => simp [symApply] at h
        | sDelay _ _ => simp [symApply] at h
        | sConstr _ _ => simp [symApply] at h
        | sIte cond a b =>
          -- applying a deferred *choice of functions*: distribute through the `sIte`, exactly
          -- as `symForce`/`symCase` do (`(if c then f else g) a ≡ if c then (f a) else (g a)`).
          simp only [symApply] at h
          rcases combineIte_some h with ⟨aE, ad, bE, bd, ha, hb, ho⟩ | ⟨wa, ad, wb, bd, ha, hb, ho⟩ |
            ⟨wa, ad, ha, hb, ho⟩ | ⟨wb, bd, ha, hb, ho⟩
          · subst ho
            cases hc : evalSmt σ cond with
            | B bb => cases bb with
              | true =>
                rw [γ_sIte_true σ hc, γ_sCon_ite_true hc]
                exact applyVal_mono (symApply_adequate σ ha (ite_true_def hc hd))
              | false =>
                rw [γ_sIte_false σ hc Bfalse_ne_Btrue, γ_sCon_ite_false hc]
                exact applyVal_mono (symApply_adequate σ hb (ite_false_def hc hd))
            | I _ => exact absurd hd (by simp [evalSmt, hc])
            | D _ => exact absurd hd (by simp [evalSmt, hc])
            | BS _ => exact absurd hd (by simp [evalSmt, hc])
            | P _ _ => exact absurd hd (by simp [evalSmt, hc])
            | L _ => exact absurd hd (by simp [evalSmt, hc])
            | bad => exact absurd hd (by simp [evalSmt, hc])
          · subst ho
            cases hc : evalSmt σ cond with
            | B bb => cases bb with
              | true =>
                rw [γ_sIte_true σ (a := a) (b := b) hc, γ_sIte_true σ (a := wa) (b := wb) hc]
                exact applyVal_mono (symApply_adequate σ ha (ite_true_def hc hd))
              | false =>
                rw [γ_sIte_false σ (a := a) (b := b) hc Bfalse_ne_Btrue,
                    γ_sIte_false σ (a := wa) (b := wb) hc Bfalse_ne_Btrue]
                exact applyVal_mono (symApply_adequate σ hb (ite_false_def hc hd))
            | I _ => exact absurd hd (by simp [evalSmt, hc])
            | D _ => exact absurd hd (by simp [evalSmt, hc])
            | BS _ => exact absurd hd (by simp [evalSmt, hc])
            | P _ _ => exact absurd hd (by simp [evalSmt, hc])
            | L _ => exact absurd hd (by simp [evalSmt, hc])
            | bad => exact absurd hd (by simp [evalSmt, hc])
          · subst ho
            cases hc : evalSmt σ cond with
            | B bb => cases bb with
              | true =>
                rw [γ_sIte_true σ hc]
                have ih := symApply_adequate σ ha (ite_true_def hc hd)
                exact applyVal_mono ih
              | false =>
                exfalso; have hf := ite_false_def hc hd; rw [evalSmt_falseE] at hf
                exact absurd hf Bfalse_ne_Btrue
            | I _ => exact absurd hd (by simp [evalSmt, hc])
            | D _ => exact absurd hd (by simp [evalSmt, hc])
            | BS _ => exact absurd hd (by simp [evalSmt, hc])
            | P _ _ => exact absurd hd (by simp [evalSmt, hc])
            | L _ => exact absurd hd (by simp [evalSmt, hc])
            | bad => exact absurd hd (by simp [evalSmt, hc])
          · subst ho
            cases hc : evalSmt σ cond with
            | B bb => cases bb with
              | true =>
                exfalso; have hf := ite_true_def hc hd; rw [evalSmt_falseE] at hf
                exact absurd hf Bfalse_ne_Btrue
              | false =>
                rw [γ_sIte_false σ hc Bfalse_ne_Btrue]
                have ih := symApply_adequate σ hb (ite_false_def hc hd)
                exact applyVal_mono ih
            | I _ => exact absurd hd (by simp [evalSmt, hc])
            | D _ => exact absurd hd (by simp [evalSmt, hc])
            | BS _ => exact absurd hd (by simp [evalSmt, hc])
            | P _ _ => exact absurd hd (by simp [evalSmt, hc])
            | L _ => exact absurd hd (by simp [evalSmt, hc])
            | bad => exact absurd hd (by simp [evalSmt, hc])
  termination_by f _ _ => (f, 0)

  /-- `symForce` adequate to `forceVal`. -/
  theorem symForce_adequate (σ : Model) : ∀ {f : Nat} {vt : SymVal} {o : SymOut},
      symForce f vt = some o → evalSmt σ o.defined = .B true →
      forceVal f (γ σ vt) = some (γ σ o.value)
    | 0, _, _, h, _ => by simp [symForce] at h
    | f + 1, vt, o, h, hd => by
        cases vt with
        | sDelay body ρ =>
          simp only [symForce] at h
          have ih := symEval_adequate σ h hd
          simpa only [forceVal, γ_sDelay] using ih
        | sBuiltin b args ea =>
          simp only [symForce] at h
          cases hh : ea.head with
          | argQ =>
            cases ht : ea.tail with
            | some rest =>
              rw [hh, ht] at h; simp only [Option.some.injEq] at h; subst h
              simp only [forceVal, γ_sBuiltin, hh, ht]
            | none =>
              rw [hh, ht] at h
              have ih := symEvalBuiltin_adequate σ h hd
              simpa only [forceVal, γ_sBuiltin, hh, ht] using ih
          | argV => rw [hh] at h; simp at h
        | sCon _ => simp [symForce] at h
        | sConst _ => simp [symForce] at h
        | sLam _ _ => simp [symForce] at h
        | sConstr _ _ => simp [symForce] at h
        | sIte cond a b =>
          -- forcing a deferred choice: `combineIte` of the two forced branches.  At a model,
          -- the SMT `ite` selects the branch the condition picks (matching the CEK); a
          -- fuel-exhausted (`none`) branch is gated out by `defined`.  When both forced
          -- branches survive but are not first-order, the choice is *kept* as `sIte`.
          simp only [symForce] at h
          rcases combineIte_some h with ⟨aE, ad, bE, bd, ha, hb, ho⟩ | ⟨va, ad, vb, bd, ha, hb, ho⟩ |
            ⟨va, ad, ha, hb, ho⟩ | ⟨vb, bd, ha, hb, ho⟩
          · -- both branches first-order: value collapses `sCon (ite aE bE)` per `cond`
            subst ho
            cases hc : evalSmt σ cond with
            | B bb => cases bb with
              | true =>
                rw [γ_sIte_true σ hc, γ_sCon_ite_true hc]
                exact forceVal_mono (symForce_adequate σ ha (ite_true_def hc hd))
              | false =>
                rw [γ_sIte_false σ hc Bfalse_ne_Btrue, γ_sCon_ite_false hc]
                exact forceVal_mono (symForce_adequate σ hb (ite_false_def hc hd))
            | I _ => exact absurd hd (by simp [evalSmt, hc])
            | D _ => exact absurd hd (by simp [evalSmt, hc])
            | BS _ => exact absurd hd (by simp [evalSmt, hc])
            | bad => exact absurd hd (by simp [evalSmt, hc])
            | P _ _ => exact absurd hd (by simp [evalSmt, hc])
            | L _ => exact absurd hd (by simp [evalSmt, hc])
          · -- both branches forced but not first-order: keep the choice `sIte va vb`
            subst ho
            cases hc : evalSmt σ cond with
            | B bb => cases bb with
              | true =>
                rw [γ_sIte_true σ (a := a) (b := b) hc, γ_sIte_true σ (a := va) (b := vb) hc]
                exact forceVal_mono (symForce_adequate σ ha (ite_true_def hc hd))
              | false =>
                rw [γ_sIte_false σ (a := a) (b := b) hc Bfalse_ne_Btrue,
                    γ_sIte_false σ (a := va) (b := vb) hc Bfalse_ne_Btrue]
                exact forceVal_mono (symForce_adequate σ hb (ite_false_def hc hd))
            | I _ => exact absurd hd (by simp [evalSmt, hc])
            | D _ => exact absurd hd (by simp [evalSmt, hc])
            | BS _ => exact absurd hd (by simp [evalSmt, hc])
            | bad => exact absurd hd (by simp [evalSmt, hc])
            | P _ _ => exact absurd hd (by simp [evalSmt, hc])
            | L _ => exact absurd hd (by simp [evalSmt, hc])
          · -- only `a` forced (`b` exhausted): `cond=true` ⇒ value `va`; `cond=false` ⇒ undefined
            subst ho
            cases hc : evalSmt σ cond with
            | B bb => cases bb with
              | true =>
                rw [γ_sIte_true σ hc]
                have ih := symForce_adequate σ ha (ite_true_def hc hd)
                exact forceVal_mono ih
              | false =>
                exfalso; have hf := ite_false_def hc hd; rw [evalSmt_falseE] at hf
                exact absurd hf Bfalse_ne_Btrue
            | I _ => exact absurd hd (by simp [evalSmt, hc])
            | D _ => exact absurd hd (by simp [evalSmt, hc])
            | BS _ => exact absurd hd (by simp [evalSmt, hc])
            | bad => exact absurd hd (by simp [evalSmt, hc])
            | P _ _ => exact absurd hd (by simp [evalSmt, hc])
            | L _ => exact absurd hd (by simp [evalSmt, hc])
          · -- only `b` forced (`a` exhausted): `cond=false` ⇒ value `vb`; `cond=true` ⇒ undefined
            subst ho
            cases hc : evalSmt σ cond with
            | B bb => cases bb with
              | true =>
                exfalso; have hf := ite_true_def hc hd; rw [evalSmt_falseE] at hf
                exact absurd hf Bfalse_ne_Btrue
              | false =>
                rw [γ_sIte_false σ hc Bfalse_ne_Btrue]
                have ih := symForce_adequate σ hb (ite_false_def hc hd)
                exact forceVal_mono ih
            | I _ => exact absurd hd (by simp [evalSmt, hc])
            | D _ => exact absurd hd (by simp [evalSmt, hc])
            | BS _ => exact absurd hd (by simp [evalSmt, hc])
            | bad => exact absurd hd (by simp [evalSmt, hc])
            | P _ _ => exact absurd hd (by simp [evalSmt, hc])
            | L _ => exact absurd hd (by simp [evalSmt, hc])
  termination_by f _ => (f, 0)

  /-- `symEvalList` adequate to `bigEvalList`. -/
  theorem symEvalList_adequate (σ : Model) : ∀ {f : Nat} {ρ : SymEnv} {ts : List Term}
      {vs : List SymVal} {d : SmtExpr},
      symEvalList f ρ ts = some (vs, d) → evalSmt σ d = .B true →
      bigEvalList f (γE σ ρ) ts = some (γL σ vs)
    | _, _, [], vs, d, h, _ => by
        simp only [symEvalList, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hvs, _⟩ := h; subst hvs; simp only [bigEvalList, γL_nil]
    | f, ρ, t :: ts, vs, d, h, hd => by
        cases ht : symEval f ρ t with
        | none => simp [symEvalList, ht] at h
        | some ot =>
          cases htl : symEvalList f ρ ts with
          | none => simp [symEvalList, ht, htl] at h
          | some vsd =>
            obtain ⟨vs', d'⟩ := vsd
            simp only [symEvalList, ht, htl, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hvs, hd'⟩ := h; subst hvs; subst hd'
            obtain ⟨hdt, hdtl⟩ := and_true_split σ hd
            simp only [bigEvalList, symEval_adequate σ ht hdt, symEvalList_adequate σ htl hdtl,
              γL_cons]
  termination_by f _ ts => (f, sizeOf ts)

  /-- `symApplyList` adequate to `applyValList`. -/
  theorem symApplyList_adequate (σ : Model) : ∀ {f : Nat} {vf : SymVal} {vs : List SymVal}
      {o : SymOut},
      symApplyList f vf vs = some o → evalSmt σ o.defined = .B true →
      applyValList f (γ σ vf) (γL σ vs) = some (γ σ o.value)
    | _, vf, [], o, h, _ => by
        simp only [symApplyList, Option.some.injEq] at h; subst h
        simp only [applyValList, γL_nil]
    | f, vf, a :: as, o, h, hd => by
        cases hap : symApply f vf a with
        | none => simp [symApplyList, hap] at h
        | some o1 =>
          cases hapl : symApplyList f o1.value as with
          | none => simp [symApplyList, hap, hapl] at h
          | some o2 =>
            simp only [symApplyList, hap, hapl, Option.some.injEq] at h; subst h
            obtain ⟨hd1, hd2⟩ := and_true_split σ hd
            simp only [γL_cons, applyValList, symApply_adequate σ hap hd1,
              symApplyList_adequate σ hapl hd2]
  termination_by f _ vs => (f, sizeOf vs)

  /-- `symCase` adequate to `bigEval`'s `Case` dispatch.  Given a scrutinee term whose
      `bigEval` value is `γ v`, distributing `Case` through the (possibly `sIte`) value `v`
      agrees with `bigEval (Case scrut alts)`.  The distributor evaluates a selected
      alternative one fuel level below `bigEval`'s `Case`, so the concrete leaf lifts the
      simulation with `bigEval_mono`/`applyValList_mono`; the `sIte` leaves recurse and
      collapse exactly as `symForce`'s deferred choice. -/
  theorem symCase_adequate (σ : Model) : ∀ {f : Nat} {ρ : SymEnv} {v : SymVal}
      {alts : List Term} {oc : SymOut} {scrut : Term},
      symCase f ρ v alts = some oc → evalSmt σ oc.defined = .B true →
      bigEval f (γE σ ρ) scrut = some (γ σ v) →
      bigEval (f + 1) (γE σ ρ) (.Case scrut alts) = some (γ σ oc.value)
    | 0, _, _, _, _, _, h, _, _ => by simp [symCase] at h
    | f + 1, ρ, .sConstr tag fields, alts, oc, scrut, h, hd, hscrut => by
        cases hat : alts[tag]? with
        | none => simp [symCase, hat] at h
        | some alt =>
          cases halt : symEval f ρ alt with
          | none => simp [symCase, hat, halt] at h
          | some oalt =>
            cases hap : symApplyList f oalt.value fields with
            | none => simp [symCase, hat, halt, hap] at h
            | some oap =>
              simp only [symCase, hat, halt, hap, Option.some.injEq] at h; subst h
              obtain ⟨hdalt, hdap⟩ := and_true_split σ hd
              simp only [γ_sConstr] at hscrut
              simp only [bigEval, hscrut, hat]
              rw [bigEval_mono (symEval_adequate σ halt hdalt)]
              exact applyValList_mono (symApplyList_adequate σ hap hdap)
    | f + 1, ρ, .sIte cond va vb, alts, oc, scrut, h, hd, hscrut => by
        simp only [symCase] at h
        rcases combineIte_some h with ⟨aE, ad, bE, bd, ha, hb, ho⟩ | ⟨wa, ad, wb, bd, ha, hb, ho⟩ |
          ⟨wa, ad, ha, hb, ho⟩ | ⟨wb, bd, ha, hb, ho⟩
        · subst ho
          cases hc : evalSmt σ cond with
          | B bb => cases bb with
            | true =>
              rw [γ_sIte_true σ hc] at hscrut
              rw [γ_sCon_ite_true hc]
              exact symCase_adequate σ ha (ite_true_def hc hd) hscrut
            | false =>
              rw [γ_sIte_false σ hc Bfalse_ne_Btrue] at hscrut
              rw [γ_sCon_ite_false hc]
              exact symCase_adequate σ hb (ite_false_def hc hd) hscrut
          | I _ => exact absurd hd (by simp [evalSmt, hc])
          | D _ => exact absurd hd (by simp [evalSmt, hc])
          | BS _ => exact absurd hd (by simp [evalSmt, hc])
          | bad => exact absurd hd (by simp [evalSmt, hc])
          | P _ _ => exact absurd hd (by simp [evalSmt, hc])
          | L _ => exact absurd hd (by simp [evalSmt, hc])
        · subst ho
          cases hc : evalSmt σ cond with
          | B bb => cases bb with
            | true =>
              rw [γ_sIte_true σ (a := va) (b := vb) hc] at hscrut
              rw [γ_sIte_true σ (a := wa) (b := wb) hc]
              exact symCase_adequate σ ha (ite_true_def hc hd) hscrut
            | false =>
              rw [γ_sIte_false σ (a := va) (b := vb) hc Bfalse_ne_Btrue] at hscrut
              rw [γ_sIte_false σ (a := wa) (b := wb) hc Bfalse_ne_Btrue]
              exact symCase_adequate σ hb (ite_false_def hc hd) hscrut
          | I _ => exact absurd hd (by simp [evalSmt, hc])
          | D _ => exact absurd hd (by simp [evalSmt, hc])
          | BS _ => exact absurd hd (by simp [evalSmt, hc])
          | bad => exact absurd hd (by simp [evalSmt, hc])
          | P _ _ => exact absurd hd (by simp [evalSmt, hc])
          | L _ => exact absurd hd (by simp [evalSmt, hc])
        · subst ho
          cases hc : evalSmt σ cond with
          | B bb => cases bb with
            | true =>
              rw [γ_sIte_true σ (a := va) (b := vb) hc] at hscrut
              have ih := symCase_adequate σ ha (ite_true_def hc hd) hscrut
              exact ih
            | false =>
              exfalso; have hf := ite_false_def hc hd; rw [evalSmt_falseE] at hf
              exact absurd hf Bfalse_ne_Btrue
          | I _ => exact absurd hd (by simp [evalSmt, hc])
          | D _ => exact absurd hd (by simp [evalSmt, hc])
          | BS _ => exact absurd hd (by simp [evalSmt, hc])
          | bad => exact absurd hd (by simp [evalSmt, hc])
          | P _ _ => exact absurd hd (by simp [evalSmt, hc])
          | L _ => exact absurd hd (by simp [evalSmt, hc])
        · subst ho
          cases hc : evalSmt σ cond with
          | B bb => cases bb with
            | true =>
              exfalso; have hf := ite_true_def hc hd; rw [evalSmt_falseE] at hf
              exact absurd hf Bfalse_ne_Btrue
            | false =>
              rw [γ_sIte_false σ (a := va) (b := vb) hc Bfalse_ne_Btrue] at hscrut
              have ih := symCase_adequate σ hb (ite_false_def hc hd) hscrut
              exact ih
          | I _ => exact absurd hd (by simp [evalSmt, hc])
          | D _ => exact absurd hd (by simp [evalSmt, hc])
          | BS _ => exact absurd hd (by simp [evalSmt, hc])
          | bad => exact absurd hd (by simp [evalSmt, hc])
          | P _ _ => exact absurd hd (by simp [evalSmt, hc])
          | L _ => exact absurd hd (by simp [evalSmt, hc])
    | _ + 1, _, .sCon _, _, _, _, h, _, _ => by simp [symCase] at h
    | _ + 1, _, .sConst _, _, _, _, h, _, _ => by simp [symCase] at h
    | _ + 1, _, .sLam _ _, _, _, _, h, _, _ => by simp [symCase] at h
    | _ + 1, _, .sDelay _ _, _, _, _, h, _, _ => by simp [symCase] at h
    | _ + 1, _, .sBuiltin _ _ _, _, _, _, h, _, _ => by simp [symCase] at h
  termination_by f _ v _ _ _ => (f, sizeOf v)
end

/-! ## Composition to a CEK statement (§6.3) -/

/-- `extract o = some e` exposes `o.value` as a first-order `sCon ev` with success formula
    `e = defined ∧ ev`. -/
theorem extract_eq {o : SymOut} {e : SmtExpr} (h : extract o = some e) :
    ∃ ev, o.value = .sCon ev ∧ e = SmtExpr.andE o.defined ev := by
  obtain ⟨val, d⟩ := o
  cases val with
  | sCon ev => simp only [extract, Option.some.injEq] at h; exact ⟨ev, rfl, h.symm⟩
  | sConst _ => simp [extract] at h
  | sLam _ _ => simp [extract] at h
  | sDelay _ _ => simp [extract] at h
  | sConstr _ _ => simp [extract] at h
  | sBuiltin _ _ _ => simp [extract] at h
  | sIte _ _ _ => simp [extract] at h

/-- **The success bridge.**  If the compiler committed to `o` with success formula `e`, and
    `e` holds at `σ`, then `bigEval` on the `σ`-concretized inputs returns `true`.  (Composing
    with `bigEval_sound`/`bigEval_iff_halt` then yields the CEK halting at `true`.) -/
theorem symEval_extract_true {σ : Model} {F : Nat} {ρ : SymEnv} {t : Term} {o : SymOut}
    {e : SmtExpr} (hc : symEval F ρ t = some o) (hx : extract o = some e)
    (ht : evalSmt σ e = .B true) :
    bigEval F (γE σ ρ) t = some (.VCon (.Bool true)) := by
  obtain ⟨ev, hval, he⟩ := extract_eq hx
  subst he
  obtain ⟨hdef, hev⟩ := and_true_split σ ht
  rw [symEval_adequate σ hc hdef, hval]
  simp only [γ_sCon, hev, svalToConst]

end Moist.Compile
