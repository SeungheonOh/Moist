import Moist.MIR.Optimize.Advanced.PairLists
import Moist.Verified.KnownListsSoundness.Walk
import Moist.Verified.ShapesSoundness.DataComparisons

variable [sv : Moist.CEK.SemVariant]

/-! # Lists of data pairs

The lists of data pairs form a family of list values closed under tails
(`pairFamily`): `pairListKnown` accepts expressions returning them
(`pairKnowledge`), and the head of such a list is a pair of data
(`pairFamily_head`). The positions computed for recursive parameters satisfy
the call checks of `KnownLists` (`pairListPositions_spec`,
`letFixPairPositions_spec`).
-/

namespace Moist.Verified.KnownLists

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.ShapeFacts

theorem pairDataList_cons {ps : List (Moist.Plutus.Data × Moist.Plutus.Data)} {ty : BuiltinType} {c : Const}
    {cs : List Const} (h : Const.pairDataList ps = .ConstList ty (c :: cs)) :
    ∃ p ps', ps = p :: ps' ∧ ty = pairDataType ∧ c = Const.pairData p ∧ cs = ps'.map Const.pairData := by
  cases ps with
  | nil => simp [Const.pairDataList] at h
  | cons p ps' =>
    simp only [Const.pairDataList, List.map_cons, Const.ConstList.injEq, List.cons.injEq] at h
    exact ⟨p, ps', rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- Lists of data pairs. -/
def pairFamily : ListFamily where
  mem := PairDataListValue
  list := by
    intro v h
    obtain ⟨ps, rfl⟩ := h
    trivial
  tail := by
    intro ty c cs h
    obtain ⟨ps, hps⟩ := h
    have hc : Const.pairDataList ps = .ConstList ty (c :: cs) := by injection hps with h1; exact h1.symm
    obtain ⟨p, ps', rfl, rfl, rfl, rfl⟩ := pairDataList_cons hc
    exact ⟨ps', rfl⟩

/-- The head of a list of data pairs is a pair of data. -/
theorem pairFamily_head {ty : BuiltinType} {c : Const} {cs : List Const}
    (h : pairFamily.mem (.VCon (.ConstList ty (c :: cs)))) :
    ∃ a b, c = .Pair (.Data a, .Data b) := by
  obtain ⟨ps, hps⟩ := h
  have hc : Const.pairDataList ps = .ConstList ty (c :: cs) := by injection hps with h1; exact h1.symm
  obtain ⟨p, ps', rfl, rfl, rfl, rfl⟩ := pairDataList_cons hc
  exact ⟨p.1, p.2, rfl⟩

theorem pairListKnown_sound {Γ : List (VarId × Expr)} {L : List VarId} {e : Expr} {env : List VarId}
    {ρ : CekEnv} {t : Term} {v : CekValue} (h : pairListKnown Γ L e = true)
    (hF : KnownFacts pairFamily Γ L env ρ) (hd : EnvDistinct env) (hlow : lowerTotalExpr env e = some t)
    (hv : Halts ρ t v) : pairFamily.mem v := by
  unfold pairListKnown at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · rename_i x
      obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
      obtain ⟨w, hw, hlw⟩ := hF.2 x h i hi
      have := halts_var hv
      rw [hw] at this; cases this
      exact hlw
    · cases h
  · exact knownPairDataList_sound (fun _ _ _ _ h => h) 64 Γ e h hF.1 hd hlow hv

omit sv in
theorem pairListKnown_bound {Γ : List (VarId × Expr)} {L env : List VarId} {y : VarId}
    (h : pairListKnown Γ L (.Var y) = true) (hk : KeysBound Γ env) (hn : NamesBound L env) :
    (envLookupT env y).isSome = true := by
  unfold pairListKnown at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact hn y h
  · rw [knownPairDataList] at h
    cases hf : Γ.find? (fun entry => entry.1 == y) with
    | none => rw [hf] at h; cases h
    | some entry =>
      have hmem := List.mem_of_find?_eq_some hf
      have hbeq : (entry.1 == y) = true := by simpa using List.find?_some hf
      rw [← envLookupT_congr hbeq]; exact hk entry hmem

/-- `pairListKnown` accepts expressions returning lists of data pairs. -/
def pairKnowledge : ListKnowledge pairFamily where
  known := pairListKnown
  sound := fun h hF hd hlow hv => pairListKnown_sound h hF hd hlow hv
  bound := fun h hk hn => pairListKnown_bound h hk hn

/-! ## Positions of recursive parameters -/

omit sv in
theorem pairListPositions_spec {env : List (VarId × Expr)} {lists : List VarId} {f : VarId}
    {params : List VarId} {args : List Expr} {body : Expr}
    (hne : pairListPositions env lists f params args body ≠ []) :
    params.length ≤ args.length ∧
      (∀ p ∈ pairListPositions env lists f params args body,
        ∃ a, args[p]? = some a ∧ pairListKnown env lists a = true) ∧
      listCallsOK f params.length (pairListPositions env lists f params args body)
        (listedParameters params (pairListPositions env lists f params args body) ++ lists) body = true := by
  unfold pairListPositions at hne ⊢
  split
  · rename_i h; simp [h] at hne
  · rename_i h
    simp only [h, if_false] at hne
    refine ⟨by omega, ?_⟩
    rcases stable_spec lists f params body _ _ with h' | ⟨hsub, hcheck⟩
    · exact absurd h' hne
    · refine ⟨fun p hp => ?_, hcheck⟩
      have := (List.mem_filter.mp (hsub p hp)).2
      revert this
      cases ha : args[p]? with
      | none => simp
      | some a => intro hk; exact ⟨a, rfl, by simpa using hk⟩

omit sv in
theorem letPairStable_spec (env : List (VarId × Expr)) (lists : List VarId) (g f : VarId)
    (params : List VarId) (inner scope : Expr) :
    ∀ (fuel : Nat) (ps : List Nat),
      letFixPairPositions.stable env lists g f params inner scope fuel ps = [] ∨
        (listCallsOK f params.length (letFixPairPositions.stable env lists g f params inner scope fuel ps)
            (listedParameters params (letFixPairPositions.stable env lists g f params inner scope fuel ps)
              ++ lists) inner = true ∧
          listCallsOK g params.length (letFixPairPositions.stable env lists g f params inner scope fuel ps)
            (environmentPairLists env lists ++ lists) scope = true)
  | 0, ps => .inl (by simp [letFixPairPositions.stable])
  | fuel + 1, ps => by
    simp only [letFixPairPositions.stable]
    split
    · exact .inl rfl
    · split
      · split
        · rename_i h
          simp only [Bool.and_eq_true] at h
          exact .inr h
        · exact .inl rfl
      · exact letPairStable_spec env lists g f params inner scope fuel _

omit sv in
theorem letFixPairPositions_spec {env : List (VarId × Expr)} {lists : List VarId} {g f : VarId}
    {params : List VarId} {inner scope : Expr}
    (hne : letFixPairPositions env lists g f params inner scope ≠ []) :
    listCallsOK f params.length (letFixPairPositions env lists g f params inner scope)
        (listedParameters params (letFixPairPositions env lists g f params inner scope) ++ lists)
        inner = true ∧
      listCallsOK g params.length (letFixPairPositions env lists g f params inner scope)
        (environmentPairLists env lists ++ lists) scope = true := by
  unfold letFixPairPositions at hne ⊢
  rcases letPairStable_spec env lists g f params inner scope _ _ with h | h
  · exact absurd h hne
  · exact h

omit sv in
theorem pairListKnown_congr {Γ : List (VarId × Expr)} {L : List VarId} {x y : VarId}
    (hxy : (x == y) = true) : pairListKnown Γ L (.Var x) = pairListKnown Γ L (.Var y) := by
  have hc : L.contains x = L.contains y := by
    simp only [List.contains_eq_any_beq]
    congr 1; funext z; exact beq_congr_left hxy z
  have hf : Γ.find? (fun entry => entry.1 == x) = Γ.find? (fun entry => entry.1 == y) := by
    congr 1; funext entry; exact beq_congr_right hxy entry.1
  show (L.contains x || knownPairDataList 64 Γ (.Var x)) = (L.contains y || knownPairDataList 64 Γ (.Var y))
  rw [knownPairDataList, knownPairDataList, hc, hf]

omit sv in
theorem environmentPairLists_known {Γ : List (VarId × Expr)} {L : List VarId} {y : VarId}
    (h : (environmentPairLists Γ L ++ L).contains y = true) : pairListKnown Γ L (.Var y) = true := by
  obtain ⟨y', hy', hyy'⟩ := List.contains_iff_exists_mem_beq.mp h
  rw [pairListKnown_congr hyy']
  rcases List.mem_append.mp hy' with hy' | hy'
  · simp only [environmentPairLists, List.mem_filterMap] at hy'
    obtain ⟨entry, _, he⟩ := hy'
    split at he
    · cases he; assumption
    · cases he
  · show (L.contains y' || knownPairDataList 64 Γ (.Var y')) = true
    rw [List.contains_iff_exists_mem_beq.mpr ⟨y', hy', varId_beq_self y'⟩]; rfl

end Moist.Verified.KnownLists
