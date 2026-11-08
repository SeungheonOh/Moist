import Moist.Verified.GuardsSoundness.Binders

/-! # Scrutinee shapes and the fields they carry -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.KnownLists

def KindV : Kind → CekValue → Prop
  | .bool, v => BoolValue v
  | .int, v => IntegerValue v
  | .list, v => ListValue v
  | .pair, v => PairValue v
  | .constrs ks, v => ModeV (.constrs ks) v
  | .unknown, _ => True

theorem pf_produces : ∀ env ρ rhs v, PF env ρ rhs v → Produces env ρ rhs v := fun _ _ _ _ h => h.1

theorem Inv.produces {c : TCtx} {env : List VarId} {ρ : CekEnv} (h : Inv c env ρ) :
    FactsHold Produces c.facts env ρ := h.facts.mono pf_produces

theorem scrutineeKind_sound {c : TCtx} {env : List VarId} {ρ : CekEnv} {s : Expr} {ts : Term}
    {w : CekValue} (hρ : Inv c env ρ) (hd : EnvDistinct env) (hs : lowerTotalExpr env s = some ts)
    (hw : Halts ρ ts w) : KindV (scrutineeKind c.facts c.lists s) w := by
  unfold scrutineeKind
  split
  · exact knownBooleanLocal_sound pf_produces _ _ _ (by assumption) hρ.facts hd hs hw
  split
  · exact knownInteger_sound pf_produces _ _ _ (by assumption) hρ.facts hd hs hw
  split
  · exact knownListValue_sound _ _ _ _ (by assumption) hρ.produces hρ.lists hd hs hw
  split
  · exact constructorPair_sound pf_produces _ _ _ (by assumption) hρ.facts hd hs hw
  · trivial

theorem dispatch_vcon {talts : List Term} {c : Const} {alt : Term} {fs : List CekValue}
    {tag n : Nat} {gs : List CekValue} (hc : constToTagAndFields c = some (tag, n, gs))
    (h : dispatch talts (.VCon c) = some (alt, fs)) : talts[tag]? = some alt ∧ gs = fs := by
  simp only [dispatch, hc] at h
  split at h
  · cases h
  · cases ht : talts[tag]? with
    | none => rw [ht] at h; cases h
    | some a => rw [ht] at h; cases h; exact ⟨rfl, rfl⟩

/-- The second field of a list cell or of a decoded constructor is a list. -/
def KindFields : Kind → Nat → List CekValue → Prop
  | .list, 0, gs => ∃ a b, gs = [a, b] ∧ ListValue b
  | .pair, 0, gs => ∃ a b, gs = [a, b] ∧ ListValue b
  | _, _, _ => True

theorem nullList_arg {u r : CekValue} (h : evalBuiltin .NullList [u] = some r) : ListValue u := by
  obtain ⟨c, r', rfl, hc, _⟩ := evalBuiltin_single (by decide) h
  cases c <;> (try cases hc) <;> trivial

/-- A selected alternative carries the number of fields its tag announces. -/
theorem dispatch_kind {k : Kind} {w : CekValue} (hk : KindV k w) {talts : List Term} {alt : Term}
    {fs : List CekValue} (hlen : ∀ ks, k = .constrs ks → ks.length = talts.length)
    (h : dispatch talts w = some (alt, fs)) :
    ∃ i, talts[i]? = some alt ∧ (k = .unknown ∨ k.fields i = some fs.length) ∧ KindFields k i fs := by
  have known : ∀ c tag n gs, w = .VCon c → constToTagAndFields c = some (tag, n, gs) →
      k.fields tag = some gs.length → KindFields k tag gs →
      ∃ i, talts[i]? = some alt ∧ (k = .unknown ∨ k.fields i = some fs.length) ∧ KindFields k i fs := by
    intro c tag n gs hw hc hf hkf
    subst hw
    obtain ⟨ht, rfl⟩ := dispatch_vcon hc h
    exact ⟨tag, ht, .inr hf, hkf⟩
  cases k with
  | unknown =>
    cases w with
    | VConstr tag gs =>
      simp only [dispatch] at h
      cases ht : talts[tag]? with
      | none => rw [ht] at h; cases h
      | some a => rw [ht] at h; cases h; exact ⟨tag, ht, .inl rfl, trivial⟩
    | VCon c =>
      cases hc : constToTagAndFields c with
      | none => simp [dispatch, hc] at h
      | some r =>
        obtain ⟨tag, n, gs⟩ := r
        exact ⟨tag, (dispatch_vcon hc h).1, .inl rfl, trivial⟩
    | _ => simp [dispatch] at h
  | bool =>
    obtain ⟨b, rfl⟩ := hk
    cases b
    · exact known _ 0 2 [] rfl rfl rfl trivial
    · exact known _ 1 2 [] rfl rfl rfl trivial
  | int =>
    obtain ⟨n, rfl⟩ := hk
    by_cases hn : n ≥ 0
    · exact known _ n.toNat 0 [] rfl (by simp [constToTagAndFields, hn]) rfl (by cases n.toNat <;> trivial)
    · simp [dispatch, constToTagAndFields, hn] at h
  | list =>
    cases w with
    | VCon c =>
      cases c <;> simp only [KindV, ListValue] at hk
      · rename_i l; cases l
        · exact known _ 1 2 [] rfl rfl rfl trivial
        · exact known _ 0 2 _ rfl rfl rfl ⟨_, _, rfl, trivial⟩
      · rename_i l; cases l
        · exact known _ 1 2 [] rfl rfl rfl trivial
        · exact known _ 0 2 _ rfl rfl rfl ⟨_, _, rfl, trivial⟩
      · rename_i l; cases l
        · exact known _ 1 2 [] rfl rfl rfl trivial
        · exact known _ 0 2 _ rfl rfl rfl ⟨_, _, rfl, trivial⟩
    | _ => simp [KindV, ListValue] at hk
  | pair =>
    obtain ⟨i, gs, rfl⟩ := hk
    exact known _ 0 1 _ rfl rfl rfl ⟨_, _, rfl, trivial⟩
  | constrs ks =>
    obtain ⟨tag, gs, rfl, hgs⟩ := hk
    simp only [dispatch] at h
    cases ht : talts[tag]? with
    | none => rw [ht] at h; cases h
    | some a =>
      rw [ht] at h; cases h
      refine ⟨tag, ht, .inr ?_, trivial⟩
      have hlt : tag < ks.length := by
        rw [hlen ks rfl]; exact (List.getElem?_eq_some_iff.mp ht).1
      simp only [Kind.fields]
      rw [List.getElem?_eq_getElem hlt, hgs _ (List.getElem?_eq_getElem hlt)]

end Moist.Verified.Guards
