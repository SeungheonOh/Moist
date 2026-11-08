import Moist.Verified.GuardsSoundness.BinderFacts
import Moist.Verified.FailFastSoundness

/-! # Pushing the consumer binds no new names -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.ShapeFacts

theorem freshIn_consLet' (avoid : List VarId) (binding : VarId × Expr × Bool) (e : Expr) :
    freshIn avoid (consLet binding e) = freshIn avoid (.Let [binding] e) := by
  unfold consLet
  split
  · exact freshIn_let_cons avoid _ _ _
  · rfl

theorem freshIn_assertE (avoid : List VarId) (u : Const × BuiltinType) (x : Expr) :
    freshIn avoid (assertE u x) = freshIn avoid x := by
  simp [assertE, iteE, freshIn]

theorem freshIn_assertLeaf (avoid : List VarId) (Γ : List (VarId × Expr)) (u : Const × BuiltinType)
    (x : Expr) : freshIn avoid (assertLeaf Γ u x) = freshIn avoid x := by
  unfold assertLeaf
  split
  · simp [freshIn, freshInList]
  · exact freshIn_assertE avoid u x

theorem freshIn_ite (avoid : List VarId) (c a b : Expr) :
    freshIn avoid (.Force (iteE c (.Delay a) (.Delay b))) =
      (freshIn avoid c && freshIn avoid a && freshIn avoid b) := by
  simp [freshIn, iteE]

theorem freshInList_attach_map {avoid : List VarId} {l : List Expr} {g : Expr → Expr}
    (h : ∀ a ∈ l, freshIn avoid (g a) = true) :
    freshInList avoid (l.attach.map fun ⟨a, _⟩ => g a) = true := by
  rw [freshInList_iff]
  intro e he
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at he
  obtain ⟨a, ha, rfl⟩ := he
  exact h a ha

theorem push_fresh : ∀ N : Nat,
    (∀ (e : Expr) (Γ : List (VarId × Expr)) (avoid : List VarId), exprSize e < N →
      freshIn avoid e = true → freshIn avoid (pushWalk Γ e) = true) ∧
    (∀ (x : Expr) (Γ : List (VarId × Expr)) (u : Const × BuiltinType) (avoid : List VarId),
      exprSize x < N → freshIn avoid x = true → freshIn avoid (pushAssert Γ u x) = true) := by
  intro N
  induction N with
  | zero => exact ⟨fun _ _ _ h => by omega, fun _ _ _ _ h => by omega⟩
  | succ N ih =>
  obtain ⟨ihw, iha⟩ := ih
  have walk : ∀ (e : Expr) (Γ : List (VarId × Expr)) (avoid : List VarId), exprSize e < N + 1 →
      freshIn avoid e = true → freshIn avoid (pushWalk Γ e) = true := by
    intro e Γ avoid hs hf
    unfold pushWalk
    split
    · rename_i body
      simp only [exprSize, exprSizeBinds] at hs
      rw [freshIn_let_nil] at hf
      exact ihw body Γ avoid (by omega) hf
    · rename_i x r er rest body
      simp only [exprSize, exprSizeBinds] at hs
      rw [freshIn_consLet', freshIn_let_single]
      rw [freshIn_let_cons, freshIn_let_single] at hf
      simp only [Bool.and_eq_true] at hf ⊢
      refine ⟨⟨ihw r Γ avoid (by omega) hf.1.1, hf.1.2⟩, ?_⟩
      exact ihw _ _ _ (by have := exprSize_pos r; simp only [exprSize]; omega) hf.2
    · rename_i x b
      simp only [exprSize] at hs
      simp only [freshIn, Bool.and_eq_true] at hf ⊢
      exact ⟨hf.1, ihw b Γ _ (by omega) hf.2⟩
    · rename_i f b
      simp only [exprSize] at hs
      simp only [freshIn, Bool.and_eq_true] at hf ⊢
      exact ⟨hf.1, ihw b Γ _ (by omega) hf.2⟩
    · rename_i f a
      simp only [exprSize] at hs
      simp only [freshIn, Bool.and_eq_true] at hf ⊢
      exact ⟨ihw f Γ _ (by omega) hf.1, ihw a Γ _ (by omega) hf.2⟩
    · rename_i b
      simp only [exprSize] at hs
      simp only [freshIn] at hf ⊢
      exact ihw b Γ _ (by omega) hf
    · rename_i tag fields
      simp only [exprSize] at hs
      simp only [freshIn] at hf ⊢
      refine freshInList_attach_map fun a ha => ihw a Γ _ ?_ (freshInList_iff.mp hf a ha)
      have := exprSize_lt_of_mem ha; omega
    · rename_i s h t b rest
      simp only [exprSize, exprSizeList] at hs
      simp only [freshIn, freshInList, Bool.and_eq_true] at hf ⊢
      obtain ⟨hfs, ⟨hh, ht, hfb⟩, hfr⟩ := hf
      refine ⟨ihw s Γ _ (by omega) hfs, ⟨hh, ht, ihw b _ _ (by omega) hfb⟩, ?_⟩
      refine freshInList_attach_map fun a ha => ihw a Γ _ ?_ (freshInList_iff.mp hfr a ha)
      have := exprSize_lt_of_mem ha; omega
    · rename_i s alts _
      simp only [exprSize] at hs
      simp only [freshIn, Bool.and_eq_true] at hf ⊢
      refine ⟨ihw s Γ _ (by omega) hf.1, freshInList_attach_map fun a ha => ihw a Γ _ ?_
        (freshInList_iff.mp hf.2 a ha)⟩
      have := exprSize_lt_of_mem ha; omega
    · rename_i x u
      simp only [exprSize] at hs
      simp only [freshIn, Bool.and_eq_true] at hf
      exact iha x Γ u _ (by omega) hf.1.1.2
    · rename_i inner _
      simp only [exprSize] at hs
      simp only [freshIn] at hf ⊢
      exact ihw inner Γ _ (by omega) hf
    all_goals exact hf
  refine ⟨walk, ?_⟩
  intro x Γ u avoid hs hf
  unfold pushAssert
  split
  · simp [freshIn]
  · simp [freshIn]
  · simp [freshIn]
  · rename_i body
    simp only [exprSize, exprSizeBinds] at hs
    rw [freshIn_let_nil] at hf
    exact iha body Γ u avoid (by omega) hf
  · rename_i y r er rest body
    simp only [exprSize, exprSizeBinds] at hs
    rw [freshIn_consLet', freshIn_let_single]
    rw [freshIn_let_cons, freshIn_let_single] at hf
    simp only [Bool.and_eq_true] at hf ⊢
    refine ⟨⟨ihw r Γ avoid (by omega) hf.1.1, hf.1.2⟩, ?_⟩
    exact iha _ _ u _ (by have := exprSize_pos r; simp only [exprSize]; omega) hf.2
  · rename_i s alts
    split
    · simp only [exprSize] at hs
      simp only [freshIn, Bool.and_eq_true] at hf ⊢
      refine ⟨ihw s Γ _ (by omega) hf.1, freshInList_attach_map fun a ha => iha a Γ u _ ?_
        (freshInList_iff.mp hf.2 a ha)⟩
      have := exprSize_lt_of_mem ha; omega
    · simp only [exprSize] at hs
      simp only [freshIn, Bool.and_eq_true] at hf ⊢
      refine ⟨ihw s Γ _ (by omega) hf.1, freshInList_attach_map fun a ha => iha a Γ u _ ?_
        (freshInList_iff.mp hf.2 a ha)⟩
      have := exprSize_lt_of_mem ha; omega
    · split
      · rename_i h t b a1 rest
        simp only [exprSize, exprSizeList] at hs
        simp only [freshIn, freshInList, Bool.and_eq_true] at hf ⊢
        obtain ⟨hfs, ⟨hh, ht, hfb⟩, hfa1, hfr⟩ := hf
        refine ⟨ihw s Γ _ (by omega) hfs, ⟨hh, ht, iha b _ u _ (by omega) hfb⟩,
          iha a1 Γ u _ (by omega) hfa1, ?_⟩
        refine freshInList_attach_map fun a ha => ihw a Γ _ ?_ (freshInList_iff.mp hfr a ha)
        have := exprSize_lt_of_mem ha; omega
      · rw [freshIn_assertLeaf]; exact walk _ Γ avoid hs hf
    · split
      · rename_i a b body
        simp only [exprSize, exprSizeList] at hs
        simp only [freshIn, freshInList, Bool.and_eq_true] at hf ⊢
        obtain ⟨hfs, ⟨ha, hb, hfb⟩, _⟩ := hf
        exact ⟨ihw s Γ _ (by omega) hfs, ⟨⟨ha, hb, iha body _ u _ (by omega) hfb⟩, trivial⟩⟩
      · rw [freshIn_assertLeaf]; exact walk _ Γ avoid hs hf
    · rw [freshIn_assertLeaf]; exact walk _ Γ avoid hs hf
  · rename_i c a b
    simp only [exprSize] at hs
    have hf' : freshIn avoid (.Force (iteE c (.Delay a) (.Delay b))) = true := hf
    rw [freshIn_ite] at hf' ⊢
    simp only [Bool.and_eq_true] at hf' ⊢
    exact ⟨⟨ihw c Γ _ (by omega) hf'.1.1, iha a Γ u _ (by omega) hf'.1.2⟩, iha b Γ u _ (by omega) hf'.2⟩
  · rw [freshIn_assertLeaf]; exact walk _ Γ avoid hs hf

theorem pushWalk_fresh {Γ : List (VarId × Expr)} {e : Expr} {avoid : List VarId}
    (h : freshIn avoid e = true) : freshIn avoid (pushWalk Γ e) = true :=
  (push_fresh (exprSize e + 1)).1 e Γ avoid (by omega) h

theorem pushAssert_fresh {Γ : List (VarId × Expr)} {u : Const × BuiltinType} {x : Expr}
    {avoid : List VarId} (h : freshIn avoid x = true) : freshIn avoid (pushAssert Γ u x) = true :=
  (push_fresh (exprSize x + 1)).2 x Γ u avoid (by omega) h

end Moist.Verified.Guards
