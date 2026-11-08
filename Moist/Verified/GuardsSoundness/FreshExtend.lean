import Moist.Verified.GuardsSoundness.Units

variable [sv : Moist.CEK.SemVariant]

/-! # Freshness under more names -/

namespace Moist.Verified.Guards

open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.ShapeFacts

/-- Freshness only depends on which names are avoided. -/
theorem freshIn_mono {l₁ l₂ : List VarId} (h : ∀ y, (envLookupT l₂ y).isSome = true → (envLookupT l₁ y).isSome = true)
    {e : Expr} (he : freshIn l₁ e = true) : freshIn l₂ e = true :=
  freshIn_avoids e he fun y hy => .inl (h y hy)

omit sv in
theorem lookup_append_isSome {pre env : List VarId} {y : VarId} :
    (envLookupT (pre ++ env) y).isSome = ((envLookupT pre y).isSome || (envLookupT env y).isSome) := by
  rw [envLookupT_append]
  cases envLookupT pre y <;> simp

omit sv in
theorem lookup_isNone_of_contains {l : List VarId} {x : VarId} (h : l.contains x = false) :
    (envLookupT l x).isNone = true := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [List.contains_cons, Bool.or_eq_false_iff] at h
    rw [envLookupT_cons]
    have hyx : (y == x) = false := by
      cases hxy : (y == x)
      · rfl
      · have : (x == y) = true := by rw [VarId.beq_true_iff] at hxy ⊢; exact ⟨hxy.1.symm, hxy.2.symm⟩
        rw [this] at h; simp at h
    simp only [hyx, Bool.false_eq_true, if_false, Option.isNone_map]
    exact ih h.2

omit sv in
theorem flatten_contains_false {ls : List (List VarId)} {y : VarId} :
    ls.flatten.contains y = false ↔ ∀ l ∈ ls, l.contains y = false := by
  induction ls with
  | nil => simp
  | cons l ls ih => simp [List.flatten_cons, List.contains_append, ih]

theorem bindersOf_list_contains {fs : List Expr} {x : VarId} :
    ((fs.attach.map fun ⟨f, _⟩ => bindersOf f).flatten).contains x = false ↔
      ∀ f ∈ fs, (bindersOf f).contains x = false := by
  rw [flatten_contains_false]
  constructor
  · intro h f hf
    exact h _ (List.mem_map.mpr ⟨⟨f, hf⟩, List.mem_attach _ _, rfl⟩)
  · intro h l hl
    obtain ⟨⟨f, hf⟩, _, rfl⟩ := List.mem_map.mp hl
    exact h f hf

theorem cons_swap_lookup (x y : VarId) (avoid : List VarId) :
    ∀ z, (envLookupT (x :: y :: avoid) z).isSome = true → (envLookupT (y :: x :: avoid) z).isSome = true := by
  intro z h
  rw [show x :: y :: avoid = [x] ++ (y :: avoid) from rfl, lookup_append_isSome] at h
  rw [show y :: x :: avoid = [y] ++ (x :: avoid) from rfl, lookup_append_isSome,
    show x :: avoid = [x] ++ avoid from rfl, lookup_append_isSome]
  rw [show y :: avoid = [y] ++ avoid from rfl, lookup_append_isSome] at h
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with h | h | h
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inr h)

omit sv in
theorem binds_attach_map (bs : List (VarId × Expr × Bool)) :
    (bs.attach.map fun ⟨(y, r, _), _⟩ => y :: bindersOf r) = bs.map fun (y, r, _) => y :: bindersOf r := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨y, r, er⟩ := b
    simp only [List.attach_cons, List.map_cons, List.map_map, List.cons.injEq, true_and]
    rw [← ih]
    simp [Function.comp_def]

mutual
  theorem freshIn_cons_extra : ∀ (e : Expr) {avoid : List VarId} {x : VarId}, freshIn avoid e = true →
      (bindersOf e).contains x = false → freshIn (x :: avoid) e = true
    | .Var _, _, _, _, _ | .Lit _, _, _, _, _ | .Builtin _, _, _, _, _ | .Error, _, _, _, _ => by
      simp [freshIn]
    | .Lam y b, avoid, x, h, hx => by
      simp only [freshIn, Bool.and_eq_true] at h ⊢
      simp only [bindersOf, List.contains_cons, Bool.or_eq_false_iff] at hx
      refine ⟨?_, ?_⟩
      · rw [show x :: avoid = [x] ++ avoid from rfl]
        simp only [Option.isNone_iff_eq_none] at h ⊢
        rw [envLookupT_append]
        have : envLookupT [x] y = none := by
          rw [envLookupT_cons]
          have hxy : (x == y) = false := hx.1
          simp [hxy]; rfl
        rw [this, h.1]; rfl
      · exact freshIn_mono (cons_swap_lookup y x avoid) (freshIn_cons_extra b (avoid := y :: avoid) (x := x) h.2 hx.2)
    | .Fix y b, avoid, x, h, hx => by
      simp only [freshIn, Bool.and_eq_true] at h ⊢
      simp only [bindersOf, List.contains_cons, Bool.or_eq_false_iff] at hx
      refine ⟨?_, ?_⟩
      · rw [show x :: avoid = [x] ++ avoid from rfl]
        simp only [Option.isNone_iff_eq_none] at h ⊢
        rw [envLookupT_append]
        have : envLookupT [x] y = none := by
          rw [envLookupT_cons]
          have hxy : (x == y) = false := hx.1
          simp [hxy]; rfl
        rw [this, h.1]; rfl
      · exact freshIn_mono (cons_swap_lookup y x avoid) (freshIn_cons_extra b (avoid := y :: avoid) (x := x) h.2 hx.2)
    | .App f a, avoid, x, h, hx => by
      simp only [freshIn, Bool.and_eq_true] at h ⊢
      simp only [bindersOf, List.contains_append, Bool.or_eq_false_iff] at hx
      exact ⟨freshIn_cons_extra f h.1 hx.1, freshIn_cons_extra a h.2 hx.2⟩
    | .Force b, avoid, x, h, hx => by
      simp only [freshIn] at h ⊢; simp only [bindersOf] at hx
      exact freshIn_cons_extra b h hx
    | .Delay b, avoid, x, h, hx => by
      simp only [freshIn] at h ⊢; simp only [bindersOf] at hx
      exact freshIn_cons_extra b h hx
    | .Constr _ fs, avoid, x, h, hx => by
      simp only [freshIn] at h ⊢; simp only [bindersOf] at hx
      exact freshInList_cons_extra fs h (bindersOf_list_contains.mp hx)
    | .Case s alts, avoid, x, h, hx => by
      simp only [freshIn, Bool.and_eq_true] at h ⊢
      simp only [bindersOf, List.contains_append, Bool.or_eq_false_iff] at hx
      exact ⟨freshIn_cons_extra s h.1 hx.1, freshInList_cons_extra alts h.2 (bindersOf_list_contains.mp hx.2)⟩
    | .Let bs body, avoid, x, h, hx => by
      simp only [freshIn] at h ⊢
      exact freshInLet_cons_extra bs body h (by simpa [bindersOf, binds_attach_map] using hx)
  termination_by e => sizeOf e

  theorem freshInList_cons_extra : ∀ (es : List Expr) {avoid : List VarId} {x : VarId},
      freshInList avoid es = true → (∀ e ∈ es, (bindersOf e).contains x = false) →
      freshInList (x :: avoid) es = true
    | [], _, _, _, _ => by simp [freshInList]
    | e :: es, avoid, x, h, hx => by
      simp only [freshInList, Bool.and_eq_true] at h ⊢
      exact ⟨freshIn_cons_extra e h.1 (hx e (.head _)),
        freshInList_cons_extra es h.2 fun e' he' => hx e' (.tail _ he')⟩
  termination_by es => sizeOf es

  theorem freshInLet_cons_extra : ∀ (bs : List (VarId × Expr × Bool)) (body : Expr) {avoid : List VarId}
      {x : VarId}, freshInLet avoid bs body = true →
      ((bs.map fun (y, r, _) => y :: bindersOf r).flatten ++ bindersOf body).contains x = false →
      freshInLet (x :: avoid) bs body = true
    | [], body, avoid, x, h, hx => by
      simp only [freshInLet] at h ⊢
      exact freshIn_cons_extra body h (by simpa using hx)
    | (y, r, er) :: rest, body, avoid, x, h, hx => by
      simp only [freshInLet, Bool.and_eq_true] at h ⊢
      simp only [List.map_cons, List.flatten_cons, List.contains_append,
        List.contains_cons, Bool.or_eq_false_iff] at hx
      obtain ⟨⟨⟨hyx, hrx⟩, hrestx⟩, hbx⟩ := hx
      refine ⟨⟨freshIn_cons_extra r h.1.1 hrx, ?_⟩, ?_⟩
      · rw [show x :: avoid = [x] ++ avoid from rfl]
        simp only [Option.isNone_iff_eq_none] at h ⊢
        rw [envLookupT_append]
        have : envLookupT [x] y = none := by
          rw [envLookupT_cons]
          have hxy : (x == y) = false := hyx
          simp [hxy]; rfl
        rw [this, h.1.2]; rfl
      · have := freshInLet_cons_extra rest body (avoid := y :: avoid) (x := x) h.2
          (by rw [List.contains_append, hrestx, hbx]; rfl)
        have h' : freshIn (x :: y :: avoid) (.Let rest body) = true := by simpa [freshIn] using this
        simpa [freshIn] using freshIn_mono (cons_swap_lookup y x avoid) h'
  termination_by bs body => sizeOf bs + sizeOf body
end

end Moist.Verified.Guards

namespace Moist.Verified.Guards

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts

theorem freshIn_extend : ∀ (extra : List VarId) {avoid : List VarId} {e : Expr}, freshIn avoid e = true →
    (∀ x ∈ extra, (bindersOf e).contains x = false) → freshIn (extra ++ avoid) e = true
  | [], _, _, h, _ => h
  | x :: extra, avoid, e, h, hx =>
    freshIn_cons_extra e (freshIn_extend extra h fun y hy => hx y (.tail _ hy)) (hx x (.head _))

end Moist.Verified.Guards
