import Moist.Verified.GuardsSoundness.SinkSpec

/-! # Exchanging two steps found by `unitView` -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.FloatOut (LookupShift lowerTotalExpr_lookupShift)

/-! ## Freshness of a plugged step -/

/-- Binders introduced one after the other, each new. -/
def lamsFresh : List VarId → List VarId → Bool
  | _, [] => true
  | avoid, x :: xs => (envLookupT avoid x).isNone && lamsFresh (x :: avoid) xs

theorem freshIn_lams : ∀ (bs avoid : List VarId) (X : Expr),
    freshIn avoid (Advanced.lams bs X) = (lamsFresh avoid bs && freshIn (bs.reverse ++ avoid) X)
  | [], avoid, X => by simp [Advanced.lams, lamsFresh]
  | b :: bs, avoid, X => by
    rw [lams_cons]
    simp only [freshIn, lamsFresh, freshIn_lams bs (b :: avoid) X, List.reverse_cons, List.append_assoc,
      List.singleton_append, Bool.and_assoc]

theorem freshInList_append (avoid : List VarId) :
    ∀ (xs ys : List Expr), freshInList avoid (xs ++ ys) = (freshInList avoid xs && freshInList avoid ys)
  | [], ys => by simp [freshInList]
  | x :: xs, ys => by
    simp only [List.cons_append, freshInList, freshInList_append avoid xs ys, Bool.and_assoc]

def _root_.Moist.MIR.Advanced.GUnit.parts : GUnit → List Expr
  | .bind _ r _ => [r]
  | .cases s before after _ => s :: (before ++ after)
  | .ite c => [c]

theorem freshIn_plug (u : GUnit) (avoid : List VarId) (X : Expr) :
    freshIn avoid (u.plug X) =
      (freshInList avoid u.parts && lamsFresh avoid u.binders && freshIn (u.binders.reverse ++ avoid) X) := by
  cases u with
  | bind x r er =>
    simp only [GUnit.plug, GUnit.parts, GUnit.binders, freshIn_let_single, freshInList, lamsFresh,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, Bool.and_true]
  | cases s before after bs =>
    simp only [GUnit.plug, GUnit.parts, GUnit.binders, freshIn, freshInList, freshInList_append,
      freshIn_lams, Bool.and_true]
    cases freshIn avoid s <;> cases freshInList avoid before <;> cases lamsFresh avoid bs <;>
      cases freshIn (bs.reverse ++ avoid) X <;> cases freshInList avoid after <;> rfl
  | ite c =>
    simp only [GUnit.plug, GUnit.parts, GUnit.binders, freshIn_ite, freshIn, freshInList, lamsFresh,
      List.reverse_nil, List.nil_append, Bool.and_true]

theorem freshInList_mono {l₁ l₂ : List VarId}
    (h : ∀ y, (envLookupT l₂ y).isSome = true → (envLookupT l₁ y).isSome = true) :
    ∀ {es : List Expr}, freshInList l₁ es = true → freshInList l₂ es = true
  | [], _ => by simp [freshInList]
  | e :: es, he => by
    simp only [freshInList, Bool.and_eq_true] at he ⊢
    exact ⟨freshIn_mono h he.1, freshInList_mono h he.2⟩

theorem lookup_cons_mono {l₁ l₂ : List VarId} (x : VarId)
    (h : ∀ y, (envLookupT l₂ y).isSome = true → (envLookupT l₁ y).isSome = true) :
    ∀ y, (envLookupT (x :: l₂) y).isSome = true → (envLookupT (x :: l₁) y).isSome = true := by
  intro y hy
  rw [show x :: l₂ = [x] ++ l₂ from rfl, lookup_append_isSome] at hy
  rw [show x :: l₁ = [x] ++ l₁ from rfl, lookup_append_isSome]
  simp only [Bool.or_eq_true] at hy ⊢
  rcases hy with hy | hy
  · exact .inl hy
  · exact .inr (h y hy)

theorem lamsFresh_mono : ∀ {bs l₁ l₂ : List VarId},
    (∀ y, (envLookupT l₂ y).isSome = true → (envLookupT l₁ y).isSome = true) →
    lamsFresh l₁ bs = true → lamsFresh l₂ bs = true
  | [], _, _, _, _ => rfl
  | x :: xs, l₁, l₂, h, hf => by
    simp only [lamsFresh, Bool.and_eq_true] at hf ⊢
    refine ⟨?_, lamsFresh_mono (lookup_cons_mono x h) hf.2⟩
    cases h2 : envLookupT l₂ x with
    | none => rfl
    | some i =>
      have := h x (by simp [h2])
      rw [Option.isNone_iff_eq_none] at hf
      rw [hf.1] at this; cases this

theorem lookup_isNone_tail {x y : VarId} {l : List VarId}
    (h : (envLookupT (x :: l) y).isNone = true) : (envLookupT l y).isNone = true := by
  rw [show x :: l = [x] ++ l from rfl] at h
  have h' := lookup_append_isSome (pre := [x]) (env := l) (y := y)
  cases h1 : envLookupT ([x] ++ l) y with
  | some _ => rw [h1] at h; cases h
  | none =>
    rw [h1] at h'
    cases h2 : envLookupT l y with
    | none => rfl
    | some _ => rw [h2] at h'; simp at h'

theorem lamsFresh_not_mem : ∀ {bs avoid : List VarId}, lamsFresh avoid bs = true →
    ∀ y ∈ bs, (envLookupT avoid y).isNone = true
  | [], _, _, _, hy => by cases hy
  | x :: xs, avoid, hf, y, hy => by
    simp only [lamsFresh, Bool.and_eq_true] at hf
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hf.1
    · exact lookup_isNone_tail (lamsFresh_not_mem hf.2 y hy)

theorem beq_symm_var {a b : VarId} (h : (a == b) = true) : (b == a) = true := by
  rw [VarId.beq_true_iff] at h ⊢; exact ⟨h.1.symm, h.2.symm⟩

theorem lookup_none_beq : ∀ {l : List VarId} {y : VarId}, (envLookupT l y).isNone = true →
    ∀ x ∈ l, (x == y) = false
  | [], _, _, _, hx => by cases hx
  | z :: l, y, h, x, hx => by
    rw [envLookupT_cons] at h
    by_cases hzy : (z == y) = true
    · simp [hzy] at h
    · simp only [hzy, Bool.false_eq_true, if_false, Option.isNone_map] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa using hzy
      · exact lookup_none_beq h x hx

theorem lookup_none_of_beq : ∀ {l : List VarId} {y : VarId}, (∀ x ∈ l, (x == y) = false) →
    (envLookupT l y).isNone = true
  | [], _, _ => rfl
  | z :: l, y, h => by
    rw [envLookupT_cons]
    simp only [h z (.head _), Bool.false_eq_true, if_false, Option.isNone_map]
    exact lookup_none_of_beq fun x hx => h x (.tail _ hx)

theorem lamsFresh_extend : ∀ {bs avoid extra : List VarId}, lamsFresh avoid bs = true →
    (∀ y ∈ bs, (envLookupT extra y).isNone = true) → lamsFresh (extra ++ avoid) bs = true
  | [], _, _, _, _ => rfl
  | x :: xs, avoid, extra, hf, hx => by
    simp only [lamsFresh, Bool.and_eq_true] at hf ⊢
    refine ⟨?_, ?_⟩
    · have h' := lookup_append_isSome (pre := extra) (env := avoid) (y := x)
      have h1 := hx x (.head _)
      have h2 := hf.1
      rw [Option.isNone_iff_eq_none] at h1 h2 ⊢
      rw [h1, h2] at h'
      cases h3 : envLookupT (extra ++ avoid) x with
      | none => rfl
      | some _ => rw [h3] at h'; simp at h'
    · have ih := lamsFresh_extend (extra := extra) hf.2 fun y hy => hx y (.tail _ hy)
      refine lamsFresh_mono (fun y hy => ?_) ih
      rw [show x :: (extra ++ avoid) = [x] ++ (extra ++ avoid) from rfl, lookup_append_isSome,
        lookup_append_isSome] at hy
      rw [lookup_append_isSome, show x :: avoid = [x] ++ avoid from rfl, lookup_append_isSome]
      simp only [Bool.or_eq_true] at hy ⊢
      rcases hy with hy | hy | hy
      · exact .inr (.inl hy)
      · exact .inl hy
      · exact .inr (.inr hy)

theorem freshInList_extend : ∀ (extra : List VarId) {avoid : List VarId} {es : List Expr},
    freshInList avoid es = true → (∀ e ∈ es, ∀ x ∈ extra, (bindersOf e).contains x = false) →
    freshInList (extra ++ avoid) es = true
  | _, _, [], _, _ => by simp [freshInList]
  | extra, avoid, e :: es, h, hx => by
    simp only [freshInList, Bool.and_eq_true] at h ⊢
    exact ⟨freshIn_extend extra h.1 (hx e (.head _)), freshInList_extend extra h.2 fun e' he' => hx e' (.tail _ he')⟩

/-! ## The semantics of a valid step -/

structure UnitSem (Γ : List (VarId × Expr)) (u : GUnit) where
  S : SemUnit
  arity : S.arity = u.binders.length
  lower : ∀ env X, lowerTotalExpr env (u.plug X) =
    (lowerTotalExpr env u.expr).bind fun tE => (lowerTotalExpr (u.binders.reverse ++ env) X).map (S.plug tE)
  ok : ∀ env ρ tE w, EnvWellFormed env.length ρ → env.length ≤ ρ.length → FactsHold PF Γ env ρ →
    EnvDistinct env → lowerTotalExpr env u.expr = some tE → Halts ρ tE w → S.ok w

theorem fields_some_of_lt {k : Kind} (hk : k = .bool ∨ k = .int ∨ k = .list ∨ k = .pair) {n m j : Nat}
    (hn : k.fields n = some m) (hj : j < n) : ∃ m', k.fields j = some m' := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨0, rfl⟩
  · cases j <;> exact ⟨_, rfl⟩
  · cases n with
    | zero => omega
    | succ n => simp [Kind.fields] at hn

theorem unit_sem {Γ : List (VarId × Expr)} : ∀ (u : GUnit), u.valid Γ = true → Nonempty (UnitSem Γ u)
  | .bind x r er, _ => ⟨{
      S := bindUnit
      arity := rfl
      lower := fun env X => by
        simp only [GUnit.plug, GUnit.expr, GUnit.binders, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append]
        rw [lowerTotalExpr_let_single]
        cases lowerTotalExpr env r <;> cases lowerTotalExpr (x :: env) X <;> rfl
      ok := fun _ _ _ _ _ _ _ _ _ _ => trivial }⟩
  | .ite c, _ => ⟨{
      S := iteUnit
      arity := rfl
      lower := fun env X => by
        simp only [GUnit.plug, GUnit.expr, GUnit.binders, iteE, MIR.lowerTotalExpr_force,
          MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_delay, lowerTotalExpr_builtin, lowerTotalExpr_error,
          List.reverse_nil, List.nil_append]
        cases lowerTotalExpr env c <;> cases lowerTotalExpr env X <;> rfl
      ok := fun _ _ _ _ _ _ _ _ _ _ => trivial }⟩
  | .cases s before after bs, hv => by
    simp only [GUnit.valid] at hv
    generalize hkd : scrutineeKind Γ [] s = kind at hv
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hv
    obtain ⟨⟨⟨hk, hcont⟩, hb⟩, ha⟩ := hv
    have hk' : kind = .bool ∨ kind = .int ∨ kind = .list ∨ kind = .pair := by
      rcases hk with ((h | h) | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))
    obtain ⟨tsB, htsB, hlB, hspecB⟩ := errorAlts_lower (kind := kind) 0 before hb
    obtain ⟨tsA, htsA, _, hspecA⟩ := errorAlts_lower (kind := kind) (before.length + 1) after ha
    let S : CaseShape := {
      kind := kind
      before := tsB
      after := tsA
      arity := bs.length
      hkind := hk'
      hcont := by rw [hlB]; exact hcont
      hbefore := fun j a hj => by
        obtain ⟨m, rfl, hm⟩ := hspecB j a hj
        have hjl : j < before.length := by
          rw [← hlB]; exact (List.getElem?_eq_some_iff.mp hj).1
        obtain ⟨m', hm'⟩ := fields_some_of_lt hk' hcont hjl
        exact ⟨m, by rw [hm', hm m' (by simpa using hm')], rfl⟩
      hafter := fun j a hj => by
        obtain ⟨m, rfl, hm⟩ := hspecA j a hj
        exact ⟨m, rfl, fun m' hm' => hm m' (by rw [hlB] at hm'; rwa [← Nat.add_assoc])⟩ }
    refine ⟨{ S := caseUnit S, arity := rfl, lower := fun env X => ?_, ok := ?_ }⟩
    · simp only [GUnit.plug, GUnit.expr, GUnit.binders]
      rw [MIR.lowerTotalExpr_case_of_list, lowerList_append, lowerList_append, htsB, htsA,
        MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil, lower_lams_iff]
      cases lowerTotalExpr env s <;> cases lowerTotalExpr (bs.reverse ++ env) X <;> rfl
    · intro env ρ tE w henv hlen hF hd hl hw
      show KindV kind w
      rw [← hkd]
      exact kind_of_facts henv hlen hF hd hl hw

/-! ## What `canSwap` checks -/

theorem contains_flatMap_false {f : Expr → List VarId} {x : VarId} :
    ∀ {es : List Expr}, (es.flatMap f).contains x = false → ∀ p ∈ es, (f p).contains x = false
  | [], _, _, hp => by cases hp
  | e :: es, h, p, hp => by
    rw [List.flatMap_cons, List.contains_append, Bool.or_eq_false_iff] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact contains_flatMap_false h.2 p hp

theorem innerBinders_parts {a : GUnit} {x : VarId} (h : a.innerBinders.contains x = false) :
    ∀ p ∈ a.parts, (bindersOf p).contains x = false := by
  intro p hp
  cases a with
  | bind y r er =>
    simp only [GUnit.parts, List.mem_singleton] at hp; subst hp; exact h
  | ite c =>
    simp only [GUnit.parts, List.mem_singleton] at hp; subst hp; exact h
  | cases s before after bs =>
    simp only [GUnit.innerBinders, List.contains_append, Bool.or_eq_false_iff] at h
    simp only [GUnit.parts] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact contains_flatMap_false h.2 p hp

theorem disjoint_spec {xs : List VarId} {vars : VarSet} (h : disjoint xs vars = true) :
    ∀ x ∈ xs, vars.contains x = false := by
  intro x hx
  unfold disjoint at h
  rw [List.all_eq_true] at h
  simpa using h x hx

theorem canSwap_spec {Γ : List (VarId × Expr)} {a b : GUnit} (h : canSwap Γ a b = true) :
    a.valid Γ = true ∧ b.valid Γ = true ∧
      (∀ x ∈ a.binders, (freeVars b.expr).contains x = false) ∧
      (∀ x ∈ b.binders, (freeVars a.expr).contains x = false) ∧
      (∀ p ∈ a.parts, ∀ x ∈ b.binders, (bindersOf p).contains x = false) ∧
      terminatesWith Γ b.expr = true := by
  unfold canSwap at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hva, hvb⟩, hd1⟩, hd2⟩, hin⟩, _⟩, _⟩, hterm⟩ := h
  refine ⟨hva, hvb, disjoint_spec hd1, disjoint_spec hd2, fun p hp x hx => ?_, hterm⟩
  rw [List.all_eq_true] at hin
  have := hin x hx
  simp only [Bool.not_eq_true'] at this
  exact innerBinders_parts this p hp

/-! ## Exchanging two steps -/

theorem freshInList_mem {avoid : List VarId} :
    ∀ {es : List Expr}, freshInList avoid es = true → ∀ e ∈ es, freshIn avoid e = true
  | [], _, _, he => by cases he
  | e :: es, h, e', he' => by
    simp only [freshInList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp he' with rfl | he'
    · exact h.1
    · exact freshInList_mem h.2 e' he'

theorem _root_.Moist.MIR.Advanced.GUnit.expr_mem_parts (u : GUnit) : u.expr ∈ u.parts := by
  cases u <;> simp [GUnit.expr, GUnit.parts]

theorem lookup_suffix (pre : List VarId) {env : List VarId} :
    ∀ y, (envLookupT env y).isSome = true → (envLookupT (pre ++ env) y).isSome = true := by
  intro y hy
  rw [lookup_append_isSome, hy, Bool.or_true]

theorem lookup_swap_blocks (p q env : List VarId) :
    ∀ y, (envLookupT (p ++ (q ++ env)) y).isSome = true → (envLookupT (q ++ (p ++ env)) y).isSome = true := by
  intro y hy
  rw [lookup_append_isSome, lookup_append_isSome] at hy ⊢
  simp only [Bool.or_eq_true] at hy ⊢
  rcases hy with hy | hy | hy
  · exact .inr (.inl hy)
  · exact .inl hy
  · exact .inr (.inr hy)

theorem plug_fresh_parts {u : GUnit} {avoid : List VarId} {X : Expr} (h : freshIn avoid (u.plug X) = true) :
    freshInList avoid u.parts = true ∧ lamsFresh avoid u.binders = true ∧
      freshIn (u.binders.reverse ++ avoid) X = true := by
  rw [freshIn_plug] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem plug_fresh_of_parts {u : GUnit} {avoid : List VarId} {X : Expr} (h1 : freshInList avoid u.parts = true)
    (h2 : lamsFresh avoid u.binders = true) (h3 : freshIn (u.binders.reverse ++ avoid) X = true) :
    freshIn avoid (u.plug X) = true := by
  rw [freshIn_plug, h1, h2, h3]; rfl

theorem swap_disjoint {a b : GUnit} {env : List VarId}
    (hlB : lamsFresh (a.binders.reverse ++ env) b.binders = true) :
    ∀ x ∈ a.binders, ∀ y ∈ b.binders, (x == y) = false := by
  intro x hx y hy
  exact lookup_none_beq (lamsFresh_not_mem hlB y hy) x (List.mem_append_left _ (List.mem_reverse.mpr hx))

theorem swap_fresh {Γ : List (VarId × Expr)} {a b : GUnit} {T : Expr} (hc : canSwap Γ a b = true)
    {env : List VarId} (h : freshIn env (a.plug (b.plug T)) = true) :
    freshIn env (b.plug (a.plug T)) = true := by
  obtain ⟨_, _, _, _, hin, _⟩ := canSwap_spec hc
  obtain ⟨hpA, hlA, hB⟩ := plug_fresh_parts h
  obtain ⟨hpB, hlB, hT⟩ := plug_fresh_parts hB
  have hdis := swap_disjoint hlB
  refine plug_fresh_of_parts (freshInList_mono (lookup_suffix _) hpB) (lamsFresh_mono (lookup_suffix _) hlB) ?_
  refine plug_fresh_of_parts ?_ ?_ (freshIn_mono (lookup_swap_blocks _ _ env) hT)
  · exact freshInList_extend _ hpA fun p hp x hx => hin p hp x (List.mem_reverse.mp hx)
  · exact lamsFresh_extend hlA fun y hy => lookup_none_of_beq fun x hx =>
      beq_false_symm (hdis y hy x (List.mem_reverse.mp hx))

theorem swap_rel {Γ : List (VarId × Expr)} {a b : GUnit} {T : Expr} (hc : canSwap Γ a b = true) :
    FactRel AnyName PF Γ (a.plug (b.plug T)) (b.plug (a.plug T)) := by
  obtain ⟨hva, hvb, hdA, hdB, _, hterm⟩ := canSwap_spec hc
  obtain ⟨UA⟩ := unit_sem a hva
  obtain ⟨UB⟩ := unit_sem b hvb
  intro env t _ hd hfresh _ _ hlow
  obtain ⟨hpA, _, hB⟩ := plug_fresh_parts hfresh
  obtain ⟨hpB, hlB, _⟩ := plug_fresh_parts hB
  have hdis := swap_disjoint hlB
  have hfrB : freshIn env b.expr = true :=
    freshIn_mono (lookup_suffix _) (freshInList_mem hpB _ b.expr_mem_parts)
  rw [UA.lower] at hlow
  cases hEA : lowerTotalExpr env a.expr with
  | none => rw [hEA] at hlow; cases hlow
  | some tA =>
  rw [hEA, Option.bind_some, UB.lower, lower_prepend_all a.binders env b.expr hdA] at hlow
  cases hEB : lowerTotalExpr env b.expr with
  | none => rw [hEB] at hlow; cases hlow
  | some tB =>
  rw [hEB] at hlow
  cases hET : lowerTotalExpr (b.binders.reverse ++ (a.binders.reverse ++ env)) T with
  | none => rw [hET] at hlow; cases hlow
  | some tT =>
  rw [hET] at hlow
  simp only [Option.map_some, Option.bind_some, Option.some.injEq] at hlow
  subst hlow
  have hTT : lowerTotalExpr (a.binders.reverse ++ (b.binders.reverse ++ env)) T =
      some (renameTerm (blockSwap a.binders.length b.binders.length) tT) := by
    have hs := lookupShift_blockSwap (bA := a.binders) (bB := b.binders) env hdis
    simp only [List.append_assoc] at hs
    rw [lowerTotalExpr_lookupShift T hs, hET]; rfl
  refine ⟨UB.S.plug tB (UA.S.plug (shiftN b.binders.length tA)
    (renameTerm (blockSwap a.binders.length b.binders.length) tT)), ?_, ?_⟩
  · rw [UB.lower, hEB, Option.bind_some, UA.lower, lower_prepend_all b.binders env a.expr hdB, hEA]
    simp only [Option.map_some, Option.bind_some, hTT]
  · have hcA := MIR.lowerTotalExpr_closedAt hEA
    have hcB := MIR.lowerTotalExpr_closedAt hEB
    have hcT := MIR.lowerTotalExpr_closedAt hET
    simp only [List.length_append, List.length_reverse] at hcT
    have := unit_swap UA.S UB.S (d := env.length) (F := FactsHold PF Γ env) (tA := tA) (tB := tB) (T := tT)
      hcA hcB (by rw [UA.arity, UB.arity]; rwa [show env.length + a.binders.length + b.binders.length =
        b.binders.length + (a.binders.length + env.length) by omega])
      (fun ρ hF henv hlen w hw => UA.ok env ρ tA w henv hlen hF hd hEA hw)
      (fun ρ hF henv hlen w hw => UB.ok env ρ tB w henv hlen hF hd hEB hw)
      (fun ρ hF henv hlen => terminatesWith_sound hterm hd hfrB hEB henv hlen hF)
    rw [UA.arity, UB.arity] at this
    exact this

/-! ## Congruence below a step -/

theorem lams_rel {Γ : List (VarId × Expr)} : ∀ (bs : List VarId) {X X' : Expr},
    FactRel AnyName PF Γ X X' → FactRel AnyName PF Γ (Advanced.lams bs X) (Advanced.lams bs X')
  | [], _, _, h => h
  | _ :: bs, _, _, h => (lams_rel bs h).lam trivial

theorem listRel_mid {R : Expr → Expr → Prop} (hR : ∀ e, R e e) {y y' : Expr} (hy : R y y') :
    ∀ (xs zs : List Expr), ListRel R (xs ++ [y] ++ zs) (xs ++ [y'] ++ zs)
  | [], zs => ⟨hy, listRel_refl hR zs⟩
  | x :: xs, zs => ⟨hR x, listRel_mid hR hy xs zs⟩

theorem valid_two_binders {Γ : List (VarId × Expr)} {s : Expr} {before after : List Expr} {h t : VarId}
    (hv : (GUnit.cases s before after [h, t]).valid Γ = true) : before = [] := by
  simp only [GUnit.valid] at hv
  generalize scrutineeKind Γ [] s = kind at hv
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hv
  obtain ⟨⟨⟨hk, hcont⟩, _⟩, _⟩ := hv
  cases before with
  | nil => rfl
  | cons a rest =>
    exfalso
    simp only [List.length_cons] at hcont
    rcases hk with ((rfl | rfl) | rfl) | rfl <;> simp [Kind.fields] at hcont

theorem plug_rel {Γ : List (VarId × Expr)} {b : GUnit} (hv : b.valid Γ = true) {X X' : Expr}
    (h : FactRel AnyName PF (b.facts Γ) X X') : FactRel AnyName PF Γ (b.plug X) (b.plug X') := by
  cases b with
  | bind x r er =>
    exact FactRel.let_single r trivial (.inl rfl) (FactRel.refl _ _ _ _) h
      (fun env ρ v hG hd hf hp => pf_push env ρ r v hG hd hf hp)
  | ite c =>
    exact FactRel.force (.app (.app (.app (FactRel.refl _ _ _ _) (FactRel.refl _ _ _ _)) h.delay)
      (FactRel.refl _ _ _ _))
  | cases s before after bs =>
    have generic : FactRel AnyName PF Γ X X' →
        FactRel AnyName PF Γ ((GUnit.cases s before after bs).plug X) ((GUnit.cases s before after bs).plug X') :=
      fun h => FactRel.case (FactRel.refl _ _ _ _)
        (listRel_mid (fun e => FactRel.refl _ _ _ e) (lams_rel bs h) before after)
    rcases bs with _ | ⟨h1, _ | ⟨t1, _ | ⟨u, rest⟩⟩⟩
    · exact generic h
    · exact generic h
    · have hb := valid_two_binders hv
      subst hb
      exact FactRel.caseBind (rest := after) trivial trivial h (listRel_refl (fun e => FactRel.refl _ _ _ e) _)
    · exact generic h

/-! ## The views `unitView` takes -/

theorem unitView_spec {Γ : List (VarId × Expr)} {e : Expr} {u : GUnit} {body : Expr}
    (h : unitView Γ e = some (u, body)) :
    (∀ env, lowerTotalExpr env e = lowerTotalExpr env (u.plug body)) ∧
      (∀ avoid, freshIn avoid e = freshIn avoid (u.plug body)) := by
  unfold unitView at h
  split at h
  · cases h; exact ⟨fun _ => rfl, fun _ => rfl⟩
  · cases h
    exact ⟨fun env => lowerTotalExpr_let_cons env _ _ _, fun avoid => freshIn_let_cons avoid _ _ _⟩
  · rename_i s alts
    revert h
    cases hfi : alts.findIdx? (fun a => !isErrorAlt a) with
    | none => simp
    | some k =>
      cases halt : alts[k]? with
      | none => simp [halt]
      | some alt =>
        simp only [halt]
        split
        · cases hc : continuing (scrutineeKind Γ [] s) (alts.take k) alt with
          | none => simp
          | some p =>
            obtain ⟨bs, body0⟩ := p
            simp only [Option.some.injEq, Prod.mk.injEq]
            rintro ⟨rfl, rfl⟩
            have hst := (continuing_spec hc).1
            have heq : alts = alts.take k ++ [Advanced.lams bs body0] ++ alts.drop (k + 1) := by
              obtain ⟨hk, hak⟩ := List.getElem?_eq_some_iff.mp halt
              rw [← hst, List.append_assoc, List.singleton_append, ← hak, ← List.drop_eq_getElem_cons hk,
                List.take_append_drop]
            have : Expr.Case s alts = (GUnit.cases s (alts.take k) (alts.drop (k + 1)) bs).plug body0 := by
              simp only [GUnit.plug]; rw [← heq]
            rw [this]
            exact ⟨fun _ => rfl, fun _ => rfl⟩
        · simp
  · cases h; exact ⟨fun _ => rfl, fun _ => rfl⟩
  · cases h

theorem plug_congr {Γ : List (VarId × Expr)} {u : GUnit} (hv : u.valid Γ = true) {X Y : Expr}
    (hl : ∀ env, lowerTotalExpr env X = lowerTotalExpr env Y) (hf : ∀ avoid, freshIn avoid X = freshIn avoid Y) :
    (∀ env, lowerTotalExpr env (u.plug X) = lowerTotalExpr env (u.plug Y)) ∧
      (∀ avoid, freshIn avoid (u.plug X) = freshIn avoid (u.plug Y)) := by
  obtain ⟨U⟩ := unit_sem u hv
  exact ⟨fun env => by rw [U.lower, U.lower, hl], fun avoid => by rw [freshIn_plug, freshIn_plug, hf]⟩

/-! ## Sinking a step -/

theorem sinkPast_rel : ∀ (n : Nat) (Γ : List (VarId × Expr)) (a : GUnit) (body r : Expr),
    sinkPast n Γ a body = some r → FactRel AnyName PF Γ (a.plug body) r
  | 0, _, _, _, _, h => by simp [sinkPast] at h
  | n + 1, Γ, a, body, r, h => by
    simp only [sinkPast] at h
    cases hv : unitView Γ body with
    | none => rw [hv] at h; cases h
    | some p =>
      obtain ⟨b, inner⟩ := p
      rw [hv] at h
      simp only at h
      by_cases hc : canSwap Γ a b = true
      · rw [if_pos hc] at h
        have hva := (canSwap_spec hc).1
        have hvb := (canSwap_spec hc).2.1
        obtain ⟨hl, hf⟩ := unitView_spec hv
        obtain ⟨hl', hf'⟩ := plug_congr hva hl hf
        have hswap := swap_rel (T := inner) hc
        cases hs : sinkPast n (b.facts Γ) a inner with
        | some inner' =>
          rw [hs] at h; cases h
          have ih := sinkPast_rel n (b.facts Γ) a inner inner' hs
          exact (FactRel.trans' hswap (plug_rel hvb ih) fun env hfe => swap_fresh hc hfe).congr_left hl' hf'
        | none =>
          rw [hs] at h
          simp only at h
          by_cases hg : b.guard = true
          · rw [if_pos hg] at h; cases h; exact hswap.congr_left hl' hf'
          · rw [if_neg hg] at h; cases h
      · rw [if_neg hc] at h; cases h

theorem sinkPast_fresh : ∀ (n : Nat) (Γ : List (VarId × Expr)) (a : GUnit) (body r : Expr),
    sinkPast n Γ a body = some r → ∀ env, freshIn env (a.plug body) = true → freshIn env r = true
  | 0, _, _, _, _, h => by simp [sinkPast] at h
  | n + 1, Γ, a, body, r, h => by
    simp only [sinkPast] at h
    cases hv : unitView Γ body with
    | none => rw [hv] at h; cases h
    | some p =>
      obtain ⟨b, inner⟩ := p
      rw [hv] at h
      simp only at h
      by_cases hc : canSwap Γ a b = true
      · rw [if_pos hc] at h
        have hva := (canSwap_spec hc).1
        obtain ⟨hl, hf⟩ := unitView_spec hv
        obtain ⟨_, hf'⟩ := plug_congr hva hl hf
        intro env he
        rw [hf'] at he
        have hsw := swap_fresh hc he
        cases hs : sinkPast n (b.facts Γ) a inner with
        | some inner' =>
          rw [hs] at h; cases h
          obtain ⟨h1, h2, h3⟩ := plug_fresh_parts hsw
          exact plug_fresh_of_parts h1 h2 (sinkPast_fresh n (b.facts Γ) a inner inner' hs _ h3)
        | none =>
          rw [hs] at h
          simp only at h
          by_cases hg : b.guard = true
          · rw [if_pos hg] at h; cases h; exact hsw
          · rw [if_neg hg] at h; cases h
      · rw [if_neg hc] at h; cases h

theorem trySink_rel (Γ : List (VarId × Expr)) (e : Expr) : FactRel AnyName PF Γ e (trySink Γ e) := by
  unfold trySink
  split
  · rename_i a body hv
    split
    · cases hs : sinkPast sinkFuel Γ a body with
      | none => exact FactRel.refl _ _ _ _
      | some r =>
        obtain ⟨hl, hf⟩ := unitView_spec hv
        exact (sinkPast_rel _ _ _ _ _ hs).congr_left hl hf
    · exact FactRel.refl _ _ _ _
  · exact FactRel.refl _ _ _ _

theorem trySink_fresh {Γ : List (VarId × Expr)} {e : Expr} {env : List VarId} (he : freshIn env e = true) :
    freshIn env (trySink Γ e) = true := by
  unfold trySink
  split
  · rename_i a body hv
    split
    · cases hs : sinkPast sinkFuel Γ a body with
      | none => exact he
      | some r =>
        obtain ⟨_, hf⟩ := unitView_spec hv
        exact sinkPast_fresh _ _ _ _ _ hs env (by rw [← hf]; exact he)
    · exact he
  · exact he

/-! ## The walk -/

theorem sinkWalk_fresh_aux : ∀ N : Nat, ∀ (e : Expr) (Γ : List (VarId × Expr)) (avoid : List VarId),
    exprSize e < N → freshIn avoid e = true → freshIn avoid (sinkWalk Γ e) = true := by
  intro N
  induction N with
  | zero => intro _ _ _ h; omega
  | succ N ihw =>
  intro e Γ avoid hs hf
  unfold sinkWalk
  split
  · rename_i body
    simp only [exprSize, exprSizeBinds] at hs
    rw [freshIn_let_nil] at hf
    exact ihw body Γ avoid (by omega) hf
  · rename_i x r er rest body
    simp only [exprSize, exprSizeBinds] at hs
    refine trySink_fresh ?_
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
    refine trySink_fresh ?_
    simp only [freshIn, freshInList, Bool.and_eq_true] at hf ⊢
    obtain ⟨hfs, ⟨hh, ht, hfb⟩, hfr⟩ := hf
    refine ⟨ihw s Γ _ (by omega) hfs, ⟨hh, ht, ihw b _ _ (by omega) hfb⟩, ?_⟩
    refine freshInList_attach_map fun a ha => ihw a Γ _ ?_ (freshInList_iff.mp hfr a ha)
    have := exprSize_lt_of_mem ha; omega
  · rename_i s alts _
    simp only [exprSize] at hs
    refine trySink_fresh ?_
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    refine ⟨ihw s Γ _ (by omega) hf.1, freshInList_attach_map fun a ha => ihw a Γ _ ?_
      (freshInList_iff.mp hf.2 a ha)⟩
    have := exprSize_lt_of_mem ha; omega
  · rename_i inner
    simp only [exprSize] at hs
    refine trySink_fresh ?_
    simp only [freshIn] at hf ⊢
    exact ihw inner Γ _ (by omega) hf
  all_goals exact hf

theorem sinkWalk_fresh {Γ : List (VarId × Expr)} {e : Expr} {avoid : List VarId} (h : freshIn avoid e = true) :
    freshIn avoid (sinkWalk Γ e) = true :=
  sinkWalk_fresh_aux _ e Γ avoid (Nat.lt_succ_self _) h

theorem sinkWalk_rel_aux : ∀ N : Nat, ∀ (e : Expr) (Γ : List (VarId × Expr)), exprSize e < N →
    FactRel AnyName PF Γ e (sinkWalk Γ e) := by
  intro N
  induction N with
  | zero => intro _ _ h; omega
  | succ N ihw =>
  intro e Γ hs
  unfold sinkWalk
  split
  · rename_i body
    simp only [exprSize, exprSizeBinds] at hs
    exact (ihw body Γ (by omega)).congr_left (fun env => lowerTotalExpr_let_nil env body)
      (fun avoid => freshIn_let_nil avoid body)
  · rename_i x r er rest body
    simp only [exprSize, exprSizeBinds] at hs
    have hlet := (FactRel.let_single (er := er) r trivial (.inl rfl) (ihw r Γ (by omega))
      (ihw (.Let rest body) ((x, r) :: Γ) (by have := exprSize_pos r; simp only [exprSize]; omega))
      (fun env ρ v hG hd hf hp => pf_push env ρ r v hG hd hf hp)).congr_left (fun env => lowerTotalExpr_let_cons env _ _ _)
      (fun avoid => freshIn_let_cons avoid _ _ _)
    refine FactRel.trans' (hlet.congr_right fun env => lowerTotalExpr_consLet' env _ _) (trySink_rel _ _)
      fun env hf => ?_
    rw [freshIn_consLet', freshIn_let_single]
    rw [freshIn_let_cons, freshIn_let_single] at hf
    simp only [Bool.and_eq_true] at hf ⊢
    exact ⟨⟨sinkWalk_fresh hf.1.1, hf.1.2⟩, sinkWalk_fresh hf.2⟩
  · rename_i x b
    simp only [exprSize] at hs
    exact (ihw b Γ (by omega)).lam trivial
  · rename_i f b
    simp only [exprSize] at hs
    cases b with
    | Lam x inner =>
      unfold sinkWalk
      simp only [exprSize] at hs
      exact (ihw inner Γ (by omega)).fix_lam trivial trivial (fun _ _ => trivial)
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
      cases hlow
  · rename_i f a
    simp only [exprSize] at hs
    exact (ihw f Γ (by omega)).app (ihw a Γ (by omega))
  · rename_i b
    simp only [exprSize] at hs
    exact (ihw b Γ (by omega)).delay
  · rename_i tag fields
    simp only [exprSize] at hs
    rw [productList_attach_map]
    exact FactRel.constr (listRel_of_forall fun a ha => ihw a Γ (by have := exprSize_lt_of_mem ha; omega))
  · rename_i s h t b rest
    simp only [exprSize, exprSizeList] at hs
    rw [productList_attach_map]
    have step₁ : FactRel AnyName PF Γ (.Case s (.Lam h (.Lam t b) :: rest))
        (.Case (sinkWalk Γ s) (.Lam h (.Lam t b) :: rest)) :=
      FactRel.case (ihw s Γ (by omega)) (listRel_refl (fun e => FactRel.refl _ _ _ e) _)
    have step₂ := FactRel.caseBind (s := sinkWalk Γ s) (h := h) (t := t) (rest := rest) trivial trivial
      (ihw b (altFacts Γ (sinkWalk Γ s) h t) (by omega))
      (listRel_of_forall fun a ha => ihw a Γ (by have := exprSize_lt_of_mem ha; omega))
    have fr₁ : ∀ env, freshIn env (.Case s (.Lam h (.Lam t b) :: rest)) = true →
        freshIn env (.Case (sinkWalk Γ s) (.Lam h (.Lam t b) :: rest)) = true := by
      intro env hf
      simp only [freshIn, Bool.and_eq_true] at hf ⊢
      exact ⟨sinkWalk_fresh hf.1, hf.2⟩
    refine FactRel.trans' (FactRel.trans' step₁ step₂ fr₁) (trySink_rel _ _) fun env hf => ?_
    have hf₁ := fr₁ env hf
    simp only [freshIn, freshInList, Bool.and_eq_true] at hf₁ ⊢
    obtain ⟨hfs, ⟨hh, ht, hfb⟩, hfr⟩ := hf₁
    refine ⟨hfs, ⟨hh, ht, sinkWalk_fresh hfb⟩, ?_⟩
    rw [freshInList_iff] at hfr ⊢
    intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    exact sinkWalk_fresh (hfr a' ha')
  · rename_i s alts _
    simp only [exprSize] at hs
    rw [productList_attach_map]
    refine FactRel.trans' (FactRel.case (ihw s Γ (by omega))
      (listRel_of_forall fun a ha => ihw a Γ (by have := exprSize_lt_of_mem ha; omega))) (trySink_rel _ _)
      fun env hf => ?_
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    refine ⟨sinkWalk_fresh hf.1, ?_⟩
    rw [freshInList_iff] at hf ⊢
    intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    exact sinkWalk_fresh (hf.2 a' ha')
  · rename_i inner
    simp only [exprSize] at hs
    refine FactRel.trans' (ihw inner Γ (by omega)).force (trySink_rel _ _) fun env hf => ?_
    simp only [freshIn] at hf ⊢
    exact sinkWalk_fresh hf
  all_goals exact FactRel.refl _ _ _ _

theorem sinkWalk_rel (Γ : List (VarId × Expr)) (e : Expr) : FactRel AnyName PF Γ e (sinkWalk Γ e) :=
  sinkWalk_rel_aux _ e Γ (Nat.lt_succ_self _)

end Moist.Verified.Guards
