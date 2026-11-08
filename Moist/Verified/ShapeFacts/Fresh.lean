import Moist.Verified.ShapeFacts.Facts

variable [sv : Moist.CEK.SemVariant]

/-! # Binders fresh for a lowering environment

`freshIn env e` holds when no binder of `e` is already bound in `env` and no
binder of `e` shadows an enclosing binder of `e`. Lowering such an expression
in a distinct environment keeps every environment met along the way distinct.
-/

namespace Moist.Verified.ShapeFacts

open Moist.MIR

mutual
  def freshIn (avoid : List VarId) : Expr → Bool
    | .Var _ | .Lit _ | .Builtin _ | .Error => true
    | .Lam x body | .Fix x body => (envLookupT avoid x).isNone && freshIn (x :: avoid) body
    | .App f a => freshIn avoid f && freshIn avoid a
    | .Force e | .Delay e => freshIn avoid e
    | .Constr _ es => freshInList avoid es
    | .Case s alts => freshIn avoid s && freshInList avoid alts
    | .Let bs body => freshInLet avoid bs body
  termination_by e => sizeOf e

  def freshInList (avoid : List VarId) : List Expr → Bool
    | [] => true
    | e :: es => freshIn avoid e && freshInList avoid es
  termination_by es => sizeOf es

  def freshInLet (avoid : List VarId) : List (VarId × Expr × Bool) → Expr → Bool
    | [], body => freshIn avoid body
    | (x, rhs, _) :: rest, body =>
      freshIn avoid rhs && (envLookupT avoid x).isNone && freshInLet (x :: avoid) rest body
  termination_by bs body => sizeOf bs + sizeOf body
end

omit sv in
theorem freshInList_iff {avoid : List VarId} :
    ∀ {es : List Expr}, freshInList avoid es = true ↔ ∀ e ∈ es, freshIn avoid e = true
  | [] => by simp [freshInList]
  | e :: es => by
    simp only [freshInList, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    rw [freshInList_iff]

omit sv in
theorem EnvDistinct.cons {env : List VarId} {x : VarId} (hd : EnvDistinct env)
    (hx : (envLookupT env x).isNone = true) : EnvDistinct (x :: env) :=
  ⟨by simpa using hx, hd⟩

/-! ## Changing the avoided names -/

/-- Names the binders of `e` are known to avoid. -/
def Avoids (avoid avoid' : List VarId) (bound : Nat) : Prop :=
  ∀ y, (envLookupT avoid' y).isSome = true → (envLookupT avoid y).isSome = true ∨ bound < y.uid

omit sv in
theorem Avoids.cons {avoid avoid' : List VarId} {bound : Nat} (h : Avoids avoid avoid' bound)
    (x : VarId) : Avoids (x :: avoid) (x :: avoid') bound := by
  intro y hy
  rw [envLookupT_cons] at hy ⊢
  split
  · simp
  · rename_i hxy
    simp only [hxy, Bool.false_eq_true, if_false, Option.isSome_map] at hy ⊢
    exact h y hy

omit sv in
theorem Avoids.mono {avoid avoid' : List VarId} {b b' : Nat} (h : Avoids avoid avoid' b)
    (hb : b' ≤ b) : Avoids avoid avoid' b' := by
  intro y hy
  rcases h y hy with h | h
  · exact .inl h
  · exact .inr (by omega)

omit sv in
private theorem lookup_none_of_avoids {avoid avoid' : List VarId} {bound : Nat} {x : VarId}
    (h : Avoids avoid avoid' bound) (hx : (envLookupT avoid x).isNone = true)
    (hbound : x.uid ≤ bound) : (envLookupT avoid' x).isNone = true := by
  cases hl : envLookupT avoid' x with
  | none => rfl
  | some _ =>
    rcases h x (by simp [hl]) with h | h
    · simp [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none] at h hx; exact absurd hx h
    · omega

mutual
  theorem freshIn_avoids : ∀ (e : Expr) {avoid avoid' : List VarId},
      freshIn avoid e = true → Avoids avoid avoid' (maxUidExpr e) → freshIn avoid' e = true
    | .Var _, _, _, _, _ | .Lit _, _, _, _, _ | .Builtin _, _, _, _, _ | .Error, _, _, _, _ => by
      simp [freshIn]
    | .Lam x body, avoid, avoid', h, ha => by
      simp only [freshIn, Bool.and_eq_true] at h ⊢
      refine ⟨lookup_none_of_avoids ha h.1 (by simp only [maxUidExpr]; omega), ?_⟩
      exact freshIn_avoids body h.2 ((ha.mono (by simp only [maxUidExpr]; omega)).cons x)
    | .Fix x body, avoid, avoid', h, ha => by
      simp only [freshIn, Bool.and_eq_true] at h ⊢
      refine ⟨lookup_none_of_avoids ha h.1 (by simp only [maxUidExpr]; omega), ?_⟩
      exact freshIn_avoids body h.2 ((ha.mono (by simp only [maxUidExpr]; omega)).cons x)
    | .App f a, avoid, avoid', h, ha => by
      simp only [freshIn, Bool.and_eq_true] at h ⊢
      exact ⟨freshIn_avoids f h.1 (ha.mono (by simp only [maxUidExpr]; omega)),
        freshIn_avoids a h.2 (ha.mono (by simp only [maxUidExpr]; omega))⟩
    | .Force e, avoid, avoid', h, ha => by
      simp only [freshIn] at h ⊢
      exact freshIn_avoids e h (ha.mono (by simp only [maxUidExpr]; omega))
    | .Delay e, avoid, avoid', h, ha => by
      simp only [freshIn] at h ⊢
      exact freshIn_avoids e h (ha.mono (by simp only [maxUidExpr]; omega))
    | .Constr _ es, avoid, avoid', h, ha => by
      simp only [freshIn] at h ⊢
      exact freshInList_avoids es h (ha.mono (by simp only [maxUidExpr]; omega))
    | .Case s alts, avoid, avoid', h, ha => by
      simp only [freshIn, Bool.and_eq_true] at h ⊢
      exact ⟨freshIn_avoids s h.1 (ha.mono (by simp only [maxUidExpr]; omega)),
        freshInList_avoids alts h.2 (ha.mono (by simp only [maxUidExpr]; omega))⟩
    | .Let bs body, avoid, avoid', h, ha => by
      simp only [freshIn] at h ⊢
      exact freshInLet_avoids bs body h (ha.mono (by simp only [maxUidExpr]; omega))
  termination_by e => sizeOf e

  theorem freshInList_avoids : ∀ (es : List Expr) {avoid avoid' : List VarId},
      freshInList avoid es = true → Avoids avoid avoid' (maxUidExprList es) →
      freshInList avoid' es = true
    | [], _, _, _, _ => by simp [freshInList]
    | e :: es, avoid, avoid', h, ha => by
      simp only [freshInList, Bool.and_eq_true] at h ⊢
      exact ⟨freshIn_avoids e h.1 (ha.mono (by simp only [maxUidExprList]; omega)),
        freshInList_avoids es h.2 (ha.mono (by simp only [maxUidExprList]; omega))⟩
  termination_by es => sizeOf es

  theorem freshInLet_avoids : ∀ (bs : List (VarId × Expr × Bool)) (body : Expr)
      {avoid avoid' : List VarId},
      freshInLet avoid bs body = true → Avoids avoid avoid' (max (maxUidExprBinds bs) (maxUidExpr body)) →
      freshInLet avoid' bs body = true
    | [], body, avoid, avoid', h, ha => by
      simp only [freshInLet] at h ⊢
      exact freshIn_avoids body h (ha.mono (by simp only [maxUidExprBinds]; omega))
    | (x, rhs, er) :: rest, body, avoid, avoid', h, ha => by
      simp only [freshInLet, Bool.and_eq_true] at h ⊢
      refine ⟨⟨freshIn_avoids rhs h.1.1 (ha.mono (by simp only [maxUidExprBinds]; omega)),
        lookup_none_of_avoids ha h.1.2 (by simp only [maxUidExprBinds]; omega)⟩, ?_⟩
      exact freshInLet_avoids rest body h.2
        ((ha.mono (by simp only [maxUidExprBinds]; omega)).cons x)
  termination_by bs body => sizeOf bs + sizeOf body
end

end Moist.Verified.ShapeFacts
