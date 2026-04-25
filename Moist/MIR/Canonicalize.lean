import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.LowerTotal

namespace Moist.MIR

/-! # Canonicalize

Rewrites every bound-variable binder to a globally unique uid
(`origin = .gen`), assigned by a counter threaded through the tree.
Free variables retain their original identity. The counter ensures
that sibling sub-expressions (e.g. both children of App) get distinct
binder uids, satisfying the Barendregt variable convention.
-/

private def canonBinder (uid : Nat) (hint : String) : VarId :=
  { uid := uid, origin := .gen, hint := hint }

private abbrev CanonEnv := List (VarId × Nat)

private def canonEnvLookup (env : CanonEnv) (x : VarId) : Option Nat :=
  match env with
  | [] => none
  | (v, uid) :: rest => if v == x then some uid else canonEnvLookup rest x

mutual
  def canonicalizeAux (env : CanonEnv) (c : Nat) : Expr → Expr × Nat
    | .Var x =>
      match canonEnvLookup env x with
      | some uid => (.Var (canonBinder uid x.hint), c)
      | none     => (.Var x, c)
    | .Lit l        => (.Lit l, c)
    | .Builtin b    => (.Builtin b, c)
    | .Error        => (.Error, c)
    | .Lam x body   =>
      let x' := canonBinder c x.hint
      let (body', c') := canonicalizeAux ((x, c) :: env) (c + 1) body
      (.Lam x' body', c')
    | .Fix f body   =>
      let f' := canonBinder c f.hint
      let (body', c') := canonicalizeAux ((f, c) :: env) (c + 1) body
      (.Fix f' body', c')
    | .App f x      =>
      let (f', c1) := canonicalizeAux env c f
      let (x', c2) := canonicalizeAux env c1 x
      (.App f' x', c2)
    | .Force e      =>
      let (e', c') := canonicalizeAux env c e
      (.Force e', c')
    | .Delay e      =>
      let (e', c') := canonicalizeAux env c e
      (.Delay e', c')
    | .Constr t as  =>
      let (as', c') := canonicalizeList env c as
      (.Constr t as', c')
    | .Case s alts  =>
      let (s', c1) := canonicalizeAux env c s
      let (alts', c2) := canonicalizeList env c1 alts
      (.Case s' alts', c2)
    | .Let binds body => canonicalizeLet env c binds body
  termination_by e => sizeOf e

  def canonicalizeList (env : CanonEnv) (c : Nat) : List Expr → List Expr × Nat
    | []       => ([], c)
    | e :: es  =>
      let (e', c1) := canonicalizeAux env c e
      let (es', c2) := canonicalizeList env c1 es
      (e' :: es', c2)
  termination_by es => sizeOf es

  def canonicalizeLet (env : CanonEnv) (c : Nat)
      : List (VarId × Expr × Bool) → Expr → Expr × Nat
    | [], body =>
      let (body', c') := canonicalizeAux env c body
      (.Let [] body', c')
    | (x, rhs, er) :: rest, body =>
      let (rhs', c1) := canonicalizeAux env c rhs
      let x' := canonBinder c1 x.hint
      let (inner, c2) := canonicalizeLet ((x, c1) :: env) (c1 + 1) rest body
      (.Let [(x', rhs', er)] inner, c2)
  termination_by bs body => sizeOf bs + sizeOf body
end

def canonicalize (e : Expr) : Expr := (canonicalizeAux [] (maxUidExpr e + 1) e).1

/-! ## BEq helpers -/

private theorem varid_beq_iff {a b : VarId} :
    (a == b) = true ↔ a.origin = b.origin ∧ a.uid = b.uid := by
  constructor
  · intro h
    have h' : (a.origin == b.origin && a.uid == b.uid) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨ho, hu⟩ := h'
    refine ⟨?_, beq_iff_eq.mp hu⟩
    generalize hka : a.origin = ka at ho
    generalize hkb : b.origin = kb at ho
    cases ka <;> cases kb
    · rfl
    · cases ho
    · cases ho
    · rfl
  · intro ⟨ho, hu⟩
    show (a.origin == b.origin && a.uid == b.uid) = true
    rw [Bool.and_eq_true]
    refine ⟨?_, beq_iff_eq.mpr hu⟩
    rw [ho]
    cases b.origin <;> rfl

private theorem canonBinder_beq_canonBinder (d1 d2 : Nat) (h1 h2 : String) :
    (canonBinder d1 h1 == canonBinder d2 h2) = true ↔ d1 = d2 := by
  rw [varid_beq_iff]; simp [canonBinder]

private theorem canonBinder_beq_varid (uid : Nat) (h : String) (y : VarId) :
    (canonBinder uid h == y) = true ↔ y.origin = .gen ∧ y.uid = uid := by
  rw [varid_beq_iff]; simp [canonBinder]
  constructor
  · intro ⟨ho, hu⟩; exact ⟨ho.symm, hu.symm⟩
  · intro ⟨ho, hu⟩; exact ⟨ho.symm, hu.symm⟩

/-! ## Counter monotonicity -/

mutual
private theorem canonicalizeAux_counter_le (env : CanonEnv) (c : Nat) (e : Expr) :
    c ≤ (canonicalizeAux env c e).2 := by
  cases e with
  | Var x =>
    unfold canonicalizeAux; cases canonEnvLookup env x <;> dsimp <;> omega
  | Lit _ | Builtin _ | Error => unfold canonicalizeAux; dsimp; omega
  | Lam x body =>
    unfold canonicalizeAux
    show c ≤ (canonicalizeAux ((x, c) :: env) (c + 1) body).2
    have := canonicalizeAux_counter_le ((x, c) :: env) (c + 1) body; omega
  | Fix f body =>
    unfold canonicalizeAux
    show c ≤ (canonicalizeAux ((f, c) :: env) (c + 1) body).2
    have := canonicalizeAux_counter_le ((f, c) :: env) (c + 1) body; omega
  | App f x =>
    unfold canonicalizeAux
    show c ≤ (canonicalizeAux env (canonicalizeAux env c f).2 x).2
    have h1 := canonicalizeAux_counter_le env c f
    have h2 := canonicalizeAux_counter_le env (canonicalizeAux env c f).2 x; omega
  | Force e =>
    unfold canonicalizeAux
    show c ≤ (canonicalizeAux env c e).2
    exact canonicalizeAux_counter_le env c e
  | Delay e =>
    unfold canonicalizeAux
    show c ≤ (canonicalizeAux env c e).2
    exact canonicalizeAux_counter_le env c e
  | Constr _ args =>
    unfold canonicalizeAux
    show c ≤ (canonicalizeList env c args).2
    exact canonicalizeList_counter_le env c args
  | Case scrut alts =>
    unfold canonicalizeAux
    show c ≤ (canonicalizeList env (canonicalizeAux env c scrut).2 alts).2
    have h1 := canonicalizeAux_counter_le env c scrut
    have h2 := canonicalizeList_counter_le env (canonicalizeAux env c scrut).2 alts; omega
  | Let binds body =>
    unfold canonicalizeAux
    exact canonicalizeLet_counter_le env c binds body
termination_by sizeOf e

private theorem canonicalizeList_counter_le (env : CanonEnv) (c : Nat) (es : List Expr) :
    c ≤ (canonicalizeList env c es).2 := by
  cases es with
  | nil => unfold canonicalizeList; dsimp; omega
  | cons e rest =>
    unfold canonicalizeList
    show c ≤ (canonicalizeList env (canonicalizeAux env c e).2 rest).2
    have h1 := canonicalizeAux_counter_le env c e
    have h2 := canonicalizeList_counter_le env (canonicalizeAux env c e).2 rest; omega
termination_by sizeOf es

private theorem canonicalizeLet_counter_le (env : CanonEnv) (c : Nat)
    (binds : List (VarId × Expr × Bool)) (body : Expr) :
    c ≤ (canonicalizeLet env c binds body).2 := by
  cases binds with
  | nil => unfold canonicalizeLet; exact canonicalizeAux_counter_le env c body
  | cons b rest =>
    have _hlt1 : sizeOf b.2.1 < sizeOf (b :: rest) + sizeOf body := by
      have : sizeOf b.2.1 < sizeOf b := by
        cases b with | mk a p => cases p with | mk e c => simp_wf; omega
      have : sizeOf b < sizeOf (b :: rest) := by simp_wf; omega
      omega
    unfold canonicalizeLet
    show c ≤ (canonicalizeLet ((b.1, (canonicalizeAux env c b.2.1).2) :: env)
      ((canonicalizeAux env c b.2.1).2 + 1) rest body).2
    have h1 := canonicalizeAux_counter_le env c b.2.1
    have h2 := canonicalizeLet_counter_le ((b.1, (canonicalizeAux env c b.2.1).2) :: env)
      ((canonicalizeAux env c b.2.1).2 + 1) rest body; omega
termination_by sizeOf binds + sizeOf body
end

/-! ## Source-only invariant -/

def allFreeVarsSource (e : Expr) : Prop :=
  ∀ y : VarId, (freeVars e).contains y = true → y.origin = .source

theorem allFreeVarsSource_expandFix (e : Expr) (hs : allFreeVarsSource e) :
    allFreeVarsSource (expandFix e) := by
  intro y hy
  have : (freeVars e).contains y = true := by
    cases hy' : (freeVars e).contains y with
    | true => rfl
    | false =>
      have := expandFix_freeVars_not_contains e y hy'
      rw [this] at hy; exact absurd hy (by simp)
  exact hs y this

/-! ## wellScoped for canonicalized expressions

Key insight: the counter starts at `maxUidExpr e + 1`, so all canonical
binder uids are strictly greater than any uid in the original expression.
Since `VarSet.contains` uses BEq (which checks both origin AND uid),
no canonical binder can match any element of `freeVars e`. -/

private theorem canonBinder_not_in_uid_lt_set (s : VarSet) (uid : Nat) (h : String)
    (hs : ∀ w, s.contains w = true → w.uid < uid) :
    s.contains (canonBinder uid h) = false := by
  cases hc : s.contains (canonBinder uid h)
  · rfl
  · exact absurd (hs _ hc) (by simp [canonBinder])

private theorem canonBinder_not_in_gen_uid_lt (s : VarSet) (uid : Nat) (h : String)
    (hs : ∀ w, s.contains w = true → w.origin = .gen → w.uid < uid) :
    s.contains (canonBinder uid h) = false := by
  cases hc : s.contains (canonBinder uid h)
  · rfl
  · exact absurd (hs _ hc rfl) (by simp [canonBinder])

private theorem insert_canonBinder_gen_bound (s : VarSet) (uid : Nat) (h : String)
    (hs : ∀ w, s.contains w = true → w.origin = .gen → w.uid < uid) :
    ∀ w, (s.insert (canonBinder uid h)).contains w = true → w.origin = .gen → w.uid < uid + 1 := by
  intro w hw hwo
  rcases (VarSet.contains_insert_elim s (canonBinder uid h) w).mp hw with hw | hw
  · exact Nat.lt_succ_of_lt (hs w hw hwo)
  · have ⟨_, huid⟩ := (canonBinder_beq_varid uid h w).mp hw; rw [huid]; omega

/-! The wsc lemmas prove wellScopedAux succeeds on canonicalized output.
The return type includes a bound on the returned seen-set so we can
transfer the `hseen` invariant across sequential siblings. -/

private abbrev SeenBound (s : VarSet) (c : Nat) : Prop :=
  ∀ w, s.contains w = true → w.origin = .gen → w.uid < c

mutual
private theorem wsc_expr (env : CanonEnv) (c : Nat) (e : Expr) (seen fv : VarSet)
    (henv : ∀ y v, canonEnvLookup env y = some v → v < c)
    (hfv_uid : ∀ w, fv.contains w = true → w.uid < c)
    (hseen : SeenBound seen c)
    (hfv : ∀ y, (freeVars e).contains y = true → canonEnvLookup env y = none → y.uid < c) :
    ∃ s, wellScopedAux seen fv (canonicalizeAux env c e).1 = some s ∧
         SeenBound s (canonicalizeAux env c e).2 := by
  cases e with
  | Var x =>
    unfold canonicalizeAux
    cases hel : canonEnvLookup env x <;> (dsimp; unfold wellScopedAux; exact ⟨seen, rfl, hseen⟩)
  | Lit _ | Builtin _ | Error =>
    unfold canonicalizeAux; dsimp; unfold wellScopedAux; exact ⟨seen, rfl, hseen⟩
  | Force inner =>
    unfold canonicalizeAux; dsimp; unfold wellScopedAux
    exact wsc_expr env c inner seen fv henv hfv_uid hseen
      (fun y hy hel => hfv y (by rw [freeVars.eq_8]; exact hy) hel)
  | Delay inner =>
    unfold canonicalizeAux; dsimp; unfold wellScopedAux
    exact wsc_expr env c inner seen fv henv hfv_uid hseen
      (fun y hy hel => hfv y (by rw [freeVars.eq_9]; exact hy) hel)
  | Lam x body =>
    unfold canonicalizeAux; dsimp; unfold wellScopedAux
    have hs := canonBinder_not_in_gen_uid_lt seen c x.hint hseen
    have hf := canonBinder_not_in_uid_lt_set fv c x.hint hfv_uid
    rw [hs, hf]; simp only [Bool.false_or]
    have henv' : ∀ y v, canonEnvLookup ((x, c) :: env) y = some v → v < c + 1 := by
      intro y v h; unfold canonEnvLookup at h; split at h
      · injection h with h; omega
      · exact Nat.lt_succ_of_lt (henv y v h)
    exact wsc_expr ((x, c) :: env) (c + 1) body _ fv henv'
      (fun w hw => Nat.lt_succ_of_lt (hfv_uid w hw))
      (insert_canonBinder_gen_bound seen c x.hint hseen)
      (fun y hy hel => by
        unfold canonEnvLookup at hel
        cases hxy : (x == y) <;> simp [hxy] at hel
        exact Nat.lt_succ_of_lt (hfv y (by rw [freeVars.eq_5]; exact VarSet.contains_erase_ne _ x y hxy hy) hel))
  | Fix f body =>
    unfold canonicalizeAux; dsimp; unfold wellScopedAux
    have hs := canonBinder_not_in_gen_uid_lt seen c f.hint hseen
    have hf := canonBinder_not_in_uid_lt_set fv c f.hint hfv_uid
    rw [hs, hf]; simp only [Bool.false_or]
    have henv' : ∀ y v, canonEnvLookup ((f, c) :: env) y = some v → v < c + 1 := by
      intro y v h; unfold canonEnvLookup at h; split at h
      · injection h with h; omega
      · exact Nat.lt_succ_of_lt (henv y v h)
    exact wsc_expr ((f, c) :: env) (c + 1) body _ fv henv'
      (fun w hw => Nat.lt_succ_of_lt (hfv_uid w hw))
      (insert_canonBinder_gen_bound seen c f.hint hseen)
      (fun y hy hel => by
        unfold canonEnvLookup at hel
        cases hfy : (f == y) <;> simp [hfy] at hel
        exact Nat.lt_succ_of_lt (hfv y (by rw [freeVars.eq_6]; exact VarSet.contains_erase_ne _ f y hfy hy) hel))
  | App f x =>
    unfold canonicalizeAux; dsimp; unfold wellScopedAux
    simp only [bind, Option.bind]
    have hfvf := fun y hy hel => hfv y (by rw [freeVars.eq_7]; exact VarSet.contains_union_left _ _ _ hy) hel
    have hfvx := fun y hy hel => hfv y (by rw [freeVars.eq_7]; exact VarSet.contains_union_right _ _ _ hy) hel
    have ⟨s1, hs1, hb1⟩ := wsc_expr env c f seen fv henv hfv_uid hseen hfvf
    rw [hs1]
    have henv1 := fun y v h => Nat.lt_of_lt_of_le (henv y v h) (canonicalizeAux_counter_le env c f)
    exact wsc_expr env _ x s1 fv henv1
      (fun w hw => Nat.lt_of_lt_of_le (hfv_uid w hw) (canonicalizeAux_counter_le env c f))
      hb1 (fun y hy hel => Nat.lt_of_lt_of_le (hfvx y hy hel) (canonicalizeAux_counter_le env c f))
  | Constr _ args =>
    unfold canonicalizeAux; dsimp; unfold wellScopedAux
    exact wsc_list env c args seen fv henv hfv_uid hseen
      (fun y hy hel => hfv y (by rw [freeVars.eq_10]; exact hy) hel)
  | Case scrut alts =>
    unfold canonicalizeAux; dsimp; unfold wellScopedAux
    simp only [bind, Option.bind]
    have hfvs := fun y hy hel => hfv y (by rw [freeVars.eq_11]; exact VarSet.contains_union_left _ _ _ hy) hel
    have hfva := fun y hy hel => hfv y (by rw [freeVars.eq_11]; exact VarSet.contains_union_right _ _ _ hy) hel
    have ⟨s1, hs1, hb1⟩ := wsc_expr env c scrut seen fv henv hfv_uid hseen hfvs
    rw [hs1]
    have henv1 := fun y v h => Nat.lt_of_lt_of_le (henv y v h) (canonicalizeAux_counter_le env c scrut)
    exact wsc_list env _ alts s1 fv henv1
      (fun w hw => Nat.lt_of_lt_of_le (hfv_uid w hw) (canonicalizeAux_counter_le env c scrut))
      hb1 (fun y hy hel => Nat.lt_of_lt_of_le (hfva y hy hel) (canonicalizeAux_counter_le env c scrut))
  | Let binds body =>
    unfold canonicalizeAux
    exact wsc_let env c binds body seen fv henv hfv_uid hseen
      (fun y hy hel => hfv y (by rw [freeVars.eq_12]; exact hy) hel)
termination_by sizeOf e

private theorem wsc_list (env : CanonEnv) (c : Nat) (es : List Expr) (seen fv : VarSet)
    (henv : ∀ y v, canonEnvLookup env y = some v → v < c)
    (hfv_uid : ∀ w, fv.contains w = true → w.uid < c)
    (hseen : SeenBound seen c)
    (hfv : ∀ y, (freeVarsList es).contains y = true → canonEnvLookup env y = none → y.uid < c) :
    ∃ s, wellScopedListAux seen fv (canonicalizeList env c es).1 = some s ∧
         SeenBound s (canonicalizeList env c es).2 := by
  cases es with
  | nil =>
    unfold canonicalizeList; dsimp; unfold wellScopedListAux
    exact ⟨seen, rfl, hseen⟩
  | cons e rest =>
    unfold canonicalizeList; dsimp; unfold wellScopedListAux; simp only [bind, Option.bind]
    have hfve := fun y hy hel => hfv y (by rw [freeVarsList.eq_2]; exact VarSet.contains_union_left _ _ _ hy) hel
    have hfvr := fun y hy hel => hfv y (by rw [freeVarsList.eq_2]; exact VarSet.contains_union_right _ _ _ hy) hel
    have ⟨s1, hs1, hb1⟩ := wsc_expr env c e seen fv henv hfv_uid hseen hfve
    rw [hs1]
    exact wsc_list env _ rest s1 fv
      (fun y v h => Nat.lt_of_lt_of_le (henv y v h) (canonicalizeAux_counter_le env c e))
      (fun w hw => Nat.lt_of_lt_of_le (hfv_uid w hw) (canonicalizeAux_counter_le env c e))
      hb1 (fun y hy hel => Nat.lt_of_lt_of_le (hfvr y hy hel) (canonicalizeAux_counter_le env c e))
termination_by sizeOf es

private theorem wsc_let (env : CanonEnv) (c : Nat) (binds : List (VarId × Expr × Bool))
    (body : Expr) (seen fv : VarSet)
    (henv : ∀ y v, canonEnvLookup env y = some v → v < c)
    (hfv_uid : ∀ w, fv.contains w = true → w.uid < c)
    (hseen : SeenBound seen c)
    (hfv : ∀ y, (freeVarsLet binds body).contains y = true → canonEnvLookup env y = none → y.uid < c) :
    ∃ s, wellScopedAux seen fv (canonicalizeLet env c binds body).1 = some s ∧
         SeenBound s (canonicalizeLet env c binds body).2 := by
  cases binds with
  | nil =>
    unfold canonicalizeLet; dsimp; unfold wellScopedAux wellScopedLetAux
    exact wsc_expr env c body seen fv henv hfv_uid hseen
      (fun y hy hel => hfv y (by unfold freeVarsLet; exact hy) hel)
  | cons b rest =>
    have _hlt1 : sizeOf b.2.1 < sizeOf (b :: rest) + sizeOf body := by
      have : sizeOf b.2.1 < sizeOf b := by
        cases b with | mk a p => cases p with | mk e c => simp_wf; omega
      have : sizeOf b < sizeOf (b :: rest) := by simp_wf; omega
      omega
    unfold canonicalizeLet; dsimp; unfold wellScopedAux wellScopedLetAux
    simp only [bind, Option.bind]
    have hfvr := fun y hy hel => hfv y (by rw [freeVarsLet.eq_2]; exact VarSet.contains_union_left _ _ _ hy) hel
    have ⟨s1, hs1, hb1⟩ := wsc_expr env c b.2.1 seen fv henv hfv_uid hseen hfvr
    rw [hs1]; simp only
    have hcle := canonicalizeAux_counter_le env c b.2.1
    have hs1c := canonBinder_not_in_gen_uid_lt s1 (canonicalizeAux env c b.2.1).2 b.1.hint hb1
    have hfc := canonBinder_not_in_uid_lt_set fv (canonicalizeAux env c b.2.1).2 b.1.hint
      (fun w hw => Nat.lt_of_lt_of_le (hfv_uid w hw) hcle)
    simp only [hs1c, hfc, Bool.or_false]
    unfold wellScopedLetAux
    have henv' : ∀ y v, canonEnvLookup ((b.1, (canonicalizeAux env c b.2.1).2) :: env) y = some v →
        v < (canonicalizeAux env c b.2.1).2 + 1 := by
      intro y v h; unfold canonEnvLookup at h; split at h
      · injection h with h; omega
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (henv y v h) hcle)
    have hfvrest : ∀ y, (freeVarsLet rest body).contains y = true →
        canonEnvLookup ((b.1, (canonicalizeAux env c b.2.1).2) :: env) y = none →
        y.uid < (canonicalizeAux env c b.2.1).2 + 1 := by
      intro y hy hel; unfold canonEnvLookup at hel
      cases hby : (b.1 == y) <;> simp [hby] at hel
      exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le
        (hfv y (by rw [freeVarsLet.eq_2]
                   exact VarSet.contains_union_right _ _ _ (VarSet.contains_erase_ne _ b.1 y hby hy)) hel)
        hcle)
    exact wsc_let _ _ rest body _ fv henv'
      (fun w hw => Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hfv_uid w hw) hcle) (Nat.le_succ _))
      (insert_canonBinder_gen_bound s1 _ b.1.hint hb1) hfvrest
termination_by sizeOf binds + sizeOf body
end

theorem freeVars_uid_le_maxUid (e : Expr) (y : VarId)
    (hy : (freeVars e).contains y = true) : y.uid ≤ maxUidExpr e := by
  exact Classical.byContradiction fun h => by
    have h' : y.uid > maxUidExpr e := by omega
    exact absurd hy (by rw [maxUidExpr_fresh e y h']; decide)

/-! ## Helpers for freeVars_canonicalize_sub -/

private theorem VarSet.contains_of_contains_erase (s : VarSet) (v x : VarId)
    (h : (s.erase v).contains x = true) : s.contains x = true := by
  cases hsx : s.contains x
  · exact absurd h (by rw [VarSet.erase_not_contains_fwd s v x hsx]; decide)
  · rfl

private theorem VarSet.contains_union_elim (s1 s2 : VarSet) (x : VarId)
    (h : (s1.union s2).contains x = true) :
    s1.contains x = true ∨ s2.contains x = true := by
  cases h1 : s1.contains x
  · cases h2 : s2.contains x
    · exact absurd h (by rw [VarSet.union_not_contains_fwd s1 s2 x h1 h2]; decide)
    · exact Or.inr rfl
  · exact Or.inl rfl

private theorem list_any_beq_congr (l : List VarId) (x y : VarId)
    (ho : x.origin = y.origin) (hu : x.uid = y.uid)
    (h : l.any (· == x) = true) : l.any (· == y) = true := by
  induction l with
  | nil => exact h
  | cons w rest ih =>
    simp only [List.any_cons] at h ⊢
    cases hwx : (w == x)
    · simp only [hwx, Bool.false_or] at h
      exact Bool.or_eq_true_iff.mpr (Or.inr (ih h))
    · exact Bool.or_eq_true_iff.mpr (Or.inl
        (varid_beq_iff.mpr ⟨(varid_beq_iff.mp hwx).1.trans ho, (varid_beq_iff.mp hwx).2.trans hu⟩))

private theorem VarSet.contains_beq_congr (s : VarSet) (x y : VarId)
    (hxy : (x == y) = true) (h : s.contains x = true) : s.contains y = true := by
  have ⟨ho, hu⟩ := varid_beq_iff.mp hxy
  unfold VarSet.contains at *; rw [← Array.any_toList] at *
  exact list_any_beq_congr _ x y ho hu h

/-! ## freeVars_canonicalize_sub: mutual induction

The result type says: if v is free in the canonicalized expression, then there
exists an original variable y that is free in the source expression, and either
y maps directly to v (for unchanged free vars) or y was remapped by cenv to
produce v (for bound variables viewed as canonical images). -/

private abbrev CanonFVResult (cenv : CanonEnv) (fv : VarSet) (v : VarId) : Prop :=
  ∃ y, fv.contains y = true ∧
    (((y == v) = true ∧ canonEnvLookup cenv y = none) ∨
     (∃ uid, canonEnvLookup cenv y = some uid ∧ (canonBinder uid y.hint == v) = true))

private theorem canonFV_lift_union_left {cenv : CanonEnv} {s1 s2 : VarSet} {v : VarId}
    (h : CanonFVResult cenv s1 v) : CanonFVResult cenv (s1.union s2) v := by
  obtain ⟨y, hy, hc⟩ := h; exact ⟨y, VarSet.contains_union_left s1 s2 y hy, hc⟩

private theorem canonFV_lift_union_right {cenv : CanonEnv} {s1 s2 : VarSet} {v : VarId}
    (h : CanonFVResult cenv s2 v) : CanonFVResult cenv (s1.union s2) v := by
  obtain ⟨y, hy, hc⟩ := h; exact ⟨y, VarSet.contains_union_right s1 s2 y hy, hc⟩

private theorem canonFV_lift_erase {cenv : CanonEnv} {s : VarSet} {x v : VarId}
    (h : CanonFVResult cenv s v)
    (hne_free : ∀ y, (y == v) = true → canonEnvLookup cenv y = none →
        s.contains y = true → (x == y) = false)
    (hne_canon : ∀ y uid, canonEnvLookup cenv y = some uid →
        (canonBinder uid y.hint == v) = true → s.contains y = true → (x == y) = false) :
    CanonFVResult cenv (s.erase x) v := by
  obtain ⟨y, hy, hcase⟩ := h
  cases hcase with
  | inl hfree =>
    exact ⟨y, VarSet.contains_erase_ne s x y (hne_free y hfree.1 hfree.2 hy) hy,
           Or.inl hfree⟩
  | inr hcanon =>
    obtain ⟨uid, hel, hbv⟩ := hcanon
    exact ⟨y, VarSet.contains_erase_ne s x y (hne_canon y uid hel hbv hy) hy,
           Or.inr ⟨uid, hel, hbv⟩⟩

private theorem canonFV_binder_elim {cenv : CanonEnv} {s : VarSet} {binder : VarId}
    {c : Nat} {v : VarId}
    (ih : CanonFVResult ((binder, c) :: cenv) s v)
    (hv_ne : (canonBinder c binder.hint == v) = false) :
    CanonFVResult cenv (s.erase binder) v := by
  obtain ⟨y, hy, hcase⟩ := ih
  have hby : (binder == y) = false ∨ (binder == y) = true := by
    cases (binder == y) <;> simp
  cases hby with
  | inr hby_true =>
    cases hcase with
    | inl hfree =>
      obtain ⟨_, hcenv⟩ := hfree
      unfold canonEnvLookup at hcenv; simp [hby_true] at hcenv
    | inr hcanon =>
      obtain ⟨uid, hel, hbv⟩ := hcanon
      unfold canonEnvLookup at hel; simp [hby_true] at hel
      subst hel
      exact absurd ((canonBinder_beq_varid c binder.hint v).mpr
        ((canonBinder_beq_varid c y.hint v).mp hbv))
        (by simp [hv_ne])
  | inl hby_false =>
    cases hcase with
    | inl hfree =>
      obtain ⟨hyv, hcenv⟩ := hfree
      unfold canonEnvLookup at hcenv; simp [hby_false] at hcenv
      exact ⟨y, VarSet.contains_erase_ne s binder y hby_false hy, Or.inl ⟨hyv, hcenv⟩⟩
    | inr hcanon =>
      obtain ⟨uid, hel, hbv⟩ := hcanon
      unfold canonEnvLookup at hel; simp [hby_false] at hel
      exact ⟨y, VarSet.contains_erase_ne s binder y hby_false hy, Or.inr ⟨uid, hel, hbv⟩⟩

mutual
  private theorem freeVars_canon_aux_elim (cenv : CanonEnv) (c : Nat) (e : Expr) (v : VarId)
      (hv : (freeVars (canonicalizeAux cenv c e).1).contains v = true)
      (henv : ∀ y uid, canonEnvLookup cenv y = some uid → uid < c) :
      CanonFVResult cenv (freeVars e) v := by
    cases e with
    | Var x =>
      unfold canonicalizeAux at hv; unfold freeVars at hv ⊢
      cases hel : canonEnvLookup cenv x <;> simp only [hel] at hv
      · exact ⟨x, VarSet.contains_singleton_self x,
               Or.inl ⟨by rw [VarSet.singleton_contains'] at hv; exact hv, hel⟩⟩
      · rename_i uid
        exact ⟨x, VarSet.contains_singleton_self x,
               Or.inr ⟨uid, hel, by rw [VarSet.singleton_contains'] at hv; exact hv⟩⟩
    | Lit _ => unfold canonicalizeAux at hv; dsimp at hv; unfold freeVars at hv; simp [VarSet.contains_empty] at hv
    | Builtin _ => unfold canonicalizeAux at hv; dsimp at hv; unfold freeVars at hv; simp [VarSet.contains_empty] at hv
    | Error => unfold canonicalizeAux at hv; dsimp at hv; unfold freeVars at hv; simp [VarSet.contains_empty] at hv
    | Force inner =>
      unfold canonicalizeAux at hv; dsimp at hv; unfold freeVars at hv ⊢
      exact freeVars_canon_aux_elim cenv c inner v hv henv
    | Delay inner =>
      unfold canonicalizeAux at hv; dsimp at hv; unfold freeVars at hv ⊢
      exact freeVars_canon_aux_elim cenv c inner v hv henv
    | Lam x body =>
      unfold canonicalizeAux at hv; dsimp at hv; unfold freeVars at hv ⊢
      have hv_ne : (canonBinder c x.hint == v) = false := by
        cases hb : (canonBinder c x.hint == v)
        · rfl
        · exact absurd hv (by rw [VarSet.erase_self_not_contains _ _ _ hb]; decide)
      have henv' : ∀ y uid, canonEnvLookup ((x, c) :: cenv) y = some uid → uid < c + 1 := by
        intro y uid h; unfold canonEnvLookup at h; split at h
        · injection h with h; omega
        · exact Nat.lt_succ_of_lt (henv y uid h)
      have hv_body := VarSet.contains_of_contains_erase _ _ _ hv
      exact canonFV_binder_elim
        (freeVars_canon_aux_elim ((x, c) :: cenv) (c + 1) body v hv_body henv') hv_ne
    | Fix f body =>
      unfold canonicalizeAux at hv; dsimp at hv; unfold freeVars at hv ⊢
      have hv_ne : (canonBinder c f.hint == v) = false := by
        cases hb : (canonBinder c f.hint == v)
        · rfl
        · exact absurd hv (by rw [VarSet.erase_self_not_contains _ _ _ hb]; decide)
      have henv' : ∀ y uid, canonEnvLookup ((f, c) :: cenv) y = some uid → uid < c + 1 := by
        intro y uid h; unfold canonEnvLookup at h; split at h
        · injection h with h; omega
        · exact Nat.lt_succ_of_lt (henv y uid h)
      have hv_body := VarSet.contains_of_contains_erase _ _ _ hv
      exact canonFV_binder_elim
        (freeVars_canon_aux_elim ((f, c) :: cenv) (c + 1) body v hv_body henv') hv_ne
    | App f x =>
      unfold canonicalizeAux at hv; dsimp at hv; unfold freeVars at hv ⊢
      have hcle := canonicalizeAux_counter_le cenv c f
      cases VarSet.contains_union_elim _ _ _ hv with
      | inl hf =>
        exact canonFV_lift_union_left (freeVars_canon_aux_elim cenv c f v hf henv)
      | inr hx =>
        exact canonFV_lift_union_right
          (freeVars_canon_aux_elim cenv _ x v hx
            (fun y uid h => Nat.lt_of_lt_of_le (henv y uid h) hcle))
    | Constr _ args =>
      unfold canonicalizeAux at hv; dsimp at hv; unfold freeVars at hv ⊢
      exact freeVars_canon_list_elim cenv c args v hv henv
    | Case scrut alts =>
      unfold canonicalizeAux at hv; dsimp at hv; unfold freeVars at hv ⊢
      have hcle := canonicalizeAux_counter_le cenv c scrut
      cases VarSet.contains_union_elim _ _ _ hv with
      | inl hs =>
        exact canonFV_lift_union_left (freeVars_canon_aux_elim cenv c scrut v hs henv)
      | inr ha =>
        exact canonFV_lift_union_right
          (freeVars_canon_list_elim cenv _ alts v ha
            (fun y uid h => Nat.lt_of_lt_of_le (henv y uid h) hcle))
    | Let binds body =>
      unfold canonicalizeAux at hv; unfold freeVars at ⊢
      exact freeVars_canon_let_elim cenv c binds body v hv henv
  termination_by sizeOf e

  private theorem freeVars_canon_list_elim (cenv : CanonEnv) (c : Nat) (es : List Expr)
      (v : VarId)
      (hv : (freeVarsList (canonicalizeList cenv c es).1).contains v = true)
      (henv : ∀ y uid, canonEnvLookup cenv y = some uid → uid < c) :
      CanonFVResult cenv (freeVarsList es) v := by
    cases es with
    | nil =>
      unfold canonicalizeList at hv; dsimp at hv
      rw [freeVarsList.eq_1] at hv; simp [VarSet.contains_empty] at hv
    | cons e rest =>
      unfold canonicalizeList at hv; dsimp at hv; unfold freeVarsList at hv ⊢
      have hcle := canonicalizeAux_counter_le cenv c e
      cases VarSet.contains_union_elim _ _ _ hv with
      | inl he =>
        exact canonFV_lift_union_left (freeVars_canon_aux_elim cenv c e v he henv)
      | inr hr =>
        exact canonFV_lift_union_right
          (freeVars_canon_list_elim cenv _ rest v hr
            (fun y uid h => Nat.lt_of_lt_of_le (henv y uid h) hcle))
  termination_by sizeOf es

  private theorem freeVars_canon_let_elim (cenv : CanonEnv) (c : Nat)
      (binds : List (VarId × Expr × Bool)) (body : Expr) (v : VarId)
      (hv : (freeVars (canonicalizeLet cenv c binds body).1).contains v = true)
      (henv : ∀ y uid, canonEnvLookup cenv y = some uid → uid < c) :
      CanonFVResult cenv (freeVarsLet binds body) v := by
    cases binds with
    | nil =>
      unfold canonicalizeLet at hv; dsimp at hv; unfold freeVarsLet at ⊢
      rw [freeVars.eq_12, freeVarsLet.eq_1] at hv
      exact freeVars_canon_aux_elim cenv c body v hv henv
    | cons b rest =>
      have _hlt1 : sizeOf b.2.1 < sizeOf (b :: rest) + sizeOf body := by
        have : sizeOf b.2.1 < sizeOf b := by
          cases b with | mk a p => cases p with | mk e c => simp_wf; omega
        have : sizeOf b < sizeOf (b :: rest) := by simp_wf; omega
        omega
      unfold canonicalizeLet at hv; dsimp at hv
      rw [freeVars.eq_12, freeVarsLet] at hv; unfold freeVarsLet at ⊢
      have hcle := canonicalizeAux_counter_le cenv c b.2.1
      cases VarSet.contains_union_elim _ _ _ hv with
      | inl hrhs =>
        exact canonFV_lift_union_left (freeVars_canon_aux_elim cenv c b.2.1 v hrhs henv)
      | inr hinner =>
        have hv_ne : (canonBinder (canonicalizeAux cenv c b.2.1).2 b.1.hint == v) = false := by
          cases hb : (canonBinder (canonicalizeAux cenv c b.2.1).2 b.1.hint == v)
          · rfl
          · exact absurd hinner (by rw [VarSet.erase_self_not_contains _ _ _ hb]; decide)
        have henv' : ∀ y uid,
            canonEnvLookup ((b.1, (canonicalizeAux cenv c b.2.1).2) :: cenv) y = some uid →
            uid < (canonicalizeAux cenv c b.2.1).2 + 1 := by
          intro y uid h; unfold canonEnvLookup at h; split at h
          · injection h with h; omega
          · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (henv y uid h) hcle)
        have hv_inner := VarSet.contains_of_contains_erase _ _ _ hinner
        simp only [freeVarsLet.eq_1] at hv_inner
        exact canonFV_lift_union_right (canonFV_binder_elim
          (freeVars_canon_let_elim _ _ rest body v hv_inner henv') hv_ne)
  termination_by sizeOf binds + sizeOf body
end

theorem freeVars_canonicalize_sub (e : Expr) (v : VarId)
    (hv : (freeVars (canonicalize e)).contains v = true) :
    (freeVars e).contains v = true := by
  unfold canonicalize at hv
  have h := freeVars_canon_aux_elim [] (maxUidExpr e + 1) e v hv
    (by intro y uid h; unfold canonEnvLookup at h; simp at h)
  obtain ⟨y, hy, hcase⟩ := h
  cases hcase with
  | inl hfree => exact VarSet.contains_beq_congr _ y v hfree.1 hy
  | inr hcanon =>
    obtain ⟨uid, hel, _⟩ := hcanon
    exact absurd hel (by unfold canonEnvLookup; simp)

theorem wellScopedAux_canonicalize_with_freeVars (e : Expr) :
    ∃ s, wellScopedAux VarSet.empty (freeVars e)
      (canonicalizeAux [] (maxUidExpr e + 1) e).1 = some s := by
  have hfv_bound : ∀ w, (freeVars e).contains w = true → w.uid < maxUidExpr e + 1 :=
    fun w hw => Nat.lt_succ_of_le (freeVars_uid_le_maxUid e w hw)
  have ⟨s, hs, _⟩ := wsc_expr [] (maxUidExpr e + 1) e VarSet.empty (freeVars e)
    (by intro y v h; unfold canonEnvLookup at h; simp at h)
    hfv_bound
    (by intro w hw _; simp [VarSet.contains_empty] at hw)
    (fun y hy _ => hfv_bound y hy)
  exact ⟨s, hs⟩

/-! ## lowerTotalExpr_canonicalize: mutual induction -/

private abbrev CLT (cenv : CanonEnv) (c : Nat) (env1 env2 : List VarId) (fv : VarSet) : Prop :=
  (∀ v, fv.contains v = true →
    (match canonEnvLookup cenv v with
     | some uid => envLookupT env1 (canonBinder uid v.hint)
     | none => envLookupT env1 v) = envLookupT env2 v) ∧
  (∀ y uid, canonEnvLookup cenv y = some uid → uid < c) ∧
  (∀ v, fv.contains v = true → canonEnvLookup cenv v = none → v.uid < c)

private theorem CLT_sub {cenv c env1 env2 fv1 fv2}
    (h : CLT cenv c env1 env2 fv1)
    (hsub : ∀ v, fv2.contains v = true → fv1.contains v = true) :
    CLT cenv c env1 env2 fv2 :=
  ⟨fun v hv => h.1 v (hsub v hv), h.2.1, fun v hv hel => h.2.2 v (hsub v hv) hel⟩

private theorem CLT_counter_le {cenv c1 c2 env1 env2 fv}
    (h : CLT cenv c1 env1 env2 fv) (hle : c1 ≤ c2) :
    CLT cenv c2 env1 env2 fv :=
  ⟨h.1, fun y uid hy => Nat.lt_of_lt_of_le (h.2.1 y uid hy) hle,
   fun v hv hel => Nat.lt_of_lt_of_le (h.2.2 v hv hel) hle⟩

private theorem CLT_binder {cenv : CanonEnv} {c : Nat} {env1 env2 : List VarId}
    {x : VarId} {fv_outer fv_body : VarSet}
    (h : CLT cenv c env1 env2 fv_outer)
    (_hfv_sub : ∀ v, fv_outer.contains v = true → fv_body.contains v = true)
    (hfv_erase : ∀ v, fv_body.contains v = true → (x == v) = false →
        fv_outer.contains v = true) :
    CLT ((x, c) :: cenv) (c + 1) (canonBinder c x.hint :: env1)
        (x :: env2) fv_body := by
  refine ⟨fun v hv => ?_, fun y uid hy => ?_, fun v hv hel => ?_⟩
  · -- agree: show the lookup agrees under extended envs
    cases hxv : (x == v)
    · -- v ≠ x
      have hv_out := hfv_erase v hv hxv
      have houter := h.1 v hv_out
      -- Rewrite the outer canonEnvLookup to strip the (x, c) prefix
      show (match canonEnvLookup ((x, c) :: cenv) v with
            | some uid => envLookupT (canonBinder c x.hint :: env1) (canonBinder uid v.hint)
            | none => envLookupT (canonBinder c x.hint :: env1) v) =
           envLookupT (x :: env2) v
      unfold canonEnvLookup; simp only [hxv]
      -- Now the match is on canonEnvLookup cenv v, same as houter
      -- Need to shift envLookupT through the extra cons
      show (match canonEnvLookup cenv v with
            | some uid => envLookupT (canonBinder c x.hint :: env1) (canonBinder uid v.hint)
            | none => envLookupT (canonBinder c x.hint :: env1) v) =
           envLookupT (x :: env2) v
      -- houter : (match canonEnvLookup cenv v with
      --           | some uid => envLookupT env1 (canonBinder uid v.hint)
      --           | none => envLookupT env1 v) = envLookupT env2 v
      rw [envLookupT_cons_neq x v env2 hxv]
      cases hel' : canonEnvLookup cenv v with
      | some uid =>
        simp only [hel'] at houter ⊢
        have huid_lt := h.2.1 v uid hel'
        have : (canonBinder c x.hint == canonBinder uid v.hint) = false := by
          cases hq : (canonBinder c x.hint == canonBinder uid v.hint)
          · rfl
          · exact absurd ((canonBinder_beq_canonBinder c uid x.hint v.hint).mp hq) (by omega)
        rw [envLookupT_cons_neq _ _ _ this, houter]
      | none =>
        simp only [hel'] at houter ⊢
        have hlt := h.2.2 v hv_out hel'
        have : (canonBinder c x.hint == v) = false := by
          cases hq : (canonBinder c x.hint == v)
          · rfl
          · have ⟨_, hu⟩ := varid_beq_iff.mp hq; simp [canonBinder] at hu; omega
        rw [envLookupT_cons_neq _ _ _ this, houter]
    · -- v == x
      show (match canonEnvLookup ((x, c) :: cenv) v with
            | some uid => envLookupT (canonBinder c x.hint :: env1) (canonBinder uid v.hint)
            | none => envLookupT (canonBinder c x.hint :: env1) v) =
           envLookupT (x :: env2) v
      unfold canonEnvLookup; simp only [hxv, ite_true]
      -- Goal: envLookupT (canonBinder c x.hint :: env1) (canonBinder c v.hint) = envLookupT (x :: env2) v
      have hbeq : (canonBinder c x.hint == canonBinder c v.hint) = true :=
        (canonBinder_beq_canonBinder c c x.hint v.hint).mpr rfl
      rw [show envLookupT (canonBinder c x.hint :: env1) (canonBinder c v.hint) = some 0 from by
        unfold envLookupT envLookupT.go; simp [hbeq]]
      show some 0 = envLookupT (x :: env2) v
      unfold envLookupT envLookupT.go; simp [hxv]
  ·
    unfold canonEnvLookup at hy; split at hy
    · injection hy with hy; omega
    · exact Nat.lt_succ_of_lt (h.2.1 y uid hy)
  ·
    unfold canonEnvLookup at hel; cases hxv : (x == v) <;> simp [hxv] at hel
    exact Nat.lt_succ_of_lt (h.2.2 v (hfv_erase v hv hxv) hel)

private theorem expandFix_let_eq (binds : List (VarId × Expr × Bool)) (body : Expr) :
    expandFix (.Let binds body) = .Let (expandFixBinds binds) (expandFix body) := by
  simp [expandFix]

private theorem lowerTotal_let_eq (env : List VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotal env (.Let binds body) = lowerTotalLet env binds body := by
  simp [lowerTotal]

private theorem canonicalizeAux_fix_eq (cenv : CanonEnv) (c : Nat) (f : VarId) (body : Expr) :
    (canonicalizeAux cenv c (.Fix f body)).1 =
      .Fix (canonBinder c f.hint) (canonicalizeAux ((f, c) :: cenv) (c + 1) body).1 := by
  simp only [canonicalizeAux]

private theorem lt_canon_fix_lam (cenv : CanonEnv) (c : Nat) (env1 env2 : List VarId)
    (f : VarId) (x : VarId) (inner : Expr)
    (_hinv : CLT cenv c env1 env2 (freeVars (.Fix f (.Lam x inner))))
    (ih : lowerTotal
        (canonBinder (c + 1) x.hint :: canonBinder c f.hint :: env1)
        (expandFix (canonicalizeAux ((x, c + 1) :: (f, c) :: cenv) (c + 2) inner).1) =
      lowerTotal (x :: f :: env2) (expandFix inner)) :
    lowerTotal env1 (expandFix (canonicalizeAux cenv c (.Fix f (.Lam x inner))).1) =
      lowerTotal env2 (expandFix (.Fix f (.Lam x inner))) := by
  -- Step 1: Simplify LHS canonicalizeAux to reveal Fix f' (Lam x' inner')
  have hc1 : (canonicalizeAux cenv c (.Fix f (.Lam x inner))).1 =
      .Fix (canonBinder c f.hint) (.Lam (canonBinder (c+1) x.hint)
        (canonicalizeAux ((x, c+1) :: (f, c) :: cenv) (c+2) inner).1) := by
    simp only [canonicalizeAux]
  -- Step 2: Rewrite to use lowerTotalExpr
  -- lowerTotal env (expandFix e) = lowerTotalExpr env e by definition
  have hle : ∀ env e, lowerTotal env (expandFix e) = lowerTotalExpr env e := fun _ _ => rfl
  -- Reduce goal to lowerTotalExpr form and use fix_lam_canonical
  rw [hc1]
  let inner' := (canonicalizeAux ((x, c+1) :: (f, c) :: cenv) (c+2) inner).1
  have hs1 := maxUidExpr_fresh (expandFix inner')
    ⟨maxUidExpr (expandFix inner') + 1, .gen, "s"⟩ (Nat.lt_succ_self _)
  have hs2 := maxUidExpr_fresh (expandFix inner)
    ⟨maxUidExpr (expandFix inner) + 1, .gen, "s"⟩ (Nat.lt_succ_self _)
  -- Chain: LHS = lowerTotalExpr = (...s1...).map = (...s2...).map = RHS (reversed)
  cases hR : lowerTotal
      (canonBinder (c+1) x.hint :: canonBinder c f.hint :: env1) (expandFix inner') with
  | none =>
    have hR2 : lowerTotal (x :: f :: env2) (expandFix inner) = none := ih ▸ hR
    have h1 := lowerTotal_prepend_unused_none_gen
      [canonBinder (c+1) x.hint, canonBinder c f.hint] env1
      ⟨maxUidExpr (expandFix inner') + 1, .gen, "s"⟩ (expandFix inner') (.inl hs1) hR
    have h2 := lowerTotal_prepend_unused_none_gen [x, f] env2
      ⟨maxUidExpr (expandFix inner) + 1, .gen, "s"⟩ (expandFix inner) (.inl hs2) hR2
    -- LHS: lowerTotal env1 (expandFix (Fix f' (Lam x' inner')))
    --     = lowerTotalExpr env1 (Fix f' (Lam x' inner'))
    --     = (lowerTotal (x'::f'::s1::env1) (expandFix inner')).map fixLamWrapUplc  [by canonical]
    --     = none.map fixLamWrapUplc = none  [by h1]
    -- Similarly RHS = none  [by h2]
    have hlhs : lowerTotalExpr env1 (.Fix (canonBinder c f.hint) (.Lam (canonBinder (c+1) x.hint) inner')) =
        none := by
      rw [lowerTotalExpr_fix_lam_canonical]
      simp only [List.cons_append, List.nil_append] at h1
      rw [h1]; rfl
    have hrhs : lowerTotalExpr env2 (.Fix f (.Lam x inner)) = none := by
      rw [lowerTotalExpr_fix_lam_canonical]
      simp only [List.cons_append, List.nil_append] at h2
      rw [h2]; rfl
    simp only [lowerTotalExpr] at hlhs hrhs; rw [hlhs, hrhs]
  | some t =>
    have hR2 : lowerTotal (x :: f :: env2) (expandFix inner) = some t := ih ▸ hR
    have h1 := lowerTotal_prepend_unused_gen
      [canonBinder (c+1) x.hint, canonBinder c f.hint] env1
      ⟨maxUidExpr (expandFix inner') + 1, .gen, "s"⟩ (expandFix inner') (.inl hs1) t hR
    have h2 := lowerTotal_prepend_unused_gen [x, f] env2
      ⟨maxUidExpr (expandFix inner) + 1, .gen, "s"⟩ (expandFix inner) (.inl hs2) t hR2
    let t' := Moist.Verified.renameTerm (Moist.Verified.shiftRename 3) t
    have hlhs : lowerTotalExpr env1 (.Fix (canonBinder c f.hint) (.Lam (canonBinder (c+1) x.hint) inner')) =
        some (fixLamWrapUplc t') := by
      rw [lowerTotalExpr_fix_lam_canonical]
      simp only [List.cons_append, List.nil_append] at h1
      rw [h1]; rfl
    have hrhs : lowerTotalExpr env2 (.Fix f (.Lam x inner)) =
        some (fixLamWrapUplc t') := by
      rw [lowerTotalExpr_fix_lam_canonical]
      simp only [List.cons_append, List.nil_append] at h2
      rw [h2]; rfl
    simp only [lowerTotalExpr] at hlhs hrhs; rw [hlhs, hrhs]

private theorem lt_canon_fix_nonlam (cenv : CanonEnv) (c : Nat) (env1 env2 : List VarId)
    (f : VarId) (body : Expr) (hbody : ∀ x inner, body ≠ .Lam x inner)
    (_hinv : CLT cenv c env1 env2 (freeVars (.Fix f body))) :
    lowerTotal env1 (expandFix (canonicalizeAux cenv c (.Fix f body)).1) =
      lowerTotal env2 (expandFix (.Fix f body)) := by
  cases body with
  | Lam x inner => exact absurd rfl (hbody x inner)
  | Var _ => simp only [canonicalizeAux]; split <;> (dsimp; unfold expandFix; simp [lowerTotal])
  | Lit _ =>
    simp only [canonicalizeAux]; unfold expandFix; simp [lowerTotal]
  | Builtin _ =>
    simp only [canonicalizeAux]; unfold expandFix; simp [lowerTotal]
  | Error =>
    simp only [canonicalizeAux]; unfold expandFix; simp [lowerTotal]
  | Force _ =>
    simp only [canonicalizeAux]; unfold expandFix; simp [lowerTotal]
  | Delay _ =>
    simp only [canonicalizeAux]; unfold expandFix; simp [lowerTotal]
  | Fix _ _ =>
    simp only [canonicalizeAux]; unfold expandFix; simp [lowerTotal]
  | App _ _ =>
    simp only [canonicalizeAux]; unfold expandFix; simp [lowerTotal]
  | Case _ _ =>
    simp only [canonicalizeAux]; unfold expandFix; simp [lowerTotal]
  | Constr _ _ =>
    simp only [canonicalizeAux]; unfold expandFix; simp [lowerTotal]
  | Let binds body =>
    cases binds with
    | nil =>
      simp only [canonicalizeAux, canonicalizeLet]; unfold expandFix; simp [lowerTotal]
    | cons b rest =>
      obtain ⟨bv, brhs, ber⟩ := b
      simp only [canonicalizeAux, canonicalizeLet]; unfold expandFix; simp [lowerTotal]

mutual
  private theorem lt_canon_expr (cenv : CanonEnv) (c : Nat) (env1 env2 : List VarId) (e : Expr)
      (hinv : CLT cenv c env1 env2 (freeVars e)) :
      lowerTotal env1 (expandFix (canonicalizeAux cenv c e).1) =
        lowerTotal env2 (expandFix e) := by
    cases e with
    | Var x =>
      unfold canonicalizeAux
      cases hel : canonEnvLookup cenv x <;> simp only [expandFix, lowerTotal]
      · have := hinv.1 x (by rw [freeVars]; exact VarSet.contains_singleton_self x)
        simp [hel] at this; rw [this]
      · have := hinv.1 x (by rw [freeVars]; exact VarSet.contains_singleton_self x)
        simp [hel] at this; rw [this]
    | Lit l =>
      cases l with | mk c ty => unfold canonicalizeAux; simp [expandFix, lowerTotal]
    | Builtin b => unfold canonicalizeAux; dsimp; simp [expandFix, lowerTotal]
    | Error => unfold canonicalizeAux; dsimp; simp [expandFix, lowerTotal]
    | Force inner =>
      unfold canonicalizeAux; dsimp; simp only [expandFix, lowerTotal, Option.bind_eq_bind]
      rw [lt_canon_expr cenv c env1 env2 inner
        (CLT_sub hinv (fun v hv => by rw [freeVars.eq_8]; exact hv))]
    | Delay inner =>
      unfold canonicalizeAux; dsimp; simp only [expandFix, lowerTotal, Option.bind_eq_bind]
      rw [lt_canon_expr cenv c env1 env2 inner
        (CLT_sub hinv (fun v hv => by rw [freeVars.eq_9]; exact hv))]
    | Lam x body =>
      unfold canonicalizeAux; dsimp
      simp only [expandFix, lowerTotal, Option.bind_eq_bind]
      have hinv_body : CLT ((x, c) :: cenv) (c + 1)
          (canonBinder c x.hint :: env1) (x :: env2) (freeVars body) :=
        CLT_binder
          (CLT_sub hinv (fun v hv => by rw [freeVars.eq_5]; exact hv))
          (fun v hv => VarSet.contains_of_contains_erase _ _ _ hv)
          (fun v hv hxv => VarSet.contains_erase_ne _ _ _ hxv hv)
      rw [lt_canon_expr ((x, c) :: cenv) (c + 1) _ _ body hinv_body]
    | App f a =>
      unfold canonicalizeAux; dsimp
      simp only [expandFix, lowerTotal, Option.bind_eq_bind]
      rw [lt_canon_expr cenv c env1 env2 f
            (CLT_sub hinv (fun v hv => by
              rw [freeVars.eq_7]; exact VarSet.contains_union_left _ _ _ hv)),
          lt_canon_expr cenv _ env1 env2 a
            (CLT_counter_le
              (CLT_sub hinv (fun v hv => by
                rw [freeVars.eq_7]; exact VarSet.contains_union_right _ _ _ hv))
              (canonicalizeAux_counter_le cenv c f))]
    | Constr tag args =>
      unfold canonicalizeAux; dsimp
      simp only [expandFix, lowerTotal, Option.bind_eq_bind]
      rw [lt_canon_list cenv c env1 env2 args
        (CLT_sub hinv (fun v hv => by rw [freeVars.eq_10]; exact hv))]
    | Case scrut alts =>
      unfold canonicalizeAux; dsimp
      simp only [expandFix, lowerTotal, Option.bind_eq_bind]
      rw [lt_canon_expr cenv c env1 env2 scrut
            (CLT_sub hinv (fun v hv => by
              rw [freeVars.eq_11]; exact VarSet.contains_union_left _ _ _ hv)),
          lt_canon_list cenv _ env1 env2 alts
            (CLT_counter_le
              (CLT_sub hinv (fun v hv => by
                rw [freeVars.eq_11]; exact VarSet.contains_union_right _ _ _ hv))
              (canonicalizeAux_counter_le cenv c scrut))]
    | Let binds body =>
      unfold canonicalizeAux
      show lowerTotal env1 (expandFix (canonicalizeLet cenv c binds body).1) =
        lowerTotal env2 (expandFix (.Let binds body))
      exact lt_canon_let cenv c env1 env2 binds body
        (CLT_sub hinv (fun v hv => by rw [freeVars.eq_12]; exact hv))
    | Fix f body =>
      cases body with
      | Lam x inner =>
        have hinv_f : CLT ((f, c) :: cenv) (c + 1)
            (canonBinder c f.hint :: env1) (f :: env2) ((freeVars inner).erase x) :=
          CLT_binder
            (CLT_sub hinv (fun v hv => by rw [freeVars.eq_6, freeVars.eq_5]; exact hv))
            (fun v hv => VarSet.contains_of_contains_erase _ f _ hv)
            (fun v hv hfv => VarSet.contains_erase_ne _ f v hfv hv)
        have hinv_body : CLT ((x, c + 1) :: (f, c) :: cenv) (c + 2)
            (canonBinder (c + 1) x.hint :: canonBinder c f.hint :: env1)
            (x :: f :: env2) (freeVars inner) :=
          CLT_binder hinv_f
            (fun v hv => VarSet.contains_of_contains_erase _ x _ hv)
            (fun v hv hxv => VarSet.contains_erase_ne _ x v hxv hv)
        exact lt_canon_fix_lam cenv c env1 env2 f x inner hinv
          (lt_canon_expr _ _ _ _ inner hinv_body)
      | _ =>
        exact lt_canon_fix_nonlam cenv c env1 env2 f _ (by intro x inner; exact Expr.noConfusion) hinv
  termination_by sizeOf e

  private theorem lt_canon_list (cenv : CanonEnv) (c : Nat) (env1 env2 : List VarId)
      (es : List Expr) (hinv : CLT cenv c env1 env2 (freeVarsList es)) :
      lowerTotalList env1 (expandFixList (canonicalizeList cenv c es).1) =
        lowerTotalList env2 (expandFixList es) := by
    cases es with
    | nil => unfold canonicalizeList; simp [expandFixList, lowerTotalList]
    | cons e rest =>
      unfold canonicalizeList; dsimp
      simp only [expandFixList, lowerTotalList, Option.bind_eq_bind]
      rw [lt_canon_expr cenv c env1 env2 e
            (CLT_sub hinv (fun v hv => by
              rw [freeVarsList.eq_2]; exact VarSet.contains_union_left _ _ _ hv)),
          lt_canon_list cenv _ env1 env2 rest
            (CLT_counter_le
              (CLT_sub hinv (fun v hv => by
                rw [freeVarsList.eq_2]; exact VarSet.contains_union_right _ _ _ hv))
              (canonicalizeAux_counter_le cenv c e))]
  termination_by sizeOf es

  private theorem lt_canon_let (cenv : CanonEnv) (c : Nat) (env1 env2 : List VarId)
      (binds : List (VarId × Expr × Bool)) (body : Expr)
      (hinv : CLT cenv c env1 env2 (freeVarsLet binds body)) :
      lowerTotal env1 (expandFix (canonicalizeLet cenv c binds body).1) =
        lowerTotal env2 (expandFix (.Let binds body)) := by
    cases binds with
    | nil =>
      -- Goal: lowerTotal env1 (expandFix (canonicalizeLet cenv c [] body).1) =
      --       lowerTotal env2 (expandFix (.Let [] body))
      -- canonicalizeLet cenv c [] body = (.Let [] (canonicalizeAux cenv c body).1, ...)
      -- expandFix (.Let [] e) = .Let [] (expandFix e)
      -- lowerTotal env (.Let [] body) = lowerTotalLet env [] body = lowerTotal env body
      unfold canonicalizeLet
      simp only [expandFix, expandFixBinds, lowerTotal, lowerTotalLet]
      exact lt_canon_expr cenv c env1 env2 body
        (CLT_sub hinv (fun v hv => by unfold freeVarsLet; exact hv))
    | cons b rest =>
      have _hlt1 : sizeOf b.2.1 < sizeOf (b :: rest) + sizeOf body := by
        have : sizeOf b.2.1 < sizeOf b := by
          cases b with | mk a p => cases p with | mk e c => simp_wf; omega
        have : sizeOf b < sizeOf (b :: rest) := by simp_wf; omega
        omega
      have hcle := canonicalizeAux_counter_le cenv c b.2.1
      have hinv_rhs : CLT cenv c env1 env2 (freeVars b.2.1) :=
        CLT_sub hinv (fun v hv => by
          rw [freeVarsLet.eq_2]; exact VarSet.contains_union_left _ _ _ hv)
      have hinv_rest : CLT ((b.1, (canonicalizeAux cenv c b.2.1).2) :: cenv)
          ((canonicalizeAux cenv c b.2.1).2 + 1)
          (canonBinder (canonicalizeAux cenv c b.2.1).2 b.1.hint :: env1)
          (b.1 :: env2) (freeVarsLet rest body) :=
        CLT_binder
          (CLT_counter_le
            (CLT_sub hinv (fun v hv => by
              rw [freeVarsLet.eq_2]; exact VarSet.contains_union_right _ _ _ hv))
            hcle)
          (fun v hv => VarSet.contains_of_contains_erase _ _ _ hv)
          (fun v hv hxv => VarSet.contains_erase_ne _ _ _ hxv hv)
      have ih_rhs := lt_canon_expr cenv c env1 env2 b.2.1 hinv_rhs
      have ih_rest := lt_canon_let
        ((b.1, (canonicalizeAux cenv c b.2.1).2) :: cenv)
        ((canonicalizeAux cenv c b.2.1).2 + 1)
        (canonBinder (canonicalizeAux cenv c b.2.1).2 b.1.hint :: env1)
        (b.1 :: env2) rest body hinv_rest
      unfold canonicalizeLet
      rw [expandFix_let_eq, lowerTotal_let_eq]
      simp only [expandFixBinds]
      have ih_rest' :
          lowerTotal (canonBinder (canonicalizeAux cenv c b.2.1).2 b.1.hint :: env1)
              (expandFix
                (canonicalizeLet ((b.1, (canonicalizeAux cenv c b.2.1).2) :: cenv)
                  ((canonicalizeAux cenv c b.2.1).2 + 1) rest body).1) =
            lowerTotalLet (b.1 :: env2) (expandFixBinds rest) (expandFix body) := by
        simpa [expandFix_let_eq, lowerTotal_let_eq] using ih_rest
      calc
        lowerTotalLet env1
            [(canonBinder (canonicalizeAux cenv c b.2.1).2 b.1.hint,
              expandFix (canonicalizeAux cenv c b.2.1).1, b.2.2)]
            (expandFix
              (canonicalizeLet ((b.1, (canonicalizeAux cenv c b.2.1).2) :: cenv)
                ((canonicalizeAux cenv c b.2.1).2 + 1) rest body).1) =
          lowerTotalLet env2
            ((b.1, expandFix b.2.1, b.2.2) :: expandFixBinds rest) (expandFix body) := by
              simp [lowerTotalLet, ih_rhs, ih_rest', Option.bind_eq_bind]
        _ = lowerTotal env2 (expandFix (.Let (b :: rest) body)) := by
              rw [expandFix_let_eq, lowerTotal_let_eq]
              cases b with
              | mk x p =>
                cases p with
                | mk rhs er =>
                  simp [expandFixBinds]
  termination_by sizeOf binds + sizeOf body
end

theorem lowerTotalExpr_canonicalize (env : List VarId) (e : Expr) :
    lowerTotalExpr env (canonicalize e) = lowerTotalExpr env e := by
  simp only [lowerTotalExpr, canonicalize]
  exact lt_canon_expr [] (maxUidExpr e + 1) env env e
    ⟨fun v hv => by simp [canonEnvLookup],
     fun y uid h => by simp [canonEnvLookup] at h,
     fun v hv hel => Nat.lt_succ_of_le (freeVars_uid_le_maxUid e v hv)⟩

end Moist.MIR
