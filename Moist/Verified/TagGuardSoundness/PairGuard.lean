import Moist.Verified.TagGuardSoundness.Pair

/-! # Soundness of `pairGuard`

In the scope of `case (unConstrData e₁) [λt₁ f₁. body]`, the bindings in front
of the next pair case `case (unConstrData e₂) [λt₂ f₂. B]` move into its
alternative (`factRefines_sinkPair`, one binding at a time), and the
alternative is guarded by an integer case on `t₁` and `t₂`
(`factRefines_guard`, `guard_sound`).
-/

namespace Moist.Verified.TagGuard

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast

/-! ## Syntax -/

theorem lowerTotalExpr_nestLets_congr :
    ∀ (bs : List (VarId × Expr × Bool)) {E E' : Expr},
      (∀ env, lowerTotalExpr env E = lowerTotalExpr env E') →
      ∀ env, lowerTotalExpr env (nestLets bs E) = lowerTotalExpr env (nestLets bs E')
  | [], _, _, h, env => h env
  | (x, r, er) :: bs, E, E', h, env => by
    simp only [nestLets]
    rw [lowerTotalExpr_let_single, lowerTotalExpr_let_single,
      lowerTotalExpr_nestLets_congr bs h (x :: env)]

theorem nestLets_append (bs cs : List (VarId × Expr × Bool)) (E : Expr) :
    nestLets (bs ++ cs) E = nestLets bs (nestLets cs E) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [nestLets, ih]

theorem bindingsBefore_spec : ∀ (e : Expr) (acc : List (VarId × Expr × Bool))
    {bs : List (VarId × Expr × Bool)} {inner : Expr},
    bindingsBefore e acc = some (bs, inner) →
      ∀ env, lowerTotalExpr env (nestLets acc.reverse e) = lowerTotalExpr env (nestLets bs inner)
  | .Let [] rest, acc, bs, inner, h => by
    rw [bindingsBefore] at h
    intro env
    rw [← bindingsBefore_spec rest acc h env]
    exact lowerTotalExpr_nestLets_congr _ (fun env => lowerTotalExpr_let_nil env rest) env
  | .Let ((y, rhs, er) :: more) rest, acc, bs, inner, h => by
    rw [bindingsBefore] at h
    intro env
    rw [← bindingsBefore_spec (.Let more rest) ((y, rhs, er) :: acc) h env, List.reverse_cons,
      nestLets_append]
    exact lowerTotalExpr_nestLets_congr _ (fun env => lowerTotalExpr_let_cons env _ _ _) env
  | .Var _, acc, bs, inner, h | .Lit _, acc, bs, inner, h | .Builtin _, acc, bs, inner, h
  | .Error, acc, bs, inner, h | .Lam _ _, acc, bs, inner, h | .Fix _ _, acc, bs, inner, h
  | .App _ _, acc, bs, inner, h | .Force _, acc, bs, inner, h | .Delay _, acc, bs, inner, h
  | .Constr _ _, acc, bs, inner, h | .Case _ _, acc, bs, inner, h => by
    rw [bindingsBefore] at h
    all_goals first
      | (split at h
         · cases h; exact fun _ => rfl
         · cases h)
      | (intros; simp_all)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem pairCaseView_some {e e₂ B : Expr} {t f : VarId} (h : pairCaseView e = some (e₂, t, f, B)) :
    e = .Case (.App (.Builtin .UnConstrData) e₂) [.Lam t (.Lam f B)] := by
  unfold pairCaseView at h
  split at h
  · cases h; rfl
  · cases h

/-! ## Moving the bindings -/

theorem sinkPair_lowering {x : VarId} {r : Expr} {er : Bool} {e₂ Y : Expr} {t f : VarId}
    (hterm : terminates (.App (.Builtin .UnConstrData) e₂) = true)
    (hx : (freeVars e₂).contains x = false) (ht : (freeVars r).contains t = false)
    (hf : (freeVars r).contains f = false) (hft : (f == t) = false) (hfx : (f == x) = false)
    (htx : (t == x) = false) :
    ∀ env tt, lowerTotalExpr env
        (.Let [(x, r, er)] (.Case (.App (.Builtin .UnConstrData) e₂) [.Lam t (.Lam f Y)])) = some tt →
      ∃ t', lowerTotalExpr env
          (.Case (.App (.Builtin .UnConstrData) e₂) [.Lam t (.Lam f (.Let [(x, r, er)] Y))]) = some t' ∧
        ∀ F, FactRefines env.length F tt t' := by
  intro env tt hlow
  obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
  obtain ⟨tsc, talts, htsc, htalts, rfl⟩ := lowerTotalExpr_case_some htb
  obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some htsc
  rw [lowerTotalExpr_builtin] at htf; cases htf
  rw [MIR.lowerTotalExpr_prepend_unused env x e₂ hx] at hta
  cases hE : lowerTotalExpr env e₂ with
  | none => rw [hE] at hta; cases hta
  | some tE =>
    rw [hE] at hta; cases hta
    rw [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil] at htalts
    cases hl : lowerTotalExpr (x :: env) (.Lam t (.Lam f Y)) with
    | none => rw [hl] at htalts; cases htalts
    | some tl =>
      rw [hl] at htalts; cases htalts
      obtain ⟨tl1, htl1, rfl⟩ := lowerTotalExpr_lam_some hl
      obtain ⟨tB, htB, rfl⟩ := lowerTotalExpr_lam_some htl1
      have hrot := lowerTotalExpr_rot hft hfx htx env Y
      rw [htB] at hrot
      have hr2 : lowerTotalExpr (f :: t :: env) r =
          some (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) tr)) := by
        rw [MIR.lowerTotalExpr_prepend_unused (t :: env) f r hf,
          MIR.lowerTotalExpr_prepend_unused env t r ht, htr]; rfl
      refine ⟨.Case (.Apply (.Builtin .UnConstrData) tE) [.Lam 0 (.Lam 0 (.Apply
        (.Lam 0 (renameTerm rotRename tB)) (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) tr))))],
        ?_, fun F => ?_⟩
      · rw [MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExpr_app, lowerTotalExpr_builtin, hE,
          MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil, MIR.lowerTotalExpr_lam,
          MIR.lowerTotalExpr_lam, lowerTotalExpr_let_single, hr2, hrot]
        rfl
      · have hBc := MIR.lowerTotalExpr_closedAt htB
        simp only [List.length_cons] at hBc
        refine factRefines_sinkPair (MIR.lowerTotalExpr_closedAt htr) (MIR.lowerTotalExpr_closedAt hE)
          hBc ?_
        have := terminates_sound hterm (env := env)
          (t := .Apply (.Builtin .UnConstrData) tE) (by
            rw [MIR.lowerTotalExpr_app, lowerTotalExpr_builtin, hE]; rfl)
        exact this

theorem sinkAll_lowering {e₂ B : Expr} {t f : VarId}
    (hterm : terminates (.App (.Builtin .UnConstrData) e₂) = true) (hft : (f == t) = false) :
    ∀ (bs : List (VarId × Expr × Bool)),
      (∀ b ∈ bs, (freeVars e₂).contains b.1 = false ∧ (freeVars b.2.1).contains t = false ∧
        (freeVars b.2.1).contains f = false ∧ (b.1 == t) = false ∧ (b.1 == f) = false) →
      ∀ env tt, lowerTotalExpr env
          (nestLets bs (.Case (.App (.Builtin .UnConstrData) e₂) [.Lam t (.Lam f B)])) = some tt →
        ∃ t', lowerTotalExpr env
            (.Case (.App (.Builtin .UnConstrData) e₂) [.Lam t (.Lam f (nestLets bs B))]) = some t' ∧
          ∀ F, FactRefines env.length F tt t'
  | [], _, env, tt, h => ⟨tt, h, fun _ => FactRefines.refl _ _ _⟩
  | (x, r, er) :: bs, hconds, env, tt, h => by
    simp only [nestLets] at h ⊢
    obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some h
    obtain ⟨tb', htb', hrb⟩ := sinkAll_lowering hterm hft bs (fun c hc => hconds c (.tail _ hc))
      (x :: env) tb htb
    obtain ⟨hx, ht, hf, hxt, hxf⟩ := hconds (x, r, er) (.head _)
    have hmid : lowerTotalExpr env (.Let [(x, r, er)]
        (.Case (.App (.Builtin .UnConstrData) e₂) [.Lam t (.Lam f (nestLets bs B))])) =
        some (.Apply (.Lam 0 tb') tr) := by
      rw [lowerTotalExpr_let_single, htr, htb']; rfl
    obtain ⟨t', ht', hr'⟩ := sinkPair_lowering (Y := nestLets bs B) (er := er) hterm hx ht hf hft
      (by rw [Moist.Verified.InlineSoundness.Rename.beq_comm]; exact hxf)
      (by rw [Moist.Verified.InlineSoundness.Rename.beq_comm]; exact hxt) env _ hmid
    refine ⟨t', ht', fun F => ?_⟩
    have closedR := MIR.lowerTotalExpr_closedAt htr
    refine (factRefines_let (G := fun _ => True) 0 0 closedR (fun _ _ _ _ => trivial) ?_).trans (hr' F)
    simpa using hrb (fun _ => True)

/-! ## The guard -/

theorem valIn_congr {env : List VarId} {ρ : CekEnv} {x y : VarId} {v : CekValue} (h : (x == y) = true)
    (hy : ValIn env ρ y v) : ValIn env ρ x v := by
  obtain ⟨i, hi, hl⟩ := hy
  exact ⟨i, by rw [envLookupT_congr h env]; exact hi, hl⟩

theorem gAllVars_of_varsAmong {P : VarId → Prop} {p q : VarId}
    (hcongr : ∀ x y, (x == y) = true → P y → P x) (hp : P p) (hq : P q) :
    ∀ (N : Nat) (T : GuardTree), sizeOf T < N → T.varsAmong p q = true → gAllVars P T
  | 0, _, h, _ => absurd h (by omega)
  | N + 1, .ok, _, _ => by simp [gAllVars]
  | N + 1, .fail, _, _ => by simp [gAllVars]
  | N + 1, .split x ts, hsize, h => by
    simp only [GuardTree.varsAmong, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at h
    obtain ⟨hx, hall⟩ := h
    refine ⟨hx.elim (fun h => hcongr x p h hp) (fun h => hcongr x q h hq), ?_⟩
    have : ∀ (us : List GuardTree), (∀ u ∈ us, u ∈ ts) → gAllVarsList P us := by
      intro us
      induction us with
      | nil => intro _; trivial
      | cons u us ih =>
        intro hsub
        have hu := hsub u (.head _)
        refine ⟨gAllVars_of_varsAmong hcongr hp hq N u ?_ (hall ⟨u, hu⟩ (List.mem_attach _ _)),
          ih fun w hw => hsub w (.tail _ hw)⟩
        have := List.sizeOf_lt_of_mem hu
        simp only [GuardTree.split.sizeOf_spec] at hsize; omega
    exact this ts fun _ h => h

theorem toExpr_lowers {p q : VarId} (env : List VarId)
    (hp : (envLookupT env p).isSome = true) (hq : (envLookupT env q).isSome = true) :
    ∀ (N : Nat) (T : GuardTree), sizeOf T < N → T.varsAmong p q = true →
      ∃ t, lowerTotalExpr env T.toExpr = some t
  | 0, _, h, _ => absurd h (by omega)
  | N + 1, .ok, _, _ => ⟨_, by rw [GuardTree.toExpr, unitExpr, lowerTotalExpr_lit]⟩
  | N + 1, .fail, _, _ => ⟨_, by rw [GuardTree.toExpr, lowerTotalExpr_error]⟩
  | N + 1, .split x ts, hsize, hamong => by
    simp only [GuardTree.varsAmong, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at hamong
    obtain ⟨hx, hall⟩ := hamong
    have hxe : (envLookupT env x).isSome = true := by
      rcases hx with h | h
      · rw [envLookupT_congr h env]; exact hp
      · rw [envLookupT_congr h env]; exact hq
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hxe
    have halts : ∀ (us : List GuardTree), (∀ u ∈ us, u ∈ ts) →
        ∃ tus, MIR.lowerTotalExprList env (us.map GuardTree.toExpr) = some tus := by
      intro us
      induction us with
      | nil => intro _; exact ⟨[], MIR.lowerTotalExprList_nil _⟩
      | cons u us ih =>
        intro hsub
        have hu := hsub u (.head _)
        have hs : sizeOf u < N := by
          have := List.sizeOf_lt_of_mem hu
          simp only [GuardTree.split.sizeOf_spec] at hsize; omega
        obtain ⟨tu, htu⟩ := toExpr_lowers env hp hq N u hs (hall ⟨u, hu⟩ (List.mem_attach _ _))
        obtain ⟨tus, htus⟩ := ih fun w hw => hsub w (.tail _ hw)
        exact ⟨tu :: tus, by rw [List.map_cons, MIR.lowerTotalExprList_cons, htu, htus]; rfl⟩
    obtain ⟨tus, htus⟩ := halts ts fun _ h => h
    refine ⟨.Case (.Var (i + 1)) tus, ?_⟩
    have hmap : ts.attach.map (fun ⟨t, _⟩ => t.toExpr) = ts.map GuardTree.toExpr := by simp
    simp only [GuardTree.toExpr]
    rw [hmap, MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_var, hi, htus]
    rfl

/-! ## The rewrite -/

/-- `M ⊑ case G [M]` when `G` terminates, fails only where `M` cannot halt and
    otherwise returns the unit constant. -/
theorem factRefines_guard {d : Nat} {F : CekEnv → Prop} {tG tM : Term}
    (hterm : TerminatesAt d tG)
    (hguard : ∀ ρ, F ρ → EnvWellFormed d ρ → d ≤ ρ.length →
      (Errs ρ tG → ¬ ∃ v, Halts ρ tM v) ∧ (∀ w, Halts ρ tG w → w = .VCon .Unit)) :
    FactRefines d F tM (.Case tG [tM]) := by
  intro ρ π henv hlen _ hF
  obtain ⟨herr, hunit⟩ := hguard ρ hF henv hlen
  rcases hterm ρ henv hlen with he | ⟨w, hw⟩
  · refine obsRefines_of_left_no_halt ?_ (reaches_trans (reaches_of_steps 1 rfl) (errs_on_stack he _))
    rintro ⟨v, hv⟩
    rcases sequence (.inr ⟨v, rfl⟩) hv with ⟨_, hx⟩ | ⟨u, hu, _⟩
    · cases hx
    · exact herr he ⟨u, hu⟩
  · have := hunit w hw
    subst this
    refine obsRefines_of_reaches (reaches_refl _) ?_ (obsRefines_refl _)
    exact reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (halts_on_stack hw _)
      (reaches_of_steps 1 rfl))

theorem not_true' {b : Bool} (h : (!b) = true) : b = false := by
  cases b <;> simp_all

theorem beq_false_symm' {a b : VarId} (h : (a == b) = false) : (b == a) = false := by
  rw [Moist.Verified.InlineSoundness.Rename.beq_comm]; exact h

theorem pairGuard_sound {Γ : List (VarId × Expr)} {t₁ f₁ : VarId} {body guarded : Expr}
    (h : pairGuard Γ t₁ f₁ body = some guarded) :
    ∀ (env : List VarId) (tbody : Term), EnvDistinct env →
      lowerTotalExpr (f₁ :: t₁ :: env) body = some tbody →
      ∃ tg, lowerTotalExpr (f₁ :: t₁ :: env) guarded = some tg ∧
        FactRefines (env.length + 2) (PairExt env.length (FactsHold Produces Γ env)) tbody tg := by
  intro env tbody hd hlow
  unfold pairGuard at h
  split at h
  · cases h
  · rename_i bs inner hbb
    split at h
    · cases h
    · rename_i e₂ t₂ f₂ B hpv
      have hinner := pairCaseView_some hpv
      subst hinner
      simp only [] at h
      split at h
      · rename_i hcond
        cases h
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, _⟩, htf2⟩, hterm⟩, _⟩, hbs⟩, _⟩, hamong⟩,
          hGterm⟩, _⟩, hok⟩ := hcond
        replace h1 := not_true' h1
        replace h2 := not_true' h2
        replace h3 := not_true' h3
        replace htf2 := not_true' htf2
        replace hbs := List.all_eq_true.mp hbs
        -- the bindings move into the inner alternative
        have hspec := bindingsBefore_spec body [] hbb (f₁ :: t₁ :: env)
        simp only [List.reverse_nil, nestLets] at hspec
        rw [hspec] at hlow
        obtain ⟨t', ht', hr⟩ := sinkAll_lowering hterm (beq_false_symm' htf2) bs (by
            intro b hb
            have := hbs b hb
            simp only [Bool.and_eq_true] at this
            exact ⟨not_true' this.1.1.1.1.1, not_true' this.1.1.1.1.2, not_true' this.1.1.1.2,
              not_true' this.1.1.2, not_true' this.1.2⟩)
          (f₁ :: t₁ :: env) tbody hlow
        obtain ⟨tsc, talts, htsc, htalts, rfl⟩ := lowerTotalExpr_case_some ht'
        obtain ⟨tf, tE, htf, htE, rfl⟩ := lowerTotalExpr_app_some htsc
        rw [lowerTotalExpr_builtin] at htf; cases htf
        rw [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil] at htalts
        cases hl : lowerTotalExpr (f₁ :: t₁ :: env) (.Lam t₂ (.Lam f₂ (nestLets bs B))) with
        | none => rw [hl] at htalts; cases htalts
        | some tl =>
          rw [hl] at htalts; cases htalts
          obtain ⟨tl1, htl1, rfl⟩ := lowerTotalExpr_lam_some hl
          obtain ⟨tM, htM, rfl⟩ := lowerTotalExpr_lam_some htl1
          -- the guard lowers where the tags are bound
          have hlook1 : envLookupT (f₂ :: t₂ :: f₁ :: t₁ :: env) t₁ = some 3 := by
            rw [envLookupT_cons, if_neg (by simp [beq_false_symm' h3]), envLookupT_cons,
              if_neg (by simp [beq_false_symm' h2]), envLookupT_cons, if_neg (by simp [beq_false_symm' h1]),
              envLookupT_cons, if_pos (by simp [VarId.beq_true_iff])]
            rfl
          have hlook2 : envLookupT (f₂ :: t₂ :: f₁ :: t₁ :: env) t₂ = some 1 := by
            rw [envLookupT_cons, if_neg (by simp [beq_false_symm' htf2]), envLookupT_cons,
              if_pos (by simp [VarId.beq_true_iff])]
            rfl
          obtain ⟨tG, htG⟩ := toExpr_lowers (f₂ :: t₂ :: f₁ :: t₁ :: env) (by rw [hlook1]; rfl)
            (by rw [hlook2]; rfl) _ _ (Nat.lt_succ_self _) hamong
          refine ⟨.Case (.Apply (.Builtin .UnConstrData) tE) [.Lam 0 (.Lam 0 (.Case tG [tM]))], ?_, ?_⟩
          · rw [MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExpr_app, lowerTotalExpr_builtin, htE,
              MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil, MIR.lowerTotalExpr_lam,
              MIR.lowerTotalExpr_lam, MIR.lowerTotalExpr_case_of_list, htG,
              MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil, htM]
            rfl
          · refine (hr _).trans (factRefines_pairCase (MIR.lowerTotalExpr_closedAt htE) ?_)
            have hGt := terminates_sound hGterm htG
            simp only [List.length_cons] at hGt
            refine factRefines_guard hGt ?_
            rintro ρ₄ ⟨ρ₂, n₂, c₂, rfl, ⟨ρ, n₁, c₁, rfl, hFe, hwf, hlen⟩, _, _⟩ _ _
            have hctx : Ctx Γ [] [(f₂, .top), (t₂, .top), (f₁, .top), (t₁, .top)] env
                ((((ρ.extend (.VCon (.Integer n₁))).extend (.VCon c₁)).extend (.VCon (.Integer n₂))).extend
                  (.VCon c₂)) := by
              refine ⟨hd, by simpa using hFe, fun x a ha => by simp [lookupAVal] at ha, ?_⟩
              intro i hi
              simp only [List.length_cons, List.length_nil] at hi
              match i, hi with
              | 0, _ => exact ⟨_, rfl, trivial⟩
              | 1, _ => exact ⟨_, rfl, trivial⟩
              | 2, _ => exact ⟨_, rfl, trivial⟩
              | 3, _ => exact ⟨_, rfl, trivial⟩
            exact guard_sound _ _ [] _ (Nat.lt_succ_self _) htM hok hctx
              (gAllVars_of_varsAmong (fun x y hxy hy => by
                  obtain ⟨v, hv, hint⟩ := hy
                  exact ⟨v, valIn_congr hxy hv, hint⟩)
                ⟨_, ⟨3, hlook1, rfl⟩, n₁, rfl⟩ ⟨_, ⟨1, hlook2, rfl⟩, n₂, rfl⟩ _ _
                (Nat.lt_succ_self _) hamong) tG htG
      · cases h

end Moist.Verified.TagGuard
