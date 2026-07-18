import Moist.SMT.Soundness.AdvancedBuiltinFailureTernary

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.Verified.BigStep
open Moist.CEK (ArgKind ExpectedArgs expectedArgs CekEnv CekValue)

/-! Generic failure proofs for the advanced concrete builtins.  These reduce
the repetitive argument-count/error-branch reasoning to two completeness
obligations: every concrete CEK success satisfies the projection guard, and
for guarded builtins it also satisfies the runtime-definedness guard. -/

set_option maxHeartbeats 0 in
theorem binaryCheckedConstBuiltinError
    (b : BuiltinFun) (p : SymVal → SymVal → Proj SExpr)
    (mk : SExpr → SymConst)
    (hone : ∀ x y, evalBuiltinSym b [x, y] = checkedConst (p x y) mk)
    (_hother : ∀ args, args.length ≠ 2 → evalBuiltinSym b args = err)
    (hlen : ∀ cargs, cargs.length ≠ 2 → Moist.CEK.evalBuiltin b cargs = none)
    (hguard : ∀ {m : SmtSem.Model} {x y : SymVal} {cx cy cv : CekValue},
      symValToCek? m x = some cx → symValToCek? m y = some cy →
      Moist.CEK.evalBuiltin b [cx, cy] = some cv →
      pcHolds m (p x y).guard = true) : BuiltinErrorSound b := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      apply hlen cargs
      intro htwo
      have hzero : cargs.length = 0 := by
        simpa using symValListToCekList_length hargs
      omega
  | cons x rest =>
      cases rest with
      | nil =>
          apply hlen cargs
          intro htwo
          have hone' : cargs.length = 1 := by
            simpa using symValListToCekList_length hargs
          omega
      | cons y tail =>
          cases tail with
          | cons extra tail' =>
              apply hlen cargs
              intro htwo
              have hthree : 3 ≤ cargs.length := by
                rw [symValListToCekList_length hargs]
                simp
              omega
          | nil =>
              rw [hone x y] at hmem
              simp only [checkedConst, checked1, List.mem_cons,
                List.not_mem_nil] at hmem
              obtain ⟨cx, cy, hx, hy, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  cases hcek : Moist.CEK.evalBuiltin b [cx, cy] with
                  | none => rfl
                  | some cv =>
                      exact False.elim (pcHolds_not_contra
                        (hguard hx hy hcek) hactive)
                · cases hfalse

set_option maxHeartbeats 0 in
theorem ternaryCheckedConstBuiltinError
    (b : BuiltinFun) (p : SymVal → SymVal → SymVal → Proj SExpr)
    (mk : SExpr → SymConst)
    (hone : ∀ x y z, evalBuiltinSym b [x, y, z] = checkedConst (p x y z) mk)
    (_hother : ∀ args, args.length ≠ 3 → evalBuiltinSym b args = err)
    (hlen : ∀ cargs, cargs.length ≠ 3 → Moist.CEK.evalBuiltin b cargs = none)
    (hguard : ∀ {m : SmtSem.Model} {x y z : SymVal}
        {cx cy cz cv : CekValue},
      symValToCek? m x = some cx → symValToCek? m y = some cy →
      symValToCek? m z = some cz →
      Moist.CEK.evalBuiltin b [cx, cy, cz] = some cv →
      pcHolds m (p x y z).guard = true) : BuiltinErrorSound b := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      apply hlen cargs
      intro hthree
      have hzero : cargs.length = 0 := by
        simpa using symValListToCekList_length hargs
      omega
  | cons x rest =>
      cases rest with
      | nil =>
          apply hlen cargs
          intro hthree
          have hone' : cargs.length = 1 := by
            simpa using symValListToCekList_length hargs
          omega
      | cons y tail =>
          cases tail with
          | nil =>
              apply hlen cargs
              intro hthree
              have htwo : cargs.length = 2 := by
                simpa using symValListToCekList_length hargs
              omega
          | cons z tail' =>
              cases tail' with
              | cons extra tail'' =>
                  apply hlen cargs
                  intro hthree
                  have hfour : 4 ≤ cargs.length := by
                    rw [symValListToCekList_length hargs]
                    simp
                  omega
              | nil =>
                  rw [hone x y z] at hmem
                  simp only [checkedConst, checked1, List.mem_cons,
                    List.not_mem_nil] at hmem
                  obtain ⟨cx, cy, cz, hx, hy, hz, rfl⟩ :=
                    symValListToCekList_triple hargs
                  rcases hmem with hok | herr
                  · subst out
                    simp [outcomeErrorActive] at hactive
                  · rcases herr with herr | hfalse
                    · subst out
                      cases hcek : Moist.CEK.evalBuiltin b [cx, cy, cz] with
                      | none => rfl
                      | some cv =>
                          exact False.elim (pcHolds_not_contra
                            (hguard hx hy hz hcek) hactive)
                    · cases hfalse

set_option maxHeartbeats 0 in
theorem binaryCheckedGuardedBuiltinError
    {A : Type} (b : BuiltinFun) (p : SymVal → SymVal → Proj A)
    (innerGuard : A → SExpr) (result : A → SymVal)
    (hone : ∀ x y, evalBuiltinSym b [x, y] =
      checked2 (p x y) (fun a =>
        [.ok (innerGuard a) (result a), .error (SExpr.not (innerGuard a))]))
    (_hother : ∀ args, args.length ≠ 2 → evalBuiltinSym b args = err)
    (hlen : ∀ cargs, cargs.length ≠ 2 → Moist.CEK.evalBuiltin b cargs = none)
    (hprojection : ∀ {m : SmtSem.Model} {x y : SymVal} {cx cy cv : CekValue},
      symValToCek? m x = some cx → symValToCek? m y = some cy →
      Moist.CEK.evalBuiltin b [cx, cy] = some cv →
      pcHolds m (p x y).guard = true)
    (hinner : ∀ {m : SmtSem.Model} {x y : SymVal} {cx cy cv : CekValue},
      symValToCek? m x = some cx → symValToCek? m y = some cy →
      Moist.CEK.evalBuiltin b [cx, cy] = some cv →
      pcHolds m (innerGuard (p x y).val) = true) : BuiltinErrorSound b := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      apply hlen cargs
      intro htwo
      have hzero : cargs.length = 0 := by
        simpa using symValListToCekList_length hargs
      omega
  | cons x rest =>
      cases rest with
      | nil =>
          apply hlen cargs
          intro htwo
          have hone' : cargs.length = 1 := by
            simpa using symValListToCekList_length hargs
          omega
      | cons y tail =>
          cases tail with
          | cons extra tail' =>
              apply hlen cargs
              intro htwo
              have hthree : 3 ≤ cargs.length := by
                rw [symValListToCekList_length hargs]
                simp
              omega
          | nil =>
              rw [hone x y] at hmem
              obtain ⟨cx, cy, hx, hy, rfl⟩ := symValListToCekList_pair hargs
              have hpath := checked2_active_error hmem hactive
              cases hcek : Moist.CEK.evalBuiltin b [cx, cy] with
              | none => rfl
              | some cv =>
                  rcases hpath with hinside | houtside
                  · rcases hinside with ⟨inner, hinnerMem, _hp, hinnerActive⟩
                    simp only [List.mem_cons, List.not_mem_nil] at hinnerMem
                    rcases hinnerMem with hok | herr
                    · subst inner
                      simp [outcomeErrorActive] at hinnerActive
                    · rcases herr with herr | hfalse
                      · subst inner
                        exact False.elim (pcHolds_not_contra
                          (hinner hx hy hcek) hinnerActive)
                      · cases hfalse
                  · exact False.elim (pcHolds_not_contra
                      (hprojection hx hy hcek) houtside)

set_option maxHeartbeats 0 in
theorem ternaryCheckedGuardedBuiltinError
    {A : Type} (b : BuiltinFun)
    (p : SymVal → SymVal → SymVal → Proj A)
    (innerGuard : A → SExpr) (result : A → SymVal)
    (hone : ∀ x y z, evalBuiltinSym b [x, y, z] =
      checked2 (p x y z) (fun a =>
        [.ok (innerGuard a) (result a), .error (SExpr.not (innerGuard a))]))
    (_hother : ∀ args, args.length ≠ 3 → evalBuiltinSym b args = err)
    (hlen : ∀ cargs, cargs.length ≠ 3 → Moist.CEK.evalBuiltin b cargs = none)
    (hprojection : ∀ {m : SmtSem.Model} {x y z : SymVal}
        {cx cy cz cv : CekValue},
      symValToCek? m x = some cx → symValToCek? m y = some cy →
      symValToCek? m z = some cz →
      Moist.CEK.evalBuiltin b [cx, cy, cz] = some cv →
      pcHolds m (p x y z).guard = true)
    (hinner : ∀ {m : SmtSem.Model} {x y z : SymVal}
        {cx cy cz cv : CekValue},
      symValToCek? m x = some cx → symValToCek? m y = some cy →
      symValToCek? m z = some cz →
      Moist.CEK.evalBuiltin b [cx, cy, cz] = some cv →
      pcHolds m (innerGuard (p x y z).val) = true) : BuiltinErrorSound b := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      apply hlen cargs
      intro hthree
      have hzero : cargs.length = 0 := by
        simpa using symValListToCekList_length hargs
      omega
  | cons x rest =>
      cases rest with
      | nil =>
          apply hlen cargs
          intro hthree
          have hone' : cargs.length = 1 := by
            simpa using symValListToCekList_length hargs
          omega
      | cons y tail =>
          cases tail with
          | nil =>
              apply hlen cargs
              intro hthree
              have htwo : cargs.length = 2 := by
                simpa using symValListToCekList_length hargs
              omega
          | cons z tail' =>
              cases tail' with
              | cons extra tail'' =>
                  apply hlen cargs
                  intro hthree
                  have hfour : 4 ≤ cargs.length := by
                    rw [symValListToCekList_length hargs]
                    simp
                  omega
              | nil =>
                  rw [hone x y z] at hmem
                  obtain ⟨cx, cy, cz, hx, hy, hz, rfl⟩ :=
                    symValListToCekList_triple hargs
                  have hpath := checked2_active_error hmem hactive
                  cases hcek : Moist.CEK.evalBuiltin b [cx, cy, cz] with
                  | none => rfl
                  | some cv =>
                      rcases hpath with hinside | houtside
                      · rcases hinside with
                          ⟨inner, hinnerMem, _hp, hinnerActive⟩
                        simp only [List.mem_cons, List.not_mem_nil] at hinnerMem
                        rcases hinnerMem with hok | herr
                        · subst inner
                          simp [outcomeErrorActive] at hinnerActive
                        · rcases herr with herr | hfalse
                          · subst inner
                            exact False.elim (pcHolds_not_contra
                              (hinner hx hy hz hcek) hinnerActive)
                          · cases hfalse
                      · exact False.elim (pcHolds_not_contra
                          (hprojection hx hy hz hcek) houtside)

theorem pcHolds_defined_of_const_success
    {m : SmtSem.Model} {guard : SExpr} {b : BuiltinFun}
    {cs : List Const} {c : Const}
    (heval : SmtSem.eval m guard = some (.bool
      (Moist.SMT.Semantics.cekBuiltinConstDefined b cs)))
    (hconst : Moist.CEK.evalBuiltinConst b cs = some c) :
    pcHolds m guard = true := by
  apply (Moist.SMT.Semantics.evalBoolIs_true_eq m guard).mpr
  simpa [Moist.SMT.Semantics.cekBuiltinConstDefined, hconst] using heval

theorem evalBuiltinConst_some_of_evalBuiltin_vcons
    {b : BuiltinFun} {cs : List Const} {cv : CekValue}
    (hpass : Moist.CEK.evalBuiltinPassThrough b (cs.map CekValue.VCon) = none)
    (hcek : Moist.CEK.evalBuiltin b (cs.map CekValue.VCon) = some cv) :
    ∃ c, Moist.CEK.evalBuiltinConst b cs = some c := by
  rw [Moist.CEK.evalBuiltin, hpass, extractConsts_map_vcon] at hcek
  cases hc : Moist.CEK.evalBuiltinConst b cs with
  | none => simp [hc] at hcek
  | some c => exact ⟨c, rfl⟩

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_AddInteger :
    BuiltinErrorSound .AddInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_AddInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_AddInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_AddInteger_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt aSym).guard (asInt bSym).guard)
                  (SymVal.const (SymConst.integer
                    (SExpr.intAdd (asInt aSym).val (asInt bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt aSym).guard (asInt bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                  · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                    have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                    have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt aSym).guard (asInt bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_AddInteger_none_of_pair_not_ints (by
                      intro ib ia h
                      exact hshape ⟨ib, ia, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_AddInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_SubtractInteger :
    BuiltinErrorSound .SubtractInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_SubtractInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_SubtractInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_SubtractInteger_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt aSym).guard (asInt bSym).guard)
                  (SymVal.const (SymConst.integer
                    (SExpr.intSub (asInt aSym).val (asInt bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt aSym).guard (asInt bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                  · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                    have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                    have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt aSym).guard (asInt bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_SubtractInteger_none_of_pair_not_ints (by
                      intro ib ia h
                      exact hshape ⟨ib, ia, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_SubtractInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_MultiplyInteger :
    BuiltinErrorSound .MultiplyInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_MultiplyInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_MultiplyInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_MultiplyInteger_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt aSym).guard (asInt bSym).guard)
                  (SymVal.const (SymConst.integer
                    (SExpr.intMul (asInt aSym).val (asInt bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt aSym).guard (asInt bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                  · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                    have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                    have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt aSym).guard (asInt bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_MultiplyInteger_none_of_pair_not_ints (by
                      intro ib ia h
                      exact hshape ⟨ib, ia, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_MultiplyInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_DivideInteger :
    BuiltinErrorSound .DivideInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_DivideInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_DivideInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_DivideInteger_eq bSym aSym] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases checked2_active_error hmem hactive with hinner | hproj
              · rcases hinner with ⟨inner, hinnerMem, hpArgs, hinnerActive⟩
                simp only [List.mem_cons, List.not_mem_nil] at hinnerMem
                rcases hinnerMem with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mp hpArgs
                    obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                    obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                    have hz : ib = 0 :=
                      pcHolds_not_ne_int_zero heb
                        (by simpa [outcomeErrorActive, divisionGuard] using hinnerActive)
                    exact evalBuiltin_DivideInteger_none_of_divisor_zero (a := ia) (b := ib) hz
                  · cases hfalse
              · by_cases hshape :
                    ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                  have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                  have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                  have hg :
                      pcHolds m
                        (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                    simpa [pcHolds] using
                      ((Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mpr
                          ⟨by simpa [pcHolds] using hga,
                           by simpa [pcHolds] using hgb⟩)
                  exact False.elim (pcHolds_not_contra hg hproj)
                · exact evalBuiltin_DivideInteger_none_of_pair_not_ints (by
                    intro ib ia h
                    exact hshape ⟨ib, ia, h.1, h.2⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_DivideInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_QuotientInteger :
    BuiltinErrorSound .QuotientInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_QuotientInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_QuotientInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_QuotientInteger_eq bSym aSym] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases checked2_active_error hmem hactive with hinner | hproj
              · rcases hinner with ⟨inner, hinnerMem, hpArgs, hinnerActive⟩
                simp only [List.mem_cons, List.not_mem_nil] at hinnerMem
                rcases hinnerMem with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mp hpArgs
                    obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                    obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                    have hz : ib = 0 :=
                      pcHolds_not_ne_int_zero heb
                        (by simpa [outcomeErrorActive, divisionGuard] using hinnerActive)
                    exact evalBuiltin_QuotientInteger_none_of_divisor_zero (a := ia) (b := ib) hz
                  · cases hfalse
              · by_cases hshape :
                    ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                  have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                  have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                  have hg :
                      pcHolds m
                        (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                    simpa [pcHolds] using
                      ((Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mpr
                          ⟨by simpa [pcHolds] using hga,
                           by simpa [pcHolds] using hgb⟩)
                  exact False.elim (pcHolds_not_contra hg hproj)
                · exact evalBuiltin_QuotientInteger_none_of_pair_not_ints (by
                    intro ib ia h
                    exact hshape ⟨ib, ia, h.1, h.2⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_QuotientInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_RemainderInteger :
    BuiltinErrorSound .RemainderInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_RemainderInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_RemainderInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_RemainderInteger_eq bSym aSym] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases checked2_active_error hmem hactive with hinner | hproj
              · rcases hinner with ⟨inner, hinnerMem, hpArgs, hinnerActive⟩
                simp only [List.mem_cons, List.not_mem_nil] at hinnerMem
                rcases hinnerMem with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mp hpArgs
                    obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                    obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                    have hz : ib = 0 :=
                      pcHolds_not_ne_int_zero heb
                        (by simpa [outcomeErrorActive, divisionGuard] using hinnerActive)
                    exact evalBuiltin_RemainderInteger_none_of_divisor_zero (a := ia) (b := ib) hz
                  · cases hfalse
              · by_cases hshape :
                    ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                  have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                  have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                  have hg :
                      pcHolds m
                        (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                    simpa [pcHolds] using
                      ((Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mpr
                          ⟨by simpa [pcHolds] using hga,
                           by simpa [pcHolds] using hgb⟩)
                  exact False.elim (pcHolds_not_contra hg hproj)
                · exact evalBuiltin_RemainderInteger_none_of_pair_not_ints (by
                    intro ib ia h
                    exact hshape ⟨ib, ia, h.1, h.2⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_RemainderInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ModInteger :
    BuiltinErrorSound .ModInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ModInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ModInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_ModInteger_eq bSym aSym] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases checked2_active_error hmem hactive with hinner | hproj
              · rcases hinner with ⟨inner, hinnerMem, hpArgs, hinnerActive⟩
                simp only [List.mem_cons, List.not_mem_nil] at hinnerMem
                rcases hinnerMem with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mp hpArgs
                    obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                    obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                    have hz : ib = 0 :=
                      pcHolds_not_ne_int_zero heb
                        (by simpa [outcomeErrorActive, divisionGuard] using hinnerActive)
                    exact evalBuiltin_ModInteger_none_of_divisor_zero (a := ia) (b := ib) hz
                  · cases hfalse
              · by_cases hshape :
                    ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                  have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                  have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                  have hg :
                      pcHolds m
                        (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                    simpa [pcHolds] using
                      ((Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mpr
                          ⟨by simpa [pcHolds] using hga,
                           by simpa [pcHolds] using hgb⟩)
                  exact False.elim (pcHolds_not_contra hg hproj)
                · exact evalBuiltin_ModInteger_none_of_pair_not_ints (by
                    intro ib ia h
                    exact hshape ⟨ib, ia, h.1, h.2⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_ModInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_EqualsInteger :
    BuiltinErrorSound .EqualsInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_EqualsInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_EqualsInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsInteger_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt aSym).guard (asInt bSym).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.reflexiveEq (asInt aSym).val (asInt bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt aSym).guard (asInt bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                  · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                    have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                    have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt aSym).guard (asInt bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_EqualsInteger_none_of_pair_not_ints (by
                      intro ib ia h
                      exact hshape ⟨ib, ia, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_EqualsInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_LessThanInteger :
    BuiltinErrorSound .LessThanInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_LessThanInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_LessThanInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanInteger_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt aSym).guard (asInt bSym).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.lt (asInt aSym).val (asInt bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt aSym).guard (asInt bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                  · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                    have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                    have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt aSym).guard (asInt bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_LessThanInteger_none_of_pair_not_ints (by
                      intro ib ia h
                      exact hshape ⟨ib, ia, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_LessThanInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_LessThanEqualsInteger :
    BuiltinErrorSound .LessThanEqualsInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_LessThanEqualsInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_LessThanEqualsInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanEqualsInteger_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt aSym).guard (asInt bSym).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.le (asInt aSym).val (asInt bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt aSym).guard (asInt bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                  · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                    have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                    have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt aSym).guard (asInt bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_LessThanEqualsInteger_none_of_pair_not_ints (by
                      intro ib ia h
                      exact hshape ⟨ib, ia, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_LessThanEqualsInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_AppendByteString :
    BuiltinErrorSound .AppendByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_AppendByteString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_AppendByteString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_AppendByteString_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asBytes aSym).guard (asBytes bSym).guard)
                  (SymVal.const (SymConst.bytes
                    (SExpr.seqAppend (asBytes aSym).val (asBytes bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes aSym).guard (asBytes bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ bs2 bs1, cb = .VCon (.ByteString bs2) ∧
                        ca = .VCon (.ByteString bs1)
                  · rcases hshape with ⟨bs2, bs1, rfl, rfl⟩
                    have hga := asBytes_guard_of_cek (m := m) (v := aSym) (bs := bs1) ha
                    have hgb := asBytes_guard_of_cek (m := m) (v := bSym) (bs := bs2) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asBytes aSym).guard (asBytes bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asBytes aSym).guard (asBytes bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_AppendByteString_none_of_pair_not_bytes (by
                      intro bs2 bs1 h
                      exact hshape ⟨bs2, bs1, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_AppendByteString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ConsByteString :
    BuiltinErrorSound .ConsByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ConsByteString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bsSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ConsByteString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons nSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_ConsByteString_eq bsSym nSym] at hmem
              obtain ⟨cbs, cn, hbsArg, hnArg, rfl⟩ :=
                symValListToCekList_pair hargs
              have hpath := checked2_active_error hmem hactive
              rcases hpath with hinner | hproj
              · rcases hinner with ⟨inner, hinner, hpArgs, hinnerActive⟩
                change inner ∈
                  (let inByte := SExpr.and (SExpr.ge (asInt nSym).val (.int 0))
                    (SExpr.le (asInt nSym).val (.int 255))
                   [Outcome.ok inByte
                      (SymVal.const (SymConst.bytes
                        (SExpr.seqAppend (SExpr.seqUnit (asInt nSym).val)
                          (asBytes bsSym).val))),
                    Outcome.error (SExpr.not inByte)]) at hinner
                simp only [List.mem_cons, List.not_mem_nil] at hinner
                rcases hinner with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hnotRange :
                        pcHolds m
                          (SExpr.not
                            (SExpr.and (SExpr.ge (asInt nSym).val (.int 0))
                              (SExpr.le (asInt nSym).val (.int 255)))) = true := by
                      simpa [outcomeErrorActive] using hinnerActive
                    change pcHolds m
                      (SExpr.and (asInt nSym).guard (asBytes bsSym).guard) = true at hpArgs
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt nSym).guard (asBytes bsSym).guard).mp hpArgs
                    obtain ⟨n, rfl, hnEval⟩ := asInt_sound hnArg hp.1
                    obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbsArg hp.2
                    by_cases hbad : n < 0 ∨ 255 < n
                    · exact evalBuiltin_ConsByteString_none_of_byte_out_of_range hbad
                    · have hbad' := not_or.mp hbad
                      have hge : 0 ≤ n := (Int.not_lt).mp hbad'.1
                      have hle : n ≤ 255 := (Int.not_lt).mp hbad'.2
                      have hgePc : pcHolds m
                          (SExpr.ge (asInt nSym).val (.int 0)) = true :=
                        pcHolds_ge_int_intro hnEval
                          (by simp [Moist.SMT.Semantics.eval]) hge
                      have hlePc : pcHolds m
                          (SExpr.le (asInt nSym).val (.int 255)) = true :=
                        pcHolds_le_int_intro hnEval
                          (by simp [Moist.SMT.Semantics.eval]) hle
                      have hrange : pcHolds m
                          (SExpr.and (SExpr.ge (asInt nSym).val (.int 0))
                            (SExpr.le (asInt nSym).val (.int 255))) = true :=
                        pcHolds_and_intro hgePc hlePc
                      exact False.elim (pcHolds_not_contra hrange hnotRange)
                  · cases hfalse
              · by_cases hshape :
                  ∃ bs n, cbs = .VCon (.ByteString bs) ∧ cn = .VCon (.Integer n)
                · rcases hshape with ⟨bs, n, rfl, rfl⟩
                  have hgBs := asBytes_guard_of_cek (m := m)
                    (v := bsSym) (bs := bs) hbsArg
                  have hgN := asInt_guard_of_cek (m := m)
                    (v := nSym) (i := n) hnArg
                  have hprojGuard : pcHolds m
                      (SExpr.and (asInt nSym).guard (asBytes bsSym).guard) = true :=
                    pcHolds_and_intro hgN hgBs
                  exact False.elim (pcHolds_not_contra hprojGuard hproj)
                · exact evalBuiltin_ConsByteString_none_of_pair_not_byte_int
                    (bs := cbs) (n := cn) (by
                      intro bytes i h
                      exact hshape ⟨bytes, i, h⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_ConsByteString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_SliceByteString :
    BuiltinErrorSound .SliceByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_SliceByteString_none_of_length_ne_three (by
        intro h3
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bsSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_SliceByteString_none_of_length_ne_three (by
            intro h3
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons lenSym rest2 =>
          cases rest2 with
          | nil =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_SliceByteString_none_of_length_ne_three (by
                intro h3
                have htwo : cargs.length = 2 := by simpa using hlen
                omega)
          | cons startSym rest3 =>
              cases rest3 with
              | nil =>
                  rw [evalBuiltinSym_SliceByteString_eq bsSym lenSym startSym] at hmem
                  change out ∈
                    [Outcome.ok
                      (SExpr.all [(asInt startSym).guard, (asInt lenSym).guard,
                        (asBytes bsSym).guard])
                      (SymVal.const (SymConst.bytes
                        (SExpr.seqExtract (asBytes bsSym).val
                          (SExpr.ite (SExpr.lt (asInt startSym).val (.int 0))
                            (.int 0) (asInt startSym).val)
                          (SExpr.ite (SExpr.lt (asInt lenSym).val (.int 0))
                            (.int 0) (asInt lenSym).val)))),
                     Outcome.error (SExpr.not
                      (SExpr.all [(asInt startSym).guard, (asInt lenSym).guard,
                        (asBytes bsSym).guard]))] at hmem
                  simp only [List.mem_cons, List.not_mem_nil] at hmem
                  obtain ⟨cbs, clen, cstart, hbsArg, hlenArg, hstartArg, rfl⟩ :=
                    symValListToCekList_triple hargs
                  rcases hmem with hok | herr
                  · subst out
                    simp [outcomeErrorActive] at hactive
                  · rcases herr with herr | hfalse
                    · subst out
                      by_cases hshape :
                          ∃ bs len start,
                            cbs = .VCon (.ByteString bs) ∧
                            clen = .VCon (.Integer len) ∧
                            cstart = .VCon (.Integer start)
                      · rcases hshape with ⟨bs, len, start, rfl, rfl, rfl⟩
                        have hgStart := asInt_guard_of_cek (m := m)
                          (v := startSym) (i := start) hstartArg
                        have hgLen := asInt_guard_of_cek (m := m)
                          (v := lenSym) (i := len) hlenArg
                        have hgBs := asBytes_guard_of_cek (m := m)
                          (v := bsSym) (bs := bs) hbsArg
                        have hguard : pcHolds m
                            (SExpr.all [(asInt startSym).guard,
                              (asInt lenSym).guard, (asBytes bsSym).guard]) = true :=
                          pcHolds_all3_intro hgStart hgLen hgBs
                        exact False.elim (pcHolds_not_contra hguard hactive)
                      · exact evalBuiltin_SliceByteString_none_of_triple_not_byte_int_int
                          (bs := cbs) (len := clen) (start := cstart) (by
                            intro bytes len start h
                            exact hshape ⟨bytes, len, start, h⟩)
                    · cases hfalse
              | cons extra rest4 =>
                  have hlen := symValListToCekList_length hargs
                  exact evalBuiltin_SliceByteString_none_of_length_ne_three (by
                    intro h3
                    have hfour : 4 ≤ cargs.length := by
                      rw [hlen]
                      simp
                    omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_LengthOfByteString :
    BuiltinErrorSound .LengthOfByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_LengthOfByteString_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_LengthOfByteString_eq bsSym] at hmem
          change out ∈
            [Outcome.ok (asBytes bsSym).guard
              (SymVal.const (SymConst.integer (SExpr.seqLen (asBytes bsSym).val))),
             Outcome.error (SExpr.not (asBytes bsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ bs, cbs = .VCon (.ByteString bs)
              · rcases hshape with ⟨bs, rfl⟩
                have hg := asBytes_guard_of_cek (m := m) (v := bsSym) (bs := bs) hbs
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_LengthOfByteString_none_of_single_not_bytes (by
                  intro bs h
                  exact hshape ⟨bs, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_LengthOfByteString_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_IndexByteString :
    BuiltinErrorSound .IndexByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_IndexByteString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons idxSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_IndexByteString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons bsSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_IndexByteString_eq idxSym bsSym] at hmem
              obtain ⟨cidx, cbs, hidxArg, hbsArg, rfl⟩ :=
                symValListToCekList_pair hargs
              have hpath := checked2_active_error hmem hactive
              rcases hpath with hinner | hproj
              · rcases hinner with ⟨inner, hinner, hpArgs, hinnerActive⟩
                change inner ∈
                  (let inRange := SExpr.and (SExpr.ge (asInt idxSym).val (.int 0))
                    (SExpr.lt (asInt idxSym).val (SExpr.seqLen (asBytes bsSym).val))
                   [Outcome.ok inRange
                      (SymVal.const (SymConst.integer
                        (SExpr.seqNth (asBytes bsSym).val (asInt idxSym).val))),
                    Outcome.error (SExpr.not inRange)]) at hinner
                simp only [List.mem_cons, List.not_mem_nil] at hinner
                rcases hinner with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hnotRange :
                        pcHolds m
                          (SExpr.not
                            (SExpr.and (SExpr.ge (asInt idxSym).val (.int 0))
                              (SExpr.lt (asInt idxSym).val
                                (SExpr.seqLen (asBytes bsSym).val)))) = true := by
                      simpa [outcomeErrorActive] using hinnerActive
                    change pcHolds m
                      (SExpr.and (asBytes bsSym).guard (asInt idxSym).guard) = true at hpArgs
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asBytes bsSym).guard (asInt idxSym).guard).mp hpArgs
                    obtain ⟨idx, rfl, hidxEval⟩ := asInt_sound hidxArg hp.2
                    obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbsArg hp.1
                    by_cases hneg : idx < 0
                    · exact evalBuiltin_IndexByteString_none_of_negative hneg
                    · have hge : 0 ≤ idx := (Int.not_lt).mp hneg
                      by_cases hout : Int.ofNat bs.size ≤ idx
                      · exact evalBuiltin_IndexByteString_none_of_nonnegative_out_of_range
                          hge hout
                      · have hlt : idx < Int.ofNat bs.size := Int.not_le.mp hout
                        have hlenEval := Moist.SMT.Semantics.eval_seqLen_of
                          (m := m) (a := (asBytes bsSym).val) hbsEval
                        change SmtSem.eval m (SExpr.seqLen (asBytes bsSym).val) =
                          some (Moist.SMT.Semantics.SVal.int (Int.ofNat bs.size)) at hlenEval
                        have hgePc : pcHolds m
                            (SExpr.ge (asInt idxSym).val (.int 0)) = true :=
                          pcHolds_ge_int_intro hidxEval
                            (by simp [Moist.SMT.Semantics.eval]) hge
                        have hltPc : pcHolds m
                            (SExpr.lt (asInt idxSym).val
                              (SExpr.seqLen (asBytes bsSym).val)) = true :=
                          pcHolds_lt_int_intro hidxEval hlenEval hlt
                        have hrange : pcHolds m
                            (SExpr.and (SExpr.ge (asInt idxSym).val (.int 0))
                              (SExpr.lt (asInt idxSym).val
                                (SExpr.seqLen (asBytes bsSym).val))) = true :=
                          pcHolds_and_intro hgePc hltPc
                        exact False.elim (pcHolds_not_contra hrange hnotRange)
                  · cases hfalse
              · by_cases hshape :
                  ∃ idx bs, cidx = .VCon (.Integer idx) ∧
                    cbs = .VCon (.ByteString bs)
                · rcases hshape with ⟨idx, bs, rfl, rfl⟩
                  have hgBs := asBytes_guard_of_cek (m := m)
                    (v := bsSym) (bs := bs) hbsArg
                  have hgIdx := asInt_guard_of_cek (m := m)
                    (v := idxSym) (i := idx) hidxArg
                  have hprojGuard : pcHolds m
                      (SExpr.and (asBytes bsSym).guard (asInt idxSym).guard) = true :=
                    pcHolds_and_intro hgBs hgIdx
                  exact False.elim (pcHolds_not_contra hprojGuard hproj)
                · exact evalBuiltin_IndexByteString_none_of_pair_not_int_byte
                    (idx := cidx) (bs := cbs) (by
                      intro idx bs h
                      exact hshape ⟨idx, bs, h⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_IndexByteString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_EqualsByteString :
    BuiltinErrorSound .EqualsByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_EqualsByteString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_EqualsByteString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsByteString_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asBytes aSym).guard (asBytes bSym).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.reflexiveEq (asBytes aSym).val (asBytes bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes aSym).guard (asBytes bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ bs2 bs1, cb = .VCon (.ByteString bs2) ∧
                        ca = .VCon (.ByteString bs1)
                  · rcases hshape with ⟨bs2, bs1, rfl, rfl⟩
                    have hga := asBytes_guard_of_cek (m := m) (v := aSym) (bs := bs1) ha
                    have hgb := asBytes_guard_of_cek (m := m) (v := bSym) (bs := bs2) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asBytes aSym).guard (asBytes bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asBytes aSym).guard (asBytes bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_EqualsByteString_none_of_pair_not_bytes (by
                      intro bs2 bs1 h
                      exact hshape ⟨bs2, bs1, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_EqualsByteString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_LessThanByteString :
    BuiltinErrorSound .LessThanByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_LessThanByteString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_LessThanByteString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanByteString_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asBytes aSym).guard (asBytes bSym).guard)
                  (SymVal.const (SymConst.bool
                    (.app "bytes_lt" [(asBytes aSym).val, (asBytes bSym).val]))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes aSym).guard (asBytes bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ bs2 bs1, cb = .VCon (.ByteString bs2) ∧
                        ca = .VCon (.ByteString bs1)
                  · rcases hshape with ⟨bs2, bs1, rfl, rfl⟩
                    have hga := asBytes_guard_of_cek (m := m) (v := aSym) (bs := bs1) ha
                    have hgb := asBytes_guard_of_cek (m := m) (v := bSym) (bs := bs2) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asBytes aSym).guard (asBytes bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asBytes aSym).guard (asBytes bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_LessThanByteString_none_of_pair_not_bytes (by
                      intro bs2 bs1 h
                      exact hshape ⟨bs2, bs1, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_LessThanByteString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_LessThanEqualsByteString :
    BuiltinErrorSound .LessThanEqualsByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_LessThanEqualsByteString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_LessThanEqualsByteString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanEqualsByteString_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asBytes aSym).guard (asBytes bSym).guard)
                  (SymVal.const (SymConst.bool
                    (.app "bytes_le" [(asBytes aSym).val, (asBytes bSym).val]))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes aSym).guard (asBytes bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ bs2 bs1, cb = .VCon (.ByteString bs2) ∧
                        ca = .VCon (.ByteString bs1)
                  · rcases hshape with ⟨bs2, bs1, rfl, rfl⟩
                    have hga := asBytes_guard_of_cek (m := m) (v := aSym) (bs := bs1) ha
                    have hgb := asBytes_guard_of_cek (m := m) (v := bSym) (bs := bs2) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asBytes aSym).guard (asBytes bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asBytes aSym).guard (asBytes bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_LessThanEqualsByteString_none_of_pair_not_bytes (by
                      intro bs2 bs1 h
                      exact hshape ⟨bs2, bs1, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_LessThanEqualsByteString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_AppendString :
    BuiltinErrorSound .AppendString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_AppendString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_AppendString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_AppendString_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asString aSym).guard (asString bSym).guard)
                  (SymVal.const (SymConst.string
                    (SExpr.strAppend (asString aSym).val (asString bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asString aSym).guard (asString bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ sb sa, cb = .VCon (.String sb) ∧ ca = .VCon (.String sa)
                  · rcases hshape with ⟨sb, sa, rfl, rfl⟩
                    have hga := asString_guard_of_cek (m := m) (v := aSym) (s := sa) ha
                    have hgb := asString_guard_of_cek (m := m) (v := bSym) (s := sb) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asString aSym).guard (asString bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asString aSym).guard (asString bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_AppendString_none_of_pair_not_strings (by
                      intro sb sa h
                      exact hshape ⟨sb, sa, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_AppendString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_EqualsString :
    BuiltinErrorSound .EqualsString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_EqualsString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_EqualsString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsString_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asString aSym).guard (asString bSym).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.reflexiveEq (asString aSym).val (asString bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asString aSym).guard (asString bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ sb sa, cb = .VCon (.String sb) ∧ ca = .VCon (.String sa)
                  · rcases hshape with ⟨sb, sa, rfl, rfl⟩
                    have hga := asString_guard_of_cek (m := m) (v := aSym) (s := sa) ha
                    have hgb := asString_guard_of_cek (m := m) (v := bSym) (s := sb) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asString aSym).guard (asString bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asString aSym).guard (asString bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_EqualsString_none_of_pair_not_strings (by
                      intro sb sa h
                      exact hshape ⟨sb, sa, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_EqualsString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_EncodeUtf8 :
    BuiltinErrorSound .EncodeUtf8 := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_EncodeUtf8_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons sSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_EncodeUtf8_eq sSym] at hmem
          change out ∈
            [Outcome.ok (asString sSym).guard
              (SymVal.const (SymConst.bytes
                (.app "uplc_encodeUtf8" [(asString sSym).val]))),
             Outcome.error (SExpr.not (asString sSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cs, hs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ s, cs = .VCon (.String s)
              · rcases hshape with ⟨s, rfl⟩
                have hg := asString_guard_of_cek (m := m) (v := sSym) (s := s) hs
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_EncodeUtf8_none_of_single_not_string (by
                  intro s h
                  exact hshape ⟨s, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_EncodeUtf8_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_DecodeUtf8 :
    BuiltinErrorSound .DecodeUtf8 := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_DecodeUtf8_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_DecodeUtf8_eq bsSym] at hmem
          obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
          rcases checked2_active_error hmem hactive with hinner | hproj
          · rcases hinner with ⟨inner, hinnerMem, hguard, hinnerActive⟩
            simp only [List.mem_cons, List.not_mem_nil] at hinnerMem
            rcases hinnerMem with hok | herr
            · subst inner
              simp [outcomeErrorActive] at hinnerActive
            · rcases herr with herr | hfalse
              · subst inner
                by_cases hshape : ∃ bs, cbs = .VCon (.ByteString bs)
                · rcases hshape with ⟨bs, rfl⟩
                  obtain ⟨bs', hcv, hbsEval⟩ := asBytes_sound hbs hguard
                  cases hcv
                  have hfalseValid :
                      SmtSem.evalBoolIs m
                        (.app "valid_utf8" [(asBytes bsSym).val]) false = true :=
                    (Moist.SMT.Semantics.evalBoolIs_not_true m
                      (.app "valid_utf8" [(asBytes bsSym).val])).mp
                      (by simpa [outcomeErrorActive, pcHolds] using hinnerActive)
                  have hnotValid :=
                    Moist.SMT.Semantics.not_validUtf8_of_evalBoolIs_validUtf8_false
                      (m := m) (e := (asBytes bsSym).val) (bs := bs) hbsEval hfalseValid
                  exact evalBuiltin_DecodeUtf8_none_of_invalid hnotValid
                · exact evalBuiltin_DecodeUtf8_none_of_single_not_bytes (by
                    intro bs h
                    exact hshape ⟨bs, h⟩)
              · cases hfalse
          · by_cases hshape : ∃ bs, cbs = .VCon (.ByteString bs)
            · rcases hshape with ⟨bs, rfl⟩
              have hg := asBytes_guard_of_cek (m := m) (v := bsSym) (bs := bs) hbs
              exact False.elim (pcHolds_not_contra hg hproj)
            · exact evalBuiltin_DecodeUtf8_none_of_single_not_bytes (by
                intro bs h
                exact hshape ⟨bs, h⟩)
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_DecodeUtf8_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_IfThenElse :
    BuiltinErrorSound .IfThenElse := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_IfThenElse_none_of_length_ne_three (by
        intro h3
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons elseV rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_IfThenElse_none_of_length_ne_three (by
            intro h3
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons thenV rest2 =>
          cases rest2 with
          | nil =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_IfThenElse_none_of_length_ne_three (by
                intro h3
                have htwo : cargs.length = 2 := by simpa using hlen
                omega)
          | cons cond rest3 =>
              cases rest3 with
              | nil =>
                  rw [evalBuiltinSym_IfThenElse_eq elseV thenV cond] at hmem
                  change out ∈
                    [Outcome.ok (SExpr.and (asBool cond).guard (asBool cond).val) thenV,
                     Outcome.ok (SExpr.and (asBool cond).guard
                      (SExpr.not (asBool cond).val)) elseV,
                     Outcome.error (SExpr.not (asBool cond).guard)] at hmem
                  simp only [List.mem_cons, List.not_mem_nil] at hmem
                  obtain ⟨celse, cthen, ccond, helse, hthen, hcond, rfl⟩ :=
                    symValListToCekList_triple hargs
                  rcases hmem with hthenBranch | hrest
                  · subst out
                    simp [outcomeErrorActive] at hactive
                  · rcases hrest with helseBranch | herr
                    · subst out
                      simp [outcomeErrorActive] at hactive
                    · rcases herr with herr | hfalse
                      · subst out
                        by_cases hshape : ∃ b, ccond = .VCon (.Bool b)
                        · rcases hshape with ⟨b, rfl⟩
                          have hg := asBool_guard_of_cek (m := m) (v := cond) (b := b) hcond
                          exact False.elim (pcHolds_not_contra hg hactive)
                        · exact evalBuiltin_IfThenElse_none_of_cond_not_bool (by
                            intro b h
                            exact hshape ⟨b, h⟩)
                      · cases hfalse
              | cons extra rest4 =>
                  have hlen := symValListToCekList_length hargs
                  exact evalBuiltin_IfThenElse_none_of_length_ne_three (by
                    intro h3
                    have hfour : 4 ≤ cargs.length := by
                      rw [hlen]
                      simp
                    omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ChooseUnit :
    BuiltinErrorSound .ChooseUnit := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ChooseUnit_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons result rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ChooseUnit_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons unitV rest2 =>
          cases rest2 with
          | nil =>
              obtain ⟨cresult, cunit, hresult, hunit, rfl⟩ :=
                symValListToCekList_pair hargs
              cases unitV with
              | const c =>
                  cases c <;>
                    try
                      (change out ∈ err at hmem
                       simp [err] at hmem
                       subst out
                       exact evalBuiltin_ChooseUnit_none_of_unit_not_unit (by
                         intro hcu
                         subst cunit
                         have hc := symConstToCek_unit (by
                           simpa [symValToCek?] using hunit)
                         cases hc))
                  case unit =>
                    change out ∈ ok result at hmem
                    simp [ok] at hmem
                    rcases hmem with ⟨rfl, rfl⟩
                    simp [outcomeErrorActive] at hactive
              | dyn e =>
                  change out ∈
                    [Outcome.ok (SExpr.isCtor "VUnit" e) result,
                     Outcome.error (SExpr.not (SExpr.isCtor "VUnit" e))] at hmem
                  simp only [List.mem_cons, List.not_mem_nil] at hmem
                  rcases hmem with hok | herr
                  · subst out
                    simp [outcomeErrorActive] at hactive
                  · rcases herr with herr | hfalse
                    · subst out
                      by_cases hshape : cunit = .VCon .Unit
                      · subst cunit
                        have hg := unitGuard_complete (m := m) (u := SymVal.dyn e) hunit
                        exact False.elim (pcHolds_not_contra hg hactive)
                      · exact evalBuiltin_ChooseUnit_none_of_unit_not_unit hshape
                    · cases hfalse
              | pair a b =>
                  change out ∈ err at hmem
                  simp [err] at hmem
                  subst out
                  exact evalBuiltin_ChooseUnit_none_of_unit_not_unit (by
                    intro hcu
                    subst cunit
                    simp [symValToCek?] at hunit
                    cases ha : symValToCek? m a <;> simp [ha] at hunit
                    rename_i cva
                    cases hb : symValToCek? m b <;> simp [hb] at hunit
                    rename_i cvb
                    cases cva <;> cases cvb <;> simp at hunit)
              | constr tag fields =>
                  change out ∈ err at hmem
                  simp [err] at hmem
                  subst out
                  exact evalBuiltin_ChooseUnit_none_of_unit_not_unit (by
                    intro hcu
                    subst cunit
                    simp [symValToCek?] at hunit
                    cases htag : SmtSem.eval m tag <;> simp [htag] at hunit
                    rename_i sv
                    cases sv <;> simp [htag] at hunit
                    rename_i i
                    by_cases hneg : i < 0
                    · exact False.elim ((Int.not_le).mpr hneg hunit.1)
                    · cases hfields : symValListToCekList? m fields <;> simp [hfields] at hunit)
              | lam body ρ =>
                  change out ∈ err at hmem
                  simp [err] at hmem
                  subst out
                  exact evalBuiltin_ChooseUnit_none_of_unit_not_unit (by
                    intro hcu
                    subst cunit
                    simp [symValToCek?] at hunit
                    cases henv : symEnvToCek? m ρ <;> simp [henv] at hunit)
              | delay body ρ =>
                  change out ∈ err at hmem
                  simp [err] at hmem
                  subst out
                  exact evalBuiltin_ChooseUnit_none_of_unit_not_unit (by
                    intro hcu
                    subst cunit
                    simp [symValToCek?] at hunit
                    cases henv : symEnvToCek? m ρ <;> simp [henv] at hunit)
              | builtin b bargs ea =>
                  change out ∈ err at hmem
                  simp [err] at hmem
                  subst out
                  exact evalBuiltin_ChooseUnit_none_of_unit_not_unit (by
                    intro hcu
                    subst cunit
                    simp [symValToCek?] at hunit
                    cases hbargs : symValListToCekList? m bargs <;> simp [hbargs] at hunit)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_ChooseUnit_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_Trace :
    BuiltinErrorSound .Trace := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_Trace_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons result rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_Trace_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons msg rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_Trace_eq result msg] at hmem
              simp [checked2, ok, Outcome.guard] at hmem
              obtain ⟨cresult, cmsg, hresult, hmsg, rfl⟩ :=
                symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · subst out
                by_cases hshape : ∃ s, cmsg = .VCon (.String s)
                · rcases hshape with ⟨s, rfl⟩
                  have hg := asString_guard_of_cek (m := m) (v := msg) (s := s) hmsg
                  exact False.elim (pcHolds_not_contra hg hactive)
                · exact evalBuiltin_Trace_none_of_msg_not_string (by
                    intro s h
                    exact hshape ⟨s, h⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_Trace_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinConst_FstPair_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .FstPair cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_SndPair_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .SndPair cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

theorem evalBuiltin_FstPair_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .FstPair args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_FstPair_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_SndPair_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .SndPair args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_SndPair_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_FstPair_none_of_single_not_pair {cv : CekValue}
    (hp : ∀ a b, cv ≠ .VCon (.Pair (a, b)))
    (hpd : ∀ a b, cv ≠ .VCon (.PairData (a, b))) :
    Moist.CEK.evalBuiltin .FstPair [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Pair p =>
          cases p with
          | mk a b => exact False.elim (hp a b rfl)
      | PairData p =>
          cases p with
          | mk a b => exact False.elim (hpd a b rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_SndPair_none_of_single_not_pair {cv : CekValue}
    (hp : ∀ a b, cv ≠ .VCon (.Pair (a, b)))
    (hpd : ∀ a b, cv ≠ .VCon (.PairData (a, b))) :
    Moist.CEK.evalBuiltin .SndPair [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Pair p =>
          cases p with
          | mk a b => exact False.elim (hp a b rfl)
      | PairData p =>
          cases p with
          | mk a b => exact False.elim (hpd a b rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ChooseData_none (cs : List Const) :
    Moist.CEK.evalBuiltinConst .ChooseData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest => cases rest <;> cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_ChooseData_none_of_length_ne_six {args : List CekValue}
    (h : args.length ≠ 6) :
    Moist.CEK.evalBuiltin .ChooseData args = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .ChooseData args = none := by
    cases args with
    | nil => rfl
    | cons a r1 =>
        cases r1 with
        | nil => rfl
        | cons b r2 =>
            cases r2 with
            | nil => rfl
            | cons c r3 =>
                cases r3 with
                | nil => rfl
                | cons d r4 =>
                    cases r4 with
                    | nil => rfl
                    | cons e r5 =>
                        cases r5 with
                        | nil => rfl
                        | cons f r6 =>
                            cases r6 with
                            | nil => exact False.elim (h rfl)
                            | cons g r7 =>
                                simp [Moist.CEK.evalBuiltinPassThrough]
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts args with
  | none => simp
  | some cs =>
      have hnone := evalBuiltinConst_ChooseData_none cs
      simp [hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ChooseData_none_of_six_not_data
    {cb ci cl cm cc cd : CekValue}
    (h : ∀ d, cd ≠ .VCon (.Data d)) :
    Moist.CEK.evalBuiltin .ChooseData [cb, ci, cl, cm, cc, cd] = none := by
  have hpass :
      Moist.CEK.evalBuiltinPassThrough .ChooseData [cb, ci, cl, cm, cc, cd] =
        none := by
    cases cd with
    | VCon c =>
        cases c with
        | Data d => exact False.elim (h d rfl)
        | Integer i => rfl
        | ByteString bs => rfl
        | String s => rfl
        | Unit => rfl
        | Bool b => rfl
        | Pair p => rfl
        | PairData p => rfl
        | ConstList xs => rfl
        | ConstDataList xs => rfl
        | ConstPairDataList xs => rfl
        | ConstArray xs => rfl
        | Bls12_381_G1_element => rfl
        | Bls12_381_G2_element => rfl
        | Bls12_381_MlResult => rfl
    | VLam body ρ => rfl
    | VDelay body ρ => rfl
    | VConstr tag fields => rfl
    | VBuiltin b args expected => rfl
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts [cb, ci, cl, cm, cc, cd] with
  | none => simp
  | some cs =>
      have hnone := evalBuiltinConst_ChooseData_none cs
      simp [hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ChooseList_none (cs : List Const) :
    Moist.CEK.evalBuiltinConst .ChooseList cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest => cases rest <;> cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_ChooseList_none_of_length_ne_three {args : List CekValue}
    (h : args.length ≠ 3) :
    Moist.CEK.evalBuiltin .ChooseList args = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .ChooseList args = none := by
    cases args with
    | nil => rfl
    | cons a r1 =>
        cases r1 with
        | nil => rfl
        | cons b r2 =>
            cases r2 with
            | nil => rfl
            | cons c r3 =>
                cases r3 with
                | nil => exact False.elim (h rfl)
                | cons d r4 =>
                    simp [Moist.CEK.evalBuiltinPassThrough]
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts args with
  | none => simp
  | some cs =>
      have hnone := evalBuiltinConst_ChooseList_none cs
      simp [hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ChooseList_none_of_triple_not_list
    {consCase nilCase xs : CekValue}
    (hdl : ∀ ds, xs ≠ .VCon (.ConstDataList ds))
    (hvl : ∀ cs, xs ≠ .VCon (.ConstList cs)) :
    Moist.CEK.evalBuiltin .ChooseList [consCase, nilCase, xs] = none := by
  have hpass :
      Moist.CEK.evalBuiltinPassThrough .ChooseList [consCase, nilCase, xs] =
        none := by
    cases xs with
    | VCon c =>
        cases c with
        | ConstDataList ds => exact False.elim (hdl ds rfl)
        | ConstList cs => exact False.elim (hvl cs rfl)
        | Integer i => rfl
        | ByteString bs => rfl
        | String s => rfl
        | Unit => rfl
        | Bool b => rfl
        | Data d => rfl
        | Pair p => rfl
        | PairData p => rfl
        | ConstPairDataList xs => rfl
        | ConstArray xs => rfl
        | Bls12_381_G1_element => rfl
        | Bls12_381_G2_element => rfl
        | Bls12_381_MlResult => rfl
    | VLam body ρ => rfl
    | VDelay body ρ => rfl
    | VConstr tag fields => rfl
    | VBuiltin b args expected => rfl
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts [consCase, nilCase, xs] with
  | none => simp
  | some cs =>
      have hnone := evalBuiltinConst_ChooseList_none cs
      simp [hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_NullList_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .NullList cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest => cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_NullList_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .NullList args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro h1
        apply h
        omega
      have hnone := evalBuiltinConst_NullList_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_NullList_none_of_single_not_list {xs : CekValue}
    (hdl : ∀ ds, xs ≠ .VCon (.ConstDataList ds))
    (hvl : ∀ cs, xs ≠ .VCon (.ConstList cs)) :
    Moist.CEK.evalBuiltin .NullList [xs] = none := by
  cases xs with
  | VCon c =>
      cases c with
      | ConstDataList ds => exact False.elim (hdl ds rfl)
      | ConstList cs => exact False.elim (hvl cs rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_MkCons_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .MkCons cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> try rfl
              case ConstDataList ds =>
                cases c2 <;> cases c3 <;> cases rest3 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinPassThrough_MkCons_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltinPassThrough .MkCons args = none := by
  cases args with
  | nil => rfl
  | cons a r1 =>
      cases r1 with
      | nil =>
          cases a with
          | VCon c => cases c <;> rfl
          | VLam body ρ => rfl
          | VDelay body ρ => rfl
          | VConstr tag fields => rfl
          | VBuiltin b args expected => rfl
      | cons b r2 =>
          cases r2 with
          | nil => exact False.elim (h rfl)
          | cons c r3 =>
              simp [Moist.CEK.evalBuiltinPassThrough]

set_option maxHeartbeats 0 in
theorem evalBuiltin_MkCons_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .MkCons args = none := by
  have hpass := evalBuiltinPassThrough_MkCons_none_of_length_ne_two h
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts args with
  | none => simp
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro h2
        apply h
        omega
      have hnone := evalBuiltinConst_MkCons_none_of_length_ne_two hcs
      simp [hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_MkCons_none_of_pair_not_consable {tail head : CekValue}
    (hdata :
      ∀ ds d, ¬(tail = .VCon (.ConstDataList ds) ∧ head = .VCon (.Data d)))
    (hconst :
      ∀ cs c, ¬(tail = .VCon (.ConstList cs) ∧ head = .VCon c)) :
    Moist.CEK.evalBuiltin .MkCons [tail, head] = none := by
  cases tail with
  | VCon tc =>
      cases tc with
      | ConstDataList ds =>
          cases head with
          | VCon hc =>
              cases hc with
              | Data d => exact False.elim (hdata ds d ⟨rfl, rfl⟩)
              | Integer i => rfl
              | ByteString bs => rfl
              | String s => rfl
              | Unit => rfl
              | Bool b => rfl
              | Pair p => rfl
              | PairData p => rfl
              | ConstList xs => rfl
              | ConstDataList xs => rfl
              | ConstPairDataList xs => rfl
              | ConstArray xs => rfl
              | Bls12_381_G1_element => rfl
              | Bls12_381_G2_element => rfl
              | Bls12_381_MlResult => rfl
          | VLam body ρ => rfl
          | VDelay body ρ => rfl
          | VConstr tag fields => rfl
          | VBuiltin b args expected => rfl
      | ConstList cs =>
          cases head with
          | VCon hc => exact False.elim (hconst cs hc ⟨rfl, rfl⟩)
          | VLam body ρ => rfl
          | VDelay body ρ => rfl
          | VConstr tag fields => rfl
          | VBuiltin b args expected => rfl
      | Integer i => cases head <;> rfl
      | ByteString bs => cases head <;> rfl
      | String s => cases head <;> rfl
      | Unit => cases head <;> rfl
      | Bool b => cases head <;> rfl
      | Data d => cases head <;> rfl
      | Pair p => cases head <;> rfl
      | PairData p => cases head <;> rfl
      | ConstPairDataList xs => cases head <;> rfl
      | ConstArray xs => cases head <;> rfl
      | Bls12_381_G1_element => cases head <;> rfl
      | Bls12_381_G2_element => cases head <;> rfl
      | Bls12_381_MlResult => cases head <;> rfl
  | VLam body ρ => cases head <;> rfl
  | VDelay body ρ => cases head <;> rfl
  | VConstr tag fields => cases head <;> rfl
  | VBuiltin b args expected => cases head <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_HeadList_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .HeadList cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case ConstDataList ds =>
            cases ds <;> cases c2 <;> cases rest <;> rfl
          case ConstList xs =>
            cases xs <;> cases c2 <;> cases rest <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_TailList_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .TailList cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case ConstDataList ds =>
            cases ds <;> cases c2 <;> cases rest <;> rfl
          case ConstList xs =>
            cases xs <;> cases c2 <;> cases rest <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_HeadList_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .HeadList args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro h1
        apply h
        omega
      have hnone := evalBuiltinConst_HeadList_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_TailList_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .TailList args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro h1
        apply h
        omega
      have hnone := evalBuiltinConst_TailList_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_HeadList_none_of_single_not_nonempty_list {xs : CekValue}
    (hdl : ∀ d ds, xs ≠ .VCon (.ConstDataList (d :: ds)))
    (hvl : ∀ c cs, xs ≠ .VCon (.ConstList (c :: cs))) :
    Moist.CEK.evalBuiltin .HeadList [xs] = none := by
  cases xs with
  | VCon c =>
      cases c with
      | ConstDataList ds =>
          cases ds with
          | nil => rfl
          | cons d ds => exact False.elim (hdl d ds rfl)
      | ConstList cs =>
          cases cs with
          | nil => rfl
          | cons c cs => exact False.elim (hvl c cs rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_TailList_none_of_single_not_nonempty_list {xs : CekValue}
    (hdl : ∀ d ds, xs ≠ .VCon (.ConstDataList (d :: ds)))
    (hvl : ∀ c cs, xs ≠ .VCon (.ConstList (c :: cs))) :
    Moist.CEK.evalBuiltin .TailList [xs] = none := by
  cases xs with
  | VCon c =>
      cases c with
      | ConstDataList ds =>
          cases ds with
          | nil => rfl
          | cons d ds => exact False.elim (hdl d ds rfl)
      | ConstList cs =>
          cases cs with
          | nil => rfl
          | cons c cs => exact False.elim (hvl c cs rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem asDataList_nonempty_guard_of_cek {m : SmtSem.Model} {v : SymVal}
    {d : Moist.Plutus.Data} {ds : List Moist.Plutus.Data}
    (hv : symValToCek? m v = some (.VCon (.ConstDataList (d :: ds)))) :
    pcHolds m
      (SExpr.and (asDataList v).guard
        (SExpr.not (SExpr.isCtor "DNil" (asDataList v).val))) = true := by
  have hg := asDataList_guard_of_cek (m := m) (v := v) (xs := d :: ds) hv
  obtain ⟨xs, hcv, heval⟩ := asDataList_sound hv hg
  injection hcv with hconst
  injection hconst with hxs
  subst xs
  have hfalse := Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons heval
  have hnot :
      pcHolds m (SExpr.not (SExpr.isCtor "DNil" (asDataList v).val)) = true := by
    simpa [pcHolds] using
      (Moist.SMT.Semantics.evalBoolIs_not_true m
        (SExpr.isCtor "DNil" (asDataList v).val)).mpr hfalse
  exact pcHolds_and_intro hg hnot

set_option maxHeartbeats 0 in
theorem asConstList_nonempty_guard_of_cek {m : SmtSem.Model} {v : SymVal}
    {c : Const} {cs : List Const}
    (hv : symValToCek? m v = some (.VCon (.ConstList (c :: cs)))) :
    pcHolds m
      (SExpr.and (asConstList v).guard
        (SExpr.not (SExpr.isCtor "VNil" (asConstList v).val))) = true := by
  have hg := asConstList_guard_of_cek (m := m) (v := v) (cs := c :: cs) hv
  obtain ⟨vals, cs', hcv, heval, hconsts⟩ := asConstList_sound hv hg
  injection hcv with hconst
  injection hconst with hcsEq
  subst cs'
  cases vals with
  | nil =>
      simp [semValListToConstList?] at hconsts
  | cons vh vt =>
      have hfalse := Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons heval
      have hnot :
          pcHolds m (SExpr.not (SExpr.isCtor "VNil" (asConstList v).val)) = true := by
        simpa [pcHolds] using
          (Moist.SMT.Semantics.evalBoolIs_not_true m
            (SExpr.isCtor "VNil" (asConstList v).val)).mpr hfalse
      exact pcHolds_and_intro hg hnot

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_FstPair : BuiltinErrorSound .FstPair := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      exact evalBuiltin_FstPair_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by
          simpa using symValListToCekList_length hargs
        omega)
  | cons p rest =>
      cases rest with
      | nil =>
          change out ∈
            (let pp := asPair p
             let pd := asPairData p
             [Outcome.ok pp.guard pp.val.1,
              Outcome.ok pd.guard (.const (.data pd.val.1)),
              Outcome.error (SExpr.not (SExpr.or pp.guard pd.guard))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cp, hp, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hokPair | hokPairData | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              simp [outcomeErrorActive] at hactive
              by_cases hpCek : ∃ a b, cp = .VCon (.Pair (a, b))
              · rcases hpCek with ⟨a, b, rfl⟩
                have hg := asPair_guard_of_cek (m := m) (v := p) (a := a) (b := b) hp
                exact False.elim
                  (pcHolds_not_or_contra_left (m := m)
                    (a := (asPair p).guard) (b := (asPairData p).guard)
                    hg hactive)
              · by_cases hpdCek : ∃ a b, cp = .VCon (.PairData (a, b))
                · rcases hpdCek with ⟨a, b, rfl⟩
                  have hg := asPairData_guard_of_cek (m := m) (v := p) (a := a) (b := b) hp
                  exact False.elim
                    (pcHolds_not_or_contra_right (m := m)
                      (a := (asPair p).guard) (b := (asPairData p).guard)
                      hg hactive)
                · exact evalBuiltin_FstPair_none_of_single_not_pair
                    (cv := cp)
                    (by
                      intro a b h
                      exact hpCek ⟨a, b, h⟩)
                    (by
                      intro a b h
                      exact hpdCek ⟨a, b, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          exact evalBuiltin_FstPair_none_of_length_ne_one (by
            intro h1
            have hlen := symValListToCekList_length hargs
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_SndPair : BuiltinErrorSound .SndPair := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      exact evalBuiltin_SndPair_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by
          simpa using symValListToCekList_length hargs
        omega)
  | cons p rest =>
      cases rest with
      | nil =>
          change out ∈
            (let pp := asPair p
             let pd := asPairData p
             [Outcome.ok pp.guard pp.val.2,
              Outcome.ok pd.guard (.const (.data pd.val.2)),
              Outcome.error (SExpr.not (SExpr.or pp.guard pd.guard))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cp, hp, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hokPair | hokPairData | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              simp [outcomeErrorActive] at hactive
              by_cases hpCek : ∃ a b, cp = .VCon (.Pair (a, b))
              · rcases hpCek with ⟨a, b, rfl⟩
                have hg := asPair_guard_of_cek (m := m) (v := p) (a := a) (b := b) hp
                exact False.elim
                  (pcHolds_not_or_contra_left (m := m)
                    (a := (asPair p).guard) (b := (asPairData p).guard)
                    hg hactive)
              · by_cases hpdCek : ∃ a b, cp = .VCon (.PairData (a, b))
                · rcases hpdCek with ⟨a, b, rfl⟩
                  have hg := asPairData_guard_of_cek (m := m) (v := p) (a := a) (b := b) hp
                  exact False.elim
                    (pcHolds_not_or_contra_right (m := m)
                      (a := (asPair p).guard) (b := (asPairData p).guard)
                      hg hactive)
                · exact evalBuiltin_SndPair_none_of_single_not_pair
                    (cv := cp)
                    (by
                      intro a b h
                      exact hpCek ⟨a, b, h⟩)
                    (by
                      intro a b h
                      exact hpdCek ⟨a, b, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          exact evalBuiltin_SndPair_none_of_length_ne_one (by
            intro h1
            have hlen := symValListToCekList_length hargs
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ChooseList : BuiltinErrorSound .ChooseList := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ChooseList_none_of_length_ne_three (by
        intro h3
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons consCase rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ChooseList_none_of_length_ne_three (by
            intro h3
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons nilCase rest2 =>
          cases rest2 with
          | nil =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_ChooseList_none_of_length_ne_three (by
                intro h3
                have htwo : cargs.length = 2 := by simpa using hlen
                omega)
          | cons xs rest3 =>
              cases rest3 with
              | nil =>
                  change out ∈
                    (let dl := asDataList xs
                     let vl := asConstList xs
                     let dBranches :=
                       [Outcome.ok (SExpr.and dl.guard (SExpr.isCtor "DNil" dl.val))
                          nilCase,
                        Outcome.ok
                          (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                          consCase]
                     let nilOutcome :=
                       Outcome.ok (SExpr.and vl.guard (SExpr.isCtor "VNil" vl.val)) nilCase
                     let consOutcome :=
                       Outcome.ok
                         (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                         consCase
                     let vBranches :=
                       constListBranches (knownConstListLength xs) nilOutcome consOutcome
                     dBranches ++ vBranches ++
                       [Outcome.error (SExpr.not (SExpr.or dl.guard vl.guard))]) at hmem
                  have hmemFull : out ∈
                      (let dl := asDataList xs
                       let vl := asConstList xs
                       let dBranches :=
                         [Outcome.ok (SExpr.and dl.guard (SExpr.isCtor "DNil" dl.val))
                            nilCase,
                          Outcome.ok
                            (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                            consCase]
                       let vBranches :=
                         [Outcome.ok (SExpr.and vl.guard (SExpr.isCtor "VNil" vl.val))
                            nilCase,
                          Outcome.ok
                            (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                            consCase]
                       dBranches ++ vBranches ++
                         [Outcome.error (SExpr.not (SExpr.or dl.guard vl.guard))]) := by
                    let dl := asDataList xs
                    let vl := asConstList xs
                    let dBranches : List Outcome :=
                      [Outcome.ok (SExpr.and dl.guard (SExpr.isCtor "DNil" dl.val))
                         nilCase,
                       Outcome.ok
                         (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                         consCase]
                    let nilOutcome :=
                      Outcome.ok (SExpr.and vl.guard (SExpr.isCtor "VNil" vl.val)) nilCase
                    let consOutcome :=
                      Outcome.ok
                        (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                        consCase
                    let errorOutcome :=
                      Outcome.error (SExpr.not (SExpr.or dl.guard vl.guard))
                    change out ∈
                      dBranches ++
                        constListBranches (knownConstListLength xs)
                          nilOutcome consOutcome ++ [errorOutcome] at hmem
                    change out ∈ dBranches ++ [nilOutcome, consOutcome] ++ [errorOutcome]
                    have hs : List.Sublist
                        (dBranches ++
                          constListBranches (knownConstListLength xs)
                            nilOutcome consOutcome ++ [errorOutcome])
                        (dBranches ++ [nilOutcome, consOutcome] ++ [errorOutcome]) :=
                      (List.Sublist.refl dBranches).append
                        ((constListBranches_sublist _ _ _).append
                          (List.Sublist.refl [errorOutcome]))
                    exact hs.subset hmem
                  clear hmem
                  have hmem := hmemFull
                  simp only [List.mem_cons, List.not_mem_nil, List.mem_append] at hmem
                  obtain ⟨ccons, cnil, cxs, hcons, hnil, hxs, rfl⟩ :=
                    symValListToCekList_triple hargs
                  rcases hmem with hokBranches | herr
                  · rcases hokBranches with hd | hv
                    · rcases hd with hdNil | hdCons
                      · subst out
                        simp [outcomeErrorActive] at hactive
                      · rcases hdCons with hdCons | hfalse
                        · subst out
                          simp [outcomeErrorActive] at hactive
                        · cases hfalse
                    · rcases hv with hvNil | hvCons
                      · subst out
                        simp [outcomeErrorActive] at hactive
                      · rcases hvCons with hvCons | hfalse
                        · subst out
                          simp [outcomeErrorActive] at hactive
                        · cases hfalse
                  · rcases herr with herr | hfalse
                    · subst out
                      simp [outcomeErrorActive] at hactive
                      by_cases hdl : ∃ ds, cxs = .VCon (.ConstDataList ds)
                      · rcases hdl with ⟨ds, rfl⟩
                        have hg := asDataList_guard_of_cek
                          (m := m) (v := xs) (xs := ds) hxs
                        exact False.elim
                          (pcHolds_not_or_contra_left
                            (m := m) (a := (asDataList xs).guard)
                            (b := (asConstList xs).guard) hg hactive)
                      · by_cases hvl : ∃ cs, cxs = .VCon (.ConstList cs)
                        · rcases hvl with ⟨cs, rfl⟩
                          have hg := asConstList_guard_of_cek
                            (m := m) (v := xs) (cs := cs) hxs
                          exact False.elim
                            (pcHolds_not_or_contra_right
                              (m := m) (a := (asDataList xs).guard)
                              (b := (asConstList xs).guard) hg hactive)
                        · exact evalBuiltin_ChooseList_none_of_triple_not_list
                            (consCase := ccons) (nilCase := cnil) (xs := cxs)
                            (by
                              intro ds h
                              exact hdl ⟨ds, h⟩)
                            (by
                              intro cs h
                              exact hvl ⟨cs, h⟩)
                    · cases hfalse
              | cons extra rest4 =>
                  have hlen := symValListToCekList_length hargs
                  exact evalBuiltin_ChooseList_none_of_length_ne_three (by
                    intro h3
                    have hfour : 4 ≤ cargs.length := by
                      rw [hlen]
                      simp
                    omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_MkCons : BuiltinErrorSound .MkCons := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_MkCons_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons tail rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_MkCons_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons head rest2 =>
          cases rest2 with
          | nil =>
              change out ∈
                (let dl := asDataList tail
                 let hd := asData head
                 let vl := asConstList tail
                 let hv := asConstVal head
                 let dataOk := SExpr.and dl.guard hd.guard
                 let constOk := SExpr.and vl.guard hv.guard
                 [Outcome.ok dataOk (.const (.dataList (.app "DCons" [hd.val, dl.val]))),
                  Outcome.ok constOk (consConstListValue hv.val tail),
                  Outcome.error (SExpr.not (SExpr.or dataOk constOk))]) at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨ctail, chead, htail, hhead, rfl⟩ :=
                symValListToCekList_pair hargs
              rcases hmem with hokData | hokConst | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  simp [outcomeErrorActive] at hactive
                  by_cases hdataCek :
                      ∃ ds d,
                        ctail = .VCon (.ConstDataList ds) ∧
                          chead = .VCon (.Data d)
                  · rcases hdataCek with ⟨ds, d, rfl, rfl⟩
                    have hgtail := asDataList_guard_of_cek
                      (m := m) (v := tail) (xs := ds) htail
                    have hghead := asData_guard_of_cek
                      (m := m) (v := head) (d := d) hhead
                    have hg := pcHolds_and_intro hgtail hghead
                    exact False.elim
                      (pcHolds_not_or_contra_left
                        (m := m)
                        (a := SExpr.and (asDataList tail).guard (asData head).guard)
                        (b := SExpr.and (asConstList tail).guard (asConstVal head).guard)
                        hg hactive)
                  · by_cases hconstCek :
                      ∃ cs c,
                        ctail = .VCon (.ConstList cs) ∧ chead = .VCon c
                    · rcases hconstCek with ⟨cs, c, rfl, rfl⟩
                      have hgtail := asConstList_guard_of_cek
                        (m := m) (v := tail) (cs := cs) htail
                      have hghead := asConstVal_guard_of_cek
                        (m := m) (v := head) (c := c) hhead
                      have hg := pcHolds_and_intro hgtail hghead
                      exact False.elim
                        (pcHolds_not_or_contra_right
                          (m := m)
                          (a := SExpr.and (asDataList tail).guard (asData head).guard)
                          (b := SExpr.and (asConstList tail).guard (asConstVal head).guard)
                          hg hactive)
                    · exact evalBuiltin_MkCons_none_of_pair_not_consable
                        (tail := ctail) (head := chead)
                        (by
                          intro ds d h
                          exact hdataCek ⟨ds, d, h⟩)
                        (by
                          intro cs c h
                          exact hconstCek ⟨cs, c, h⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_MkCons_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_HeadList : BuiltinErrorSound .HeadList := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_HeadList_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons xs rest =>
      cases rest with
      | nil =>
          change out ∈
            (let dl := asDataList xs
             let vl := asConstList xs
             [Outcome.ok
                (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                (.const (.data (.app "dhead" [dl.val]))),
              Outcome.ok
                (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                (.dyn (.app "vhead" [vl.val])),
              Outcome.error (SExpr.not
                (SExpr.or
                  (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                  (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hokData | hokConst | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              simp [outcomeErrorActive] at hactive
              by_cases hdl :
                  ∃ d ds, cxs = .VCon (.ConstDataList (d :: ds))
              · rcases hdl with ⟨d, ds, rfl⟩
                have hg := asDataList_nonempty_guard_of_cek
                  (m := m) (v := xs) (d := d) (ds := ds) hxs
                exact False.elim
                  (pcHolds_not_or_contra_left
                    (m := m)
                    (a := SExpr.and (asDataList xs).guard
                      (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val)))
                    (b := SExpr.and (asConstList xs).guard
                      (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val)))
                    hg hactive)
              · by_cases hvl :
                  ∃ c cs, cxs = .VCon (.ConstList (c :: cs))
                · rcases hvl with ⟨c, cs, rfl⟩
                  have hg := asConstList_nonempty_guard_of_cek
                    (m := m) (v := xs) (c := c) (cs := cs) hxs
                  exact False.elim
                    (pcHolds_not_or_contra_right
                      (m := m)
                      (a := SExpr.and (asDataList xs).guard
                        (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val)))
                      (b := SExpr.and (asConstList xs).guard
                        (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val)))
                      hg hactive)
                · exact evalBuiltin_HeadList_none_of_single_not_nonempty_list
                    (xs := cxs)
                    (by
                      intro d ds h
                      exact hdl ⟨d, ds, h⟩)
                    (by
                      intro c cs h
                      exact hvl ⟨c, cs, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_HeadList_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_TailList : BuiltinErrorSound .TailList := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_TailList_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons xs rest =>
      cases rest with
      | nil =>
          change out ∈
            (let dl := asDataList xs
             let vl := asConstList xs
             [Outcome.ok
                (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                (.const (.dataList (.app "dtail" [dl.val]))),
              Outcome.ok
                (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                (tailConstListValue xs),
              Outcome.error (SExpr.not
                (SExpr.or
                  (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                  (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hokData | hokConst | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              simp [outcomeErrorActive] at hactive
              by_cases hdl :
                  ∃ d ds, cxs = .VCon (.ConstDataList (d :: ds))
              · rcases hdl with ⟨d, ds, rfl⟩
                have hg := asDataList_nonempty_guard_of_cek
                  (m := m) (v := xs) (d := d) (ds := ds) hxs
                exact False.elim
                  (pcHolds_not_or_contra_left
                    (m := m)
                    (a := SExpr.and (asDataList xs).guard
                      (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val)))
                    (b := SExpr.and (asConstList xs).guard
                      (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val)))
                    hg hactive)
              · by_cases hvl :
                  ∃ c cs, cxs = .VCon (.ConstList (c :: cs))
                · rcases hvl with ⟨c, cs, rfl⟩
                  have hg := asConstList_nonempty_guard_of_cek
                    (m := m) (v := xs) (c := c) (cs := cs) hxs
                  exact False.elim
                    (pcHolds_not_or_contra_right
                      (m := m)
                      (a := SExpr.and (asDataList xs).guard
                        (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val)))
                      (b := SExpr.and (asConstList xs).guard
                        (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val)))
                      hg hactive)
                · exact evalBuiltin_TailList_none_of_single_not_nonempty_list
                    (xs := cxs)
                    (by
                      intro d ds h
                      exact hdl ⟨d, ds, h⟩)
                    (by
                      intro c cs h
                      exact hvl ⟨c, cs, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_TailList_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_NullList : BuiltinErrorSound .NullList := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_NullList_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons xs rest =>
      cases rest with
      | nil =>
          change out ∈
            (let dl := asDataList xs
             let vl := asConstList xs
             [Outcome.ok dl.guard (.const (.bool (SExpr.isCtor "DNil" dl.val))),
              Outcome.ok vl.guard (.const (.bool (SExpr.isCtor "VNil" vl.val))),
              Outcome.error (SExpr.not (SExpr.or dl.guard vl.guard))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hd | hv | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              simp [outcomeErrorActive] at hactive
              by_cases hdl : ∃ ds, cxs = .VCon (.ConstDataList ds)
              · rcases hdl with ⟨ds, rfl⟩
                have hg := asDataList_guard_of_cek
                  (m := m) (v := xs) (xs := ds) hxs
                exact False.elim
                  (pcHolds_not_or_contra_left
                    (m := m) (a := (asDataList xs).guard)
                    (b := (asConstList xs).guard) hg hactive)
              · by_cases hvl : ∃ cs, cxs = .VCon (.ConstList cs)
                · rcases hvl with ⟨cs, rfl⟩
                  have hg := asConstList_guard_of_cek
                    (m := m) (v := xs) (cs := cs) hxs
                  exact False.elim
                    (pcHolds_not_or_contra_right
                      (m := m) (a := (asDataList xs).guard)
                      (b := (asConstList xs).guard) hg hactive)
                · exact evalBuiltin_NullList_none_of_single_not_list
                    (xs := cxs)
                    (by
                      intro ds h
                      exact hdl ⟨ds, h⟩)
                    (by
                      intro cs h
                      exact hvl ⟨cs, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_NullList_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ChooseData : BuiltinErrorSound .ChooseData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ChooseData_none_of_length_ne_six (by
        intro h6
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bCase rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ChooseData_none_of_length_ne_six (by
            intro h6
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons iCase rest2 =>
          cases rest2 with
          | nil =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_ChooseData_none_of_length_ne_six (by
                intro h6
                have htwo : cargs.length = 2 := by simpa using hlen
                omega)
          | cons listCase rest3 =>
              cases rest3 with
              | nil =>
                  have hlen := symValListToCekList_length hargs
                  exact evalBuiltin_ChooseData_none_of_length_ne_six (by
                    intro h6
                    have hthree : cargs.length = 3 := by simpa using hlen
                    omega)
              | cons mapCase rest4 =>
                  cases rest4 with
                  | nil =>
                      have hlen := symValListToCekList_length hargs
                      exact evalBuiltin_ChooseData_none_of_length_ne_six (by
                        intro h6
                        have hfour : cargs.length = 4 := by simpa using hlen
                        omega)
                  | cons constrCase rest5 =>
                      cases rest5 with
                      | nil =>
                          have hlen := symValListToCekList_length hargs
                          exact evalBuiltin_ChooseData_none_of_length_ne_six (by
                            intro h6
                            have hfive : cargs.length = 5 := by simpa using hlen
                            omega)
                      | cons dVal rest6 =>
                          cases rest6 with
                          | nil =>
                              change out ∈
                                (let d := asData dVal
                                 [Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DConstr" d.val))
                                    constrCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DMap" d.val))
                                    mapCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DList" d.val))
                                    listCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DI" d.val))
                                    iCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DB" d.val))
                                    bCase,
                                  Outcome.error (SExpr.not d.guard)]) at hmem
                              simp only [List.mem_cons, List.not_mem_nil] at hmem
                              obtain ⟨cb, ci, cl, cm, cc, cd, hb, hi, hl, hm, hc, hd,
                                  rfl⟩ :=
                                symValListToCekList_six hargs
                              rcases hmem with hConstr | rest
                              · subst out
                                simp [outcomeErrorActive] at hactive
                              · rcases rest with hMap | rest
                                · subst out
                                  simp [outcomeErrorActive] at hactive
                                · rcases rest with hList | rest
                                  · subst out
                                    simp [outcomeErrorActive] at hactive
                                  · rcases rest with hI | rest
                                    · subst out
                                      simp [outcomeErrorActive] at hactive
                                    · rcases rest with hB | herr
                                      · subst out
                                        simp [outcomeErrorActive] at hactive
                                      · rcases herr with herr | hfalse
                                        · subst out
                                          simp [outcomeErrorActive] at hactive
                                          by_cases hdata : ∃ d, cd = .VCon (.Data d)
                                          · rcases hdata with ⟨d, rfl⟩
                                            have hg := asData_guard_of_cek
                                              (m := m) (v := dVal) (d := d) hd
                                            exact False.elim
                                              (pcHolds_not_contra hg hactive)
                                          · exact
                                              evalBuiltin_ChooseData_none_of_six_not_data
                                                (cb := cb) (ci := ci) (cl := cl)
                                                (cm := cm) (cc := cc) (cd := cd)
                                                (by
                                                  intro d hcd
                                                  exact hdata ⟨d, hcd⟩)
                                        · cases hfalse
                          | cons extra rest7 =>
                              have hlen := symValListToCekList_length hargs
                              exact evalBuiltin_ChooseData_none_of_length_ne_six (by
                                intro h6
                                have hseven : 7 ≤ cargs.length := by
                                  rw [hlen]
                                  simp
                                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ConstrData :
    BuiltinErrorSound .ConstrData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ConstrData_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons fieldsSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ConstrData_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons tagSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_ConstrData_eq fieldsSym tagSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt tagSym).guard (asDataList fieldsSym).guard)
                  (SymVal.const (SymConst.data
                    (.app "DConstr" [(asInt tagSym).val, (asDataList fieldsSym).val]))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt tagSym).guard (asDataList fieldsSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cfields, ctag, hfields, htag, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ds i,
                        cfields = .VCon (.ConstDataList ds) ∧
                          ctag = .VCon (.Integer i)
                  · rcases hshape with ⟨ds, i, rfl, rfl⟩
                    have hgf :=
                      asDataList_guard_of_cek (m := m) (v := fieldsSym) (xs := ds) hfields
                    have hgt := asInt_guard_of_cek (m := m) (v := tagSym) (i := i) htag
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt tagSym).guard (asDataList fieldsSym).guard) =
                            true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt tagSym).guard (asDataList fieldsSym).guard).mpr
                            ⟨by simpa [pcHolds] using hgt,
                             by simpa [pcHolds] using hgf⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_ConstrData_none_of_pair_not_supported (by
                      intro ds i h
                      exact hshape ⟨ds, i, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_ConstrData_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_MapData :
    BuiltinErrorSound .MapData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_MapData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons psSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_MapData_eq psSym] at hmem
          change out ∈
            [Outcome.ok (asPairDataList psSym).guard
              (SymVal.const (SymConst.data (.app "DMap" [(asPairDataList psSym).val]))),
             Outcome.error (SExpr.not (asPairDataList psSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cps, hps, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ ps, cps = .VCon (.ConstPairDataList ps)
              · rcases hshape with ⟨ps, rfl⟩
                have hg :=
                  asPairDataList_guard_of_cek (m := m) (v := psSym) (xs := ps) hps
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_MapData_none_of_single_not_pair_data_list (by
                  intro ps h
                  exact hshape ⟨ps, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_MapData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ListData :
    BuiltinErrorSound .ListData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ListData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons xsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_ListData_eq xsSym] at hmem
          change out ∈
            [Outcome.ok (asDataList xsSym).guard
              (SymVal.const (SymConst.data (.app "DList" [(asDataList xsSym).val]))),
             Outcome.error (SExpr.not (asDataList xsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ ds, cxs = .VCon (.ConstDataList ds)
              · rcases hshape with ⟨ds, rfl⟩
                have hg :=
                  asDataList_guard_of_cek (m := m) (v := xsSym) (xs := ds) hxs
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_ListData_none_of_single_not_data_list (by
                  intro ds h
                  exact hshape ⟨ds, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ListData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_IData :
    BuiltinErrorSound .IData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_IData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons iSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_IData_eq iSym] at hmem
          change out ∈
            [Outcome.ok (asInt iSym).guard
              (SymVal.const (SymConst.data (.app "DI" [(asInt iSym).val]))),
             Outcome.error (SExpr.not (asInt iSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨ci, hi, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ i, ci = .VCon (.Integer i)
              · rcases hshape with ⟨i, rfl⟩
                have hg := asInt_guard_of_cek (m := m) (v := iSym) (i := i) hi
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_IData_none_of_single_not_int (by
                  intro i h
                  exact hshape ⟨i, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_IData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_BData :
    BuiltinErrorSound .BData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_BData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_BData_eq bsSym] at hmem
          change out ∈
            [Outcome.ok (asBytes bsSym).guard
              (SymVal.const (SymConst.data (.app "DB" [(asBytes bsSym).val]))),
             Outcome.error (SExpr.not (asBytes bsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ bs, cbs = .VCon (.ByteString bs)
              · rcases hshape with ⟨bs, rfl⟩
                have hg := asBytes_guard_of_cek (m := m) (v := bsSym) (bs := bs) hbs
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_BData_none_of_single_not_bytes (by
                  intro bs h
                  exact hshape ⟨bs, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_BData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_UnConstrData :
    BuiltinErrorSound .UnConstrData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_UnConstrData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnConstrData_eq dVal] at hmem
          obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
          have hpath := checked2_active_error hmem hactive
          rcases hpath with hinner | hproj
          · rcases hinner with ⟨inner, hinner, hpData, hinnerActive⟩
            change inner ∈
              (let is := SExpr.isCtor "DConstr" (asData dVal).val
               [Outcome.ok is
                  (SymVal.const (SymConst.pairData
                    (.app "DI" [.app "dataConstrTag" [(asData dVal).val]])
                    (.app "DList" [.app "dataConstrFields" [(asData dVal).val]]))),
                Outcome.error (SExpr.not is)]) at hinner
            simp only [List.mem_cons, List.not_mem_nil] at hinner
            rcases hinner with hok | herr
            · subst inner
              simp [outcomeErrorActive] at hinnerActive
            · rcases herr with herr | hfalse
              · subst inner
                by_cases hshape :
                    ∃ tag fields, cd = .VCon (.Data (.Constr tag fields))
                · rcases hshape with ⟨tag, fields, rfl⟩
                  obtain ⟨d, hdCd, hdEval⟩ := asData_sound hd hpData
                  injection hdCd with hdEq
                  injection hdEq with hdDataEq
                  subst d
                  have his := pcHolds_isDConstr_intro (m := m)
                    (e := (asData dVal).val) (tag := tag) (fields := fields) hdEval
                  exact False.elim (pcHolds_not_contra his hinnerActive)
                · exact evalBuiltin_UnConstrData_none_of_single_not_constr (cv := cd) (by
                    intro tag fields h
                    exact hshape ⟨tag, fields, h⟩)
              · cases hfalse
          · by_cases hshape :
              ∃ tag fields, cd = .VCon (.Data (.Constr tag fields))
            · rcases hshape with ⟨tag, fields, rfl⟩
              have hg := asData_guard_of_cek (m := m) (v := dVal)
                (d := .Constr tag fields) hd
              exact False.elim (pcHolds_not_contra hg hproj)
            · exact evalBuiltin_UnConstrData_none_of_single_not_constr (cv := cd) (by
                intro tag fields h
                exact hshape ⟨tag, fields, h⟩)
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_UnConstrData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_UnMapData :
    BuiltinErrorSound .UnMapData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_UnMapData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnMapData_eq dVal] at hmem
          obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
          have hpath := checked2_active_error hmem hactive
          rcases hpath with hinner | hproj
          · rcases hinner with ⟨inner, hinner, hpData, hinnerActive⟩
            change inner ∈
              (let is := SExpr.isCtor "DMap" (asData dVal).val
               [Outcome.ok is
                  (SymVal.const (SymConst.pairDataList
                    (.app "dataMapEntries" [(asData dVal).val]))),
                Outcome.error (SExpr.not is)]) at hinner
            simp only [List.mem_cons, List.not_mem_nil] at hinner
            rcases hinner with hok | herr
            · subst inner
              simp [outcomeErrorActive] at hinnerActive
            · rcases herr with herr | hfalse
              · subst inner
                by_cases hshape : ∃ ps, cd = .VCon (.Data (.Map ps))
                · rcases hshape with ⟨ps, rfl⟩
                  obtain ⟨d, hdCd, hdEval⟩ := asData_sound hd hpData
                  injection hdCd with hdEq
                  injection hdEq with hdDataEq
                  subst d
                  have his := pcHolds_isDMap_intro (m := m)
                    (e := (asData dVal).val) (ps := ps) hdEval
                  exact False.elim (pcHolds_not_contra his hinnerActive)
                · exact evalBuiltin_UnMapData_none_of_single_not_map (cv := cd) (by
                    intro ps h
                    exact hshape ⟨ps, h⟩)
              · cases hfalse
          · by_cases hshape : ∃ ps, cd = .VCon (.Data (.Map ps))
            · rcases hshape with ⟨ps, rfl⟩
              have hg := asData_guard_of_cek (m := m) (v := dVal)
                (d := .Map ps) hd
              exact False.elim (pcHolds_not_contra hg hproj)
            · exact evalBuiltin_UnMapData_none_of_single_not_map (cv := cd) (by
                intro ps h
                exact hshape ⟨ps, h⟩)
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_UnMapData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_UnListData :
    BuiltinErrorSound .UnListData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_UnListData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnListData_eq dVal] at hmem
          obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
          have hpath := checked2_active_error hmem hactive
          rcases hpath with hinner | hproj
          · rcases hinner with ⟨inner, hinner, hpData, hinnerActive⟩
            change inner ∈
              (let is := SExpr.isCtor "DList" (asData dVal).val
               [Outcome.ok is
                  (SymVal.const (SymConst.dataList
                    (.app "dataListItems" [(asData dVal).val]))),
                Outcome.error (SExpr.not is)]) at hinner
            simp only [List.mem_cons, List.not_mem_nil] at hinner
            rcases hinner with hok | herr
            · subst inner
              simp [outcomeErrorActive] at hinnerActive
            · rcases herr with herr | hfalse
              · subst inner
                by_cases hshape : ∃ xs, cd = .VCon (.Data (.List xs))
                · rcases hshape with ⟨xs, rfl⟩
                  obtain ⟨d, hdCd, hdEval⟩ := asData_sound hd hpData
                  injection hdCd with hdEq
                  injection hdEq with hdDataEq
                  subst d
                  have his := pcHolds_isDList_intro (m := m)
                    (e := (asData dVal).val) (xs := xs) hdEval
                  exact False.elim (pcHolds_not_contra his hinnerActive)
                · exact evalBuiltin_UnListData_none_of_single_not_list (cv := cd) (by
                    intro xs h
                    exact hshape ⟨xs, h⟩)
              · cases hfalse
          · by_cases hshape : ∃ xs, cd = .VCon (.Data (.List xs))
            · rcases hshape with ⟨xs, rfl⟩
              have hg := asData_guard_of_cek (m := m) (v := dVal)
                (d := .List xs) hd
              exact False.elim (pcHolds_not_contra hg hproj)
            · exact evalBuiltin_UnListData_none_of_single_not_list (cv := cd) (by
                intro xs h
                exact hshape ⟨xs, h⟩)
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_UnListData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_UnIData :
    BuiltinErrorSound .UnIData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_UnIData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnIData_eq dVal] at hmem
          obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
          have hpath := checked2_active_error hmem hactive
          rcases hpath with hinner | hproj
          · rcases hinner with ⟨inner, hinner, hpData, hinnerActive⟩
            change inner ∈
              (let is := SExpr.isCtor "DI" (asData dVal).val
               [Outcome.ok is
                  (SymVal.const (SymConst.integer
                    (.app "dataInt" [(asData dVal).val]))),
                Outcome.error (SExpr.not is)]) at hinner
            simp only [List.mem_cons, List.not_mem_nil] at hinner
            rcases hinner with hok | herr
            · subst inner
              simp [outcomeErrorActive] at hinnerActive
            · rcases herr with herr | hfalse
              · subst inner
                by_cases hshape : ∃ i, cd = .VCon (.Data (.I i))
                · rcases hshape with ⟨i, rfl⟩
                  obtain ⟨d, hdCd, hdEval⟩ := asData_sound hd hpData
                  injection hdCd with hdEq
                  injection hdEq with hdDataEq
                  subst d
                  have his := pcHolds_isDI_intro (m := m)
                    (e := (asData dVal).val) (i := i) hdEval
                  exact False.elim (pcHolds_not_contra his hinnerActive)
                · exact evalBuiltin_UnIData_none_of_single_not_i (cv := cd) (by
                    intro i h
                    exact hshape ⟨i, h⟩)
              · cases hfalse
          · by_cases hshape : ∃ i, cd = .VCon (.Data (.I i))
            · rcases hshape with ⟨i, rfl⟩
              have hg := asData_guard_of_cek (m := m) (v := dVal)
                (d := .I i) hd
              exact False.elim (pcHolds_not_contra hg hproj)
            · exact evalBuiltin_UnIData_none_of_single_not_i (cv := cd) (by
                intro i h
                exact hshape ⟨i, h⟩)
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_UnIData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_UnBData :
    BuiltinErrorSound .UnBData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_UnBData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnBData_eq dVal] at hmem
          obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
          have hpath := checked2_active_error hmem hactive
          rcases hpath with hinner | hproj
          · rcases hinner with ⟨inner, hinner, hpData, hinnerActive⟩
            change inner ∈
              (let is := SExpr.isCtor "DB" (asData dVal).val
               [Outcome.ok is
                  (SymVal.const (SymConst.bytes
                    (.app "dataBytes" [(asData dVal).val]))),
                Outcome.error (SExpr.not is)]) at hinner
            simp only [List.mem_cons, List.not_mem_nil] at hinner
            rcases hinner with hok | herr
            · subst inner
              simp [outcomeErrorActive] at hinnerActive
            · rcases herr with herr | hfalse
              · subst inner
                by_cases hshape : ∃ bs, cd = .VCon (.Data (.B bs))
                · rcases hshape with ⟨bs, rfl⟩
                  obtain ⟨d, hdCd, hdEval⟩ := asData_sound hd hpData
                  injection hdCd with hdEq
                  injection hdEq with hdDataEq
                  subst d
                  have his := pcHolds_isDB_intro (m := m)
                    (e := (asData dVal).val) (bs := bs) hdEval
                  exact False.elim (pcHolds_not_contra his hinnerActive)
                · exact evalBuiltin_UnBData_none_of_single_not_b (cv := cd) (by
                    intro bs h
                    exact hshape ⟨bs, h⟩)
              · cases hfalse
          · by_cases hshape : ∃ bs, cd = .VCon (.Data (.B bs))
            · rcases hshape with ⟨bs, rfl⟩
              have hg := asData_guard_of_cek (m := m) (v := dVal)
                (d := .B bs) hd
              exact False.elim (pcHolds_not_contra hg hproj)
            · exact evalBuiltin_UnBData_none_of_single_not_b (cv := cd) (by
                intro bs h
                exact hshape ⟨bs, h⟩)
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_UnBData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_EqualsData :
    BuiltinErrorSound .EqualsData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_EqualsData_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_EqualsData_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsData_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asData aSym).guard (asData bSym).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.reflexiveEq (asData aSym).val (asData bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asData aSym).guard (asData bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ db da, cb = .VCon (.Data db) ∧ ca = .VCon (.Data da)
                  · rcases hshape with ⟨db, da, rfl, rfl⟩
                    have hga := asData_guard_of_cek (m := m) (v := aSym) (d := da) ha
                    have hgb := asData_guard_of_cek (m := m) (v := bSym) (d := db) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asData aSym).guard (asData bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asData aSym).guard (asData bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_EqualsData_none_of_pair_not_data (by
                      intro db da h
                      exact hshape ⟨db, da, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_EqualsData_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_MkPairData :
    BuiltinErrorSound .MkPairData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_MkPairData_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_MkPairData_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_MkPairData_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asData aSym).guard (asData bSym).guard)
                  (SymVal.const (SymConst.pairData (asData aSym).val (asData bSym).val)),
                 Outcome.error (SExpr.not
                  (SExpr.and (asData aSym).guard (asData bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ db da, cb = .VCon (.Data db) ∧ ca = .VCon (.Data da)
                  · rcases hshape with ⟨db, da, rfl, rfl⟩
                    have hga := asData_guard_of_cek (m := m) (v := aSym) (d := da) ha
                    have hgb := asData_guard_of_cek (m := m) (v := bSym) (d := db) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asData aSym).guard (asData bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asData aSym).guard (asData bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_MkPairData_none_of_pair_not_data (by
                      intro db da h
                      exact hshape ⟨db, da, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_MkPairData_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_MkNilData :
    BuiltinErrorSound .MkNilData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_MkNilData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons u rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_MkNilData_eq u] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cu, hu, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hunit : cu = .VCon .Unit
              · subst cu
                have hg := unitGuard_complete (m := m) (u := u) hu
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_MkNilData_none_of_single_not_unit hunit
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_MkNilData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_MkNilPairData :
    BuiltinErrorSound .MkNilPairData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_MkNilPairData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons u rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_MkNilPairData_eq u] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cu, hu, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hunit : cu = .VCon .Unit
              · subst cu
                have hg := unitGuard_complete (m := m) (u := u) hu
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_MkNilPairData_none_of_single_not_unit hunit
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_MkNilPairData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
theorem evalBuiltinSym_active_error_IntegerToByteString :
    BuiltinErrorSound .IntegerToByteString :=
  ternaryCheckedGuardedBuiltinError .IntegerToByteString
    (fun n width endian => Proj.map3
      (fun endian width n => (endian, width, n))
      (asBool endian) (asInt width) (asInt n))
    (fun (endian, width, n) =>
      .app "uplc_integerToByteString_defined" [endian, width, n])
    (fun (endian, width, n) => .const (.bytes
      (.app "uplc_integerToByteString" [endian, width, n])))
    (by intro n width endian; rfl)
    (by
      intro args hlen
      cases args with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b tail =>
              cases tail with
              | nil => rfl
              | cons c tail' =>
                  cases tail' with
                  | nil => exact (hlen rfl).elim
                  | cons d tail'' => rfl)
    (by
      intro cargs hlen
      exact evalBuiltin_advanced_ternary_none_of_length .IntegerToByteString
        (Or.inl rfl) hlen)
    (by
      intro m nSym widthSym endianSym cn cwidth cendian cv
        hn hwidth hendian hcek
      obtain ⟨n, width, endian, rfl, rfl, rfl⟩ :=
        evalBuiltin_IntegerToByteString_some_shape hcek
      exact pcHolds_all3_intro (asBool_guard_of_cek hendian)
        (asInt_guard_of_cek hwidth) (asInt_guard_of_cek hn))
    (by
      intro m nSym widthSym endianSym cn cwidth cendian cv
        hn hwidth hendian hcek
      obtain ⟨n, width, endian, rfl, rfl, rfl⟩ :=
        evalBuiltin_IntegerToByteString_some_shape hcek
      have gn := asInt_guard_of_cek hn
      have gw := asInt_guard_of_cek hwidth
      have ge := asBool_guard_of_cek hendian
      obtain ⟨n', hnEq, hnEval⟩ := asInt_sound hn gn
      obtain ⟨width', hwEq, hwidthEval⟩ := asInt_sound hwidth gw
      obtain ⟨endian', heEq, hendianEval⟩ := asBool_sound hendian ge
      injection hnEq with hnConst
      injection hnConst with hnSub
      injection hwEq with hwConst
      injection hwConst with hwSub
      injection heEq with heConst
      injection heConst with heSub
      subst n'
      subst width'
      subst endian'
      obtain ⟨c, hconst⟩ := evalBuiltinConst_some_of_evalBuiltin_vcons
        (b := .IntegerToByteString)
        (cs := [.Integer n, .Integer width, .Bool endian]) (by rfl) hcek
      exact pcHolds_defined_of_const_success
        (Moist.SMT.Semantics.eval_uplcIntegerToByteStringDefined_of
          hendianEval hwidthEval hnEval) hconst)
theorem evalBuiltinSym_active_error_ByteStringToInteger :
    BuiltinErrorSound .ByteStringToInteger :=
  binaryCheckedConstBuiltinError .ByteStringToInteger
    (fun bs endian => Proj.map2
      (fun endian bs => .app "uplc_byteStringToInteger" [endian, bs])
      (asBool endian) (asBytes bs)) .integer
    (by intro bs endian; rfl)
    (by
      intro args hlen
      cases args with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b tail =>
              cases tail with
              | nil => exact (hlen rfl).elim
              | cons c tail' => rfl)
    (by
      intro cargs hlen
      exact evalBuiltin_advanced_binary_none_of_length .ByteStringToInteger
        (Or.inl rfl) hlen)
    (by
      intro m bsSym endianSym cbs cendian cv hbs hendian hcek
      obtain ⟨bs, endian, rfl, rfl⟩ :=
        evalBuiltin_ByteStringToInteger_some_shape hcek
      exact pcHolds_and_intro
        (asBool_guard_of_cek hendian) (asBytes_guard_of_cek hbs))

theorem evalBuiltinSym_active_error_AndByteString :
    BuiltinErrorSound .AndByteString :=
  ternaryCheckedConstBuiltinError .AndByteString
    (fun b a pad => Proj.map3
      (fun pad a b => .app "uplc_andByteString" [pad, a, b])
      (asBool pad) (asBytes a) (asBytes b)) .bytes
    (by intro b a pad; rfl)
    (by
      intro args hlen
      cases args with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b tail =>
              cases tail with
              | nil => rfl
              | cons c tail' =>
                  cases tail' with
                  | nil => exact (hlen rfl).elim
                  | cons d tail'' => rfl)
    (by
      intro cargs hlen
      exact evalBuiltin_advanced_ternary_none_of_length .AndByteString
        (Or.inr (Or.inl rfl)) hlen)
    (by
      intro m bSym aSym padSym cb ca cpad cv hb ha hpad hcek
      obtain ⟨b, a, pad, rfl, rfl, rfl⟩ :=
        evalBuiltin_Bitwise_some_shape .AndByteString (Or.inl rfl) hcek
      exact pcHolds_all3_intro (asBool_guard_of_cek hpad)
        (asBytes_guard_of_cek ha) (asBytes_guard_of_cek hb))

theorem evalBuiltinSym_active_error_OrByteString :
    BuiltinErrorSound .OrByteString :=
  ternaryCheckedConstBuiltinError .OrByteString
    (fun b a pad => Proj.map3
      (fun pad a b => .app "uplc_orByteString" [pad, a, b])
      (asBool pad) (asBytes a) (asBytes b)) .bytes
    (by intro b a pad; rfl)
    (by
      intro args hlen
      cases args with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b tail =>
              cases tail with
              | nil => rfl
              | cons c tail' =>
                  cases tail' with
                  | nil => exact (hlen rfl).elim
                  | cons d tail'' => rfl)
    (by
      intro cargs hlen
      exact evalBuiltin_advanced_ternary_none_of_length .OrByteString
        (Or.inr (Or.inr (Or.inl rfl))) hlen)
    (by
      intro m bSym aSym padSym cb ca cpad cv hb ha hpad hcek
      obtain ⟨b, a, pad, rfl, rfl, rfl⟩ :=
        evalBuiltin_Bitwise_some_shape .OrByteString
          (Or.inr (Or.inl rfl)) hcek
      exact pcHolds_all3_intro (asBool_guard_of_cek hpad)
        (asBytes_guard_of_cek ha) (asBytes_guard_of_cek hb))

theorem evalBuiltinSym_active_error_XorByteString :
    BuiltinErrorSound .XorByteString :=
  ternaryCheckedConstBuiltinError .XorByteString
    (fun b a pad => Proj.map3
      (fun pad a b => .app "uplc_xorByteString" [pad, a, b])
      (asBool pad) (asBytes a) (asBytes b)) .bytes
    (by intro b a pad; rfl)
    (by
      intro args hlen
      cases args with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b tail =>
              cases tail with
              | nil => rfl
              | cons c tail' =>
                  cases tail' with
                  | nil => exact (hlen rfl).elim
                  | cons d tail'' => rfl)
    (by
      intro cargs hlen
      exact evalBuiltin_advanced_ternary_none_of_length .XorByteString
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hlen)
    (by
      intro m bSym aSym padSym cb ca cpad cv hb ha hpad hcek
      obtain ⟨b, a, pad, rfl, rfl, rfl⟩ :=
        evalBuiltin_Bitwise_some_shape .XorByteString
          (Or.inr (Or.inr rfl)) hcek
      exact pcHolds_all3_intro (asBool_guard_of_cek hpad)
        (asBytes_guard_of_cek ha) (asBytes_guard_of_cek hb))
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ComplementByteString :
    BuiltinErrorSound .ComplementByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ComplementByteString_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_ComplementByteString_eq bsSym] at hmem
          change out ∈
            [Outcome.ok (asBytes bsSym).guard
              (SymVal.const (SymConst.bytes
                (.app "uplc_complementByteString" [(asBytes bsSym).val]))),
             Outcome.error (SExpr.not (asBytes bsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ bs, cbs = .VCon (.ByteString bs)
              · rcases hshape with ⟨bs, rfl⟩
                have hg := asBytes_guard_of_cek (m := m) (v := bsSym) (bs := bs) hbs
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_ComplementByteString_none_of_single_not_bytes (by
                  intro bs h
                  exact hshape ⟨bs, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ComplementByteString_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
theorem evalBuiltinSym_active_error_ReadBit : BuiltinErrorSound .ReadBit :=
  binaryCheckedGuardedBuiltinError .ReadBit
    (fun idx bs => Proj.map2 (fun bs idx => (bs, idx))
      (asBytes bs) (asInt idx))
    (fun (bs, idx) => .app "uplc_readBit_defined" [bs, idx])
    (fun (bs, idx) => .const (.bool (.app "uplc_readBit" [bs, idx])))
    (by intro idx bs; rfl)
    (by
      intro args hlen
      cases args with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b tail =>
              cases tail with
              | nil => exact (hlen rfl).elim
              | cons c tail' => rfl)
    (by
      intro cargs hlen
      exact evalBuiltin_advanced_binary_none_of_length .ReadBit
        (Or.inr (Or.inl rfl)) hlen)
    (by
      intro m idxSym bsSym cidx cbs cv hidx hbs hcek
      obtain ⟨idx, bs, rfl, rfl⟩ := evalBuiltin_IntBytes_some_shape
        .ReadBit (Or.inl rfl) hcek
      exact pcHolds_and_intro
        (asBytes_guard_of_cek hbs) (asInt_guard_of_cek hidx))
    (by
      intro m idxSym bsSym cidx cbs cv hidx hbs hcek
      obtain ⟨idx, bs, rfl, rfl⟩ := evalBuiltin_IntBytes_some_shape
        .ReadBit (Or.inl rfl) hcek
      have gi := asInt_guard_of_cek hidx
      have gb := asBytes_guard_of_cek hbs
      obtain ⟨idx', hiEq, hidxEval⟩ := asInt_sound hidx gi
      obtain ⟨bs', hbEq, hbsEval⟩ := asBytes_sound hbs gb
      injection hiEq with hiConst
      injection hiConst with hiSub
      injection hbEq with hbConst
      injection hbConst with hbSub
      subst idx'
      subst bs'
      obtain ⟨c, hconst⟩ := evalBuiltinConst_some_of_evalBuiltin_vcons
        (b := .ReadBit) (cs := [.Integer idx, .ByteString bs]) (by rfl) hcek
      exact pcHolds_defined_of_const_success
        (Moist.SMT.Semantics.eval_uplcReadBitDefined_of hbsEval hidxEval)
        hconst)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_WriteBits : BuiltinErrorSound .WriteBits :=
  ternaryCheckedGuardedBuiltinError .WriteBits
    (fun value indices bs => Proj.map3 (fun bs indices value =>
      (bs, indices, value)) (asBytes bs) (asConstList indices) (asBool value))
    (fun (bs, indices, value) =>
      .app "uplc_writeBits_defined" [bs, indices, value])
    (fun (bs, indices, value) => .const (.bytes
      (.app "uplc_writeBits" [bs, indices, value])))
    (by intro value indices bs; rfl)
    (by
      intro args hlen
      cases args with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b tail =>
              cases tail with
              | nil => rfl
              | cons c tail' =>
                  cases tail' with
                  | nil => exact (hlen rfl).elim
                  | cons d tail'' => rfl)
    (by
      intro cargs hlen
      exact evalBuiltin_advanced_ternary_none_of_length .WriteBits
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hlen)
    (by
      intro m valueSym indicesSym bsSym cvalue cindices cbs cv
        hvalue hindices hbs hcek
      obtain ⟨value, indices, bs, rfl, rfl, rfl⟩ :=
        evalBuiltin_WriteBits_some_shape hcek
      exact pcHolds_all3_intro (asBytes_guard_of_cek hbs)
        (asConstList_guard_of_cek hindices) (asBool_guard_of_cek hvalue))
    (by
      intro m valueSym indicesSym bsSym cvalue cindices cbs cv
        hvalue hindices hbs hcek
      obtain ⟨value, indices, bs, rfl, rfl, rfl⟩ :=
        evalBuiltin_WriteBits_some_shape hcek
      have gv := asBool_guard_of_cek hvalue
      have gi := asConstList_guard_of_cek hindices
      have gb := asBytes_guard_of_cek hbs
      obtain ⟨value', hvEq, hvalueEval⟩ := asBool_sound hvalue gv
      obtain ⟨vals, cs, hcEq, hindicesEval, hsem⟩ :=
        asConstList_sound hindices gi
      obtain ⟨bs', hbEq, hbsEval⟩ := asBytes_sound hbs gb
      injection hvEq with hvConst
      injection hvConst with hvSub
      injection hcEq with hcConst
      injection hcConst with hcSub
      injection hbEq with hbConst
      injection hbConst with hbSub
      subst value'
      subst cs
      subst bs'
      obtain ⟨c, hconst⟩ := evalBuiltinConst_some_of_evalBuiltin_vcons
        (b := .WriteBits)
        (cs := [.Bool value, .ConstList indices, .ByteString bs])
        (by rfl) hcek
      cases hci : Moist.CEK.constListToInts indices with
      | none =>
          rw [Moist.CEK.evalBuiltinConst_writeBits] at hconst
          simp [Moist.CEK.builtinWriteBits, hci] at hconst
      | some is =>
          have his := Moist.CEK.constListToInts_some_shape hci
          subst indices
          have hi := intValsToConsts?_of_semValListToConstList?_integers hsem
          have hdefined : Moist.SMT.Semantics.writeBitsDefined
              bs vals value = true := by
            simp [Moist.SMT.Semantics.writeBitsDefined,
              Moist.SMT.Semantics.writeBitsConstArgs?, hi,
              Moist.SMT.Semantics.cekBuiltinConstDefined, hconst]
          apply (Moist.SMT.Semantics.evalBoolIs_true_eq m
            (.app "uplc_writeBits_defined"
              [(asBytes bsSym).val, (asConstList indicesSym).val,
               (asBool valueSym).val])).mpr
          simpa [hdefined] using
            (Moist.SMT.Semantics.eval_uplcWriteBitsDefined_of
              hbsEval hindicesEval hvalueEval))
theorem evalBuiltinSym_active_error_ReplicateByte :
    BuiltinErrorSound .ReplicateByte :=
  binaryCheckedGuardedBuiltinError .ReplicateByte
    (fun byte count => Proj.map2 (fun count byte => (count, byte))
      (asInt count) (asInt byte))
    (fun (count, byte) => .app "uplc_replicateByte_defined" [count, byte])
    (fun (count, byte) => .const (.bytes
      (.app "uplc_replicateByte" [count, byte])))
    (by intro byte count; rfl)
    (by
      intro args hlen
      cases args with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b tail =>
              cases tail with
              | nil => exact (hlen rfl).elim
              | cons c tail' => rfl)
    (by
      intro cargs hlen
      exact evalBuiltin_advanced_binary_none_of_length .ReplicateByte
        (Or.inr (Or.inr (Or.inl rfl))) hlen)
    (by
      intro m byteSym countSym cbyte ccount cv hbyte hcount hcek
      obtain ⟨byte, count, rfl, rfl⟩ :=
        evalBuiltin_ReplicateByte_some_shape hcek
      exact pcHolds_and_intro
        (asInt_guard_of_cek hcount) (asInt_guard_of_cek hbyte))
    (by
      intro m byteSym countSym cbyte ccount cv hbyte hcount hcek
      obtain ⟨byte, count, rfl, rfl⟩ :=
        evalBuiltin_ReplicateByte_some_shape hcek
      have gb := asInt_guard_of_cek hbyte
      have gc := asInt_guard_of_cek hcount
      obtain ⟨byte', hbEq, hbyteEval⟩ := asInt_sound hbyte gb
      obtain ⟨count', hcEq, hcountEval⟩ := asInt_sound hcount gc
      injection hbEq with hbConst
      injection hbConst with hbSub
      injection hcEq with hcConst
      injection hcConst with hcSub
      subst byte'
      subst count'
      obtain ⟨c, hconst⟩ := evalBuiltinConst_some_of_evalBuiltin_vcons
        (b := .ReplicateByte) (cs := [.Integer byte, .Integer count])
        (by rfl) hcek
      exact pcHolds_defined_of_const_success
        (Moist.SMT.Semantics.eval_uplcReplicateByteDefined_of
          hcountEval hbyteEval) hconst)
theorem evalBuiltinSym_active_error_ShiftByteString :
    BuiltinErrorSound .ShiftByteString :=
  binaryCheckedConstBuiltinError .ShiftByteString
    (fun n bs => Proj.map2 (fun bs n =>
        .app "uplc_shiftByteString" [bs, n])
      (asBytes bs) (asInt n))
    .bytes
    (by intro n bs; rfl)
    (by
      intro args hlen
      cases args with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b tail =>
              cases tail with
              | nil => exact (hlen rfl).elim
              | cons c tail' => rfl)
    (by
      intro cargs hlen
      exact evalBuiltin_advanced_binary_none_of_length .ShiftByteString
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hlen)
    (by
      intro m nSym bsSym cn cbs cv hn hbs hcek
      obtain ⟨n, bs, rfl, rfl⟩ := evalBuiltin_IntBytes_some_shape
        .ShiftByteString (Or.inr (Or.inl rfl)) hcek
      exact pcHolds_and_intro
        (asBytes_guard_of_cek hbs) (asInt_guard_of_cek hn))

theorem evalBuiltinSym_active_error_RotateByteString :
    BuiltinErrorSound .RotateByteString :=
  binaryCheckedConstBuiltinError .RotateByteString
    (fun n bs => Proj.map2 (fun bs n =>
        .app "uplc_rotateByteString" [bs, n])
      (asBytes bs) (asInt n))
    .bytes
    (by intro n bs; rfl)
    (by
      intro args hlen
      cases args with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b tail =>
              cases tail with
              | nil => exact (hlen rfl).elim
              | cons c tail' => rfl)
    (by
      intro cargs hlen
      exact evalBuiltin_advanced_binary_none_of_length .RotateByteString
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hlen)
    (by
      intro m nSym bsSym cn cbs cv hn hbs hcek
      obtain ⟨n, bs, rfl, rfl⟩ := evalBuiltin_IntBytes_some_shape
        .RotateByteString (Or.inr (Or.inr rfl)) hcek
      exact pcHolds_and_intro
        (asBytes_guard_of_cek hbs) (asInt_guard_of_cek hn))
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_CountSetBits :
    BuiltinErrorSound .CountSetBits := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_CountSetBits_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_CountSetBits_eq bsSym] at hmem
          change out ∈
            [Outcome.ok (asBytes bsSym).guard
              (SymVal.const (SymConst.integer
                (.app "uplc_countSetBits" [(asBytes bsSym).val]))),
             Outcome.error (SExpr.not (asBytes bsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ bs, cbs = .VCon (.ByteString bs)
              · rcases hshape with ⟨bs, rfl⟩
                have hg := asBytes_guard_of_cek (m := m) (v := bsSym) (bs := bs) hbs
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_CountSetBits_none_of_single_not_bytes (by
                  intro bs h
                  exact hshape ⟨bs, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_CountSetBits_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_FindFirstSetBit :
    BuiltinErrorSound .FindFirstSetBit := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_FindFirstSetBit_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_FindFirstSetBit_eq bsSym] at hmem
          change out ∈
            [Outcome.ok (asBytes bsSym).guard
              (SymVal.const (SymConst.integer
                (.app "uplc_findFirstSetBit" [(asBytes bsSym).val]))),
             Outcome.error (SExpr.not (asBytes bsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ bs, cbs = .VCon (.ByteString bs)
              · rcases hshape with ⟨bs, rfl⟩
                have hg := asBytes_guard_of_cek (m := m) (v := bsSym) (bs := bs) hbs
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_FindFirstSetBit_none_of_single_not_bytes (by
                  intro bs h
                  exact hshape ⟨bs, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_FindFirstSetBit_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
theorem evalBuiltinSym_active_error_ExpModInteger :
    BuiltinErrorSound .ExpModInteger :=
  ternaryCheckedGuardedBuiltinError .ExpModInteger
    (fun modulus exponent base => Proj.map3 (fun base exponent modulus =>
      (base, exponent, modulus)) (asInt base) (asInt exponent) (asInt modulus))
    (fun (base, exponent, modulus) =>
      .app "uplc_expModInteger_defined" [base, exponent, modulus])
    (fun (base, exponent, modulus) => .const (.integer
      (.app "uplc_expModInteger" [base, exponent, modulus])))
    (by intro modulus exponent base; rfl)
    (by
      intro args hlen
      cases args with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b tail =>
              cases tail with
              | nil => rfl
              | cons c tail' =>
                  cases tail' with
                  | nil => exact (hlen rfl).elim
                  | cons d tail'' => rfl)
    (by
      intro cargs hlen
      exact evalBuiltin_advanced_ternary_none_of_length .ExpModInteger
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hlen)
    (by
      intro m mSym eSym bSym cm ce cb cv hm he hb hcek
      obtain ⟨modulus, exponent, base, rfl, rfl, rfl⟩ :=
        evalBuiltin_ExpModInteger_some_shape hcek
      exact pcHolds_all3_intro (asInt_guard_of_cek hb)
        (asInt_guard_of_cek he) (asInt_guard_of_cek hm))
    (by
      intro m mSym eSym bSym cm ce cb cv hm he hb hcek
      obtain ⟨modulus, exponent, base, rfl, rfl, rfl⟩ :=
        evalBuiltin_ExpModInteger_some_shape hcek
      have gm := asInt_guard_of_cek hm
      have ge := asInt_guard_of_cek he
      have gb := asInt_guard_of_cek hb
      obtain ⟨modulus', hmEq, hmEval⟩ := asInt_sound hm gm
      obtain ⟨exponent', heEq, heEval⟩ := asInt_sound he ge
      obtain ⟨base', hbEq, hbEval⟩ := asInt_sound hb gb
      injection hmEq with hmConst
      injection hmConst with hmSub
      injection heEq with heConst
      injection heConst with heSub
      injection hbEq with hbConst
      injection hbConst with hbSub
      subst modulus'
      subst exponent'
      subst base'
      obtain ⟨c, hconst⟩ := evalBuiltinConst_some_of_evalBuiltin_vcons
        (b := .ExpModInteger)
        (cs := [.Integer modulus, .Integer exponent, .Integer base])
        (by rfl) hcek
      exact pcHolds_defined_of_const_success
        (Moist.SMT.Semantics.eval_uplcExpModIntegerDefined_of
          hbEval heEval hmEval) hconst)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_DropList : BuiltinErrorSound .DropList := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_DropList_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons xs rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_DropList_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons n rest2 =>
          cases rest2 with
          | nil =>
              change out ∈
                (let vl := Proj.map2 (fun n xs => .app "vlist_drop" [n, xs])
                    (asInt n) (asConstList xs)
                 let dl := Proj.map2 (fun n xs => .app "dlist_drop" [n, xs])
                    (asInt n) (asDataList xs)
                 [Outcome.ok vl.guard (.const (.constList vl.val .unknown)),
                  Outcome.ok dl.guard (.const (.dataList dl.val)),
                  Outcome.error (SExpr.not (SExpr.or vl.guard dl.guard))]) at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cxs, cn, hxs, hn, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hokVl | hokDl | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hlist :
                      ∃ cs i, cxs = .VCon (.ConstList cs) ∧ cn = .VCon (.Integer i)
                  · rcases hlist with ⟨cs, i, rfl, rfl⟩
                    have hgInt := asInt_guard_of_cek (m := m) (v := n) (i := i) hn
                    have hgList := asConstList_guard_of_cek (m := m) (v := xs) (cs := cs) hxs
                    have hvl : pcHolds m
                        (SExpr.and (asInt n).guard (asConstList xs).guard) = true :=
                      pcHolds_all2_intro (m := m) hgInt hgList
                    exact False.elim
                      (pcHolds_not_or_contra_left (m := m)
                        (a := SExpr.and (asInt n).guard (asConstList xs).guard)
                        (b := SExpr.and (asInt n).guard (asDataList xs).guard)
                        hvl hactive)
                  · by_cases hdata :
                      ∃ ds i, cxs = .VCon (.ConstDataList ds) ∧ cn = .VCon (.Integer i)
                    · rcases hdata with ⟨ds, i, rfl, rfl⟩
                      have hgInt := asInt_guard_of_cek (m := m) (v := n) (i := i) hn
                      have hgData :=
                        asDataList_guard_of_cek (m := m) (v := xs) (xs := ds) hxs
                      have hdl : pcHolds m
                          (SExpr.and (asInt n).guard (asDataList xs).guard) = true :=
                        pcHolds_all2_intro (m := m) hgInt hgData
                      exact False.elim
                        (pcHolds_not_or_contra_right (m := m)
                          (a := SExpr.and (asInt n).guard (asConstList xs).guard)
                          (b := SExpr.and (asInt n).guard (asDataList xs).guard)
                          hdl hactive)
                    · exact evalBuiltin_DropList_none_of_pair_not_supported
                        (a := cxs) (b := cn)
                        (by
                          intro cs i h
                          exact hlist ⟨cs, i, h⟩)
                        (by
                          intro ds i h
                          exact hdata ⟨ds, i, h⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_DropList_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_IndexArray : BuiltinErrorSound .IndexArray := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_IndexArray_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons idx rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_IndexArray_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons arr rest2 =>
          cases rest2 with
          | nil =>
              change out ∈
                checked2
                  (Proj.map2 (fun arr idx => (arr, idx)) (asArray arr) (asInt idx))
                  (fun (arr, idx) =>
                    let g := SExpr.and (SExpr.ge idx (.int 0))
                      (SExpr.lt idx (.app "vlist_length" [arr]))
                    [Outcome.ok g (.dyn (.app "vlist_index" [idx, arr])),
                     Outcome.error (SExpr.not g)]) at hmem
              obtain ⟨cidx, carr, hidxArg, harrArg, rfl⟩ :=
                symValListToCekList_pair hargs
              have hpath := checked2_active_error hmem hactive
              rcases hpath with hinner | hproj
              · rcases hinner with ⟨inner, hinner, hpArgs, hinnerActive⟩
                change inner ∈
                  (let g := SExpr.and (SExpr.ge (asInt idx).val (.int 0))
                    (SExpr.lt (asInt idx).val
                      (.app "vlist_length" [(asArray arr).val]))
                   [Outcome.ok g (.dyn (.app "vlist_index" [(asInt idx).val,
                     (asArray arr).val])),
                    Outcome.error (SExpr.not g)]) at hinner
                simp only [List.mem_cons, List.not_mem_nil] at hinner
                rcases hinner with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hnotRange :
                        pcHolds m
                          (SExpr.not
                            (SExpr.and (SExpr.ge (asInt idx).val (.int 0))
                              (SExpr.lt (asInt idx).val
                                (.app "vlist_length" [(asArray arr).val])))) = true := by
                      simpa [outcomeErrorActive] using hinnerActive
                    change pcHolds m
                      (SExpr.and (asArray arr).guard (asInt idx).guard) = true at hpArgs
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asArray arr).guard (asInt idx).guard).mp hpArgs
                    obtain ⟨i, rfl, hiEval⟩ := asInt_sound hidxArg hp.2
                    obtain ⟨vals, cs, rfl, harrEval, hconsts⟩ :=
                      asArray_sound harrArg hp.1
                    by_cases hneg : i < 0
                    · exact evalBuiltin_IndexArray_none_of_negative (cs := cs) hneg
                    · have hge : 0 ≤ i := (Int.not_lt).mp hneg
                      by_cases hsome : ∃ c, cs[i.toNat]? = some c
                      · rcases hsome with ⟨c, hgetCs⟩
                        have hidxNatLtCs : i.toNat < cs.length := by
                          rcases (List.getElem?_eq_some_iff.mp hgetCs) with ⟨h, _hval⟩
                          exact h
                        have hlenNat : vals.length = cs.length :=
                          semValListToConstList_length hconsts
                        have hidxNatLtVals : i.toNat < vals.length := by
                          rwa [hlenNat]
                        have hlt : i < Int.ofNat vals.length :=
                          (Int.toNat_lt hge).mp hidxNatLtVals
                        have hlenEval := Moist.SMT.Semantics.eval_vlist_length_of
                          (m := m) (e := (asArray arr).val) harrEval
                        have hgePc : pcHolds m
                            (SExpr.ge (asInt idx).val (.int 0)) = true :=
                          pcHolds_ge_int_intro hiEval
                            (by simp [Moist.SMT.Semantics.eval]) hge
                        have hltPc : pcHolds m
                            (SExpr.lt (asInt idx).val
                              (.app "vlist_length" [(asArray arr).val])) = true :=
                          pcHolds_lt_int_intro hiEval hlenEval hlt
                        have hrange : pcHolds m
                            (SExpr.and (SExpr.ge (asInt idx).val (.int 0))
                              (SExpr.lt (asInt idx).val
                                (.app "vlist_length" [(asArray arr).val]))) = true :=
                          pcHolds_and_intro hgePc hltPc
                        exact False.elim (pcHolds_not_contra hrange hnotRange)
                      · have hgetNone : cs[i.toNat]? = none := by
                          cases hget : cs[i.toNat]? with
                          | none => rfl
                          | some c => exact False.elim (hsome ⟨c, hget⟩)
                        exact evalBuiltin_IndexArray_none_of_nonnegative_get_none
                          (cs := cs) hge hgetNone
                  · cases hfalse
              · by_cases hshape :
                  ∃ i cs, cidx = .VCon (.Integer i) ∧ carr = .VCon (.ConstArray cs)
                · rcases hshape with ⟨i, cs, rfl, rfl⟩
                  have hgArr := asArray_guard_of_cek (m := m) (v := arr) (cs := cs) harrArg
                  have hgIdx := asInt_guard_of_cek (m := m) (v := idx) (i := i) hidxArg
                  have hprojGuard : pcHolds m
                      (SExpr.and (asArray arr).guard (asInt idx).guard) = true :=
                    pcHolds_and_intro hgArr hgIdx
                  exact False.elim (pcHolds_not_contra hprojGuard hproj)
                · exact evalBuiltin_IndexArray_none_of_pair_not_supported
                    (a := cidx) (b := carr)
                    (by
                      intro i cs h
                      exact hshape ⟨i, cs, h⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_IndexArray_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_LengthOfArray :
    BuiltinErrorSound .LengthOfArray := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_LengthOfArray_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons arr rest =>
      cases rest with
      | nil =>
          change out ∈
            [Outcome.ok (asArray arr).guard
              (SymVal.const (SymConst.integer
                (.app "vlist_length" [(asArray arr).val]))),
             Outcome.error (SExpr.not (asArray arr).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨carr, harr, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ cs, carr = .VCon (.ConstArray cs)
              · rcases hshape with ⟨cs, rfl⟩
                have hg := asArray_guard_of_cek harr
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_LengthOfArray_none_of_single_not_array (by
                  intro cs h
                  exact hshape ⟨cs, h⟩)
            · cases hfalse
      | cons a rest =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_LengthOfArray_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ListToArray :
    BuiltinErrorSound .ListToArray := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ListToArray_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons xs rest =>
      cases rest with
      | nil =>
          change out ∈
            [Outcome.ok (asConstList xs).guard
              (SymVal.const (SymConst.array (asConstList xs).val)),
             Outcome.error (SExpr.not (asConstList xs).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ cs, cxs = .VCon (.ConstList cs)
              · rcases hshape with ⟨cs, rfl⟩
                have hg := asConstList_guard_of_cek hxs
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_ListToArray_none_of_single_not_list (by
                  intro cs h
                  exact hshape ⟨cs, h⟩)
            · cases hfalse
      | cons a rest =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ListToArray_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
end Moist.SMT.UPLC.Soundness
