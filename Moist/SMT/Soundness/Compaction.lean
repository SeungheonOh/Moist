import Moist.SMT.Soundness.Foundations

/-!
# Soundness of symbolic outcome compaction

This module proves that every active compacted success or error comes from an
active pre-compaction outcome with the same decoded CEK value.  These lemmas
are the sole proof boundary used when `evalSym` compacts forced lazy branches.
-/

namespace Moist.SMT.UPLC.Soundness

theorem symValToCek_dyn_compactEncode {m : SmtSem.Model} {v : SymVal} {e : SExpr}
    (h : compactEncodeVal? v = some e) :
    symValToCek? m (.dyn e) = symValToCek? m v := by
  cases v with
  | const c =>
      cases c with
      | constList xs =>
          simp [compactEncodeVal?] at h
          subst e
          simp only [symValToCek?, symConstToCek?]
          change (match Moist.SMT.Semantics.eval m (.app "VList" [xs]) with
            | some (.val v) => semValToCek? v
            | _ => none) = _
          rw [Moist.SMT.Semantics.eval_VList_exact]
          cases hxs : SmtSem.eval m xs <;>
            simp [hxs, semValToCek?, semValToConst?]
          rename_i sv
          cases sv <;> simp [hxs, semValToCek?, semValToConst?]
          rename_i vals
          cases hcs : semValListToConstList? vals <;> simp [hcs]
      | dataList xs =>
          simp [compactEncodeVal?] at h
          subst e
          simp only [symValToCek?, symConstToCek?]
          change (match Moist.SMT.Semantics.eval m (.app "VDataList" [xs]) with
            | some (.val v) => semValToCek? v
            | _ => none) = _
          rw [Moist.SMT.Semantics.eval_VDataList_exact]
          cases hxs : SmtSem.eval m xs <;>
            simp [hxs, semValToCek?, semValToConst?]
          rename_i sv
          cases sv <;> simp [hxs, semValToCek?, semValToConst?]
      | integer x | bytes x | string x | bool x | data x | pairDataList x
      | array x | g1 x | g2 x | ml x => simp [compactEncodeVal?] at h
      | unit => simp [compactEncodeVal?] at h
      | pairData a b => simp [compactEncodeVal?] at h
  | dyn d =>
      simp [compactEncodeVal?] at h
      subst e
      rfl
  | pair a b => simp [compactEncodeVal?] at h
  | constr tag fields => simp [compactEncodeVal?] at h
  | lam body env => simp [compactEncodeVal?] at h
  | delay body env => simp [compactEncodeVal?] at h
  | builtin b args ea => simp [compactEncodeVal?] at h

theorem symValNoOpaque_dyn_compactEncode {v : SymVal} {e : SExpr}
    (h : compactEncodeVal? v = some e) :
    symValNoOpaqueForSoundness (.dyn e) = symValNoOpaqueForSoundness v := by
  cases v with
  | const c =>
      cases c <;> simp [compactEncodeVal?, symValNoOpaqueForSoundness] at h ⊢
  | dyn d => simp [compactEncodeVal?, symValNoOpaqueForSoundness] at h ⊢
  | pair a b => simp [compactEncodeVal?] at h
  | constr tag fields => simp [compactEncodeVal?] at h
  | lam body env => simp [compactEncodeVal?] at h
  | delay body env => simp [compactEncodeVal?] at h
  | builtin b args ea => simp [compactEncodeVal?] at h

theorem symValToCek_dyn_ite_of {m : SmtSem.Model} {c t e : SExpr} {b : Bool}
    (hc : SmtSem.eval m c = some (.bool b)) :
    symValToCek? m (.dyn (.ite c t e)) =
      if b then symValToCek? m (.dyn t) else symValToCek? m (.dyn e) := by
  simp only [symValToCek?]
  change (match Moist.SMT.Semantics.eval m (.ite c t e) with
    | some (.val v) => semValToCek? v
    | _ => none) = _
  have hc' : Moist.SMT.Semantics.eval m c = some (.bool b) := hc
  rw [Moist.SMT.Semantics.eval_ite_exact, hc']
  cases b <;> rfl

theorem encodedOks_mem {outs : List Outcome} {pc value : SExpr}
    (h : (pc, value) ∈ encodedOks outs) :
    ∃ v, Outcome.ok pc v ∈ outs ∧ compactEncodeVal? v = some value := by
  induction outs with
  | nil => simp [encodedOks] at h
  | cons out outs ih =>
      cases out with
      | ok pc' v =>
          cases he : compactEncodeVal? v with
          | none =>
              simp [encodedOks, he] at h
              obtain ⟨v', hv', he'⟩ := ih h
              exact ⟨v', by simp [hv'], he'⟩
          | some e =>
              simp [encodedOks, he] at h
              rcases h with h | h
              · rcases h with ⟨rfl, rfl⟩
                exact ⟨v, by simp, he⟩
              · obtain ⟨v', hv', he'⟩ := ih h
                exact ⟨v', by simp [hv'], he'⟩
      | error pc' =>
          simp [encodedOks] at h
          obtain ⟨v', hv', he'⟩ := ih h
          exact ⟨v', by simp [hv'], he'⟩
      | timeout pc' =>
          simp [encodedOks] at h
          obtain ⟨v', hv', he'⟩ := ih h
          exact ⟨v', by simp [hv'], he'⟩

theorem nonEncodedOks_mem {outs : List Outcome} {out : Outcome}
    (h : out ∈ nonEncodedOks outs) : out ∈ outs := by
  induction outs with
  | nil => simp [nonEncodedOks] at h
  | cons head tail ih =>
      cases head with
      | ok pc v =>
          cases he : compactEncodeVal? v <;> simp [nonEncodedOks, he] at h
          · exact h.elim (by intro hEq; simpa [hEq]) (fun ht => by simp [ih ht])
          · exact by simp [ih h]
      | error pc => exact by simp [nonEncodedOks, ih h]
      | timeout pc => exact by simp [nonEncodedOks, ih h]

theorem errorPcs_mem {outs : List Outcome} {pc : SExpr}
    (h : pc ∈ errorPcs outs) : Outcome.error pc ∈ outs := by
  induction outs with
  | nil => simp [errorPcs] at h
  | cons out outs ih =>
      cases out with
      | ok p v => simp [errorPcs, ih h]
      | timeout p => simp [errorPcs, ih h]
      | error p =>
          simp [errorPcs] at h
          rcases h with h | h
          · subst p; simp
          · simp [ih h]

theorem timeoutPcs_mem {outs : List Outcome} {pc : SExpr}
    (h : pc ∈ timeoutPcs outs) : Outcome.timeout pc ∈ outs := by
  induction outs with
  | nil => simp [timeoutPcs] at h
  | cons out outs ih =>
      cases out with
      | ok p v => simp [timeoutPcs, ih h]
      | error p => simp [timeoutPcs, ih h]
      | timeout p =>
          simp [timeoutPcs] at h
          rcases h with h | h
          · subst p; simp
          · simp [ih h]

theorem mergeEncodedOks_active {m : SmtSem.Model} {oks : List EncodedOk}
    {pc value : SExpr}
    (hmerge : mergeEncodedOks oks = some (pc, value))
    (hpc : pcHolds m pc = true) :
    ∃ sourcePc sourceValue,
      (sourcePc, sourceValue) ∈ oks ∧
      pcHolds m sourcePc = true ∧
      symValToCek? m (.dyn value) = symValToCek? m (.dyn sourceValue) := by
  induction oks generalizing pc value with
  | nil => simp [mergeEncodedOks] at hmerge
  | cons head tail ih =>
      rcases head with ⟨headPc, headValue⟩
      cases hm : mergeEncodedOks tail with
      | none =>
          simp [mergeEncodedOks, hm] at hmerge
          rcases hmerge with ⟨rfl, rfl⟩
          exact ⟨headPc, headValue, by simp, hpc, rfl⟩
      | some merged =>
          rcases merged with ⟨tailPc, tailValue⟩
          simp [mergeEncodedOks, hm] at hmerge
          rcases hmerge with ⟨rfl, rfl⟩
          cases hc : Moist.SMT.Semantics.eval m headPc with
          | none =>
              simp [pcHolds, Moist.SMT.Semantics.evalBoolIs,
                Moist.SMT.Semantics.evalBool?, Moist.SMT.Semantics.eval, hc] at hpc
          | some sv =>
              cases sv with
              | bool b =>
                  cases b with
                  | false =>
                      have hheadFalse : pcHolds m headPc = false := by
                        simp [pcHolds, Moist.SMT.Semantics.evalBoolIs,
                          Moist.SMT.Semantics.evalBool?, hc]
                      have htail : pcHolds m tailPc = true := by
                        cases ht : Moist.SMT.Semantics.eval m tailPc with
                        | none =>
                            simp [pcHolds, Moist.SMT.Semantics.evalBoolIs,
                              Moist.SMT.Semantics.evalBool?, Moist.SMT.Semantics.eval,
                              hc, ht] at hpc
                        | some tailSv =>
                            cases tailSv <;>
                              simp [pcHolds, Moist.SMT.Semantics.evalBoolIs,
                                Moist.SMT.Semantics.evalBool?, Moist.SMT.Semantics.eval,
                                hc, ht] at hpc ⊢
                            exact hpc
                      obtain ⟨p, e, hmem, hp, he⟩ := ih hm htail
                      refine ⟨p, e, by simp [hmem], hp, ?_⟩
                      rw [symValToCek_dyn_ite_of hc]
                      exact he
                  | true =>
                      have hp : pcHolds m headPc = true := by
                        simp [pcHolds, Moist.SMT.Semantics.evalBoolIs,
                          Moist.SMT.Semantics.evalBool?, hc]
                      refine ⟨headPc, headValue, by simp, hp, ?_⟩
                      rw [symValToCek_dyn_ite_of hc]
                      rfl
              | int i | string i | bytes i | data i | dataList i
              | dataPairList i | val i | valList i | g1 i | g2 i | ml i =>
                  simp [pcHolds, Moist.SMT.Semantics.evalBoolIs,
                    Moist.SMT.Semantics.evalBool?, Moist.SMT.Semantics.eval, hc] at hpc

theorem ok_not_mem_mergedErrorOutcome {outs : List Outcome} {pc : SExpr}
    {v : SymVal} : Outcome.ok pc v ∉ mergedErrorOutcome outs := by
  unfold mergedErrorOutcome
  split <;> simp

theorem ok_not_mem_mergedTimeoutOutcome {outs : List Outcome} {pc : SExpr}
    {v : SymVal} : Outcome.ok pc v ∉ mergedTimeoutOutcome outs := by
  unfold mergedTimeoutOutcome
  split <;> simp

theorem error_not_mem_mergedTimeoutOutcome {outs : List Outcome} {pc : SExpr} :
    Outcome.error pc ∉ mergedTimeoutOutcome outs := by
  unfold mergedTimeoutOutcome
  split <;> simp

theorem timeout_not_mem_mergedOkOutcome {outs : List Outcome} {pc : SExpr} :
    Outcome.timeout pc ∉ mergedOkOutcome outs := by
  unfold mergedOkOutcome
  split <;> simp

theorem timeout_not_mem_mergedErrorOutcome {outs : List Outcome} {pc : SExpr} :
    Outcome.timeout pc ∉ mergedErrorOutcome outs := by
  unfold mergedErrorOutcome
  split <;> simp

theorem compactOutcomes_active_ok {m : SmtSem.Model} {outs : List Outcome}
    {pc : SExpr} {v : SymVal}
    (hmem : Outcome.ok pc v ∈ compactOutcomes outs)
    (hpc : pcHolds m pc = true) :
    ∃ sourcePc sourceValue,
      Outcome.ok sourcePc sourceValue ∈ outs ∧
      pcHolds m sourcePc = true ∧
      symValToCek? m v = symValToCek? m sourceValue ∧
      symValNoOpaqueForSoundness v =
        symValNoOpaqueForSoundness sourceValue := by
  rw [compactOutcomes] at hmem
  rcases List.mem_append.mp hmem with hprefix | htimeout
  · rcases List.mem_append.mp hprefix with hab | herr
    · rcases List.mem_append.mp hab with hmerged | hnon
      · unfold mergedOkOutcome at hmerged
        cases hm : mergeEncodedOks (encodedOks outs) with
        | none => simp [hm] at hmerged
        | some merged =>
            rcases merged with ⟨mergedPc, mergedValue⟩
            simp [hm] at hmerged
            rcases hmerged with ⟨rfl, rfl⟩
            obtain ⟨sourcePc, sourceExpr, hentry, hsourcePc, hsourceEq⟩ :=
              mergeEncodedOks_active hm hpc
            obtain ⟨sourceValue, hsourceMem, hencode⟩ := encodedOks_mem hentry
            refine ⟨sourcePc, sourceValue, hsourceMem, hsourcePc, ?_, ?_⟩
            · rw [hsourceEq, symValToCek_dyn_compactEncode hencode]
            · simpa [symValNoOpaqueForSoundness] using
                (symValNoOpaque_dyn_compactEncode
                  (v := sourceValue) (e := sourceExpr) hencode)
      · exact ⟨pc, v, nonEncodedOks_mem hnon, hpc, rfl, rfl⟩
    · exact False.elim (ok_not_mem_mergedErrorOutcome herr)
  · exact False.elim (ok_not_mem_mergedTimeoutOutcome htimeout)

theorem error_not_mem_nonEncodedOks {outs : List Outcome} {pc : SExpr} :
    Outcome.error pc ∉ nonEncodedOks outs := by
  induction outs with
  | nil => simp [nonEncodedOks]
  | cons out outs ih =>
      cases out with
      | ok p v =>
          cases he : compactEncodeVal? v <;> simp [nonEncodedOks, he, ih]
      | error p => simp [nonEncodedOks, ih]
      | timeout p => simp [nonEncodedOks, ih]

theorem timeout_not_mem_nonEncodedOks {outs : List Outcome} {pc : SExpr} :
    Outcome.timeout pc ∉ nonEncodedOks outs := by
  induction outs with
  | nil => simp [nonEncodedOks]
  | cons out outs ih =>
      cases out with
      | ok p v =>
          cases he : compactEncodeVal? v <;> simp [nonEncodedOks, he, ih]
      | error p => simp [nonEncodedOks, ih]
      | timeout p => simp [nonEncodedOks, ih]

theorem compactOutcomes_active_error {m : SmtSem.Model} {outs : List Outcome}
    {pc : SExpr}
    (hmem : Outcome.error pc ∈ compactOutcomes outs)
    (hpc : pcHolds m pc = true) :
    ∃ sourcePc, Outcome.error sourcePc ∈ outs ∧
      pcHolds m sourcePc = true := by
  rw [compactOutcomes] at hmem
  rcases List.mem_append.mp hmem with hprefix | htimeout
  · rcases List.mem_append.mp hprefix with hab | herr
    · rcases List.mem_append.mp hab with hmerged | hnon
      · unfold mergedOkOutcome at hmerged
        split at hmerged <;> simp_all
      · exact False.elim (error_not_mem_nonEncodedOks hnon)
    · unfold mergedErrorOutcome at herr
      cases hp : errorPcs outs with
      | nil => simp [hp] at herr
      | cons p ps =>
          simp [hp] at herr
          subst pc
          obtain ⟨sourcePc, hsourceMem, hsourceActive⟩ :=
            evalBoolIs_any_true (m := m) (by simpa [pcHolds] using hpc)
          exact ⟨sourcePc, errorPcs_mem (by simpa [hp] using hsourceMem),
            by simpa [pcHolds] using hsourceActive⟩
  · exact False.elim (error_not_mem_mergedTimeoutOutcome htimeout)

theorem compactOutcomes_active_timeout {m : SmtSem.Model} {outs : List Outcome}
    {pc : SExpr}
    (hmem : Outcome.timeout pc ∈ compactOutcomes outs)
    (hpc : pcHolds m pc = true) :
    ∃ sourcePc, Outcome.timeout sourcePc ∈ outs ∧
      pcHolds m sourcePc = true := by
  rw [compactOutcomes] at hmem
  rcases List.mem_append.mp hmem with hprefix | htimeout
  · rcases List.mem_append.mp hprefix with hab | herr
    · rcases List.mem_append.mp hab with hmerged | hnon
      · exact False.elim (timeout_not_mem_mergedOkOutcome hmerged)
      · exact False.elim (timeout_not_mem_nonEncodedOks hnon)
    · exact False.elim (timeout_not_mem_mergedErrorOutcome herr)
  · unfold mergedTimeoutOutcome at htimeout
    cases hp : timeoutPcs outs with
    | nil => simp [hp] at htimeout
    | cons p ps =>
        simp [hp] at htimeout
        subst pc
        obtain ⟨sourcePc, hsourceMem, hsourceActive⟩ :=
          evalBoolIs_any_true (m := m) (by simpa [pcHolds] using hpc)
        exact ⟨sourcePc, timeoutPcs_mem (by simpa [hp] using hsourceMem),
          by simpa [pcHolds] using hsourceActive⟩

end Moist.SMT.UPLC.Soundness
