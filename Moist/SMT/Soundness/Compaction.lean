import Moist.SMT.Soundness.ListCertificates

/-!
# Soundness of symbolic outcome compaction

This module proves that every active compacted success, error, or timeout
comes from an active pre-compaction outcome.  Successful values retain their
native SMT sort whenever one is available, avoiding repeated generic-datatype
projections while preserving exactly the same decoded CEK value.
-/

namespace Moist.SMT.UPLC.Soundness

theorem compactDecode_encode_toCek {m : SmtSem.Model} {kind : CompactKind}
    {v : SymVal} {e : SExpr} (h : kind.encode? v = some e) :
    symValToCek? m (kind.decode e) = symValToCek? m v := by
  cases kind with
  | integer =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | bool =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | unit =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | bytes =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | string =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | data =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | constList =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | dataList =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | pairDataList =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | array =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | dyn =>
      cases v with
      | dyn d =>
          simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | const c | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h

theorem compactDecode_encode_noOpaque {kind : CompactKind} {v : SymVal}
    {e : SExpr} (h : kind.encode? v = some e) :
    symValNoOpaqueForSoundness (kind.decode e) =
      symValNoOpaqueForSoundness v := by
  cases kind with
  | bool =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | unit =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | integer =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | bytes =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | string =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | data =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | constList =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | dataList =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | pairDataList =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | array =>
      cases v with
      | const c =>
          cases c <;> simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | dyn d | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h
  | dyn =>
      cases v with
      | dyn d =>
          simp [CompactKind.encode?, CompactKind.decode] at h ⊢
          subst e
          rfl
      | const c | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
          simp [CompactKind.encode?] at h

theorem mergedDecode_toCek (m : SmtSem.Model) (kind : CompactKind)
    (e : SExpr) :
    symValToCek? m (mergedDecode kind e) =
      symValToCek? m (kind.decode e) := by
  cases kind <;> rfl

theorem mergedDecode_noOpaque (kind : CompactKind) (e : SExpr) :
    symValNoOpaqueForSoundness (mergedDecode kind e) =
      symValNoOpaqueForSoundness (kind.decode e) := by
  cases kind <;> rfl

theorem compactDecode_noOpaque_irrel (kind : CompactKind) (a b : SExpr) :
    symValNoOpaqueForSoundness (kind.decode a) =
      symValNoOpaqueForSoundness (kind.decode b) := by
  cases kind <;> rfl

theorem symValToCek_decode_ite_of (kind : CompactKind) {m : SmtSem.Model}
    {c t e : SExpr} {b : Bool}
    (hc : SmtSem.eval m c = some (.bool b)) :
    symValToCek? m (kind.decode (.ite c t e)) =
      if b then symValToCek? m (kind.decode t)
      else symValToCek? m (kind.decode e) := by
  have hc' : Moist.SMT.Semantics.eval m c = some (.bool b) := hc
  have hEval : SmtSem.eval m (SExpr.ite c t e) =
      if b then SmtSem.eval m t else SmtSem.eval m e := by
    change Moist.SMT.Semantics.eval m (Moist.SMT.Expr.ite c t e) = _
    rw [Moist.SMT.Semantics.eval_ite_exact, hc']
    cases b <;> rfl
  cases kind <;>
    simp only [CompactKind.decode, symValToCek?, symConstToCek?]
  all_goals first
    | (rw [hEval]; cases b <;> rfl)
    | (cases b <;> rfl)

theorem encodedOks_mem {kind : CompactKind} {outs : List Outcome}
    {pc value : SExpr} (h : (pc, value) ∈ encodedOks kind outs) :
    ∃ v, Outcome.ok pc v ∈ outs ∧ kind.encode? v = some value := by
  induction outs with
  | nil => simp [encodedOks] at h
  | cons out outs ih =>
      cases out with
      | ok pc' v =>
          cases he : kind.encode? v with
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

theorem encodedConstListOks_erase (outs : List Outcome) :
    (encodedConstListOks outs).map EncodedConstListOk.erase =
      encodedOks .constList outs := by
  induction outs with
  | nil => rfl
  | cons out outs ih =>
      cases out with
      | error pc | timeout pc => simpa [encodedConstListOks, encodedOks] using ih
      | ok pc value =>
          cases value with
          | const c =>
              cases c <;> simp [encodedConstListOks, encodedOks,
                CompactKind.encode?, EncodedConstListOk.erase, ih]
          | dyn e | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ =>
              simp [encodedConstListOks, encodedOks, CompactKind.encode?, ih]

theorem mergeEncodedConstListOks_erase (oks : List EncodedConstListOk) :
    (mergeEncodedConstListOks oks).map EncodedConstListOk.erase =
      mergeEncodedOks (oks.map EncodedConstListOk.erase) := by
  induction oks with
  | nil => rfl
  | cons ok oks ih =>
      cases hm : mergeEncodedConstListOks oks with
      | none =>
          have hmErase : mergeEncodedOks (oks.map EncodedConstListOk.erase) = none := by
            simpa [hm] using ih.symm
          simp [mergeEncodedConstListOks, hm, mergeEncodedOks, hmErase,
            EncodedConstListOk.erase]
      | some rest =>
          have hmErase :
              mergeEncodedOks (oks.map EncodedConstListOk.erase) =
                some rest.erase := by
            simpa [hm] using ih.symm
          cases hs : SExpr.sameAtom ok.value rest.value <;>
            simp [mergeEncodedConstListOks, hm, mergeEncodedOks, hmErase,
              EncodedConstListOk.erase, hs]

theorem nonEncodedOks_mem {outs : List Outcome} {out : Outcome}
    (h : out ∈ nonEncodedOks outs) : out ∈ outs := by
  induction outs with
  | nil => simp [nonEncodedOks] at h
  | cons head tail ih =>
      cases head with
      | ok pc v =>
          cases he : compactKind? v <;> simp [nonEncodedOks, he] at h
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

theorem mergeEncodedOks_active (kind : CompactKind) {m : SmtSem.Model}
    {oks : List EncodedOk} {pc value : SExpr}
    (hmerge : mergeEncodedOks oks = some (pc, value))
    (hpc : pcHolds m pc = true) :
    ∃ sourcePc sourceValue,
      (sourcePc, sourceValue) ∈ oks ∧
      pcHolds m sourcePc = true ∧
      symValToCek? m (kind.decode value) =
        symValToCek? m (kind.decode sourceValue) := by
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
          have hpcEval :
              Moist.SMT.Semantics.eval m
                  (SExpr.ite headPc SExpr.trueE tailPc) =
                some (.bool true) := by
            exact (Moist.SMT.Semantics.evalBoolIs_true_eq m _).mp hpc
          change Moist.SMT.Semantics.eval m
              (.ite headPc SExpr.trueE tailPc) = some (.bool true) at hpcEval
          cases hc : Moist.SMT.Semantics.eval m headPc with
          | none =>
              rw [Moist.SMT.Semantics.eval_ite_exact, hc] at hpcEval
              contradiction
          | some sv =>
              cases sv with
              | bool b =>
                  cases b with
                  | false =>
                      have htail : pcHolds m tailPc = true := by
                        rw [Moist.SMT.Semantics.eval_ite_exact, hc] at hpcEval
                        exact
                          (Moist.SMT.Semantics.evalBoolIs_true_eq m tailPc).mpr
                            hpcEval
                      obtain ⟨p, e, hmem, hp, he⟩ := ih hm htail
                      refine ⟨p, e, by simp [hmem], hp, ?_⟩
                      cases hs : SExpr.sameAtom headValue tailValue with
                      | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          rw [symValToCek_decode_ite_of kind hc]
                          exact he
                      | true =>
                          have hvalue : headValue = tailValue :=
                            SExpr.sameAtom_eq_true hs
                          simp only [↓reduceIte]
                          rw [hvalue]
                          exact he
                  | true =>
                      have hp : pcHolds m headPc = true := by
                        simp [pcHolds, Moist.SMT.Semantics.evalBoolIs,
                          Moist.SMT.Semantics.evalBool?, hc]
                      refine ⟨headPc, headValue, by simp, hp, ?_⟩
                      cases hs : SExpr.sameAtom headValue tailValue with
                      | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          rw [symValToCek_decode_ite_of kind hc]
                          simp
                      | true => simp
              | int i | string i | bytes i | data i | dataList i
              | dataPairList i | val i | valList i | g1 i | g2 i | ml i =>
                  rw [Moist.SMT.Semantics.eval_ite_exact, hc] at hpcEval
                  contradiction

private theorem genericMergedOkOutcome_active {kind : CompactKind} {m : SmtSem.Model}
    {outs : List Outcome} {pc : SExpr} {v : SymVal}
    (hmem : Outcome.ok pc v ∈
      (match mergeEncodedOks (encodedOks kind outs) with
      | none => []
      | some (mergedPc, mergedValue) =>
          [Outcome.ok mergedPc (mergedDecode kind mergedValue)]))
    (hpc : pcHolds m pc = true) :
    ∃ sourcePc sourceValue,
      Outcome.ok sourcePc sourceValue ∈ outs ∧
      pcHolds m sourcePc = true ∧
      symValToCek? m v = symValToCek? m sourceValue ∧
      symValNoOpaqueForSoundness v =
        symValNoOpaqueForSoundness sourceValue := by
  cases hm : mergeEncodedOks (encodedOks kind outs) with
  | none => simp [hm] at hmem
  | some merged =>
      rcases merged with ⟨mergedPc, mergedValue⟩
      simp [hm] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      obtain ⟨sourcePc, sourceExpr, hentry, hsourcePc, hsourceEq⟩ :=
        mergeEncodedOks_active kind hm hpc
      obtain ⟨sourceValue, hsourceMem, hencode⟩ := encodedOks_mem hentry
      have hdecode := compactDecode_encode_toCek (m := m) hencode
      have hdecodeNo := compactDecode_encode_noOpaque hencode
      refine ⟨sourcePc, sourceValue, hsourceMem, hsourcePc, ?_, ?_⟩
      · exact (mergedDecode_toCek m kind mergedValue).trans
          (hsourceEq.trans hdecode)
      · exact (mergedDecode_noOpaque kind mergedValue).trans
          ((compactDecode_noOpaque_irrel kind mergedValue sourceExpr).trans hdecodeNo)

theorem mergedOkOutcome_active {kind : CompactKind} {m : SmtSem.Model}
    {outs : List Outcome} {pc : SExpr} {v : SymVal}
    (hmem : Outcome.ok pc v ∈ mergedOkOutcome kind outs)
    (hpc : pcHolds m pc = true) :
    ∃ sourcePc sourceValue,
      Outcome.ok sourcePc sourceValue ∈ outs ∧
      pcHolds m sourcePc = true ∧
      symValToCek? m v = symValToCek? m sourceValue ∧
      symValNoOpaqueForSoundness v =
        symValNoOpaqueForSoundness sourceValue := by
  cases kind with
  | bool =>
      apply genericMergedOkOutcome_active (kind := .bool)
        (by simpa [mergedOkOutcome] using hmem) hpc
  | integer =>
      apply genericMergedOkOutcome_active (kind := .integer)
        (by simpa [mergedOkOutcome] using hmem) hpc
  | unit =>
      apply genericMergedOkOutcome_active (kind := .unit)
        (by simpa [mergedOkOutcome] using hmem) hpc
  | bytes =>
      apply genericMergedOkOutcome_active (kind := .bytes)
        (by simpa [mergedOkOutcome] using hmem) hpc
  | string =>
      apply genericMergedOkOutcome_active (kind := .string)
        (by simpa [mergedOkOutcome] using hmem) hpc
  | data =>
      apply genericMergedOkOutcome_active (kind := .data)
        (by simpa [mergedOkOutcome] using hmem) hpc
  | dataList =>
      apply genericMergedOkOutcome_active (kind := .dataList)
        (by simpa [mergedOkOutcome] using hmem) hpc
  | pairDataList =>
      apply genericMergedOkOutcome_active (kind := .pairDataList)
        (by simpa [mergedOkOutcome] using hmem) hpc
  | array =>
      apply genericMergedOkOutcome_active (kind := .array)
        (by simpa [mergedOkOutcome] using hmem) hpc
  | dyn =>
      apply genericMergedOkOutcome_active (kind := .dyn)
        (by simpa [mergedOkOutcome] using hmem) hpc
  | constList =>
      unfold mergedOkOutcome at hmem
      cases hm : mergeEncodedConstListOks (encodedConstListOks outs) with
      | none => simp [hm] at hmem
      | some merged =>
          simp [hm] at hmem
          rcases hmem with ⟨rfl, rfl⟩
          have hMapped := congrArg (Option.map EncodedConstListOk.erase) hm
          rw [mergeEncodedConstListOks_erase] at hMapped
          simp only [Option.map_some] at hMapped
          rw [encodedConstListOks_erase] at hMapped
          obtain ⟨sourcePc, sourceExpr, hentry, hsourcePc, hsourceEq⟩ :=
            mergeEncodedOks_active .constList hMapped hpc
          obtain ⟨sourceValue, hsourceMem, hencode⟩ := encodedOks_mem hentry
          have hdecode := compactDecode_encode_toCek (m := m) hencode
          have hdecodeNo := compactDecode_encode_noOpaque hencode
          refine ⟨sourcePc, sourceValue, hsourceMem, hsourcePc, ?_, ?_⟩
          · exact hsourceEq.trans hdecode
          · exact (compactDecode_noOpaque_irrel .constList
              merged.value sourceExpr).trans hdecodeNo

theorem compactedOkOutcomes_active_ok {m : SmtSem.Model} {outs : List Outcome}
    {pc : SExpr} {v : SymVal}
    (hmem : Outcome.ok pc v ∈ compactedOkOutcomes outs)
    (hpc : pcHolds m pc = true) :
    ∃ sourcePc sourceValue,
      Outcome.ok sourcePc sourceValue ∈ outs ∧
      pcHolds m sourcePc = true ∧
      symValToCek? m v = symValToCek? m sourceValue ∧
      symValNoOpaqueForSoundness v =
        symValNoOpaqueForSoundness sourceValue := by
  rw [compactedOkOutcomes] at hmem
  rcases List.mem_append.mp hmem with hmerged | hnon
  · rcases List.mem_flatMap.mp hmerged with ⟨kind, _, hkind⟩
    exact mergedOkOutcome_active hkind hpc
  · exact ⟨pc, v, nonEncodedOks_mem hnon, hpc, rfl, rfl⟩

theorem ok_not_mem_mergedErrorOutcome {outs : List Outcome} {pc : SExpr}
    {v : SymVal} : Outcome.ok pc v ∉ mergedErrorOutcome outs := by
  unfold mergedErrorOutcome
  split <;> simp

theorem ok_not_mem_mergedTimeoutOutcome {outs : List Outcome} {pc : SExpr}
    {v : SymVal} : Outcome.ok pc v ∉ mergedTimeoutOutcome outs := by
  unfold mergedTimeoutOutcome
  split <;> simp

theorem error_not_mem_mergedOkOutcome {kind : CompactKind}
    {outs : List Outcome} {pc : SExpr} :
    Outcome.error pc ∉ mergedOkOutcome kind outs := by
  intro hmem
  cases kind <;> simp only [mergedOkOutcome] at hmem
  all_goals split at hmem <;> simp_all

theorem timeout_not_mem_mergedOkOutcome {kind : CompactKind}
    {outs : List Outcome} {pc : SExpr} :
    Outcome.timeout pc ∉ mergedOkOutcome kind outs := by
  intro hmem
  cases kind <;> simp only [mergedOkOutcome] at hmem
  all_goals split at hmem <;> simp_all

theorem error_not_mem_nonEncodedOks {outs : List Outcome} {pc : SExpr} :
    Outcome.error pc ∉ nonEncodedOks outs := by
  induction outs with
  | nil => simp [nonEncodedOks]
  | cons out outs ih =>
      cases out with
      | ok p v => cases he : compactKind? v <;> simp [nonEncodedOks, he, ih]
      | error p => simp [nonEncodedOks, ih]
      | timeout p => simp [nonEncodedOks, ih]

theorem timeout_not_mem_nonEncodedOks {outs : List Outcome} {pc : SExpr} :
    Outcome.timeout pc ∉ nonEncodedOks outs := by
  induction outs with
  | nil => simp [nonEncodedOks]
  | cons out outs ih =>
      cases out with
      | ok p v => cases he : compactKind? v <;> simp [nonEncodedOks, he, ih]
      | error p => simp [nonEncodedOks, ih]
      | timeout p => simp [nonEncodedOks, ih]

theorem error_not_mem_compactedOkOutcomes {outs : List Outcome} {pc : SExpr} :
    Outcome.error pc ∉ compactedOkOutcomes outs := by
  simp [compactedOkOutcomes, error_not_mem_mergedOkOutcome,
    error_not_mem_nonEncodedOks]

theorem timeout_not_mem_compactedOkOutcomes {outs : List Outcome} {pc : SExpr} :
    Outcome.timeout pc ∉ compactedOkOutcomes outs := by
  simp [compactedOkOutcomes, timeout_not_mem_mergedOkOutcome,
    timeout_not_mem_nonEncodedOks]

theorem error_not_mem_mergedTimeoutOutcome {outs : List Outcome} {pc : SExpr} :
    Outcome.error pc ∉ mergedTimeoutOutcome outs := by
  unfold mergedTimeoutOutcome
  split <;> simp

theorem timeout_not_mem_mergedErrorOutcome {outs : List Outcome} {pc : SExpr} :
    Outcome.timeout pc ∉ mergedErrorOutcome outs := by
  unfold mergedErrorOutcome
  split <;> simp

/-- A syntactically false path is inactive in the executable partial SMT
semantics, so every active outcome survives dead-path pruning exactly. -/
theorem mem_pruneFalseOutcomes_iff_of_active {m : SmtSem.Model}
    {outs : List Outcome} {out : Outcome}
    (hactive : pcHolds m out.pc = true) :
    out ∈ pruneFalseOutcomes outs ↔ out ∈ outs := by
  have hnotFalse : Expr.isFalse out.pc = false := by
    cases hfalse : Expr.isFalse out.pc with
    | false => rfl
    | true =>
        rw [Moist.SMT.Semantics.isFalse_eq_true] at hfalse
        rw [hfalse] at hactive
        simp [pcHolds, SmtSem.evalBoolIs, Moist.SMT.Semantics.evalBoolIs,
          Moist.SMT.Semantics.evalBool?, Moist.SMT.Semantics.eval] at hactive
  simp [pruneFalseOutcomes, hnotFalse]

theorem mem_of_mem_pruneFalseOutcomes {outs : List Outcome} {out : Outcome}
    (hmem : out ∈ pruneFalseOutcomes outs) : out ∈ outs := by
  exact (List.mem_filter.mp hmem).1

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
  · rcases List.mem_append.mp hprefix with hok | herr
    · obtain ⟨sourcePc, sourceValue, hsourceMem, hsourcePc,
          hsourceValue, hsourceOpaque⟩ :=
        compactedOkOutcomes_active_ok hok hpc
      exact ⟨sourcePc, sourceValue,
        mem_of_mem_pruneFalseOutcomes hsourceMem, hsourcePc,
        hsourceValue, hsourceOpaque⟩
    · exact False.elim (ok_not_mem_mergedErrorOutcome herr)
  · exact False.elim (ok_not_mem_mergedTimeoutOutcome htimeout)

theorem compactOutcomes_active_error {m : SmtSem.Model} {outs : List Outcome}
    {pc : SExpr}
    (hmem : Outcome.error pc ∈ compactOutcomes outs)
    (hpc : pcHolds m pc = true) :
    ∃ sourcePc, Outcome.error sourcePc ∈ outs ∧
      pcHolds m sourcePc = true := by
  rw [compactOutcomes] at hmem
  rcases List.mem_append.mp hmem with hprefix | htimeout
  · rcases List.mem_append.mp hprefix with hok | herr
    · exact False.elim (error_not_mem_compactedOkOutcomes hok)
    · unfold mergedErrorOutcome at herr
      cases hp : errorPcs (pruneFalseOutcomes outs) with
      | nil => simp [hp] at herr
      | cons p ps =>
          simp [hp] at herr
          subst pc
          obtain ⟨sourcePc, hsourceMem, hsourceActive⟩ :=
            evalBoolIs_any_true (m := m) (by simpa [pcHolds] using hpc)
          exact ⟨sourcePc, mem_of_mem_pruneFalseOutcomes
              (errorPcs_mem (by simpa [hp] using hsourceMem)),
            by simpa [pcHolds] using hsourceActive⟩
  · exact False.elim (error_not_mem_mergedTimeoutOutcome htimeout)

/-- Compaction never invents a satisfiable timeout path. -/
theorem compactOutcomes_active_timeout {m : SmtSem.Model} {outs : List Outcome}
    {pc : SExpr}
    (hmem : Outcome.timeout pc ∈ compactOutcomes outs)
    (hpc : pcHolds m pc = true) :
    ∃ sourcePc, Outcome.timeout sourcePc ∈ outs ∧
      pcHolds m sourcePc = true := by
  rw [compactOutcomes] at hmem
  rcases List.mem_append.mp hmem with hprefix | htimeout
  · rcases List.mem_append.mp hprefix with hok | herr
    · exact False.elim (timeout_not_mem_compactedOkOutcomes hok)
    · exact False.elim (timeout_not_mem_mergedErrorOutcome herr)
  · unfold mergedTimeoutOutcome at htimeout
    cases hp : timeoutPcs (pruneFalseOutcomes outs) with
    | nil => simp [hp] at htimeout
    | cons p ps =>
        simp [hp] at htimeout
        subst pc
        obtain ⟨sourcePc, hsourceMem, hsourceActive⟩ :=
          evalBoolIs_any_true (m := m) (by simpa [pcHolds] using hpc)
        exact ⟨sourcePc, mem_of_mem_pruneFalseOutcomes
            (timeoutPcs_mem (by simpa [hp] using hsourceMem)),
          by simpa [pcHolds] using hsourceActive⟩

end Moist.SMT.UPLC.Soundness
