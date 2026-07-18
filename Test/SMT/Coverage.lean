import Moist.SMT.Soundness

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term

def outcomeActive (m : SmtSem.Model) (out : Outcome) : Prop :=
  SmtSem.evalBoolIs m out.pc true = true

def outcomesCovered (m : SmtSem.Model) (outs : List Outcome) : Prop :=
  ∃ out, out ∈ outs ∧ outcomeActive m out

theorem outcomesCovered_ok (m : SmtSem.Model) (v : SymVal) :
    outcomesCovered m (ok v) := by
  exact ⟨Outcome.ok SExpr.trueE v, by simp [ok], by simp [outcomeActive, Outcome.pc]⟩

theorem outcomesCovered_err (m : SmtSem.Model) : outcomesCovered m err := by
  exact ⟨Outcome.error SExpr.trueE, by simp [err], by simp [outcomeActive, Outcome.pc]⟩

theorem outcomesCovered_timeout (m : SmtSem.Model) : outcomesCovered m timeout := by
  exact ⟨Outcome.timeout SExpr.trueE, by simp [timeout], by simp [outcomeActive, Outcome.pc]⟩

theorem outcomesCovered_mapPc {m : SmtSem.Model} {g : SExpr} {outs : List Outcome}
    (hg : SmtSem.evalBoolIs m g true = true)
    (houts : outcomesCovered m outs) : outcomesCovered m (mapPc g outs) := by
  rcases houts with ⟨out, hout, hactive⟩
  refine ⟨Outcome.guard g out, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨out, hout, rfl⟩
  · cases out <;>
      simpa [outcomeActive, Outcome.pc, Outcome.guard] using
        (Moist.SMT.Semantics.evalBoolIs_and_true m g _).mpr ⟨hg, hactive⟩

theorem outcomesCovered_bindOk {m : SmtSem.Model} {pc : SExpr} {v : SymVal}
    {k : SymVal → List Outcome}
    (hpc : SmtSem.evalBoolIs m pc true = true)
    (hk : outcomesCovered m (k v)) : outcomesCovered m (bindOk pc v k) := by
  by_cases hfalse : pc = .bool false
  · subst pc
    simp [Moist.SMT.Semantics.evalBoolIs, Moist.SMT.Semantics.evalBool?,
      Moist.SMT.Semantics.eval] at hpc
  · simp only [bindOk]
    exact outcomesCovered_mapPc (m := m) (g := pc) (outs := k v) hpc hk

theorem outcomesCovered_bindOut {m : SmtSem.Model} {outs : List Outcome}
    {k : SymVal → List Outcome}
    (houts : outcomesCovered m outs)
    (hk : ∀ v, outcomesCovered m (k v)) : outcomesCovered m (bindOut outs k) := by
  rcases houts with ⟨out, hout, hactive⟩
  cases out with
  | error pc =>
      by_cases hfalse : pc = .bool false
      · subst pc
        simp [outcomeActive, Outcome.pc, Moist.SMT.Semantics.evalBoolIs,
          Moist.SMT.Semantics.evalBool?, Moist.SMT.Semantics.eval] at hactive
      · have hinner : Outcome.error pc ∈ carryError pc := by
          cases pc <;> simp [carryError] at hfalse ⊢
        exact ⟨Outcome.error pc,
          by simp only [bindOut, List.mem_flatMap];
             exact ⟨Outcome.error pc, hout, hinner⟩,
          hactive⟩
  | timeout pc =>
      by_cases hfalse : pc = .bool false
      · subst pc
        simp [outcomeActive, Outcome.pc, Moist.SMT.Semantics.evalBoolIs,
          Moist.SMT.Semantics.evalBool?, Moist.SMT.Semantics.eval] at hactive
      · have hinner : Outcome.timeout pc ∈ carryTimeout pc := by
          cases pc <;> simp [carryTimeout] at hfalse ⊢
        exact ⟨Outcome.timeout pc,
          by simp only [bindOut, List.mem_flatMap];
             exact ⟨Outcome.timeout pc, hout, hinner⟩,
          hactive⟩
  | ok pc v =>
      have hbound := outcomesCovered_bindOk (m := m) (pc := pc) (v := v)
        (k := k) hactive (hk v)
      rcases hbound with ⟨inner, hinner, hinnerActive⟩
      exact ⟨inner,
        by simp only [bindOut, List.mem_flatMap]; exact ⟨Outcome.ok pc v, hout, hinner⟩,
        hinnerActive⟩

end Moist.SMT.UPLC.Soundness
