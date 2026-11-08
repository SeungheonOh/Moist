import Moist.Verified.TermObsRefinesWF
import Moist.Verified.FundamentalRefines

variable [sv : Moist.CEK.SemVariant]

/-! # Well-formedness instance of the fundamental theorem

`ftlr_wf`: every closed term self-refines under the well-formedness-guarded
relation; the `wfGuard`, `r₁ = r₂ = id` instance of `renameRefinesG`.
-/

namespace Moist.Verified.FundamentalRefinesWF

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified
open Moist.Verified.Contextual.Guarded
open Moist.Verified.TermObsRefinesWF
open Moist.Verified.FundamentalRefines
open Moist.Verified.StepWellFormed (StateWellFormed)

theorem ftlr_wf (d : Nat) (t : Term) (ht : closedAt d t = true) :
    OpenRefinesWF d t t := by
  intro k j _ ρ₁ ρ₂ henv henv_wf_l hlen_l henv_wf_r hlen_r i hi π₁ π₂ hwf_π₁ hwf_π₂ hπ
  have ht' : closedAt d (renameTerm id t) = true := by rw [renameTerm_id]; exact ht
  have h := renameRefinesG wfGuard id id is0preserving_id is0preserving_id d t ht j
    (renameEnvRef2_id henv) i hi π₁ π₂ ⟨hwf_π₁, hwf_π₂, hπ⟩
    (StateWellFormed.compute hwf_π₁ henv_wf_l hlen_l ht')
    (StateWellFormed.compute hwf_π₂ henv_wf_r hlen_r ht')
  rwa [renameTerm_id] at h

end Moist.Verified.FundamentalRefinesWF
