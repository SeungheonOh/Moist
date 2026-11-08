import Moist.Verified.GuardsSoundness.PushRel
import Moist.Verified.MIR.Hoist

variable [sv : Moist.CEK.SemVariant]

/-! # Shifting a term below a block of unused binders -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast

/-- `t` moved below `n` new binders. -/
def shiftN : Nat → Term → Term
  | 0, t => t
  | n + 1, t => shiftN n (renameTerm (shiftRename 1) t)

theorem lower_prepend_all : ∀ (bs : List VarId) (env : List VarId) (e : Expr),
    (∀ b ∈ bs, (freeVars e).contains b = false) →
    lowerTotalExpr (bs.reverse ++ env) e = (lowerTotalExpr env e).map (shiftN bs.length)
  | [], env, e, _ => by simp only [List.reverse_nil, List.nil_append, List.length_nil]; cases lowerTotalExpr env e <;> rfl
  | b :: bs, env, e, h => by
    have ih := lower_prepend_all bs (b :: env) e (fun b' hb' => h b' (.tail _ hb'))
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, ih,
      Moist.Verified.MIR.lowerTotalExpr_prepend_unused env b e (h b (.head _))]
    cases lowerTotalExpr env e <;> rfl

theorem closedAt_shiftN : ∀ (n : Nat) {d : Nat} {t : Term}, closedAt d t = true →
    closedAt (d + n) (shiftN n t) = true
  | 0, _, _, h => h
  | n + 1, d, t, h => by
    have h1 : closedAt (d + 1) (renameTerm (shiftRename 1) t) = true :=
      Moist.Verified.closedAt_renameTerm_shiftRename t d 1 (Nat.le_refl 1) (by omega) h
    simpa [Nat.add_assoc, Nat.add_comm 1 n] using closedAt_shiftN n h1

theorem extendAll_wf : ∀ (fs : List CekValue) {d : Nat} {ρ : CekEnv}, EnvWellFormed d ρ → d ≤ ρ.length →
    ValueListWellFormed fs →
    EnvWellFormed (d + fs.length) (extendAll ρ fs) ∧ d + fs.length ≤ (extendAll ρ fs).length
  | [], d, ρ, h, hl, _ => ⟨by simpa [extendAll] using h, by simpa [extendAll] using hl⟩
  | f :: fs, d, ρ, h, hl, .cons hf hfs => by
    obtain ⟨h1, hl1⟩ := envWellFormed_extend' h hl hf
    obtain ⟨h2, hl2⟩ := extendAll_wf fs h1 hl1 hfs
    exact ⟨by simpa [extendAll, Nat.add_assoc, Nat.add_comm 1] using h2,
      by simpa [extendAll, Nat.add_assoc, Nat.add_comm 1] using hl2⟩

/-- A term evaluates alike below a block of binders it does not mention. -/
theorem obsEq_shiftN : ∀ (fs : List CekValue) {d : Nat} {ρ : CekEnv} {π : Stack} {t : Term},
    EnvWellFormed d ρ → d ≤ ρ.length → ValueListWellFormed fs → StackWellFormed π →
    closedAt d t = true →
    ObsRefines (.compute π ρ t) (.compute π (extendAll ρ fs) (shiftN fs.length t)) ∧
    ObsRefines (.compute π (extendAll ρ fs) (shiftN fs.length t)) (.compute π ρ t)
  | [], _, _, _, _, _, _, _, _, _ => ⟨obsRefines_refl _, obsRefines_refl _⟩
  | f :: fs, d, ρ, π, t, henv, hlen, .cons hf hfs, hπ, hc => by
    have h1 := obsEq_shift (π := π) f henv hπ hc
    obtain ⟨henv1, hlen1⟩ := envWellFormed_extend' henv hlen hf
    have hc1 : closedAt (d + 1) (renameTerm (shiftRename 1) t) = true :=
      Moist.Verified.closedAt_renameTerm_shiftRename t d 1 (Nat.le_refl 1) (by omega) hc
    have h2 := obsEq_shiftN fs henv1 hlen1 hfs hπ hc1
    exact ⟨obsRefines_trans h1.1 h2.1, obsRefines_trans h2.2 h1.2⟩

end Moist.Verified.Guards
