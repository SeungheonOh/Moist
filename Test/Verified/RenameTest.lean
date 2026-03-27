import Moist.Verified.RenameBase
import Moist.Verified.ClosedAt

namespace Test.Verified.RenameTest

open Moist.Verified
open Moist.Plutus.Term
open Moist.CEK

/-! # Concrete tests for the renaming infrastructure

These tests exercise `liftRename`, `renameTerm`, `shiftRename`,
and `EnvRelV` on concrete examples to build confidence in the
definitions before relying on them in the bisimulation proofs.
-/

/-! ## liftRename tests -/

-- Position 0 (unused) is preserved
example : liftRename id 0 = 0 := rfl
example : liftRename (fun n => n + 1) 0 = 0 := rfl

-- Position 1 (new binder) is always preserved
example : liftRename id 1 = 1 := rfl
example : liftRename (fun n => n + 1) 1 = 1 := rfl
example : liftRename (fun n => n + 5) 1 = 1 := rfl

-- Position n+2 maps through sigma: liftRename sigma (n+2) = sigma(n+1) + 1
-- For id: liftRename id 2 = id 1 + 1 = 2
example : liftRename id 2 = 2 := rfl
example : liftRename id 3 = 3 := rfl
example : liftRename id 4 = 4 := rfl

-- For shift by 1: liftRename (. + 1) 2 = (1 + 1) + 1 = 3
example : liftRename (· + 1) 2 = 3 := rfl
example : liftRename (· + 1) 3 = 4 := rfl
example : liftRename (· + 1) 4 = 5 := rfl

-- For shiftRename 1: every n >= 1 maps to n+1
example : shiftRename 1 0 = 0 := rfl
example : shiftRename 1 1 = 2 := rfl
example : shiftRename 1 2 = 3 := rfl
example : shiftRename 1 3 = 4 := rfl

-- liftRename of shiftRename 1 should equal shiftRename 2
-- (under a binder, the gap position shifts up by 1)
example : liftRename (shiftRename 1) 0 = shiftRename 2 0 := rfl
example : liftRename (shiftRename 1) 1 = shiftRename 2 1 := rfl
example : liftRename (shiftRename 1) 2 = shiftRename 2 2 := rfl
example : liftRename (shiftRename 1) 3 = shiftRename 2 3 := rfl
example : liftRename (shiftRename 1) 4 = shiftRename 2 4 := rfl

-- Full functional equality (already proved, but verify it reduces)
theorem liftRename_shiftRename1_eq : liftRename (shiftRename 1) = shiftRename 2 :=
  liftRename_shiftRename (by omega)

/-! ## renameTerm tests -/

-- Identity renaming is a no-op
example : renameTerm id (.Var 3) = .Var 3 := rfl
example : renameTerm id (.Error) = .Error := rfl

-- Var renaming: renameTerm sigma (Var n) = Var (sigma n)
example : renameTerm (· + 1) (.Var 0) = .Var 1 := rfl
example : renameTerm (· + 1) (.Var 1) = .Var 2 := rfl
example : renameTerm (· + 1) (.Var 5) = .Var 6 := rfl

-- shiftRename 1 on Var: shifts indices >= 1 by 1
example : renameTerm (shiftRename 1) (.Var 0) = .Var 0 := rfl
example : renameTerm (shiftRename 1) (.Var 1) = .Var 2 := rfl
example : renameTerm (shiftRename 1) (.Var 2) = .Var 3 := rfl

-- Lam: body gets liftRename applied
-- renameTerm (shift 1) (Lam 0 (Var 1)) = Lam 0 (renameTerm (liftRename (shift 1)) (Var 1))
-- liftRename (shiftRename 1) 1 = 1 (new binder stays)
-- So result: Lam 0 (Var 1)
example : renameTerm (shiftRename 1) (.Lam 0 (.Var 1)) = .Lam 0 (.Var 1) := rfl

-- renameTerm (shift 1) (Lam 0 (Var 2)) = Lam 0 (Var 3)
-- liftRename (shiftRename 1) 2 = shiftRename 1 1 + 1 = 2 + 1 = 3
example : renameTerm (shiftRename 1) (.Lam 0 (.Var 2)) = .Lam 0 (.Var 3) := rfl

-- Apply: both sides renamed
example : renameTerm (· + 1) (.Apply (.Var 1) (.Var 2)) = .Apply (.Var 2) (.Var 3) := rfl

-- Nested lambda: two layers of liftRename
-- Lam 0 (Lam 0 (Var 3)) under shift 1:
-- outer body: renameTerm (liftRename (shift 1)) (Lam 0 (Var 3))
-- inner body: renameTerm (liftRename (liftRename (shift 1))) (Var 3)
-- liftRename (liftRename (shiftRename 1)) 3
--   = liftRename (shiftRename 1) 2 + 1
--   = (shiftRename 1 1 + 1) + 1
--   = (2 + 1) = 3, then + 1 = 4
example : renameTerm (shiftRename 1) (.Lam 0 (.Lam 0 (.Var 3))) =
    .Lam 0 (.Lam 0 (.Var 4)) := rfl

-- Var 1 and Var 2 inside nested lambda are preserved/shifted correctly
-- liftRename (liftRename (shift 1)) 1 = 1 (innermost binder)
-- liftRename (liftRename (shift 1)) 2 = liftRename (shift 1) 1 + 1 = 1 + 1 = 2 (outer binder)
example : renameTerm (shiftRename 1) (.Lam 0 (.Lam 0 (.Var 1))) =
    .Lam 0 (.Lam 0 (.Var 1)) := rfl
example : renameTerm (shiftRename 1) (.Lam 0 (.Lam 0 (.Var 2))) =
    .Lam 0 (.Lam 0 (.Var 2)) := rfl

-- Force and Delay propagate
example : renameTerm (· + 1) (.Force (.Var 1)) = .Force (.Var 2) := rfl
example : renameTerm (· + 1) (.Delay (.Var 1)) = .Delay (.Var 2) := rfl

-- Constr and Case propagate
example : renameTerm (· + 1) (.Constr 0 [.Var 1, .Var 2]) =
    .Constr 0 [.Var 2, .Var 3] := rfl
example : renameTerm (· + 1) (.Case (.Var 1) [.Var 2, .Var 3]) =
    .Case (.Var 2) [.Var 3, .Var 4] := rfl

/-! ## closedAt tests -/

-- closedAt is defined in a mutual block so kernel reduction is limited.
-- We use native_decide for concrete computations.
-- Var n is closedAt d iff n <= d
example : closedAt 0 (.Var 0) = true := by native_decide
example : closedAt 0 (.Var 1) = false := by native_decide
example : closedAt 1 (.Var 1) = true := by native_decide
example : closedAt 2 (.Var 1) = true := by native_decide
example : closedAt 2 (.Var 3) = false := by native_decide

-- Lam increments depth by 1
example : closedAt 0 (.Lam 0 (.Var 1)) = true := by native_decide
example : closedAt 0 (.Lam 0 (.Var 2)) = false := by native_decide

-- Constants, builtins, Error are always closed
example : closedAt 0 (.Error) = true := by native_decide
example : closedAt 0 (.Builtin .AddInteger) = true := by native_decide

/-! ## CekEnv.lookup tests (verifying 1-based indexing) -/

private def intVal (n : Int) : CekValue := .VCon (.Integer n)

-- Empty env always returns none
example : CekEnv.lookup .nil 0 = none := rfl
example : CekEnv.lookup .nil 1 = none := rfl
example : CekEnv.lookup .nil 5 = none := rfl

-- Position 0 always returns none (unused sentinel)
example : CekEnv.lookup (.cons (intVal 1) .nil) 0 = none := rfl

-- Position 1 returns the head (most recent binding)
example : CekEnv.lookup (.cons (intVal 1) .nil) 1 = some (intVal 1) := rfl

-- Position 2 in a two-element env returns the second (earlier) binding
example : CekEnv.lookup (.cons (intVal 1) (.cons (intVal 2) .nil)) 2 =
    some (intVal 2) := rfl

-- Position 3 in a two-element env is out of bounds
example : CekEnv.lookup (.cons (intVal 1) (.cons (intVal 2) .nil)) 3 = none := rfl

-- extend puts the new value at position 1
example : CekEnv.lookup (CekEnv.extend .nil (intVal 99)) 1 = some (intVal 99) := rfl

-- extend preserves old position 1 at new position 2
example : CekEnv.lookup (CekEnv.extend (.cons (intVal 42) .nil) (intVal 99)) 2 =
    some (intVal 42) := rfl

/-! ## EnvRelV construction tests -/

-- EnvRelV id 0 is vacuously true for any pair of environments
-- (no positions in range 1..0)
theorem envRelV_id_zero_any : EnvRelV id 0 (.cons (intVal 1) .nil) .nil :=
  .mk (fun n hn hle => absurd (Nat.lt_of_lt_of_le hn hle) (Nat.lt_irrefl 0))
      (fun n hn hle => absurd (Nat.lt_of_lt_of_le hn hle) (Nat.lt_irrefl 0))
      rfl

-- EnvRelV id 1 for identical single-element envs
theorem envRelV_id_one_same :
    let env := CekEnv.cons (intVal 42) .nil
    EnvRelV id 1 env env :=
  envRelV_refl 1 _

-- Verify the dead-let EnvRelV construction from the theorem:
-- EnvRelV id 0 (cons ve nil) nil is vacuously true
theorem dead_let_envRelV :
    EnvRelV id 0 (CekEnv.cons (intVal 99) .nil) .nil :=
  .mk (fun n hn hle => absurd (Nat.lt_of_lt_of_le hn hle) (Nat.lt_irrefl 0))
      (fun n hn hle => absurd (Nat.lt_of_lt_of_le hn hle) (Nat.lt_irrefl 0))
      rfl

/-! ## envRelV_extend tests -/

-- Starting from EnvRelV id 0 env env, extending with identical values
-- should give EnvRelV (liftRename id) 1 (env.extend v) (env.extend v)
theorem extend_preserves_refl :
    let v := intVal 1
    let env := CekEnv.nil
    EnvRelV (liftRename id) 1 (env.extend v) (env.extend v) :=
  envRelV_extend id 0 .nil .nil _ _ (envRelV_refl 0 .nil) .refl

-- After extending, position 1 in both envs should be the new value
-- This follows from the EnvRelV witness above: envRelV_elim at n=1
-- gives LookupRelV (some v) (some v)
theorem extend_lookup_pos1 :
    let v := intVal 1
    let env1 := CekEnv.nil.extend v
    let env2 := CekEnv.nil.extend v
    LookupRelV (env1.lookup 1) (env2.lookup (liftRename id 1)) := by
  have h := extend_preserves_refl
  exact envRelV_elim h (by omega) (by omega)

-- Extending a 1-element env: EnvRelV (liftRename id) 2 on two-element envs
theorem extend_two_elements :
    let v1 := intVal 10
    let v2 := intVal 20
    let env := CekEnv.cons v1 .nil
    EnvRelV (liftRename id) 2 (env.extend v2) (env.extend v2) :=
  envRelV_extend id 1 _ _ _ _ (envRelV_refl 1 _) .refl

/-! ## shiftRename composition with liftRename -/

-- Verify iterated lifting: under two binders, shiftRename 1 becomes shiftRename 3
theorem double_lift_shift :
    liftRename (liftRename (shiftRename 1)) = shiftRename 3 := by
  rw [liftRename_shiftRename (by omega : (1 : Nat) >= 1)]
  rw [liftRename_shiftRename (by omega : (2 : Nat) >= 1)]

-- Check specific values of the double-lifted shift
example : liftRename (liftRename (shiftRename 1)) 0 = 0 := rfl
example : liftRename (liftRename (shiftRename 1)) 1 = 1 := rfl
example : liftRename (liftRename (shiftRename 1)) 2 = 2 := rfl
example : liftRename (liftRename (shiftRename 1)) 3 = 4 := rfl
example : liftRename (liftRename (shiftRename 1)) 4 = 5 := rfl

/-! ## renameTerm_id is the identity on all terms -/

-- These verify that renameTerm id really is the identity at the term level
example : renameTerm id (.Apply (.Lam 0 (.Var 1)) (.Var 2)) =
    .Apply (.Lam 0 (.Var 1)) (.Var 2) := by
  rw [renameTerm_id]

/-! ## renameTermList tests -/

example : renameTermList (· + 1) [] = ([] : List Term) := rfl
example : renameTermList (· + 1) [.Var 1] = [.Var 2] := rfl
example : renameTermList (· + 1) [.Var 1, .Var 2] = [.Var 2, .Var 3] := rfl

-- Length preservation
example : (renameTermList (· + 1) [.Var 1, .Var 2, .Var 3]).length = 3 := rfl

/-! ## ValueRelV construction tests -/

-- VCon values are related when they carry the same constant
example : ValueRelV (intVal 42) (intVal 42) := .vcon

-- Any value is related to itself via refl
example : ValueRelV (intVal 42) (intVal 42) := .refl

-- VLam with id renaming: body stays the same (after renameTerm id = id)
theorem vlam_id_example :
    let body := Term.Var 1
    let env := CekEnv.nil
    ValueRelV (.VLam body env) (.VLam (renameTerm (liftRename id) body) env) := by
  simp only [liftRename_id, renameTerm_id]
  exact .refl

-- ListValueRelV for empty lists
example : ListValueRelV ([] : List CekValue) [] := .nil

-- ListValueRelV for singleton
example : ListValueRelV [intVal 1] [intVal 1] := .cons .vcon .nil

/-! ## LookupRelV tests -/

example : LookupRelV (none : Option CekValue) none := .bothNone
example : LookupRelV (some (intVal 1)) (some (intVal 1)) := .bothSome .vcon

end Test.Verified.RenameTest
