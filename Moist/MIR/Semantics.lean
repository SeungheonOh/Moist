import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.MIR.Lower
import Moist.MIR.LowerTotal

namespace Moist.MIR.Semantics

open Moist.CEK
open Moist.Plutus.Term (Term Const)

/-! # Behavioral Equivalence via CEK Machine

All definitions use the total `step` function (not partial `eval`),
so they are usable in proofs.
-/

/-- Apply `step` n times. -/
def steps : Nat → State → State
  | 0, s => s
  | n + 1, s => steps n (step s)

/-- A state reaches value `v` if iterated stepping produces `halt v`. -/
def Reaches (s : State) (v : CekValue) : Prop :=
  ∃ n : Nat, steps n s = .halt v

/-! ## Determinism

The CEK machine is deterministic: `halt` is a fixed point of `step`,
so if two step sequences from the same state both reach `halt`,
they reach the same value. -/

theorem step_halt (v : CekValue) : step (.halt v) = .halt v := rfl
theorem step_error : step .error = .error := rfl

theorem steps_halt (v : CekValue) (n : Nat) : steps n (.halt v) = .halt v := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [steps, step_halt, ih]

private theorem reaches_unique_aux : ∀ (m n : Nat) (s : State) (v w : CekValue),
    steps m s = .halt v → steps n s = .halt w → v = w := by
  intro m
  induction m with
  | zero =>
    intro n s v w hm hn
    dsimp [steps] at hm; subst hm
    rw [steps_halt] at hn; exact State.halt.inj hn
  | succ m ih =>
    intro n s v w hm hn
    dsimp [steps] at hm
    cases n with
    | zero =>
      dsimp [steps] at hn; subst hn
      simp only [step_halt] at hm; rw [steps_halt] at hm
      exact (State.halt.inj hm).symm
    | succ n =>
      dsimp [steps] at hn
      exact ih n (step s) v w hm hn

theorem reaches_unique {s : State} {v w : CekValue}
    (hv : Reaches s v) (hw : Reaches s w) : v = w :=
  let ⟨m, hm⟩ := hv; let ⟨n, hn⟩ := hw; reaches_unique_aux m n s v w hm hn

/-! ## Step-Indexed Value Equivalence -/

mutual
  def ValueEq : Nat → CekValue → CekValue → Prop
    | 0, _, _ => True
    | _ + 1, .VCon c1, .VCon c2 => c1 = c2
    | k + 1, .VLam body1 env1, .VLam body2 env2 =>
      ∀ (arg : CekValue) (v1 v2 : CekValue),
        Reaches (.compute [] (env1.extend arg) body1) v1 →
        Reaches (.compute [] (env2.extend arg) body2) v2 →
        ValueEq k v1 v2
    | k + 1, .VConstr tag1 fields1, .VConstr tag2 fields2 =>
      tag1 = tag2 ∧ ListValueEq k fields1 fields2
    | k + 1, .VDelay body1 env1, .VDelay body2 env2 =>
      ∀ (v1 v2 : CekValue),
        Reaches (.compute [] env1 body1) v1 →
        Reaches (.compute [] env2 body2) v2 →
        ValueEq k v1 v2
    | k + 1, .VBuiltin b1 args1 ea1, .VBuiltin b2 args2 ea2 =>
      b1 = b2 ∧ ListValueEq k args1 args2 ∧ ea1 = ea2
    | _, _, _ => False

  def ListValueEq : Nat → List CekValue → List CekValue → Prop
    | _, [], [] => True
    | k, a :: as, b :: bs => ValueEq k a b ∧ ListValueEq k as bs
    | _, _, _ => False
end

/-! ## Behavioral Equivalence -/

def lowerMIR (m : Expr) : Option Term := lowerTotal [] m

/-- Two closed MIR expressions are behaviorally equivalent if,
for any values they reach, those values are equivalent at all depths.
Holds vacuously when either side fails to lower.
Defined entirely using total functions (`steps`), so it's provable. -/
def BehEqClosed (m1 m2 : Expr) : Prop :=
  match lowerTotal [] m1, lowerTotal [] m2 with
  | some t1, some t2 =>
    ∀ (k : Nat) (v1 v2 : CekValue),
      Reaches (.compute [] .nil t1) v1 →
      Reaches (.compute [] .nil t2) v2 →
      ValueEq k v1 v2
  | _, _ => True

/-! ## Executable observation (for conformance testing only) -/

inductive Obs where
  | success : Term → Obs
  | failure : Obs

instance : BEq Obs where
  beq
    | .success t1, .success t2 => termEq t1 t2
    | .failure, .failure => true
    | _, _ => false

def obsOf : CekResult → Obs
  | .success v => .success (readbackValue v)
  | .failure => .failure
  | .outOfBudget => .failure

instance : ToString Obs where
  toString
    | .success t => s!"success({repr t})"
    | .failure => "failure"

end Moist.MIR.Semantics
