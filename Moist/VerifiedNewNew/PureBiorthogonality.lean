import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.MIR.Lower
import Moist.MIR.LowerTotal
import Moist.Verified.ClosedAt

namespace Moist.Verified.Equivalence

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified (closedAt closedAtList)

--------------------------------------------------------------------------------
-- 1. OBSERVATIONS
--------------------------------------------------------------------------------

def steps : Nat → State → State
  | 0, s => s
  | n + 1, s => steps n (step s)

def Reaches (s s' : State) : Prop := ∃ n : Nat, steps n s = s'

/-- Standard, unbounded observational equivalence. -/
def ObsEq (c₁ c₂ : State) : Prop :=
  (∃ v₁, Reaches c₁ (.halt v₁)) ↔ (∃ v₂, Reaches c₂ (.halt v₂))

--------------------------------------------------------------------------------
-- 2. ORDER THEORY: BIVARIANT RELATIONS (mixed-variance, no step indexing)
--------------------------------------------------------------------------------

/-- The lattice type: binary relations on values. -/
abbrev ValRel := CekValue → CekValue → Prop

/-- The subset operator for relations (polymorphic in the carrier). -/
def Subset {α β : Sort _} (R₁ R₂ : α → β → Prop) : Prop :=
  ∀ v₁ v₂, R₁ v₁ v₂ → R₂ v₁ v₂

infix:50 " ⊆ " => Subset

/-- A bivariant operator: antitone in the first (negative) argument,
    monotone in the second (positive) argument. This is the mixed-variance
    replacement for the ordinary `Monotone` requirement of Knaster–Tarski.
    In untyped pure biorthogonality, the value relation must appear
    contravariantly in the argument-hypothesis of λ-values, so a plain
    monotone GFP does not exist — we need this weaker bivariance. -/
def Bivariant (F : ValRel → ValRel → ValRel) : Prop :=
  ∀ Rn Rn' Rp Rp' : ValRel,
    Rn' ⊆ Rn → Rp ⊆ Rp' →
    F Rn Rp ⊆ F Rn' Rp'

--------------------------------------------------------------------------------
-- 3. HAND-ROLLED PITTS / LEVY-STYLE BIVARIANT FIXED POINT
--------------------------------------------------------------------------------

/-- A (post-)fixed pair for a bivariant operator `F`: the positive component
    `Rp` is contained in `F Rn Rp`, and the negative component `Rn` absorbs
    `F Rp Rn`. Think of this as the pair-lattice analogue of `R ⊆ F R` for
    an ordinary monotone operator. -/
structure ClosedPair (F : ValRel → ValRel → ValRel) (Rp Rn : ValRel) : Prop where
  pos : Rp ⊆ F Rn Rp
  neg : F Rp Rn ⊆ Rn

/-- Positive component of the bivariant GFP: the union of positive components
    over all closed pairs. This is the *value equivalence* we care about. -/
def BivGFPPos (F : ValRel → ValRel → ValRel) : ValRel :=
  fun v₁ v₂ => ∃ Rp Rn : ValRel, ClosedPair F Rp Rn ∧ Rp v₁ v₂

/-- Negative component of the bivariant GFP: the intersection of negative
    components over all closed pairs. This is the dual relation used in
    hypothesis positions inside `F_Gen`. -/
def BivGFPNeg (F : ValRel → ValRel → ValRel) : ValRel :=
  fun v₁ v₂ => ∀ Rp Rn : ValRel, ClosedPair F Rp Rn → Rn v₁ v₂

/-- Coinduction (positive side): every closed pair's positive component sits
    inside the bivariant GFP. -/
theorem biv_coind_pos {F : ValRel → ValRel → ValRel} {Rp Rn : ValRel}
    (h : ClosedPair F Rp Rn) : Rp ⊆ BivGFPPos F := by
  intro v₁ v₂ hv
  exact ⟨Rp, Rn, h, hv⟩

/-- Coinduction (negative side): the bivariant GFP's negative component sits
    inside every closed pair's negative component. -/
theorem biv_coind_neg {F : ValRel → ValRel → ValRel} {Rp Rn : ValRel}
    (h : ClosedPair F Rp Rn) : BivGFPNeg F ⊆ Rn := by
  intro v₁ v₂ hv
  exact hv Rp Rn h

/-- The positive GFP is a post-fixed point under the canonical pairing. -/
theorem bivGFPPos_postfix {F : ValRel → ValRel → ValRel} (h_biv : Bivariant F) :
    BivGFPPos F ⊆ F (BivGFPNeg F) (BivGFPPos F) := by
  intro v₁ v₂ ⟨Rp, Rn, hC, hv⟩
  have h1 : F Rn Rp v₁ v₂ := hC.pos v₁ v₂ hv
  exact h_biv Rn (BivGFPNeg F) Rp (BivGFPPos F)
    (biv_coind_neg hC) (biv_coind_pos hC) v₁ v₂ h1

/-- The negative GFP absorbs `F` applied to the canonical positive/negative
    pair. -/
theorem bivGFPNeg_prefix {F : ValRel → ValRel → ValRel} (h_biv : Bivariant F) :
    F (BivGFPPos F) (BivGFPNeg F) ⊆ BivGFPNeg F := by
  intro v₁ v₂ hv Rp Rn hC
  have h1 : F Rp Rn v₁ v₂ :=
    h_biv (BivGFPPos F) Rp (BivGFPNeg F) Rn
      (biv_coind_pos hC) (biv_coind_neg hC) v₁ v₂ hv
  exact hC.neg v₁ v₂ h1

/-- The positive GFP is a pre-fixed point under the canonical pairing. -/
theorem bivGFPPos_prefix {F : ValRel → ValRel → ValRel} (h_biv : Bivariant F) :
    F (BivGFPNeg F) (BivGFPPos F) ⊆ BivGFPPos F := by
  intro a₁ a₂ ha
  -- Extension trick: (BivGFPPos ∪ {(a₁,a₂)}, BivGFPNeg) is itself a closed pair.
  let Rp' : ValRel := fun w₁ w₂ => BivGFPPos F w₁ w₂ ∨ (w₁ = a₁ ∧ w₂ = a₂)
  let Rn' : ValRel := BivGFPNeg F
  have h_pos_sub_Rp' : BivGFPPos F ⊆ Rp' := fun _ _ h => Or.inl h
  have hC' : ClosedPair F Rp' Rn' := by
    refine ⟨?_, ?_⟩
    · -- pos: Rp' ⊆ F Rn' Rp'
      intro w₁ w₂ hw
      rcases hw with h_gfp | ⟨e₁, e₂⟩
      · have h1 : F (BivGFPNeg F) (BivGFPPos F) w₁ w₂ :=
          bivGFPPos_postfix h_biv w₁ w₂ h_gfp
        exact h_biv (BivGFPNeg F) Rn' (BivGFPPos F) Rp'
          (fun _ _ h => h) h_pos_sub_Rp' w₁ w₂ h1
      · cases e₁; cases e₂
        exact h_biv (BivGFPNeg F) Rn' (BivGFPPos F) Rp'
          (fun _ _ h => h) h_pos_sub_Rp' a₁ a₂ ha
    · -- neg: F Rp' Rn' ⊆ Rn'
      intro w₁ w₂ hw
      -- Shrink Rp' back to BivGFPPos via antitone first slot.
      have h1 : F (BivGFPPos F) (BivGFPNeg F) w₁ w₂ :=
        h_biv Rp' (BivGFPPos F) Rn' (BivGFPNeg F)
          h_pos_sub_Rp' (fun _ _ h => h) w₁ w₂ hw
      exact bivGFPNeg_prefix h_biv w₁ w₂ h1
  exact ⟨Rp', Rn', hC', Or.inr ⟨rfl, rfl⟩⟩

/-- Unrolling theorem for the positive bivariant GFP. -/
theorem bivGFPPos_unroll {F : ValRel → ValRel → ValRel} (h_biv : Bivariant F) :
    ∀ v₁ v₂, BivGFPPos F v₁ v₂ ↔ F (BivGFPNeg F) (BivGFPPos F) v₁ v₂ := by
  intro v₁ v₂
  exact ⟨bivGFPPos_postfix h_biv v₁ v₂, bivGFPPos_prefix h_biv v₁ v₂⟩

--------------------------------------------------------------------------------
-- 4. PURE BIORTHOGONALITY (No Step-Indexing)
--------------------------------------------------------------------------------

/-- R^⊤ : The Stack Relation (Antitone) -/
def StackRel (R : ValRel) (π₁ π₂ : Stack) : Prop :=
  ∀ v₁ v₂, R v₁ v₂ → ObsEq (.ret π₁ v₁) (.ret π₂ v₂)

/-- R^⊤⊤ : The Expression Relation (Monotone) -/
def BehEq (R : ValRel) (ρ₁ ρ₂ : CekEnv) (t₁ t₂ : Term) : Prop :=
  ∀ π₁ π₂, StackRel R π₁ π₂ → ObsEq (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)

theorem stackRel_anti {R₁ R₂ : ValRel} (h_sub : R₁ ⊆ R₂) :
  StackRel R₂ ⊆ StackRel R₁ := by
  intro π₁ π₂ h v₁ v₂ hv
  exact h v₁ v₂ (h_sub v₁ v₂ hv)

theorem behEq_mono {R₁ R₂ : ValRel} (h_sub : R₁ ⊆ R₂)
  {ρ₁ ρ₂ : CekEnv} {t₁ t₂ : Term} :
  BehEq R₁ ρ₁ ρ₂ t₁ t₂ → BehEq R₂ ρ₁ ρ₂ t₁ t₂ := by
  intro h π₁ π₂ hπ
  exact h π₁ π₂ (stackRel_anti h_sub π₁ π₂ hπ)

--------------------------------------------------------------------------------
-- 5. THE RELATIONAL GENERATOR (Bivariant)
--------------------------------------------------------------------------------

def ListRel (R : α → α → Prop) : List α → List α → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ ListRel R as bs
  | _, _ => False

/-- ListRel is monotone in its relation argument. -/
theorem listRel_mono {α : Type _} {R₁ R₂ : α → α → Prop}
    (h : ∀ a b, R₁ a b → R₂ a b) :
    ∀ l₁ l₂, ListRel R₁ l₁ l₂ → ListRel R₂ l₁ l₂
  | [], [], _ => trivial
  | [], _ :: _, hl => hl.elim
  | _ :: _, [], hl => hl.elim
  | a :: as, b :: bs, hl => ⟨h a b hl.1, listRel_mono h as bs hl.2⟩

/-- One structural unrolling of the equivalence logic.
    Bivariant: `Rn` is the negative (argument-hypothesis) slot, `Rp` is the
    positive (conclusion) slot. -/
def F_Gen (Rn Rp : ValRel) : ValRel
  | .VCon c₁, .VCon c₂ => c₁ = c₂
  | .VLam b₁ ρ₁, .VLam b₂ ρ₂ =>
      ∀ arg₁ arg₂, Rn arg₁ arg₂ →
        BehEq Rp (ρ₁.extend arg₁) (ρ₂.extend arg₂) b₁ b₂
  | .VDelay b₁ ρ₁, .VDelay b₂ ρ₂ =>
      BehEq Rp ρ₁ ρ₂ b₁ b₂
  | .VConstr tag₁ f₁, .VConstr tag₂ f₂ =>
      tag₁ = tag₂ ∧ ListRel Rp f₁ f₂
  | .VBuiltin b₁ a₁ e₁, .VBuiltin b₂ a₂ e₂ =>
      b₁ = b₂ ∧ e₁ = e₂ ∧ ListRel Rp a₁ a₂
  | _, _ => False

--------------------------------------------------------------------------------
-- 6. BIVARIANCE OF F_Gen (The Boss Fight)
--------------------------------------------------------------------------------

theorem F_Gen_bivariant : Bivariant F_Gen := by
  intro Rn Rn' Rp Rp' hn hp v₁ v₂
  match v₁, v₂ with
  | .VLam _ _, .VLam _ _ =>
    exact fun h arg₁ arg₂ hR =>
      behEq_mono hp (h arg₁ arg₂ (hn _ _ hR))
  | .VDelay _ _, .VDelay _ _ =>
    exact fun h => behEq_mono hp h
  | .VConstr _ _, .VConstr _ _ =>
    exact fun h => ⟨h.1, listRel_mono (fun a b hab => hp a b hab) _ _ h.2⟩
  | .VBuiltin _ _ _, .VBuiltin _ _ _ =>
    exact fun h => ⟨h.1, h.2.1, listRel_mono (fun a b hab => hp a b hab) _ _ h.2.2⟩
  | .VCon _, .VCon _ => exact id
  | .VCon _, .VLam _ _ => exact id
  | .VCon _, .VDelay _ _ => exact id
  | .VCon _, .VConstr _ _ => exact id
  | .VCon _, .VBuiltin _ _ _ => exact id
  | .VLam _ _, .VCon _ => exact id
  | .VLam _ _, .VDelay _ _ => exact id
  | .VLam _ _, .VConstr _ _ => exact id
  | .VLam _ _, .VBuiltin _ _ _ => exact id
  | .VDelay _ _, .VCon _ => exact id
  | .VDelay _ _, .VLam _ _ => exact id
  | .VDelay _ _, .VConstr _ _ => exact id
  | .VDelay _ _, .VBuiltin _ _ _ => exact id
  | .VConstr _ _, .VCon _ => exact id
  | .VConstr _ _, .VLam _ _ => exact id
  | .VConstr _ _, .VDelay _ _ => exact id
  | .VConstr _ _, .VBuiltin _ _ _ => exact id
  | .VBuiltin _ _ _, .VCon _ => exact id
  | .VBuiltin _ _ _, .VLam _ _ => exact id
  | .VBuiltin _ _ _, .VDelay _ _ => exact id
  | .VBuiltin _ _ _, .VConstr _ _ => exact id

--------------------------------------------------------------------------------
-- 7. THE KNOT
--------------------------------------------------------------------------------

/-- The true, fuel-free value equivalence: the positive component of the
    bivariant GFP of `F_Gen`. -/
def ValueEq : ValRel := BivGFPPos F_Gen

/-- The dual relation used in the negative-hypothesis slot of `F_Gen`. -/
def ValueEqNeg : ValRel := BivGFPNeg F_Gen

/-- We can unroll the bivariant GFP exactly when we need to evaluate a body! -/
theorem valueEq_eq_F :
    ∀ v₁ v₂, ValueEq v₁ v₂ ↔ F_Gen ValueEqNeg ValueEq v₁ v₂ :=
  bivGFPPos_unroll F_Gen_bivariant

def EnvEq (d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup n, ρ₂.lookup n with
    | some v₁, some v₂ => ValueEq v₁ v₂
    | none, none => True
    | _, _ => False

/-- Open Equivalence using the bivariant GFP. -/
def OpenEq (d : Nat) (t₁ t₂ : Term) : Prop :=
  ∀ ρ₁ ρ₂, EnvEq d ρ₁ ρ₂ → BehEq ValueEq ρ₁ ρ₂ t₁ t₂

--------------------------------------------------------------------------------
-- 8. STEPPING / ObsEq INFRASTRUCTURE
--------------------------------------------------------------------------------

/-- Pushing a step commutes with `steps n` on the right. -/
private theorem steps_succ (n : Nat) (s : State) :
    steps (n + 1) s = steps n (step s) := rfl

/-- `Reaches` is preserved across one step. -/
theorem reaches_step_iff (s : State) (v : CekValue) :
    Reaches s (.halt v) ↔ Reaches (step s) (.halt v) := by
  constructor
  · intro ⟨n, hn⟩
    match n with
    | 0 =>
      -- s = halt v, so step s = halt v (step is identity on halt).
      subst hn
      exact ⟨0, by rfl⟩
    | m + 1 =>
      exact ⟨m, by rw [← hn]; rfl⟩
  · intro ⟨n, hn⟩
    exact ⟨n + 1, hn⟩

/-- Stepping on both sides preserves `ObsEq`. -/
theorem obsEq_step_iff (s₁ s₂ : State) :
    ObsEq s₁ s₂ ↔ ObsEq (step s₁) (step s₂) := by
  unfold ObsEq
  constructor
  · intro h
    refine ⟨fun ⟨v, hv⟩ => ?_, fun ⟨v, hv⟩ => ?_⟩
    · obtain ⟨v', hv'⟩ := h.mp ⟨v, (reaches_step_iff s₁ v).mpr hv⟩
      exact ⟨v', (reaches_step_iff s₂ v').mp hv'⟩
    · obtain ⟨v', hv'⟩ := h.mpr ⟨v, (reaches_step_iff s₂ v).mpr hv⟩
      exact ⟨v', (reaches_step_iff s₁ v').mp hv'⟩
  · intro h
    refine ⟨fun ⟨v, hv⟩ => ?_, fun ⟨v, hv⟩ => ?_⟩
    · obtain ⟨v', hv'⟩ := h.mp ⟨v, (reaches_step_iff s₁ v).mp hv⟩
      exact ⟨v', (reaches_step_iff s₂ v').mpr hv'⟩
    · obtain ⟨v', hv'⟩ := h.mpr ⟨v, (reaches_step_iff s₂ v).mp hv⟩
      exact ⟨v', (reaches_step_iff s₁ v').mpr hv'⟩

end Moist.Verified.Equivalence
