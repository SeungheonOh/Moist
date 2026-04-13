import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.Plutus.Term
import Moist.Verified.Equivalence
import Moist.Verified.Contextual

/-! # Syntactic substitution congruence on the CEK universe

Phase 1 of the Path A plan (`Contextual-PathA-Plan.md`).

Defines a family of inductive relations `_Subst t₁ t₂ _ _` indexed by a pair
of "hole-content" terms `t₁`, `t₂`. Two terms / values / envs / frames /
stacks / states are related iff they differ only by zero or more `t₁ ↔ t₂`
swaps at corresponding positions.

The relation will then be used (Phases 2–5) to prove the open-context version
of `soundness` for `CtxEq` without going through `openEq_contextual_closure`.
-/

namespace Moist.Verified.Contextual.Subst

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Equivalence

--------------------------------------------------------------------------------
-- 1. TermSubst
--------------------------------------------------------------------------------

mutual
/-- Two terms are `TermSubst t₁ t₂`-related iff they are structurally equal up
    to occurrences of `t₁` swapped with `t₂` (at any positions). -/
inductive TermSubst (t₁ t₂ : Term) : Term → Term → Prop
  | swap     : TermSubst t₁ t₂ t₁ t₂
  | swapInv  : TermSubst t₁ t₂ t₂ t₁
  | varRefl  (n : Nat) : TermSubst t₁ t₂ (.Var n) (.Var n)
  | constRefl (c : Const × BuiltinType) : TermSubst t₁ t₂ (.Constant c) (.Constant c)
  | builtinRefl (b : BuiltinFun) : TermSubst t₁ t₂ (.Builtin b) (.Builtin b)
  | errorRefl : TermSubst t₁ t₂ .Error .Error
  | lam {x : Nat} {b₁ b₂ : Term} :
      TermSubst t₁ t₂ b₁ b₂ → TermSubst t₁ t₂ (.Lam x b₁) (.Lam x b₂)
  | apply {f₁ f₂ a₁ a₂ : Term} :
      TermSubst t₁ t₂ f₁ f₂ → TermSubst t₁ t₂ a₁ a₂ →
      TermSubst t₁ t₂ (.Apply f₁ a₁) (.Apply f₂ a₂)
  | force {e₁ e₂ : Term} :
      TermSubst t₁ t₂ e₁ e₂ → TermSubst t₁ t₂ (.Force e₁) (.Force e₂)
  | delay {e₁ e₂ : Term} :
      TermSubst t₁ t₂ e₁ e₂ → TermSubst t₁ t₂ (.Delay e₁) (.Delay e₂)
  | constr {tag : Nat} {as₁ as₂ : List Term} :
      TermListSubst t₁ t₂ as₁ as₂ →
      TermSubst t₁ t₂ (.Constr tag as₁) (.Constr tag as₂)
  | case {s₁ s₂ : Term} {as₁ as₂ : List Term} :
      TermSubst t₁ t₂ s₁ s₂ → TermListSubst t₁ t₂ as₁ as₂ →
      TermSubst t₁ t₂ (.Case s₁ as₁) (.Case s₂ as₂)

/-- Pointwise lift of `TermSubst` to lists. -/
inductive TermListSubst (t₁ t₂ : Term) : List Term → List Term → Prop
  | nil  : TermListSubst t₁ t₂ [] []
  | cons {a b : Term} {as bs : List Term} :
      TermSubst t₁ t₂ a b → TermListSubst t₁ t₂ as bs →
      TermListSubst t₁ t₂ (a :: as) (b :: bs)
end

--------------------------------------------------------------------------------
-- 2. ValueSubst / ValueListSubst / EnvSubst
--------------------------------------------------------------------------------

mutual
/-- `ValueSubst t₁ t₂ v_l v_r` says that two CEK values differ only by `t₁ ↔ t₂`
    swaps inside their term/env contents. -/
inductive ValueSubst (t₁ t₂ : Term) : CekValue → CekValue → Prop
  | vCon (c : Const) : ValueSubst t₁ t₂ (.VCon c) (.VCon c)
  | vLam {b_l b_r : Term} {ρ_l ρ_r : CekEnv} :
      TermSubst t₁ t₂ b_l b_r → EnvSubst t₁ t₂ ρ_l ρ_r →
      ValueSubst t₁ t₂ (.VLam b_l ρ_l) (.VLam b_r ρ_r)
  | vDelay {b_l b_r : Term} {ρ_l ρ_r : CekEnv} :
      TermSubst t₁ t₂ b_l b_r → EnvSubst t₁ t₂ ρ_l ρ_r →
      ValueSubst t₁ t₂ (.VDelay b_l ρ_l) (.VDelay b_r ρ_r)
  | vConstr {tag : Nat} {fields_l fields_r : List CekValue} :
      ValueListSubst t₁ t₂ fields_l fields_r →
      ValueSubst t₁ t₂ (.VConstr tag fields_l) (.VConstr tag fields_r)
  | vBuiltin {b : BuiltinFun} {args_l args_r : List CekValue} {exp : ExpectedArgs} :
      ValueListSubst t₁ t₂ args_l args_r →
      ValueSubst t₁ t₂ (.VBuiltin b args_l exp) (.VBuiltin b args_r exp)

/-- Pointwise lift of `ValueSubst` to lists. -/
inductive ValueListSubst (t₁ t₂ : Term) : List CekValue → List CekValue → Prop
  | nil : ValueListSubst t₁ t₂ [] []
  | cons {v_l v_r : CekValue} {vs_l vs_r : List CekValue} :
      ValueSubst t₁ t₂ v_l v_r → ValueListSubst t₁ t₂ vs_l vs_r →
      ValueListSubst t₁ t₂ (v_l :: vs_l) (v_r :: vs_r)

/-- `EnvSubst t₁ t₂ ρ_l ρ_r` says that two CEK environments differ only by
    pointwise `ValueSubst` at corresponding positions. -/
inductive EnvSubst (t₁ t₂ : Term) : CekEnv → CekEnv → Prop
  | nil : EnvSubst t₁ t₂ .nil .nil
  | cons {v_l v_r : CekValue} {ρ_l ρ_r : CekEnv} :
      ValueSubst t₁ t₂ v_l v_r → EnvSubst t₁ t₂ ρ_l ρ_r →
      EnvSubst t₁ t₂ (.cons v_l ρ_l) (.cons v_r ρ_r)
end

--------------------------------------------------------------------------------
-- 3. FrameSubst / StackSubst
--------------------------------------------------------------------------------

/-- Substitution congruence on individual CEK stack frames. -/
inductive FrameSubst (t₁ t₂ : Term) : Frame → Frame → Prop
  | force : FrameSubst t₁ t₂ .force .force
  | arg {m_l m_r : Term} {ρ_l ρ_r : CekEnv} :
      TermSubst t₁ t₂ m_l m_r → EnvSubst t₁ t₂ ρ_l ρ_r →
      FrameSubst t₁ t₂ (.arg m_l ρ_l) (.arg m_r ρ_r)
  | funV {v_l v_r : CekValue} :
      ValueSubst t₁ t₂ v_l v_r → FrameSubst t₁ t₂ (.funV v_l) (.funV v_r)
  | applyArg {v_l v_r : CekValue} :
      ValueSubst t₁ t₂ v_l v_r → FrameSubst t₁ t₂ (.applyArg v_l) (.applyArg v_r)
  | constrField {tag : Nat} {d_l d_r : List CekValue}
      {ms_l ms_r : List Term} {ρ_l ρ_r : CekEnv} :
      ValueListSubst t₁ t₂ d_l d_r → TermListSubst t₁ t₂ ms_l ms_r →
      EnvSubst t₁ t₂ ρ_l ρ_r →
      FrameSubst t₁ t₂ (.constrField tag d_l ms_l ρ_l) (.constrField tag d_r ms_r ρ_r)
  | caseScrutinee {as_l as_r : List Term} {ρ_l ρ_r : CekEnv} :
      TermListSubst t₁ t₂ as_l as_r → EnvSubst t₁ t₂ ρ_l ρ_r →
      FrameSubst t₁ t₂ (.caseScrutinee as_l ρ_l) (.caseScrutinee as_r ρ_r)

/-- Pointwise lift of `FrameSubst` to stacks. -/
inductive StackSubst (t₁ t₂ : Term) : Stack → Stack → Prop
  | nil : StackSubst t₁ t₂ [] []
  | cons {f_l f_r : Frame} {π_l π_r : Stack} :
      FrameSubst t₁ t₂ f_l f_r → StackSubst t₁ t₂ π_l π_r →
      StackSubst t₁ t₂ (f_l :: π_l) (f_r :: π_r)

--------------------------------------------------------------------------------
-- 4. StateSubst
--------------------------------------------------------------------------------

/-- `StateSubst t₁ t₂ s_l s_r` lifts substitution congruence to whole CEK
    machine states. -/
inductive StateSubst (t₁ t₂ : Term) : State → State → Prop
  | compute {π_l π_r : Stack} {ρ_l ρ_r : CekEnv} {tm_l tm_r : Term} :
      StackSubst t₁ t₂ π_l π_r → EnvSubst t₁ t₂ ρ_l ρ_r →
      TermSubst t₁ t₂ tm_l tm_r →
      StateSubst t₁ t₂ (.compute π_l ρ_l tm_l) (.compute π_r ρ_r tm_r)
  | ret {π_l π_r : Stack} {v_l v_r : CekValue} :
      StackSubst t₁ t₂ π_l π_r → ValueSubst t₁ t₂ v_l v_r →
      StateSubst t₁ t₂ (.ret π_l v_l) (.ret π_r v_r)
  | error : StateSubst t₁ t₂ .error .error
  | halt {v_l v_r : CekValue} :
      ValueSubst t₁ t₂ v_l v_r → StateSubst t₁ t₂ (.halt v_l) (.halt v_r)

--------------------------------------------------------------------------------
-- 5. REFLEXIVITY
--
-- Every CEK object is `Subst`-related to itself (no swaps, only structural
-- congruences). Mutually defined for terms / values / envs.
--------------------------------------------------------------------------------

mutual
def TermSubst.refl {t₁ t₂ : Term} : ∀ (t : Term), TermSubst t₁ t₂ t t
  | .Var n => .varRefl n
  | .Constant c => .constRefl c
  | .Builtin b => .builtinRefl b
  | .Error => .errorRefl
  | .Lam _ b => .lam (TermSubst.refl b)
  | .Apply f a => .apply (TermSubst.refl f) (TermSubst.refl a)
  | .Force e => .force (TermSubst.refl e)
  | .Delay e => .delay (TermSubst.refl e)
  | .Constr _ as => .constr (TermListSubst.refl as)
  | .Case s as => .case (TermSubst.refl s) (TermListSubst.refl as)

def TermListSubst.refl {t₁ t₂ : Term} : ∀ (ts : List Term), TermListSubst t₁ t₂ ts ts
  | [] => .nil
  | t :: rest => .cons (TermSubst.refl t) (TermListSubst.refl rest)
end

mutual
def ValueSubst.refl {t₁ t₂ : Term} : ∀ (v : CekValue), ValueSubst t₁ t₂ v v
  | .VCon c => .vCon c
  | .VLam b ρ => .vLam (TermSubst.refl b) (EnvSubst.refl ρ)
  | .VDelay b ρ => .vDelay (TermSubst.refl b) (EnvSubst.refl ρ)
  | .VConstr _ fields => .vConstr (ValueListSubst.refl fields)
  | .VBuiltin _ args _ => .vBuiltin (ValueListSubst.refl args)

def ValueListSubst.refl {t₁ t₂ : Term} : ∀ (vs : List CekValue), ValueListSubst t₁ t₂ vs vs
  | [] => .nil
  | v :: rest => .cons (ValueSubst.refl v) (ValueListSubst.refl rest)

def EnvSubst.refl {t₁ t₂ : Term} : ∀ (ρ : CekEnv), EnvSubst t₁ t₂ ρ ρ
  | .nil => .nil
  | .cons v ρ => .cons (ValueSubst.refl v) (EnvSubst.refl ρ)
end

def FrameSubst.refl {t₁ t₂ : Term} : ∀ (f : Frame), FrameSubst t₁ t₂ f f
  | .force => .force
  | .arg m ρ => .arg (TermSubst.refl m) (EnvSubst.refl ρ)
  | .funV v => .funV (ValueSubst.refl v)
  | .applyArg v => .applyArg (ValueSubst.refl v)
  | .constrField _ d ms ρ =>
      .constrField (ValueListSubst.refl d) (TermListSubst.refl ms) (EnvSubst.refl ρ)
  | .caseScrutinee as ρ =>
      .caseScrutinee (TermListSubst.refl as) (EnvSubst.refl ρ)

def StackSubst.refl {t₁ t₂ : Term} : ∀ (π : Stack), StackSubst t₁ t₂ π π
  | [] => .nil
  | f :: rest => .cons (FrameSubst.refl f) (StackSubst.refl rest)

def StateSubst.refl {t₁ t₂ : Term} : ∀ (s : State), StateSubst t₁ t₂ s s
  | .compute π ρ tm =>
      .compute (StackSubst.refl π) (EnvSubst.refl ρ) (TermSubst.refl tm)
  | .ret π v =>
      .ret (StackSubst.refl π) (ValueSubst.refl v)
  | .error => .error
  | .halt v => .halt (ValueSubst.refl v)

--------------------------------------------------------------------------------
-- 6. SYMMETRY (within the same `t₁`/`t₂` parameters)
--
-- The relation `TermSubst t₁ t₂` is symmetric in its two arguments: if `a`
-- is related to `b`, then `b` is related to `a`. The constructors `swap` and
-- `swapInv` are each other's mirror.
--------------------------------------------------------------------------------

mutual
def TermSubst.symm {t₁ t₂ : Term} :
    ∀ {a b : Term}, TermSubst t₁ t₂ a b → TermSubst t₁ t₂ b a
  | _, _, .swap => .swapInv
  | _, _, .swapInv => .swap
  | _, _, .varRefl n => .varRefl n
  | _, _, .constRefl c => .constRefl c
  | _, _, .builtinRefl b => .builtinRefl b
  | _, _, .errorRefl => .errorRefl
  | _, _, .lam h => .lam (TermSubst.symm h)
  | _, _, .apply hf ha => .apply (TermSubst.symm hf) (TermSubst.symm ha)
  | _, _, .force h => .force (TermSubst.symm h)
  | _, _, .delay h => .delay (TermSubst.symm h)
  | _, _, .constr h => .constr (TermListSubst.symm h)
  | _, _, .case hs ha => .case (TermSubst.symm hs) (TermListSubst.symm ha)

def TermListSubst.symm {t₁ t₂ : Term} :
    ∀ {as bs : List Term}, TermListSubst t₁ t₂ as bs → TermListSubst t₁ t₂ bs as
  | _, _, .nil => .nil
  | _, _, .cons hh ht => .cons (TermSubst.symm hh) (TermListSubst.symm ht)
end

mutual
def ValueSubst.symm {t₁ t₂ : Term} :
    ∀ {v_l v_r : CekValue}, ValueSubst t₁ t₂ v_l v_r → ValueSubst t₁ t₂ v_r v_l
  | _, _, .vCon c => .vCon c
  | _, _, .vLam hb hρ => .vLam (TermSubst.symm hb) (EnvSubst.symm hρ)
  | _, _, .vDelay hb hρ => .vDelay (TermSubst.symm hb) (EnvSubst.symm hρ)
  | _, _, .vConstr h => .vConstr (ValueListSubst.symm h)
  | _, _, .vBuiltin h => .vBuiltin (ValueListSubst.symm h)

def ValueListSubst.symm {t₁ t₂ : Term} :
    ∀ {vs_l vs_r : List CekValue},
      ValueListSubst t₁ t₂ vs_l vs_r → ValueListSubst t₁ t₂ vs_r vs_l
  | _, _, .nil => .nil
  | _, _, .cons hh ht => .cons (ValueSubst.symm hh) (ValueListSubst.symm ht)

def EnvSubst.symm {t₁ t₂ : Term} :
    ∀ {ρ_l ρ_r : CekEnv}, EnvSubst t₁ t₂ ρ_l ρ_r → EnvSubst t₁ t₂ ρ_r ρ_l
  | _, _, .nil => .nil
  | _, _, .cons hv hρ => .cons (ValueSubst.symm hv) (EnvSubst.symm hρ)
end

def FrameSubst.symm {t₁ t₂ : Term} :
    ∀ {f_l f_r : Frame}, FrameSubst t₁ t₂ f_l f_r → FrameSubst t₁ t₂ f_r f_l
  | _, _, .force => .force
  | _, _, .arg hm hρ => .arg (TermSubst.symm hm) (EnvSubst.symm hρ)
  | _, _, .funV h => .funV (ValueSubst.symm h)
  | _, _, .applyArg h => .applyArg (ValueSubst.symm h)
  | _, _, .constrField hd hm hρ =>
      .constrField (ValueListSubst.symm hd) (TermListSubst.symm hm) (EnvSubst.symm hρ)
  | _, _, .caseScrutinee ha hρ =>
      .caseScrutinee (TermListSubst.symm ha) (EnvSubst.symm hρ)

def StackSubst.symm {t₁ t₂ : Term} :
    ∀ {π_l π_r : Stack}, StackSubst t₁ t₂ π_l π_r → StackSubst t₁ t₂ π_r π_l
  | _, _, .nil => .nil
  | _, _, .cons hf hπ => .cons (FrameSubst.symm hf) (StackSubst.symm hπ)

def StateSubst.symm {t₁ t₂ : Term} :
    ∀ {s_l s_r : State}, StateSubst t₁ t₂ s_l s_r → StateSubst t₁ t₂ s_r s_l
  | _, _, .compute hπ hρ htm =>
      .compute (StackSubst.symm hπ) (EnvSubst.symm hρ) (TermSubst.symm htm)
  | _, _, .ret hπ hv => .ret (StackSubst.symm hπ) (ValueSubst.symm hv)
  | _, _, .error => .error
  | _, _, .halt hv => .halt (ValueSubst.symm hv)

--------------------------------------------------------------------------------
-- 7. INITIAL STATE LEMMA
--
-- Phase 2 of the plan: filling a context with `t₁` vs `t₂` produces two
-- terms (and two whole CEK initial states) that are `Subst`-related.
--------------------------------------------------------------------------------

open Moist.Verified.Contextual (Context fill)

/-- Filling a context's hole with `t₁` vs `t₂` yields `TermSubst`-related
    terms. Proven by induction on the context. -/
theorem fill_termSubst (C : Context) (t₁ t₂ : Term) :
    TermSubst t₁ t₂ (fill C t₁) (fill C t₂) := by
  induction C with
  | Hole => exact .swap
  | Lam x C ih => exact .lam ih
  | AppLeft C e ih => exact .apply ih (TermSubst.refl e)
  | AppRight e C ih => exact .apply (TermSubst.refl e) ih
  | Delay C ih => exact .delay ih
  | Force C ih => exact .force ih
  | Constr tag lefts C rights ih =>
    -- fill produces `Constr tag (lefts ++ [fill C t₁] ++ rights)` on each side.
    -- The list parts are `TermListSubst`-related: lefts/rights reflexively, the
    -- middle by ih.
    refine .constr ?_
    show TermListSubst t₁ t₂
      (lefts ++ [fill C t₁] ++ rights) (lefts ++ [fill C t₂] ++ rights)
    -- Reassociate so the middle "swap point" is exposed.
    rw [List.append_assoc, List.append_assoc]
    show TermListSubst t₁ t₂
      (lefts ++ fill C t₁ :: rights) (lefts ++ fill C t₂ :: rights)
    exact termListSubst_around lefts rights ih
  | Case C alts ih =>
    exact .case ih (TermListSubst.refl alts)
  | CaseAlt scrut lefts C rights ih =>
    refine .case (TermSubst.refl scrut) ?_
    show TermListSubst t₁ t₂
      (lefts ++ [fill C t₁] ++ rights) (lefts ++ [fill C t₂] ++ rights)
    rw [List.append_assoc, List.append_assoc]
    show TermListSubst t₁ t₂
      (lefts ++ fill C t₁ :: rights) (lefts ++ fill C t₂ :: rights)
    exact termListSubst_around lefts rights ih
where
  -- Splice helper: `pre ++ a :: post` and `pre ++ b :: post` are
  -- `TermListSubst`-related when `a` and `b` are `TermSubst`-related.
  termListSubst_around : ∀ (pre post : List Term) {a b : Term},
      TermSubst t₁ t₂ a b →
      TermListSubst t₁ t₂ (pre ++ a :: post) (pre ++ b :: post)
    | [], post, _, _, hab =>
        .cons hab (TermListSubst.refl post)
    | p :: ps, post, _, _, hab =>
        .cons (TermSubst.refl p) (termListSubst_around ps post hab)

/-- The initial CEK states (`compute [] .nil` of two `fill C` terms) are
    `StateSubst`-related. -/
theorem initial_stateSubst (C : Context) (t₁ t₂ : Term) :
    StateSubst t₁ t₂ (.compute [] .nil (fill C t₁))
                     (.compute [] .nil (fill C t₂)) :=
  .compute .nil .nil (fill_termSubst C t₁ t₂)

--------------------------------------------------------------------------------
-- 8. AUXILIARY LEMMAS FOR THE STEP LEMMA
--------------------------------------------------------------------------------

/-- Env lookup preserves `Subst`: if two envs are pointwise `ValueSubst`-related,
    so are their lookups at any index (both `some`/`some` related, or both
    `none`). -/
theorem envSubst_lookup {t₁ t₂ : Term} :
    ∀ {ρ_l ρ_r : CekEnv}, EnvSubst t₁ t₂ ρ_l ρ_r → ∀ (n : Nat),
      (ρ_l.lookup n = none ∧ ρ_r.lookup n = none) ∨
      (∃ v_l v_r, ρ_l.lookup n = some v_l ∧ ρ_r.lookup n = some v_r ∧
        ValueSubst t₁ t₂ v_l v_r)
  | _, _, .nil, n => .inl ⟨rfl, rfl⟩
  | _, _, .cons (v_l := vl) (v_r := vr) hv hρ, n => by
    match n with
    | 0 => exact .inl ⟨rfl, rfl⟩
    | 1 => exact .inr ⟨vl, vr, rfl, rfl, hv⟩
    | k + 2 =>
      -- shifts to the rest
      have := envSubst_lookup hρ (k + 1)
      simp [CekEnv.lookup] at this ⊢
      exact this

/-- `EnvSubst.extend`: extending two `EnvSubst`-related envs with two
    `ValueSubst`-related values gives an `EnvSubst`-related extended env. -/
theorem envSubst_extend {t₁ t₂ : Term} {ρ_l ρ_r : CekEnv} {v_l v_r : CekValue}
    (hρ : EnvSubst t₁ t₂ ρ_l ρ_r) (hv : ValueSubst t₁ t₂ v_l v_r) :
    EnvSubst t₁ t₂ (ρ_l.extend v_l) (ρ_r.extend v_r) :=
  .cons hv hρ

/-- Concatenation/cons preservation for stacks. -/
theorem stackSubst_cons {t₁ t₂ : Term} {f_l f_r : Frame} {π_l π_r : Stack}
    (hf : FrameSubst t₁ t₂ f_l f_r) (hπ : StackSubst t₁ t₂ π_l π_r) :
    StackSubst t₁ t₂ (f_l :: π_l) (f_r :: π_r) :=
  .cons hf hπ

/-- Append preserves `ValueListSubst` pointwise. -/
theorem valueListSubst_append {t₁ t₂ : Term} :
    ∀ {l₁ l₂ r₁ r₂ : List CekValue},
      ValueListSubst t₁ t₂ l₁ l₂ → ValueListSubst t₁ t₂ r₁ r₂ →
      ValueListSubst t₁ t₂ (l₁ ++ r₁) (l₂ ++ r₂)
  | _, _, _, _, .nil, hr => hr
  | _, _, _, _, .cons hh ht, hr => .cons hh (valueListSubst_append ht hr)

/-- Reverse preserves `ValueListSubst` pointwise. -/
theorem valueListSubst_reverse {t₁ t₂ : Term} :
    ∀ {l₁ l₂ : List CekValue}, ValueListSubst t₁ t₂ l₁ l₂ →
      ValueListSubst t₁ t₂ l₁.reverse l₂.reverse
  | _, _, .nil => by simp; exact .nil
  | _, _, .cons hh ht => by
    simp [List.reverse_cons]
    exact valueListSubst_append (valueListSubst_reverse ht) (.cons hh .nil)

/-- Append preserves `StackSubst`. -/
theorem stackSubst_append {t₁ t₂ : Term} :
    ∀ {π_l₁ π_r₁ π_l₂ π_r₂ : Stack},
      StackSubst t₁ t₂ π_l₁ π_r₁ → StackSubst t₁ t₂ π_l₂ π_r₂ →
      StackSubst t₁ t₂ (π_l₁ ++ π_l₂) (π_r₁ ++ π_r₂)
  | _, _, _, _, .nil, h₂ => h₂
  | _, _, _, _, .cons hf hπ, h₂ => .cons hf (stackSubst_append hπ h₂)

/-- Mapping `Frame.applyArg` over a `ValueListSubst` gives a `StackSubst`. -/
theorem valueListSubst_map_applyArg {t₁ t₂ : Term} :
    ∀ {l_l l_r : List CekValue}, ValueListSubst t₁ t₂ l_l l_r →
      StackSubst t₁ t₂ (l_l.map Frame.applyArg) (l_r.map Frame.applyArg)
  | _, _, .nil => .nil
  | _, _, .cons hh ht =>
      .cons (.applyArg hh) (valueListSubst_map_applyArg ht)

/-- Lookup in a `TermListSubst`-related list at a specific index returns
    `TermSubst`-related elements (or both `none`). -/
theorem termListSubst_getElem? {t₁ t₂ : Term} :
    ∀ {l_l l_r : List Term}, TermListSubst t₁ t₂ l_l l_r → ∀ (n : Nat),
      (l_l[n]? = none ∧ l_r[n]? = none) ∨
      (∃ a_l a_r, l_l[n]? = some a_l ∧ l_r[n]? = some a_r ∧
        TermSubst t₁ t₂ a_l a_r)
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons (a := al) (b := ar) hh ht, n => by
    cases n with
    | zero => exact .inr ⟨al, ar, by simp, by simp, hh⟩
    | succ k =>
      have ih := termListSubst_getElem? ht k
      cases ih with
      | inl h => obtain ⟨hl, hr⟩ := h; exact .inl ⟨by simp [hl], by simp [hr]⟩
      | inr h => obtain ⟨a_l, a_r, hl, hr, hab⟩ := h
                 exact .inr ⟨a_l, a_r, by simp [hl], by simp [hr], hab⟩

/-- `TermListSubst`-related lists have the same length. -/
theorem termListSubst_length_eq {t₁ t₂ : Term} :
    ∀ {l_l l_r : List Term}, TermListSubst t₁ t₂ l_l l_r → l_l.length = l_r.length
  | _, _, .nil => rfl
  | _, _, .cons _ ht => by simp [termListSubst_length_eq ht]

end Moist.Verified.Contextual.Subst
