import Moist.Verified.KnownListsSoundness.Lowering
import Moist.Verified.KnownListsSoundness.Knot

/-! # Recursive functions applied to known lists

`KnownRel.fixApp`: when every call of a recursive function — the external
application and the calls inside its body (`listCallsOK`) — passes known
lists at the positions `P`, its body may be transformed assuming that the
parameters at `P` hold lists. The lowered application is related by the
knot of `Knot.lean` (`fixApply_obs`), then by congruence on the arguments.
-/

namespace Moist.Verified.KnownLists

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts

/-! ## Application spines and lambda chains -/

theorem lowerTotalExpr_applyAll_some {env : List VarId} :
    ∀ {f : Expr} {args : List Expr} {t : Term}, lowerTotalExpr env (applyAll f args) = some t →
      ∃ tf targs, lowerTotalExpr env f = some tf ∧ MIR.lowerTotalExprList env args = some targs ∧
        t = applyAllT tf targs
  | f, [], t, h => ⟨t, [], h, MIR.lowerTotalExprList_nil env, rfl⟩
  | f, a :: as, t, h => by
    obtain ⟨tfa, targs, hfa, has, rfl⟩ := lowerTotalExpr_applyAll_some (f := .App f a) (args := as) h
    obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hfa
    refine ⟨tf, ta :: targs, htf, ?_, rfl⟩
    rw [MIR.lowerTotalExprList_cons, hta, has]; rfl

theorem lowerTotalExpr_applyAll_of {env : List VarId} :
    ∀ {f : Expr} {args : List Expr} {tf : Term} {targs : List Term},
      lowerTotalExpr env f = some tf → MIR.lowerTotalExprList env args = some targs →
      lowerTotalExpr env (applyAll f args) = some (applyAllT tf targs)
  | f, [], tf, targs, hf, has => by
    rw [MIR.lowerTotalExprList_nil] at has; cases has; exact hf
  | f, a :: as, tf, targs, hf, has => by
    rw [MIR.lowerTotalExprList_cons] at has
    cases ha : lowerTotalExpr env a with
    | none => rw [ha] at has; cases has
    | some ta =>
      cases has' : MIR.lowerTotalExprList env as with
      | none => rw [ha, has'] at has; cases has
      | some tas =>
        rw [ha, has'] at has; cases has
        exact lowerTotalExpr_applyAll_of (f := .App f a) (targs := tas)
          (by rw [MIR.lowerTotalExpr_app, hf, ha]; rfl) has'

theorem freshIn_applyAll (avoid : List VarId) :
    ∀ (f : Expr) (args : List Expr),
      freshIn avoid (applyAll f args) = (freshIn avoid f && freshInList avoid args)
  | f, [] => by simp [applyAll, freshInList]
  | f, a :: as => by
    rw [applyAll, freshIn_applyAll avoid (.App f a) as]
    simp only [freshIn, freshInList, Bool.and_assoc]

theorem KnownRel.applyAll {Γ : List (VarId × Expr)} {L : List VarId} :
    ∀ {f f' : Expr} {args args' : List Expr}, KnownRel Γ L f f' → ListRel (KnownRel Γ L) args args' →
      KnownRel Γ L (Advanced.applyAll f args) (Advanced.applyAll f' args')
  | _, _, [], [], hf, _ => hf
  | _, _, [], _ :: _, _, h => absurd h id
  | _, _, _ :: _, [], _, h => absurd h id
  | f, f', a :: _, a' :: _, hf, h =>
    KnownRel.applyAll (f := .App f a) (f' := .App f' a') (hf.app h.1) h.2

theorem KnownRel.lambdaWrap {Γ : List (VarId × Expr)} {L : List VarId} :
    ∀ (xs : List VarId) {e e' : Expr}, KnownRel Γ L e e' →
      KnownRel Γ L (Advanced.lambdaWrap xs e) (Advanced.lambdaWrap xs e')
  | [], _, _, h => h
  | _ :: xs, _, _, h => (KnownRel.lambdaWrap xs h).lam

theorem lowerTotalExpr_lambdaWrap :
    ∀ (xs : List VarId) (env : List VarId) (e : Expr),
      lowerTotalExpr env (Advanced.lambdaWrap xs e) =
        (lowerTotalExpr (xs.reverse ++ env) e).map (lams xs.length)
  | [], env, e => by
    simp only [Advanced.lambdaWrap, List.reverse_nil, List.nil_append, List.length_nil]
    cases lowerTotalExpr env e <;> rfl
  | x :: xs, env, e => by
    rw [Advanced.lambdaWrap, MIR.lowerTotalExpr_lam, lowerTotalExpr_lambdaWrap xs (x :: env) e]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons]
    cases lowerTotalExpr (xs.reverse ++ x :: env) e <;> rfl

theorem lambdaChain_wrap : ∀ (e : Expr),
    Advanced.lambdaWrap (lambdaChain e).1 (lambdaChain e).2 = e
  | .Lam x b => by
    simp only [lambdaChain, Advanced.lambdaWrap]
    rw [lambdaChain_wrap b]
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Fix _ _ | .App _ _ | .Force _ | .Delay _
  | .Constr _ _ | .Case _ _ | .Let _ _ => rfl

theorem listCallsOK_lambdaWrap {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} :
    ∀ (xs : List VarId) (e : Expr),
      listCallsOK f m P names (Advanced.lambdaWrap xs e) = listCallsOK f m P names e
  | [], e => rfl
  | x :: xs, e => by rw [Advanced.lambdaWrap, listCallsOK_lam, listCallsOK_lambdaWrap xs e]

/-! ## Entering a chain of fresh binders -/

theorem enter_lambdaWrap {Γ : List (VarId × Expr)} {L : List VarId} :
    ∀ (xs : List VarId) {env : List VarId} {e : Expr},
      freshIn env (Advanced.lambdaWrap xs e) = true → EnvDistinct env → KeysBound Γ env →
      FactsScoped Γ env → NamesBound L env →
      EnvDistinct (xs.reverse ++ env) ∧ KeysBound Γ (xs.reverse ++ env) ∧
        FactsScoped Γ (xs.reverse ++ env) ∧ NamesBound L (xs.reverse ++ env) ∧
        freshIn (xs.reverse ++ env) e = true ∧
        (∀ ρ as, KnownFacts Γ L env ρ → as.length = xs.length →
          KnownFacts Γ L (xs.reverse ++ env) (extendAll ρ as)) ∧
        (∀ x ∈ xs, (envLookupT env x).isNone = true)
  | [], env, e, hf, hd, hk, hs, hn => by
    simp only [List.reverse_nil, List.nil_append]
    refine ⟨hd, hk, hs, hn, hf, fun ρ as hF has => ?_, fun x hx => by cases hx⟩
    cases as with
    | nil => exact hF
    | cons _ _ => simp at has
  | x :: xs, env, e, hf, hd, hk, hs, hn => by
    simp only [Advanced.lambdaWrap, freshIn, Bool.and_eq_true] at hf
    obtain ⟨hd₁, hk₁, hs₁, hnone⟩ := enter_binder hd hk hs hf.1
    obtain ⟨hd', hk', hs', hn', hf', hfacts, hxs⟩ := enter_lambdaWrap xs hf.2 hd₁ hk₁ hs₁ (hn.cons x)
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    refine ⟨hd', hk', hs', hn', hf', fun ρ as hF has => ?_, fun z hz => ?_⟩
    · cases as with
      | nil => simp at has
      | cons a as =>
        exact hfacts (ρ.extend a) as (hF.extend a hn hf.1 hnone) (by simpa using has)
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hf.1
      · have := hxs z hz
        rw [envLookupT_cons] at this
        split at this
        · simp at this
        · simpa using this

/-! ## Lookups in the environment of the body -/

theorem envLookupT_of_getElem : ∀ {env : List VarId} {i : Nat} {y : VarId}, EnvDistinct env →
    env[i]? = some y → envLookupT env y = some i
  | [], i, y, _, h => by simp at h
  | z :: env, 0, y, _, h => by
    simp at h; subst h
    exact MIR.envLookupT_cons_of_beq (varId_beq_self z) env
  | z :: env, i + 1, y, hd, h => by
    simp only [List.getElem?_cons_succ] at h
    have ih := envLookupT_of_getElem hd.2 h
    have hzy : (z == y) = false := by
      cases hc : (z == y)
      · rfl
      · have := hd.1
        rw [envLookupT_congr hc, ih] at this; cases this
    rw [envLookupT_cons_neq z y env hzy, ih]; rfl

theorem envLookupT_shift_many (y : VarId) (rest : List VarId) :
    ∀ (xs : List VarId), (∀ x ∈ xs, (x == y) = false) →
      envLookupT (xs.reverse ++ rest) y = (envLookupT rest y).map (· + xs.length)
  | [], _ => by simp
  | x :: xs, h => by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons]
    rw [envLookupT_shift_many y (x :: rest) xs (fun z hz => h z (.tail _ hz)),
      envLookupT_cons_neq x y rest (h x (.head _))]
    cases envLookupT rest y <;> simp; omega

theorem param_lookup {xs rest : List VarId} {p : Nat} {y : VarId} (hd : EnvDistinct (xs.reverse ++ rest))
    (hp : xs[p]? = some y) : envLookupT (xs.reverse ++ rest) y = some (xs.length - 1 - p) := by
  have hplt : p < xs.length := by
    rcases Nat.lt_or_ge p xs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none_iff.mpr h] at hp; cases hp
  apply envLookupT_of_getElem hd
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_reverse (by omega)]
  rw [show xs.length - 1 - (xs.length - 1 - p) = p by omega]; exact hp

theorem mem_listedParameters {params : List VarId} {P : List Nat} {y : VarId}
    (h : y ∈ listedParameters params P) : ∃ p ∈ P, params[p]? = some y := by
  simp only [listedParameters, List.mem_filterMap] at h
  obtain ⟨p, hp, hy⟩ := h
  exact ⟨p, hp, hy⟩

theorem lowerList_get {env : List VarId} :
    ∀ {es : List Expr} {ts : List Term} {p : Nat} {a : Expr},
      MIR.lowerTotalExprList env es = some ts → es[p]? = some a →
        ∃ ta, ts[p]? = some ta ∧ lowerTotalExpr env a = some ta
  | [], _, _, _, _, h => by simp at h
  | e :: es, ts, p, a, hl, hp => by
    rw [MIR.lowerTotalExprList_cons] at hl
    cases he : lowerTotalExpr env e with
    | none => rw [he] at hl; cases hl
    | some te =>
      cases hes : MIR.lowerTotalExprList env es with
      | none => rw [he, hes] at hl; cases hl
      | some tes =>
        rw [he, hes] at hl; cases hl
        cases p with
        | zero => simp at hp; subst hp; exact ⟨te, rfl, he⟩
        | succ p =>
          simp only [List.getElem?_cons_succ] at hp ⊢
          exact lowerList_get hes hp

theorem factRefines_applyAllT {d : Nat} {F : CekEnv → Prop} :
    ∀ {f f' : Term} {as as' : List Term}, FactRefines d F f f' →
      ListRel (FactRefines d F) as as' → closedAt d f' = true → closedAtList d as = true →
      closedAtList d as' = true → FactRefines d F (applyAllT f as) (applyAllT f' as')
  | _, _, [], [], hf, _, _, _, _ => hf
  | _, _, [], _ :: _, _, h, _, _, _ => absurd h id
  | _, _, _ :: _, [], _, h, _, _, _ => absurd h id
  | f, f', a :: as, a' :: as', hf, h, cf, ca, ca' => by
    simp only [closedAtList, Bool.and_eq_true] at ca ca'
    exact factRefines_applyAllT (f := .Apply f a) (f' := .Apply f' a')
      (factRefines_apply hf h.1 cf ca.1) h.2 (by simp [closedAt, cf, ca'.1]) ca.2 ca'.2

theorem freshIn_insert {f s : VarId} {env : List VarId} {e : Expr}
    (h : freshIn (f :: env) e = true) (hs : maxUidExpr e < s.uid) :
    freshIn (f :: s :: env) e = true := by
  refine freshIn_avoids e h ?_
  intro z hz
  rw [envLookupT_cons] at hz ⊢
  split
  · simp
  · rename_i hfz
    simp only [hfz, Bool.false_eq_true, if_false, Option.isSome_map] at hz ⊢
    rw [envLookupT_cons] at hz
    split at hz
    · rename_i hsz
      right
      have := (VarId.beq_true_iff s z).mp hsz
      omega
    · left; simpa using hz

theorem closedAtList_of_mem {d : Nat} : ∀ {ts : List Term} {t : Term}, closedAtList d ts = true →
    t ∈ ts → closedAt d t = true
  | [], _, _, h => by cases h
  | u :: us, t, h, hm => by
    simp only [closedAtList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h.1
    · exact closedAtList_of_mem h.2 hm

/-! ## The rewrite -/

/-- The lowered fixed points of a recursive function whose calls pass known
    lists at `P`, with the knot relating them in every environment realizing
    the facts. -/
theorem fix_setup {Γ : List (VarId × Expr)} {L : List VarId} {f : VarId}
    {params : List VarId} {inner inner' : Expr} {P : List Nat}
    (hne : params ≠ [])
    (hcheck : listCallsOK f params.length P (listedParameters params P ++ L) inner = true)
    (hbody : KnownRel Γ (listedParameters params P ++ L) inner inner')
    {env : List VarId} {tF : Term} (hd : EnvDistinct env) (hk : KeysBound Γ env)
    (hs : FactsScoped Γ env) (hn : NamesBound L env)
    (hfF : freshIn env (.Fix f (Advanced.lambdaWrap params inner)) = true)
    (htF : lowerTotalExpr env (.Fix f (Advanced.lambdaWrap params inner)) = some tF) :
    ∃ tB₁ tB₂ T₁ T₂, tF = fixLamWrapUplc tB₁ ∧
      lowerTotalExpr env (.Fix f (Advanced.lambdaWrap params inner')) =
        some (fixLamWrapUplc tB₂) ∧
      closedAt (env.length + 2 + params.length) T₁ = true ∧
      closedAt (env.length + 2 + params.length) T₂ = true ∧
      tB₁ = lams (params.length - 1) T₁ ∧ tB₂ = lams (params.length - 1) T₂ ∧
      ∀ ρ, EnvWellFormed env.length ρ → env.length ≤ ρ.length → KnownFacts Γ L env ρ →
        ∀ k, Knot P params.length tB₁ tB₂ T₁ T₂ ρ k := by
  obtain ⟨x₀, rest, rfl⟩ : ∃ x₀ rest, params = x₀ :: rest := by
    cases params with
    | nil => exact absurd rfl hne
    | cons x₀ rest => exact ⟨x₀, rest, rfl⟩
  have hm : 0 < (x₀ :: rest).length := by simp
  -- the self-application name
  let s : VarId := ⟨envMax env + maxUidExpr (Advanced.lambdaWrap (x₀ :: rest) inner) +
    maxUidExpr (expandFix (Advanced.lambdaWrap rest inner)) +
    maxUidExpr (expandFix (Advanced.lambdaWrap rest inner')) + f.uid + 1, .gen, "s"⟩
  have hs₁ : (freeVars (expandFix (Advanced.lambdaWrap rest inner))).contains s = false :=
    maxUidExpr_fresh _ _ (by simp [s]; omega)
  have hs₂ : (freeVars (expandFix (Advanced.lambdaWrap rest inner'))).contains s = false :=
    maxUidExpr_fresh _ _ (by simp [s]; omega)
  have hs_env : envLookupT env s = none := envLookupT_none_of_gt env s (by simp [s]; omega)
  have hwrap_uid : maxUidExpr (Advanced.lambdaWrap (x₀ :: rest) inner) < s.uid := by simp [s]; omega
  have hinner_uid : maxUidExpr inner < s.uid := by
    have : ∀ (xs : List VarId), maxUidExpr inner ≤ maxUidExpr (Advanced.lambdaWrap xs inner) := by
      intro xs
      induction xs with
      | nil => exact Nat.le_refl _
      | cons x xs ih => simp only [Advanced.lambdaWrap, maxUidExpr]; omega
    have := this (x₀ :: rest); omega
  -- source lowering
  simp only [Advanced.lambdaWrap] at htF
  rw [lowerTotalExpr_fix_lam_with_fresh env f x₀ _ s hs₁] at htF
  obtain ⟨tB₁, htB₁, rfl⟩ := Option.map_eq_some_iff.mp htF
  change lowerTotalExpr (x₀ :: f :: s :: env) (Advanced.lambdaWrap rest inner) = some tB₁ at htB₁
  rw [lowerTotalExpr_lambdaWrap] at htB₁
  obtain ⟨T₁, hT₁, rfl⟩ := Option.map_eq_some_iff.mp htB₁
  -- the environment of the body
  simp only [freshIn, Bool.and_eq_true] at hfF
  obtain ⟨hf_none, hfbody⟩ := hfF
  have hfs : (f == s) = false := by rw [VarId.beq_false_iff]; right; simp [s]; omega
  have hs_none : (envLookupT env s).isNone = true := by simp [hs_env]
  have hf_none' : (envLookupT (s :: env) f).isNone = true := by
    rw [envLookupT_cons]
    have : (s == f) = false := by
      cases h : (s == f)
      · rfl
      · exact absurd (varId_beq_symm h) (by simp [hfs])
    simp only [this, Bool.false_eq_true, if_false]; simpa using hf_none
  obtain ⟨hd₁, hk₁, hs₁', _⟩ := enter_binder hd hk hs hs_none
  obtain ⟨hd₂, hk₂, hs₂', _⟩ := enter_binder hd₁ hk₁ hs₁' hf_none'
  have hn₂ : NamesBound L (f :: s :: env) := (hn.cons s).cons f
  have hfbody' : freshIn (f :: s :: env) (Advanced.lambdaWrap (x₀ :: rest) inner) = true :=
    freshIn_insert (by simpa [Advanced.lambdaWrap, freshIn] using hfbody) hwrap_uid
  obtain ⟨hdN, hkN, hsN, hnN, hfN, hfactsN, hfreshP⟩ :=
    enter_lambdaWrap (Γ := Γ) (L := L) (x₀ :: rest) hfbody' hd₂ hk₂ hs₂' hn₂
  have henvN : (x₀ :: rest).reverse ++ f :: s :: env = rest.reverse ++ x₀ :: f :: s :: env := by simp
  have hdN' := hdN
  rw [henvN] at hdN hkN hsN hnN hfN
  -- lookups in the environment of the body
  have hlook_f : envLookupT (rest.reverse ++ x₀ :: f :: s :: env) f = some (rest.length + 1) := by
    apply envLookupT_of_getElem hdN
    rw [List.getElem?_append_right (by simp)]; simp
  have hlook_s : envLookupT (rest.reverse ++ x₀ :: f :: s :: env) s = some (rest.length + 2) := by
    apply envLookupT_of_getElem hdN
    rw [List.getElem?_append_right (by simp)]; simp
  have hlook_L : ∀ y j, envLookupT env y = some j →
      envLookupT (rest.reverse ++ x₀ :: f :: s :: env) y = some (j + (rest.length + 3)) := by
    intro y j hj
    have heq : rest.reverse ++ x₀ :: f :: s :: env = (s :: f :: x₀ :: rest).reverse ++ env := by simp
    rw [heq, envLookupT_shift_many y env _ ?_, hj]
    · first | (simp; done) | (simp; omega)
    · intro x hx
      cases h : (x == y)
      · rfl
      · exfalso
        rcases List.mem_cons.mp hx with rfl | hx
        · have := envLookupT_none_of_gt env y (by
            have := (VarId.beq_true_iff _ _).mp h
            simp [s] at this ⊢; omega)
          rw [hj] at this; cases this
        rcases List.mem_cons.mp hx with rfl | hx
        · have := hf_none; rw [envLookupT_congr h, hj] at this; cases this
        · have := hfreshP x (by simpa using hx)
          rw [envLookupT_cons] at this
          split at this
          · simp at this
          · rw [envLookupT_cons] at this
            split at this
            · simp at this
            · simp only [Option.isNone_map] at this
              rw [envLookupT_congr h, hj] at this; cases this
  -- names known to hold lists in the body
  let names := listedParameters (x₀ :: rest) P ++ L
  have hparam : ∀ p y, (x₀ :: rest)[p]? = some y →
      envLookupT (rest.reverse ++ x₀ :: f :: s :: env) y = some ((x₀ :: rest).length - 1 - p) := by
    intro p y hp
    rw [← henvN]; exact param_lookup hdN' hp
  have hnamesN : NamesBound names (rest.reverse ++ x₀ :: f :: s :: env) := by
    intro y hy
    simp only [names, List.contains_append, Bool.or_eq_true] at hy
    rcases hy with hy | hy
    · obtain ⟨y', hy', hyy'⟩ := List.contains_iff_exists_mem_beq.mp hy
      obtain ⟨p, _, hp⟩ := mem_listedParameters hy'
      rw [envLookupT_congr hyy', hparam p y' hp]; rfl
    · exact hnN y hy
  obtain ⟨T₂, hT₂, hrB⟩ := hbody _ T₁ hdN hfN hkN hsN hnamesN hT₁
  -- target lowering
  have htF' : lowerTotalExpr env (.Fix f (Advanced.lambdaWrap (x₀ :: rest) inner')) =
      some (fixLamWrapUplc (lams rest.length T₂)) := by
    simp only [Advanced.lambdaWrap]
    rw [lowerTotalExpr_fix_lam_with_fresh env f x₀ _ s hs₂]
    change (lowerTotalExpr (x₀ :: f :: s :: env) (Advanced.lambdaWrap rest inner')).map
      fixLamWrapUplc = _
    rw [lowerTotalExpr_lambdaWrap, hT₂]; rfl
  -- the list slots of the body
  have hlenN : (rest.reverse ++ x₀ :: f :: s :: env).length =
      env.length + 2 + (x₀ :: rest).length := by
    simp; omega
  have hcT₁ : closedAt (env.length + 2 + (x₀ :: rest).length) T₁ = true := by
    rw [← hlenN]; exact MIR.lowerTotalExpr_closedAt hT₁
  have hcT₂ : closedAt (env.length + 2 + (x₀ :: rest).length) T₂ = true := by
    rw [← hlenN]; exact MIR.lowerTotalExpr_closedAt hT₂
  have hB₁ : lams rest.length T₁ = lams ((x₀ :: rest).length - 1) T₁ := by simp
  have hB₂ : lams rest.length T₂ = lams ((x₀ :: rest).length - 1) T₂ := by simp
  let Ls : List Nat := names.filterMap fun y =>
    (envLookupT (rest.reverse ++ x₀ :: f :: s :: env) y).map (· + 1)
  have hctx : CheckCtx f [s] names (rest.reverse ++ x₀ :: f :: s :: env) ((x₀ :: rest).length + 1)
      [(x₀ :: rest).length + 2] Ls := by
    refine ⟨by rw [hlook_f]; simp, by omega, fun x hx => ?_, fun y hy => ?_⟩
    · simp only [List.mem_singleton] at hx; subst hx
      refine ⟨by omega, s, .head _, ?_⟩
      rw [hlook_s]; simp
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (hnamesN y hy)
    obtain ⟨y', hy', hyy'⟩ := List.contains_iff_exists_mem_beq.mp hy
    refine ⟨i, hi, List.mem_filterMap.mpr ⟨y', hy', ?_⟩⟩
    rw [← envLookupT_congr hyy', hi]; rfl
  have hcalls := lower_calls inner hctx (fun σ hσ => by simp at hσ; subst hσ; exact hinner_uid) hfN hcheck hT₁
  refine ⟨lams rest.length T₁, lams rest.length T₂, T₁, T₂, rfl, htF', hcT₁, hcT₂, hB₁, hB₂, ?_⟩
  intro ρ henv hlen hF
  have hLs : ∀ i ∈ Ls, (0 < i ∧ i ≤ (x₀ :: rest).length ∧ (x₀ :: rest).length - i ∈ P) ∨
      ((x₀ :: rest).length + 2 < i ∧ ∃ l, ρ.lookup (i - ((x₀ :: rest).length + 2)) = some l ∧
        ListValue l) := by
    intro i hi
    obtain ⟨y, hy, hyi⟩ := List.mem_filterMap.mp hi
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hyi
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨p, hpP, hp⟩ := mem_listedParameters hy
      rw [hparam p y hp] at hj; cases hj
      have hplt : p < (x₀ :: rest).length := by
        rcases Nat.lt_or_ge p (x₀ :: rest).length with h | h
        · exact h
        · rw [List.getElem?_eq_none_iff.mpr h] at hp; cases hp
      exact .inl ⟨by omega, by omega, by rw [show (x₀ :: rest).length - ((x₀ :: rest).length - 1 - p + 1) = p by omega]; exact hpP⟩
    · have hyc : L.contains y = true := List.contains_iff_exists_mem_beq.mpr ⟨y, hy, varId_beq_self y⟩
      obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.mp (hn y hyc)
      rw [hlook_L y j' hj'] at hj; cases hj
      obtain ⟨l, hl, hlv⟩ := hF.2 y hyc j' hj'
      refine .inr ⟨by simp; omega, l, ?_, hlv⟩
      rw [show j' + (rest.length + 3) + 1 - ((x₀ :: rest).length + 2) = j' + 1 by simp; omega]
      exact hl
  have hbody' : ∀ as : List CekValue, as.length = (x₀ :: rest).length →
      (∀ a ∈ as, ValueWellFormed a) → (∀ p ∈ P, ∀ a, as[p]? = some a → ListValue a) →
      ∀ π, StackWellFormed π →
      ObsRefines (.compute π (extendAll (fixEnv (lams rest.length T₂) ρ) as) T₁)
        (.compute π (extendAll (fixEnv (lams rest.length T₂) ρ) as) T₂) := by
    intro as has hw hlist π' hπ'
    have htB₂ : closedAt (env.length + 3) (lams rest.length T₂) = true := by
      rw [closedAt_lams]; simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcT₂
    obtain ⟨henv', hlen'⟩ := prefixEnv_wf henv hlen htB₂ hw
    have hF₁ : KnownFacts Γ L (s :: env) (ρ.extend (selfVal (lams rest.length T₂) ρ)) :=
      hF.extend _ hn hs_none (find?_none_of_unbound hk hs_none)
    have hF₂ : KnownFacts Γ L (f :: s :: env) (fixEnv (lams rest.length T₂) ρ) :=
      hF₁.extend _ (hn.cons s) hf_none' (find?_none_of_unbound hk₁ hf_none')
    have hF₃ := hfactsN _ as hF₂ has
    rw [henvN] at hF₃
    have hlisted : ListsHold (listedParameters (x₀ :: rest) P) (rest.reverse ++ x₀ :: f :: s :: env)
        (extendAll (fixEnv (lams rest.length T₂) ρ) as) := by
      intro y hy i hi
      obtain ⟨y', hy', hyy'⟩ := List.contains_iff_exists_mem_beq.mp hy
      obtain ⟨p, hpP, hp⟩ := mem_listedParameters hy'
      rw [envLookupT_congr hyy', hparam p y' hp] at hi; cases hi
      have hplt : p < (x₀ :: rest).length := by
        rcases Nat.lt_or_ge p (x₀ :: rest).length with h | h
        · exact h
        · rw [List.getElem?_eq_none_iff.mpr h] at hp; cases hp
      obtain ⟨a, ha⟩ : ∃ a, as[p]? = some a := by
        cases h : as[p]? with
        | none => rw [List.getElem?_eq_none_iff] at h; omega
        | some a => exact ⟨a, rfl⟩
      refine ⟨a, ?_, hlist p hpP a ha⟩
      rw [extendAll_lookup_low _ as _ (by omega) (by omega), has,
        show (x₀ :: rest).length - ((x₀ :: rest).length - 1 - p + 1) = p by omega]
      exact ha
    have hFN : KnownFacts Γ names (rest.reverse ++ x₀ :: f :: s :: env)
        (extendAll (fixEnv (lams rest.length T₂) ρ) as) := ⟨hF₃.1, hF₃.2.append hlisted⟩
    rw [has] at henv' hlen'
    exact hrB _ π' (by rw [hlenN]; exact henv') (by rw [hlenN]; exact hlen') hπ' hFN
  exact knot henv hlen hcT₁ hcT₂ hB₁ hB₂ hm hcalls hLs hbody'

theorem KnownRel.fixApp {Γ : List (VarId × Expr)} {L : List VarId} {f : VarId}
    {params : List VarId} {inner inner' : Expr} {args args' : List Expr} {P : List Nat}
    (hne : params ≠ []) (hlenA : params.length ≤ args.length)
    (hargs : ListRel (KnownRel Γ L) args args')
    (hpos : ∀ p ∈ P, ∃ a, args[p]? = some a ∧ listKnown Γ L a = true)
    (hcheck : listCallsOK f params.length P (listedParameters params P ++ L) inner = true)
    (hbody : KnownRel Γ (listedParameters params P ++ L) inner inner') :
    KnownRel Γ L (Advanced.applyAll (.Fix f (Advanced.lambdaWrap params inner)) args)
      (Advanced.applyAll (.Fix f (Advanced.lambdaWrap params inner')) args') := by
  intro env t hd hfresh hk hs hn hlow
  rw [freshIn_applyAll, Bool.and_eq_true] at hfresh
  obtain ⟨hfF, hfargs⟩ := hfresh
  obtain ⟨tF, targs, htF, htargs, rfl⟩ := lowerTotalExpr_applyAll_some hlow
  obtain ⟨targs', htargs', hrargs⟩ := KnownRel.list hargs env targs hd hfargs hk hs hn htargs
  obtain ⟨tB₁, tB₂, T₁, T₂, rfl, htF', hcT₁, hcT₂, hB₁, hB₂, hknot⟩ :=
    fix_setup hne hcheck hbody hd hk hs hn hfF htF
  refine ⟨_, lowerTotalExpr_applyAll_of htF' htargs', ?_⟩
  intro ρ π henv hlen hπ hF
  have hm : 0 < params.length := by
    cases params with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hlist : ∀ p ∈ P, ∀ a, targs[p]? = some a → ∀ v, Halts ρ a v → ListValue v := by
    intro p hp a ha v hv
    obtain ⟨a₀, ha₀, hl⟩ := hpos p hp
    obtain ⟨ta, hta, hlow⟩ := lowerList_get htargs ha₀
    rw [hta] at ha; cases ha
    exact listKnown_sound hl hF hd hlow hv
  have hclosedA := lowerTotalExprList_closedAtList htargs
  have hclosedA' := lowerTotalExprList_closedAtList htargs'
  have hnA : params.length ≤ targs.length := by
    rw [lowerList_length htargs]; exact hlenA
  refine obsRefines_trans (fixApply_obs henv hlen hcT₁ hcT₂ hB₁ hB₂ hm (hknot ρ henv hlen hF) targs hnA
    (fun a ha => closedAtList_of_mem hclosedA ha) hlist π hπ) ?_
  exact factRefines_applyAllT (FactRefines.refl _ _ _) hrargs
    (MIR.lowerTotalExpr_closedAt htF') hclosedA hclosedA' ρ π henv hlen hπ hF

/-! ## Let-bound recursive functions -/

theorem listKnown_bound {Γ : List (VarId × Expr)} {L env : List VarId} {y : VarId}
    (h : listKnown Γ L (.Var y) = true) (hk : KeysBound Γ env) (hn : NamesBound L env) :
    (envLookupT env y).isSome = true := by
  have h' : (L.contains y || (Γ.find? (fun entry => entry.1 == y)).any
      (fun entry => knownListValue 63 Γ L entry.2)) = true := h
  simp only [Bool.or_eq_true] at h'
  rcases h' with h | h
  · exact hn y h
  · cases hf : Γ.find? (fun entry => entry.1 == y) with
    | none => rw [hf] at h; cases h
    | some entry =>
      have hmem := List.mem_of_find?_eq_some hf
      have hbeq : (entry.1 == y) = true := by simpa using List.find?_some hf
      rw [← envLookupT_congr hbeq]; exact hk entry hmem

theorem fix_halts (tB : Term) (ρ : CekEnv) :
    Halts ρ (fixLamWrapUplc tB) (fixVal tB ρ) := ⟨17, by rw [steps_trans 16 1, fix_steps]; rfl⟩

theorem letFix_steps (tb tB : Term) (π : Stack) (ρ : CekEnv) :
    steps 20 (.compute π ρ (.Apply (.Lam 0 tb) (fixLamWrapUplc tB))) =
      .compute π (ρ.extend (fixVal tB ρ)) tb := by
  rw [show 20 = 3 + (16 + 1) from rfl, steps_trans, steps_trans]
  rw [show steps 3 (.compute π ρ (.Apply (.Lam 0 tb) (fixLamWrapUplc tB))) =
    .compute (.funV (.VLam tb ρ) :: π) ρ (fixLamWrapUplc tB) from rfl, fix_steps]
  rfl

theorem KnownRel.letFix {Γ : List (VarId × Expr)} {L : List VarId} {g f : VarId}
    {params : List VarId} {inner inner' b b' : Expr} {er : Bool} {P : List Nat} {B : List VarId}
    (hne : params ≠ [])
    (hcheck : listCallsOK f params.length P (listedParameters params P ++ L) inner = true)
    (hinner : KnownRel Γ (listedParameters params P ++ L) inner inner')
    (hcheckBody : listCallsOK g params.length P B b = true)
    (hB : ∀ y, B.contains y = true → listKnown Γ L (.Var y) = true)
    (hbody : KnownRel ((g, .Fix f (Advanced.lambdaWrap params inner')) :: Γ) L b b') :
    KnownRel Γ L (.Let [(g, .Fix f (Advanced.lambdaWrap params inner), er)] b)
      (.Let [(g, .Fix f (Advanced.lambdaWrap params inner'), er)] b') := by
  intro env t hd hfresh hk hs hn hlow
  rw [freshIn_let_single] at hfresh
  simp only [Bool.and_eq_true] at hfresh
  obtain ⟨⟨hfr, hx⟩, hfb⟩ := hfresh
  obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
  obtain ⟨tB₁, tB₂, T₁, T₂, rfl, htr', hcT₁, hcT₂, hB₁, hB₂, hknot⟩ :=
    fix_setup hne hcheck hinner hd hk hs hn hfr htr
  have hk' : KeysBound ((g, .Fix f (Advanced.lambdaWrap params inner')) :: Γ) (g :: env) := by
    intro entry hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · simp [envLookupT_cons, varId_beq_self]
    · exact hk.cons g entry hmem
  have hs' : FactsScoped ((g, .Fix f (Advanced.lambdaWrap params inner')) :: Γ) (g :: env) :=
    hs.push (by simp [htr'])
  obtain ⟨tb', htb', hrb⟩ := hbody (g :: env) tb (hd.cons hx) hfb hk' hs' (hn.cons g) htb
  refine ⟨.Apply (.Lam 0 tb') (fixLamWrapUplc tB₂), by rw [lowerTotalExpr_let_single, htr', htb']; rfl, ?_⟩
  -- the calls of `g` in the body
  let Ls : List Nat := B.filterMap fun y => (envLookupT (g :: env) y).map (· + 1)
  have hctx : CheckCtx g [] B (g :: env) 1 [] Ls := by
    refine ⟨by rw [MIR.envLookupT_cons_of_beq (varId_beq_self g)], by omega,
      fun x hx => (by cases hx), fun y hy => ?_⟩
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (listKnown_bound (hB y hy) hk hn)
    obtain ⟨y', hy', hyy'⟩ := List.contains_iff_exists_mem_beq.mp hy
    refine ⟨j + 1, lookup_shift hx hj, List.mem_filterMap.mpr ⟨y', hy', ?_⟩⟩
    rw [← envLookupT_congr hyy', lookup_shift hx hj]; rfl
  have hcalls := lower_calls b hctx (fun σ hσ => by cases hσ) hfb hcheckBody htb
  have hm : 0 < params.length := by
    cases params with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  intro ρ π henv hlen hπ hF
  have hK := hknot ρ henv hlen hF
  have htB₁ : closedAt (env.length + 3) tB₁ = true := tB_closed₁ hcT₁ hB₁ hm
  have htB₂ : closedAt (env.length + 3) tB₂ = true := tB_closed₂ hcT₂ hB₂ hm
  have hw₁ := fixVal_wf henv hlen htB₁
  have hw₂ := fixVal_wf henv hlen htB₂
  have henv₁ := envWellFormed_extend env.length henv hlen hw₁
  have henv₂ := envWellFormed_extend env.length henv hlen hw₂
  have hlen' : ∀ w : CekValue, env.length + 1 ≤ (ρ.extend w).length := by
    intro w; simp [CekEnv.extend, CekEnv.length]; omega
  have hctb := MIR.lowerTotalExpr_closedAt htb
  simp only [List.length_cons] at hctb hrb
  refine obsRefines_of_steps 20 20 ?_
  rw [letFix_steps, letFix_steps]
  apply obsRefines_of_forall_k
  intro k
  have henvOK : EnvOK P params.length k (env.length + 1) 1 [] Ls (ρ.extend (fixVal tB₁ ρ))
      (ρ.extend (fixVal tB₂ ρ)) := by
    refine ⟨fun n hn hnd h1 _ => ?_, fun i hi => ?_, ?_⟩
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [lookup_extend_succ _ _ _ (by omega), lookup_extend_succ _ _ _ (by omega)]
      obtain ⟨v, hv, hwf⟩ := envWellFormed_lookup env.length henv (n := n') (by omega) (by omega)
      exact ⟨v, v, hv, hv, valueRel_refl k v hwf⟩
    · obtain ⟨y, hy, hyi⟩ := List.mem_filterMap.mp hi
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hyi
      have hyc : B.contains y = true := List.contains_iff_exists_mem_beq.mpr ⟨y, hy, varId_beq_self y⟩
      obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.mp (listKnown_bound (hB y hyc) hk hn)
      rw [lookup_shift hx hj'] at hj; cases hj
      obtain ⟨l, hl, hlv⟩ := listKnown_var (hB y hyc) hF hd hj' henv
      refine ⟨l, ?_, ?_, hlv⟩
      · rw [lookup_extend_succ _ _ _ (by omega)]; exact hl
      · rw [lookup_extend_succ _ _ _ (by omega)]; exact hl
    · refine ⟨fixVal tB₁ ρ, fixVal tB₂ ρ, rfl, rfl, ?_, hw₁, hw₂⟩
      exact partial_PR henv hlen hcT₁ hcT₂ hB₁ hB₂ hm k (fun j _ => hK j) params.length hm
        (Nat.le_refl _) k (Nat.le_refl _) [] [] (by simp) trivial (by simp) (by simp) (by simp) _ _
        (fixVal_applies tB₁ T₁ hB₁) (fixVal_applies tB₂ T₂ hB₂)
  have hst₁ : Moist.Verified.TermObsRefinesWF.wfGuard.St (.compute π (ρ.extend (fixVal tB₁ ρ)) tb) := .compute hπ henv₁ (hlen' _) hctb
  have hst₂ : Moist.Verified.TermObsRefinesWF.wfGuard.St (.compute π (ρ.extend (fixVal tB₂ ρ)) tb) := .compute hπ henv₂ (hlen' _) hctb
  have hFb : KnownFacts ((g, .Fix f (Advanced.lambdaWrap params inner')) :: Γ) L (g :: env)
      (ρ.extend (fixVal tB₂ ρ)) :=
    ⟨FactsHold.push hF.1 ⟨_, htr', fix_halts tB₂ ρ⟩, hF.2.extend _ hn hx⟩
  exact InlineSoundness.SubstRefinesExt.obsRefinesK_compose_obsRefines_right
    (calls_eval hcalls hctb henvOK k (Nat.le_refl _) π π (stackRel_refl k hπ) hst₁ hst₂)
    (hrb _ π henv₂ (hlen' _) hπ hFb)

end Moist.Verified.KnownLists
