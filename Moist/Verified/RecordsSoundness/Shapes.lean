import Moist.MIR.Optimize.Advanced.Records
import Moist.Verified.ShapesSoundness.Rewrites
import Moist.Verified.ListShapeSoundness

/-! # Shapes of returned values

`ShapeHolds s v` says that the value `v` has shape `s`. A constructor shape
fixes the tag and the number of fields; a union accepts either side. The
lemmas below read the fields of one tag off a shape (`atTag_constr`), show
that only constructors have constructor shapes (`atTag_other`), and turn
`isRecord` into a constructor `0` with the expected number of fields
(`isRecord_holds`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

mutual
  def ShapeHolds : Shape → CekValue → Prop
    | .any, _ => True
    | .none, _ => False
    | .constr tag fields, v => ∃ vs, v = .VConstr tag vs ∧ FieldsHold fields vs
    | .union left right, v => ShapeHolds left v ∨ ShapeHolds right v

  def FieldsHold : List Shape → List CekValue → Prop
    | [], [] => True
    | shape :: shapes, v :: vs => ShapeHolds shape v ∧ FieldsHold shapes vs
    | [], _ :: _ => False
    | _ :: _, [] => False
end

theorem fieldsHold_length : ∀ {shapes : List Shape} {vs : List CekValue},
    FieldsHold shapes vs → shapes.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [FieldsHold] at h
    simp [fieldsHold_length h.2]
  | [], _ :: _, h => by simp [FieldsHold] at h
  | _ :: _, [], h => by simp [FieldsHold] at h

theorem fieldsHold_get : ∀ {shapes : List Shape} {vs : List CekValue},
    FieldsHold shapes vs → ∀ (k : Nat) (s : Shape) (v : CekValue), shapes[k]? = some s →
      vs[k]? = some v → ShapeHolds s v
  | [], [], _, _, _, _, h, _ => by simp at h
  | s₀ :: _, v₀ :: _, h, 0, s, v, hs, hv => by
    simp only [FieldsHold] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs hv
    subst hs hv; exact h.1
  | _ :: _, _ :: _, h, k + 1, s, v, hs, hv => by
    simp only [FieldsHold] at h
    exact fieldsHold_get h.2 k s v (by simpa using hs) (by simpa using hv)
  | [], _ :: _, h, _, _, _, _, _ => by simp [FieldsHold] at h
  | _ :: _, [], h, _, _, _, _, _ => by simp [FieldsHold] at h

theorem fieldsHold_of_get : ∀ {shapes : List Shape} {vs : List CekValue},
    shapes.length = vs.length →
    (∀ (k : Nat) (s : Shape) (v : CekValue), shapes[k]? = some s → vs[k]? = some v → ShapeHolds s v) →
    FieldsHold shapes vs
  | [], [], _, _ => by simp [FieldsHold]
  | s :: shapes, v :: vs, hlen, h => by
    simp only [FieldsHold]
    exact ⟨h 0 s v rfl rfl, fieldsHold_of_get (by simpa using hlen)
      fun k s' v' hs hv => h (k + 1) s' v' (by simpa using hs) (by simpa using hv)⟩
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

theorem fieldsHold_zipWith_left : ∀ {left right : List Shape} {vs : List CekValue},
    FieldsHold left vs → left.length = right.length →
      FieldsHold (List.zipWith Shape.union left right) vs
  | [], [], [], _, _ => by simp [FieldsHold]
  | _ :: _, _ :: _, _ :: _, h, hlen => by
    simp only [FieldsHold] at h
    simp only [List.zipWith_cons_cons, FieldsHold, ShapeHolds]
    exact ⟨.inl h.1, fieldsHold_zipWith_left h.2 (by simpa using hlen)⟩
  | [], _ :: _, _, _, hlen => by simp at hlen
  | _ :: _, [], _, _, hlen => by simp at hlen
  | [], [], _ :: _, h, _ => by simp [FieldsHold] at h
  | _ :: _, _ :: _, [], h, _ => by simp [FieldsHold] at h

theorem fieldsHold_zipWith_right : ∀ {left right : List Shape} {vs : List CekValue},
    FieldsHold right vs → left.length = right.length →
      FieldsHold (List.zipWith Shape.union left right) vs
  | [], [], [], _, _ => by simp [FieldsHold]
  | _ :: _, _ :: _, _ :: _, h, hlen => by
    simp only [FieldsHold] at h
    simp only [List.zipWith_cons_cons, FieldsHold, ShapeHolds]
    exact ⟨.inr h.1, fieldsHold_zipWith_right h.2 (by simpa using hlen)⟩
  | [], _ :: _, _, _, hlen => by simp at hlen
  | _ :: _, [], _, _, hlen => by simp at hlen
  | [], [], _ :: _, h, _ => by simp [FieldsHold] at h
  | _ :: _, _ :: _, [], h, _ => by simp [FieldsHold] at h

theorem merge_unknown_right (x : TagFields) : x.merge .unknown = .unknown := by
  cases x <;> rfl

/-- The fields a shape records for the tag of a constructor value. -/
theorem atTag_constr : ∀ (s : Shape) {tag : Nat} {vs : List CekValue},
    ShapeHolds s (.VConstr tag vs) →
      s.atTag tag = .unknown ∨ ∃ shapes, s.atTag tag = .fields shapes ∧ FieldsHold shapes vs
  | .any, _, _, _ => .inl rfl
  | .none, _, _, h => by simp [ShapeHolds] at h
  | .constr other fields, tag, vs, h => by
    simp only [ShapeHolds] at h
    obtain ⟨ws, hw, hf⟩ := h
    cases hw
    right
    exact ⟨fields, by simp [Shape.atTag], hf⟩
  | .union left right, tag, vs, h => by
    simp only [ShapeHolds] at h
    simp only [Shape.atTag]
    rcases h with h | h
    · rcases atTag_constr left h with hl | ⟨shapes, hl, hf⟩
      · rw [hl]; exact .inl rfl
      · rw [hl]
        cases hr : right.atTag tag with
        | unknown => exact .inl rfl
        | unreachable => exact .inr ⟨shapes, rfl, hf⟩
        | fields others =>
          simp only [TagFields.merge]
          split
          · rename_i hlen
            exact .inr ⟨_, rfl, fieldsHold_zipWith_left hf (by simpa using hlen)⟩
          · exact .inl rfl
    · rcases atTag_constr right h with hr | ⟨shapes, hr, hf⟩
      · rw [hr, merge_unknown_right]; exact .inl rfl
      · rw [hr]
        cases hl : left.atTag tag with
        | unknown => exact .inl rfl
        | unreachable => exact .inr ⟨shapes, rfl, hf⟩
        | fields others =>
          simp only [TagFields.merge]
          split
          · rename_i hlen
            exact .inr ⟨_, rfl, fieldsHold_zipWith_right hf (by simpa using hlen)⟩
          · exact .inl rfl

/-- A value that is not a constructor has no recorded fields at any tag. -/
theorem atTag_other : ∀ (s : Shape) {v : CekValue}, ShapeHolds s v →
    (∀ tag vs, v ≠ .VConstr tag vs) → ∀ tag, s.atTag tag = .unknown
  | .any, _, _, _, _ => rfl
  | .none, _, h, _, _ => by simp [ShapeHolds] at h
  | .constr _ _, _, h, hv, _ => by
    simp only [ShapeHolds] at h
    obtain ⟨vs, rfl, _⟩ := h
    exact absurd rfl (hv _ vs)
  | .union left right, _, h, hv, tag => by
    simp only [ShapeHolds] at h
    simp only [Shape.atTag]
    rcases h with h | h
    · rw [atTag_other left h hv tag]; rfl
    · rw [atTag_other right h hv tag, merge_unknown_right]

theorem tagZeroOnly_holds : ∀ (s : Shape) {v : CekValue}, s.tagZeroOnly = true → ShapeHolds s v →
    ∃ vs, v = .VConstr 0 vs
  | .any, _, h, _ => by simp [Shape.tagZeroOnly] at h
  | .none, _, _, h => by simp [ShapeHolds] at h
  | .constr tag _, _, h, hv => by
    simp only [Shape.tagZeroOnly, beq_iff_eq] at h
    subst h
    simp only [ShapeHolds] at hv
    obtain ⟨vs, rfl, _⟩ := hv
    exact ⟨vs, rfl⟩
  | .union left right, _, h, hv => by
    simp only [Shape.tagZeroOnly, Bool.and_eq_true] at h
    simp only [ShapeHolds] at hv
    rcases hv with hv | hv
    · exact tagZeroOnly_holds left h.1 hv
    · exact tagZeroOnly_holds right h.2 hv

/-- A record shape: constructor `0` with exactly `arity` fields. -/
theorem isRecord_holds {s : Shape} {v : CekValue} {arity : Nat} (h : s.isRecord arity = true)
    (hv : ShapeHolds s v) : ∃ vs, v = .VConstr 0 vs ∧ vs.length = arity := by
  unfold Shape.isRecord at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hzero, hfields⟩ := h
  obtain ⟨vs, rfl⟩ := tagZeroOnly_holds s hzero hv
  refine ⟨vs, rfl, ?_⟩
  rcases atTag_constr s hv with hu | ⟨shapes, hs, hf⟩
  · rw [hu] at hfields; cases hfields
  · rw [hs] at hfields
    simp only [beq_iff_eq] at hfields
    rw [← fieldsHold_length hf, hfields]

/-- Either the value is a constructor or the shape accepts every value. -/
theorem holds_constr_or_any : ∀ (s : Shape) {v : CekValue}, ShapeHolds s v →
    (∃ tag vs, v = .VConstr tag vs) ∨ ∀ w, ShapeHolds s w
  | .any, _, _ => .inr fun _ => trivial
  | .none, _, h => by simp [ShapeHolds] at h
  | .constr _ _, _, h => by
    simp only [ShapeHolds] at h
    obtain ⟨vs, rfl, _⟩ := h
    exact .inl ⟨_, vs, rfl⟩
  | .union left right, _, h => by
    simp only [ShapeHolds] at h
    rcases h with h | h
    · rcases holds_constr_or_any left h with hc | hall
      · exact .inl hc
      · exact .inr fun w => .inl (hall w)
    · rcases holds_constr_or_any right h with hc | hall
      · exact .inl hc
      · exact .inr fun w => .inr (hall w)

theorem fieldsHold_map_any : ∀ {α : Type} (xs : List α) (vs : List CekValue),
    xs.length = vs.length → FieldsHold (xs.map fun _ => Shape.any) vs
  | _, [], [], _ => by simp [FieldsHold]
  | _, _ :: xs, _ :: vs, h => by
    simp only [List.map_cons, FieldsHold, ShapeHolds, true_and]
    exact fieldsHold_map_any xs vs (by simpa using h)
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

end Moist.Verified.ShapeFacts
