namespace Moist
namespace Plutus
namespace Lemma

theorem String.data_length_of_nonEmpty_pos (s : String) (h : s ≠ "") : 0 < List.length s.data := by
  obtain ⟨data⟩ := s
  induction data
  . contradiction
  . simp

theorem String.drop_decreases_data_length (s : String) (n : Nat) (hs : s ≠ "") (hn : 0 < n) : (List.drop n s.data).length < s.data.length := by
    have hs0 : 0 < List.length s.data := String.data_length_of_nonEmpty_pos s hs
    simp
    omega

theorem List.empty_length_gt_zero (l : List α) (h : l ≠ []) : 0 < l.length := by
  induction l
  . contradiction
  . simp

theorem List.drop_decreases_length (l : List α) (n : Nat) (hl : l ≠ []) (hn : 0 < n) : (List.drop n l).length < l.length := by
    have hl0 : 0 < List.length l := List.empty_length_gt_zero l hl
    simp
    omega

end Lemma
end Plutus
end Moist
