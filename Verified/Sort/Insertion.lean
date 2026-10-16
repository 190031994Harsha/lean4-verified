import Mathlib

/-!
# Correctness of insertion sort on natural-number lists: the output is sorted
and a permutation of the input.
-/

def ins (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys

def isort : List ℕ → List ℕ
  | [] => []
  | x :: xs => ins x (isort xs)

/-- Insertion only rearranges: `ins x l` is a permutation of `x :: l`. -/
lemma perm_ins (x : ℕ) (l : List ℕ) : List.Perm (ins x l) (x :: l) := by
  induction l with
  | nil =>
      simp [ins]
  | cons y ys ih =>
      by_cases h : x ≤ y
      · -- `x` goes in front, nothing else moves.
        simpa [ins, h] using List.Perm.refl (x :: y :: ys)
      · -- keep `y` in front, insert into the tail, then swap the two heads.
        simp only [ins, if_neg h]
        exact (ih.cons y).trans (List.Perm.swap _ _ _)

/-- Insertion preserves sortedness of a `≤`-ordered list. -/
lemma pairwise_ins {l : List ℕ} (hl : l.Pairwise (· ≤ ·)) (x : ℕ) :
    (ins x l).Pairwise (· ≤ ·) := by
  induction l with
  | nil =>
      simp [ins]
  | cons y ys ih =>
      obtain ⟨hy, hys⟩ := List.pairwise_cons.mp hl
      by_cases hxy : x ≤ y
      · -- `x` becomes the new head and sits below everything after it.
        rw [ins, if_pos hxy, List.pairwise_cons]
        refine ⟨?_, hl⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hxy
        · exact Nat.le_trans hxy (hy b hb)
      · -- `y` keeps the head; members of `ins x ys` are `x` or members of `ys`.
        rw [ins, if_neg hxy, List.pairwise_cons]
        refine ⟨?_, ih hys⟩
        intro b hb
        have hb' : b ∈ x :: ys := (perm_ins x ys).mem_iff.mp hb
        rcases List.mem_cons.mp hb' with rfl | hb'
        · omega
        · exact hy b hb'

theorem isort_sorted_perm (l : List ℕ) :
    (isort l).Pairwise (· ≤ ·) ∧ List.Perm (isort l) l := by
  induction l with
  | nil =>
      simp [isort]
  | cons x xs ih =>
      exact ⟨pairwise_ins ih.1 x, (perm_ins x (isort xs)).trans (ih.2.cons x)⟩
