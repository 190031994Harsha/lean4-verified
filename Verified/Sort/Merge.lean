import Mathlib

/-!
# Correctness of bottom-up merge sort on natural-number lists (well-founded
recursion with termination_by/decreasing_by): sorted output, permutation of input.
-/

def merge : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys
termination_by xs ys => xs.length + ys.length
decreasing_by
  all_goals simp_wf

def msort : List ℕ → List ℕ
  | [] => []
  | [x] => [x]
  | x :: y :: tl =>
      merge (msort ((x :: y :: tl).take ((x :: y :: tl).length / 2)))
            (msort ((x :: y :: tl).drop ((x :: y :: tl).length / 2)))
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- One-step unfoldings of `merge`. -/
lemma merge_nil_left (ys : List ℕ) : merge [] ys = ys := by rw [merge.eq_def]

lemma merge_nil_right (xs : List ℕ) : merge xs [] = xs := by
  cases xs with
  | nil => rw [merge.eq_def]
  | cons x xs => rw [merge.eq_def]

lemma merge_cons (x y : ℕ) (xs ys : List ℕ) :
    merge (x :: xs) (y :: ys) =
      if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys := by
  rw [merge.eq_def]

/-- `merge` produces a permutation of the concatenation. -/
lemma perm_merge (xs ys : List ℕ) : List.Perm (merge xs ys) (xs ++ ys) := by
  induction xs, ys using merge.induct with
  | case1 ys =>
      simp [merge_nil_left]
  | case2 xs _ =>
      simp [merge_nil_right]
  | case3 x xs y ys h ih =>
      rw [merge_cons, if_pos h, List.cons_append]
      exact ih.cons x
  | case4 x xs y ys h ih =>
      rw [merge_cons, if_neg h]
      exact (ih.cons y).trans (List.perm_middle.symm)

/-- Every member of `merge xs ys` comes from `xs` or `ys`. -/
lemma mem_merge {xs ys : List ℕ} {b : ℕ} (h : b ∈ merge xs ys) : b ∈ xs ∨ b ∈ ys := by
  have hp := perm_merge xs ys
  rw [hp.mem_iff] at h
  exact List.mem_append.mp h

/-- `merge` of two `≤`-sorted lists is sorted. -/
lemma pairwise_merge {xs ys : List ℕ} (hx : xs.Pairwise (· ≤ ·)) (hy : ys.Pairwise (· ≤ ·)) :
    (merge xs ys).Pairwise (· ≤ ·) := by
  induction xs, ys using merge.induct with
  | case1 ys =>
      rwa [merge_nil_left]
  | case2 xs _ =>
      rwa [merge_nil_right]
  | case3 x xs y ys h ih =>
      -- keep `x` in front; it is below everything in `merge xs (y :: ys)`.
      rw [merge_cons, if_pos h, List.pairwise_cons]
      obtain ⟨hxh, hxt⟩ := List.pairwise_cons.mp hx
      obtain ⟨hyh, _⟩ := List.pairwise_cons.mp hy
      refine ⟨?_, ih hxt hy⟩
      intro b hb
      rcases mem_merge hb with hb | hb
      · exact hxh b hb
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact h
        · exact Nat.le_trans h (hyh b hb)
  | case4 x xs y ys h ih =>
      -- keep `y` in front; `¬ x ≤ y` gives `y ≤ x`, and `y` is below all of `ys`.
      rw [merge_cons, if_neg h, List.pairwise_cons]
      obtain ⟨hyh, hyt⟩ := List.pairwise_cons.mp hy
      refine ⟨?_, ih hx hyt⟩
      intro b hb
      rcases mem_merge hb with hb | hb
      · rcases List.mem_cons.mp hb with rfl | hb
        · omega
        · exact Nat.le_trans (by omega) ((List.pairwise_cons.mp hx).1 b hb)
      · exact hyh b hb

/-- One-step unfolding of `msort` on a list with at least two elements. -/
lemma msort_cons_cons (x y : ℕ) (tl : List ℕ) :
    msort (x :: y :: tl) =
      merge (msort ((x :: y :: tl).take ((x :: y :: tl).length / 2)))
            (msort ((x :: y :: tl).drop ((x :: y :: tl).length / 2))) := by
  rw [msort.eq_def]

theorem msort_sorted_perm (l : List ℕ) :
    (msort l).Pairwise (· ≤ ·) ∧ List.Perm (msort l) l := by
  induction l using msort.induct with
  | case1 =>
      rw [msort.eq_def]
      exact ⟨by simp, List.Perm.refl []⟩
  | case2 x =>
      rw [msort.eq_def]
      exact ⟨by simp, List.Perm.refl [x]⟩
  | case3 x y tl ih1 ih2 =>
      rw [msort_cons_cons]
      constructor
      · exact pairwise_merge ih1.1 ih2.1
      · exact (perm_merge _ _).trans
          ((List.Perm.append ih1.2 ih2.2).trans
            (by rw [List.take_append_drop]))
