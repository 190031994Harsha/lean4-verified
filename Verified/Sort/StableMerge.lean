import Mathlib

/-!
# Stable merge sort on key/value pairs: keys sorted, permutation of input, and
stability (filtering by any key preserves the input subsequence exactly).
-/

/-!
# Stable merge sort: correctness proof

`msortP` sorts key/value pairs by key. We prove three things at once:
sortedness on keys, permutation of the input, and stability (the subsequence
of entries with any given key is preserved exactly).

Proof outline: unfoldings of the two functions via their equation lemmas;
`mergeP_perm` (merge yields a permutation of the concatenation, with
`List.perm_middle` moving the head in the else branch); `mergeP_sorted`
(merge preserves sortedness, using the permutation to transport membership);
`mergeP_filter` (for sorted inputs, filtering the merge by a key equals the
concatenation of the filtered inputs — the sortedness hypotheses are what make
the left-before-right tie order exact); then well-founded induction via
`msortP`'s recursion structure, closing with `List.take_append_drop` and
`List.filter_append`.
-/


def mergeP : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if x.1 ≤ y.1 then x :: mergeP xs (y :: ys) else y :: mergeP (x :: xs) ys
termination_by xs ys => xs.length + ys.length
decreasing_by
  all_goals simp_wf

def msortP : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | [x] => [x]
  | x :: y :: tl =>
      mergeP (msortP ((x :: y :: tl).take ((x :: y :: tl).length / 2)))
             (msortP ((x :: y :: tl).drop ((x :: y :: tl).length / 2)))
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  all_goals omega

lemma mergeP_nil_left (ys : List (ℕ × ℕ)) : mergeP [] ys = ys := by
  first
  | (rw [mergeP]; done)
  | (simp [mergeP]; done)
  | (unfold mergeP; rfl)

lemma mergeP_cons_nil (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) : mergeP (x :: xs) [] = x :: xs := by
  first
  | (simp [mergeP]; done)
  | (rw [mergeP]; done)
  | (unfold mergeP; rfl)

lemma mergeP_cons_cons (x y : ℕ × ℕ) (xs ys : List (ℕ × ℕ)) :
    mergeP (x :: xs) (y :: ys) =
      if x.1 ≤ y.1 then x :: mergeP xs (y :: ys) else y :: mergeP (x :: xs) ys := by
  first
  | (rw [mergeP]; done)
  | (unfold mergeP; rfl)
  | (simp [mergeP]; done)
  | exact mergeP.eq_3 x xs y ys

lemma mergeP_perm : ∀ (xs ys : List (ℕ × ℕ)), (mergeP xs ys).Perm (xs ++ ys)
  | [], ys => by simp [mergeP_nil_left]
  | x :: xs, [] => by simp [mergeP_cons_nil]
  | x :: xs, y :: ys => by
    rw [mergeP_cons_cons]
    split_ifs with h
    · exact List.Perm.cons x (mergeP_perm xs (y :: ys))
    · have := mergeP_perm (x :: xs) ys
      exact (List.Perm.cons y this).trans List.perm_middle.symm

lemma mergeP_sorted : ∀ (xs ys : List (ℕ × ℕ)),
    xs.Pairwise (fun p q => p.1 ≤ q.1) → ys.Pairwise (fun p q => p.1 ≤ q.1) →
    (mergeP xs ys).Pairwise (fun p q => p.1 ≤ q.1)
  | [], ys, _, hy => by rw [mergeP_nil_left]; exact hy
  | x :: xs, [], hx, _ => by rw [mergeP_cons_nil]; exact hx
  | x :: xs, y :: ys, hx, hy => by
    have hx' := List.pairwise_cons.1 hx
    have hy' := List.pairwise_cons.1 hy
    rw [mergeP_cons_cons]
    split_ifs with h
    · have ih := mergeP_sorted xs (y :: ys) hx'.2 hy
      refine List.pairwise_cons.2 ⟨?_, ih⟩
      intro a ha
      have ha' := (mergeP_perm xs (y :: ys)).mem_iff.1 ha
      simp only [List.mem_append, List.mem_cons] at ha'
      rcases ha' with ha' | rfl | ha'
      · exact hx'.1 a ha'
      · exact h
      · exact le_trans h (hy'.1 a ha')
    · have ih := mergeP_sorted (x :: xs) ys hx hy'.2
      refine List.pairwise_cons.2 ⟨?_, ih⟩
      intro a ha
      have ha' := (mergeP_perm (x :: xs) ys).mem_iff.1 ha
      simp only [List.mem_append, List.mem_cons] at ha'
      rcases ha' with (rfl | ha') | ha'
      · omega
      · have := hx'.1 a ha'
        omega
      · exact hy'.1 a ha'

lemma mergeP_filter (k : ℕ) : ∀ (xs ys : List (ℕ × ℕ)),
    xs.Pairwise (fun p q => p.1 ≤ q.1) → ys.Pairwise (fun p q => p.1 ≤ q.1) →
    (mergeP xs ys).filter (fun p => p.1 = k)
      = xs.filter (fun p => p.1 = k) ++ ys.filter (fun p => p.1 = k)
  | [], ys, _, _ => by simp [mergeP_nil_left]
  | x :: xs, [], _, _ => by simp [mergeP_cons_nil]
  | x :: xs, y :: ys, hx, hy => by
    have hx' := List.pairwise_cons.1 hx
    have hy' := List.pairwise_cons.1 hy
    rw [mergeP_cons_cons]
    split_ifs with h
    · have ih := mergeP_filter k xs (y :: ys) hx'.2 hy
      by_cases hk : x.1 = k
      · simp [List.filter_cons, hk, ih]
      · simp [List.filter_cons, hk, ih]
    · have ih := mergeP_filter k (x :: xs) ys hx hy'.2
      by_cases hk : y.1 = k
      · have hxs : (x :: xs).filter (fun p => p.1 = k) = [] := by
          first
          | rw [List.filter_eq_nil_iff]
          | rw [List.filter_eq_nil]
          intro a ha
          simp only [List.mem_cons] at ha
          have hxa : x.1 ≤ a.1 := by
            rcases ha with rfl | ha
            · exact le_refl _
            · exact hx'.1 a ha
          simp only [decide_eq_true_eq]
          omega
        rw [hxs, List.nil_append] at ih
        rw [hxs, List.nil_append]
        simp [List.filter_cons, ih]
      · simp [List.filter_cons, hk, ih]

lemma msortP_nil : msortP [] = [] := by
  first
  | (simp [msortP]; done)
  | (rw [msortP]; done)
  | (unfold msortP; rfl)

lemma msortP_single (x : ℕ × ℕ) : msortP [x] = [x] := by
  first
  | (simp [msortP]; done)
  | (rw [msortP]; done)
  | (unfold msortP; rfl)

lemma msortP_cons2 (x y : ℕ × ℕ) (tl : List (ℕ × ℕ)) :
    msortP (x :: y :: tl) =
      mergeP (msortP ((x :: y :: tl).take ((x :: y :: tl).length / 2)))
             (msortP ((x :: y :: tl).drop ((x :: y :: tl).length / 2))) := by
  first
  | (rw [msortP]; done)
  | exact msortP.eq_3 x y tl
  | (conv_lhs => unfold msortP)
  | (simp only [msortP]; done)

lemma msortP_correct' : ∀ (l : List (ℕ × ℕ)),
    (msortP l).Pairwise (fun p q => p.1 ≤ q.1) ∧
    List.Perm (msortP l) l ∧
    ∀ k : ℕ, (msortP l).filter (fun p => p.1 = k) = l.filter (fun p => p.1 = k)
  | [] => by simp [msortP_nil]
  | [x] => by simp [msortP_single]
  | x :: y :: tl => by
    have h1 := msortP_correct' ((x :: y :: tl).take ((x :: y :: tl).length / 2))
    have h2 := msortP_correct' ((x :: y :: tl).drop ((x :: y :: tl).length / 2))
    rw [msortP_cons2]
    refine ⟨mergeP_sorted _ _ h1.1 h2.1, ?_, ?_⟩
    · refine (mergeP_perm _ _).trans ?_
      refine (List.Perm.append h1.2.1 h2.2.1).trans ?_
      first
      | exact List.Perm.of_eq (List.take_append_drop _ _)
      | (rw [List.take_append_drop])
      | simp
    · intro k
      rw [mergeP_filter k _ _ h1.1 h2.1, h1.2.2 k, h2.2.2 k, ← List.filter_append,
        List.take_append_drop]
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (simp; omega) | simp

theorem msortP_correct (l : List (ℕ × ℕ)) :
    (msortP l).Pairwise (fun p q => p.1 ≤ q.1) ∧
    List.Perm (msortP l) l ∧
    ∀ k : ℕ, (msortP l).filter (fun p => p.1 = k) = l.filter (fun p => p.1 = k) := by
  exact msortP_correct' l

