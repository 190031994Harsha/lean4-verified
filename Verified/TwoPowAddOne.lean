import Mathlib

/-!
# The only solutions of `2 ^ a + 1 = 3 ^ b` are `(1, 1)` and `(3, 2)`

Elementary argument (Levi ben Gerson's theorem, the `2/3` case of Catalan):

* If `4 ≤ a` then `16 ∣ 2 ^ a`, so `3 ^ b = 2 ^ a + 1 ≡ 1 [MOD 16]`.
* The powers of `3` modulo `16` cycle with period `4` (`3 ^ 4 = 81 ≡ 1`), and
  `3 ^ 1 ≡ 3`, `3 ^ 2 ≡ 9`, `3 ^ 3 ≡ 11`, so `3 ^ b ≡ 1 [MOD 16]` forces `4 ∣ b`.
* Then `3 ^ b ≡ (3 ^ 4) ^ (b / 4) ≡ 1 [MOD 5]`, hence `2 ^ a + 1 ≡ 1 [MOD 5]`,
  i.e. `5 ∣ 2 ^ a` — impossible, since powers of `2` are never `≡ 0 [MOD 5]`.
* So `a ≤ 3`, which bounds `3 ^ b = 2 ^ a + 1 ≤ 9`, hence `b ≤ 2`.
  The remaining `4 × 3` pairs are checked one by one.
-/

/-- Powers of `x` are periodic modulo `n` with period `k` once `x ^ k ≡ 1 [MOD n]`. -/
private lemma pow_mod_period {x n k : ℕ} (h : x ^ k ≡ 1 [MOD n]) (m : ℕ) :
    x ^ m ≡ x ^ (m % k) [MOD n] := by
  conv_lhs => rw [← Nat.div_add_mod m k, pow_add, pow_mul]
  calc (x ^ k) ^ (m / k) * x ^ (m % k)
      ≡ 1 ^ (m / k) * x ^ (m % k) [MOD n] := (h.pow _).mul (Nat.ModEq.refl _)
    _ = x ^ (m % k) := by rw [one_pow, one_mul]

/-- Modulo `16`, a power of `3` depends only on the exponent modulo `4`. -/
private lemma three_pow_mod16 (b : ℕ) : 3 ^ b % 16 = 3 ^ (b % 4) % 16 :=
  pow_mod_period (by decide) b

/-- Modulo `5`, a power of `3` depends only on the exponent modulo `4`. -/
private lemma three_pow_mod5 (b : ℕ) : 3 ^ b % 5 = 3 ^ (b % 4) % 5 :=
  pow_mod_period (by decide) b

/-- Modulo `5`, a power of `2` depends only on the exponent modulo `4`. -/
private lemma two_pow_mod5 (a : ℕ) : 2 ^ a % 5 = 2 ^ (a % 4) % 5 :=
  pow_mod_period (by decide) a

/-- No power of `2` is divisible by `5`. -/
private lemma two_pow_mod5_ne_zero (a : ℕ) : 2 ^ a % 5 ≠ 0 := by
  have h := two_pow_mod5 a
  have hc : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rcases hc with h4 | h4 | h4 | h4 <;> rw [h4] at h <;> norm_num at h <;> omega

/-- If `3 ^ b ≡ 1 [MOD 16]` then the exponent is a multiple of `4`. -/
private lemma mod4_eq_zero_of_three_pow_mod16 {b : ℕ} (hb : 3 ^ b % 16 = 1) : b % 4 = 0 := by
  have h := three_pow_mod16 b
  have hc : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
  rcases hc with h4 | h4 | h4 | h4 <;> rw [h4] at h <;> norm_num at h <;> omega

/-- Any solution of `2 ^ a + 1 = 3 ^ b` has `a < 4`. -/
private lemma a_lt_four {a b : ℕ} (h : 2 ^ a + 1 = 3 ^ b) : a < 4 := by
  by_contra hna
  have ha4 : 4 ≤ a := by omega
  -- `16 ∣ 2 ^ a`, so `3 ^ b = 2 ^ a + 1 ≡ 1 [MOD 16]`.
  obtain ⟨c, hc⟩ : (2 : ℕ) ^ 4 ∣ 2 ^ a := pow_dvd_pow 2 ha4
  have h16 : 3 ^ b % 16 = 1 := by
    have e : 3 ^ b = 16 * c + 1 := by
      rw [← h, hc]; norm_num
    omega
  -- Hence `4 ∣ b`, which forces `3 ^ b ≡ 1 [MOD 5]`.
  have hb4 : b % 4 = 0 := mod4_eq_zero_of_three_pow_mod16 h16
  have h5 : 3 ^ b % 5 = 1 := by
    have h3 := three_pow_mod5 b
    rw [hb4] at h3
    norm_num at h3
    exact h3
  -- But then `2 ^ a ≡ 0 [MOD 5]`, contradicting `two_pow_mod5_ne_zero`.
  rw [← h] at h5
  exact two_pow_mod5_ne_zero a (by omega)

theorem two_pow_add_one_eq_three_pow (a b : ℕ) :
    2 ^ a + 1 = 3 ^ b ↔ (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 2) := by
  constructor
  · intro h
    have ha : a < 4 := a_lt_four h
    have hb : b < 3 := by
      by_contra hnb
      have hb3 : 3 ≤ b := by omega
      have h1 : (3 : ℕ) ^ 3 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb3
      have h2 : (2 : ℕ) ^ a ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h1 h2
      omega
    interval_cases a <;> interval_cases b <;> revert h <;> decide
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
