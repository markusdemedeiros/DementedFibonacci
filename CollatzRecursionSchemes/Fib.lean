module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Data.Int.Fib.Lemmas
public import Mathlib.Data.Int.Sqrt
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.style.header false

@[expose] public section

-- #check Real.goldenRatio                            -- φ
-- #check Real.goldenConj                             -- ψ
-- #check Real.goldenRatio_mul_goldenConj             -- φψ = -1
-- #check Nat.fib_two_mul                             -- F(2n) = F(n) (2 F(n+1) - F(n))
-- #check Real.goldenRatio_mul_fib_succ_add_fib       -- φ F(n+1) + F(n) = φ^(n+1)
-- #check Nat.fib_add                                 -- F(m+n+1) = F(m)F(n) + F(m+1) F(n+1)
-- #check Real.coe_fib_eq                             -- F(n) = (φ^n - ψ^n) / √5
-- #check Real.fib_succ_sub_goldenRatio_mul_fib       -- F(n+1) - φ F(n) = φ^n

namespace Int

-- TODO: negOnePow -> (-1) ^ n.natAbs (it's cleaner)

/-- [fib_add] but with the roles of the arguments reversed. -/
theorem fib_add' (m n : ℤ) : fib (m + n) = fib (n - 1) * fib m + fib n * fib (m + 1) := by
  rw [add_comm, fib_add]

theorem fib_add_sub_one (m n : ℤ) :
    fib (m + n - 1) = fib n * fib m + fib (n - 1) * fib (m - 1) := by
  suffices fib (m + (n - 1)) = fib n * fib m + fib (n - 1) * fib (m - 1) by grind
  rw [fib_add m (n - 1)]
  grind

theorem fib_add_add_one (m n : ℤ) :
    fib (m + n + 1) = fib (n + 1) * fib (m + 1) + fib n * fib m := by
  suffices fib ((m + 1) + (n + 1) - 1) = fib (n + 1) * fib (m + 1) + fib n * fib m by grind
  rw [fib_add_sub_one (m + 1) (n + 1)]
  grind

theorem negOnePow_two_mul_sub_one (n : ℤ) : (2 * n - 1).negOnePow = -1 :=
  negOnePow_odd _ (odd_sub_one.mpr (even_two_mul n))

theorem fib_neg_negOnePow (n : ℤ) : fib (- n) = negOnePow (n + 1) * fib n := by
  rw [fib_neg]
  by_cases H : Even n <;> simp only [H, ↓reduceIte]
  · suffices negOnePow (n + 1) = -1 by simp [this]
    refine negOnePow_odd (n + 1) H.add_one
  · suffices negOnePow (n + 1) = 1 by simp [this]
    refine negOnePow_even (n + 1) (even_add_one.mpr H)

-- Vajda's Identity (Formulation 1)
-- https://proofwiki.org/wiki/Vajda%27s_Identity/Formulation_1
theorem vajda (n i j : ℤ) :
    fib (n + i) * fib (n + j) - fib n * fib (n + i + j) = n.negOnePow * fib i * fib j := calc
  _ = (fib n * fib (i - 1) + fib (n + 1) * fib i) * fib (n + j) - fib n * fib (n + i + j) := by
    rw [fib_add']; grind
  _ = (fib n * fib (i - 1) + fib (n + 1) * fib i) * fib (n + j) - fib n * fib (i + (n + j)) := by
    grind
  _ = (fib n * fib (i - 1) + fib (n + 1) * fib i) * fib (n + j)
        - fib n * (fib (i - 1) * fib (n + j) + fib i * fib (n + j + 1)) := by rw [fib_add i]
  _ = fib i * (fib (n + 1) * fib (n + j) - fib n * fib (n + j + 1) ) := by grind
  _ = fib i * negOnePow (2 * n - 1) * (fib n * fib (n + j + 1) - fib (n + 1) * fib (n + j)) := by
    simp [negOnePow_two_mul_sub_one ↑n]; grind
  _ = fib i * (negOnePow (n - j - 1) * negOnePow (n + j)) *
        (fib n * fib (n + j + 1) - fib (n + 1) * fib (n + j)) := by
    simp [show 2 * n - 1 = (n - j - 1) + (n + j) by grind, negOnePow_add]
  _ = fib i * negOnePow (n - j - 1) *
        (negOnePow (n + j) * fib n * fib (n + j + 1)
          - negOnePow (n + j) * fib (n + 1) * fib (n + j)) := by grind
  _ = fib i * negOnePow (n - j - 1) *
        (negOnePow (n + j) * fib n * fib (n + j + 1)
          + negOnePow (n + j + 1) * fib (n + 1) * fib (n + j)) := by
    conv => enter [1, 2]; rw [Int.sub_eq_add_neg]
    simp [negOnePow_succ]
  _ = fib i * negOnePow (n - j - 1) * fib ((n + 1) - (n + j + 1)) := by
    congr 1
    rw [show(↑n + 1 - (↑n + j + 1)) = (↑n + 1 + - (↑n + j + 1)) by rfl]
    conv => enter [2]; rw [fib_add]
    congr 1
    · rw [fib_neg_negOnePow]
      suffices negOnePow (n + j) = negOnePow (n + j + 1 + 1) by grind
      exact (negOnePow_eq_iff (↑n + j) (↑n + j + 1 + 1)).mpr (by grind)
    · rw [show -(↑n + j + 1) + 1 = -(↑n + j) by grind, fib_neg_negOnePow]
      grind
  _ = fib i * negOnePow (n - j - 1) * fib (-j) := by grind
  _ = fib i * negOnePow (n - j - 1) * negOnePow (j + 1) * fib j := by rw [fib_neg_negOnePow]; grind
  _ = (negOnePow (n - j - 1) * negOnePow (j + 1)) * fib i * fib j := by grind
  _ = (negOnePow n) * fib i * fib j := by
    conv => enter [2]; rw [show n = (n - j - 1) + (j + 1) by grind, negOnePow_add]
    simp

-- d'Ocagne's Identity a la https://proofwiki.org/wiki/D%27Ocagne%27s_Identity
-- Can this follow from [fib_add] instead of [vajda]?
theorem docagne (m n : ℤ) :
    negOnePow n * fib (m - n) = fib m * fib (n + 1) - fib n * fib (m + 1) := by
  suffices
      negOnePow n * fib (m - n) = fib (n + (m - n)) * fib (n + 1) - fib n * fib (n + (m - n) + 1) by
    grind
  rw [vajda n (m - n) 1, fib_one, Int.mul_one]

theorem fib_two_mul_rec (n : ℤ) : fib (2 * n) = fib n * (fib (n - 1) + fib (n + 1)) := by
  rw [Int.two_mul, fib_add]; grind

theorem fib_two_mul_sub_square (n : ℤ) : fib (2 * n) = fib (n + 1) ^ 2 - fib (n - 1) ^ 2 := by
  rw [sq_sub_sq, fib_two_mul_rec, mul_comm _ (_ - _)]
  congr 1
  · suffices fib n = fib (n - 1 + 2) - fib (n - 1) by grind
    rw [← sub_add_cancel n 1, fib_add_one (n - 1)]
    grind
  · grind

theorem fib_two_mul_minus_one (n : ℤ) : fib (2 * n - 1) = fib n ^ 2 + fib (n - 1) ^ 2 := by
  rw [show 2 * n - 1 = 2 * (n - 1) + 1 by grind, fib_two_mul_add_one]; simp

/- Triplication -/
theorem fib_three_mul (n : ℤ) :
    fib (3 * n) = 5 * fib n ^ 3 + 3 * (-1) ^ n.natAbs * fib n := by
  have fib_sub : fib (n - 1) = fib (n + 1) - fib n := by grind [fib_add_one]
  rw [show 3 * n = 2 * n + n by grind, fib_add, fib_two_mul_minus_one, fib_sub, fib_two_mul]
  suffices fib (n + 1) * (fib (n + 1) - fib n) - fib n ^ 2 = (-1) ^ n.natAbs by
    ring_nf at this ⊢; grind
  rw [← fib_sub, fib_succ_mul_fib_pred_sub_fib_sq]

end Int

namespace Real

theorem goldenRatio_fib_add_one (n : ℕ) :
    Nat.fib n = goldenRatio ^ (n + 1) - goldenRatio * Nat.fib (n + 1) := by
  grind [goldenRatio_mul_fib_succ_add_fib]

theorem goldenRatio_zpow_add_one_sub_zpow (k : ℤ) :
    goldenRatio ^ k + (1 - goldenRatio) ^ k = 2 * Int.fib (k + 1) - Int.fib k := by
  rw [one_sub_goldenConj, coe_intFib_eq, coe_intFib_eq,
    zpow_add_one₀ goldenRatio_ne_zero, zpow_add_one₀ goldenConj_ne_zero]
  have h5 : √5 ≠ 0 := by positivity
  have hφ : 2 * goldenRatio = 1 + √5 := by rw [goldenRatio]; ring
  have hψ : 2 * goldenConj = 1 - √5 := by rw [goldenConj]; ring
  field_simp
  linear_combination (goldenRatio ^ k) * hφ - (goldenConj ^ k) * hψ

end Real
