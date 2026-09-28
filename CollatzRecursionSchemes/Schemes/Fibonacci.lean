module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzRecursionSchemes.Fib
public import CollatzRecursionSchemes.Scheme

set_option linter.style.header false

@[expose] public section

namespace Real

noncomputable def cbrt (x : ℝ) : ℝ := if 0 ≤ x then x ^ (1 / 3 : ℝ) else -(-x) ^ (1 / 3 : ℝ)

theorem cbrt_of_nonneg {x : ℝ} (hx : 0 ≤ x) : cbrt x = x ^ (1 / 3 : ℝ) := if_pos hx

theorem cbrt_pow_three (x : ℝ) : cbrt x ^ 3 = x := by
  have h3 : (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  unfold cbrt
  split_ifs with hx
  · rw [h3, rpow_inv_natCast_pow hx (by norm_num)]
  · rw [neg_pow, h3, rpow_inv_natCast_pow (by linarith) (by norm_num)]
    ring

theorem le_cbrt_iff {a x : ℝ} : a ≤ cbrt x ↔ a ^ 3 ≤ x := by
  conv_rhs => rw [← cbrt_pow_three x]
  exact (Odd.strictMono_pow ⟨1, rfl⟩).le_iff_le.symm

theorem cbrt_le_iff {a x : ℝ} : cbrt x ≤ a ↔ x ≤ a ^ 3 := by
  conv_rhs => rw [← cbrt_pow_three x]
  exact (Odd.strictMono_pow ⟨1, rfl⟩).le_iff_le.symm

noncomputable def fibRecEven (vrec : ℝ) (n : ℕ) : ℝ :=
  (goldenRatio ^ (n / 2) + (1 - goldenRatio) ^ (n / 2)) * vrec

noncomputable def fibRecOdd (vrec : ℝ) (n : ℕ) : ℝ :=
  let G : ℝ := goldenRatio ^ (3 * n + 1) - goldenRatio * vrec
  cbrt (G / 10 + √(25 * G ^ 2 - 20) / 50) + cbrt (G / 10 - √(25 * G ^ 2 - 20) / 50)

theorem fibRecEven_fib (n : ℕ) (he : n % 2 = 0) (v : ℝ) (hv : v = Nat.fib (n / 2)) :
    fibRecEven v n = Nat.fib n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  have hk : 2 * k / 2 = k := by omega
  have hL := goldenRatio_zpow_add_one_sub_zpow k
  rw [zpow_natCast, zpow_natCast] at hL
  rw [fibRecEven, hv, hk, hL, ← Int.cast_natCast (Nat.fib k),
    ← Int.cast_natCast (Nat.fib (2 * k)), ← Int.fib_natCast, ← Int.fib_natCast, Nat.cast_mul,
    Nat.cast_ofNat, Int.fib_two_mul]
  push_cast
  ring

theorem cardano_fib (x : ℝ) (hx : 1 ≤ x) :
    let G := 5 * x ^ 3 - 3 * x
    cbrt (G / 10 + √(25 * G ^ 2 - 20) / 50) +
      cbrt (G / 10 - √(25 * G ^ 2 - 20) / 50) = x := by
  intro G
  set r := √(x ^ 2 - 4 / 5)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = x ^ 2 - 4 / 5 := Real.sq_sqrt (by nlinarith)
  have hrx : r ≤ x := by nlinarith
  have hs : √(25 * G ^ 2 - 20) = 25 * r * (4 * x ^ 2 - 4 / 5) / 4 := by
    rw [show 25 * G ^ 2 - 20 = (25 * r * (4 * x ^ 2 - 4 / 5) / 4) ^ 2 by
      simp only [G]; linear_combination (-(625 / 16) * (4 * x ^ 2 - 4 / 5) ^ 2) * hr2]
    exact Real.sqrt_sq (by nlinarith)
  have hu : G / 10 + √(25 * G ^ 2 - 20) / 50 = ((x + r) / 2) ^ 3 := by
    rw [hs]; simp only [G]; linear_combination (-(3 * x + r) / 8) * hr2
  have hv : G / 10 - √(25 * G ^ 2 - 20) / 50 = ((x - r) / 2) ^ 3 := by
    rw [hs]; simp only [G]; linear_combination (-(3 * x - r) / 8) * hr2
  have h3 : (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  rw [hu, hv, cbrt_of_nonneg (pow_nonneg (by linarith) 3),
    cbrt_of_nonneg (pow_nonneg (by linarith) 3), h3,
    Real.pow_rpow_inv_natCast (by linarith) (by norm_num),
    Real.pow_rpow_inv_natCast (by linarith) (by norm_num)]
  ring

theorem fibRecOdd_fib (n : ℕ) (hn : 0 < n) (ho : n % 2 = 1) (v : ℝ)
    (hv : v = Nat.fib (3 * n + 1)) : fibRecOdd v n = Nat.fib n := by
  have hG : goldenRatio ^ (3 * n + 1) - goldenRatio * v =
      5 * (Nat.fib n : ℝ) ^ 3 - 3 * Nat.fib n := by
    rw [hv, ← goldenRatio_fib_add_one, ← Int.cast_natCast (Nat.fib n),
      ← Int.cast_natCast (Nat.fib (3 * n)), ← Int.fib_natCast, ← Int.fib_natCast, Nat.cast_mul,
      Nat.cast_ofNat, Int.fib_three_mul]
    have : (-1 : ℤ) ^ (n : ℤ).natAbs = -1 := by
      rw [Int.natAbs_natCast]; exact Odd.neg_one_pow (Nat.odd_iff.mpr ho)
    rw [this]
    push_cast
    ring
  have hx : (1 : ℝ) ≤ Nat.fib n := by exact_mod_cast Nat.fib_pos.mpr hn
  rw [fibRecOdd]
  simp only [hG]
  exact cardano_fib _ hx

noncomputable def fibScheme : CollatzRecursionScheme ℝ where
  one := 1
  odd n vrec := fibRecOdd vrec n
  even n vrec := fibRecEven vrec n

theorem fibScheme_valid : fibScheme.Valid (fun n => (Nat.fib n : ℝ)) where
  ok_one := by simp [fibScheme]
  ok_even z vr hne he hv := by
    have hz1 : (z : ℕ) ≠ 1 := by simpa using hne
    have h2 : 0 < (z : ℕ) / 2 := by have := z.pos; omega
    exact fibRecEven_fib z he vr (by rw [← hv, PNat.toPNat'_coe h2])
  ok_odd z vr hne ho hv := by
    exact fibRecOdd_fib z z.pos (by omega) vr (by rw [← hv]; push_cast; rfl)

end Real
