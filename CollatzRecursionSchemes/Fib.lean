module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Data.Int.Fib.Lemmas
public import Mathlib.Data.Int.Sqrt
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzRecursionSchemes.Scheme
public import CollatzRecursionSchemes.BigStep

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

def fibEven : Exp :=
  -- Index helpers
  let toNum m := m + 2
  let toArg m := m - 2
  let div2 := (· / 2) ∘ toNum
  let pow := Int.toNat ∘ div2
  -- The program
  exp% (φ ^ pow + (1 - φ) ^ pow) * rec (toArg ∘ div2)

def fibOdd : Exp :=
  -- Index helpers
  let toNum m := m + 2
  let toArg m := m - 2
  let trp1 := (· * 3 + 1) ∘ toNum
  let pow := Int.toNat ∘ trp1
  let two (_ : ℤ) := 2
  -- The program
  let G := exp% φ ^ pow - φ * rec (toArg ∘ trp1)
  let D := exp% √(25 * G ^ two - 20) / 50
  exp% ∛(G / 10 + D) + ∛(G / 10 - D)

def fibProg : Exp := exp%
  js (jpe 0 1) (jpe fibEven fibOdd)

noncomputable def fibRun (n : ℕ) : Option ℝ := run fibProg (n - 2)

theorem fibRun_zero : fibRun 0 = some 0 := by
  simp only [fibRun, run]
  change (denote fibProg (.Bpos (.Beven fibEven fibOdd) (.Beven (.OfRat 0) (.OfRat 1))) _ :
    Option ℝ) = _
  simp (disch := decide) only [denote_bpos_of_neg, denote_beven_of_even, denote_ofRat,
    Denotable.ofRat_real, Rat.cast_zero]

theorem fibRun_one : fibRun 1 = some 1 := by
  simp only [fibRun, run]
  change (denote fibProg (.Bpos (.Beven fibEven fibOdd) (.Beven (.OfRat 0) (.OfRat 1))) _ :
    Option ℝ) = _
  simp (disch := decide) only [denote_bpos_of_neg, denote_beven_of_odd, denote_ofRat,
    Denotable.ofRat_real, Rat.cast_one]

theorem fibRun_even (n : ℕ) (hn : 0 < n) (he : n % 2 = 0) :
    fibRun n = (fibRun (n / 2)).map (Real.fibRecEven · n) := by
  simp only [fibRun, run]
  change (denote fibProg (.Bpos (.Beven fibEven fibOdd) (.Beven (.OfRat 0) (.OfRat 1))) _ :
    Option ℝ) = _
  have e : ((n : ℤ) - 2 + 2) / 2 = ((n / 2 : ℕ) : ℤ) := by omega
  simp (disch := omega) only [denote_bpos_of_nonneg, denote_beven_of_even, fibEven, denote_mul,
    denote_add, denote_toThePowerOf, denote_φ, denote_ofRat, denote_neg, denote_recurse,
    Option.bind_some, Function.comp_apply, e, Int.toNat_natCast]
  cases (denote fibProg fibProg (((n / 2 : ℕ) : ℤ) - 2) : Option ℝ) <;>
    simp only [Option.bind_some, Option.bind_none, Option.map_some, Option.map_none,
      Real.fibRecEven, Denotable.ofRat_real, Denotable.φ_real, Rat.cast_one, sub_eq_add_neg]

theorem fibRun_odd (n : ℕ) (hn : 1 < n) (ho : n % 2 = 1) :
    fibRun n = (fibRun (3 * n + 1)).map (Real.fibRecOdd · n) := by
  simp only [fibRun, run]
  change (denote fibProg (.Bpos (.Beven fibEven fibOdd) (.Beven (.OfRat 0) (.OfRat 1))) _ :
    Option ℝ) = _
  have e : ((n : ℤ) - 2 + 2) * 3 + 1 = ((3 * n + 1 : ℕ) : ℤ) := by push_cast; ring
  rcases hrec : (denote fibProg fibProg (((3 * n + 1 : ℕ) : ℤ) - 2) : Option ℝ) with _ | v <;>
    simp (disch := omega) only [denote_bpos_of_nonneg, denote_beven_of_odd, fibOdd, denote_mul,
      denote_add, denote_toThePowerOf, denote_φ, denote_neg, denote_recurse,
      denote_sqrt, denote_cubert, denote_ofRat, Option.bind_some, Option.bind_none,
      Option.map_some, Option.map_none, Function.comp_apply, e, Int.toNat_natCast, hrec]
  simp [Real.fibRecOdd, div_eq_mul_inv, sub_eq_add_neg]

macro "step_base" : tactic => `(tactic| first | rw [fibRun_zero] | rw [fibRun_one])

macro "step_even" : tactic => `(tactic| (
  rw [fibRun_even] <;> try decide
  try simp only [Nat.reduceDiv]))

macro "step_odd" : tactic => `(tactic| (
  rw [fibRun_odd] <;> try decide
  try simp only [Nat.reduceMul, Nat.reduceAdd]))

macro "fib_value" : tactic => `(tactic| (
  simp (disch := norm_num [Nat.fib_add_two]) only [Option.map_some, Real.fibRecEven_fib,
    Real.fibRecOdd_fib]
  norm_num [Nat.fib_add_two]))

example : fibRun 0 = some 0 := by
  step_base
example : fibRun 1 = some 1 := by
  step_base
example : fibRun 2 = some 1 := by
  step_even
  step_base; fib_value
example : fibRun 3 = some 2 := by
  step_odd
  step_even
  step_odd
  step_even
  step_even
  step_even
  step_even
  step_base; fib_value
example : fibRun 4 = some 3 := by
  step_even
  step_even
  step_base; fib_value
example : fibRun 5 = some 5 := by
  step_odd
  step_even
  step_even
  step_even
  step_even
  step_base; fib_value
example : fibRun 6 = some 8 := by
  step_even
  step_odd
  step_even
  step_odd
  step_even
  step_even
  step_even
  step_even
  step_base; fib_value

def calls : Exp → ℤ → List ℤ
  | .Add e₁ e₂, n => calls e₁ n ++ calls e₂ n
  | .Neg e, n => calls e n
  | .Mul e₁ e₂, n => calls e₁ n ++ calls e₂ n
  | .OfRat _, _ => []
  | .ToThePowerOf e _, n => calls e n
  | .Sqrt e, n => calls e n
  | .Cubert e, n => calls e n
  | .Bpos enn eneg, n => if 0 ≤ n then calls enn n else calls eneg n
  | .Beven eeven eodd, n => if n % 2 = 0 then calls eeven n else calls eodd n
  | .φ, _ => []
  | .Recurse f, n => [f n]

def HaltsAt (m : ℤ) : Prop := ∃ fuel, CollatzN fuel (m + 2).toNat = some 1

theorem haltsAt_of_neg {m : ℤ} (hm : m < 0) : HaltsAt m := by
  exists 1
  by_cases hm : m = -1
  · simp [hm, CollatzN]
  · simp [show (m + 2).toNat = 0 by grind, CollatzN, collatz]

theorem haltsAt_of_calls {m : ℤ} (h : ∀ k ∈ calls fibProg m, HaltsAt k) : HaltsAt m := by
  by_cases hm : m < 0
  · exact haltsAt_of_neg hm
  simp only [fibProg, fibEven, fibOdd, calls, not_lt.mp hm, ↓reduceIte, Function.comp_apply,
    List.append_nil, List.nil_append, List.cons_append] at h
  split at h
  · obtain ⟨k, H⟩ := h _ List.mem_cons_self
    exact ⟨k + 1, by unfold CollatzN; grind [collatz]⟩
  · obtain ⟨k, H⟩ := h _ List.mem_cons_self
    exact ⟨k + 1, by unfold CollatzN; grind [collatz]⟩

theorem calls_haltsAt_of_denote_eq_some {e : Exp} {m : ℤ} {v : ℝ}
    (h : denote fibProg e m = some v) : ∀ k ∈ calls e m, HaltsAt k := by
  revert e m v h
  apply denote.partial_correctness
  intro denote IH e n r h k hk
  cases e with
  | Add e₁ e₂ | Mul e₁ e₂ =>
    cases h₁ : denote e₁ n
    · grind
    · cases h₂ : denote e₂ n
      · grind
      · grind [calls]
  | Neg e | ToThePowerOf e _ | Sqrt e | Cubert e =>
    cases h₁ : denote e n
    · grind
    · grind [calls]
  | OfRat _ | φ => grind [calls]
  | Bpos e₁ e₂ | Beven e₁ e₂ => grind [calls]
  | Recurse arg => grind [calls, haltsAt_of_calls]

theorem halts_of_fibRun_eq_some {n : ℕ+} {v : ℝ} (h : fibRun n = some v) : Halts n := by
  obtain ⟨fuel, hf⟩ := haltsAt_of_calls (calls_haltsAt_of_denote_eq_some h)
  exact Halts_of_collatzN fuel n (by simpa using hf)

theorem fibRun_eq_toFun_of_halts {n : ℕ+} (h : Halts n) :
    fibRun n = Real.fibScheme.toFun n := by
  induction h with
  | one => exact fibRun_one.trans Real.fibScheme.toFun_one.symm
  | @even n hne hev _ ih =>
    rw [fibRun_even n n.pos hev, Real.fibScheme.toFun_even hne hev, ← ih,
      PNat.toPNat'_coe (by grind [n.pos])]
    rfl
  | @odd n hne hodd _ ih =>
    have := PNat.coe_eq_one_iff.not.mpr hne
    rw [fibRun_odd n (by grind [n.pos]) (by grind), Real.fibScheme.toFun_odd hne hodd, ← ih]
    simp only [PNat.add_coe, PNat.mul_coe, PNat.val_ofNat]
    rfl

theorem fibRun_eq_none_of_not_halts {n : ℕ+} (h : ¬Halts n) : fibRun n = none :=
  Option.eq_none_iff_forall_ne_some.mpr fun _ hv => h (halts_of_fibRun_eq_some hv)

theorem toFun_eq_none_of_not_halts {α : Type*} (s : CollatzRecursionScheme α) {n : ℕ+}
    (h : ¬Halts n) : s.toFun n = none :=
  Option.eq_none_iff_forall_ne_some.mpr fun v hv => h (s.halts_of_eq_some n v hv)

theorem fibRun_eq_toFun (n : ℕ+) : fibRun n = Real.fibScheme.toFun n := by
  by_cases h : Halts n
  · exact fibRun_eq_toFun_of_halts h
  · rw [fibRun_eq_none_of_not_halts h, toFun_eq_none_of_not_halts _ h]

theorem fibRun_eq_fib_iff_collatz :
    fibRun = (fun n => some (Nat.fib n : ℝ)) ↔ CollatzConjecture := by
  rw [← Real.fibScheme.toFun_eq_spec_iff_collatz Real.fibScheme_valid]
  constructor
  · exact fun h => funext fun n => (fibRun_eq_toFun n).symm.trans (congrFun h n)
  · refine fun h => funext fun n => ?_
    rcases n with _ | n
    · simp [fibRun_zero]
    · exact (fibRun_eq_toFun n.succPNat).trans (congrFun h _)
