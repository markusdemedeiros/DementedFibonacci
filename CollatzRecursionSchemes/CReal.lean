module

public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.Data.Nat.Size
public import CollatzRecursionSchemes.BigStep

set_option linter.style.header false

@[expose] public section

structure CReal where
  approx : ℕ → ℚ

namespace CReal

def Tracks (a : CReal) (x : ℝ) : Prop := ∀ k, |(a.approx k : ℝ) - x| ≤ ((2 : ℝ) ^ k)⁻¹

def ofRat (q : ℚ) : CReal := ⟨fun _ => q⟩

def neg (a : CReal) : CReal := ⟨fun k => -a.approx k⟩

def add (a b : CReal) : CReal := ⟨fun k => a.approx (k + 1) + b.approx (k + 1)⟩

def bound (a : CReal) : ℕ := ⌈|a.approx 0|⌉₊ + 1

def mul (a b : CReal) : CReal :=
  let s := (a.bound + b.bound).size
  ⟨fun k => a.approx (k + s) * b.approx (k + s)⟩

def pow (a : CReal) (m : ℕ) : CReal :=
  let s := (m * (a.bound + 1) ^ (m - 1)).size
  ⟨fun k => a.approx (k + s) ^ m⟩

def sqrtApprox (q : ℚ) (m : ℕ) : ℚ := (Nat.sqrt ⌊q * (2 ^ m) ^ 2⌋₊ : ℚ) / 2 ^ m

def sqrt (a : CReal) : CReal := ⟨fun k => sqrtApprox (a.approx (2 * k + 2)) (k + 1)⟩

def icbrt (z : ℤ) : ℤ :=
  if 0 ≤ z then Nat.nthRoot 3 z.toNat else -((Nat.nthRoot 3 (-z - 1).toNat : ℤ) + 1)

def cbrtApprox (q : ℚ) (m : ℕ) : ℚ := (icbrt ⌊q * (2 ^ m) ^ 3⌋ : ℚ) / 2 ^ m

def cbrt (a : CReal) : CReal := ⟨fun k => cbrtApprox (a.approx (3 * k + 5)) (k + 1)⟩

def φ : CReal := mul (ofRat (1 / 2)) (add (ofRat 1) (sqrt (ofRat 5)))

instance : Denotable CReal where
  add := add
  neg := neg
  mul := mul
  pow := pow
  ofRat := ofRat
  sqrt := sqrt
  cbrt := cbrt
  φ := φ

theorem Tracks.abs_le_bound {a : CReal} {x : ℝ} (h : a.Tracks x) : |x| ≤ a.bound := by
  have h0 := h 0
  rw [pow_zero, inv_one] at h0
  have hc : |(a.approx 0 : ℝ)| ≤ ⌈|a.approx 0|⌉₊ := by exact_mod_cast Nat.le_ceil _
  have := abs_sub_abs_le_abs_sub x (a.approx 0 : ℝ)
  rw [abs_sub_comm] at this
  simp only [bound, Nat.cast_add, Nat.cast_one]
  linarith

theorem Tracks.abs_approx_le {a : CReal} {x : ℝ} (h : a.Tracks x) (k : ℕ) :
    |(a.approx k : ℝ)| ≤ a.bound + 1 := by
  have hk : ((2 : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have := abs_sub_abs_le_abs_sub (a.approx k : ℝ) x
  linarith [h k, h.abs_le_bound]

theorem two_pow_add_inv (k s : ℕ) : (2 : ℝ) ^ s * ((2 : ℝ) ^ (k + s))⁻¹ = ((2 : ℝ) ^ k)⁻¹ := by
  rw [pow_add]
  field_simp

theorem tracks_ofRat (q : ℚ) : (ofRat q).Tracks q := by
  intro k
  simp only [ofRat, sub_self, abs_zero]
  positivity

theorem Tracks.neg {a : CReal} {x : ℝ} (h : a.Tracks x) : a.neg.Tracks (-x) := by
  intro k
  simp only [CReal.neg, Rat.cast_neg]
  rw [show -(a.approx k : ℝ) - -x = -((a.approx k : ℝ) - x) by ring, abs_neg]
  exact h k

theorem Tracks.add {a b : CReal} {x y : ℝ} (ha : a.Tracks x) (hb : b.Tracks y) :
    (a.add b).Tracks (x + y) := by
  intro k
  simp only [CReal.add, Rat.cast_add]
  calc |(a.approx (k + 1) : ℝ) + b.approx (k + 1) - (x + y)|
      = |((a.approx (k + 1) : ℝ) - x) + ((b.approx (k + 1) : ℝ) - y)| := by ring_nf
    _ ≤ |(a.approx (k + 1) : ℝ) - x| + |(b.approx (k + 1) : ℝ) - y| := abs_add_le _ _
    _ ≤ ((2 : ℝ) ^ (k + 1))⁻¹ + ((2 : ℝ) ^ (k + 1))⁻¹ := add_le_add (ha _) (hb _)
    _ = ((2 : ℝ) ^ k)⁻¹ := by rw [pow_succ]; ring

theorem Tracks.mul {a b : CReal} {x y : ℝ} (ha : a.Tracks x) (hb : b.Tracks y) :
    (a.mul b).Tracks (x * y) := by
  intro k
  simp only [CReal.mul, Rat.cast_mul]
  set s := (a.bound + b.bound).size
  have hs : ((a.bound + b.bound : ℕ) : ℝ) + 1 ≤ 2 ^ s := by
    exact_mod_cast Nat.lt_size_self _
  set p := ((2 : ℝ) ^ (k + s))⁻¹
  set u : ℝ := ((a.approx (k + s) : ℚ) : ℝ)
  set v : ℝ := ((b.approx (k + s) : ℚ) : ℝ)
  have hu := ha.abs_approx_le (k + s)
  have hy := hb.abs_le_bound
  calc |u * v - x * y| = |u * (v - y) + y * (u - x)| := by ring_nf
    _ ≤ |u| * |v - y| + |y| * |u - x| := by
      rw [← abs_mul, ← abs_mul]
      exact abs_add_le _ _
    _ ≤ (a.bound + 1) * p + b.bound * p := by
      gcongr
      · exact hb _
      · exact ha _
    _ = (((a.bound + b.bound : ℕ) : ℝ) + 1) * p := by push_cast; ring
    _ ≤ 2 ^ s * p := by gcongr
    _ = ((2 : ℝ) ^ k)⁻¹ := two_pow_add_inv k s

theorem Tracks.pow {a : CReal} {x : ℝ} (ha : a.Tracks x) (m : ℕ) : (a.pow m).Tracks (x ^ m) := by
  intro k
  simp only [CReal.pow, Rat.cast_pow]
  set s := (m * (a.bound + 1) ^ (m - 1)).size
  have hs : ((m * (a.bound + 1) ^ (m - 1) : ℕ) : ℝ) ≤ 2 ^ s := by
    exact_mod_cast (Nat.lt_size_self _).le
  set p := ((2 : ℝ) ^ (k + s))⁻¹
  set u : ℝ := ((a.approx (k + s) : ℚ) : ℝ)
  have hmax : max |u| |x| ≤ a.bound + 1 :=
    max_le (ha.abs_approx_le _) (by linarith [ha.abs_le_bound])
  calc |u ^ m - x ^ m| ≤ |u - x| * m * max |u| |x| ^ (m - 1) := abs_pow_sub_pow_le _ _ _
    _ ≤ p * m * (a.bound + 1) ^ (m - 1) := by
      gcongr
      exact ha _
    _ = ((m * (a.bound + 1) ^ (m - 1) : ℕ) : ℝ) * p := by push_cast; ring
    _ ≤ 2 ^ s * p := by gcongr
    _ = ((2 : ℝ) ^ k)⁻¹ := two_pow_add_inv k s

theorem sqrtApprox_spec (q : ℚ) (m : ℕ) :
    0 ≤ sqrtApprox q m ∧ q < (sqrtApprox q m + (2 ^ m)⁻¹) ^ 2 ∧
      (sqrtApprox q m = 0 ∨ sqrtApprox q m ^ 2 ≤ q) := by
  set N := ⌊q * (2 ^ m) ^ 2⌋₊
  have h2 : (0 : ℚ) < 2 ^ m := by positivity
  have hr : sqrtApprox q m = (N.sqrt : ℚ) / 2 ^ m := rfl
  refine ⟨by rw [hr]; positivity, ?_, ?_⟩
  · have h1 : q * (2 ^ m) ^ 2 < N + 1 := Nat.lt_floor_add_one _
    have h3 : ((N + 1 : ℕ) : ℚ) ≤ ((N.sqrt + 1 : ℕ) : ℚ) ^ 2 := by
      exact_mod_cast Nat.lt_succ_sqrt' N
    rw [hr, show (N.sqrt : ℚ) / 2 ^ m + (2 ^ m)⁻¹ = (N.sqrt + 1) / 2 ^ m by field_simp, div_pow,
      lt_div_iff₀ (by positivity)]
    push_cast at h3
    linarith
  · by_cases hq : 0 ≤ q
    · right
      have h1 : (N : ℚ) ≤ q * (2 ^ m) ^ 2 := Nat.floor_le (by positivity)
      have h3 : ((N.sqrt : ℕ) : ℚ) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
      rw [hr, div_pow, div_le_iff₀ (by positivity)]
      linarith
    · left
      have hN : N = 0 := Nat.floor_of_nonpos (by nlinarith)
      rw [hr, hN]
      simp

theorem Tracks.sqrt {a : CReal} {x : ℝ} (ha : a.Tracks x) : a.sqrt.Tracks √x := by
  intro k
  simp only [CReal.sqrt]
  obtain ⟨h0, hlt, hor⟩ := sqrtApprox_spec (a.approx (2 * k + 2)) (k + 1)
  have hq := ha (2 * k + 2)
  have hlt' := (Rat.cast_lt (K := ℝ)).mpr hlt
  push_cast at hlt'
  rw [show ((2 : ℝ) ^ (2 * k + 2))⁻¹ = (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2 by ring] at hq
  set r := sqrtApprox (a.approx (2 * k + 2)) (k + 1)
  set q := a.approx (2 * k + 2)
  set h : ℝ := ((2 : ℝ) ^ (k + 1))⁻¹
  have hh : 0 < h := by positivity
  have hk : ((2 : ℝ) ^ k)⁻¹ = 2 * h := by simp only [h, pow_succ]; field_simp
  have h0' : (0 : ℝ) ≤ r := by exact_mod_cast h0
  rw [abs_sub_le_iff] at hq ⊢
  rw [hk]
  constructor
  · rcases hor with hr | hr
    · rw [hr]
      push_cast
      linarith [Real.sqrt_nonneg x]
    · have hr' : (r : ℝ) ^ 2 ≤ q := by exact_mod_cast hr
      by_cases hr2 : (r : ℝ) ≤ 2 * h
      · linarith [Real.sqrt_nonneg x]
      · have : (r : ℝ) - 2 * h ≤ √x := (Real.le_sqrt' (by linarith)).mpr <| by
          nlinarith [mul_pos hh (sub_pos.mpr (not_le.mp hr2))]
        linarith
  · have : √x ≤ r + 2 * h := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    linarith

theorem icbrt_spec (z : ℤ) : icbrt z ^ 3 ≤ z ∧ z < (icbrt z + 1) ^ 3 := by
  unfold icbrt
  split_ifs with hz
  · have h1 : Nat.nthRoot 3 z.toNat ^ 3 ≤ z.toNat := Nat.pow_nthRoot_le (.inl (by norm_num))
    have h2 : z.toNat < (Nat.nthRoot 3 z.toNat + 1) ^ 3 :=
      Nat.lt_pow_nthRoot_add_one (by norm_num) _
    have hz' : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
    constructor
    · rw [← hz']; exact_mod_cast h1
    · rw [← hz']; exact_mod_cast h2
  · set M := (-z - 1).toNat
    have hM : (M : ℤ) = -z - 1 := Int.toNat_of_nonneg (by omega)
    have h1 : ((Nat.nthRoot 3 M ^ 3 : ℕ) : ℤ) ≤ M := by
      exact_mod_cast Nat.pow_nthRoot_le (.inl (by norm_num))
    have h2 : (M : ℤ) < ((Nat.nthRoot 3 M + 1) ^ 3 : ℕ) := by
      exact_mod_cast Nat.lt_pow_nthRoot_add_one (by norm_num) _
    push_cast at h1 h2
    constructor
    · nlinarith
    · nlinarith

theorem cbrtApprox_spec (q : ℚ) (m : ℕ) :
    cbrtApprox q m ^ 3 ≤ q ∧ q < (cbrtApprox q m + (2 ^ m)⁻¹) ^ 3 := by
  set z := ⌊q * (2 ^ m) ^ 3⌋
  obtain ⟨h1, h2⟩ := icbrt_spec z
  have h3 : (z : ℚ) ≤ q * (2 ^ m) ^ 3 := Int.floor_le _
  have h4 : q * (2 ^ m) ^ 3 < z + 1 := Int.lt_floor_add_one _
  have h1' : ((icbrt z : ℚ)) ^ 3 ≤ z := by exact_mod_cast h1
  have h2' : (z : ℚ) + 1 ≤ ((icbrt z : ℚ) + 1) ^ 3 := by exact_mod_cast h2
  have hr : cbrtApprox q m = (icbrt z : ℚ) / 2 ^ m := rfl
  constructor
  · rw [hr, div_pow, div_le_iff₀ (by positivity)]
    linarith
  · rw [hr, show (icbrt z : ℚ) / 2 ^ m + (2 ^ m)⁻¹ = (icbrt z + 1) / 2 ^ m by field_simp,
      div_pow, lt_div_iff₀ (by positivity)]
    linarith

theorem Tracks.cbrt {a : CReal} {x : ℝ} (ha : a.Tracks x) : a.cbrt.Tracks (Real.cbrt x) := by
  intro k
  simp only [CReal.cbrt]
  obtain ⟨hle, hlt⟩ := cbrtApprox_spec (a.approx (3 * k + 5)) (k + 1)
  have hq := ha (3 * k + 5)
  have hlt' := (Rat.cast_lt (K := ℝ)).mpr hlt
  have hle' := (Rat.cast_le (K := ℝ)).mpr hle
  push_cast at hlt' hle'
  rw [show ((2 : ℝ) ^ (3 * k + 5))⁻¹ = (((2 : ℝ) ^ (k + 1))⁻¹) ^ 3 / 4 by ring] at hq
  set r := cbrtApprox (a.approx (3 * k + 5)) (k + 1)
  set q := a.approx (3 * k + 5)
  set h : ℝ := ((2 : ℝ) ^ (k + 1))⁻¹
  have hh : 0 < h := by positivity
  have hk : ((2 : ℝ) ^ k)⁻¹ = 2 * h := by simp only [h, pow_succ]; field_simp
  rw [abs_sub_le_iff] at hq ⊢
  rw [hk]
  constructor
  · have : (r : ℝ) - 2 * h ≤ Real.cbrt x := Real.le_cbrt_iff.mpr <| by
      nlinarith [mul_nonneg hh.le (sq_nonneg ((r : ℝ) - h)), pow_pos hh 3]
    linarith
  · have : Real.cbrt x ≤ r + 2 * h := Real.cbrt_le_iff.mpr <| by
      nlinarith [mul_nonneg hh.le (sq_nonneg ((r : ℝ) + 3 * h / 2)), pow_pos hh 3]
    linarith

theorem tracks_φ : φ.Tracks Real.goldenRatio := by
  have h := (tracks_ofRat (1 / 2)).mul ((tracks_ofRat 1).add (tracks_ofRat 5).sqrt)
  have e : ((1 / 2 : ℚ) : ℝ) * (((1 : ℚ) : ℝ) + √((5 : ℚ) : ℝ)) = Real.goldenRatio := by
    rw [Real.goldenRatio]
    push_cast
    ring
  rw [e] at h
  exact h

theorem tracks_rel : Denotable.Rel Tracks where
  add := Tracks.add
  neg := Tracks.neg
  mul := Tracks.mul
  pow m h := h.pow m
  ofRat := tracks_ofRat
  sqrt := Tracks.sqrt
  cbrt := Tracks.cbrt
  φ := tracks_φ

end CReal
