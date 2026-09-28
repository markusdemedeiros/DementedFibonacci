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

def probes : List ℕ := [0, 1, 2, 4, 8, 16, 32, 64]

def sqrtSlow (a : CReal) : CReal := ⟨fun k => sqrtApprox (a.approx (2 * k + 2)) (k + 1)⟩

def sqrtFast (a : CReal) (i : ℕ) : CReal := ⟨fun k => sqrtApprox (a.approx (k + i + 1)) (k + 1)⟩

def sqrtProbe (a : CReal) : Option ℕ := probes.find? fun i => 2 / 4 ^ i ≤ a.approx (2 * i)

def sqrt (a : CReal) : CReal :=
  match a.sqrtProbe with
  | some i => a.sqrtFast i
  | none => a.sqrtSlow

def icbrt (z : ℤ) : ℤ :=
  if 0 ≤ z then Nat.nthRoot 3 z.toNat else -((Nat.nthRoot 3 (-z - 1).toNat : ℤ) + 1)

def cbrtApprox (q : ℚ) (m : ℕ) : ℚ := (icbrt ⌊q * (2 ^ m) ^ 3⌋ : ℚ) / 2 ^ m

def cbrtSlow (a : CReal) : CReal := ⟨fun k => cbrtApprox (a.approx (3 * k + 5)) (k + 1)⟩

def cbrtFast (a : CReal) (i : ℕ) : CReal :=
  ⟨fun k => cbrtApprox (a.approx (k + 2 * i + 2)) (k + 1)⟩

def cbrtProbe (a : CReal) : Option ℕ := probes.find? fun i => 2 / 8 ^ i ≤ |a.approx (3 * i)|

def cbrt (a : CReal) : CReal :=
  match a.cbrtProbe with
  | some i => a.cbrtFast i
  | none => a.cbrtSlow

def φ : CReal := mul (ofRat (1 / 2)) (add (ofRat 1) (sqrt (ofRat 5)))

def memoStep : ℕ := 16

def memoSize : ℕ := 512

def memo (a : CReal) : CReal :=
  let t : Array (Thunk ℚ) :=
    Array.ofFn (n := memoSize) fun i => Thunk.mk fun _ => a.approx (memoStep * (i + 1))
  ⟨fun k => match t[k / memoStep]? with
    | some th => th.get
    | none => a.approx k⟩

instance : Denotable CReal where
  add := add
  neg := neg
  mul := mul
  pow := pow
  ofRat := ofRat
  sqrt := sqrt
  cbrt := cbrt
  φ := φ
  memo := memo

theorem Tracks.abs_le_bound {a : CReal} {x : ℝ} (h : a.Tracks x) : |x| ≤ a.bound := by
  have h0 : |(a.approx 0 : ℝ) - x| ≤ 1 := by simpa using h 0
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

theorem inv_two_pow_succ_add (k : ℕ) :
    ((2 : ℝ) ^ (k + 1))⁻¹ + ((2 : ℝ) ^ (k + 1))⁻¹ = ((2 : ℝ) ^ k)⁻¹ := by
  rw [pow_succ]
  ring

theorem abs_sub_le_of_halves {r y z : ℝ} {k : ℕ} (h₁ : |r - y| ≤ ((2 : ℝ) ^ (k + 1))⁻¹)
    (h₂ : |y - z| ≤ ((2 : ℝ) ^ (k + 1))⁻¹) : |r - z| ≤ ((2 : ℝ) ^ k)⁻¹ := by
  rw [← inv_two_pow_succ_add]
  exact (abs_sub_le r y z).trans (add_le_add h₁ h₂)

theorem inv_two_pow_sq (i : ℕ) : (((2 : ℝ) ^ i)⁻¹) ^ 2 = ((4 : ℝ) ^ i)⁻¹ := by
  rw [inv_pow, ← pow_mul, mul_comm, pow_mul]
  norm_num

theorem inv_two_pow_cube (i : ℕ) : (((2 : ℝ) ^ i)⁻¹) ^ 3 = ((8 : ℝ) ^ i)⁻¹ := by
  rw [inv_pow, ← pow_mul, mul_comm, pow_mul]
  norm_num

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
  rw [← inv_two_pow_succ_add]
  calc |(a.approx (k + 1) : ℝ) + b.approx (k + 1) - (x + y)|
      = |((a.approx (k + 1) : ℝ) - x) + ((b.approx (k + 1) : ℝ) - y)| := by ring_nf
    _ ≤ |(a.approx (k + 1) : ℝ) - x| + |(b.approx (k + 1) : ℝ) - y| := abs_add_le _ _
    _ ≤ ((2 : ℝ) ^ (k + 1))⁻¹ + ((2 : ℝ) ^ (k + 1))⁻¹ := add_le_add (ha _) (hb _)

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
    0 ≤ sqrtApprox q m ∧ (sqrtApprox q m = 0 ∨ sqrtApprox q m ^ 2 ≤ q) ∧
      q < (sqrtApprox q m + (2 ^ m)⁻¹) ^ 2 := by
  set N := ⌊q * (2 ^ m) ^ 2⌋₊
  have hr : sqrtApprox q m = (N.sqrt : ℚ) / 2 ^ m := rfl
  refine ⟨by rw [hr]; positivity, ?_, ?_⟩
  · by_cases hq : 0 ≤ q
    · right
      rw [hr, div_pow, div_le_iff₀ (by positivity)]
      calc ((N.sqrt : ℕ) : ℚ) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
        _ ≤ q * (2 ^ m) ^ 2 := Nat.floor_le (by positivity)
    · left
      have hN : N = 0 := Nat.floor_of_nonpos (by nlinarith)
      rw [hr, hN]
      simp
  · rw [hr, show (N.sqrt : ℚ) / 2 ^ m + (2 ^ m)⁻¹ = (N.sqrt + 1) / 2 ^ m by field_simp, div_pow,
      lt_div_iff₀ (by positivity)]
    calc q * (2 ^ m) ^ 2 < N + 1 := Nat.lt_floor_add_one _
      _ ≤ ((N.sqrt + 1 : ℕ) : ℚ) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' N
      _ = ((N.sqrt : ℚ) + 1) ^ 2 := by push_cast; ring

theorem sqrtApprox_near (q : ℚ) (m : ℕ) :
    |(sqrtApprox q m : ℝ) - √(q : ℝ)| ≤ ((2 : ℝ) ^ m)⁻¹ := by
  obtain ⟨h0, hor, hlt⟩ := sqrtApprox_spec q m
  set r := sqrtApprox q m
  have h0' : (0 : ℝ) ≤ r := by exact_mod_cast h0
  have lower : (r : ℝ) ≤ √(q : ℝ) := by
    rcases hor with hr | hr
    · simp [hr]
    · have hr' := (Rat.cast_le (K := ℝ)).mpr hr
      push_cast at hr'
      calc (r : ℝ) = √((r : ℝ) ^ 2) := (Real.sqrt_sq h0').symm
        _ ≤ √(q : ℝ) := Real.sqrt_le_sqrt hr'
  have upper : √(q : ℝ) ≤ r + ((2 : ℝ) ^ m)⁻¹ := by
    have hlt' := (Rat.cast_le (K := ℝ)).mpr hlt.le
    push_cast at hlt'
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hlt'⟩
  have hh : (0 : ℝ) ≤ ((2 : ℝ) ^ m)⁻¹ := by positivity
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem abs_sqrt_sub_sqrt_mul_add (q x : ℝ) : |√q - √x| * (√q + √x) ≤ |q - x| :=
  calc |√q - √x| * (√q + √x) = |√q ^ 2 - √x ^ 2| := by
        rw [← abs_of_nonneg (by positivity : 0 ≤ √q + √x), ← abs_mul]
        ring_nf
    _ = |max q 0 - max x 0| := by rw [Real.sq_sqrt', Real.sq_sqrt']
    _ ≤ |q - x| := abs_max_sub_max_le_abs _ _ _

theorem sq_abs_sqrt_sub_sqrt_le (q x : ℝ) : |√q - √x| ^ 2 ≤ |q - x| := by
  have hq := Real.sqrt_nonneg q
  have hx := Real.sqrt_nonneg x
  calc |√q - √x| ^ 2 = |√q - √x| * |√q - √x| := sq _
    _ ≤ |√q - √x| * (√q + √x) := by
      gcongr
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    _ ≤ |q - x| := abs_sqrt_sub_sqrt_mul_add q x

theorem abs_sqrt_sub_sqrt_mul_le (q x : ℝ) : |√q - √x| * √x ≤ |q - x| :=
  calc |√q - √x| * √x ≤ |√q - √x| * (√q + √x) := by
        gcongr
        linarith [Real.sqrt_nonneg q]
    _ ≤ |q - x| := abs_sqrt_sub_sqrt_mul_add q x

theorem Tracks.sqrtSlow {a : CReal} {x : ℝ} (ha : a.Tracks x) : a.sqrtSlow.Tracks √x := by
  intro k
  apply abs_sub_le_of_halves (sqrtApprox_near (a.approx (2 * k + 2)) (k + 1))
  have hq : |(a.approx (2 * k + 2) : ℝ) - x| ≤ (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2 := by
    rw [show (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2 = ((2 : ℝ) ^ (2 * k + 2))⁻¹ by ring]
    exact ha _
  rw [← pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero]
  exact (sq_abs_sqrt_sub_sqrt_le _ _).trans hq

theorem Tracks.sqrtFast {a : CReal} {x : ℝ} {i : ℕ} (ha : a.Tracks x) (hx : ((4 : ℝ) ^ i)⁻¹ ≤ x) :
    (a.sqrtFast i).Tracks √x := by
  intro k
  apply abs_sub_le_of_halves (sqrtApprox_near (a.approx (k + i + 1)) (k + 1))
  have hsx : ((2 : ℝ) ^ i)⁻¹ ≤ √x := Real.le_sqrt_of_sq_le ((inv_two_pow_sq i).trans_le hx)
  refine le_of_mul_le_mul_right ?_ (lt_of_lt_of_le (by positivity) hsx)
  calc |√(a.approx (k + i + 1) : ℝ) - √x| * √x ≤ |(a.approx (k + i + 1) : ℝ) - x| :=
        abs_sqrt_sub_sqrt_mul_le _ _
    _ ≤ ((2 : ℝ) ^ (k + i + 1))⁻¹ := ha _
    _ = ((2 : ℝ) ^ (k + 1))⁻¹ * ((2 : ℝ) ^ i)⁻¹ := by rw [← mul_inv, ← pow_add]; ring_nf
    _ ≤ ((2 : ℝ) ^ (k + 1))⁻¹ * √x := by gcongr

theorem Tracks.le_of_sqrtProbe {a : CReal} {x : ℝ} {i : ℕ} (ha : a.Tracks x)
    (h : a.sqrtProbe = some i) : ((4 : ℝ) ^ i)⁻¹ ≤ x := by
  have hp : 2 / 4 ^ i ≤ a.approx (2 * i) := by
    unfold sqrtProbe at h
    simpa using List.find?_some h
  have hp' : 2 * ((4 : ℝ) ^ i)⁻¹ ≤ a.approx (2 * i) := by
    have := (Rat.cast_le (K := ℝ)).mpr hp
    push_cast at this
    rwa [div_eq_mul_inv] at this
  have hx : (a.approx (2 * i) : ℝ) - x ≤ ((4 : ℝ) ^ i)⁻¹ := by
    have := (abs_sub_le_iff.mp (ha (2 * i))).1
    rwa [pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num] at this
  linarith

theorem Tracks.sqrt {a : CReal} {x : ℝ} (ha : a.Tracks x) : a.sqrt.Tracks √x := by
  unfold CReal.sqrt
  split
  next i hi => exact ha.sqrtFast (ha.le_of_sqrtProbe hi)
  next => exact ha.sqrtSlow

theorem icbrt_spec (z : ℤ) : icbrt z ^ 3 ≤ z ∧ z < (icbrt z + 1) ^ 3 := by
  unfold icbrt
  split_ifs with hz
  · have hz' : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
    rw [← hz']
    exact ⟨by exact_mod_cast Nat.pow_nthRoot_le (.inl (by norm_num)),
      by exact_mod_cast Nat.lt_pow_nthRoot_add_one (by norm_num) _⟩
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
  have hr : cbrtApprox q m = (icbrt z : ℚ) / 2 ^ m := rfl
  constructor
  · rw [hr, div_pow, div_le_iff₀ (by positivity)]
    calc ((icbrt z : ℚ)) ^ 3 ≤ z := by exact_mod_cast h1
      _ ≤ q * (2 ^ m) ^ 3 := Int.floor_le _
  · rw [hr, show (icbrt z : ℚ) / 2 ^ m + (2 ^ m)⁻¹ = (icbrt z + 1) / 2 ^ m by field_simp,
      div_pow, lt_div_iff₀ (by positivity)]
    calc q * (2 ^ m) ^ 3 < z + 1 := Int.lt_floor_add_one _
      _ ≤ ((icbrt z : ℚ) + 1) ^ 3 := by exact_mod_cast h2

theorem cbrtApprox_near (q : ℚ) (m : ℕ) :
    |(cbrtApprox q m : ℝ) - Real.cbrt (q : ℝ)| ≤ ((2 : ℝ) ^ m)⁻¹ := by
  obtain ⟨hle, hlt⟩ := cbrtApprox_spec q m
  have hle' := (Rat.cast_le (K := ℝ)).mpr hle
  have hlt' := (Rat.cast_le (K := ℝ)).mpr hlt.le
  push_cast at hle' hlt'
  have lower := Real.le_cbrt_iff.mpr hle'
  have upper := Real.cbrt_le_iff.mpr hlt'
  have hh : (0 : ℝ) ≤ ((2 : ℝ) ^ m)⁻¹ := by positivity
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem abs_cbrt_sub_cbrt_mul (q x : ℝ) :
    |Real.cbrt q - Real.cbrt x| *
      (Real.cbrt q ^ 2 + Real.cbrt q * Real.cbrt x + Real.cbrt x ^ 2) = |q - x| := by
  conv_rhs => rw [← Real.cbrt_pow_three q, ← Real.cbrt_pow_three x]
  set a := Real.cbrt q
  set b := Real.cbrt x
  rw [show a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) by ring, abs_mul,
    abs_of_nonneg (by nlinarith [sq_nonneg (a + b / 2), sq_nonneg b] :
      (0 : ℝ) ≤ a ^ 2 + a * b + b ^ 2)]

theorem pow_three_abs_cbrt_sub_cbrt_le (q x : ℝ) :
    |Real.cbrt q - Real.cbrt x| ^ 3 ≤ 4 * |q - x| := by
  rw [← abs_cbrt_sub_cbrt_mul q x]
  set a := Real.cbrt q
  set b := Real.cbrt x
  calc |a - b| ^ 3 = |a - b| * (a - b) ^ 2 := by rw [pow_succ', sq_abs]
    _ ≤ |a - b| * (4 * (a ^ 2 + a * b + b ^ 2)) := by
      gcongr
      nlinarith [sq_nonneg (a + b)]
    _ = 4 * (|a - b| * (a ^ 2 + a * b + b ^ 2)) := by ring

theorem abs_cbrt_sub_cbrt_mul_le {q x : ℝ} {i : ℕ} (hx : ((8 : ℝ) ^ i)⁻¹ ≤ |x|) :
    |Real.cbrt q - Real.cbrt x| * (3 / 4 * ((4 : ℝ) ^ i)⁻¹) ≤ |q - x| := by
  rw [← abs_cbrt_sub_cbrt_mul q x]
  have hxb := Real.cbrt_pow_three x
  set a := Real.cbrt q
  set b := Real.cbrt x
  have hb : ((2 : ℝ) ^ i)⁻¹ ≤ |b| := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (abs_nonneg b) three_ne_zero, ← abs_pow, hxb,
      inv_two_pow_cube]
    exact hx
  have hb2 : ((4 : ℝ) ^ i)⁻¹ ≤ b ^ 2 :=
    calc ((4 : ℝ) ^ i)⁻¹ = (((2 : ℝ) ^ i)⁻¹) ^ 2 := (inv_two_pow_sq i).symm
      _ ≤ |b| ^ 2 := by gcongr
      _ = b ^ 2 := sq_abs b
  gcongr
  nlinarith [sq_nonneg (a + b / 2)]

theorem Tracks.cbrtSlow {a : CReal} {x : ℝ} (ha : a.Tracks x) :
    a.cbrtSlow.Tracks (Real.cbrt x) := by
  intro k
  apply abs_sub_le_of_halves (cbrtApprox_near (a.approx (3 * k + 5)) (k + 1))
  have hq : 4 * |(a.approx (3 * k + 5) : ℝ) - x| ≤ (((2 : ℝ) ^ (k + 1))⁻¹) ^ 3 := by
    have := ha (3 * k + 5)
    rw [show ((2 : ℝ) ^ (3 * k + 5))⁻¹ = (((2 : ℝ) ^ (k + 1))⁻¹) ^ 3 / 4 by ring] at this
    linarith
  rw [← pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) three_ne_zero]
  exact (pow_three_abs_cbrt_sub_cbrt_le _ _).trans hq

theorem Tracks.cbrtFast {a : CReal} {x : ℝ} {i : ℕ} (ha : a.Tracks x)
    (hx : ((8 : ℝ) ^ i)⁻¹ ≤ |x|) : (a.cbrtFast i).Tracks (Real.cbrt x) := by
  intro k
  apply abs_sub_le_of_halves (cbrtApprox_near (a.approx (k + 2 * i + 2)) (k + 1))
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 3 / 4 * ((4 : ℝ) ^ i)⁻¹)
  calc |Real.cbrt (a.approx (k + 2 * i + 2)) - Real.cbrt x| * (3 / 4 * ((4 : ℝ) ^ i)⁻¹)
      ≤ |(a.approx (k + 2 * i + 2) : ℝ) - x| := abs_cbrt_sub_cbrt_mul_le hx
    _ ≤ ((2 : ℝ) ^ (k + 2 * i + 2))⁻¹ := ha _
    _ = ((2 : ℝ) ^ (k + 1))⁻¹ * (1 / 2 * ((4 : ℝ) ^ i)⁻¹) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      field_simp
      ring
    _ ≤ ((2 : ℝ) ^ (k + 1))⁻¹ * (3 / 4 * ((4 : ℝ) ^ i)⁻¹) := by
      gcongr _ * (?_ * _)
      norm_num

theorem Tracks.le_of_cbrtProbe {a : CReal} {x : ℝ} {i : ℕ} (ha : a.Tracks x)
    (h : a.cbrtProbe = some i) : ((8 : ℝ) ^ i)⁻¹ ≤ |x| := by
  have hp : 2 / 8 ^ i ≤ |a.approx (3 * i)| := by
    unfold cbrtProbe at h
    simpa using List.find?_some h
  have hp' : 2 * ((8 : ℝ) ^ i)⁻¹ ≤ |(a.approx (3 * i) : ℝ)| := by
    have := (Rat.cast_le (K := ℝ)).mpr hp
    push_cast at this
    rwa [div_eq_mul_inv] at this
  have hx : |(a.approx (3 * i) : ℝ) - x| ≤ ((8 : ℝ) ^ i)⁻¹ := by
    have := ha (3 * i)
    rwa [pow_mul, show (2 : ℝ) ^ 3 = 8 by norm_num] at this
  have := abs_sub_abs_le_abs_sub (a.approx (3 * i) : ℝ) x
  linarith

theorem Tracks.cbrt {a : CReal} {x : ℝ} (ha : a.Tracks x) : a.cbrt.Tracks (Real.cbrt x) := by
  unfold CReal.cbrt
  split
  next i hi => exact ha.cbrtFast (ha.le_of_cbrtProbe hi)
  next => exact ha.cbrtSlow

theorem Tracks.mono {a : CReal} {x : ℝ} (h : a.Tracks x) {k j : ℕ} (hkj : k ≤ j) :
    |(a.approx j : ℝ) - x| ≤ ((2 : ℝ) ^ k)⁻¹ :=
  (h j).trans (inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hkj))

theorem Tracks.memo {a : CReal} {x : ℝ} (h : a.Tracks x) : a.memo.Tracks x := by
  intro k
  simp only [CReal.memo, Array.getElem?_ofFn]
  split_ifs with hk
  · exact h.mono (by simp only [memoStep]; omega)
  · exact h k

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
  memo := Tracks.memo

end CReal
