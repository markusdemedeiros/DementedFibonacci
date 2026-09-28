module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

end Real

inductive Exp where
  | Add (e₁ e₂ : Exp)
  | Neg (e : Exp)
  | Mul (e₁ e₂ : Exp)
  | OfRat (q : ℚ)
  | ToThePowerOf (e : Exp) (arg : ℤ → ℕ)
  | Sqrt (e : Exp)
  | Cubert (e : Exp) -- Everybody loves Cubert :)
  | Bpos (enn eneg : Exp)
  | Beven (eeven eodd : Exp)
  | φ
  | Recurse (f : ℤ → ℤ)

class Denotable (α : Type*) extends Add α, Neg α, Mul α, Pow α ℕ where
  ofRat : ℚ → α
  sqrt : α → α
  cbrt : α → α
  φ : α

noncomputable instance : Denotable ℝ where
  ofRat q := q
  sqrt := Real.sqrt
  cbrt := Real.cbrt
  φ := Real.goldenRatio

@[simp] theorem Denotable.ofRat_real (q : ℚ) : (Denotable.ofRat q : ℝ) = q := rfl
@[simp] theorem Denotable.sqrt_real (x : ℝ) : Denotable.sqrt x = √x := rfl
@[simp] theorem Denotable.cbrt_real (x : ℝ) : Denotable.cbrt x = Real.cbrt x := rfl
@[simp] theorem Denotable.φ_real : (Denotable.φ : ℝ) = Real.goldenRatio := rfl

variable {α β : Type*} [Denotable α] [Denotable β]

def denote (body e : Exp) (n : ℤ) : Option α :=
  match e with
  | .Add e₁ e₂ => do
    let v₁ ← denote body e₁ n
    let v₂ ← denote body e₂ n
    return (v₁ + v₂)
  | .Neg e => do
    let v ← denote body e n
    return - v
  | .Mul e₁ e₂ => do
    let v₁ ← denote body e₁ n
    let v₂ ← denote body e₂ n
    return v₁ * v₂
  | .OfRat q => do
    return Denotable.ofRat q
  | .ToThePowerOf e arg => do
    let v ← denote body e n
    return v ^ (arg n)
  | .Sqrt e => do
    let v ← denote body e n
    return Denotable.sqrt v
  | .Cubert e => do
    let v ← denote body e n
    return Denotable.cbrt v
  | .Bpos enn eneg =>
    if 0 ≤ n then denote body enn n else denote body eneg n
  | .Beven eeven eodd =>
    if n % 2 = 0 then denote body eeven n else denote body eodd n
  | .φ => do
    return Denotable.φ
  | .Recurse arg =>
    denote body body (arg n)
partial_fixpoint

def run (body : Exp) (n : ℤ) : Option α :=
  denote body body n

section denote_lemmas
variable (body : Exp) (n : ℤ)

@[simp] theorem denote_add (e₁ e₂ : Exp) : (denote body (.Add e₁ e₂) n : Option α) =
    (denote body e₁ n).bind fun v₁ => (denote body e₂ n).bind fun v₂ => some (v₁ + v₂) := by
  rw [denote]; rfl

@[simp] theorem denote_neg (e : Exp) :
    (denote body (.Neg e) n : Option α) = (denote body e n).bind fun v => some (-v) := by
  rw [denote]; rfl

@[simp] theorem denote_mul (e₁ e₂ : Exp) : (denote body (.Mul e₁ e₂) n : Option α) =
    (denote body e₁ n).bind fun v₁ => (denote body e₂ n).bind fun v₂ => some (v₁ * v₂) := by
  rw [denote]; rfl

@[simp] theorem denote_ofRat (q : ℚ) :
    (denote body (.OfRat q) n : Option α) = some (Denotable.ofRat q) := by
  rw [denote]; rfl

@[simp] theorem denote_toThePowerOf (e : Exp) (f : ℤ → ℕ) :
    (denote body (.ToThePowerOf e f) n : Option α) =
      (denote body e n).bind fun v => some (v ^ f n) := by
  rw [denote]; rfl

@[simp] theorem denote_sqrt (e : Exp) :
    (denote body (.Sqrt e) n : Option α) =
      (denote body e n).bind fun v => some (Denotable.sqrt v) := by
  rw [denote]; rfl

@[simp] theorem denote_cubert (e : Exp) :
    (denote body (.Cubert e) n : Option α) =
      (denote body e n).bind fun v => some (Denotable.cbrt v) := by
  rw [denote]; rfl

@[simp] theorem denote_bpos_of_nonneg (enn eneg : Exp) (h : 0 ≤ n) :
    (denote body (.Bpos enn eneg) n : Option α) = denote body enn n := by
  rw [denote, if_pos h]

@[simp] theorem denote_bpos_of_neg (enn eneg : Exp) (h : n < 0) :
    (denote body (.Bpos enn eneg) n : Option α) = denote body eneg n := by
  rw [denote, if_neg (Int.not_le.mpr h)]

@[simp] theorem denote_beven_of_even (eeven eodd : Exp) (h : n % 2 = 0) :
    (denote body (.Beven eeven eodd) n : Option α) = denote body eeven n := by
  rw [denote, if_pos h]

@[simp] theorem denote_beven_of_odd (eeven eodd : Exp) (h : n % 2 = 1) :
    (denote body (.Beven eeven eodd) n : Option α) = denote body eodd n := by
  rw [denote, if_neg (by omega)]

@[simp] theorem denote_φ : (denote body .φ n : Option α) = some Denotable.φ := by
  rw [denote]; rfl

@[simp] theorem denote_recurse (f : ℤ → ℤ) :
    (denote body (.Recurse f) n : Option α) = denote body body (f n) := by
  rw [denote]

end denote_lemmas

structure Denotable.Rel (R : α → β → Prop) : Prop where
  add {a b x y} : R a x → R b y → R (a + b) (x + y)
  neg {a x} : R a x → R (-a) (-x)
  mul {a b x y} : R a x → R b y → R (a * b) (x * y)
  pow {a x} (m : ℕ) : R a x → R (a ^ m) (x ^ m)
  ofRat (q : ℚ) : R (ofRat q) (ofRat q)
  sqrt {a x} : R a x → R (sqrt a) (sqrt x)
  cbrt {a x} : R a x → R (cbrt a) (cbrt x)
  φ : R φ φ

theorem Denotable.Rel.flip {R : α → β → Prop} (hR : Rel R) : Rel (flip R) where
  add := hR.add
  neg := hR.neg
  mul := hR.mul
  pow m := hR.pow m
  ofRat q := hR.ofRat q
  sqrt := hR.sqrt
  cbrt := hR.cbrt
  φ := hR.φ

theorem Denotable.Rel.denote {R : α → β → Prop} (hR : Rel R) {body e : Exp} {n : ℤ} {a : α}
    (h : denote body e n = some a) : ∃ x : β, denote body e n = some x ∧ R a x := by
  revert e n a h
  apply _root_.denote.partial_correctness
  intro d IH e n a h
  cases e with
  | Add e₁ e₂ =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := h
    obtain ⟨x₁, hx₁, r₁⟩ := IH _ _ _ h₁
    obtain ⟨x₂, hx₂, r₂⟩ := IH _ _ _ h₂
    exact ⟨_, by simp [hx₁, hx₂], hR.add r₁ r₂⟩
  | Mul e₁ e₂ =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := h
    obtain ⟨x₁, hx₁, r₁⟩ := IH _ _ _ h₁
    obtain ⟨x₂, hx₂, r₂⟩ := IH _ _ _ h₂
    exact ⟨_, by simp [hx₁, hx₂], hR.mul r₁ r₂⟩
  | Neg e =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a₁, h₁, rfl⟩ := h
    obtain ⟨x₁, hx₁, r₁⟩ := IH _ _ _ h₁
    exact ⟨_, by simp [hx₁], hR.neg r₁⟩
  | ToThePowerOf e f =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a₁, h₁, rfl⟩ := h
    obtain ⟨x₁, hx₁, r₁⟩ := IH _ _ _ h₁
    exact ⟨_, by simp [hx₁], hR.pow _ r₁⟩
  | Sqrt e =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a₁, h₁, rfl⟩ := h
    obtain ⟨x₁, hx₁, r₁⟩ := IH _ _ _ h₁
    exact ⟨_, by simp [hx₁], hR.sqrt r₁⟩
  | Cubert e =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a₁, h₁, rfl⟩ := h
    obtain ⟨x₁, hx₁, r₁⟩ := IH _ _ _ h₁
    exact ⟨_, by simp [hx₁], hR.cbrt r₁⟩
  | OfRat q =>
    simp only [pure, Option.some.injEq] at h
    exact ⟨_, by simp, h ▸ hR.ofRat q⟩
  | φ =>
    simp only [pure, Option.some.injEq] at h
    exact ⟨_, by simp, h ▸ hR.φ⟩
  | Bpos e₁ e₂ =>
    dsimp only at h
    split_ifs at h with hn
    · obtain ⟨x, hx, r⟩ := IH _ _ _ h
      exact ⟨x, by rwa [denote_bpos_of_nonneg _ _ _ _ hn], r⟩
    · obtain ⟨x, hx, r⟩ := IH _ _ _ h
      exact ⟨x, by rwa [denote_bpos_of_neg _ _ _ _ (by omega)], r⟩
  | Beven e₁ e₂ =>
    dsimp only at h
    split_ifs at h with hn
    · obtain ⟨x, hx, r⟩ := IH _ _ _ h
      exact ⟨x, by rwa [denote_beven_of_even _ _ _ _ hn], r⟩
    · obtain ⟨x, hx, r⟩ := IH _ _ _ h
      exact ⟨x, by rwa [denote_beven_of_odd _ _ _ _ (by omega)], r⟩
  | Recurse f =>
    obtain ⟨x, hx, r⟩ := IH _ _ _ h
    exact ⟨x, by rwa [denote_recurse], r⟩

declare_syntax_cat exp

syntax:max num : exp
syntax:max ident : exp
syntax "(" exp ")" : exp
syntax:65 exp:65 " + " exp:66 : exp
syntax:65 exp:65 " - " exp:66 : exp
syntax:70 exp:70 " * " exp:71 : exp
syntax:70 exp:70 " / " num : exp
syntax:75 "-" exp:75 : exp
syntax:75 exp:76 " ^ " term:max : exp
syntax:max "√" exp:max : exp
syntax:max "∛" exp:max : exp
syntax:max "rec " term:max : exp
syntax:lead ident exp:max exp:max : exp

syntax "exp(" exp ")" : term
syntax:min "exp% " exp : term

macro_rules
  | `(exp% $e) => `(exp($e))
  | `(exp($n:num)) => `(Exp.OfRat $n)
  | `(exp($x:ident)) => if x.getId == `φ then `(Exp.φ) else `($x)
  | `(exp(($e))) => `(exp($e))
  | `(exp($e₁ + $e₂)) => `(Exp.Add exp($e₁) exp($e₂))
  | `(exp($e₁ - $e₂)) => `(Exp.Add exp($e₁) (Exp.Neg exp($e₂)))
  | `(exp($e₁ * $e₂)) => `(Exp.Mul exp($e₁) exp($e₂))
  | `(exp($e / $n)) => `(Exp.Mul exp($e) (Exp.OfRat (1 / $n)))
  | `(exp(-$e)) => `(Exp.Neg exp($e))
  | `(exp($e ^ $f)) => `(Exp.ToThePowerOf exp($e) $f)
  | `(exp(√$e)) => `(Exp.Sqrt exp($e))
  | `(exp(∛$e)) => `(Exp.Cubert exp($e))
  | `(exp(rec $f)) => `(Exp.Recurse $f)
  | `(exp($j:ident $e₁ $e₂)) =>
    match j.getId with
    | `jns => `(Exp.Bpos exp($e₁) exp($e₂))
    | `js => `(Exp.Bpos exp($e₂) exp($e₁))
    | `jpe => `(Exp.Beven exp($e₁) exp($e₂))
    | `jpo => `(Exp.Beven exp($e₂) exp($e₁))
    | _ => Lean.Macro.throwErrorAt j "expected `jns`, `js`, `jpe` or `jpo`"
