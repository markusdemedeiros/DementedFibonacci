module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzRecursionSchemes.Schemes.Fibonacci

set_option linter.style.header false

@[expose] public section

inductive AExp where
  | div2
  | toArgDiv2
  | trp1
  | toArgTrp1
  | two
  deriving DecidableEq, Hashable, Repr

@[simp] def AExp.eval : AExp → ℤ → ℤ
  | div2, m => (m + 2) / 2
  | toArgDiv2, m => (m + 2) / 2 - 2
  | trp1, m => (m + 2) * 3 + 1
  | toArgTrp1, m => (m + 2) * 3 + 1 - 2
  | two, _ => 2

instance : Hashable ℚ := ⟨fun q => mixHash (hash q.num) (hash q.den)⟩

inductive Exp where
  | Add (e₁ e₂ : Exp)
  | Neg (e : Exp)
  | Mul (e₁ e₂ : Exp)
  | OfRat (q : ℚ)
  | ToThePowerOf (e : Exp) (arg : AExp)
  | Sqrt (e : Exp)
  | Cubert (e : Exp) -- Everybody loves Cubert :)
  | Bpos (enn eneg : Exp)
  | Beven (eeven eodd : Exp)
  | φ
  | Recurse (f : AExp)
  | Share (e : Exp)
  deriving DecidableEq, Hashable

class Denotable (α : Type*) extends Add α, Neg α, Mul α, Pow α ℕ where
  ofRat : ℚ → α
  sqrt : α → α
  cbrt : α → α
  φ : α
  memo : α → α

noncomputable instance : Denotable ℝ where
  ofRat q := q
  sqrt := Real.sqrt
  cbrt := Real.cbrt
  φ := Real.goldenRatio
  memo x := x

@[simp] theorem Denotable.ofRat_real (q : ℚ) : (Denotable.ofRat q : ℝ) = q := rfl
@[simp] theorem Denotable.sqrt_real (x : ℝ) : Denotable.sqrt x = √x := rfl
@[simp] theorem Denotable.cbrt_real (x : ℝ) : Denotable.cbrt x = Real.cbrt x := rfl
@[simp] theorem Denotable.φ_real : (Denotable.φ : ℝ) = Real.goldenRatio := rfl
@[simp] theorem Denotable.memo_real (x : ℝ) : Denotable.memo x = x := rfl

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
    return v ^ (arg.eval n).toNat
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
    denote body body (arg.eval n)
  | .Share e => do
    let v ← denote body e n
    return Denotable.memo v
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

@[simp] theorem denote_toThePowerOf (e : Exp) (f : AExp) :
    (denote body (.ToThePowerOf e f) n : Option α) =
      (denote body e n).bind fun v => some (v ^ (f.eval n).toNat) := by
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

@[simp] theorem denote_recurse (f : AExp) :
    (denote body (.Recurse f) n : Option α) = denote body body (f.eval n) := by
  rw [denote]

@[simp] theorem denote_share (e : Exp) :
    (denote body (.Share e) n : Option α) =
      (denote body e n).bind fun v => some (Denotable.memo v) := by
  rw [denote]; rfl

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
  memo {a x} : R a x → R (memo a) (memo x)

theorem Denotable.Rel.flip {R : α → β → Prop} (hR : Rel R) : Rel (flip R) where
  add := hR.add
  neg := hR.neg
  mul := hR.mul
  pow m := hR.pow m
  ofRat q := hR.ofRat q
  sqrt := hR.sqrt
  cbrt := hR.cbrt
  φ := hR.φ
  memo := hR.memo

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
  | Share e =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a₁, h₁, rfl⟩ := h
    obtain ⟨x₁, hx₁, r₁⟩ := IH _ _ _ h₁
    exact ⟨_, by simp [hx₁], hR.memo r₁⟩

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
syntax:max "share(" exp ")" : exp
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
  | `(exp(share($e))) => `(Exp.Share exp($e))
  | `(exp($j:ident $e₁ $e₂)) =>
    match j.getId with
    | `jns => `(Exp.Bpos exp($e₁) exp($e₂))
    | `js => `(Exp.Bpos exp($e₂) exp($e₁))
    | `jpe => `(Exp.Beven exp($e₁) exp($e₂))
    | `jpo => `(Exp.Beven exp($e₂) exp($e₁))
    | _ => Lean.Macro.throwErrorAt j "expected `jns`, `js`, `jpe` or `jpo`"

def fibEven : Exp :=
  exp% (share(share(φ) ^ .div2) + (1 - share(φ)) ^ .div2) * rec .toArgDiv2

def fibOdd : Exp :=
  let G := exp% share(share(share(φ) ^ .trp1) - share(φ) * rec .toArgTrp1)
  let D := exp% share(√(25 * G ^ .two - 20) / 50)
  exp% ∛(G / 10 + D) + ∛(G / 10 - D)

def fibProg : Exp := exp%
  share(js (jpe 0 1) (jpe fibEven fibOdd))

noncomputable def fibRun (n : ℕ) : Option ℝ := run fibProg (n - 2)

theorem fibRun_zero : fibRun 0 = some 0 := by
  simp only [fibRun, run]
  change (denote fibProg (.Share (.Bpos (.Beven fibEven fibOdd) (.Beven (.OfRat 0) (.OfRat 1))))
    _ : Option ℝ) = _
  simp (disch := decide) only [denote_share, denote_bpos_of_neg, denote_beven_of_even, denote_ofRat,
    Denotable.ofRat_real, Rat.cast_zero, Option.bind_some, Denotable.memo_real]

theorem fibRun_one : fibRun 1 = some 1 := by
  simp only [fibRun, run]
  change (denote fibProg (.Share (.Bpos (.Beven fibEven fibOdd) (.Beven (.OfRat 0) (.OfRat 1))))
    _ : Option ℝ) = _
  simp (disch := decide) only [denote_share, denote_bpos_of_neg, denote_beven_of_odd, denote_ofRat,
    Denotable.ofRat_real, Rat.cast_one, Option.bind_some, Denotable.memo_real]

theorem fibRun_even (n : ℕ) (hn : 0 < n) (he : n % 2 = 0) :
    fibRun n = (fibRun (n / 2)).map (Real.fibRecEven · n) := by
  simp only [fibRun, run]
  change (denote fibProg (.Share (.Bpos (.Beven fibEven fibOdd) (.Beven (.OfRat 0) (.OfRat 1))))
    _ : Option ℝ) = _
  have e : ((n : ℤ) - 2 + 2) / 2 = ((n / 2 : ℕ) : ℤ) := by omega
  simp (disch := omega) only [denote_bpos_of_nonneg, denote_beven_of_even, fibEven, denote_mul,
    denote_add, denote_toThePowerOf, denote_φ, denote_ofRat, denote_neg, denote_recurse,
    Option.bind_some, AExp.eval, denote_share, e, Int.toNat_natCast]
  cases (denote fibProg fibProg (((n / 2 : ℕ) : ℤ) - 2) : Option ℝ) <;>
    simp only [Option.bind_some, Option.bind_none, Option.map_some, Option.map_none,
      Real.fibRecEven, Denotable.ofRat_real, Denotable.memo_real, Denotable.φ_real, Rat.cast_one,
      sub_eq_add_neg]

theorem fibRun_odd (n : ℕ) (hn : 1 < n) (ho : n % 2 = 1) :
    fibRun n = (fibRun (3 * n + 1)).map (Real.fibRecOdd · n) := by
  simp only [fibRun, run]
  change (denote fibProg (.Share (.Bpos (.Beven fibEven fibOdd) (.Beven (.OfRat 0) (.OfRat 1))))
    _ : Option ℝ) = _
  have e : ((n : ℤ) - 2 + 2) * 3 + 1 = ((3 * n + 1 : ℕ) : ℤ) := by push_cast; ring
  rcases hrec : (denote fibProg fibProg (((3 * n + 1 : ℕ) : ℤ) - 2) : Option ℝ) with _ | v <;>
    simp (disch := omega) only [denote_bpos_of_nonneg, denote_beven_of_odd, fibOdd, denote_mul,
      denote_add, denote_toThePowerOf, denote_φ, denote_neg, denote_recurse,
      denote_sqrt, denote_cubert, denote_ofRat, Option.bind_some, Option.bind_none,
      Option.map_some, Option.map_none, AExp.eval, denote_share, e, Int.toNat_natCast, hrec]
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
  | .Recurse f, n => [f.eval n]
  | .Share e, n => calls e n

def HaltsAt (m : ℤ) : Prop := ∃ fuel, collatzN fuel (m + 2).toNat = some 1

theorem haltsAt_of_neg {m : ℤ} (hm : m < 0) : HaltsAt m := by
  exists 1
  by_cases hm : m = -1
  · simp [hm, collatzN]
  · simp [show (m + 2).toNat = 0 by grind, collatzN, collatz]

theorem haltsAt_of_calls {m : ℤ} (h : ∀ k ∈ calls fibProg m, HaltsAt k) : HaltsAt m := by
  by_cases hm : m < 0
  · exact haltsAt_of_neg hm
  simp only [fibProg, fibEven, fibOdd, calls, not_lt.mp hm, ↓reduceIte, AExp.eval,
    List.append_nil, List.nil_append, List.cons_append] at h
  split at h
  · obtain ⟨k, H⟩ := h _ List.mem_cons_self
    exact ⟨k + 1, by unfold collatzN; grind [collatz]⟩
  · obtain ⟨k, H⟩ := h _ List.mem_cons_self
    exact ⟨k + 1, by unfold collatzN; grind [collatz]⟩

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
  | Neg e | ToThePowerOf e _ | Sqrt e | Cubert e | Share e =>
    cases h₁ : denote e n
    · grind
    · grind [calls]
  | OfRat _ | φ => grind [calls]
  | Bpos e₁ e₂ | Beven e₁ e₂ => grind [calls]
  | Recurse arg => grind [calls, haltsAt_of_calls]

theorem halts_of_fibRun_eq_some {n : ℕ+} {v : ℝ} (h : fibRun n = some v) : Halts n := by
  obtain ⟨fuel, hf⟩ := haltsAt_of_calls (calls_haltsAt_of_denote_eq_some h)
  exact halts_of_collatzN fuel n (by simpa using hf)

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
  Option.eq_none_iff_forall_ne_some.mpr fun v hv => h (s.halts_of_toFun_eq_some n v hv)

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
