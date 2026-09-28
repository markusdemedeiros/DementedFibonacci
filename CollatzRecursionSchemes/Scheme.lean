module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import CollatzRecursionSchemes.Collatz

set_option linter.style.header false

@[expose] public section

open Int Option

variable {α β : Type*}

/-- A _Collatz Recursion Scheme_ is a tool for defining functions out of `ℕ+` which are correct
if and only if the Collatz conjecture is true. -/
structure CollatzRecursionScheme (α : Type*) where
  /-- Base case value `F 1` -/
  one : α
  /-- Odd cases: compute `F n` from `n` and `F (3 * n + 1)` -/
  odd (n : ℕ+) (vrec : α) : α
  /-- Even cases: compute `F n` from `n` and `F (n / 2)` -/
  even (n : ℕ+) (vrec : α) : α

/-- Evaluate a [CollatzRecursionScheme]. This term equals `none` when the Collatz recursion does
not terminate, and `some` when it does. -/
def CollatzRecursionScheme.toFun (s : CollatzRecursionScheme α) (n : ℕ+) : Option α :=
  if n = 1 then some s.one
  else if (n : ℕ) % 2 = 0 then return s.even n (← s.toFun ((n : ℕ) / 2).toPNat')
  else return s.odd n (← s.toFun (3 * n + 1))
partial_fixpoint

namespace CollatzRecursionScheme

variable (s : CollatzRecursionScheme α)

/-- A [CollatzRecursionScheme] is valid with respect to a function `ℕ+ → α` when the `one`, `odd`,
and `even` cases obey the Collatz recurrence. -/
@[grind cases]
structure Valid (spec : ℕ+ → α) : Prop where
  ok_one : s.one = spec 1
  ok_even (z : ℕ+) (vr : α) : z ≠ 1 → (z : ℕ) % 2 = 0 →
    spec ((z : ℕ) / 2).toPNat' = vr → s.even z vr = spec z
  ok_odd (z : ℕ+) (vr : α) : z ≠ 1 → (z : ℕ) % 2 ≠ 0 →
    spec (3 * z + 1) = vr → s.odd z vr = spec z

theorem toFun_one : s.toFun 1 = some s.one := by
  rw [toFun.eq_def, if_pos rfl]

theorem toFun_even {n : ℕ+} (h1 : n ≠ 1) (he : (n : ℕ) % 2 = 0) :
    s.toFun n = (s.toFun ((n : ℕ) / 2).toPNat').map (s.even n) := by
  rw [toFun.eq_def, if_neg h1, if_pos he]
  cases s.toFun ((n : ℕ) / 2).toPNat' <;> rfl

theorem toFun_odd {n : ℕ+} (h1 : n ≠ 1) (ho : (n : ℕ) % 2 ≠ 0) :
    s.toFun n = (s.toFun (3 * n + 1)).map (s.odd n) := by
  rw [toFun.eq_def, if_neg h1, if_neg ho]
  cases s.toFun (3 * n + 1) <;> rfl

/-- For a valid [CollatzRecursionScheme] `s`, any value `s.toFun` returns agrees with `spec`. -/
theorem correct (spec : ℕ+ → α) (Hv : s.Valid spec) :
    ∀ point value, s.toFun point = some value → value = spec point := by
  apply CollatzRecursionScheme.toFun.partial_correctness s
  intro candidate ih point value hsome
  split_ifs at hsome with h1 h2
  · grind
  · simp only [bind_eq_bind, bind_eq_some_iff] at hsome
    grind
  · simp only [bind_eq_bind, bind_eq_some_iff] at hsome
    grind

/-- For a valid [CollatzRecursionScheme] `s`, `s.toFun` agrees with the spec everywhere if and only
if it is total, ie. returns `some` everywhere. -/
theorem toFun_eq_spec_iff {spec : ℕ+ → α} (Hv : s.Valid spec) :
    s.toFun = some ∘ spec ↔ IsTotalFun s.toFun := by
  refine ⟨fun h n => ?_, fun h => funext fun n => ?_⟩
  · simp [show s.toFun n = (some ∘ spec) n from congrFun h n]
  · obtain ⟨p, hp⟩ := isSome_iff_exists.mp (h n)
    simp [hp, s.correct spec Hv n p hp]

theorem toFun_eq_some_of_halts {n : ℕ+} (h : Halts n) : (s.toFun n).isSome := by
  induction h with
  | one => simp [toFun.eq_def]
  | even hne hev _ ih =>
    obtain ⟨v, hv⟩ := isSome_iff_exists.mp ih
    rw [toFun.eq_def]
    simp [if_neg hne, if_pos hev, hv]
  | odd hne hodd _ ih =>
    obtain ⟨v, hv⟩ := isSome_iff_exists.mp ih
    rw [toFun.eq_def]
    simp [if_neg hne, if_neg hodd, hv]

theorem halts_of_toFun_eq_some : ∀ n r, s.toFun n = some r → Halts n := by
  apply CollatzRecursionScheme.toFun.partial_correctness s
  intro g ih n r hbody
  split_ifs at hbody with h1 h2
  · grind
  · simp only [bind_eq_bind, bind_eq_some_iff] at hbody
    grind
  · simp only [bind_eq_bind, bind_eq_some_iff] at hbody
    grind

/-- Totality of `s.toFun` is equivalent to halting for all `n`. -/
theorem isTotal_iff_halts : IsTotalFun s.toFun ↔ ∀ n, Halts n := by
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · obtain ⟨r, hr⟩ := isSome_iff_exists.mp (h n)
    exact s.halts_of_toFun_eq_some n r hr
  · exact s.toFun_eq_some_of_halts (h n)

/-- Totality of `s.toFun` is equivalent to the Collatz conjecture. -/
theorem isTotal_iff_Collatz : IsTotalFun s.toFun ↔ CollatzConjecture := by
  rw [s.isTotal_iff_halts]
  refine ⟨fun Ht n => ?_, fun Hc n => ?_⟩
  · rcases h : n with (_|n)
    · exists 1
    · apply collatzN_of_halts (n := ⟨n + 1, by grind⟩) (Ht _)
  · obtain ⟨fuel, hfuel⟩ := Hc n
    exact halts_of_collatzN fuel n hfuel

/-- Correctness of `s.toFun` is equivalent to the Collatz conjecture. -/
theorem toFun_eq_spec_iff_collatz {spec : ℕ+ → α} (Hv : s.Valid spec) :
    s.toFun = some ∘ spec ↔ CollatzConjecture :=
  (s.toFun_eq_spec_iff Hv).trans (isTotal_iff_Collatz s)

end CollatzRecursionScheme
