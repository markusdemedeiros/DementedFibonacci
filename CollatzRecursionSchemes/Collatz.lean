module

public import Mathlib.Data.PNat.Basic

set_option linter.style.header false

@[expose] public section

open Int

variable {α β : Type*}

def IsTotalFun (f : α → Option β) : Prop := ∀ a, (f a).isSome

/-- One step of the Collatz function. -/
def collatz (n : ℕ) : ℕ :=
  if n = 0 then 1 -- The junk n=0 also just returns 1
  else if n = 1 then 1
  else if n % 2 = 0 then n / 2
  else 3 * n + 1

/-- [k] steps of the Collatz function, returning `none` if fuel is exhausted. -/
def collatzN : ℕ → ℕ → Option ℕ
  | _, 1 => some 1
  | 0, _ => none
  | k+1, n => collatzN k (collatz n)

/-- The Collatz conjecture -/
def CollatzConjecture : Prop := ∀ n : ℕ, ∃ fuel : ℕ, collatzN fuel n = some 1

/-- Evidence that a positive natural number halts after finitely many Collatz steps. -/
@[grind] inductive Halts : ℕ+ → Prop where
  | one : Halts 1
  | even {n : ℕ+} : n ≠ 1 → (n : ℕ) % 2 = 0 → Halts ((n : ℕ) / 2).toPNat' → Halts n
  | odd {n : ℕ+} : n ≠ 1 → (n : ℕ) % 2 ≠ 0 → Halts (3 * n + 1) → Halts n

theorem collatzN_step {fuel : ℕ} {n : ℕ} (h : n ≠ 1) :
    collatzN (fuel + 1) n = collatzN fuel (collatz n) := by
  simp [collatzN]

theorem collatz_coe_even {n : ℕ+} (hne : n ≠ 1) (hev : (n : ℕ) % 2 = 0) :
    collatz (n : ℕ) = (((n : ℕ) / 2).toPNat' : ℕ) := by
  grind [collatz, Nat.toPNat'_coe, PNat.coe_eq_one_iff.not.mpr hne]

theorem collatz_coe_odd {n : ℕ+} (hne : n ≠ 1) (hodd : (n : ℕ) % 2 ≠ 0) :
    collatz (n : ℕ) = ((3 * n + 1 : ℕ+) : ℕ) := by
  simp [collatz, hne, hodd]

theorem halts_of_collatzN (fuel : ℕ) : ∀ (n : ℕ+), collatzN fuel (n : ℕ) = some 1 → Halts n := by
  induction fuel with
  | zero =>
    intro n h
    obtain rfl : n = 1 := by by_contra h1; simp [collatzN, h1] at h
    exact .one
  | succ k ih =>
    intro n h
    obtain rfl | h1 := eq_or_ne n 1
    · exact .one
    rw [collatzN_step (by simpa using h1)] at h
    by_cases hev : (n : ℕ) % 2 = 0
    · exact .even h1 hev (ih _ (collatz_coe_even h1 hev ▸ h))
    · exact .odd h1 hev (ih _ (collatz_coe_odd h1 hev ▸ h))

theorem collatzN_of_halts {n : ℕ+} (h : Halts n) : ∃ fuel, collatzN fuel (n : ℕ) = some 1 := by
  induction h with
  | one => exact ⟨0, rfl⟩
  | even hne hev _ ih =>
    obtain ⟨fuel, hfuel⟩ := ih
    exact ⟨fuel + 1, by rwa [collatzN_step (by simpa using hne), collatz_coe_even hne hev]⟩
  | odd hne hodd _ ih =>
    obtain ⟨fuel, hfuel⟩ := ih
    exact ⟨fuel + 1, by rwa [collatzN_step (by simpa using hne), collatz_coe_odd hne hodd]⟩
