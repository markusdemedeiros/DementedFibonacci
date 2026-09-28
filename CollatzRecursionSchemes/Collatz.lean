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
def CollatzN : ℕ → ℕ → Option ℕ
  | _, 1 => some 1
  | 0, _ => none
  | k+1, n => CollatzN k (collatz n)

/-- The Collatz conjecture -/
def CollatzConjecture : Prop := ∀ n : ℕ, ∃ fuel : ℕ, CollatzN fuel n = some 1

/-- Evidence that a positive natural number halts. -/
@[grind] inductive Halts : ℕ+ → Prop where
  | one : Halts 1
  | even {n : ℕ+} : n ≠ 1 → (n : ℕ) % 2 = 0 → Halts ((n : ℕ) / 2).toPNat' → Halts n
  | odd {n : ℕ+} : n ≠ 1 → (n : ℕ) % 2 ≠ 0 → Halts (3 * n + 1) → Halts n


theorem CollatzN_step {fuel : ℕ} {n : ℕ} (h : n ≠ 1) :
    CollatzN (fuel + 1) n = CollatzN fuel (collatz n) := by
  conv_lhs => unfold CollatzN
  split <;> simp_all

theorem collatz_coe_even {n : ℕ+} (hne : n ≠ 1) (hev : (n : ℕ) % 2 = 0) :
    collatz (n : ℕ) = (((n : ℕ) / 2).toPNat' : ℕ) := by
  have hn1 : (n : ℕ) ≠ 1 := by simpa using hne
  have hpos : 0 < (n : ℕ) / 2 := by have := n.pos; omega
  rw [collatz, if_neg hn1, if_pos hev, PNat.toPNat'_coe hpos]
  grind

theorem collatz_coe_odd {n : ℕ+} (hne : n ≠ 1) (hodd : (n : ℕ) % 2 ≠ 0) :
    collatz (n : ℕ) = ((3 * n + 1 : ℕ+) : ℕ) := by
  have hn1 : (n : ℕ) ≠ 1 := by simpa using hne
  simp only [collatz, if_neg hn1, if_neg hodd]
  push_cast
  grind

theorem Halts_of_collatzN : ∀ (fuel : ℕ) (n : ℕ+), CollatzN fuel (n : ℕ) = some 1 → Halts n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n h
    unfold CollatzN at h
    split at h <;>
      first
      | (rename_i heq; exact (by exact_mod_cast heq : n = 1) ▸ Halts.one)
      | simp_all
  | succ k ih =>
    intro n h
    by_cases h1 : n = 1
    · exact h1 ▸ Halts.one
    · have hn1 : (n : ℕ) ≠ 1 := by simpa using h1
      rw [CollatzN_step hn1] at h
      by_cases hev : (n : ℕ) % 2 = 0
      · rw [collatz_coe_even h1 hev] at h
        exact Halts.even h1 hev (ih _ h)
      · rw [collatz_coe_odd h1 hev] at h
        exact Halts.odd h1 hev (ih _ h)

theorem collatzN_of_halts {n : ℕ+} (h : Halts n) : ∃ fuel, CollatzN fuel (n : ℕ) = some 1 := by
  induction h with
  | one => exact ⟨0, by simp [CollatzN]⟩
  | @even n hne hev _ ih =>
    obtain ⟨fuel, hfuel⟩ := ih
    refine ⟨fuel + 1, ?_⟩
    rw [CollatzN_step (by simpa using hne), collatz_coe_even hne hev]
    exact hfuel
  | @odd n hne hodd _ ih =>
    obtain ⟨fuel, hfuel⟩ := ih
    refine ⟨fuel + 1, ?_⟩
    rw [CollatzN_step (by simpa using hne), collatz_coe_odd hne hodd]
    exact hfuel
