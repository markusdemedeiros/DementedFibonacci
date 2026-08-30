module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Nat.Fib.Basic

set_option linter.style.header false

@[expose] public section

open Int

structure CollatzRecursionScheme where
  /-- Base case value -/
  one : ℕ+
  /-- Odd cases: compute `F n` from `n` and `F (3 * n + 1)` -/
  odd (n vrec : ℕ+) : ℕ+
  /-- Even cases: compute `F n` from `n` and `F (n / 2)` -/
  even (n vrec : ℕ+) : ℕ+

/-- Extend a spec to include a point at zero -/
def extend (spec : ℕ+ → ℕ+) : ℕ+ → ℕ := (spec ·)

/-- Predicate declaring when a collatz recursion scheme obeys the spec. -/
@[grind cases]
structure CollatzRecursionScheme.Valid (s : CollatzRecursionScheme) (spec : ℕ+ → ℕ+) : Prop
    where
  ok_one : s.one = spec 1
  ok_even (z vr : ℕ+) : z ≠ 1 → (z : ℕ) % 2 = 0 →
    spec ((z : ℕ) / 2).toPNat' = vr → s.even z vr = spec z
  ok_odd (z vr : ℕ+) : z ≠ 1 → (z : ℕ) % 2 ≠ 0 →
    spec (3 * z + 1) = vr → s.odd z vr = spec z

def CollatzRecursionScheme.asOptFun (s : CollatzRecursionScheme) (n : ℕ+) : Option ℕ+ :=
  if n = 1 then some s.one
  else if (n : ℕ) % 2 = 0 then return s.even n (← s.asOptFun ((n : ℕ) / 2).toPNat')
  else return s.odd n (← s.asOptFun (3 * n + 1))
partial_fixpoint

/-- The implementation as a total `ℕ+ → ℕ` function: `0` on divergence, else the computed value. -/
def CollatzRecursionScheme.toFun (s : CollatzRecursionScheme) (n : ℕ+) : ℕ :=
  ((s.asOptFun n).map PNat.val).getD 0

/-- Correctness of a collatz recursion scheme: when `s.asOptFun` returns a value, it matches
the specification function `spec`. -/
theorem CollatzRecursionScheme.correct (s : CollatzRecursionScheme) (spec : ℕ+ → ℕ+)
    (Hv : s.Valid spec) : ∀ point value, s.asOptFun point = some value → value = spec point := by
  apply CollatzRecursionScheme.asOptFun.partial_correctness s
  intro candidate ih point value hsome
  split_ifs at hsome with h1 h2
  · -- base case: point = 1
    subst h1
    simp only [Option.some.injEq] at hsome
    rw [← hsome]; exact Hv.ok_one
  · -- even case
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hsome
    obtain ⟨w, hw, hval⟩ := hsome
    rw [Option.pure_def, Option.some.injEq] at hval
    rw [← hval]
    exact Hv.ok_even point w h1 h2 (ih _ _ hw).symm
  · -- odd case
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hsome
    obtain ⟨w, hw, hval⟩ := hsome
    rw [Option.pure_def, Option.some.injEq] at hval
    rw [← hval]
    exact Hv.ok_odd point w h1 h2 (ih _ _ hw).symm

def IsTotalFun (f : α → Option β) : Prop := ∀ a, (f a).isSome

theorem CollatzRecursionScheme.toFun_eq_extend_iff (s : CollatzRecursionScheme) {spec : ℕ+ → ℕ+}
    (Hv : s.Valid spec) : s.toFun = extend spec ↔ IsTotalFun s.asOptFun := by
  constructor
  · intro h n
    rcases hh : s.asOptFun n with _ | p
    · exfalso
      have he := congrFun h n
      simp only [toFun, extend, hh, Option.map_none, Option.getD_none] at he
      have := (spec n).pos
      omega
    · rfl
  · intro h
    funext n
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (h n)
    have := s.correct spec Hv n p hp
    simp [toFun, extend, hp, this]

-- Now: Characterize the totality of the scheme

def collatz (n : ℕ) : ℕ :=
  -- Make the junk n=0 case also just return 1
  if n = 0 then 1
  else if n = 1 then 1
  else if n % 2 = 0 then n / 2
  else 3 * n + 1

def CollatzN : ℕ → ℕ → Option ℕ
  | _, 1 => some 1
  | 0, _ => none
  | k+1, n => CollatzN k (collatz n)

def CollatzConjecture : Prop := ∀ n : ℕ, ∃ fuel : ℕ, CollatzN fuel n = some 1

inductive Halts : ℕ+ → Prop where
  | one : Halts 1
  | even {n : ℕ+} : n ≠ 1 → (n : ℕ) % 2 = 0 → Halts ((n : ℕ) / 2).toPNat' → Halts n
  | odd {n : ℕ+} : n ≠ 1 → (n : ℕ) % 2 ≠ 0 → Halts (3 * n + 1) → Halts n

theorem Halts.asOptFun_isSome (s : CollatzRecursionScheme) {n : ℕ+} (h : Halts n) :
    (s.asOptFun n).isSome := by
  induction h with
  | one => rw [CollatzRecursionScheme.asOptFun.eq_def]; simp
  | @even n hne hev _ ih =>
    rw [CollatzRecursionScheme.asOptFun.eq_def]
    simp only [if_neg hne, if_pos hev]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ih
    simp [hv]
  | @odd n hne hodd _ ih =>
    rw [CollatzRecursionScheme.asOptFun.eq_def]
    simp only [if_neg hne, if_neg hodd]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ih
    simp [hv]

theorem CollatzRecursionScheme.halts_of_eq_some (s : CollatzRecursionScheme) :
    ∀ n r, s.asOptFun n = some r → Halts n := by
  apply CollatzRecursionScheme.asOptFun.partial_correctness s
  intro g ih n r hbody
  split_ifs at hbody with h1 h2
  · subst h1; exact Halts.one
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hbody
    obtain ⟨w, hw, _⟩ := hbody
    exact Halts.even h1 h2 (ih _ _ hw)
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hbody
    obtain ⟨w, hw, _⟩ := hbody
    exact Halts.odd h1 h2 (ih _ _ hw)

theorem CollatzRecursionScheme.isTotal_iff_halts (s : CollatzRecursionScheme) :
    IsTotalFun s.asOptFun ↔ ∀ n, Halts n := by
  constructor
  · intro h n
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (h n)
    exact s.halts_of_eq_some n r hr
  · intro h n
    exact (h n).asOptFun_isSome s

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

theorem IsTotal_of_Collatz (s : CollatzRecursionScheme) (Hc : CollatzConjecture) :
    IsTotalFun s.asOptFun := by
  rw [s.isTotal_iff_halts]
  intro n
  obtain ⟨fuel, hfuel⟩ := Hc n
  exact Halts_of_collatzN fuel n hfuel

theorem Collatz_of_IsTotal (s : CollatzRecursionScheme) (Ht : IsTotalFun s.asOptFun) :
    CollatzConjecture := by
  rw [s.isTotal_iff_halts] at Ht
  intro n
  rcases h : n with (_|n)
  · exists 1
  · apply collatzN_of_halts (n := ⟨n + 1, by grind⟩) (Ht _)

theorem IsTotal_iff_Collatz (s : CollatzRecursionScheme) :
    IsTotalFun s.asOptFun ↔ CollatzConjecture :=
  ⟨Collatz_of_IsTotal s, IsTotal_of_Collatz s⟩

theorem CollatzRecursionScheme.toFun_eq_extend_iff_collatz (s : CollatzRecursionScheme)
    {spec : ℕ+ → ℕ+} (Hv : s.Valid spec) : s.toFun = extend spec ↔ CollatzConjecture :=
  (s.toFun_eq_extend_iff Hv).trans (IsTotal_iff_Collatz s)

/--
Collatz recursion scheme for the simple arithmetic sequence
`Sn = 2 * n + 1`

Even constructor:
```
S(2n)
  = 2 * (2n) + 1
  = 2n+1 + 2n
  = Sn + 2n
```
Halving `n`, we get `Sn = S(n/2) + n`

Odd constructor:
```
3 * Sn
  = 3(2n + 1)
  = 6n + 3
  = 2(3n+1) + 1
  = S(3n+1)
```
So `Sn = S(3n+1) / 3`

Base case:
`S1 = 2(1) + 1 = 3`
-/
def ArthmeticCollatzScheme : CollatzRecursionScheme where
  one := 3
  odd _n vrec := ((vrec : ℕ) / 3).toPNat'
  even n vrec := n + vrec

def ArthmeticCollatzScheme.spec (z : ℕ+) : ℕ+ := 2 * z + 1

theorem ArthmeticCollatzScheme_Valid :
    ArthmeticCollatzScheme.Valid ArthmeticCollatzScheme.spec where
  ok_one := by decide
  ok_even z vr := by
    rintro hne hev rfl
    have hn1 : (z : ℕ) ≠ 1 := by simpa using hne
    have := z.pos
    apply PNat.coe_injective
    simp only [ArthmeticCollatzScheme, ArthmeticCollatzScheme.spec]
    push_cast [Nat.toPNat'_coe]
    split_ifs <;> omega
  ok_odd z vr := by
    rintro hne hev rfl
    have := z.pos
    apply PNat.coe_injective
    simp only [ArthmeticCollatzScheme, ArthmeticCollatzScheme.spec]
    push_cast [Nat.toPNat'_coe]
    split_ifs <;> omega

def testSequenceSegment (l u : Nat) (s₁ s₂ : ℕ+ → ℕ) : IO Unit := do
  for i in [l:u] do
    unless s₁ i.toPNat' = s₂ i.toPNat' do
      IO.println s!"test(s) failed at {i}"
      return
  IO.println s!"tests passed"

/-- info: tests passed -/
#guard_msgs in
#eval testSequenceSegment 1 50 ArthmeticCollatzScheme.toFun (extend ArthmeticCollatzScheme.spec)

example (Hc : CollatzConjecture) :
    ArthmeticCollatzScheme.toFun = extend ArthmeticCollatzScheme.spec :=
  (ArthmeticCollatzScheme.toFun_eq_extend_iff_collatz ArthmeticCollatzScheme_Valid).mpr Hc

end
