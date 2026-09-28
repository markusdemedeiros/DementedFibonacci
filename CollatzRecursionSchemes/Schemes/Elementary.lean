module

public import Mathlib.Data.PNat.Basic
public import CollatzRecursionSchemes.Scheme
public meta import Mathlib.Data.PNat.Defs
public meta import CollatzRecursionSchemes.Scheme

set_option linter.style.header false

@[expose] public section

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
def ElementaryScheme : CollatzRecursionScheme ℕ+ where
  one := 3
  odd _n vrec := ((vrec : ℕ) / 3).toPNat'
  even n vrec := n + vrec

def ElementaryScheme.spec (z : ℕ+) : ℕ+ := 2 * z + 1

theorem ElementaryScheme.valid : ElementaryScheme.Valid ElementaryScheme.spec where
  ok_one := by decide
  ok_even z vr := by
    rintro hne hev rfl
    simp only [ElementaryScheme, ElementaryScheme.spec]
    apply PNat.coe_injective
    push_cast [Nat.toPNat'_coe]
    grind [z.pos]
  ok_odd z vr := by
    rintro hne hev rfl
    apply PNat.coe_injective
    simp only [ElementaryScheme, ElementaryScheme.spec]
    push_cast [Nat.toPNat'_coe]
    grind

def testSequenceSegment [DecidableEq β] (l u : Nat) (s₁ s₂ : ℕ+ → β) : IO Unit := do
  for i in [l:u] do
    unless s₁ i.toPNat' = s₂ i.toPNat' do
      IO.println s!"test(s) failed at {i}"
      return
  IO.println s!"tests passed"

set_option linter.style.whitespace false in
/-- info: tests passed -/
#guard_msgs in #eval testSequenceSegment 1 50 ElementaryScheme.toFun (some ∘ ElementaryScheme.spec)

example (Hc : CollatzConjecture) : ElementaryScheme.toFun = some ∘ ElementaryScheme.spec :=
  (ElementaryScheme.toFun_eq_spec_iff_collatz ElementaryScheme.valid).mpr Hc

end
