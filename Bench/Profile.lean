import CollatzRecursionSchemes.Machine

structure Stats where
  queries : Nat := 0
  maxPrec : Nat := 0
  maxBits : Nat := 0

instance : Add Stats where
  add a b := ⟨a.queries + b.queries, max a.maxPrec b.maxPrec, max a.maxBits b.maxBits⟩

def tick (k : ℕ) (q : ℚ) : Stats := ⟨1, k, q.num.natAbs.log2 + q.den.log2⟩

structure CRealP where
  approx : ℕ → ℚ × Stats
  ctor : Stats := {}

namespace CRealP

def ofRat (q : ℚ) : CRealP := ⟨fun k => (q, tick k q), {}⟩

def neg (a : CRealP) : CRealP :=
  ⟨fun k => let (x, s) := a.approx k; (-x, s + tick k (-x)), a.ctor⟩

def add (a b : CRealP) : CRealP :=
  ⟨fun k =>
    let (x, s₁) := a.approx (k + 1)
    let (y, s₂) := b.approx (k + 1)
    (x + y, s₁ + s₂ + tick k (x + y)), a.ctor + b.ctor⟩

def bound (a : CRealP) : ℕ × Stats :=
  let (x, s) := a.approx 0
  (⌈|x|⌉₊ + 1, s)

def mul (a b : CRealP) : CRealP :=
  let (ba, sa) := a.bound
  let (bb, sb) := b.bound
  let s := (ba + bb).size
  ⟨fun k =>
    let (x, s₁) := a.approx (k + s)
    let (y, s₂) := b.approx (k + s)
    (x * y, s₁ + s₂ + tick k (x * y)), a.ctor + b.ctor + sa + sb⟩

def pow (a : CRealP) (m : ℕ) : CRealP :=
  let (ba, sa) := a.bound
  let s := (m * (ba + 1) ^ (m - 1)).size
  ⟨fun k =>
    let (x, s₁) := a.approx (k + s)
    (x ^ m, s₁ + tick k (x ^ m)), a.ctor + sa⟩

def probe (a : CRealP) (d : ℕ) (ok : ℕ → ℚ → Bool) : Option ℕ × Stats :=
  go CReal.probes {}
where
  go : List ℕ → Stats → Option ℕ × Stats
    | [], s => (none, s)
    | i :: is, s =>
      let (x, s') := a.approx (d * i)
      if ok i x then (some i, s + s') else go is (s + s')

def sqrt (a : CRealP) : CRealP :=
  let (p, sp) := a.probe 2 fun i x => 2 / 4 ^ i ≤ x
  let prec := match p with
    | some i => fun k => k + i + 1
    | none => fun k => 2 * k + 2
  ⟨fun k =>
    let (x, s) := a.approx (prec k)
    let r := CReal.sqrtApprox x (k + 1)
    (r, s + tick k r), a.ctor + sp⟩

def cbrt (a : CRealP) : CRealP :=
  let (p, sp) := a.probe 3 fun i x => 2 / 8 ^ i ≤ |x|
  let prec := match p with
    | some i => fun k => k + 2 * i + 2
    | none => fun k => 3 * k + 5
  ⟨fun k =>
    let (x, s) := a.approx (prec k)
    let r := CReal.cbrtApprox x (k + 1)
    (r, s + tick k r), a.ctor + sp⟩

def φ : CRealP := mul (ofRat (1 / 2)) (add (ofRat 1) (sqrt (ofRat 5)))

def memo (a : CRealP) : CRealP :=
  let t : Array (Thunk (ℚ × Stats)) := Array.ofFn (n := CReal.memoSize) fun i =>
    Thunk.mk fun _ => a.approx (CReal.memoStep * (i + 1))
  ⟨fun k => match t[k / CReal.memoStep]? with
    | some th => th.get
    | none => a.approx k, a.ctor⟩

instance : Denotable CRealP where
  add := add
  neg := neg
  mul := mul
  pow := pow
  ofRat := ofRat
  sqrt := sqrt
  cbrt := cbrt
  φ := φ
  memo := memo

end CRealP

partial def runCount (p : Machine.State CRealP × Machine.Cache CRealP) (steps : ℕ := 0) :
    Option CRealP × ℕ :=
  match p with
  | (.done v, _) => (some v, steps)
  | p => runCount (Machine.step fibProg p) (steps + 1)

partial def collatzCounts (n : ℕ) (len odd : ℕ := 0) : ℕ × ℕ :=
  if n ≤ 1 then (len, odd)
  else collatzCounts (collatz n) (len + 1) (if n % 2 = 1 then odd + 1 else odd)

def row (n : ℕ) : IO Unit := do
  let t₀ ← IO.monoNanosNow
  if (fibMachineRound n).isNone then
    throw <| IO.userError s!"machine failed at n = {n}"
  let ms := ((← IO.monoNanosNow) - t₀) / 1000000
  let (len, odd) := collatzCounts n
  let (some v, steps) := runCount (.eval fibProg ((n : ℤ) - 2) [], ∅)
    | throw <| IO.userError s!"machine failed at n = {n}"
  let (_, s) := v.approx 2
  let total := v.ctor + s
  IO.println s!"{n}\t{len}\t{odd}\t{steps}\t{total.queries}\t{total.maxPrec}\t{total.maxBits}\t{ms}"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let maxN := match args with
    | [m] => m.toNat!
    | _ => 8
  IO.println "n\tpath\todd\tsteps\tqueries\tmaxPrec\tmaxBits\tms"
  for n in [0:maxN + 1] do
    row n
