import CollatzRecursionSchemes.Machine

def worker (budgetNs : Nat) : IO UInt32 := do
  let stdout ← IO.getStdout
  let start ← IO.monoNanosNow
  let mut n := 0
  repeat
    if (fibMachineRound n).isNone then
      return 1
    if (← IO.monoNanosNow) - start > budgetNs then
      return 0
    stdout.putStrLn (toString n)
    stdout.flush
    n := n + 1
  return 0

def trial (budgetMs : Nat) : IO Nat := do
  let child ← IO.Process.spawn {
    cmd := (← IO.appPath).toString
    args := #["worker", toString budgetMs]
    stdout := .piped }
  let deadline := (← IO.monoMsNow) + budgetMs + 100
  let mut code ← child.tryWait
  while code.isNone && (← IO.monoMsNow) < deadline do
    IO.sleep 10
    code ← child.tryWait
  if code.isNone then
    child.kill
    let _ ← child.wait
  else if code != some 0 then
    throw <| IO.userError "worker failed"
  let out ← child.stdout.readToEnd
  return ((out.splitOn "\n").filterMap String.toNat?).foldl max 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["worker", budgetMs] => worker (budgetMs.toNat! * 1000000)
  | _ =>
    let (budgetMs, trials) := match args with
      | [b, t] => (b.toNat!, t.toNat!)
      | [b] => (b.toNat!, 5)
      | _ => (1000, 5)
    let _ ← trial budgetMs
    let mut scores := #[]
    for i in [0:trials] do
      let s ← trial budgetMs
      IO.println s!"trial {i + 1}: {s}"
      scores := scores.push s
    IO.println s!"median: {(scores.qsort (· < ·))[trials / 2]!}"
    return 0
