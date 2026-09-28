module

public import CollatzRecursionSchemes.CReal
public import CollatzRecursionSchemes.Fib
meta import CollatzRecursionSchemes.CReal
meta import CollatzRecursionSchemes.Fib

set_option linter.style.header false

@[expose] public section

open Relation

namespace Machine

inductive Frame (α : Type*) where
  | add₁ (e : Exp) (n : ℤ)
  | add₂ (v : α)
  | mul₁ (e : Exp) (n : ℤ)
  | mul₂ (v : α)
  | neg
  | pow (m : ℕ)
  | sqrt
  | cbrt

inductive State (α : Type*) where
  | eval (e : Exp) (n : ℤ) (K : List (Frame α))
  | ret (v : α) (K : List (Frame α))
  | done (v : α)

variable {α : Type*} [Denotable α] (body : Exp)

def step : State α → State α
  | .eval (.Add e₁ e₂) n K => .eval e₁ n (.add₁ e₂ n :: K)
  | .eval (.Neg e) n K => .eval e n (.neg :: K)
  | .eval (.Mul e₁ e₂) n K => .eval e₁ n (.mul₁ e₂ n :: K)
  | .eval (.OfRat q) _ K => .ret (Denotable.ofRat q) K
  | .eval (.ToThePowerOf e f) n K => .eval e n (.pow (f n) :: K)
  | .eval (.Sqrt e) n K => .eval e n (.sqrt :: K)
  | .eval (.Cubert e) n K => .eval e n (.cbrt :: K)
  | .eval (.Bpos enn eneg) n K => if 0 ≤ n then .eval enn n K else .eval eneg n K
  | .eval (.Beven eeven eodd) n K => if n % 2 = 0 then .eval eeven n K else .eval eodd n K
  | .eval .φ _ K => .ret Denotable.φ K
  | .eval (.Recurse f) n K => .eval body (f n) K
  | .ret v [] => .done v
  | .ret v (.add₁ e n :: K) => .eval e n (.add₂ v :: K)
  | .ret v (.add₂ v₁ :: K) => .ret (v₁ + v) K
  | .ret v (.mul₁ e n :: K) => .eval e n (.mul₂ v :: K)
  | .ret v (.mul₂ v₁ :: K) => .ret (v₁ * v) K
  | .ret v (.neg :: K) => .ret (-v) K
  | .ret v (.pow m :: K) => .ret (v ^ m) K
  | .ret v (.sqrt :: K) => .ret (Denotable.sqrt v) K
  | .ret v (.cbrt :: K) => .ret (Denotable.cbrt v) K
  | .done v => .done v

abbrev Steps : State α → State α → Prop := ReflTransGen fun s s' => step body s = s'

def run (s : State α) : Option α :=
  match s with
  | .done v => some v
  | s => run (step body s)
partial_fixpoint

def denoteK : List (Frame α) → α → Option α
  | [], v => some v
  | .add₁ e n :: K, v => (denote body e n).bind fun v₂ => denoteK K (v + v₂)
  | .add₂ v₁ :: K, v => denoteK K (v₁ + v)
  | .mul₁ e n :: K, v => (denote body e n).bind fun v₂ => denoteK K (v * v₂)
  | .mul₂ v₁ :: K, v => denoteK K (v₁ * v)
  | .neg :: K, v => denoteK K (-v)
  | .pow m :: K, v => denoteK K (v ^ m)
  | .sqrt :: K, v => denoteK K (Denotable.sqrt v)
  | .cbrt :: K, v => denoteK K (Denotable.cbrt v)

def denoteS : State α → Option α
  | .eval e n K => (denote body e n).bind (denoteK body K)
  | .ret v K => denoteK body K v
  | .done v => some v

theorem denoteS_step (s : State α) : denoteS body (step body s) = denoteS body s := by
  rcases s with ⟨e, n, K⟩ | ⟨v, _ | ⟨f, K⟩⟩ | v
  · cases e
    case Bpos =>
      rcases le_or_gt 0 n with h | h
      · simp [step, denoteS, h]
      · simp [step, denoteS, h, not_le.mpr h]
    case Beven => rcases n.emod_two_eq_zero_or_one with h | h <;> simp [step, denoteS, h]
    all_goals simp [step, denoteS, denoteK, Option.bind_assoc]
  · simp [step, denoteS, denoteK]
  · cases f <;> simp [step, denoteS, denoteK]
  · rfl

theorem denoteS_eq_of_steps {s s' : State α} (h : Steps body s s') :
    denoteS body s = denoteS body s' := by
  induction h with
  | refl => rfl
  | tail _ hst ih => rw [ih, ← hst, denoteS_step]

theorem steps_of_denote {e : Exp} {n : ℤ} {v : α} (h : denote body e n = some v)
    (K : List (Frame α)) : Steps body (.eval e n K) (.ret v K) := by
  revert e n v h K
  apply denote.partial_correctness
  intro d IH e n v h K
  cases e with
  | Add e₁ e₂ | Mul e₁ e₂ =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨v₁, h₁, v₂, h₂, rfl⟩ := h
    exact .head rfl <| (IH _ _ _ h₁ _).trans <| .head rfl <| (IH _ _ _ h₂ _).tail rfl
  | Neg e | ToThePowerOf e _ | Sqrt e | Cubert e =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨v₁, h₁, rfl⟩ := h
    exact .head rfl <| (IH _ _ _ h₁ _).tail rfl
  | OfRat _ | φ =>
    simp only [pure, Option.some.injEq] at h
    exact h ▸ .single rfl
  | Bpos e₁ e₂ | Beven e₁ e₂ =>
    dsimp only at h
    split_ifs at h with hn <;> exact .head (by simp [step, hn]) (IH _ _ _ h _)
  | Recurse f => exact .head rfl (IH _ _ _ h _)

theorem steps_done_iff {n : ℤ} {v : α} :
    Steps body (.eval body n []) (.done v) ↔ denote body body n = some v :=
  ⟨fun h => by simpa [denoteS, denoteK] using denoteS_eq_of_steps body h,
    fun h => (steps_of_denote body h []).tail rfl⟩

theorem run_step : ∀ s : State α, run body s = run body (step body s)
  | .done _ => rfl
  | .eval .. | .ret .. => by rw [run.eq_def]

theorem run_eq_some_iff {s : State α} {v : α} : run body s = some v ↔ Steps body s (.done v) := by
  constructor
  · revert s v
    apply run.partial_correctness
    intro r IH s v h
    split at h
    · exact Option.some.inj h ▸ .refl
    · exact .head rfl (IH _ _ h)
  · intro h
    induction h using ReflTransGen.head_induction_on with
    | refl => rw [run]
    | head hst _ ih => rw [run_step, hst, ih]

theorem run_eq_some_iff_denote {n : ℤ} {v : α} :
    run body (.eval body n []) = some v ↔ denote body body n = some v :=
  (run_eq_some_iff body).trans (steps_done_iff body)

end Machine

def fibMachine (n : ℕ) : Option CReal := Machine.run fibProg (.eval fibProg ((n : ℤ) - 2) [])

def fibMachineRound (n : ℕ) : Option ℤ := (fibMachine n).map fun a => round (a.approx 2)

theorem fibRun_eq_some {n : ℕ} {x : ℝ} (h : fibRun n = some x) : x = Nat.fib n := by
  rcases n with _ | n
  · simp_all [fibRun_zero]
  · rw [show n + 1 = (n.succPNat : ℕ) from rfl, fibRun_eq_toFun] at h
    exact Real.fibScheme.correct _ Real.fibScheme_valid _ _ h

theorem fibMachine_tracks {n : ℕ} {a : CReal} (h : fibMachine n = some a) :
    a.Tracks (Nat.fib n) := by
  obtain ⟨x, hx, ht⟩ := CReal.tracks_rel.denote ((Machine.run_eq_some_iff_denote _).mp h)
  rwa [fibRun_eq_some (n := n) hx] at ht

theorem fibMachine_tracks_fib_iff_collatz :
    (∀ n, ∃ a, fibMachine n = some a ∧ a.Tracks (Nat.fib n)) ↔ CollatzConjecture := by
  rw [← fibRun_eq_fib_iff_collatz]
  constructor
  · intro h
    funext n
    obtain ⟨a, ha, -⟩ := h n
    obtain ⟨x, hx, -⟩ := CReal.tracks_rel.denote ((Machine.run_eq_some_iff_denote _).mp ha)
    rwa [← fibRun_eq_some (n := n) hx]
  · intro h n
    obtain ⟨a, ha, ht⟩ := CReal.tracks_rel.flip.denote (congrFun h n)
    exact ⟨a, (Machine.run_eq_some_iff_denote _).mpr ha, ht⟩

theorem round_eq_of_tracks {a : CReal} {m : ℕ} (h : a.Tracks m) : round (a.approx 2) = m := by
  have h2 := abs_sub_le_iff.mp (h 2)
  norm_num at h2
  rw [round_eq, Int.floor_eq_iff, ← Rat.cast_le (K := ℝ), ← Rat.cast_lt (K := ℝ)]
  push_cast
  exact ⟨by linarith, by linarith⟩

theorem fibMachineRound_eq_some {n : ℕ} {a : CReal} (h : fibMachine n = some a) :
    fibMachineRound n = some (Nat.fib n : ℤ) := by
  rw [fibMachineRound, h, Option.map_some, round_eq_of_tracks (fibMachine_tracks h)]

theorem fibMachineRound_eq_fib_iff_collatz :
    fibMachineRound = (fun n => some (Nat.fib n : ℤ)) ↔ CollatzConjecture := by
  rw [← fibMachine_tracks_fib_iff_collatz]
  constructor
  · intro h n
    obtain ⟨a, ha, -⟩ := Option.map_eq_some_iff.mp (congrFun h n)
    exact ⟨a, ha, fibMachine_tracks ha⟩
  · exact fun h => funext fun n => fibMachineRound_eq_some (h n).choose_spec.1

set_option linter.style.whitespace false

/-- info: some 0 -/
#guard_msgs in #eval fibMachineRound 0

/-- info: some 1 -/
#guard_msgs in #eval fibMachineRound 1

/-- info: some 1 -/
#guard_msgs in #eval fibMachineRound 2

/-- info: some 2 -/
#guard_msgs in #eval fibMachineRound 3

/-- info: some 3 -/
#guard_msgs in #eval fibMachineRound 4

/-- info: some 5 -/
#guard_msgs in #eval fibMachineRound 5

/-- info: some 8 -/
#guard_msgs in #eval fibMachineRound 6
