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
  | store (e : Exp) (n : ℤ)

inductive State (α : Type*) where
  | eval (e : Exp) (n : ℤ) (K : List (Frame α))
  | ret (v : α) (K : List (Frame α))
  | done (v : α)

abbrev Cache (α : Type*) := Std.HashMap (Exp × ℤ) α

variable {α : Type*} [Denotable α] (body : Exp)

def step : State α × Cache α → State α × Cache α
  | (.eval (.Add e₁ e₂) n K, c) => (.eval e₁ n (.add₁ e₂ n :: K), c)
  | (.eval (.Neg e) n K, c) => (.eval e n (.neg :: K), c)
  | (.eval (.Mul e₁ e₂) n K, c) => (.eval e₁ n (.mul₁ e₂ n :: K), c)
  | (.eval (.OfRat q) _ K, c) => (.ret (Denotable.ofRat q) K, c)
  | (.eval (.ToThePowerOf e f) n K, c) => (.eval e n (.pow (f.eval n).toNat :: K), c)
  | (.eval (.Sqrt e) n K, c) => (.eval e n (.sqrt :: K), c)
  | (.eval (.Cubert e) n K, c) => (.eval e n (.cbrt :: K), c)
  | (.eval (.Bpos enn eneg) n K, c) => (if 0 ≤ n then .eval enn n K else .eval eneg n K, c)
  | (.eval (.Beven eeven eodd) n K, c) =>
    (if n % 2 = 0 then .eval eeven n K else .eval eodd n K, c)
  | (.eval .φ _ K, c) => (.ret Denotable.φ K, c)
  | (.eval (.Recurse f) n K, c) => (.eval body (f.eval n) K, c)
  | (.eval (.Share e) n K, c) =>
    match c[(e, n)]? with
    | some v => (.ret v K, c)
    | none => (.eval e n (.store e n :: K), c)
  | (.ret v [], c) => (.done v, c)
  | (.ret v (.add₁ e n :: K), c) => (.eval e n (.add₂ v :: K), c)
  | (.ret v (.add₂ v₁ :: K), c) => (.ret (v₁ + v) K, c)
  | (.ret v (.mul₁ e n :: K), c) => (.eval e n (.mul₂ v :: K), c)
  | (.ret v (.mul₂ v₁ :: K), c) => (.ret (v₁ * v) K, c)
  | (.ret v (.neg :: K), c) => (.ret (-v) K, c)
  | (.ret v (.pow m :: K), c) => (.ret (v ^ m) K, c)
  | (.ret v (.sqrt :: K), c) => (.ret (Denotable.sqrt v) K, c)
  | (.ret v (.cbrt :: K), c) => (.ret (Denotable.cbrt v) K, c)
  | (.ret v (.store e n :: K), c) =>
    (.ret (Denotable.memo v) K, c.insert (e, n) (Denotable.memo v))
  | (.done v, c) => (.done v, c)

abbrev Steps : State α × Cache α → State α × Cache α → Prop :=
  ReflTransGen fun p p' => step body p = p'

def run (p : State α × Cache α) : Option (α × Cache α) :=
  match p with
  | (.done v, c) => some (v, c)
  | p => run (step body p)
partial_fixpoint

def frameM : Frame α → α → Option α
  | .add₁ e n, v => (denote body e n).bind fun v₂ => some (v + v₂)
  | .add₂ v₁, v => some (v₁ + v)
  | .mul₁ e n, v => (denote body e n).bind fun v₂ => some (v * v₂)
  | .mul₂ v₁, v => some (v₁ * v)
  | .neg, v => some (-v)
  | .pow m, v => some (v ^ m)
  | .sqrt, v => some (Denotable.sqrt v)
  | .cbrt, v => some (Denotable.cbrt v)
  | .store _ _, v => some (Denotable.memo v)

def denoteK : List (Frame α) → α → Option α
  | [], v => some v
  | f :: K, v => (frameM body f v).bind (denoteK K)

def denoteS : State α → Option α
  | .eval e n K => (denote body e n).bind (denoteK body K)
  | .ret v K => denoteK body K v
  | .done v => some v

def FrameOK : Option α → Frame α → Prop
  | m, .store e n => m = denote body e n
  | _, _ => True

def GoodK : Option α → List (Frame α) → Prop
  | _, [] => True
  | m, f :: K => FrameOK body m f ∧ GoodK (m.bind fun v => frameM body f v) K

def Inv : State α → Prop
  | .eval e n K => GoodK body (denote body e n) K
  | .ret v K => GoodK body (some v) K
  | .done _ => True

def Valid (c : Cache α) : Prop :=
  ∀ e n v, c[(e, n)]? = some v → denote body (.Share e) n = some v

theorem valid_empty : Valid body (∅ : Cache α) := by
  intro e n v h
  simp at h

theorem Valid.insert {c : Cache α} (hc : Valid body c) {e : Exp} {n : ℤ} {v : α}
    (h : denote body (.Share e) n = some v) : Valid body (c.insert (e, n) v) := by
  intro e' n' v' h'
  rw [Std.HashMap.getElem?_insert] at h'
  split at h'
  · next heq =>
    simp only [beq_iff_eq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    cases h'
    exact h
  · exact hc _ _ _ h'

theorem step_preserves (p : State α × Cache α) (hc : Valid body p.2) (hs : Inv body p.1) :
    Valid body (step body p).2 ∧ Inv body (step body p).1 ∧
      denoteS body (step body p).1 = denoteS body p.1 := by
  obtain ⟨s, c⟩ := p
  rcases s with ⟨e, n, K⟩ | ⟨v, _ | ⟨f, K⟩⟩ | v
  · cases e
    case Share e =>
      rcases hce : c[(e, n)]? with _ | w
      · simp_all [step, Inv, GoodK, FrameOK, frameM, denoteS, denoteK, Option.bind_assoc]
      · have hw := hc _ _ _ hce
        simp_all [step, Inv, denoteS]
    case Bpos =>
      rcases le_or_gt 0 n with h | h
      · simp_all [step, Inv, denoteS]
      · simp_all [step, Inv, denoteS, not_le.mpr h]
    case Beven =>
      rcases n.emod_two_eq_zero_or_one with h | h
      · simp_all [step, Inv, denoteS]
      · simp_all [step, Inv, denoteS]
    all_goals simp_all [step, Inv, GoodK, FrameOK, frameM, denoteS, denoteK, Option.bind_assoc]
  · simp_all [step, Inv, denoteS, denoteK]
  · cases f
    case store e n =>
      simp only [Inv, GoodK, FrameOK, frameM, Option.bind_some] at hs
      exact ⟨hc.insert body (by simp [← hs.1]), hs.2, by simp [step, denoteS, denoteK, frameM]⟩
    all_goals simp_all [step, Inv, GoodK, FrameOK, frameM, denoteS, denoteK, Option.bind_assoc]
  · exact ⟨hc, hs, rfl⟩

theorem steps_preserves {p p' : State α × Cache α} (h : Steps body p p') (hc : Valid body p.2)
    (hs : Inv body p.1) :
    Valid body p'.2 ∧ Inv body p'.1 ∧ denoteS body p'.1 = denoteS body p.1 := by
  induction h with
  | refl => exact ⟨hc, hs, rfl⟩
  | tail _ hst ih =>
    obtain ⟨hc', hs', he⟩ := ih
    subst hst
    obtain ⟨h₁, h₂, h₃⟩ := step_preserves body _ hc' hs'
    exact ⟨h₁, h₂, h₃.trans he⟩

theorem steps_of_denote {e : Exp} {n : ℤ} {v : α} (h : denote body e n = some v)
    (K : List (Frame α)) {c : Cache α} (hc : Valid body c) :
    ∃ c', Valid body c' ∧ Steps body (.eval e n K, c) (.ret v K, c') := by
  suffices H : ∀ e n v, denote body e n = some v → denote body e n = some v ∧
      ∀ (K : List (Frame α)) (c : Cache α), Valid body c →
        ∃ c', Valid body c' ∧ Steps body (.eval e n K, c) (.ret v K, c') from
    (H e n v h).2 K c hc
  apply denote.partial_correctness
  intro d IH e n v h
  cases e with
  | Add e₁ e₂ | Mul e₁ e₂ =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨v₁, h₁, v₂, h₂, rfl⟩ := h
    obtain ⟨hd₁, M₁⟩ := IH _ _ _ h₁
    obtain ⟨hd₂, M₂⟩ := IH _ _ _ h₂
    refine ⟨by simp [hd₁, hd₂], fun K c hc => ?_⟩
    obtain ⟨c₁, hc₁, s₁⟩ := M₁ _ c hc
    obtain ⟨c₂, hc₂, s₂⟩ := M₂ _ c₁ hc₁
    exact ⟨c₂, hc₂, .head rfl <| s₁.trans <| .head rfl <| s₂.tail rfl⟩
  | Neg e | ToThePowerOf e _ | Sqrt e | Cubert e =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨v₁, h₁, rfl⟩ := h
    obtain ⟨hd₁, M₁⟩ := IH _ _ _ h₁
    refine ⟨by simp [hd₁], fun K c hc => ?_⟩
    obtain ⟨c₁, hc₁, s₁⟩ := M₁ _ c hc
    exact ⟨c₁, hc₁, .head rfl <| s₁.tail rfl⟩
  | OfRat _ | φ =>
    simp only [pure, Option.some.injEq] at h
    subst h
    exact ⟨by simp, fun K c hc => ⟨c, hc, .single rfl⟩⟩
  | Bpos enn eneg =>
    dsimp only at h
    split_ifs at h with hn
    · obtain ⟨hd, M⟩ := IH _ _ _ h
      refine ⟨by rwa [denote_bpos_of_nonneg _ _ _ _ hn], fun K c hc => ?_⟩
      obtain ⟨c', hc', s'⟩ := M K c hc
      exact ⟨c', hc', .head (by simp [step, hn]) s'⟩
    · obtain ⟨hd, M⟩ := IH _ _ _ h
      refine ⟨by rwa [denote_bpos_of_neg _ _ _ _ (by omega)], fun K c hc => ?_⟩
      obtain ⟨c', hc', s'⟩ := M K c hc
      exact ⟨c', hc', .head (by simp [step, hn]) s'⟩
  | Beven eeven eodd =>
    dsimp only at h
    split_ifs at h with hn
    · obtain ⟨hd, M⟩ := IH _ _ _ h
      refine ⟨by rwa [denote_beven_of_even _ _ _ _ hn], fun K c hc => ?_⟩
      obtain ⟨c', hc', s'⟩ := M K c hc
      exact ⟨c', hc', .head (by simp [step, hn]) s'⟩
    · obtain ⟨hd, M⟩ := IH _ _ _ h
      refine ⟨by rwa [denote_beven_of_odd _ _ _ _ (by omega)], fun K c hc => ?_⟩
      obtain ⟨c', hc', s'⟩ := M K c hc
      exact ⟨c', hc', .head (by simp [step, hn]) s'⟩
  | Recurse f =>
    obtain ⟨hd, M⟩ := IH _ _ _ h
    refine ⟨by rwa [denote_recurse], fun K c hc => ?_⟩
    obtain ⟨c', hc', s'⟩ := M K c hc
    exact ⟨c', hc', .head rfl s'⟩
  | Share e =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨v₁, h₁, rfl⟩ := h
    obtain ⟨hd₁, M⟩ := IH _ _ _ h₁
    have hd : denote body (.Share e) n = some (Denotable.memo v₁) := by simp [hd₁]
    refine ⟨hd, fun K c hc => ?_⟩
    rcases hce : c[(e, n)]? with _ | w
    · obtain ⟨c', hc', s'⟩ := M (.store e n :: K) c hc
      exact ⟨_, hc'.insert body hd, .head (by simp [step, hce]) (s'.tail rfl)⟩
    · have hw : w = Denotable.memo v₁ := Option.some.inj ((hc _ _ _ hce).symm.trans hd)
      exact ⟨c, hc, .single (by simp [step, hce, hw])⟩

theorem steps_done_iff {n : ℤ} {v : α} {c : Cache α} (hc : Valid body c) :
    (∃ c', Steps body (.eval body n [], c) (.done v, c')) ↔ denote body body n = some v := by
  constructor
  · rintro ⟨c', h⟩
    have := (steps_preserves body h hc (by simp [Inv, GoodK])).2.2
    simpa [denoteS, denoteK] using this.symm
  · intro h
    obtain ⟨c', -, s⟩ := steps_of_denote body h [] hc
    exact ⟨c', s.tail rfl⟩

theorem run_step : ∀ p : State α × Cache α, run body p = run body (step body p)
  | (.done _, _) => rfl
  | (.eval .., _) | (.ret .., _) => by rw [run.eq_def]

theorem run_eq_some_iff {p : State α × Cache α} {r : α × Cache α} :
    run body p = some r ↔ Steps body p (.done r.1, r.2) := by
  constructor
  · revert p r
    apply run.partial_correctness
    intro f IH p r h
    split at h
    · cases h
      exact .refl
    · exact .head rfl (IH _ _ h)
  · intro h
    induction h using ReflTransGen.head_induction_on with
    | refl => rw [run]
    | head hst _ ih => rw [run_step, hst, ih]

theorem run_sound {c : Cache α} (hc : Valid body c) {n : ℤ} {v : α} {c' : Cache α}
    (h : run body (.eval body n [], c) = some (v, c')) :
    denote body body n = some v ∧ Valid body c' := by
  have hs := (run_eq_some_iff body).mp h
  exact ⟨(steps_done_iff body hc).mp ⟨c', hs⟩,
    (steps_preserves body hs hc (by simp [Inv, GoodK])).1⟩

theorem run_eq_some_iff_denote {n : ℤ} {v : α} :
    (run body (.eval body n [], (∅ : Cache α))).map Prod.fst = some v ↔
      denote body body n = some v := by
  rw [← steps_done_iff body (valid_empty body), Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨v', c'⟩, h, rfl⟩
    exact ⟨c', (run_eq_some_iff body).mp h⟩
  · rintro ⟨c', h⟩
    exact ⟨(v, c'), (run_eq_some_iff body).mpr h, rfl⟩

end Machine

def fibMachineWith (c : Machine.Cache CReal) (n : ℕ) : Option (CReal × Machine.Cache CReal) :=
  Machine.run fibProg (.eval fibProg ((n : ℤ) - 2) [], c)

def fibMachine (n : ℕ) : Option CReal := (fibMachineWith ∅ n).map Prod.fst

def fibMachineRoundWith (c : Machine.Cache CReal) (n : ℕ) : Option (ℤ × Machine.Cache CReal) :=
  (fibMachineWith c n).map fun (a, c') => (round (a.approx 2), c')

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

theorem fibMachineWith_tracks {c c' : Machine.Cache CReal} (hc : Machine.Valid fibProg c)
    {n : ℕ} {a : CReal} (h : fibMachineWith c n = some (a, c')) :
    a.Tracks (Nat.fib n) ∧ Machine.Valid fibProg c' := by
  obtain ⟨hd, hc'⟩ := Machine.run_sound _ hc h
  obtain ⟨x, hx, ht⟩ := CReal.tracks_rel.denote hd
  exact ⟨by rwa [fibRun_eq_some (n := n) hx] at ht, hc'⟩

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
