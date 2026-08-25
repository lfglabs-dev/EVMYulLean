import EvmYul.EVM.Semantics

namespace EvmYul.EVM.Proof

/-- A decoded EVM instruction together with its optional `PUSH` argument. -/
abbrev Instruction := Operation .EVM × Option (UInt256 × Nat)

/--
The graph of the executable `EvmYul.EVM.step`.  The result is an `Except`, so
exceptional executions are represented without inventing a post-state.  This
is deliberately not the generic `EvmYul.Semantics.step`.
-/
def Step (fuel gasCost : Nat) (instr : Instruction) (pre : EVM.State)
    (result : Except EVM.ExecutionException EVM.State) : Prop :=
  EvmYul.EVM.step fuel gasCost (some instr) pre = result

/-- The successful-state projection of `Step`. -/
abbrev StepOk (fuel gasCost : Nat) (instr : Instruction)
    (pre post : EVM.State) : Prop :=
  Step fuel gasCost instr pre (.ok post)

theorem Step.deterministic_ok {fuel gasCost : Nat} {instr : Instruction}
    {pre post₁ post₂ : EVM.State}
    (h₁ : StepOk fuel gasCost instr pre post₁)
    (h₂ : StepOk fuel gasCost instr pre post₂) : post₁ = post₂ := by
  simp only [StepOk, Step] at h₁ h₂
  rw [h₁] at h₂
  exact Except.ok.inj h₂

/-- Exactly `n` successful steps, labeled by exactly `n` decoded instructions. -/
inductive Runs (fuel gasCost : Nat) : Nat → List Instruction → EVM.State → EVM.State → Prop
  | zero (state) : Runs fuel gasCost 0 [] state state
  | succ (step : StepOk fuel gasCost instr pre mid)
      (rest : Runs fuel gasCost n instrs mid post) :
      Runs fuel gasCost (n + 1) (instr :: instrs) pre post

@[simp] theorem Runs.zero_iff {fuel gasCost : Nat} {instrs : List Instruction}
    {pre post : EVM.State} :
    Runs fuel gasCost 0 instrs pre post ↔ instrs = [] ∧ pre = post := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .zero _

theorem Runs.one {fuel gasCost : Nat} {instr : Instruction} {pre post : EVM.State}
    (h : StepOk fuel gasCost instr pre post) :
    Runs fuel gasCost 1 [instr] pre post := by
  simpa using Runs.succ h (Runs.zero post)

theorem Runs.succ_iff {fuel gasCost n : Nat} {instr : Instruction}
    {instrs : List Instruction} {pre post : EVM.State} :
    Runs fuel gasCost (n + 1) (instr :: instrs) pre post ↔
      ∃ mid, StepOk fuel gasCost instr pre mid ∧
        Runs fuel gasCost n instrs mid post := by
  constructor
  · intro h
    cases h with
    | succ step rest => exact ⟨_, step, rest⟩
  · rintro ⟨mid, step, rest⟩
    exact .succ step rest

theorem Runs.trans {fuel gasCost m n : Nat} {xs ys : List Instruction}
    {s₀ s₁ s₂ : EVM.State}
    (h₁ : Runs fuel gasCost m xs s₀ s₁)
    (h₂ : Runs fuel gasCost n ys s₁ s₂) :
    Runs fuel gasCost (m + n) (xs ++ ys) s₀ s₂ := by
  induction h₁ with
  | zero => simpa using h₂
  | @succ k instr instrs pre mid post step rest ih =>
      simpa [Nat.add_assoc] using Runs.succ step (ih h₂)

/-- Execute a fixed list of decoded instructions through `EvmYul.EVM.step`. -/
def runN (fuel gasCost : Nat) : List Instruction → EVM.State →
    Except EVM.ExecutionException EVM.State
  | [], state => .ok state
  | instr :: instrs, state => do
      let state' ← EvmYul.EVM.step fuel gasCost (some instr) state
      runN fuel gasCost instrs state'

theorem runN_sound {fuel gasCost : Nat} {instrs : List Instruction}
    {pre post : EVM.State} (h : runN fuel gasCost instrs pre = .ok post) :
    Runs fuel gasCost instrs.length instrs pre post := by
  induction instrs generalizing pre with
  | nil =>
      simp only [runN, Except.ok.injEq] at h
      subst post
      exact .zero pre
  | cons instr instrs ih =>
      simp only [runN] at h
      split at h <;> rename_i result hstep
      · contradiction
      · exact .succ hstep (ih h)

theorem runN_complete {fuel gasCost n : Nat} {instrs : List Instruction}
    {pre post : EVM.State} (h : Runs fuel gasCost n instrs pre post) :
    runN fuel gasCost instrs pre = .ok post := by
  induction h with
  | zero => rfl
  | succ step _ ih =>
      simp only [runN, step, ih]

theorem runN_iff_runs {fuel gasCost : Nat} {instrs : List Instruction}
    {pre post : EVM.State} :
    runN fuel gasCost instrs pre = .ok post ↔
      Runs fuel gasCost instrs.length instrs pre post := by
  constructor
  · exact runN_sound
  · exact runN_complete

/- A straight-line fixture that crosses a conditional-branch instruction and
   ends at `RETURN`.  The zero condition makes `JUMPI` fall through to the
   `JUMPDEST`; the final two `PUSH0`s supply RETURN's offset and size. -/
private def fixtureCode : List Instruction :=
  [ (.Push .PUSH1, some (0, 1))
  , (.Push .PUSH1, some (5, 1))
  , (.JUMPI, none)
  , (.JUMPDEST, none)
  , (.Push .PUSH0, none)
  , (.Push .PUSH0, none)
  , (.RETURN, none)
  ]

private def fixtureFinal : EVM.State :=
  { (default : EVM.State) with pc := 8, execLength := 7 }

theorem fixture_runN : runN 1 0 fixtureCode default = .ok fixtureFinal := by
  rfl

/-- The fixture's proof uses the reusable soundness theorem, not a decision procedure. -/
theorem fixture_runs : Runs 1 0 7 fixtureCode default fixtureFinal := by
  exact runN_sound fixture_runN

end EvmYul.EVM.Proof
