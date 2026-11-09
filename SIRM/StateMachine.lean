/-!
# Verified State-Machine Interface

This generic interface turns local transition-preservation theorems into a
reachable-state safety theorem. A concrete RFT Network state machine must
instantiate it with the actual protocol state and all accepted transitions.
-/

namespace SIRM

/-- A deterministic-specification interface with explicit safety obligations. -/
structure VerifiedStateMachine (State : Type) where
  invariant : State → Prop
  initial : State → Prop
  step : State → State → Prop
  initial_safe : ∀ state, initial state → invariant state
  step_safe : ∀ before after, invariant before → step before after → invariant after

/-- States reachable from an initial state by zero or more allowed transitions. -/
inductive Reachable {State : Type} (machine : VerifiedStateMachine State) : State → Prop where
  | initial {state : State} : machine.initial state → Reachable machine state
  | step {before after : State} :
      Reachable machine before → machine.step before after → Reachable machine after

theorem invariant_of_reachable {State : Type}
    (machine : VerifiedStateMachine State) {state : State}
    (reachable : Reachable machine state) :
    machine.invariant state := by
  induction reachable with
  | initial hInitial =>
      exact machine.initial_safe _ hInitial
  | step _ hStep ih =>
      exact machine.step_safe _ _ ih hStep

end SIRM
