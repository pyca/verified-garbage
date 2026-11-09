module

public import VerifiedGarbage.TCB.Mem

/-!
# Searches over refillable random tapes

**Trusted.** The protocol a verified operation that needs an unknown amount
of randomness (a prime search, a rejection-sampled scalar) and its host share.
The operation reads a tape of random octets from its front, owns its limits
on attempts and on entropy, and returns one of three outcomes:

* `accepted`: it finished, having consumed `used` octets;
* `exhausted`: it gave up (its attempts or its entropy budget ran out), which
  more entropy cannot fix;
* `entropy`: the tape ran out. It consumed `used` octets, its state for the
  next call (what survives a refill, such as attempts left) is `state`, and the
  `available` octets left after them did not hold a whole step. It asks for a
  next tape of `requested` octets, any length `RequestValid` allows: more than
  `available`, so the step can go further, and at most the operation's budget.
  How much more is the operation's choice, not part of this protocol. The host
  discards the `used` octets, keeps the rest in order and appends fresh,
  independent random octets until the tape has `requested` (`Refill`), and
  calls it again with `state`.
  So an unfinished step (a candidate whose witnesses ran out) is run again from
  its own octets, never from new ones, and its outcome does not depend on how
  the stream was cut into tapes.

The status each outcome returns is the same for every operation: 0 for more
entropy, 1 for done, 3 for exhausted. `trace` is what the operation's timing
may depend on: each operation's contract says what goes in it.
-/

@[expose] public section

namespace VG.Spec.Entropy

/-- How a search over a tape ended: its state `σ` across a refill, and its
result `α`. -/
inductive Outcome (σ α : Type) where
  | entropy (state : σ) (available : Nat)
  | accepted (result : α)
  | exhausted
  deriving DecidableEq, Repr

/-- A search's outcome, the octets of its tape it consumed and the trace its
timing may depend on. -/
structure Result (σ α : Type) where
  outcome : Outcome σ α
  used : Nat
  trace : List Nat
  deriving DecidableEq, Repr

variable {σ α : Type}

/-- The status returned for each outcome: 0 for more entropy, 1 done,
3 exhausted. -/
def Outcome.status : Outcome σ α → Nat
  | .entropy .. => 0
  | .accepted _ => 1
  | .exhausted => 3

def Result.status (r : Result σ α) : Nat := r.outcome.status

/-- The octets left after those consumed, for more entropy, or 0. -/
def Result.available (r : Result σ α) : Nat :=
  match r.outcome with
  | .entropy _ available => available
  | _ => 0

/-- A search's result after `n` more octets were consumed before it, with
the trace `prior` before its own. -/
def Result.consume (n : Nat) (prior : List Nat) (r : Result σ α) : Result σ α :=
  { r with used := n + r.used, trace := prior ++ r.trace }

/-- A length the next tape may have when `available` octets did not hold a
whole step: more than `available`, and at most the budget `cap`. -/
def RequestValid (cap available requested : Nat) : Prop :=
  available < requested ∧ requested ≤ cap

/-- The length `requested` the host is asked for after the result `r`: one
`RequestValid` allows for more entropy, and 0 otherwise. -/
def Result.Requests (cap : Nat) (r : Result σ α) (requested : Nat) : Prop :=
  match r.outcome with
  | .entropy _ available => RequestValid cap available requested
  | _ => requested = 0

/-- The host's side: `next` is the tape `rand` after its first `used` octets,
followed by fresh octets, `requested` in all. -/
def Refill (rand : List Byte) (used requested : Nat) (next : List Byte) : Prop :=
  next.length = requested ∧ rand.drop used <+: next

end VG.Spec.Entropy
