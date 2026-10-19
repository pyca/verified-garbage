module
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Spec.Ffdh.Contract


/-! # Complete FFDH generation control over refillable octet tapes

The caller supplies entropy, not retry decisions. The native controller owns
candidate-search limits and entropy budgets. On a request for more entropy,
`used` octets are discarded and the unconsumed suffix is extended to `requested`
octets. In particular an incomplete candidate is replayed with its exact prefix.
-/

@[expose] public section

namespace VG.Spec.Ffdh

open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Spec.RsaKeyGen (Rand)

/-- Finite public search bound, including a malfunctioning entropy source. -/
def parameterAttempts (bits : Nat) : Nat := bits * bits * 64

/-- A per-candidate entropy budget, independent of witness-count policy. -/
def parameterEntropy (bits : Nat) : Nat := 32769 * ((bits + 7) / 8)

/-- The next entropy request is chosen by verified code: at least twice the
octets left, and at least 512 octets per octet of p, enough for a candidate
and the 2 · 128 witnesses of its two Miller–Rabin tests even when about half
of the witness draws are rejected. A shortage discards an incomplete
candidate's work, so a request that holds a whole candidate keeps the
accepted one, by far the most expensive, from being tested again. -/
def parameterRequest (bits available : Nat) : Nat :=
  min (2 * max available (256 * ((bits + 7) / 8))) (parameterEntropy bits)

/-- Initialization returns the controller's four public words, followed by
private workspace. The first request is `parameterRequest bits 0`. All parameter
validation and policy arithmetic are native. -/
def parameterInit (bits generator : Nat) : Option (List Nat) :=
  if 512 ≤ bits && bits ≤ 8192 && (generator == 2 || generator == 5) then
    some [parameterAttempts bits, (bits + 7) / 8, parameterEntropy bits,
      512 * ((bits + 7) / 8)]
  else none

inductive ParameterSearchResult where
  | entropy (remaining requested used : Nat)
  | accepted (p used : Nat)
  | exhausted (used : Nat)

def ParameterSearchResult.used : ParameterSearchResult → Nat
  | .entropy _ _ used | .accepted _ used | .exhausted used => used

def ParameterSearchResult.status : ParameterSearchResult → Nat
  | .entropy .. => 0
  | .accepted .. => 1
  | .exhausted .. => 3

def ParameterSearchResult.remaining : ParameterSearchResult → Nat
  | .entropy remaining _ _ => remaining
  | _ => 0

def ParameterSearchResult.requested : ParameterSearchResult → Nat
  | .entropy _ requested _ => requested
  | _ => 0

def ParameterSearchResult.consume (n : Nat) : ParameterSearchResult → ParameterSearchResult
  | .entropy remaining requested used => .entropy remaining requested (n + used)
  | .accepted p used => .accepted p (n + used)
  | .exhausted used => .exhausted (n + used)

/-- Search all complete candidates in the tape. Rejection advances to the next
candidate inside the verified routine; only an entropy request returns control
to the host. `remaining` is persistent native state across refills. -/
def parameterSearch (bits generator : Nat) : Nat → Rand → ParameterSearchResult
  | 0, _ => .exhausted 0
  | remaining + 1, rand =>
    match parameterCandidate bits generator rand with
    | none =>
      if parameterEntropy bits ≤ rand.length then .exhausted 0
      else .entropy (remaining + 1) (parameterRequest bits rand.length) 0
    | some (some p, rest) => .accepted p (rand.length - rest.length)
    | some (none, rest) =>
      (parameterSearch bits generator remaining rest).consume (rand.length - rest.length)

end VG.Spec.Ffdh
