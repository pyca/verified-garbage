module
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Spec.Entropy


/-! # Complete FFDH generation control over refillable octet tapes

The caller supplies entropy, not retry decisions. The native controller owns
candidate-search limits and entropy budgets, and chooses how much entropy to
ask for, within `Entropy.RequestValid`'s bounds. On a request for more entropy,
`used` octets are discarded and the unconsumed suffix, `available` octets, is
extended to the requested length. In particular an incomplete candidate is
replayed with its exact prefix.
-/

@[expose] public section

namespace VG.Spec.Ffdh

open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Spec.RsaKeyGen (Rand)

/-- Finite public search bound, including a malfunctioning entropy source. -/
def parameterAttempts (bits : Nat) : Nat := bits * bits * 64

/-- A per-candidate entropy budget, independent of witness-count policy. -/
def parameterEntropy (bits : Nat) : Nat := 32769 * ((bits + 7) / 8)

/-- Initialization's first three public words: the attempt limit, p's width in
octets and the entropy budget (the fourth, the first tape's length, is the
code's choice: `parameterInitContract`), followed by private workspace. All
parameter validation and policy arithmetic are native. -/
def parameterInit (bits generator : Nat) : Option (List Nat) :=
  if 512 ≤ bits && bits ≤ 8192 && (generator == 2 || generator == 5) then
    some [parameterAttempts bits, (bits + 7) / 8, parameterEntropy bits]
  else none

inductive ParameterSearchResult where
  | entropy (remaining available used : Nat)
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

/-- The length `requested` the host is asked for after the result `r`: one
`Entropy.RequestValid` allows for more entropy, and 0 otherwise. -/
def ParameterSearchResult.Requests (cap : Nat) (r : ParameterSearchResult) (requested : Nat) :
    Prop :=
  match r with
  | .entropy _ available _ => Entropy.RequestValid cap available requested
  | _ => requested = 0

def ParameterSearchResult.consume (n : Nat) : ParameterSearchResult → ParameterSearchResult
  | .entropy remaining available used => .entropy remaining available (n + used)
  | .accepted p used => .accepted p (n + used)
  | .exhausted used => .exhausted (n + used)

end VG.Spec.Ffdh
