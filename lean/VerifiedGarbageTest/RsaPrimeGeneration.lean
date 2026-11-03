module

import Lean.Elab.Command
meta import Lean.Elab.Command
import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
meta import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit
meta import VerifiedGarbage.TCB.Audit

/-!
# Refillable RSA prime-search specification regressions

These are API and stream-consumption properties, not invented known-answer
vectors or a second implementation of the primality test. The existing
`generatePrime` is the comparison for a deterministic synthetic byte stream.
Test randomness does not establish a probabilistic primality guarantee.
-/

namespace VG.Test.RsaPrimeGeneration

open Lean Elab Command Spec.RsaKeyGen

def octets (seed n : Nat) : List Byte := Id.run do
  let mut state := seed
  let mut result : Array Byte := #[]
  for _ in [0:n] do
    state := (state * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    result := result.push (BitVec.ofNat 8 (state / 2 ^ 56))
  return result.toList

/-- Refill from one fixed stream, preserving the incomplete prefix. The
fuel bounds this test driver, not production candidate generation. -/
def refill (eB : List Byte) (source : Rand) : Nat → Nat → Nat → Nat →
    Except String (Nat × Nat)
  | 0, _, _, _ => .error "refill test did not terminate"
  | fuel + 1, remaining, offset, requested =>
    if source.length < offset + requested then .error "test stream too short" else
      let tape := (source.drop offset).take requested
      match primeSearch 32 eB [] remaining tape with
      | .accepted p used _ => .ok (p, offset + used)
      | .exhausted .. => .error "unexpected exhausted search"
      | .entropy left next used _ =>
        if used > tape.length || next ≤ tape.length - used then
          .error "invalid consumption or non-growing entropy request"
        else refill eB source fuel left (offset + used) next

def check : Except String Unit := do
  let eB : List Byte := [1, 0, 1]
  let limit := primeLimit 256 65537
  let source := octets 1 32768
  let some (.ok expected, rest) := generatePrime 256 65537 none source
    | throw "existing generator did not produce a test prime"
  let expectedUsed := source.length - rest.length
  let direct := primeSearch 32 eB [] limit source
  match direct with
  | .accepted p used _ =>
    unless p == expected && used == expectedUsed do
      throw "one-shot search differs from the existing generator"
  | _ => throw "one-shot search did not accept"
  -- Begin with a partial candidate, then obey the controller's requests.
  unless (← refill eB source 100 limit 0 1) == (expected, expectedUsed) do
    throw "refilling changed the prime or total stream consumption"
  let exact := primeSearch 32 eB [] limit (source.take expectedUsed)
  unless exact.status == 1 && exact.used == expectedUsed do
    throw "exact sufficient tape did not accept"
  let short := primeSearch 32 eB [] limit (source.take (expectedUsed - 1))
  unless short.status == 0 && short.used < expectedUsed do
    throw "partial final witness was consumed or accepted"
  unless direct.trace.drop (direct.trace.length - 3) ==
      [2, 1, expectedUsed - short.used] do
    throw "acceptance trace exposed more than its framed status and consumption"
  -- A distance rejection consumes a candidate, but not a counted attempt.
  let close := primeSearch 32 eB (Spec.Rsa.i2osp expected 32) limit
    (Spec.Rsa.i2osp expected 32)
  unless close == .entropy limit (primeRequest 32 0) 32 [1, 2, 1, 0] do
    throw "distance rejection changed the budget or leaked candidate bytes"
  -- The standalone prime API accepts e=0's encoding; every full-width
  -- candidate fails its gcd check. One counted rejection exhausts it.
  let rejected := primeSearch 32 [0] [] 1 (source.take 32)
  unless rejected.status == 3 && rejected.used == 32 do
    throw "counted candidate budget was not enforced"
  unless primeSearch 32 eB [] 0 source == .exhausted 0 [] do
    throw "exhausted search consumed entropy"
  unless primeSearch 32 eB [] limit [] == .entropy limit 1024 0 [1, 0] do
    throw "empty tape did not request entropy"
  unless primeInit 32 [3] == primeInit 32 [0, 0, 3] do
    throw "leading-zero exponent changed the controller"
  unless primeInit 31 eB == none && primeInit 33 eB == none &&
      primeInit 520 eB == none && primeInit 32 [] == none &&
      primeInit 32 (List.replicate 9 1) == none do
    throw "invalid width or exponent encoding was accepted"
  for len in [32, 64, 128, 256, 384, 512] do
    unless primeRequest len 0 == 32 * len &&
        primeRequest len (primeEntropy len - 1) == primeEntropy len do
      throw "entropy request does not grow to its cap"

/-- Small arithmetic fixtures exercise cap exhaustion without thousands
of full-width primality rounds. This tests the mathematical controller,
not the native contract's accepted prime widths. All-zero witness octets
force nonuniform witnesses; a prime must never pass without enough
uniform witnesses, even after its resource budget runs out. -/
def checkEntropyCap : Except String Unit := do
  let accepted := (List.range 256).find? fun x =>
    match candidateOp 1 [1] []
        (Spec.Rsa.i2osp x 1 ++ List.replicate 512 (2 : Byte)) with
    | some (.prime _, _) => true
    | _ => false
  let some x := accepted | throw "no small arithmetic fixture"
  let tape := Spec.Rsa.i2osp x 1 ++ List.replicate (primeEntropy 1 - 1) 0
  let full := primeSearch 1 [1] [] 1 tape
  unless full == .exhausted 0 [1, 0] do
    throw "entropy cap accepted a test with insufficient uniform witnesses"
  let short := primeSearch 1 [1] [] 1 (tape.take (primeEntropy 1 - 1))
  unless short == .entropy 1 (primeEntropy 1) 0 [1, 0] do
    throw "near-cap request did not preserve the candidate prefix"

#assert_standard_axioms Spec.RsaKeyGen.primeInitContract
#assert_standard_axioms Spec.RsaKeyGen.primeSearchContract
#assert_no_compiler_overrides Spec.RsaKeyGen.primeInitApi Spec.RsaKeyGen.primeSearchApi
#assert_spec_origin

run_cmd do
  for result in [check, checkEntropyCap] do
    match result with
    | .ok () => pure ()
    | .error message => throwError "RSA prime controller: {message}"

end VG.Test.RsaPrimeGeneration
