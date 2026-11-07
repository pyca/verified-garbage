module

import Lean.Elab.Command
meta import Lean.Elab.Command
import VerifiedGarbage.Proof.RsaKeyGen.SearchContract
meta import VerifiedGarbage.Proof.RsaKeyGen.SearchContract
import VerifiedGarbage.TCB.Audit
meta import VerifiedGarbage.TCB.Audit

/-!
# The RSA prime search over refillable tapes

Properties of the search's consumption, refills and trace, not known
answers: `generatePrime`, the specification the search must agree with, is
the comparison, on a deterministic stream of octets. A test stream says
nothing about the primality test's error probability.
-/

namespace VG.Test.RsaPrimeSearch

open Lean Elab Command Spec.RsaKeyGen Spec.Entropy

/-- `n` octets of a 64-bit linear congruential generator's high bits. -/
def octets (seed n : Nat) : List Byte := Id.run do
  let mut state := seed
  let mut result : Array Byte := #[]
  for _ in [0:n] do
    state := (state * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    result := result.push (BitVec.ofNat 8 (state / 2 ^ 56))
  return result.toList

/-- Serve the search from one stream as a host would: each tape keeps what
the last one did not consume and takes the stream's next octets, here to
twice as many as were left and one more: any length more than the octets left
is one the search may ask for. The prime and the stream's octets consumed. `fuel` bounds
this test, not the search. -/
def refill (eB : List Byte) (source : Rand) : Nat → Nat → Nat → Nat →
    Except String (Nat × Nat)
  | 0, _, _, _ => .error "refills did not terminate"
  | fuel + 1, remaining, offset, requested =>
    if source.length < offset + requested then .error "test stream too short" else
      let tape := (source.drop offset).take requested
      let r := primeSearch 32 eB [] remaining tape
      match r.outcome with
      | .accepted p => .ok (p, offset + r.used)
      | .exhausted => .error "unexpected exhausted search"
      | .entropy left available =>
        if r.used > tape.length || available != tape.length - r.used then
          .error "consumed more than the tape, or miscounted the octets left"
        else refill eB source fuel left (offset + r.used) (2 * available + 1)

def check : Except String Unit := do
  let eB : List Byte := [1, 0, 1]
  let limit := primeLimit 256 65537
  let source := octets 1 32768
  let some (.ok expected, rest) := generatePrime 256 65537 none source
    | throw "generatePrime found no prime in the test stream"
  let expectedUsed := source.length - rest.length
  -- One tape holding everything: what `generatePrime` finds.
  let direct := primeSearch 32 eB [] limit source
  unless direct.outcome == .accepted expected && direct.used == expectedUsed do
    throw "one tape's search differs from generatePrime"
  -- Starting from one octet and refilling: the same.
  unless (← refill eB source 10000 limit 0 1) == (expected, expectedUsed) do
    throw "refills changed the prime or the octets consumed"
  -- A tape ending where the prime's test ends is enough; one octet less is not,
  -- and consumes nothing of the prime's candidate.
  let exact := primeSearch 32 eB [] limit (source.take expectedUsed)
  unless exact.status == 1 && exact.used == expectedUsed do
    throw "the exact tape did not accept"
  let short := primeSearch 32 eB [] limit (source.take (expectedUsed - 1))
  unless short.status == 0 && short.used < expectedUsed do
    throw "a partial last witness was consumed or accepted"
  -- The accepted candidate's trace entry: its length, then [1, octets read].
  unless direct.trace.drop (direct.trace.length - 3) == [2, 1, expectedUsed - short.used] do
    throw "the accepted candidate's trace entry is wrong"
  -- A candidate too close to the other prime is consumed but not counted.
  let close := primeSearch 32 eB (Spec.Rsa.i2osp expected 32) limit
    (Spec.Rsa.i2osp expected 32)
  unless close == ⟨.entropy limit 0, 32, [1, 2, 1, 0]⟩ do
    throw "a too-close candidate was counted, or its trace has its octets"
  -- e = 0 (which `primeInit` allows; full key generation does not) makes every
  -- candidate fail its gcd check: one counted rejection exhausts a budget of one.
  let rejected := primeSearch 32 [0] [] 1 (source.take 32)
  unless rejected.status == 3 && rejected.used == 32 do
    throw "the budget of counted candidates was not enforced"
  unless primeSearch 32 eB [] 0 source == ⟨.exhausted, 0, []⟩ do
    throw "an exhausted search consumed octets"
  unless primeSearch 32 eB [] limit [] == ⟨.entropy limit 0, 0, [1, 0]⟩ do
    throw "an empty tape did not ask for more"
  unless primeInit 32 [3] == primeInit 32 [0, 0, 3] do
    throw "leading zeros changed the exponent"
  unless primeInit 31 eB == none && primeInit 33 eB == none &&
      primeInit 520 eB == none && primeInit 32 [] == none &&
      primeInit 32 (List.replicate 9 1) == none do
    throw "an invalid width or exponent length was accepted"

/-- The entropy budget, on a one-octet prime (outside the native widths, so
that reaching the budget takes thousands of one-octet draws rather than
thousands of full-width tests). All-zero witness octets are never uniform
witnesses, so a prime candidate never gets enough of them: the search must
give up at the budget rather than accept it. -/
def checkEntropyBudget : Except String Unit := do
  let accepted := (List.range 256).find? fun x =>
    match candidateOp 1 [1] [] (Spec.Rsa.i2osp x 1 ++ List.replicate 512 (2 : Byte)) with
    | some (.prime _, _) => true
    | _ => false
  let some x := accepted | throw "no one-octet prime candidate"
  let tape := Spec.Rsa.i2osp x 1 ++ List.replicate (primeEntropy 1 - 1) 0
  unless primeSearch 1 [1] [] 1 tape == ⟨.exhausted, 0, [1, 0]⟩ do
    throw "the budget let a candidate through without enough uniform witnesses"
  let short := primeSearch 1 [1] [] 1 (tape.take (primeEntropy 1 - 1))
  unless short == ⟨.entropy 1 (primeEntropy 1 - 1), 0, [1, 0]⟩ do
    throw "below the budget, the candidate was not kept for a refill"

#assert_no_compiler_overrides Spec.RsaKeyGen.primeInit Spec.RsaKeyGen.primeSearch

run_cmd do
  for result in [check, checkEntropyBudget] do
    match result with
    | .ok () => pure ()
    | .error message => throwError "RSA prime search: {message}"

end VG.Test.RsaPrimeSearch
