module

import Lean.Elab.Command
meta import Lean.Elab.Command
import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
meta import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit
meta import VerifiedGarbage.TCB.Audit

/-!
# DSA parameter generation over refillable tapes

Properties of the search's consumption, refills and limits, on a
deterministic stream of octets and a 1024-bit modulus. A test stream says
nothing about the primality test's error probability. The pieces each seed runs (`qCandidate`,
`pCandidate`, `probablePrime`) keep the known answers of
`VerifiedGarbageTest/Dsa.lean`.
-/

namespace VG.Test.DsaParameterSearch

open Lean Elab Command Spec.Dsa Spec.Entropy
open Spec.RsaKeyGen (Rand)

/-- `n` octets of a 64-bit linear congruential generator's high bits. -/
def octets (seed n : Nat) : List Byte := Id.run do
  let mut state := seed
  let mut result : Array Byte := #[]
  for _ in [0:n] do
    state := (state * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    result := result.push (BitVec.ofNat 8 (state / 2 ^ 56))
  return result.toList

/-- The seeds rejected before the first accepted one in `rand`, by running
`seedCandidate` one seed at a time. -/
def rejectedSeeds (pLen : Nat) : Nat → Rand → Except String Nat
  | 0, _ => .error "no accepted seed in the test stream"
  | fuel + 1, rand =>
    match seedCandidate pLen (generationQLen pLen) rand with
    | none => .error "the test stream ran out"
    | some (some _, _) => .ok 0
    | some (none, rest) => return (← rejectedSeeds pLen fuel rest) + 1

/-- Serve the search from one stream as a host would: each tape keeps what
the last one did not consume and takes the stream's next octets, here to
twice as many as were left and one more: any length more than the octets left
is one the search may ask for. The parameters and the stream's octets consumed. `fuel`
bounds this test, not the search. -/
def refill (pLen : Nat) (source : Rand) : Nat → Nat → Nat → Nat →
    Except String (Params × Nat)
  | 0, _, _, _ => .error "refills did not terminate"
  | fuel + 1, remaining, offset, requested =>
    if source.length < offset + requested then .error "test stream too short" else
      let tape := (source.drop offset).take requested
      let r := parameterSearch pLen remaining tape
      match r.outcome with
      | .accepted a => .ok (a, offset + r.used)
      | .exhausted => .error "unexpected exhausted search"
      | .entropy left available =>
        if r.used > tape.length || available != tape.length - r.used then
          .error "consumed more than the tape, or miscounted the octets left"
        else refill pLen source fuel left (offset + r.used) (2 * available + 1)

def check : Except String Unit := do
  let pLen := 128
  let source := octets 1 100000
  -- One tape holding everything.
  let direct := parameterSearch pLen parameterSeeds source
  let .accepted a := direct.outcome | throw "one tape's search found no parameters"
  unless parametersValid a && a.q.log2 + 1 == 160 && a.p.log2 + 1 == 1024 do
    throw "the parameters are invalid or of the wrong widths"
  unless direct.trace == [] do throw "the trace is not empty"
  let used := direct.used
  -- Starting from one octet and refilling: the same.
  unless (← refill pLen source 10000 parameterSeeds 0 1) == (a, used) do
    throw "refills changed the parameters or the octets consumed"
  -- A tape ending where the accepted seed ends is enough; one octet less is
  -- not, and consumes nothing of that seed.
  let exact := parameterSearch pLen parameterSeeds (source.take used)
  unless exact == direct do throw "the exact tape did not accept"
  let short := parameterSearch pLen parameterSeeds (source.take (used - 1))
  unless short.status == 0 && short.used < used do
    throw "a partial last seed was consumed or accepted"
  -- The rejected seeds before it count against the budget.
  let rejected ← rejectedSeeds pLen parameterSeeds source
  unless short.remaining == parameterSeeds - rejected do
    throw "rejected seeds were not counted"
  unless rejected ≠ 0 do throw "the test stream's first seed was accepted"
  let tight := parameterSearch pLen (rejected + 1) source
  unless tight.outcome == .accepted a && tight.used == used do
    throw "a budget of exactly enough seeds did not accept"
  let over := parameterSearch pLen rejected source
  unless over.status == 3 && over.used == short.used do
    throw "the budget of rejected seeds was not enforced"
  unless parameterSearch pLen 0 source == ⟨.exhausted, 0, []⟩ do
    throw "an exhausted search consumed octets"
  unless parameterSearch pLen parameterSeeds [] ==
      ⟨.entropy parameterSeeds 0, 0, []⟩ do
    throw "an empty tape did not ask for more"

/-- The entropy budget, on a one-octet modulus width (so that the budget is
a few thousand octets): a seed whose `q` passes trial division, followed by
all-zero witness octets, which are never uniform witnesses, so `q`'s test
never ends. The search must give up at the budget rather than accept it. -/
def checkEntropyBudget : Except String Unit := do
  let stream := octets 2 65536
  let seeds := (List.range 2048).map fun i => (stream.drop (32 * i)).take 32
  let some seed := seeds.find? fun s =>
      probablePrime (qCandidate 256 s) (List.replicate 32 1) |>.isNone
    | throw "no seed whose q survives trial division"
  let tape := seed ++ List.replicate (parameterEntropy 1 - 32) 0
  unless parameterSearch 1 1 tape == ⟨.exhausted, 0, []⟩ do
    throw "the budget let a seed through without enough uniform witnesses"
  let short := parameterSearch 1 1 (tape.take (parameterEntropy 1 - 1))
  unless short == ⟨.entropy 1 (parameterEntropy 1 - 1), 0, []⟩ do
    throw "below the budget, the seed was not kept for a refill"

def checkInit : Except String Unit := do
  for pLen in [128, 256, 384] do
    unless parameterInit pLen ==
        some [parameterSeeds, pLen, parameterEntropy pLen] do
      throw "a supported width's words are wrong"
  for pLen in [0, 20, 32, 127, 192, 512] do
    unless parameterInit pLen == none do throw "an unsupported width was accepted"
  unless generationQLen 128 == 20 && generationQLen 256 == 32 && generationQLen 384 == 32 &&
      [128, 256, 384].all fun p => generationLengthsValid p (generationQLen p) do
    throw "the subgroup widths are not the generated (L, N) pairs"

#assert_standard_axioms Spec.Dsa.parameterInitContract
#assert_standard_axioms Spec.Dsa.parameterSearchContract
#assert_no_compiler_overrides Spec.Dsa.parameterInitApi Spec.Dsa.parameterSearchApi
#assert_spec_origin

run_cmd do
  for result in [check, checkEntropyBudget, checkInit] do
    match result with
    | .ok () => pure ()
    | .error message => throwError "DSA parameter search: {message}"

end VG.Test.DsaParameterSearch
