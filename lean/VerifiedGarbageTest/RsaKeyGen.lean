import Lean.Elab.Command
import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-!
# RSA key generation specification tests

There are no known answers to compare with: key generation's results depend
on the randomness, which no published vectors give in the form `generate`
reads it. These tests check properties instead, on randomness from a fixed
linear congruential generator:

* Keys of 512, 768 and 1024 bits, with `e` = 65537, 3 and 2^32 − 1, pass
  the key check (`Rsa.checkKey`) and the pairwise consistency test (with
  `Rsa.privateChecked`), and their private
  operation inverts the public one; their primes have half the bits, the two
  most significant set, are probably prime by trial division to 8161, and
  are more than `2^(nlen/2 − 100)` apart, and `d > 2^(nlen/2)`.
* `generate` gives the same key for any extension of randomness that
  sufficed, and `none` for randomness that ran out.
* Refused sizes and exponents fail with `badParameters`.
* The small primes are the first 1024 primes; `checksForSize`'s table
  edges; `candidate`'s bits; `witness`'s forcing into `[2, w − 2]`;
  `primalityTest` agrees with trial division on the numbers below 3000.
-/

namespace VG.Test.RsaKeyGen

open Lean Elab Command Spec.RsaKeyGen

/-- `n` octets of a 64-bit linear congruential generator from `seed`, each
the top octet of a state (the test's randomness, not a test vector). -/
def prng (seed n : Nat) : List Byte := Id.run do
  let mut s := seed
  let mut out : Array Byte := #[]
  for _ in [0:n] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    out := out.push (BitVec.ofNat 8 (s / 2 ^ 56))
  return out.toList

/-- Equal results of `generate`. -/
def same : Option (Except Failure Key) → Option (Except Failure Key) → Bool
  | none, none => true
  | some (.ok k), some (.ok k') => k == k'
  | some (.error f), some (.error f') => f == f'
  | _, _ => false

/-- Checks of a generated key of `nlen` bits with the exponent `e`. -/
def checkKey (nlen e : Nat) (k : Key) : Except String Unit := do
  let half := nlen / 2
  unless k.e == e do throw "e"
  unless keyValid k do throw "key check"
  unless pairwiseOk k do throw "pairwise consistency test"
  unless bitLength k.n == nlen && bitLength k.p == half && bitLength k.q == half do
    throw "sizes"
  unless k.p / 2 ^ (half - 2) == 3 && k.q / 2 ^ (half - 2) == 3 do throw "top two bits"
  unless k.q < k.p && k.p - k.q > 2 ^ (half - 100) do throw "distance"
  unless k.d > 2 ^ half do throw "d too small"
  unless Nat.gcd (k.p - 1) e == 1 && Nat.gcd (k.q - 1) e == 1 do throw "gcd"
  unless smallPrimes.all (fun s => k.p % s != 0 && k.q % s != 0) do throw "small factor"
  let m := 0x1234567 % k.n
  unless Spec.Rsa.powMod (Spec.Rsa.powMod m e k.n) k.d k.n == m do throw "d does not invert e"
  unless e * k.d % Nat.lcm (k.p - 1) (k.q - 1) == 1 do throw "d not e⁻¹ mod λ(n)"

/-- Generation with the randomness `prng seed len`, checked, and the same key
for longer randomness; `none` for randomness 64 octets short of what it
read. -/
def checkGenerate (nlen e seed len : Nat) : Except String Unit := do
  let rand := prng seed len
  let some (.ok k) := generate nlen e rand | throw s!"no {nlen}-bit key"
  checkKey nlen e k
  unless same (generate nlen e (rand ++ prng (seed + 1) 1000)) (some (.ok k)) do
    throw "longer randomness, other key"
  -- The octets read (by the first try, which gave the key).
  let some (.ok k', rest) := generateOnce nlen e rand | throw "first try failed"
  unless k' == k do throw "first try, other key"
  let used := rand.length - rest.length
  unless same (generate nlen e (rand.take used)) (some (.ok k)) do throw "exact randomness"
  unless same (generate nlen e (rand.take (used - 64))) none do throw "short randomness"

/-- Edges, not known answers. -/
def checkEdges : Except String Unit := do
  unless smallPrimes.length == 1024 && smallPrimes.head? == some 2 &&
      smallPrimes.getLast? == some 8161 do
    throw "smallPrimes"
  unless (smallPrimes.zip smallPrimes.tail).all (fun (a, b) => a < b) do throw "smallPrimes order"
  for (bits, ok) in [(511, none), (512, some 512), (639, some 512), (640, some 640),
      (8191, some 8064), (8192, some 8192), (8193, none), (0, none)] do
    unless modulusBits bits == ok do throw s!"modulusBits {bits}"
  for (e, ok) in [(0, false), (1, false), (2, false), (3, true), (65537, true),
      (2 ^ 32 - 1, true), (2 ^ 32 + 1, false), (65536, false)] do
    unless exponentValid e == ok do throw s!"exponentValid {e}"
  unless [(2048, 65536), (511, 65537), (8193, 65537), (2048, 1)].all fun (bits, e) =>
      same (generate bits e []) (some (.error .badParameters)) do
    throw "parameters accepted"
  for (bits, n) in [(54, 34), (55, 27), (307, 27), (308, 8), (346, 8), (347, 7), (399, 7),
      (400, 6), (475, 6), (476, 5), (1344, 5), (1345, 4), (3746, 4), (3747, 3)] do
    unless checksForSize bits == n do throw s!"checksForSize {bits}"
  for x in (prng 3 4096).map (·.toNat) do
    for bits in [8, 9, 64] do
      let c := candidate bits (x * 2 ^ 56 + x)
      unless c % 2 == 1 && bitLength c == bits && c / 2 ^ (bits - 2) == 3 do
        throw s!"candidate {bits}"
  for w in [5, 7, 9, 255, 257, 1025, 65537] do
    for x in List.range 4096 do
      let (b, u) := witness (w - 1) x
      unless 2 ≤ b && b < w - 1 do throw s!"witness {w} {x}"
      unless u == (2 ≤ x % 2 ^ bitLength (w - 1) && x % 2 ^ bitLength (w - 1) < w - 1) do
        throw s!"witness uniform {w} {x}"
  let r := prng 5 8192
  for w in List.range 3000 do
    unless (primalityTest w r).map (·.1) == some (smallPrime w) do
      throw s!"primalityTest {w}"
  unless tooClose 256 none 0 == false && tooClose 256 (some (2 ^ 156)) 0 == true &&
      tooClose 256 (some (2 ^ 156 + 1)) 0 == false && tooClose 256 (some 0) (2 ^ 156) == true do
    throw "tooClose"
  unless (pairwiseMessage 64).length == 64 do throw "pairwiseMessage"

#assert_standard_axioms Spec.RsaKeyGen.generate
#assert_standard_axioms Spec.RsaKeyGen.candidateStep
#assert_standard_axioms Spec.RsaKeyGen.keyFromPrimes
#assert_no_compiler_overrides Spec.RsaKeyGen.generate Spec.RsaKeyGen.candidateStep Spec.RsaKeyGen.keyFromPrimes
#assert_spec_origin

run_cmd do
  match checkEdges with
  | .ok () => pure ()
  | .error e => throwError "RSA key generation edges: {e}"
  for (nlen, e, seed, len) in [(512, 65537, 1, 40000), (768, 3, 2, 80000),
      (1024, 2 ^ 32 - 1, 3, 200000), (512, 3, 4, 40000)] do
    match checkGenerate nlen e seed len with
    | .ok () => pure ()
    | .error err => throwError "RSA key generation, {nlen} bits, e = {e}: {err}"

end VG.Test.RsaKeyGen
