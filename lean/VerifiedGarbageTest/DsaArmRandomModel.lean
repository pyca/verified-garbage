import VerifiedGarbageTest.DsaArmModel
import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
import VerifiedGarbage.Spec.Dsa.Random

/-! Differential execution of the scalar sampler in the AArch64 ISA model.
These are sampler boundary inputs, not cryptographic known-answer vectors.
This does not replace the whole-program verification required for emission. -/
namespace VG.Test.DsaArmRandomModel
open VG VG.AArch64
open DsaArmModel
open Impl.Dsa.AArch64.Random

def check (q qLen : Nat) (rand : List Byte) : Except String Unit := do
  let qb := Spec.Dsa.encodeBE qLen q
  let regions := [(0x2000, qb), (0x3000, rand)]
  let mem : Mem := fun a =>
    match regions.find? (fun (p, bs) => p ≤ a.toNat && a.toNat < p + bs.length) with
    | some (p, bs) => bs.getD (a.toNat - p) 0
    | none => 0
  let mut words : Words := {}
  for (p, bs) in regions do
    for i in [: (bs.length + 7) / 8] do
      words := words.insert ((p / 8) + i) (mem.readW (BitVec.ofNat 64 (p + 8 * i)) 64)
  for (slot, value) in [(oQ, 0x2000), (oQLen, qLen), (oRand, 0x3000),
      (oRandLen, rand.length), (oUsed, 0)] do
    words := words.insert ((0x1000 + slot) / 8) (BitVec.ofNat 64 value)
  let s : State := {
    gpr := fun r => BitVec.ofNat 64 (0x5500 + r.ctorIdx)
    sp := 0x1000, mem := memory words
    rd := [⟨0x2000, qLen⟩, ⟨0x3000, rand.length⟩]
    wr := [⟨0x1000, frameBytes⟩] }
  let prog : Prog isa := .seq prepare (.ite (.nonzero .x .x0) sample (.block []))
  let after ← evaluate 10000 prog ⟨s, words, 0⟩
  let expected := Spec.Dsa.Random.sample q 128 rand
  let status := if expected.scalar.isSome then 1 else
    if expected.trace.getLast? == some 2 then 2 else 0
  unless after.state.gpr .x0 == BitVec.ofNat 64 status do
    throw s!"status: q={q}, len={rand.length}"
  unless after.state.mem.readW (BitVec.ofNat 64 (0x1000 + oUsed)) 64 ==
      BitVec.ofNat 64 expected.used do throw s!"consumption: q={q}, len={rand.length}"
  if let some k := expected.scalar then
    unless Spec.Rsa.bytesAt after.state.mem (BitVec.ofNat 64 (0x1000 + oNonce)) qLen ==
        Spec.Dsa.encodeBE qLen k do throw s!"scalar: q={q}, len={rand.length}"
  for reg in [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30] do
    unless after.state.gpr reg == s.gpr reg do throw "callee-saved register changed"

def checks : Except String Nat := do
  let mut count := 0
  for q in [0, 1, 2, 3, 13, 127, 128, 129, 255, 256, 257, 65535,
      2 ^ 159 + 7, 2 ^ 223 + 9, 2 ^ 255 + 19] do
    let width := Spec.Dsa.Random.drawBytes q
    for qLen in [20, 28, 32] do
      if width ≤ qLen then
        let accepted := Spec.Dsa.encodeBE width (q - 1)
        for rand in [[], [0], accepted, Spec.Dsa.encodeBE width q ++ accepted,
            List.replicate width 0 ++ accepted,
            List.replicate (128 * width) 0 ++ accepted,
            List.replicate (127 * width) 0 ++ accepted,
            List.replicate width 255 ++ accepted,
            accepted ++ List.replicate width 255] do
          check q qLen rand
          count := count + 1
  -- Exhaustive one-byte candidates for several non-power-of-two domains.
  for q in [3, 13, 129, 255] do
    for b in [:256] do
      check q 20 [BitVec.ofNat 8 b]
      count := count + 1
  return count
end VG.Test.DsaArmRandomModel

run_cmd
  match VG.Test.DsaArmRandomModel.checks with
  | .ok _ => pure ()
  | .error e => Lean.throwError e
