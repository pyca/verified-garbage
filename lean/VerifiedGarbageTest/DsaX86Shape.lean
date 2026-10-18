import VerifiedGarbageTest.DsaX86Core
import VerifiedGarbage.Impl.Dsa.X86.Shape
import VerifiedGarbage.Proof.Dsa.X86.Shape
import VerifiedGarbage.Proof.Dsa.X86.Width
import VerifiedGarbage.Proof.Dsa.X86.ShapeParity
import VerifiedGarbage.Proof.Dsa.X86.DigestPrefix

/-! Differential tests of public shape recognition, including padded domains,
unsupported actual widths, even moduli, and empty/short/long digests. -/

#assert_standard_axioms VG.Proof.Dsa.X86.shape_ok
#assert_standard_axioms VG.Proof.Dsa.X86.optionalWidth_ok
#assert_standard_axioms VG.Proof.Dsa.X86.shapeWidth_ok
#assert_standard_axioms VG.Proof.Dsa.X86.shapeCombine_ok
#assert_standard_axioms VG.Proof.Dsa.X86.shapeParity_ok
#assert_standard_axioms VG.Proof.Dsa.X86.digestPrefix_ok

namespace VG.Test.DsaX86Shape
open VG VG.X86 VG.Test.DsaX86Mont VG.Test.DsaX86Core VG.Impl.Dsa.X86

def check (pLen qLen p q digestLen : Nat) : Except String Unit := do
  let base := 0x10000
  let input := 0x20000
  let ws := putBE (putBE ({} : Words) input pLen p) (input + pLen) qLen q
  let ws := put (put (put ws (base + Layout.field .p) 1 input)
    (base + Layout.field .q) 1 (input + pLen)) (base + Layout.field .digestLen) 1 digestLen
  let state : State := {
    gpr := fun reg => if reg == .edi then BitVec.ofNat 32 base else 0
    cf := none, zf := none, sf := none, of := none
    mem := memory ws, rd := [⟨BitVec.ofNat 64 input, pLen + qLen⟩], wr := [⟨BitVec.ofNat 64 base, 16384⟩] }
  let checked ← evaluate fuel (Shape.check pLen qLen) ⟨state, ws⟩
  let accepted := decide (Spec.Dsa.supportedSizes (Spec.Dsa.bitLength p) (Spec.Dsa.bitLength q)) &&
    p % 2 == 1 && q % 2 == 1
  unless get checked.words (base + Layout.field .mask) 1 == (if accepted then 2 ^ 32 - 1 else 0) do
    throw s!"shape mismatch: encoded={pLen}/{qLen}, actual={Spec.Dsa.bitLength p}/{Spec.Dsa.bitLength q}"
  unless checked.state.zf == some (!accepted) do throw "shape rejection branch mismatch"
  if accepted then
    unless get checked.words (base + Layout.field .digestPrefixLen) 1 == min digestLen (Spec.Dsa.bitLength q / 8) do
      throw "digest prefix mismatch"
  unless getBE checked.words input pLen == p && getBE checked.words (input + pLen) qLen == q do
    throw "shape check changed its inputs"

def checks : Except String Unit := do
  for (pLen, qLen) in [(128, 20), (256, 20), (256, 28), (256, 32), (384, 32)] do
    for (pBits, qBits) in [(1024, 160), (2048, 160), (2048, 224), (2048, 256), (3072, 256), (1024, 224), (1023, 160)] do
      if pBits ≤ pLen * 8 && qBits ≤ qLen * 8 then
        for digestLen in [0, 7, 32, 64] do
          check pLen qLen (2 ^ (pBits - 1) + 1) (2 ^ (qBits - 1) + 1) digestLen
    check pLen qLen 0 0 0
    check pLen qLen (2 ^ 1023) (2 ^ 159 + 1) 32
    check pLen qLen (2 ^ 1023 + 1) (2 ^ 159) 32

end VG.Test.DsaX86Shape

run_cmd
  match VG.Test.DsaX86Shape.checks with
  | .ok _ => pure ()
  | .error e => Lean.throwError e
