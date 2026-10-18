import VerifiedGarbageTest.DsaX86Mont
import VerifiedGarbage.Impl.Dsa.X86.Core
import VerifiedGarbage.Proof.Dsa.X86.CoreProduct
import VerifiedGarbage.Proof.Dsa.X86.CoreSum
import VerifiedGarbage.Proof.Dsa.X86.CorePower
import VerifiedGarbage.Proof.Dsa.X86.CoreReduce
import VerifiedGarbage.Proof.Dsa.X86.SignArithmetic
import VerifiedGarbage.Proof.Dsa.X86.VerifyArithmetic
import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Spec.Rsa.Contract

/-! Synthetic differential tests of the composed signing and verification
arithmetic. These exercise the ISA model, not a replacement implementation
of its instruction semantics, and are not known-answer vectors. -/

#assert_standard_axioms VG.Proof.Dsa.X86.signArithmetic_ok
#assert_standard_axioms VG.Proof.Dsa.X86.verifyArithmetic_ok
#assert_standard_axioms VG.Proof.Dsa.X86.coreProductMod_ok
#assert_standard_axioms VG.Proof.Dsa.X86.coreProduct_ok
#assert_standard_axioms VG.Proof.Dsa.X86.coreSum_ok
#assert_standard_axioms VG.Proof.Dsa.X86.corePower_ok
#assert_standard_axioms VG.Proof.Dsa.X86.coreReduce_ok

namespace VG.Test.DsaX86Core
open VG VG.X86 VG.Test.DsaX86Mont VG.Impl.Dsa.X86
open VG.Impl.Dsa.Layout

def putBE (ws : Words) (address len value : Nat) : Words :=
  put ws address ((len + 3) / 4) ((List.range len).foldl (fun a i =>
    a + ((value >>> (8 * (len - 1 - i))) % 256) * 2 ^ (8 * i)) 0)

def getBE (ws : Words) (address len : Nat) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt (memory ws) (BitVec.ofNat 64 address) len)

def check (x nonce digest : Nat) : Except String Unit := do
  let base := 0x10000
  let input := 0x20000
  let p := 563
  let q := 281
  let g := 4
  let y := Spec.Dsa.powMod g x p
  let ws := putBE (putBE ({} : Words) input 8 p) (input + 8) 4 q
  let ws := putBE (putBE ws (input + 12) 8 g) (input + 20) 8 y
  let ws := putBE (putBE ws (input + 28) 4 x) (input + 32) 4 nonce
  let ws := putBE (putBE ws (input + 36) 4 digest) (base + qMinusTwo) 4 (q - 2)
  let ws := [(Field.p, input), (.q, input + 8), (.g, input + 12), (.y, input + 20),
    (.x, input + 28), (.nonce, input + 32), (.digest, input + 36), (.signature, input + 40),
    (.qLen, 4), (.digestPrefixLen, 4)].foldl (fun w (f, value) => put w (base + Layout.field f) 1 value) ws
  let state : State := {
    gpr := fun reg => if reg == .edi then BitVec.ofNat 32 base else if reg == .esp then 0x40000 else 0
    unknowns := fun i => BitVec.ofNat 32 (0x60000 + 4 * i)
    cf := none, zf := none, sf := none, of := none
    mem := memory ws, rd := [⟨BitVec.ofNat 64 input, 48⟩], wr := [⟨BitVec.ofNat 64 base, 16384⟩] }
  let signed ← evaluate fuel (Core.sign 8 4) ⟨state, ws⟩
  let expectedR := Spec.Dsa.powMod g nonce p % q
  let expectedS := Spec.Dsa.powMod nonce (q - 2) q * (digest + x * expectedR) % q
  unless getBE signed.words (base + r) 4 == expectedR && getBE signed.words (base + s) 4 == expectedS do
    throw s!"composed signing mismatch: x={x}, nonce={nonce}, digest={digest}"
  let vw := putBE (putBE signed.words (input + 40) 4 expectedR) (input + 44) 4 expectedS
  let vs : State := { signed.state with mem := memory vw }
  let verified ← evaluate fuel (Core.verify 8 4) ⟨vs, vw⟩
  let inverse := Spec.Dsa.powMod expectedS (q - 2) q
  let expected := (Spec.Dsa.powMod g (digest * inverse % q) p *
    Spec.Dsa.powMod y (expectedR * inverse % q) p) % p % q
  unless getBE verified.words (base + u) 4 == expected do
    throw "composed verification mismatch"

def checks : Except String Unit := do
  for (x, k, d) in [(1, 1, 0), (13, 19, 123456), (280, 280, 2 ^ 32 - 1), (0, 0, 0)] do
    check x k d

end VG.Test.DsaX86Core

run_cmd
  match VG.Test.DsaX86Core.checks with
  | .ok _ => pure ()
  | .error e => Lean.throwError e
