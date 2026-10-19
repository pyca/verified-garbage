import VerifiedGarbage.Proof.Dsa.X86.SignSized
import VerifiedGarbage.Proof.Dsa.X86.VerifySized
import VerifiedGarbageTest.DsaX86Core
import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Dsa.X86.SignBody
import VerifiedGarbage.Proof.Dsa.X86.VerifyBody
import VerifiedGarbage.Proof.Dsa.X86.SignCompute
import VerifiedGarbage.Proof.Dsa.X86.VerifyCompute
import VerifiedGarbage.Proof.Dsa.X86.WriteScalar
import VerifiedGarbage.Proof.Dsa.X86.Result
import VerifiedGarbage.Impl.Dsa.X86.SignVerify

/-! Differential tests of post-shape sign/verify bodies against the DSA
specification on a synthetic small domain. A one-byte digest fits the small
subgroup bit length, so this test does not assume byte-aligned toy parameters.
The public supported-size gate is tested separately. -/

#assert_standard_axioms VG.Proof.Dsa.X86.signSized_spec
#assert_standard_axioms VG.Proof.Dsa.X86.verifySized_spec
#assert_standard_axioms VG.Proof.Dsa.X86.signBody_spec
#assert_standard_axioms VG.Proof.Dsa.X86.verifyBody_spec
#assert_standard_axioms VG.Proof.Dsa.signBytes_compute
#assert_standard_axioms VG.Proof.Dsa.verifyBytes_compute
#assert_standard_axioms VG.Proof.Dsa.signBytes_invalid_shape
#assert_standard_axioms VG.Proof.Dsa.verifyBytes_invalid_shape
#assert_standard_axioms VG.Proof.Dsa.X86.signBody_ok
#assert_standard_axioms VG.Proof.Dsa.X86.verifyBody_ok
#assert_standard_axioms VG.Proof.Dsa.X86.signCompute_ok
#assert_standard_axioms VG.Proof.Dsa.X86.verifyCompute_ok
#assert_standard_axioms VG.Proof.Dsa.X86.result_ok
#assert_standard_axioms VG.Proof.Dsa.X86.writeScalar_ok
#assert_standard_axioms VG.Proof.Dsa.publicChecks_spec
#assert_standard_axioms VG.Proof.Dsa.privateChecks_spec

namespace VG.Test.DsaX86SignVerify
open VG VG.X86 VG.Test.DsaX86Mont VG.Test.DsaX86Core VG.Impl.Dsa.X86
open VG.Impl.Dsa.Layout

def check (x nonce digest : Nat) : Except String Unit := do
  let base := 0x10000
  let input := 0x20000
  let output := 0x30000
  let y := Spec.Dsa.powMod 4 x 563
  let ws := putBE (putBE ({} : Words) input 8 563) (input + 8) 8 281
  let ws := putBE (putBE ws (input + 16) 8 4) (input + 24) 8 y
  let ws := putBE (putBE ws (input + 32) 8 x) (input + 40) 8 nonce
  let ws := putBE ws (input + 48) 1 digest
  let ws := putBE ws output 16 (2 ^ 128 - 1)
  let ws := [(Field.p, input), (.q, input + 8), (.g, input + 16), (.y, input + 24),
    (.x, input + 32), (.nonce, input + 40), (.digest, input + 48), (.signature, output),
    (.out, output), (.qLen, 8), (.digestPrefixLen, 1), (.mask, 2 ^ 32 - 1)].foldl
      (fun w (f, value) => put w (base + Layout.field f) 1 value) ws
  let state : State := {
    gpr := fun reg => if reg == .edi then BitVec.ofNat 32 base else if reg == .esp then 0x40000 else 0
    unknowns := fun i => BitVec.ofNat 32 (0x60000 + 4 * i)
    cf := none, zf := none, sf := none, of := none
    mem := memory ws, rd := [⟨BitVec.ofNat 64 input, 49⟩],
    wr := [⟨BitVec.ofNat 64 base, 16384⟩, ⟨BitVec.ofNat 64 output, 16⟩] }
  let signed ← evaluate fuel (SignVerify.signBody 8 8) ⟨state, ws⟩
  let key : Spec.Dsa.Key := ⟨⟨563, 281, 4⟩, y, some x⟩
  let dg := [BitVec.ofNat 8 digest]
  let expected := Spec.Dsa.signWithNonce key dg nonce
  let expectedR := expected.map (·.r) |>.getD 0
  let expectedS := expected.map (·.s) |>.getD 0
  unless signed.state.gpr .eax == (if expected.isSome then 1 else 0) &&
      getBE signed.words output 8 == expectedR && getBE signed.words (output + 8) 8 == expectedS do
    throw s!"sign body mismatch: x={x}, nonce={nonce}, digest={digest}"
  for rValue in [expectedR, (expectedR + 1) % 281] do
    let vw := put (putBE signed.words output 8 rValue) (base + Layout.field .mask) 1 (2 ^ 32 - 1)
    let vs : State := { signed.state with mem := memory vw }
    let verified ← evaluate fuel (SignVerify.verifyBody 8 8) ⟨vs, vw⟩
    let valid := Spec.Dsa.verify { key with x := none } ⟨rValue, expectedS⟩ dg
    unless verified.state.gpr .eax == (if valid then 1 else 0) do
      throw "verify body mismatch"

def checks : Except String Unit := do
  for (x, k, d) in [(1, 1, 0), (13, 19, 123), (280, 280, 255), (0, 1, 42), (1, 0, 42), (281, 1, 42), (1, 281, 42)] do
    check x k d

end VG.Test.DsaX86SignVerify

run_cmd
  match VG.Test.DsaX86SignVerify.checks with
  | .ok _ => pure ()
  | .error e => Lean.throwError e
