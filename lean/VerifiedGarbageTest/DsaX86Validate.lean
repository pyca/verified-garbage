import VerifiedGarbageTest.DsaX86Core
import VerifiedGarbage.Proof.Dsa.X86.PublicKey
import VerifiedGarbage.Proof.Dsa.X86.PrivateKey
import VerifiedGarbage.Impl.Dsa.X86.Validate
import VerifiedGarbage.Proof.Dsa.X86.ValidateEqual
import VerifiedGarbage.Proof.Dsa.X86.ValidateLower
import VerifiedGarbage.Proof.Dsa.X86.ValidateRange
import VerifiedGarbage.Proof.Dsa.X86.ValidateOne
import VerifiedGarbage.Proof.Dsa.X86.ValidateZero
import VerifiedGarbage.Proof.Dsa.X86.ValidateMinus

/-! Synthetic differential tests of the algebraic and key checks, using a
small domain so the complete instruction sequences can be exercised cheaply.
These test the post-shape routines; supported-size checks have separate tests. -/

#assert_standard_axioms VG.Proof.Dsa.X86.validateEqual_ok
#assert_standard_axioms VG.Proof.Dsa.X86.lowerTwo_ok
#assert_standard_axioms VG.Proof.Dsa.X86.validateRange_ok
#assert_standard_axioms VG.Proof.Dsa.X86.validateOne_ok
#assert_standard_axioms VG.Proof.Dsa.X86.validateZero_ok
#assert_standard_axioms VG.Proof.Dsa.X86.validateMinus_ok

#assert_standard_axioms VG.Proof.Dsa.X86.publicKey_ok
#assert_standard_axioms VG.Proof.Dsa.X86.privateKey_ok

namespace VG.Test.DsaX86Validate
open VG VG.X86 VG.Test.DsaX86Mont VG.Test.DsaX86Core VG.Impl.Dsa.X86
open VG.Impl.Dsa.Layout

def check (p q g x nonce y : Nat) : Except String Unit := do
  let base := 0x10000
  let input := 0x20000
  let ws := putBE (putBE ({} : Words) input 8 p) (input + 8) 8 q
  let ws := putBE (putBE ws (input + 16) 8 g) (input + 24) 8 y
  let ws := putBE (putBE ws (input + 32) 8 x) (input + 40) 8 nonce
  let ws := [(Field.p, input), (.q, input + 8), (.g, input + 16), (.y, input + 24),
    (.x, input + 32), (.nonce, input + 40), (.mask, 2 ^ 32 - 1)].foldl
      (fun w (f, value) => put w (base + Layout.field f) 1 value) ws
  let state : State := {
    gpr := fun reg => if reg == .edi then BitVec.ofNat 32 base else if reg == .esp then 0x40000 else 0
    unknowns := fun i => BitVec.ofNat 32 (0x60000 + 4 * i)
    cf := none, zf := none, sf := none, of := none
    mem := memory ws, rd := [⟨BitVec.ofNat 64 input, 48⟩], wr := [⟨BitVec.ofNat 64 base, 16384⟩] }
  let publicChecked ← evaluate fuel (Validate.publicKey 8 8) ⟨state, ws⟩
  let publicOK := 1 < g && g < p && 1 < y && y < p && (p - 1) % q == 0 &&
    Spec.Dsa.powMod g q p == 1 && Spec.Dsa.powMod y q p == 1
  unless get publicChecked.words (base + Layout.field .mask) 1 == (if publicOK then 2 ^ 32 - 1 else 0) do
    throw "public algebraic validation mismatch"
  unless getBE publicChecked.words (base + qMinusTwo) 8 == q - 2 do
    throw "Fermat exponent mismatch"
  let privateChecked ← evaluate fuel (Validate.privateKey 8 8) publicChecked
  let privateOK := publicOK && 0 < x && x < q && 0 < nonce && nonce < q && Spec.Dsa.powMod g x p == y
  unless get privateChecked.words (base + Layout.field .mask) 1 == (if privateOK then 2 ^ 32 - 1 else 0) do
    throw "private key or nonce validation mismatch"

def checks : Except String Unit := do
  for (x, nonce) in [(1, 1), (13, 19), (280, 280), (0, 1), (281, 1), (1, 0), (1, 281)] do
    check 563 281 4 x nonce (Spec.Dsa.powMod 4 x 563)
  check 563 281 4 13 19 7
  check 563 283 4 13 19 (Spec.Dsa.powMod 4 13 563)
  check 563 281 1 13 19 1
  check 563 281 563 13 19 0

end VG.Test.DsaX86Validate

run_cmd
  match VG.Test.DsaX86Validate.checks with
  | .ok _ => pure ()
  | .error e => Lean.throwError e
