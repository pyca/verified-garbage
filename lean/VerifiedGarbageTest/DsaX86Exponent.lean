import VerifiedGarbageTest.DsaX86Mont
import VerifiedGarbage.Impl.Mont.X86.Context
import VerifiedGarbage.Proof.Mont.X86.PowerTwo
import VerifiedGarbage.Proof.Mont.X86.ShiftDown
import VerifiedGarbage.Proof.Mont.X86.ExponentMask
import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Mont.X86.Exponentiate
import VerifiedGarbage.Proof.Mont.X86.PowerTiming
import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.TCB.Axioms

/-! Synthetic differential tests of the exponentiation composition. These
exercise the ISA model; they are separate from the full correctness proof. -/

#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.powerTwo_ok
#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.shiftDown_ok
#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.exponentMask_ok
#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.selectProduct_ok
#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.Context.keep
#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.contextSetup_ok
#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.exponentiate_ok
#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.exponentiate_constantTime
#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.contextSetup_constantTime

namespace VG.Test.DsaX86Exponent
open VG VG.X86 VG.Test.DsaX86Mont VG.Impl.Mont.X86.Dynamic

def check (n modulus a exponent : Nat) : Except String Unit := do
  let base := 0x10000
  let size := contextBytes n
  let ws := (List.range (size / 4)).foldl (fun w i =>
    w.insert (base / 4 + i) (0xa5a5a5a5 : BitVec 32)) ({} : Words)
  let ws := put (put (put ws (base + slot n 0) (2 * n) modulus)
    (base + slot n 5) (2 * n) a) (base + slot n 8) 2 exponent
  let state : State := {
    gpr := fun r => if r == .edi then BitVec.ofNat 32 base else BitVec.ofNat 32 (0xdead00 + r.ctorIdx)
    cf := none, zf := none, sf := none, of := none
    mem := memory ws, rd := [], wr := [⟨BitVec.ofNat 64 base, size⟩] }
  let initialized ← evaluate fuel (contextSetup n) ⟨state, ws⟩
  unless get initialized.words (base + slot n 4) (2 * n) == 2 ^ (128 * n) % modulus do
    throw "R squared setup mismatch"
  let result ← evaluate fuel (exponentiate n 2) initialized
  unless get result.words (base + slot n 6) (2 * n) == Spec.Rsa.powMod a exponent modulus do
    throw s!"exponentiation mismatch: n={n}, m={modulus}, a={a}, e={exponent}"
  unless get result.words (base + slot n 8) 2 == 0 do throw "exponent not consumed"
  unless get result.words (base + slot n 0) (2 * n) == modulus do throw "modulus changed"
  for r in [.edi, .esp] do
    unless result.state.gpr r == state.gpr r do throw "preserved register changed"

def checks : Except String Unit := do
  for (m, a, e) in [(3, 0, 0), (3, 2, 1), (97, 5, 0xffffffff),
      (2 ^ 64 - 1, 2 ^ 64 - 2, 17), (9, 2 ^ 64 - 1, 32)] do
    check 1 m a e
  check 3 (2 ^ 160 - 47) (2 ^ 192 - 1) 257

end VG.Test.DsaX86Exponent

run_cmd
  match VG.Test.DsaX86Exponent.checks with
  | .ok _ => pure ()
  | .error e => Lean.throwError e
