module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.VerifyVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 verification on RISC-V

The signature and documentation come from the reviewed Ed448 API. The
reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448Verify.RISCV64

def artifacts : List Artifact := [
  Spec.Ed448.verifyApi.artifact RISCV64.target {
    notes := ["Uses baseline integer instructions. Returns 0 at once for a context of 256 bytes \
      or more. Otherwise copies the signature and the public key into a frame of 448 bytes on \
      the stack, writes the first ten bytes of dom4(0, C) there, hashes them, the context, R, \
      the public key and the message with `vg_keccak_absorb`, `vg_keccak_pad` and \
      `vg_keccak_squeeze` (SHAKE256, with the Keccak state in `scratch` and the sponge \
      functions' frames on the stack below this function's) into the frame, reduces the hash \
      modulo L there with `vg_ed448_scalar_reduce`, and returns `vg_ed448_verify_equation`'s \
      result on the copies. The saved callee-saved registers and `ra` are in the frame too, \
      which is not cleared: verification has no secrets."]
    code := Impl.Ed448.RISCV64.Whole.verifyCode
    stack := 1616
    verified := Proof.Ed448.RISCV64.Whole.verify_framed Proof.Ed448.recover_ok Proof.Ed448.verifyEq4_ok }]

end VG.Artifacts.Ed448Verify.RISCV64
