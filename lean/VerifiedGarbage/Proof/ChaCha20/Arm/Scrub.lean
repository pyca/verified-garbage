module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.ApplyCT
public import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.ApplyCT
meta import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Init
meta import VerifiedGarbage.Proof.ChaCha20.Arm.Lit

/-!
# ChaCha20 on ARMv7, without secret residue

`vg_chacha20_init`, `vg_chacha20_set_nonce` and `vg_chacha20_apply` have no
frames: `apply` and the block and XOR functions it calls keep the registers
they save in the streaming state, a buffer. Each is registered scrubbed
(`Arm.Scrub.scrubReg`): followed by instructions that set the registers a
callee may change, but the result, and the flags to constants.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.Arm.Scrub

open VG VG.Arm

theorem init_noFrames : Impl.ChaCha20.Arm.Stream.init.noFrames = true := by lit_decide

theorem setNonce_noFrames : Impl.ChaCha20.Arm.Stream.setNonce.noFrames = true := by lit_decide

theorem apply_noFrames : Impl.ChaCha20.Arm.Stream.apply.noFrames = true := by lit_decide

/-- `Spec.ChaCha20.initApi`. -/
def initReg : Registration Spec.ChaCha20.initApi target :=
  Arm.Scrub.scrubReg {
      code := Impl.ChaCha20.Arm.Stream.init
      verified := Proof.ChaCha20.Arm.Stream.init_verified }
    init_noFrames

/-- `Spec.ChaCha20.setNonceApi`. -/
def setNonceReg : Registration Spec.ChaCha20.setNonceApi target :=
  Arm.Scrub.scrubReg {
      code := Impl.ChaCha20.Arm.Stream.setNonce
      verified := Proof.ChaCha20.Arm.Stream.setNonce_verified }
    setNonce_noFrames

/-- `Spec.ChaCha20.applyApi`. -/
def applyReg : Registration Spec.ChaCha20.applyApi target :=
  Arm.Scrub.scrubReg {
      code := Impl.ChaCha20.Arm.Stream.apply
      verified := Proof.ChaCha20.Arm.Stream.apply_verified }
    apply_noFrames

end VG.Proof.ChaCha20.Arm.Scrub
