module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.ApplyCT
public import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.ApplyCT
meta import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Init
meta import VerifiedGarbage.Proof.ChaCha20.Arm.Lit

/-!
# ChaCha20's functions on ARMv7, as emitted

`vg_chacha20_init`, `vg_chacha20_set_nonce` and `vg_chacha20_apply` with
their cleanup (`Impl.ChaCha20.Arm.Fn`): each returns with the registers a
callee may change, but the result, and the flags set to constants. They have
no frames: `apply` and the block and XOR functions it calls keep the
registers they save in the streaming state, a buffer (`Code.noFrames`,
evaluated by `lit_decide`). `Fn` below has the theorem of each: it meets its
contract in constant time and returns without secret residue
(`VerifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.Arm.Scrub

open VG VG.Arm

theorem init_noFrames : Impl.ChaCha20.Arm.Stream.init.noFrames = true := by lit_decide

theorem setNonce_noFrames : Impl.ChaCha20.Arm.Stream.setNonce.noFrames = true := by lit_decide

theorem apply_noFrames : Impl.ChaCha20.Arm.Stream.apply.noFrames = true := by lit_decide

end VG.Proof.ChaCha20.Arm.Scrub

namespace VG.Proof.ChaCha20.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_chacha20_init`. -/
theorem init : VerifiedScrubbed target Impl.ChaCha20.Arm.Fn.init (Spec.ChaCha20.initContract abi) 0 :=
  verifiedScrubbed (api := Spec.ChaCha20.initApi)
    { code := Impl.ChaCha20.Arm.Stream.init, verified := Proof.ChaCha20.Arm.Stream.init_verified }
    Scrub.init_noFrames

/-- `vg_chacha20_set_nonce`. -/
theorem setNonce :
    VerifiedScrubbed target Impl.ChaCha20.Arm.Fn.setNonce (Spec.ChaCha20.setNonceContract abi) 0 :=
  verifiedScrubbed (api := Spec.ChaCha20.setNonceApi)
    { code := Impl.ChaCha20.Arm.Stream.setNonce, verified := Proof.ChaCha20.Arm.Stream.setNonce_verified }
    Scrub.setNonce_noFrames

/-- `vg_chacha20_apply`. -/
theorem apply :
    VerifiedScrubbed target Impl.ChaCha20.Arm.Fn.apply (Spec.ChaCha20.applyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.ChaCha20.applyApi)
    { code := Impl.ChaCha20.Arm.Stream.apply, verified := Proof.ChaCha20.Arm.Stream.apply_verified }
    Scrub.apply_noFrames

end VG.Proof.ChaCha20.Arm.Fn
