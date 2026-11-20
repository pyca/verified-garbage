module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Sm4Gcm.Arm.Fn
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Frame
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Sm4Gcm.Scratch
import VerifiedGarbage.Proof.Gcm.Arm.Lit
import VerifiedGarbage.Proof.Sm4.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Sm4Gcm.Arm.Fn
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Frame
meta import VerifiedGarbage.Proof.AesGcm.Scratch
meta import VerifiedGarbage.Proof.Sm4Gcm.Scratch
meta import VerifiedGarbage.Proof.Gcm.Arm.Lit
meta import VerifiedGarbage.Proof.Sm4.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM4-GCM on ARMv7, as emitted

Each function is its code with its cleanup (`Impl.Sm4Gcm.Arm.Fn`): the
stack its contract reserves zeroed (2288, 2304 or 2320 bytes, each a frame
size of the model), and the registers a callee may change, but the result,
set to constants. `Fn` below has the theorem of each: it meets its contract
in constant time and returns without secret residue (`VerifiedScrubbed`),
from `Arm.Scrub.verifiedScrubbedF`, which is what its registration binds.

What the cleanup needs of the code (`CodeOk`: its frames, and those of the
internal functions it calls, `vg_ghash`, `vg_sm4_ctr32` and
`vg_sm4_expand_key_core`, within that stack, and no indirect call) is
evaluated by `lit_decide`. The postconditions read the memory on return only
within their buffers (`Arm.Scrub.PostOut`, from the lemmas of
`Proof/Sm4Gcm/Scratch.lean`, and of `Proof/AesGcm/Scratch.lean` for the
streaming init and AAD functions, whose contracts AES-GCM shares). The
theorems are over the law of `vg_ghash` (`Gcm.Arm.GhashLaw`), which the
registration file gives, as for AES-GCM (`Proof/AesGcm/Arm/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Impl.StackScratch.Arm

theorem init_ok : CodeOk (withRegScratch 768 .r2 Impl.Sm4Gcm.Arm.init) 2288 := by lit_decide

theorem seal_ok : CodeOk (withStackScratch 800 4 Impl.Sm4Gcm.Arm.«seal») 2320 := by lit_decide

theorem open_ok : CodeOk (withStackScratch 800 5 Impl.Sm4Gcm.Arm.«open») 2320 := by lit_decide

theorem streamInit_ok : CodeOk (withStackScratch 784 0 Impl.Sm4Gcm.Arm.streamInit) 2304 := by lit_decide

theorem streamAad_ok : CodeOk (withStackScratch 784 2 Impl.Sm4Gcm.Arm.streamAad) 2304 := by lit_decide

theorem streamEncrypt_ok : CodeOk (withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamEncrypt) 2320 := by
  lit_decide

theorem streamDecrypt_ok : CodeOk (withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamDecrypt) 2320 := by
  lit_decide

theorem streamFinish_ok : CodeOk (withStackScratch 800 3 Impl.Sm4Gcm.Arm.streamFinish) 2320 := by
  lit_decide

theorem streamVerify_ok : CodeOk (withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamVerify) 2320 := by
  lit_decide

end VG.Proof.Sm4Gcm.Arm.Scrub

namespace VG.Proof.Sm4Gcm.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Impl.StackScratch.Arm

/-- `vg_sm4_gcm_init`. -/
theorem init : VerifiedScrubbed target Impl.Sm4Gcm.Arm.Fn.init (Spec.Sm4.Gcm.initContract abi 2288) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.Gcm.initApi)
    { code := withRegScratch 768 .r2 Impl.Sm4Gcm.Arm.init, verified := init_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.initPostOut_local _))
    (scrubSideF_of Scrub.init_ok (by decide) _)

variable [VG.Proof.Gcm.Arm.GhashLaw]

/-- `vg_sm4_gcm_seal`. -/
theorem «seal» : VerifiedScrubbed target Impl.Sm4Gcm.Arm.Fn.«seal» (Spec.Sm4.Gcm.sealContract abi 2320) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.Gcm.sealApi)
    { code := withStackScratch 800 4 Impl.Sm4Gcm.Arm.«seal», verified := seal_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.sealPostOut_local _))
    (scrubSideF_of Scrub.seal_ok (by decide) _)

/-- `vg_sm4_gcm_open`. -/
theorem «open» : VerifiedScrubbed target Impl.Sm4Gcm.Arm.Fn.«open» (Spec.Sm4.Gcm.openContract abi 2320) 32 :=
  verifiedScrubbedF (api := Spec.Sm4.Gcm.openApi)
    { code := withStackScratch 800 5 Impl.Sm4Gcm.Arm.«open», verified := open_framed }
    (postOut_of_local (leak := some (Spec.Sm4.Gcm.openLeak abi.ptrBits)) ScrubAbi.plain
      (Proof.Sm4Gcm.openPostOut_local _))
    (scrubSideF_of Scrub.open_ok (by decide) _)

/-- `vg_sm4_gcm_stream_init`. -/
theorem streamInit :
    VerifiedScrubbed target Impl.Sm4Gcm.Arm.Fn.streamInit (Spec.Gcm.streamInitContract abi 2304) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.Gcm.streamInitApi)
    { code := withStackScratch 784 0 Impl.Sm4Gcm.Arm.streamInit, verified := streamInit_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamInitPostOut_local _))
    (scrubSideF_of Scrub.streamInit_ok (by decide) _)

/-- `vg_sm4_gcm_stream_aad`. -/
theorem streamAad :
    VerifiedScrubbed target Impl.Sm4Gcm.Arm.Fn.streamAad (Spec.Gcm.streamAadContract abi 2304) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.Gcm.streamAadApi)
    { code := withStackScratch 784 2 Impl.Sm4Gcm.Arm.streamAad, verified := streamAad_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamAadPostOut_local _))
    (scrubSideF_of Scrub.streamAad_ok (by decide) _)

/-- `vg_sm4_gcm_stream_encrypt`. -/
theorem streamEncrypt :
    VerifiedScrubbed target Impl.Sm4Gcm.Arm.Fn.streamEncrypt (Spec.Sm4.Gcm.streamEncryptContract abi 2320) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.Gcm.streamEncryptApi)
    { code := withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamEncrypt, verified := streamEncrypt_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamEncryptPostOut_local _))
    (scrubSideF_of Scrub.streamEncrypt_ok (by decide) _)

/-- `vg_sm4_gcm_stream_decrypt`. -/
theorem streamDecrypt :
    VerifiedScrubbed target Impl.Sm4Gcm.Arm.Fn.streamDecrypt (Spec.Sm4.Gcm.streamDecryptContract abi 2320) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.Gcm.streamDecryptApi)
    { code := withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamDecrypt, verified := streamDecrypt_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamDecryptPostOut_local _))
    (scrubSideF_of Scrub.streamDecrypt_ok (by decide) _)

/-- `vg_sm4_gcm_stream_finish`. -/
theorem streamFinish :
    VerifiedScrubbed target Impl.Sm4Gcm.Arm.Fn.streamFinish (Spec.Sm4.Gcm.streamFinishContract abi 2320) 0 :=
  verifiedScrubbedF (api := Spec.Sm4.Gcm.streamFinishApi)
    { code := withStackScratch 800 3 Impl.Sm4Gcm.Arm.streamFinish, verified := streamFinish_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamFinishPostOut_local _))
    (scrubSideF_of Scrub.streamFinish_ok (by decide) _)

/-- `vg_sm4_gcm_stream_verify`. -/
theorem streamVerify :
    VerifiedScrubbed target Impl.Sm4Gcm.Arm.Fn.streamVerify (Spec.Sm4.Gcm.streamVerifyContract abi 2320) 32 :=
  verifiedScrubbedF (api := Spec.Sm4.Gcm.streamVerifyApi)
    { code := withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamVerify, verified := streamVerify_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamVerifyPostOut_local _))
    (scrubSideF_of Scrub.streamVerify_ok (by decide) _)

end VG.Proof.Sm4Gcm.Arm.Fn
