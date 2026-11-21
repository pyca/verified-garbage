module

public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Frame
public import VerifiedGarbage.Proof.AesGcm.X86.Scrub
public import VerifiedGarbage.Impl.Sm4Gcm.X86.Fn
import VerifiedGarbage.Proof.Sm4Gcm.Scratch
import VerifiedGarbage.Proof.Sm4.X86.Lit
import VerifiedGarbage.Proof.Sm4.X86.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.Frame
meta import VerifiedGarbage.Proof.AesGcm.X86.Scrub
meta import VerifiedGarbage.Impl.Sm4Gcm.X86.Fn
meta import VerifiedGarbage.Proof.Sm4Gcm.Scratch
meta import VerifiedGarbage.Proof.Sm4.X86.Lit
meta import VerifiedGarbage.Proof.Sm4.X86.Ctr32Lit
meta import VerifiedGarbage.Proof.Sm4.X86.LayersLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# SM4-GCM on x86 (32-bit), without secret residue

Every function of SM4-GCM on x86, as emitted (`Impl.Sm4Gcm.X86.Fn`), is its
code in its frame of working space (`withStackScratch`) followed by the
zeroing of the stack its contract reserves below `esp` (that frame, and the
frames of its calls of `vg_sm4_ctr32`, `vg_sm4_expand_key_core` and
`vg_ghash`) and by the clearing of the registers
(`Impl.Scrub.X86.scrubAll`). One theorem each states `VerifiedScrubbed` of
it, for every implementation `v` of `vg_ghash` it calls (`init_scrubbed`,
…), from `X86.Scrub.verifiedScrubbedAll` with:

* the postcondition reading the memory on return only within the key
  context, the state and the buffers (`Proof/Sm4Gcm/Scratch.lean`, for any
  pointer width);
* what the cleanup needs of the code (`scrubFSide`): for `init`, which
  calls no implementation, evaluated once; for the others, for every `v`,
  from SM4-GCM's code with AES-GCM's stub implementations
  (`Proof.AesGcm.X86.Scrub.stub`, whose code is `.block []`), which the
  kernel evaluates once here (`streamEncrypt_side`, …), `vg_ghash`'s own
  facts (`GhashImpl.scrub`, its stack, 0) and `Fill`, which `fill_calls`
  proves of any implementation by walking only SM4-GCM's code.

`vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad`, AES-GCM's code with
AES-GCM's contracts, are AES-GCM's theorems
(`Proof.AesGcm.X86.Scrub.streamInit_scrubbed`, `streamAad_scrubbed`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86.Scrub

open VG VG.X86 VG.X86.Scrub VG.Impl.Sm4Gcm.X86 VG.Proof.Sm4Gcm.X86
open VG.Proof.AesGcm.X86 (GcmImpl withStackScratch_spSafe)
open VG.Proof.AesGcm.X86.Scrub (stub)
open VG.Impl.StackScratch.X86 (withStackScratch)

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.initContract X86.abi stack) (Spec.Sm4.Gcm.initSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.initPostOut_local _)

theorem streamEncryptOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamEncryptContract X86.abi stack) (Spec.Sm4.Gcm.streamCryptSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamEncryptPostOut_local _)

theorem streamDecryptOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamDecryptContract X86.abi stack) (Spec.Sm4.Gcm.streamCryptSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamDecryptPostOut_local _)

theorem streamFinishOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamFinishContract X86.abi stack) (Spec.Sm4.Gcm.streamFinishSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamFinishPostOut_local _)

theorem streamVerifyOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamVerifyContract X86.abi stack) (Spec.Sm4.Gcm.streamVerifySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.streamVerifyPostOut_local _)

theorem sealOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.sealContract X86.abi stack) (Spec.Sm4.Gcm.sealSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4Gcm.sealPostOut_local _)

theorem openOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.openContract X86.abi stack) (Spec.Sm4.Gcm.openSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sm4Gcm.openPostOut_local _)

/-! ## What the cleanup needs of the code -/

-- SM4-GCM's own code, with AES-GCM's stubs, as literals for the kernel's evaluation.
materialize_code initCode := withStackScratch 2576 2 init
materialize_code streamEncryptStub := withStackScratch 2600 8 (streamEncrypt stub)
materialize_code streamDecryptStub := withStackScratch 2600 8 (streamDecrypt stub)
materialize_code streamFinishStub := withStackScratch 2596 7 (streamFinish stub)
materialize_code streamVerifyStub := withStackScratch 2600 8 (streamVerify stub)
materialize_code sealStub := withStackScratch 2600 8 («seal» stub)
materialize_code openStub := withStackScratch 2604 9 («open» stub)

theorem init_side : scrubFSide (withStackScratch 2576 2 init) [] 4112 = true := by lit_decide
theorem streamEncrypt_side : scrubFSide (withStackScratch 2600 8 (streamEncrypt stub)) [] 4136 = true := by
  lit_decide
theorem streamDecrypt_side : scrubFSide (withStackScratch 2600 8 (streamDecrypt stub)) [] 4136 = true := by
  lit_decide
theorem streamFinish_side : scrubFSide (withStackScratch 2596 7 (streamFinish stub)) [] 4132 = true := by
  lit_decide
theorem streamVerify_side : scrubFSide (withStackScratch 2600 8 (streamVerify stub)) [] 4136 = true := by
  lit_decide
theorem seal_side : scrubFSide (withStackScratch 2600 8 («seal» stub)) [] 4136 = true := by
  lit_decide
theorem open_side : scrubFSide (withStackScratch 2604 9 («open» stub)) [] 4140 = true := by
  lit_decide

variable (v : GcmImpl)

theorem streamEncrypt_scrub : scrubFSide (withStackScratch 2600 8 (streamEncrypt v.callees)) [] 4136 = true := by
  have hg : calleeSide v.gh.fn.code 0 = true := calleeSide_of_eq v.gh.stack v.gh.scrub
  exact scrubFSide_of_fill (n := 0) (by fill_calls) streamEncrypt_side

theorem streamDecrypt_scrub : scrubFSide (withStackScratch 2600 8 (streamDecrypt v.callees)) [] 4136 = true := by
  have hg : calleeSide v.gh.fn.code 0 = true := calleeSide_of_eq v.gh.stack v.gh.scrub
  exact scrubFSide_of_fill (n := 0) (by fill_calls) streamDecrypt_side

theorem streamFinish_scrub : scrubFSide (withStackScratch 2596 7 (streamFinish v.callees)) [] 4132 = true := by
  have hg : calleeSide v.gh.fn.code 0 = true := calleeSide_of_eq v.gh.stack v.gh.scrub
  exact scrubFSide_of_fill (n := 0) (by fill_calls) streamFinish_side

theorem streamVerify_scrub : scrubFSide (withStackScratch 2600 8 (streamVerify v.callees)) [] 4136 = true := by
  have hg : calleeSide v.gh.fn.code 0 = true := calleeSide_of_eq v.gh.stack v.gh.scrub
  exact scrubFSide_of_fill (n := 0) (by fill_calls) streamVerify_side

theorem seal_scrub : scrubFSide (withStackScratch 2600 8 («seal» v.callees)) [] 4136 = true := by
  have hg : calleeSide v.gh.fn.code 0 = true := calleeSide_of_eq v.gh.stack v.gh.scrub
  exact scrubFSide_of_fill (n := 0) (by fill_calls) seal_side

theorem open_scrub : scrubFSide (withStackScratch 2604 9 («open» v.callees)) [] 4140 = true := by
  have hg : calleeSide v.gh.fn.code 0 = true := calleeSide_of_eq v.gh.stack v.gh.scrub
  exact scrubFSide_of_fill (n := 0) (by fill_calls) open_side

/-! ## The functions as emitted -/

/-- `vg_sm4_gcm_init`. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.Sm4Gcm.X86.Fn.init (Spec.Sm4.Gcm.initContract X86.abi 4112) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.initApi)
    { code := withStackScratch 2576 2 init
      verified := init_framed
      spSafe := withStackScratch_spSafe init_spSafe }
    (initOut _) (hs := init_side)

/-- `vg_sm4_gcm_stream_encrypt`. -/
theorem streamEncrypt_scrubbed :
    VerifiedScrubbed target (Impl.Sm4Gcm.X86.Fn.streamEncrypt v.callees) (Spec.Sm4.Gcm.streamEncryptContract X86.abi 4136) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.streamEncryptApi)
    { code := withStackScratch 2600 8 (streamEncrypt v.callees)
      verified := streamEncrypt_framed v
      spSafe := withStackScratch_spSafe (streamEncrypt_spSafe v) }
    (streamEncryptOut _) (hs := streamEncrypt_scrub v)

/-- `vg_sm4_gcm_stream_decrypt`. -/
theorem streamDecrypt_scrubbed :
    VerifiedScrubbed target (Impl.Sm4Gcm.X86.Fn.streamDecrypt v.callees) (Spec.Sm4.Gcm.streamDecryptContract X86.abi 4136) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.streamDecryptApi)
    { code := withStackScratch 2600 8 (streamDecrypt v.callees)
      verified := streamDecrypt_framed v
      spSafe := withStackScratch_spSafe (streamDecrypt_spSafe v) }
    (streamDecryptOut _) (hs := streamDecrypt_scrub v)

/-- `vg_sm4_gcm_stream_finish`. -/
theorem streamFinish_scrubbed :
    VerifiedScrubbed target (Impl.Sm4Gcm.X86.Fn.streamFinish v.callees) (Spec.Sm4.Gcm.streamFinishContract X86.abi 4132) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.streamFinishApi)
    { code := withStackScratch 2596 7 (streamFinish v.callees)
      verified := streamFinish_framed v
      spSafe := withStackScratch_spSafe (streamFinish_spSafe v) }
    (streamFinishOut _) (hs := streamFinish_scrub v)

/-- `vg_sm4_gcm_stream_verify`. -/
theorem streamVerify_scrubbed :
    VerifiedScrubbed target (Impl.Sm4Gcm.X86.Fn.streamVerify v.callees) (Spec.Sm4.Gcm.streamVerifyContract X86.abi 4136) 32 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.streamVerifyApi)
    { code := withStackScratch 2600 8 (streamVerify v.callees)
      verified := streamVerify_framed v
      spSafe := withStackScratch_spSafe (streamVerify_spSafe v) }
    (streamVerifyOut _) (hs := streamVerify_scrub v)

/-- `vg_sm4_gcm_seal`. -/
theorem seal_scrubbed :
    VerifiedScrubbed target (Impl.Sm4Gcm.X86.Fn.«seal» v.callees) (Spec.Sm4.Gcm.sealContract X86.abi 4136) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.sealApi)
    { code := withStackScratch 2600 8 («seal» v.callees)
      verified := seal_framed v
      spSafe := withStackScratch_spSafe (seal_spSafe v) }
    (sealOut _) (hs := seal_scrub v)

/-- `vg_sm4_gcm_open`. -/
theorem open_scrubbed :
    VerifiedScrubbed target (Impl.Sm4Gcm.X86.Fn.«open» v.callees) (Spec.Sm4.Gcm.openContract X86.abi 4140) 32 :=
  verifiedScrubbedAll (api := Spec.Sm4.Gcm.openApi)
    { code := withStackScratch 2604 9 («open» v.callees)
      verified := open_framed v
      spSafe := withStackScratch_spSafe (open_spSafe v) }
    (@openOut _) (hs := open_scrub v)

/-! ## `spSafe` of the functions as emitted, which their registrations state -/

theorem init_spSafeF : Impl.Sm4Gcm.X86.Fn.init.all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe init_spSafe)
theorem streamEncrypt_spSafeF : (Impl.Sm4Gcm.X86.Fn.streamEncrypt v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (streamEncrypt_spSafe v))
theorem streamDecrypt_spSafeF : (Impl.Sm4Gcm.X86.Fn.streamDecrypt v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (streamDecrypt_spSafe v))
theorem streamFinish_spSafeF : (Impl.Sm4Gcm.X86.Fn.streamFinish v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (streamFinish_spSafe v))
theorem streamVerify_spSafeF : (Impl.Sm4Gcm.X86.Fn.streamVerify v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (streamVerify_spSafe v))
theorem seal_spSafeF : (Impl.Sm4Gcm.X86.Fn.«seal» v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (seal_spSafe v))
theorem open_spSafeF : (Impl.Sm4Gcm.X86.Fn.«open» v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (open_spSafe v))

end VG.Proof.Sm4Gcm.X86.Scrub
