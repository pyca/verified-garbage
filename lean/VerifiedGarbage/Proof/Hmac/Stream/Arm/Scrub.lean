module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Hmac.Stream.Arm.CodeOk
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyInstances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeySha256
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.Hmac.Stream.Arm.CodeOk
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyInstances
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeySha256
meta import VerifiedGarbage.Proof.Hmac.AnyKey
meta import VerifiedGarbage.Proof.Hmac.Scratch
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# HMAC on ARMv7, as emitted

Each hash's HMAC `init` and `finalize` keep their working space in frames
(`withStackScratch`), make no indirect call, and their
postconditions read the memory on return only within their buffers
(`Arm.Scrub.PostOut`, from the lemmas of `Proof/Hmac/AnyKey.lean` and
`Proof/Hmac/Scratch.lean` that the other targets use too: `initOutArm`,
`finOutArm`, once for every hash). Each is emitted followed by a wipe of the
stack its contract reserves and by instructions that set the registers a
callee may change, but the result, and the flags to constants
(`Impl.Hmac.Stream.Arm.Fn`), and `Fn` below states that it returns without
secret residue (`Arm.Scrub.verifiedScrubbedAll`), which its registration binds.
What that cleanup needs of the code follows from what the hash function's
own code gives (`MdOk`, `Proof/Hmac/Stream/Arm/CodeOk.lean`). `init`'s proof
reserves `24 + anyFrame I` bytes, which is no frame size of the model
(`FrameOk`), so its contract reserves the next multiple of 32 that is
(`Arm.Scrub.Verified.stack_le`).

ECDSA's table of HMAC functions (`Proof/Ecdsa/Rfc6979/Arm/Blocks.lean`,
`tableOf`) names the forms that take their working space as an argument
(`vg_hmac_<hash>_init_any_scratch`, `Fns.hmacInitAny`, and
`vg_hmac_<hash>_finalize_scratch`), which are internal functions and not
these: it is unchanged.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

/-- HMAC's `init`'s postcondition reads the memory on return only within its
buffers. -/
theorem initOutArm (I : Spec.Hmac.Instance) (hR : Proof.Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (stack : Nat) : PostOut (I.initAnyKeyContract abi stack) ((Spec.Hmac.initSig I.S).retBits 32) := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Hmac.initPostOut_local I.S _ hR hS)

/-- So does HMAC's `finalize`'s. -/
theorem finOutArm (I : Spec.Hmac.Instance) (stack : Nat) :
    PostOut (I.finalizeContract abi stack) ((Spec.Hmac.finalizeSig I.S).retBits 32) := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Hmac.finalizePostOut_local I.S _)

/-! ## md5 -/

theorem md5_initSatArm : ∃ s, (Spec.Hmac.md5I.initAnyKeyContract abi 1088).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Pbkdf2.Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Pbkdf2.Md.Arm.initFrameSat 80

theorem md5_initArm : Verified target (Pbkdf2.Whole.Arm.initCode Spec.Hmac.md5I Pbkdf2.Md.Arm.md5Md.hmacInit
      Pbkdf2.Whole.Arm.md5F)
    (Spec.Hmac.md5I.initAnyKeyContract abi 1088) := by
  have hv := Pbkdf2.Whole.Arm.Any.md5_initF
  have hs := md5_initSatArm
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract at hv hs ⊢
  exact Verified.stack_le (by decide) hv hs

/-! ## sha1 -/

theorem sha1_initSatArm : ∃ s, (Spec.Hmac.sha1I.initAnyKeyContract abi 1184).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Pbkdf2.Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Pbkdf2.Md.Arm.initFrameSat 84

theorem sha1_initArm : Verified target (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha1I Pbkdf2.Md.Arm.sha1Md.hmacInit
      Pbkdf2.Whole.Arm.sha1F)
    (Spec.Hmac.sha1I.initAnyKeyContract abi 1184) := by
  have hv := Pbkdf2.Whole.Arm.Any.sha1_initF
  have hs := sha1_initSatArm
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract at hv hs ⊢
  exact Verified.stack_le (by decide) hv hs

/-! ## sha224 -/

theorem sha224_initSatArm : ∃ s, (Spec.Hmac.sha224I.initAnyKeyContract abi 1664).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Pbkdf2.Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Pbkdf2.Md.Arm.initFrameSat 96

theorem sha224_initArm : Verified target (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha224I Pbkdf2.Md.Arm.sha224Md.hmacInit
      Pbkdf2.Whole.Arm.sha224F)
    (Spec.Hmac.sha224I.initAnyKeyContract abi 1664) := by
  have hv := Pbkdf2.Whole.Arm.Any.sha224_initF
  have hs := sha224_initSatArm
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract at hv hs ⊢
  exact Verified.stack_le (by decide) hv hs

/-! ## sha256 -/

theorem sha256_initSatArm : ∃ s, (Spec.Hmac.sha256I.initAnyKeyContract abi 1664).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Pbkdf2.Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Pbkdf2.Md.Arm.initFrameSat 96

theorem sha256_initArm : Verified target (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha256I Pbkdf2.Md.Arm.sha256Md.hmacInit
      Pbkdf2.Whole.Arm.sha256F)
    (Spec.Hmac.sha256I.initAnyKeyContract abi 1664) := by
  have hv := Pbkdf2.Whole.Arm.Any.sha256_initF
  have hs := sha256_initSatArm
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract at hv hs ⊢
  exact Verified.stack_le (by decide) hv hs

/-! ## sha384 -/

theorem sha384_initSatArm : ∃ s, (Spec.Hmac.sha384I.initAnyKeyContract abi 3456).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Pbkdf2.Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Pbkdf2.Md.Arm.initFrameSat 192

theorem sha384_initArm : Verified target (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha384I Pbkdf2.Md.Arm.sha384Md.hmacInit
      Pbkdf2.Whole.Arm.sha384F)
    (Spec.Hmac.sha384I.initAnyKeyContract abi 3456) := by
  have hv := Pbkdf2.Whole.Arm.Any.sha384_initF
  have hs := sha384_initSatArm
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract at hv hs ⊢
  exact Verified.stack_le (by decide) hv hs

/-! ## sha512 -/

theorem sha512_initSatArm : ∃ s, (Spec.Hmac.sha512I.initAnyKeyContract abi 3456).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Pbkdf2.Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Pbkdf2.Md.Arm.initFrameSat 192

theorem sha512_initArm : Verified target (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512I Pbkdf2.Md.Arm.sha512Md'.hmacInit
      Pbkdf2.Whole.Arm.sha512F)
    (Spec.Hmac.sha512I.initAnyKeyContract abi 3456) := by
  have hv := Pbkdf2.Whole.Arm.Any.sha512_initF
  have hs := sha512_initSatArm
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract at hv hs ⊢
  exact Verified.stack_le (by decide) hv hs

/-! ## sha512_224 -/

theorem sha512_224_initSatArm : ∃ s, (Spec.Hmac.sha512_224I.initAnyKeyContract abi 3456).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Pbkdf2.Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Pbkdf2.Md.Arm.initFrameSat 192

theorem sha512_224_initArm : Verified target (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512_224I Pbkdf2.Md.Arm.sha512_224Md.hmacInit
      Pbkdf2.Whole.Arm.sha512_224F)
    (Spec.Hmac.sha512_224I.initAnyKeyContract abi 3456) := by
  have hv := Pbkdf2.Whole.Arm.Any.sha512_224_initF
  have hs := sha512_224_initSatArm
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract at hv hs ⊢
  exact Verified.stack_le (by decide) hv hs

/-! ## sha512_256 -/

theorem sha512_256_initSatArm : ∃ s, (Spec.Hmac.sha512_256I.initAnyKeyContract abi 3456).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Pbkdf2.Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Pbkdf2.Md.Arm.initFrameSat 192

theorem sha512_256_initArm : Verified target (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512_256I Pbkdf2.Md.Arm.sha512_256Md.hmacInit
      Pbkdf2.Whole.Arm.sha512_256F)
    (Spec.Hmac.sha512_256I.initAnyKeyContract abi 3456) := by
  have hv := Pbkdf2.Whole.Arm.Any.sha512_256_initF
  have hs := sha512_256_initSatArm
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract at hv hs ⊢
  exact Verified.stack_le (by decide) hv hs

end VG.Proof.Hmac.Stream.Arm.Scrub

namespace VG.Proof.Hmac.Stream.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Proof.Hmac.Stream.Arm VG.Proof.Hmac.Stream.Arm.Scrub

/-- `vg_hmac_md5_init`. -/
theorem initMd5 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.initMd5
    (Spec.Hmac.md5I.initAnyKeyContract abi 1088) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.md5I.initAnyKeyApi)
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.md5I Pbkdf2.Md.Arm.md5Md.hmacInit
        Pbkdf2.Whole.Arm.md5F
      verified := md5_initArm }
    (initOutArm Spec.Hmac.md5I Hmac.md5_local (by decide) _)
    (scrubSideF_of (md5_mdOk.initCode_ok _ (by decide) (by decide)) (by decide) _)

/-- `vg_hmac_md5_finalize`. -/
theorem finalizeMd5 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.finalizeMd5
    (Spec.Hmac.md5I.finalizeContract abi 432) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.md5I.finalizeApi)
    { code := Impl.Hmac.Stream.Arm.finCode Spec.Hmac.md5I Pbkdf2.Md.Arm.md5Md
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.md5_finalize Hmac.md5_local
        Pbkdf2.Md.Arm.md5_finFrameSat }
    (finOutArm Spec.Hmac.md5I _)
    (scrubSideF_of (md5_mdOk.finCode_ok _ (by decide)) (by decide) _)

/-- `vg_hmac_sha1_init`. -/
theorem initSha1 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.initSha1
    (Spec.Hmac.sha1I.initAnyKeyContract abi 1184) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha1I.initAnyKeyApi)
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha1I Pbkdf2.Md.Arm.sha1Md.hmacInit
        Pbkdf2.Whole.Arm.sha1F
      verified := sha1_initArm }
    (initOutArm Spec.Hmac.sha1I Hmac.sha1_local (by decide) _)
    (scrubSideF_of (sha1_mdOk.initCode_ok _ (by decide) (by decide)) (by decide) _)

/-- `vg_hmac_sha1_finalize`. -/
theorem finalizeSha1 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.finalizeSha1
    (Spec.Hmac.sha1I.finalizeContract abi 496) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha1I.finalizeApi)
    { code := Impl.Hmac.Stream.Arm.finCode Spec.Hmac.sha1I Pbkdf2.Md.Arm.sha1Md
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha1_finalize Hmac.sha1_local
        Pbkdf2.Md.Arm.sha1_finFrameSat }
    (finOutArm Spec.Hmac.sha1I _)
    (scrubSideF_of (sha1_mdOk.finCode_ok _ (by decide)) (by decide) _)

/-- `vg_hmac_sha224_init`. -/
theorem initSha224 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.initSha224
    (Spec.Hmac.sha224I.initAnyKeyContract abi 1664) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha224I.initAnyKeyApi)
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha224I Pbkdf2.Md.Arm.sha224Md.hmacInit
        Pbkdf2.Whole.Arm.sha224F
      verified := sha224_initArm }
    (initOutArm Spec.Hmac.sha224I Hmac.sha224_local (by decide) _)
    (scrubSideF_of (sha224_mdOk.initCode_ok _ (by decide) (by decide)) (by decide) _)

/-- `vg_hmac_sha224_finalize`. -/
theorem finalizeSha224 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.finalizeSha224
    (Spec.Hmac.sha224I.finalizeContract abi 880) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha224I.finalizeApi)
    { code := Impl.Hmac.Stream.Arm.finCode Spec.Hmac.sha224I Pbkdf2.Md.Arm.sha224Md
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha224_finalize Hmac.sha224_local
        Pbkdf2.Md.Arm.sha224_finFrameSat }
    (finOutArm Spec.Hmac.sha224I _)
    (scrubSideF_of (sha224_mdOk.finCode_ok _ (by decide)) (by decide) _)

/-- `vg_hmac_sha256_init`. -/
theorem initSha256 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.initSha256
    (Spec.Hmac.sha256I.initAnyKeyContract abi 1664) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha256I.initAnyKeyApi)
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha256I Pbkdf2.Md.Arm.sha256Md.hmacInit
        Pbkdf2.Whole.Arm.sha256F
      verified := sha256_initArm }
    (initOutArm Spec.Hmac.sha256I Hmac.sha256_local (by decide) _)
    (scrubSideF_of (sha256_mdOk.initCode_ok _ (by decide) (by decide)) (by decide) _)

/-- `vg_hmac_sha256_finalize`. -/
theorem finalizeSha256 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.finalizeSha256
    (Spec.Hmac.sha256I.finalizeContract abi 880) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha256I.finalizeApi)
    { code := Impl.Hmac.Stream.Arm.finCode Spec.Hmac.sha256I Pbkdf2.Md.Arm.sha256Md
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha256_finalize Hmac.sha256_local
        Pbkdf2.Md.Arm.sha256_finFrameSat }
    (finOutArm Spec.Hmac.sha256I _)
    (scrubSideF_of (sha256_mdOk.finCode_ok _ (by decide)) (by decide) _)

/-- `vg_hmac_sha384_init`. -/
theorem initSha384 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.initSha384
    (Spec.Hmac.sha384I.initAnyKeyContract abi 3456) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha384I.initAnyKeyApi)
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha384I Pbkdf2.Md.Arm.sha384Md.hmacInit
        Pbkdf2.Whole.Arm.sha384F
      verified := sha384_initArm }
    (initOutArm Spec.Hmac.sha384I Hmac.sha384_local (by decide) _)
    (scrubSideF_of ((sha512_mdOk _ _ _).initCode_ok _ (by decide) (by decide)) (by decide) _)

/-- `vg_hmac_sha384_finalize`. -/
theorem finalizeSha384 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.finalizeSha384
    (Spec.Hmac.sha384I.finalizeContract abi 1904) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha384I.finalizeApi)
    { code := Impl.Hmac.Stream.Arm.finCode Spec.Hmac.sha384I Pbkdf2.Md.Arm.sha384Md
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha384_finalize Hmac.sha384_local
        Pbkdf2.Md.Arm.sha384_finFrameSat }
    (finOutArm Spec.Hmac.sha384I _)
    (scrubSideF_of ((sha512_mdOk _ _ _).finCode_ok _ (by decide)) (by decide) _)

/-- `vg_hmac_sha512_init`. -/
theorem initSha512 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.initSha512
    (Spec.Hmac.sha512I.initAnyKeyContract abi 3456) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512I.initAnyKeyApi)
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512I Pbkdf2.Md.Arm.sha512Md'.hmacInit
        Pbkdf2.Whole.Arm.sha512F
      verified := sha512_initArm }
    (initOutArm Spec.Hmac.sha512I Hmac.sha512_local (by decide) _)
    (scrubSideF_of ((sha512_mdOk _ _ _).initCode_ok _ (by decide) (by decide)) (by decide) _)

/-- `vg_hmac_sha512_finalize`. -/
theorem finalizeSha512 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.finalizeSha512
    (Spec.Hmac.sha512I.finalizeContract abi 1904) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512I.finalizeApi)
    { code := Impl.Hmac.Stream.Arm.finCode Spec.Hmac.sha512I Pbkdf2.Md.Arm.sha512Md'
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha512_finalize Hmac.sha512_local
        Pbkdf2.Md.Arm.sha512_finFrameSat }
    (finOutArm Spec.Hmac.sha512I _)
    (scrubSideF_of ((sha512_mdOk _ _ _).finCode_ok _ (by decide)) (by decide) _)

/-- `vg_hmac_sha512_224_init`. -/
theorem initSha512_224 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.initSha512_224
    (Spec.Hmac.sha512_224I.initAnyKeyContract abi 3456) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_224I.initAnyKeyApi)
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512_224I Pbkdf2.Md.Arm.sha512_224Md.hmacInit
        Pbkdf2.Whole.Arm.sha512_224F
      verified := sha512_224_initArm }
    (initOutArm Spec.Hmac.sha512_224I Hmac.sha512_224_local (by decide) _)
    (scrubSideF_of ((sha512_mdOk _ _ _).initCode_ok _ (by decide) (by decide)) (by decide) _)

/-- `vg_hmac_sha512_224_finalize`. -/
theorem finalizeSha512_224 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.finalizeSha512_224
    (Spec.Hmac.sha512_224I.finalizeContract abi 1904) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_224I.finalizeApi)
    { code := Impl.Hmac.Stream.Arm.finCode Spec.Hmac.sha512_224I Pbkdf2.Md.Arm.sha512_224Md
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha512_224_finalize Hmac.sha512_224_local
        Pbkdf2.Md.Arm.sha512_224_finFrameSat }
    (finOutArm Spec.Hmac.sha512_224I _)
    (scrubSideF_of ((sha512_mdOk _ _ _).finCode_ok _ (by decide)) (by decide) _)

/-- `vg_hmac_sha512_256_init`. -/
theorem initSha512_256 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.initSha512_256
    (Spec.Hmac.sha512_256I.initAnyKeyContract abi 3456) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_256I.initAnyKeyApi)
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512_256I Pbkdf2.Md.Arm.sha512_256Md.hmacInit
        Pbkdf2.Whole.Arm.sha512_256F
      verified := sha512_256_initArm }
    (initOutArm Spec.Hmac.sha512_256I Hmac.sha512_256_local (by decide) _)
    (scrubSideF_of ((sha512_mdOk _ _ _).initCode_ok _ (by decide) (by decide)) (by decide) _)

/-- `vg_hmac_sha512_256_finalize`. -/
theorem finalizeSha512_256 : VerifiedScrubbed target Impl.Hmac.Stream.Arm.Fn.finalizeSha512_256
    (Spec.Hmac.sha512_256I.finalizeContract abi 1904) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_256I.finalizeApi)
    { code := Impl.Hmac.Stream.Arm.finCode Spec.Hmac.sha512_256I Pbkdf2.Md.Arm.sha512_256Md
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha512_256_finalize Hmac.sha512_256_local
        Pbkdf2.Md.Arm.sha512_256_finFrameSat }
    (finOutArm Spec.Hmac.sha512_256I _)
    (scrubSideF_of ((sha512_mdOk _ _ _).finCode_ok _ (by decide)) (by decide) _)

end VG.Proof.Hmac.Stream.Arm.Fn
