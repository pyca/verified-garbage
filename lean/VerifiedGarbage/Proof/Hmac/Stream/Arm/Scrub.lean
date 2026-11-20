module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyInstances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeySha256
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sha1.Arm.Lit
import VerifiedGarbage.Proof.Sha256.Arm.Lit
import VerifiedGarbage.Proof.Sha512.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyInstances
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeySha256
meta import VerifiedGarbage.Proof.Hmac.AnyKey
meta import VerifiedGarbage.Proof.Hmac.Scratch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha1.Arm.Lit
meta import VerifiedGarbage.Proof.Sha256.Arm.Lit
meta import VerifiedGarbage.Proof.Sha512.Arm.Lit

/-!
# HMAC on ARMv7, without secret residue

Each hash's HMAC `init` and `finalize` keep their working space in frames
(`init`'s for a key of any length wiped by its own code,
`withStackScratchWiped`; `finalize`'s not), make no indirect call, and their
postconditions read the memory on return only within their buffers
(`Arm.Scrub.PostOut`, from the lemmas of `Proof/Hmac/AnyKey.lean` and
`Proof/Hmac/Scratch.lean` that the other targets use too: `initOutArm`,
`finOutArm`, once for every hash). Each is registered followed by a wipe of
the stack its contract reserves and by instructions that set the registers a
callee may change, but the result, and the flags to constants
(`Arm.Scrub.scrubRegF`). `init`'s proof reserves `24 + anyFrame I` bytes,
which is no frame size of the model (`FrameOk`), so it is registered with the
next multiple of 32 that is (`Arm.Scrub.Verified.stack_le`).

ECDSA's table of HMAC functions (`Proof/Ecdsa/Rfc6979/Arm/Blocks.lean`,
`tableOf`) names the forms that take their working space as an argument
(`vg_hmac_<hash>_init_scratch`, `vg_hmac_<hash>_finalize_scratch`), which
are internal functions and not these: it is unchanged.
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

materialize_code md5InitCodeArm := Pbkdf2.Whole.Arm.initCode Spec.Hmac.md5I Pbkdf2.Md.Arm.md5Md.hmacInit
      Pbkdf2.Whole.Arm.md5F

materialize_code md5FinCodeArm := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.md5I) 1
      Pbkdf2.Md.Arm.md5Md.hmacFin

theorem md5_initCodeArm :
    armStack (Pbkdf2.Whole.Arm.initCode Spec.Hmac.md5I Pbkdf2.Md.Arm.md5Md.hmacInit
      Pbkdf2.Whole.Arm.md5F) ≤ 1088 ∧
    noIcall (Pbkdf2.Whole.Arm.initCode Spec.Hmac.md5I Pbkdf2.Md.Arm.md5Md.hmacInit
      Pbkdf2.Whole.Arm.md5F) = true := by
  lit_decide

theorem md5_finCodeArm :
    armStack (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.md5I) 1
      Pbkdf2.Md.Arm.md5Md.hmacFin) ≤ 16 + Pbkdf2.Md.Arm.frame Spec.Hmac.md5I ∧
    noIcall (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.md5I) 1
      Pbkdf2.Md.Arm.md5Md.hmacFin) = true := by
  lit_decide

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

/-- `Spec.Hmac.md5I.initAnyKeyApi`, with its stack wiped on return. -/
def md5InitRegArm : Registration Spec.Hmac.md5I.initAnyKeyApi target :=
  scrubRegF
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.md5I Pbkdf2.Md.Arm.md5Md.hmacInit
          Pbkdf2.Whole.Arm.md5F
      verified := md5_initArm }
    md5_initCodeArm.1 md5_initCodeArm.2 (by decide)
    (initOutArm Spec.Hmac.md5I Hmac.md5_local (by decide) _) rfl

/-- `Spec.Hmac.md5I.finalizeApi`, with its stack wiped on return. -/
def md5FinRegArm : Registration Spec.Hmac.md5I.finalizeApi target :=
  scrubRegF
    { code := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.md5I) 1
          Pbkdf2.Md.Arm.md5Md.hmacFin
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.md5_finalize Hmac.md5_local
        Pbkdf2.Md.Arm.md5_finFrameSat }
    md5_finCodeArm.1 md5_finCodeArm.2 (by decide) (finOutArm Spec.Hmac.md5I _) rfl

/-! ## sha1 -/

materialize_code sha1InitCodeArm := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha1I Pbkdf2.Md.Arm.sha1Md.hmacInit
      Pbkdf2.Whole.Arm.sha1F

materialize_code sha1FinCodeArm := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha1I) 1
      Pbkdf2.Md.Arm.sha1Md.hmacFin

theorem sha1_initCodeArm :
    armStack (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha1I Pbkdf2.Md.Arm.sha1Md.hmacInit
      Pbkdf2.Whole.Arm.sha1F) ≤ 1184 ∧
    noIcall (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha1I Pbkdf2.Md.Arm.sha1Md.hmacInit
      Pbkdf2.Whole.Arm.sha1F) = true := by
  lit_decide

theorem sha1_finCodeArm :
    armStack (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha1I) 1
      Pbkdf2.Md.Arm.sha1Md.hmacFin) ≤ 16 + Pbkdf2.Md.Arm.frame Spec.Hmac.sha1I ∧
    noIcall (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha1I) 1
      Pbkdf2.Md.Arm.sha1Md.hmacFin) = true := by
  lit_decide

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

/-- `Spec.Hmac.sha1I.initAnyKeyApi`, with its stack wiped on return. -/
def sha1InitRegArm : Registration Spec.Hmac.sha1I.initAnyKeyApi target :=
  scrubRegF
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha1I Pbkdf2.Md.Arm.sha1Md.hmacInit
          Pbkdf2.Whole.Arm.sha1F
      verified := sha1_initArm }
    sha1_initCodeArm.1 sha1_initCodeArm.2 (by decide)
    (initOutArm Spec.Hmac.sha1I Hmac.sha1_local (by decide) _) rfl

/-- `Spec.Hmac.sha1I.finalizeApi`, with its stack wiped on return. -/
def sha1FinRegArm : Registration Spec.Hmac.sha1I.finalizeApi target :=
  scrubRegF
    { code := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha1I) 1
          Pbkdf2.Md.Arm.sha1Md.hmacFin
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha1_finalize Hmac.sha1_local
        Pbkdf2.Md.Arm.sha1_finFrameSat }
    sha1_finCodeArm.1 sha1_finCodeArm.2 (by decide) (finOutArm Spec.Hmac.sha1I _) rfl

/-! ## sha224 -/

materialize_code sha224InitCodeArm := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha224I Pbkdf2.Md.Arm.sha224Md.hmacInit
      Pbkdf2.Whole.Arm.sha224F

materialize_code sha224FinCodeArm := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I) 1
      Pbkdf2.Md.Arm.sha224Md.hmacFin

theorem sha224_initCodeArm :
    armStack (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha224I Pbkdf2.Md.Arm.sha224Md.hmacInit
      Pbkdf2.Whole.Arm.sha224F) ≤ 1664 ∧
    noIcall (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha224I Pbkdf2.Md.Arm.sha224Md.hmacInit
      Pbkdf2.Whole.Arm.sha224F) = true := by
  lit_decide

theorem sha224_finCodeArm :
    armStack (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I) 1
      Pbkdf2.Md.Arm.sha224Md.hmacFin) ≤ 16 + Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I ∧
    noIcall (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I) 1
      Pbkdf2.Md.Arm.sha224Md.hmacFin) = true := by
  lit_decide

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

/-- `Spec.Hmac.sha224I.initAnyKeyApi`, with its stack wiped on return. -/
def sha224InitRegArm : Registration Spec.Hmac.sha224I.initAnyKeyApi target :=
  scrubRegF
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha224I Pbkdf2.Md.Arm.sha224Md.hmacInit
          Pbkdf2.Whole.Arm.sha224F
      verified := sha224_initArm }
    sha224_initCodeArm.1 sha224_initCodeArm.2 (by decide)
    (initOutArm Spec.Hmac.sha224I Hmac.sha224_local (by decide) _) rfl

/-- `Spec.Hmac.sha224I.finalizeApi`, with its stack wiped on return. -/
def sha224FinRegArm : Registration Spec.Hmac.sha224I.finalizeApi target :=
  scrubRegF
    { code := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I) 1
          Pbkdf2.Md.Arm.sha224Md.hmacFin
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha224_finalize Hmac.sha224_local
        Pbkdf2.Md.Arm.sha224_finFrameSat }
    sha224_finCodeArm.1 sha224_finCodeArm.2 (by decide) (finOutArm Spec.Hmac.sha224I _) rfl

/-! ## sha256 -/

materialize_code sha256InitCodeArm := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha256I Pbkdf2.Md.Arm.sha256Md.hmacInit
      Pbkdf2.Whole.Arm.sha256F

materialize_code sha256FinCodeArm := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I) 1
      Pbkdf2.Md.Arm.sha256Md.hmacFin

theorem sha256_initCodeArm :
    armStack (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha256I Pbkdf2.Md.Arm.sha256Md.hmacInit
      Pbkdf2.Whole.Arm.sha256F) ≤ 1664 ∧
    noIcall (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha256I Pbkdf2.Md.Arm.sha256Md.hmacInit
      Pbkdf2.Whole.Arm.sha256F) = true := by
  lit_decide

theorem sha256_finCodeArm :
    armStack (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I) 1
      Pbkdf2.Md.Arm.sha256Md.hmacFin) ≤ 16 + Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I ∧
    noIcall (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I) 1
      Pbkdf2.Md.Arm.sha256Md.hmacFin) = true := by
  lit_decide

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

/-- `Spec.Hmac.sha256I.initAnyKeyApi`, with its stack wiped on return. -/
def sha256InitRegArm : Registration Spec.Hmac.sha256I.initAnyKeyApi target :=
  scrubRegF
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha256I Pbkdf2.Md.Arm.sha256Md.hmacInit
          Pbkdf2.Whole.Arm.sha256F
      verified := sha256_initArm }
    sha256_initCodeArm.1 sha256_initCodeArm.2 (by decide)
    (initOutArm Spec.Hmac.sha256I Hmac.sha256_local (by decide) _) rfl

/-- `Spec.Hmac.sha256I.finalizeApi`, with its stack wiped on return. -/
def sha256FinRegArm : Registration Spec.Hmac.sha256I.finalizeApi target :=
  scrubRegF
    { code := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I) 1
          Pbkdf2.Md.Arm.sha256Md.hmacFin
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha256_finalize Hmac.sha256_local
        Pbkdf2.Md.Arm.sha256_finFrameSat }
    sha256_finCodeArm.1 sha256_finCodeArm.2 (by decide) (finOutArm Spec.Hmac.sha256I _) rfl

/-! ## sha384 -/

materialize_code sha384InitCodeArm := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha384I Pbkdf2.Md.Arm.sha384Md.hmacInit
      Pbkdf2.Whole.Arm.sha384F

materialize_code sha384FinCodeArm := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha384I) 1
      Pbkdf2.Md.Arm.sha384Md.hmacFin

theorem sha384_initCodeArm :
    armStack (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha384I Pbkdf2.Md.Arm.sha384Md.hmacInit
      Pbkdf2.Whole.Arm.sha384F) ≤ 3456 ∧
    noIcall (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha384I Pbkdf2.Md.Arm.sha384Md.hmacInit
      Pbkdf2.Whole.Arm.sha384F) = true := by
  lit_decide

theorem sha384_finCodeArm :
    armStack (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha384I) 1
      Pbkdf2.Md.Arm.sha384Md.hmacFin) ≤ 16 + Pbkdf2.Md.Arm.frame Spec.Hmac.sha384I ∧
    noIcall (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha384I) 1
      Pbkdf2.Md.Arm.sha384Md.hmacFin) = true := by
  lit_decide

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

/-- `Spec.Hmac.sha384I.initAnyKeyApi`, with its stack wiped on return. -/
def sha384InitRegArm : Registration Spec.Hmac.sha384I.initAnyKeyApi target :=
  scrubRegF
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha384I Pbkdf2.Md.Arm.sha384Md.hmacInit
          Pbkdf2.Whole.Arm.sha384F
      verified := sha384_initArm }
    sha384_initCodeArm.1 sha384_initCodeArm.2 (by decide)
    (initOutArm Spec.Hmac.sha384I Hmac.sha384_local (by decide) _) rfl

/-- `Spec.Hmac.sha384I.finalizeApi`, with its stack wiped on return. -/
def sha384FinRegArm : Registration Spec.Hmac.sha384I.finalizeApi target :=
  scrubRegF
    { code := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha384I) 1
          Pbkdf2.Md.Arm.sha384Md.hmacFin
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha384_finalize Hmac.sha384_local
        Pbkdf2.Md.Arm.sha384_finFrameSat }
    sha384_finCodeArm.1 sha384_finCodeArm.2 (by decide) (finOutArm Spec.Hmac.sha384I _) rfl

/-! ## sha512 -/

materialize_code sha512InitCodeArm := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512I Pbkdf2.Md.Arm.sha512Md'.hmacInit
      Pbkdf2.Whole.Arm.sha512F

materialize_code sha512FinCodeArm := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha512I) 1
      Pbkdf2.Md.Arm.sha512Md'.hmacFin

theorem sha512_initCodeArm :
    armStack (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512I Pbkdf2.Md.Arm.sha512Md'.hmacInit
      Pbkdf2.Whole.Arm.sha512F) ≤ 3456 ∧
    noIcall (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512I Pbkdf2.Md.Arm.sha512Md'.hmacInit
      Pbkdf2.Whole.Arm.sha512F) = true := by
  lit_decide

theorem sha512_finCodeArm :
    armStack (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha512I) 1
      Pbkdf2.Md.Arm.sha512Md'.hmacFin) ≤ 16 + Pbkdf2.Md.Arm.frame Spec.Hmac.sha512I ∧
    noIcall (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha512I) 1
      Pbkdf2.Md.Arm.sha512Md'.hmacFin) = true := by
  lit_decide

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

/-- `Spec.Hmac.sha512I.initAnyKeyApi`, with its stack wiped on return. -/
def sha512InitRegArm : Registration Spec.Hmac.sha512I.initAnyKeyApi target :=
  scrubRegF
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512I Pbkdf2.Md.Arm.sha512Md'.hmacInit
          Pbkdf2.Whole.Arm.sha512F
      verified := sha512_initArm }
    sha512_initCodeArm.1 sha512_initCodeArm.2 (by decide)
    (initOutArm Spec.Hmac.sha512I Hmac.sha512_local (by decide) _) rfl

/-- `Spec.Hmac.sha512I.finalizeApi`, with its stack wiped on return. -/
def sha512FinRegArm : Registration Spec.Hmac.sha512I.finalizeApi target :=
  scrubRegF
    { code := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha512I) 1
          Pbkdf2.Md.Arm.sha512Md'.hmacFin
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha512_finalize Hmac.sha512_local
        Pbkdf2.Md.Arm.sha512_finFrameSat }
    sha512_finCodeArm.1 sha512_finCodeArm.2 (by decide) (finOutArm Spec.Hmac.sha512I _) rfl

/-! ## sha512_224 -/

materialize_code sha512_224InitCodeArm := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512_224I Pbkdf2.Md.Arm.sha512_224Md.hmacInit
      Pbkdf2.Whole.Arm.sha512_224F

materialize_code sha512_224FinCodeArm := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_224I) 1
      Pbkdf2.Md.Arm.sha512_224Md.hmacFin

theorem sha512_224_initCodeArm :
    armStack (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512_224I Pbkdf2.Md.Arm.sha512_224Md.hmacInit
      Pbkdf2.Whole.Arm.sha512_224F) ≤ 3456 ∧
    noIcall (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512_224I Pbkdf2.Md.Arm.sha512_224Md.hmacInit
      Pbkdf2.Whole.Arm.sha512_224F) = true := by
  lit_decide

theorem sha512_224_finCodeArm :
    armStack (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_224I) 1
      Pbkdf2.Md.Arm.sha512_224Md.hmacFin) ≤ 16 + Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_224I ∧
    noIcall (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_224I) 1
      Pbkdf2.Md.Arm.sha512_224Md.hmacFin) = true := by
  lit_decide

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

/-- `Spec.Hmac.sha512_224I.initAnyKeyApi`, with its stack wiped on return. -/
def sha512_224InitRegArm : Registration Spec.Hmac.sha512_224I.initAnyKeyApi target :=
  scrubRegF
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512_224I Pbkdf2.Md.Arm.sha512_224Md.hmacInit
          Pbkdf2.Whole.Arm.sha512_224F
      verified := sha512_224_initArm }
    sha512_224_initCodeArm.1 sha512_224_initCodeArm.2 (by decide)
    (initOutArm Spec.Hmac.sha512_224I Hmac.sha512_224_local (by decide) _) rfl

/-- `Spec.Hmac.sha512_224I.finalizeApi`, with its stack wiped on return. -/
def sha512_224FinRegArm : Registration Spec.Hmac.sha512_224I.finalizeApi target :=
  scrubRegF
    { code := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_224I) 1
          Pbkdf2.Md.Arm.sha512_224Md.hmacFin
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha512_224_finalize Hmac.sha512_224_local
        Pbkdf2.Md.Arm.sha512_224_finFrameSat }
    sha512_224_finCodeArm.1 sha512_224_finCodeArm.2 (by decide) (finOutArm Spec.Hmac.sha512_224I _) rfl

/-! ## sha512_256 -/

materialize_code sha512_256InitCodeArm := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512_256I Pbkdf2.Md.Arm.sha512_256Md.hmacInit
      Pbkdf2.Whole.Arm.sha512_256F

materialize_code sha512_256FinCodeArm := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_256I) 1
      Pbkdf2.Md.Arm.sha512_256Md.hmacFin

theorem sha512_256_initCodeArm :
    armStack (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512_256I Pbkdf2.Md.Arm.sha512_256Md.hmacInit
      Pbkdf2.Whole.Arm.sha512_256F) ≤ 3456 ∧
    noIcall (Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512_256I Pbkdf2.Md.Arm.sha512_256Md.hmacInit
      Pbkdf2.Whole.Arm.sha512_256F) = true := by
  lit_decide

theorem sha512_256_finCodeArm :
    armStack (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_256I) 1
      Pbkdf2.Md.Arm.sha512_256Md.hmacFin) ≤ 16 + Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_256I ∧
    noIcall (Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_256I) 1
      Pbkdf2.Md.Arm.sha512_256Md.hmacFin) = true := by
  lit_decide

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

/-- `Spec.Hmac.sha512_256I.initAnyKeyApi`, with its stack wiped on return. -/
def sha512_256InitRegArm : Registration Spec.Hmac.sha512_256I.initAnyKeyApi target :=
  scrubRegF
    { code := Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha512_256I Pbkdf2.Md.Arm.sha512_256Md.hmacInit
          Pbkdf2.Whole.Arm.sha512_256F
      verified := sha512_256_initArm }
    sha512_256_initCodeArm.1 sha512_256_initCodeArm.2 (by decide)
    (initOutArm Spec.Hmac.sha512_256I Hmac.sha512_256_local (by decide) _) rfl

/-- `Spec.Hmac.sha512_256I.finalizeApi`, with its stack wiped on return. -/
def sha512_256FinRegArm : Registration Spec.Hmac.sha512_256I.finalizeApi target :=
  scrubRegF
    { code := Impl.StackScratch.Arm.withStackScratch (Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_256I) 1
          Pbkdf2.Md.Arm.sha512_256Md.hmacFin
      verified := Pbkdf2.Md.Arm.finFramed Pbkdf2.Md.Arm.Instances.sha512_256_finalize Hmac.sha512_256_local
        Pbkdf2.Md.Arm.sha512_256_finFrameSat }
    sha512_256_finCodeArm.1 sha512_256_finCodeArm.2 (by decide) (finOutArm Spec.Hmac.sha512_256I _) rfl

end VG.Proof.Hmac.Stream.Arm.Scrub
