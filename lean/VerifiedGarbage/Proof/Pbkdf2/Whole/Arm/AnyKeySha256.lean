module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyEntry
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha224
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Sha256.Arm.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Sha1.Arm.Lit
import VerifiedGarbage.Proof.Sha512.Arm.Lit
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyEntry
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha224
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Sha256.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Sha1.Arm.Lit
meta import VerifiedGarbage.Proof.Sha512.Arm.Lit

/-!
# HMAC-SHA-256's and HMAC-SHA-224's `init` for a key of any length on 32-bit ARM

The generic proof (`AnyKeyCT.lean`) at SHA-256 and SHA-224, with the
functions `pbkdf2` calls (`Sha256.lean`, `Sha224.lean`), as for the other hash
functions (`AnyKeyInstances.lean`): the taint
checks are evaluated by the kernel, a state satisfies the contract
(`Md.Arm.Instances.initSat`), and the function runs in a frame of its own
(`anyFramed`), and `init` chooses on entry between it and the framed `init`
for a key of at most a block (`initF`, `AnyKeyEntry.lean`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.Arm.Any

open VG.Arm

/-! ## sha224 -/

theorem sha224_anyChecks : AnyChecks Whole.Arm.sha224F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha224_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha224I.S Spec.Hmac.sha224I.initAnyKeyScratch).pre s := by
  inst_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha224I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha224S, Spec.Hmac.sha224, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using Md.Arm.Instances.initSat 96 200

theorem sha224_anyFrameSat : ∃ s, (Spec.Hmac.sha224I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Md.Arm.initFrameSat 96

/-- `init` for a key of any length, verified. -/
theorem sha224_anyFramed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped (anyFrame Spec.Hmac.sha224I) 0 (2 * Spec.Hmac.sha224I.initAnyKeyScratch)
        Whole.Arm.sha224F.hmacInitAny)
      (Spec.Hmac.sha224I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha224I)) :=
  anyFramed (verified Whole.Arm.sha224OKF sha224_anyChecks rfl rfl sha224_anySat) Proof.Hmac.sha224_local (by decide)
    sha224_anyFrameSat

/-- `init`, choosing on entry between `init` for a key of at most a block
(`Md.Arm.initFramed`) and for a key of any length (`sha224_anyFramed`), verified. -/
theorem sha224_initF :
    Verified Arm.target (initCode Spec.Hmac.sha224I Md.Arm.sha224Md.hmacInit Whole.Arm.sha224F)
      (Spec.Hmac.sha224I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha224I)) :=
  initCode_verified (Md.Arm.initFramed Md.Arm.Instances.sha224_init Md.Arm.sha224_initFrameSat) sha224_anyFramed
    (by decide) (by decide) (by decide) sha224_anyFrameSat

/-! ## sha256 -/

theorem sha256_anyChecks : AnyChecks Whole.Arm.sha256F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha256_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha256I.S Spec.Hmac.sha256I.initAnyKeyScratch).pre s := by
  inst_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha256I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha256S, Spec.Hmac.sha256, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using Md.Arm.Instances.initSat 96 200

theorem sha256_anyFrameSat : ∃ s, (Spec.Hmac.sha256I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Md.Arm.initFrameSat 96

/-- `init` for a key of any length, verified. -/
theorem sha256_anyFramed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped (anyFrame Spec.Hmac.sha256I) 0 (2 * Spec.Hmac.sha256I.initAnyKeyScratch)
        Whole.Arm.sha256F.hmacInitAny)
      (Spec.Hmac.sha256I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha256I)) :=
  anyFramed (verified Whole.Arm.sha256OKF sha256_anyChecks rfl rfl sha256_anySat) Proof.Hmac.sha256_local (by decide)
    sha256_anyFrameSat

/-- `init`, choosing on entry between `init` for a key of at most a block
(`Md.Arm.initFramed`) and for a key of any length (`sha256_anyFramed`), verified. -/
theorem sha256_initF :
    Verified Arm.target (initCode Spec.Hmac.sha256I Md.Arm.sha256Md.hmacInit Whole.Arm.sha256F)
      (Spec.Hmac.sha256I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha256I)) :=
  initCode_verified (Md.Arm.initFramed Md.Arm.Instances.sha256_init Md.Arm.sha256_initFrameSat) sha256_anyFramed
    (by decide) (by decide) (by decide) sha256_anyFrameSat

end VG.Proof.Pbkdf2.Whole.Arm.Any
