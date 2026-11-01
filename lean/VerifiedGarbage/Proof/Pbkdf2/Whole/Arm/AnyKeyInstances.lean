module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyEntry
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Sha1.Arm.Lit
import VerifiedGarbage.Proof.Sha512.Arm.Lit
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyEntry
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Sha1.Arm.Lit
meta import VerifiedGarbage.Proof.Sha512.Arm.Lit

/-!
# HMAC's `init` for a key of any length on 32-bit ARM: the instances

The generic proof (`AnyKeyCT.lean`) at each hash function, with the functions
`pbkdf2` calls (`Instances.lean`; SHA-256's and SHA-224's are in
`AnyKeySha256.lean`): the taint
checks are evaluated by the kernel, a state satisfies the contract
(`Md.Arm.Instances.initSat`), and the function runs in a frame of its own
(`anyFramed`), and `init` chooses on entry between it and the framed `init`
for a key of at most a block (`initF`, `AnyKeyEntry.lean`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.Arm.Any

open VG.Arm

/-! ## md5 -/

theorem md5_anyChecks : AnyChecks Whole.Arm.md5F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem md5_anySat : ∃ s, (anyScratchContract Spec.Hmac.md5I.S Spec.Hmac.md5I.initAnyKeyScratch).pre s := by
  inst_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.md5I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.md5S, Spec.Hmac.md5, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using Md.Arm.Instances.initSat 80 128

theorem md5_anyFrameSat : ∃ s, (Spec.Hmac.md5I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.md5I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Md.Arm.initFrameSat 80

/-- `init` for a key of any length, verified. -/
theorem md5_anyFramed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped (anyFrame Spec.Hmac.md5I) 0 (2 * Spec.Hmac.md5I.initAnyKeyScratch)
        Whole.Arm.md5F.hmacInitAny)
      (Spec.Hmac.md5I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.md5I)) :=
  anyFramed (verified Whole.Arm.md5OKF md5_anyChecks rfl rfl md5_anySat) Proof.Hmac.md5_local (by decide)
    md5_anyFrameSat

/-- `init`, choosing on entry between `init` for a key of at most a block
(`Md.Arm.initFramed`) and for a key of any length (`md5_anyFramed`), verified. -/
theorem md5_initF :
    Verified Arm.target (initCode Spec.Hmac.md5I Md.Arm.md5Md.hmacInit Whole.Arm.md5F)
      (Spec.Hmac.md5I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.md5I)) :=
  initCode_verified (Md.Arm.initFramed Md.Arm.Instances.md5_init Md.Arm.md5_initFrameSat) md5_anyFramed
    (by decide) (by decide) (by decide) md5_anyFrameSat

/-! ## sha1 -/

theorem sha1_anyChecks : AnyChecks Whole.Arm.sha1F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha1_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha1I.S Spec.Hmac.sha1I.initAnyKeyScratch).pre s := by
  inst_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha1I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha1S, Spec.Hmac.sha1, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using Md.Arm.Instances.initSat 84 140

theorem sha1_anyFrameSat : ∃ s, (Spec.Hmac.sha1I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha1I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Md.Arm.initFrameSat 84

/-- `init` for a key of any length, verified. -/
theorem sha1_anyFramed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped (anyFrame Spec.Hmac.sha1I) 0 (2 * Spec.Hmac.sha1I.initAnyKeyScratch)
        Whole.Arm.sha1F.hmacInitAny)
      (Spec.Hmac.sha1I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha1I)) :=
  anyFramed (verified Whole.Arm.sha1OKF sha1_anyChecks rfl rfl sha1_anySat) Proof.Hmac.sha1_local (by decide)
    sha1_anyFrameSat

/-- `init`, choosing on entry between `init` for a key of at most a block
(`Md.Arm.initFramed`) and for a key of any length (`sha1_anyFramed`), verified. -/
theorem sha1_initF :
    Verified Arm.target (initCode Spec.Hmac.sha1I Md.Arm.sha1Md.hmacInit Whole.Arm.sha1F)
      (Spec.Hmac.sha1I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha1I)) :=
  initCode_verified (Md.Arm.initFramed Md.Arm.Instances.sha1_init Md.Arm.sha1_initFrameSat) sha1_anyFramed
    (by decide) (by decide) (by decide) sha1_anyFrameSat

/-! ## sha384 -/

theorem sha384_anyChecks : AnyChecks Whole.Arm.sha384F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha384_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha384I.S Spec.Hmac.sha384I.initAnyKeyScratch).pre s := by
  inst_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha384I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha384S, Spec.Hmac.sha384, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using Md.Arm.Instances.initSat 192 426

theorem sha384_anyFrameSat : ∃ s, (Spec.Hmac.sha384I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha384I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Md.Arm.initFrameSat 192

/-- `init` for a key of any length, verified. -/
theorem sha384_anyFramed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped (anyFrame Spec.Hmac.sha384I) 0 (2 * Spec.Hmac.sha384I.initAnyKeyScratch)
        Whole.Arm.sha384F.hmacInitAny)
      (Spec.Hmac.sha384I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha384I)) :=
  anyFramed (verified Whole.Arm.sha384OKF sha384_anyChecks rfl rfl sha384_anySat) Proof.Hmac.sha384_local (by decide)
    sha384_anyFrameSat

/-- `init`, choosing on entry between `init` for a key of at most a block
(`Md.Arm.initFramed`) and for a key of any length (`sha384_anyFramed`), verified. -/
theorem sha384_initF :
    Verified Arm.target (initCode Spec.Hmac.sha384I Md.Arm.sha384Md.hmacInit Whole.Arm.sha384F)
      (Spec.Hmac.sha384I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha384I)) :=
  initCode_verified (Md.Arm.initFramed Md.Arm.Instances.sha384_init Md.Arm.sha384_initFrameSat) sha384_anyFramed
    (by decide) (by decide) (by decide) sha384_anyFrameSat

/-! ## sha512 -/

theorem sha512_anyChecks : AnyChecks Whole.Arm.sha512F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha512_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha512I.S Spec.Hmac.sha512I.initAnyKeyScratch).pre s := by
  inst_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha512S, Spec.Hmac.sha512, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using Md.Arm.Instances.initSat 192 426

theorem sha512_anyFrameSat : ∃ s, (Spec.Hmac.sha512I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha512I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Md.Arm.initFrameSat 192

/-- `init` for a key of any length, verified. -/
theorem sha512_anyFramed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped (anyFrame Spec.Hmac.sha512I) 0 (2 * Spec.Hmac.sha512I.initAnyKeyScratch)
        Whole.Arm.sha512F.hmacInitAny)
      (Spec.Hmac.sha512I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha512I)) :=
  anyFramed (verified Whole.Arm.sha512OKF sha512_anyChecks rfl rfl sha512_anySat) Proof.Hmac.sha512_local (by decide)
    sha512_anyFrameSat

/-- `init`, choosing on entry between `init` for a key of at most a block
(`Md.Arm.initFramed`) and for a key of any length (`sha512_anyFramed`), verified. -/
theorem sha512_initF :
    Verified Arm.target (initCode Spec.Hmac.sha512I Md.Arm.sha512Md'.hmacInit Whole.Arm.sha512F)
      (Spec.Hmac.sha512I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha512I)) :=
  initCode_verified (Md.Arm.initFramed Md.Arm.Instances.sha512_init Md.Arm.sha512_initFrameSat) sha512_anyFramed
    (by decide) (by decide) (by decide) sha512_anyFrameSat

/-! ## sha512_224 -/

theorem sha512_224_anyChecks : AnyChecks Whole.Arm.sha512_224F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha512_224_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha512_224I.S Spec.Hmac.sha512_224I.initAnyKeyScratch).pre s := by
  inst_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512_224I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using Md.Arm.Instances.initSat 192 426

theorem sha512_224_anyFrameSat : ∃ s, (Spec.Hmac.sha512_224I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha512_224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Md.Arm.initFrameSat 192

/-- `init` for a key of any length, verified. -/
theorem sha512_224_anyFramed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped (anyFrame Spec.Hmac.sha512_224I) 0 (2 * Spec.Hmac.sha512_224I.initAnyKeyScratch)
        Whole.Arm.sha512_224F.hmacInitAny)
      (Spec.Hmac.sha512_224I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha512_224I)) :=
  anyFramed (verified Whole.Arm.sha512_224OKF sha512_224_anyChecks rfl rfl sha512_224_anySat) Proof.Hmac.sha512_224_local (by decide)
    sha512_224_anyFrameSat

/-- `init`, choosing on entry between `init` for a key of at most a block
(`Md.Arm.initFramed`) and for a key of any length (`sha512_224_anyFramed`), verified. -/
theorem sha512_224_initF :
    Verified Arm.target (initCode Spec.Hmac.sha512_224I Md.Arm.sha512_224Md.hmacInit Whole.Arm.sha512_224F)
      (Spec.Hmac.sha512_224I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha512_224I)) :=
  initCode_verified (Md.Arm.initFramed Md.Arm.Instances.sha512_224_init Md.Arm.sha512_224_initFrameSat) sha512_224_anyFramed
    (by decide) (by decide) (by decide) sha512_224_anyFrameSat

/-! ## sha512_256 -/

theorem sha512_256_anyChecks : AnyChecks Whole.Arm.sha512_256F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha512_256_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha512_256I.S Spec.Hmac.sha512_256I.initAnyKeyScratch).pre s := by
  inst_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512_256I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using Md.Arm.Instances.initSat 192 426

theorem sha512_256_anyFrameSat : ∃ s, (Spec.Hmac.sha512_256I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha512_256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Md.Arm.initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Md.Arm.initFrameSat 192

/-- `init` for a key of any length, verified. -/
theorem sha512_256_anyFramed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped (anyFrame Spec.Hmac.sha512_256I) 0 (2 * Spec.Hmac.sha512_256I.initAnyKeyScratch)
        Whole.Arm.sha512_256F.hmacInitAny)
      (Spec.Hmac.sha512_256I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha512_256I)) :=
  anyFramed (verified Whole.Arm.sha512_256OKF sha512_256_anyChecks rfl rfl sha512_256_anySat) Proof.Hmac.sha512_256_local (by decide)
    sha512_256_anyFrameSat

/-- `init`, choosing on entry between `init` for a key of at most a block
(`Md.Arm.initFramed`) and for a key of any length (`sha512_256_anyFramed`), verified. -/
theorem sha512_256_initF :
    Verified Arm.target (initCode Spec.Hmac.sha512_256I Md.Arm.sha512_256Md.hmacInit Whole.Arm.sha512_256F)
      (Spec.Hmac.sha512_256I.initAnyKeyContract Arm.abi (24 + anyFrame Spec.Hmac.sha512_256I)) :=
  initCode_verified (Md.Arm.initFramed Md.Arm.Instances.sha512_256_init Md.Arm.sha512_256_initFrameSat) sha512_256_anyFramed
    (by decide) (by decide) (by decide) sha512_256_anyFrameSat

end VG.Proof.Pbkdf2.Whole.Arm.Any
