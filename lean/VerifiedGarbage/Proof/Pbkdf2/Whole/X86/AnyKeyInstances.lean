module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyEntry
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Sha256.X86.Shared
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyEntry
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Sha256.X86.Shared
meta import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Md5.X86.Lit
meta import VerifiedGarbage.Proof.Pbkdf2.MdHmac
meta import VerifiedGarbage.Proof.Pbkdf2.Memory
meta import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Md5
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Md5
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512_224
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512_224
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512_256
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512_256

/-!
# HMAC's `init` for a key of any length on x86 (32-bit): the instances

The generic proof (`AnyKeyCT.lean`) at each hash function of
`Proof/Pbkdf2/Whole/X86/Instances.lean`, with the functions `pbkdf2` calls
(`md5OKF`, …): the taint checks are evaluated by the kernel, a state
satisfies the shared contract (`Md.X86.Instances.initSat`), and the function
runs in a frame of its own (`anyFramed`), which keeps `esp` (`…_anySp`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86.Any

open VG.X86
open VG.Proof.Pbkdf2.Whole.X86 (md5F sha384F sha512F sha512_224F sha512_256F md5OKF sha384OKF sha512OKF
  sha512_224OKF sha512_256OKF)

/-! ## md5 -/

theorem md5_anyChecks : AnyChecks md5F := by
  refine {
    pro := ⟨?_, ?_⟩
    cmp := ⟨?_, ?_⟩
    hk1 := ⟨?_, ?_⟩
    hk3 := ⟨?_, ?_⟩
    hk5 := ⟨?_, ?_⟩
    hk7 := ⟨?_, ?_⟩
    short := ⟨?_, ?_⟩
    args := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem md5_anySat : ∃ s, (anyScratchContract Spec.Hmac.md5I.S Spec.Hmac.md5I.initAnyKeyScratch).pre s := by
  sig_implies_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.md5I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.md5S, Spec.Hmac.md5, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.Instances.initSat, Md.X86.Instances.initMem] using Md.X86.Instances.initSat 80 128

theorem md5_anyFrameSat : ∃ s, (Spec.Hmac.md5I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.md5I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.initFrameSat, Md.X86.initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using Md.X86.initFrameSat 80

theorem md5_anyNoEsp : md5F.hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true :=
  hmacInitAny_noEsp md5OKF (by decide +kernel)

/-- `init` for a key of any length, verified. -/
theorem md5_anyFramed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.md5I) 4 (2 * Spec.Hmac.md5I.initAnyKeyScratch)
        md5F.hmacInitAny)
      (Spec.Hmac.md5I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.md5I)) :=
  anyFramed (verified md5OKF md5_anyChecks rfl rfl md5_anySat) Proof.Hmac.md5_local (by decide)
    md5_anyFrameSat md5_anyNoEsp (hmacInitAny_stack md5OKF)

theorem md5_anySp :
    (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.md5I) 4 (2 * Spec.Hmac.md5I.initAnyKeyScratch)
      md5F.hmacInitAny).all (fun i => !isa.writesSp i) = true :=
  withStackScratchWiped_spSafe (by rw [all_writesSp_eq]; exact md5_anyNoEsp)

/-- `vg_hmac_md5_init`: `init` for a key of at most a block, or (cold) for any
key, wiped. -/
theorem md5_initF :
    Verified X86.target (initCode Spec.Hmac.md5I Md.X86.md5M.hmacInit md5F) (Spec.Hmac.md5I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.md5I)) :=
  initCode_verified (Md.X86.initFramed Md.X86.Instances.md5_init Md.X86.md5_initFrameSat) md5_anyFramed (by decide)
    md5_anyFrameSat

theorem md5_initSp : (initCode Spec.Hmac.md5I Md.X86.md5M.hmacInit md5F).all (fun i => !isa.writesSp i) = true :=
  initCode_spSafe (Code.all_of_allInstrs (by lit_decide)) (by decide +kernel) md5_anySp

/-! ## sha384 -/

theorem sha384_anyChecks : AnyChecks sha384F := by
  refine {
    pro := ⟨?_, ?_⟩
    cmp := ⟨?_, ?_⟩
    hk1 := ⟨?_, ?_⟩
    hk3 := ⟨?_, ?_⟩
    hk5 := ⟨?_, ?_⟩
    hk7 := ⟨?_, ?_⟩
    short := ⟨?_, ?_⟩
    args := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha384_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha384I.S Spec.Hmac.sha384I.initAnyKeyScratch).pre s := by
  sig_implies_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha384I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.Instances.initSat, Md.X86.Instances.initMem] using Md.X86.Instances.initSat 192 426

theorem sha384_anyFrameSat : ∃ s, (Spec.Hmac.sha384I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha384I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.initFrameSat, Md.X86.initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using Md.X86.initFrameSat 192

theorem sha384_anyNoEsp : sha384F.hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true :=
  hmacInitAny_noEsp sha384OKF (by decide +kernel)

/-- `init` for a key of any length, verified. -/
theorem sha384_anyFramed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha384I) 4 (2 * Spec.Hmac.sha384I.initAnyKeyScratch)
        sha384F.hmacInitAny)
      (Spec.Hmac.sha384I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha384I)) :=
  anyFramed (verified sha384OKF sha384_anyChecks rfl rfl sha384_anySat) Proof.Hmac.sha384_local (by decide)
    sha384_anyFrameSat sha384_anyNoEsp (hmacInitAny_stack sha384OKF)

theorem sha384_anySp :
    (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha384I) 4 (2 * Spec.Hmac.sha384I.initAnyKeyScratch)
      sha384F.hmacInitAny).all (fun i => !isa.writesSp i) = true :=
  withStackScratchWiped_spSafe (by rw [all_writesSp_eq]; exact sha384_anyNoEsp)

/-- `vg_hmac_sha384_init`: `init` for a key of at most a block, or (cold) for any
key, wiped. -/
theorem sha384_initF :
    Verified X86.target (initCode Spec.Hmac.sha384I Md.X86.sha384M.hmacInit sha384F) (Spec.Hmac.sha384I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha384I)) :=
  initCode_verified (Md.X86.initFramed Md.X86.Instances.sha384_init Md.X86.sha384_initFrameSat) sha384_anyFramed (by decide)
    sha384_anyFrameSat

theorem sha384_initSp : (initCode Spec.Hmac.sha384I Md.X86.sha384M.hmacInit sha384F).all (fun i => !isa.writesSp i) = true :=
  initCode_spSafe (Code.all_of_allInstrs (by lit_decide)) (by decide +kernel) sha384_anySp

/-! ## sha512 -/

theorem sha512_anyChecks : AnyChecks sha512F := by
  refine {
    pro := ⟨?_, ?_⟩
    cmp := ⟨?_, ?_⟩
    hk1 := ⟨?_, ?_⟩
    hk3 := ⟨?_, ?_⟩
    hk5 := ⟨?_, ?_⟩
    hk7 := ⟨?_, ?_⟩
    short := ⟨?_, ?_⟩
    args := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha512I.S Spec.Hmac.sha512I.initAnyKeyScratch).pre s := by
  sig_implies_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.Instances.initSat, Md.X86.Instances.initMem] using Md.X86.Instances.initSat 192 426

theorem sha512_anyFrameSat : ∃ s, (Spec.Hmac.sha512I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha512I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.initFrameSat, Md.X86.initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using Md.X86.initFrameSat 192

theorem sha512_anyNoEsp : sha512F.hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true :=
  hmacInitAny_noEsp sha512OKF (by decide +kernel)

/-- `init` for a key of any length, verified. -/
theorem sha512_anyFramed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha512I) 4 (2 * Spec.Hmac.sha512I.initAnyKeyScratch)
        sha512F.hmacInitAny)
      (Spec.Hmac.sha512I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha512I)) :=
  anyFramed (verified sha512OKF sha512_anyChecks rfl rfl sha512_anySat) Proof.Hmac.sha512_local (by decide)
    sha512_anyFrameSat sha512_anyNoEsp (hmacInitAny_stack sha512OKF)

theorem sha512_anySp :
    (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha512I) 4 (2 * Spec.Hmac.sha512I.initAnyKeyScratch)
      sha512F.hmacInitAny).all (fun i => !isa.writesSp i) = true :=
  withStackScratchWiped_spSafe (by rw [all_writesSp_eq]; exact sha512_anyNoEsp)

/-- `vg_hmac_sha512_init`: `init` for a key of at most a block, or (cold) for any
key, wiped. -/
theorem sha512_initF :
    Verified X86.target (initCode Spec.Hmac.sha512I Md.X86.sha512M'.hmacInit sha512F) (Spec.Hmac.sha512I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha512I)) :=
  initCode_verified (Md.X86.initFramed Md.X86.Instances.sha512_init Md.X86.sha512_initFrameSat) sha512_anyFramed (by decide)
    sha512_anyFrameSat

theorem sha512_initSp : (initCode Spec.Hmac.sha512I Md.X86.sha512M'.hmacInit sha512F).all (fun i => !isa.writesSp i) = true :=
  initCode_spSafe (Code.all_of_allInstrs (by lit_decide)) (by decide +kernel) sha512_anySp

/-! ## sha512_224 -/

theorem sha512_224_anyChecks : AnyChecks sha512_224F := by
  refine {
    pro := ⟨?_, ?_⟩
    cmp := ⟨?_, ?_⟩
    hk1 := ⟨?_, ?_⟩
    hk3 := ⟨?_, ?_⟩
    hk5 := ⟨?_, ?_⟩
    hk7 := ⟨?_, ?_⟩
    short := ⟨?_, ?_⟩
    args := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_224_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha512_224I.S Spec.Hmac.sha512_224I.initAnyKeyScratch).pre s := by
  sig_implies_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512_224I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.Instances.initSat, Md.X86.Instances.initMem] using Md.X86.Instances.initSat 192 426

theorem sha512_224_anyFrameSat : ∃ s, (Spec.Hmac.sha512_224I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha512_224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.initFrameSat, Md.X86.initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using Md.X86.initFrameSat 192

theorem sha512_224_anyNoEsp : sha512_224F.hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true :=
  hmacInitAny_noEsp sha512_224OKF (by decide +kernel)

/-- `init` for a key of any length, verified. -/
theorem sha512_224_anyFramed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha512_224I) 4 (2 * Spec.Hmac.sha512_224I.initAnyKeyScratch)
        sha512_224F.hmacInitAny)
      (Spec.Hmac.sha512_224I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha512_224I)) :=
  anyFramed (verified sha512_224OKF sha512_224_anyChecks rfl rfl sha512_224_anySat) Proof.Hmac.sha512_224_local (by decide)
    sha512_224_anyFrameSat sha512_224_anyNoEsp (hmacInitAny_stack sha512_224OKF)

theorem sha512_224_anySp :
    (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha512_224I) 4 (2 * Spec.Hmac.sha512_224I.initAnyKeyScratch)
      sha512_224F.hmacInitAny).all (fun i => !isa.writesSp i) = true :=
  withStackScratchWiped_spSafe (by rw [all_writesSp_eq]; exact sha512_224_anyNoEsp)

/-- `vg_hmac_sha512_224_init`: `init` for a key of at most a block, or (cold) for any
key, wiped. -/
theorem sha512_224_initF :
    Verified X86.target (initCode Spec.Hmac.sha512_224I Md.X86.sha512_224M.hmacInit sha512_224F) (Spec.Hmac.sha512_224I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha512_224I)) :=
  initCode_verified (Md.X86.initFramed Md.X86.Instances.sha512_224_init Md.X86.sha512_224_initFrameSat) sha512_224_anyFramed (by decide)
    sha512_224_anyFrameSat

theorem sha512_224_initSp : (initCode Spec.Hmac.sha512_224I Md.X86.sha512_224M.hmacInit sha512_224F).all (fun i => !isa.writesSp i) = true :=
  initCode_spSafe (Code.all_of_allInstrs (by lit_decide)) (by decide +kernel) sha512_224_anySp

/-! ## sha512_256 -/

theorem sha512_256_anyChecks : AnyChecks sha512_256F := by
  refine {
    pro := ⟨?_, ?_⟩
    cmp := ⟨?_, ?_⟩
    hk1 := ⟨?_, ?_⟩
    hk3 := ⟨?_, ?_⟩
    hk5 := ⟨?_, ?_⟩
    hk7 := ⟨?_, ?_⟩
    short := ⟨?_, ?_⟩
    args := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha512_256_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha512_256I.S Spec.Hmac.sha512_256I.initAnyKeyScratch).pre s := by
  sig_implies_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512_256I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.Instances.initSat, Md.X86.Instances.initMem] using Md.X86.Instances.initSat 192 426

theorem sha512_256_anyFrameSat : ∃ s, (Spec.Hmac.sha512_256I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha512_256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.initFrameSat, Md.X86.initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using Md.X86.initFrameSat 192

theorem sha512_256_anyNoEsp : sha512_256F.hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true :=
  hmacInitAny_noEsp sha512_256OKF (by decide +kernel)

/-- `init` for a key of any length, verified. -/
theorem sha512_256_anyFramed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha512_256I) 4 (2 * Spec.Hmac.sha512_256I.initAnyKeyScratch)
        sha512_256F.hmacInitAny)
      (Spec.Hmac.sha512_256I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha512_256I)) :=
  anyFramed (verified sha512_256OKF sha512_256_anyChecks rfl rfl sha512_256_anySat) Proof.Hmac.sha512_256_local (by decide)
    sha512_256_anyFrameSat sha512_256_anyNoEsp (hmacInitAny_stack sha512_256OKF)

theorem sha512_256_anySp :
    (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha512_256I) 4 (2 * Spec.Hmac.sha512_256I.initAnyKeyScratch)
      sha512_256F.hmacInitAny).all (fun i => !isa.writesSp i) = true :=
  withStackScratchWiped_spSafe (by rw [all_writesSp_eq]; exact sha512_256_anyNoEsp)

/-- `vg_hmac_sha512_256_init`: `init` for a key of at most a block, or (cold) for any
key, wiped. -/
theorem sha512_256_initF :
    Verified X86.target (initCode Spec.Hmac.sha512_256I Md.X86.sha512_256M.hmacInit sha512_256F) (Spec.Hmac.sha512_256I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha512_256I)) :=
  initCode_verified (Md.X86.initFramed Md.X86.Instances.sha512_256_init Md.X86.sha512_256_initFrameSat) sha512_256_anyFramed (by decide)
    sha512_256_anyFrameSat

theorem sha512_256_initSp : (initCode Spec.Hmac.sha512_256I Md.X86.sha512_256M.hmacInit sha512_256F).all (fun i => !isa.writesSp i) = true :=
  initCode_spSafe (Code.all_of_allInstrs (by lit_decide)) (by decide +kernel) sha512_256_anySp

end VG.Proof.Pbkdf2.Whole.X86.Any
