module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyEntry
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha1
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Sha256.X86.Shared
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyEntry
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha1
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Sha256.X86.Shared

/-!
# HMAC-SHA-1's `init` for a key of any length on x86 (32-bit), for every backend

The generic proof (`AnyKeyCT.lean`) at SHA-1, for any backend
(`Proof/Sha1/X86/Variants/Interface.lean`), with the functions `pbkdf2`
calls (`Sha1.lean`). The taint checks, and that the code keeps `esp`, depend
only on the sizes, so they are evaluated once, for any backend
(`sha1Shape`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86.Any

open VG.X86
open VG.Proof.Sha1.X86.Variants (Backend)

/-! ## sha1 -/

theorem sha1Shape_anyChecks : AnyChecks Whole.X86.sha1Shape := by
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

theorem sha1Shape_anyNoEsp :
    Whole.X86.sha1Shape.hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  decide +kernel

theorem sha1_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha1I.S Spec.Hmac.sha1I.initAnyKeyScratch).pre s := by
  sig_implies_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha1I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha1S, Spec.Hmac.sha1, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.Instances.initSat, Md.X86.Instances.initMem] using Md.X86.Instances.initSat 84 140

theorem sha1_anyFrameSat : ∃ s, (Spec.Hmac.sha1I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha1I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.initFrameSat, Md.X86.initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using Md.X86.initFrameSat 84

theorem sha1_anyNoEsp (v : Backend) : v.F.hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true :=
  hmacInitAny_noEsp (Whole.X86.sha1OKF v) sha1Shape_anyNoEsp

/-- `init` for a key of any length with the backend `v`, verified. -/
theorem sha1_anyFramed (v : Backend) :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha1I) 4 (2 * Spec.Hmac.sha1I.initAnyKeyScratch)
        v.F.hmacInitAny)
      (Spec.Hmac.sha1I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha1I)) :=
  anyFramed (verified (Whole.X86.sha1OKF v) (anyChecks_of_shape (F := v.F) sha1Shape_anyChecks) rfl rfl sha1_anySat)
    Proof.Hmac.sha1_local (by decide) sha1_anyFrameSat (sha1_anyNoEsp v) (hmacInitAny_stack (Whole.X86.sha1OKF v))

theorem sha1_anySp (v : Backend) :
    (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha1I) 4 (2 * Spec.Hmac.sha1I.initAnyKeyScratch)
      v.F.hmacInitAny).all (fun i => !isa.writesSp i) = true :=
  withStackScratchWiped_spSafe (by rw [all_writesSp_eq]; exact sha1_anyNoEsp v)

/-- `vg_hmac_sha1_init` with the backend `v`: `init` for a key of at most a
block, or (cold) for any key, wiped. -/
theorem sha1_initF (v : Backend) :
    Verified X86.target (initCode Spec.Hmac.sha1I v.M.hmacInit v.F) (Spec.Hmac.sha1I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha1I)) :=
  initCode_verified (Md.X86.initFramed v.hmacInit Md.X86.sha1_initFrameSat (Md.X86.noEsp_of v.initNoSp) v.initStack)
    (sha1_anyFramed v) (by decide) sha1_anyFrameSat

theorem sha1_initSp (v : Backend) : (initCode Spec.Hmac.sha1I v.M.hmacInit v.F).all (fun i => !isa.writesSp i) = true :=
  initCode_spSafe v.initSp (by decide +kernel) (sha1_anySp v)

end VG.Proof.Pbkdf2.Whole.X86.Any
