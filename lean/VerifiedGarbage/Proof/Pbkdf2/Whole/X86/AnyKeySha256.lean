module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyCT
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyCT
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha224
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha224
public import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# HMAC-SHA-256's and HMAC-SHA-224's `init` for a key of any length on x86 (32-bit), for every backend

The generic proof (`AnyKeyCT.lean`) at SHA-256 and SHA-224, for any backend
(`Proof/Sha256/X86/Variants/Interface.lean`), with the functions `pbkdf2`
calls (`Sha256.lean`, `Sha224.lean`). The taint checks, and that the code
keeps `esp`, depend only on the sizes, so they are evaluated once, for any
backend (`sha256Shape`, `sha224Shape`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86.Any

open VG.X86
open VG.Proof.Sha256.X86.Variants (Backend)

/-! ## sha256 -/

theorem sha256Shape_anyChecks : AnyChecks Whole.X86.sha256Shape := by
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

theorem sha256Shape_anyNoEsp :
    Whole.X86.sha256Shape.hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  decide +kernel

theorem sha256_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha256I.S Spec.Hmac.sha256I.initAnyKeyScratch).pre s := by
  sig_implies_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha256I, Spec.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.Instances.initSat, Md.X86.Instances.initMem] using Md.X86.Instances.initSat 96 200

theorem sha256_anyFrameSat : ∃ s, (Spec.Hmac.sha256I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.initFrameSat, Md.X86.initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using Md.X86.initFrameSat 96

theorem sha256_anyNoEsp (v : Backend) : v.F.hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true :=
  hmacInitAny_noEsp (Whole.X86.sha256OKF v) sha256Shape_anyNoEsp

/-- `init` for a key of any length with the backend `v`, verified. -/
theorem sha256_anyFramed (v : Backend) :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha256I) 4 (2 * Spec.Hmac.sha256I.initAnyKeyScratch)
        v.F.hmacInitAny)
      (Spec.Hmac.sha256I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha256I)) :=
  anyFramed (verified (Whole.X86.sha256OKF v) (anyChecks_of_shape (F := v.F) sha256Shape_anyChecks) rfl rfl sha256_anySat)
    Proof.Hmac.sha256_local (by decide) sha256_anyFrameSat (sha256_anyNoEsp v) (hmacInitAny_stack (Whole.X86.sha256OKF v))

theorem sha256_anySp (v : Backend) :
    (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha256I) 4 (2 * Spec.Hmac.sha256I.initAnyKeyScratch)
      v.F.hmacInitAny).all (fun i => !isa.writesSp i) = true :=
  withStackScratchWiped_spSafe (by rw [all_writesSp_eq]; exact sha256_anyNoEsp v)

/-! ## sha224 -/

theorem sha224Shape_anyChecks : AnyChecks Whole.X86.sha224Shape := by
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

theorem sha224Shape_anyNoEsp :
    Whole.X86.sha224Shape.hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  decide +kernel

theorem sha224_anySat : ∃ s, (anyScratchContract Spec.Hmac.sha224I.S Spec.Hmac.sha224I.initAnyKeyScratch).pre s := by
  sig_implies_sat [anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha224I, Spec.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.Instances.initSat, Md.X86.Instances.initMem] using Md.X86.Instances.initSat 96 200

theorem sha224_anyFrameSat : ∃ s, (Spec.Hmac.sha224I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Md.X86.initFrameSat, Md.X86.initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using Md.X86.initFrameSat 96

theorem sha224_anyNoEsp (v : Backend) : v.F224.hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true :=
  hmacInitAny_noEsp (Whole.X86.sha224OKF v) sha224Shape_anyNoEsp

/-- `init` for a key of any length with the backend `v`, verified. -/
theorem sha224_anyFramed (v : Backend) :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha224I) 4 (2 * Spec.Hmac.sha224I.initAnyKeyScratch)
        v.F224.hmacInitAny)
      (Spec.Hmac.sha224I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha224I)) :=
  anyFramed (verified (Whole.X86.sha224OKF v) (anyChecks_of_shape (F := v.F224) sha224Shape_anyChecks) rfl rfl sha224_anySat)
    Proof.Hmac.sha224_local (by decide) sha224_anyFrameSat (sha224_anyNoEsp v) (hmacInitAny_stack (Whole.X86.sha224OKF v))

theorem sha224_anySp (v : Backend) :
    (Impl.StackScratch.X86.withStackScratchWiped (anyFrame Spec.Hmac.sha224I) 4 (2 * Spec.Hmac.sha224I.initAnyKeyScratch)
      v.F224.hmacInitAny).all (fun i => !isa.writesSp i) = true :=
  withStackScratchWiped_spSafe (by rw [all_writesSp_eq]; exact sha224_anyNoEsp v)

end VG.Proof.Pbkdf2.Whole.X86.Any
