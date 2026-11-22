module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PcVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PdVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PcValid
public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCall
public import VerifiedGarbage.Proof.Framework.Arm.ScrubFill
import VerifiedGarbage.Proof.Bignum.Arm.R2PublicCT
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Bignum.Arm.PublicPrecomputeNormalized`, which only this module used -/

section

/-! Public normalized setup supplies the same kernel interface as the original setup. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

def normalizedPublicPrecomputeKernel : PublicPrecomputeKernel where
  code := precomputeWith r2Public
  correct := by exact precomputeWith_ok ⟨r2Public, r2Public_ok⟩
  ct := by exact precomputePublic_ct ⟨r2Public, r2Public_ok⟩ r2Public_ct

end VG.Proof.Bignum.Arm

end

end


/-!
# `vg_rsa_private_crt` on ARMv7, over each Montgomery product

The variant of the private CRT for a Montgomery product `b`
(`Variants/RsaMont/Arm.lean`): the window's products call `b`'s
(`CrtCall.code`), and `b`'s rewriting of its callers (`MontBackend.caller`)
applies to the CRT and its public precomputation and check, with the
proofs its interface asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.Arm.Backend

open VG.Arm VG.Arm.Scrub VG.Arm.ScrubFill VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

theorem crtStub : CodeOk (CrtCall.code "" (holeStub 40)) 104 := by lit_decide

theorem crtPStub : CodeOk (CrtCall.codeGiven "" (holeStub 40)) 104 := by lit_decide

theorem crtOk (b : MontBackend) : CodeOk (b.caller.code (CrtCall.code b.name b.mul)) 104 :=
  b.callerOk _ _ ((show FillB _ (CrtCall.code b.name b.mul) by have := b.mulOk; fill_holes).codeOk crtStub)

theorem crtPOk (b : MontBackend) : CodeOk (b.caller.code (CrtCall.codeGiven b.name b.mul)) 104 :=
  b.callerOk _ _ ((show FillB _ (CrtCall.codeGiven b.name b.mul) by have := b.mulOk; fill_holes).codeOk crtPStub)

def pc : Prog isa := PcFn.codeWith normalizedPublicPrecomputeKernel.code

theorem pcOk : CodeOk pc 56 := ⟨by decide +kernel, by lit_decide⟩

theorem pdOk : CodeOk PdFn.code 56 := ⟨by decide +kernel, by lit_decide⟩

def variant (b : MontBackend) : Proof.Rsa.Arm.CrtImpl where
  name := "vg_rsa_private_crt" ++ b.suffix
  code := b.caller.code (CrtCall.code b.name b.mul)
  verified := b.caller.verified (crtCall_verified b)
  stack := (crtOk b).1
  crtPName := "vg_rsa_private_crt_precomputed" ++ b.suffix
  crtP := b.caller.code (CrtCall.codeGiven b.name b.mul)
  crtPVerified := b.caller.verified (crtCall_verifiedP b)
  crtPStack := (crtPOk b).1
  crtPNoIcall := (crtPOk b).2
  pcName := Spec.Rsa.publicPrecomputeApi.name ++ b.suffix
  pc := b.caller.code pc
  pcVerified := b.caller.verified (precompute_verified (kernel := normalizedPublicPrecomputeKernel))
  pcStack := (b.callerOk _ _ pcOk).1
  pcNoIcall := (b.callerOk _ _ pcOk).2
  pdName := "vg_rsa_public_precomputed_checked" ++ b.suffix
  pd := b.caller.code PdFn.code
  pdVerified := b.caller.verified pd_verified
  pdStack := (b.callerOk _ _ pdOk).1
  pdNoIcall := (b.callerOk _ _ pdOk).2
  suffix := b.suffix
  features := b.features

end VG.Proof.Variants.RsaPrivateCrt.Arm.Backend
