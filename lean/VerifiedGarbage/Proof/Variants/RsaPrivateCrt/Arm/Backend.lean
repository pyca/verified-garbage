module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PcVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PdVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PcValid
public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
public import VerifiedGarbage.Proof.Framework.Arm.ScrubFill
import VerifiedGarbage.Proof.Bignum.Arm.R2PublicCT
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Bignum.Arm.CrtCall
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
public import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhase
public import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhaseCT
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.CrtPrecomputedContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target

section

/-! The private CRT over a shared Montgomery product

The window's products are calls to a `MontBackend`'s product
(`TwoExp.sharedMontgomery`), which writes the 48 bytes below the stack the
kernel's callers leave it (`KernelStack`): one CRT proof for every
implementation of the product. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

/-- The window exponentiation whose products call `b`'s. -/
def callKernel (b : MontBackend) : WindowKernel where
  code := CrtCall.phase b.name b.mul
  mul := b.callOp
  correct := by
    intro s base ep len w M x eb h fits stack
    refine WP.mono (sharedWindowExpPhase_ok (TwoExp.sharedMontgomery base s.sp len w b.name b.mul
      (fun _ _ _ ho ha hb z input => b.correct z input ho ha hb) b.stackOk) s h ⟨⟨stack.fit, stack.separate⟩, rfl⟩
      fits ?_) ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.separate
      · exact stack.exponent.symm
    · rintro t ⟨ready, value, modulus, r2, one, _, frame, rest⟩
      exact ⟨ready, value, modulus, r2, one, frame, rest⟩
  ct := by
    intro base ep len w M1 M2 x1 x2 eb1 eb2 _ fits positive length
    intro s t tr1 tr2 u v h e1 e2
    exact SharedWindow.phase_ct
      (TwoExp.sharedMontgomery base s.sp len w b.name b.mul
        (fun _ _ _ ho ha hb z input => b.correct z input ho ha hb) b.stackOk)
      (TwoExp.sharedMontgomeryTiming base s.sp len w b.name b.mul
        (fun _ _ _ ho ha hb z input => b.correct z input ho ha hb) b.stackOk
        (fun _ _ _ ho ha hb => b.rawCT ho ha hb))
      fits positive length (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.1.separate
        · exact h.1.2.exponent.symm) s t tr1 tr2 u v
      ⟨⟨h.1.1, ⟨h.1.2.fit, h.1.2.separate⟩, rfl⟩, ⟨h.2.1.1, ⟨h.2.1.2.fit, h.2.1.2.separate⟩, h.2.2.symm⟩, h.2.2⟩
      e1 e2

theorem crtCall_verified (b : MontBackend) :
    Verified target (CrtCall.code b.name b.mul) (Proof.Rsa.privateCrtContract abi 104) :=
  crt_verified (kernel := callKernel b)

theorem crtCall_verifiedP (b : MontBackend) :
    Verified target (CrtCall.codeGiven b.name b.mul) (Proof.Rsa.privateCrtPrecomputedContract abi 104) :=
  crt_verifiedP (kernel := callKernel b)

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

/-- The public precomputation, its squarings calling `b`'s product. -/
def pc (b : MontBackend) : Prog isa := PcFn.codeWith (callPublicPrecomputeKernel b.callOp b.callDbl).code

theorem pcStub : CodeOk (PcFn.codeWith (precomputeWith (r2PublicWith (MontCall.op "" (holeStub 40))
    (MontCall.op "" (holeStub 40) 4 7 4)))) 104 := by
  lit_decide

theorem pcOk (b : MontBackend) : CodeOk (pc b) 104 :=
  (show FillB _ (pc b) by have := b.mulOk; have := b.dblOk; fill_holes).codeOk pcStub

/-- The public operation on precomputed values, its products calling `b`'s. -/
def pd (b : MontBackend) : Prog isa := PdFn.code b.callOp.op

theorem pdStub : CodeOk (PdFn.code (MontCall.op "" (holeStub 40))) 104 := by lit_decide

theorem pdOk (b : MontBackend) : CodeOk (pd b) 104 :=
  (show FillB _ (pd b) by have := b.mulOk; fill_holes).codeOk pdStub

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
  pc := b.caller.code (pc b)
  pcVerified := b.caller.verified (precompute_verified (kernel := callPublicPrecomputeKernel b.callOp b.callDbl))
  pcStack := (b.callerOk _ _ (pcOk b)).1
  pcNoIcall := (b.callerOk _ _ (pcOk b)).2
  pdName := "vg_rsa_public_precomputed_checked" ++ b.suffix
  pd := b.caller.code (pd b)
  pdVerified := b.caller.verified (pd_verified b.callOp)
  pdStack := (b.callerOk _ _ (pdOk b)).1
  pdNoIcall := (b.callerOk _ _ (pdOk b)).2
  suffix := b.suffix
  features := b.features

end VG.Proof.Variants.RsaPrivateCrt.Arm.Backend
