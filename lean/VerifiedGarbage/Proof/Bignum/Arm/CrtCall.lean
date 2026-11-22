module

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
import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified

/-! # The private CRT over a shared Montgomery product

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
