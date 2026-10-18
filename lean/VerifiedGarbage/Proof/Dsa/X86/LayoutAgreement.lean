module

public import VerifiedGarbage.Proof.Dsa.X86.VerifyLayout
public import VerifiedGarbage.Proof.Dsa.X86.SignLayout

/-! # Identical public arguments and domain values select one call layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem verifyLayout_eq {s t : State} (A : VerifyingABI s) (B : VerifyingABI t)
    (args : ∀ i < 10, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (verifyKey s).params.p = (verifyKey t).params.p)
    (Q : (verifyKey s).params.q = (verifyKey t).params.q) : verifyLayout s A = verifyLayout t B := by
  have A0 := args 0 (by decide)
  have A2 := args 2 (by decide)
  have A3 := args 3 (by decide)
  have A4 := args 4 (by decide)
  have A6 := args 6 (by decide)
  have A7 := args 7 (by decide)
  have A8 := args 8 (by decide)
  have A9 := args 9 (by decide)
  have pointers : verifyPointers s = verifyPointers t := by
    funext p
    cases p with
    | input f => cases f <;> simp only [verifyPointers, A0, A2, A3, A4, A6]
    | «local» d => rfl
    | signatureS => simp only [verifyPointers, A4, A3]
  simp only [verifyLayout, SP, argumentPointer, A2, A3, A7, A8, A9, P, Q, pointers]

theorem signLayout_eq {s t : State} (A : SigningABI s) (B : SigningABI t)
    (args : ∀ i < 11, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (signKey s).params.p = (signKey t).params.p)
    (Q : (signKey s).params.q = (signKey t).params.q) : signLayout s A = signLayout t B := by
  have A2 := args 2 (by decide)
  have A4 := args 4 (by decide)
  have A5 := args 5 (by decide)
  have A6 := args 6 (by decide)
  have A7 := args 7 (by decide)
  have A8 := args 8 (by decide)
  have A9 := args 9 (by decide)
  have A10 := args 10 (by decide)
  have pointers : signPointers s = signPointers t := by
    funext p
    cases p with
    | input f => cases f <;> simp only [signPointers, A2, A4, A5, A6, A7]
    | «local» d => rfl
    | signatureS => rfl
  simp only [signLayout, SP, argumentPointer, A4, A6, A8, A9, A10, P, Q, pointers]

end VG.Proof.Dsa.X86
