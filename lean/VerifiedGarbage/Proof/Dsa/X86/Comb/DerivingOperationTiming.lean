module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.DeriveBodyTiming
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Deriving
public import VerifiedGarbage.Proof.Dsa.X86.DerivingLayout
import VerifiedGarbage.Proof.Dsa.X86.DerivingOperationCT
import VerifiedGarbage.Proof.Dsa.X86.Comb.DeriveSizedTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.CanonicalFrame
import VerifiedGarbage.Proof.Dsa.X86.Comb.StagePower
import VerifiedGarbage.Proof.Dsa.X86.GenerateParameters
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ABIResources

/-! Whole internal derivation timing retains the validated table through entry and dispatch. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem deriveContext_prefix {s : State} (A : DerivingABI s) {a b : Mem}
    (O : Outside (argumentPointer s 7) 0 8272 a b) (C : deriveContext s a) : deriveContext s b := by
  apply canonical_outs (supported_widths A.lengths) C (Outs.of_outside (rs := [(0,8272)]) O (by simp))
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  apply Or.inr
  change 8272≤context (((arg s 4).toNat+7)/8)
  unfold context; split <;> omega

theorem derivingInstalled_context {s t : State} (A : DerivingABI s)
    (I : Installed (argumentPointer s 7) ((arg s 8).toNat*8) Generate.deriveArguments 2 4 6 s t)
    (C : deriveContext s t.mem) (D : validParameters s) :
    ContextReady (derivingLayout s A) t ∧ DomainReady (derivingLayout s A) t := by
  have L : 0<(arg s 4).toNat ∧ 0<(arg s 6).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Params,Bytes⟩ := I.input (by decide : (2,.p)∈Generate.deriveArguments) A.keyBound
    (by rw [A.rd,A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr,Gptr,_⟩ := I.pointers (by decide)
  obtain ⟨_,_,_,Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr
  have G := (congrArg (fun k : Spec.Dsa.Params => k.g) Value).symm
  change operandValue t (argumentPointer s 7) (.input .g) (arg s 4).toNat=(derivingParams s).g at G
  unfold ContextReady DomainReady
  dsimp only [derivingLayout]
  rw [G]
  refine ⟨C,?_⟩
  have H := (generationChecks_spec (parametersValid_shape D)).mpr D
  exact H

theorem derivingOperation_agrees {s t : State} (A : DerivingABI s) (B : DerivingABI t)
    (args : ∀ i<9, arg s i=arg t i) (SP : s.gpr .esp=t.gpr .esp)
    (P : (derivingParams s).p=(derivingParams t).p)
    (Q : (derivingParams s).q=(derivingParams t).q)
    (Ds : validParameters s) (Dt : validParameters t)
    (Cs : deriveContext s s.mem) (Ct : deriveContext t t.mem)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa deriveKey s tr sf) (F : Exec isa deriveKey t ur tf) : tr=ur := by
  let L := derivingLayout s A
  have LayoutEq := derivingLayout_eq A B args SP P Q
  have DL := args 4 (by decide)
  refine derivingOperationWith_agrees A B args SP P Q deriveSized (deriveContext s) (deriveContext t)
    Cs Ct (deriveContext_prefix A) (deriveContext_prefix B) ?_ E F
  apply (deriveSized_relCT L (arg s 0) (arg s 4).toNat
    (by simp [L,derivingLayout,derivingInputs]) (by simp [L,derivingLayout,derivingInputs])
    (by simp [L,derivingLayout,derivingInputs]) (by simp [L,derivingLayout,derivingInputs])
    (by simp [L,derivingLayout,derivingInputs]) (derivingInputs_shape _ _) rfl
    (by change (arg s 0).toNat+(3*(arg s 4).toNat+2*(arg s 6).toNat)≤_
        rw [←A.outLength]; exact A.outBound)
    (by change Region.Disjoint _ ⟨argumentPointer s 0,3*(arg s 4).toNat+2*(arg s 6).toNat⟩
        rw [←A.outLength]; exact A.outScratch.symm)
    (Nat.le_trans (context_fits A.lengths) (Nat.mul_le_mul_right 8 A.scratchLength))).mono ?_
      (fun _ _ h => h)
  intro u v ⟨I,J,Ci,Cj⟩
  have SI := derivingInstalled_context A I Ci Ds
  have TJ := derivingInstalled_context B J Cj Dt
  refine ⟨derivingInstalled_ready A I,?_,derivingInstalled_output A I,?_,SI.1,?_,SI.2,?_⟩
  · simpa only [L,LayoutEq,DL] using derivingInstalled_ready B J
  · simpa only [L,LayoutEq,args 0 (by decide)] using derivingInstalled_output B J
  · simpa only [L,LayoutEq] using TJ.1
  · simpa only [L,LayoutEq] using TJ.2

end VG.Proof.Dsa.X86.Comb
