module

public import VerifiedGarbage.Proof.Dsa.X86.CheckingLayout
import VerifiedGarbage.Proof.Dsa.X86.Comb.Checking
import VerifiedGarbage.Proof.Dsa.X86.CheckingOperationCT
import VerifiedGarbage.Proof.Dsa.X86.Comb.CheckingSizedTiming
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
public import VerifiedGarbage.Impl.Dsa.X86.CombGenerate
public import VerifiedGarbage.Proof.Dsa.X86.CheckingABI
public import VerifiedGarbage.Proof.Dsa.X86.Installed

/-! Whole checker timing reuses the common entry and dispatch proof. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem checkingInstalled_generator {s t : State} (A : CheckingABI s)
    (I : Installed (argumentPointer s 4) ((arg s 5).toNat*8) Generate.checkArguments 0 2 3 s t) :
    operandValue t (argumentPointer s 4) (.input .g) (arg s 2).toNat=(checkingParams s).g := by
  have L : 0<(arg s 2).toNat ∧ 0<(arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Params,Bytes⟩ := I.input (by decide : (0,.p)∈Generate.checkArguments) A.keyBound
    (by rw [A.rd,A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr,Gptr,_⟩ := I.pointers (by decide)
  obtain ⟨_,_,_,Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr
  exact (congrArg (fun k : Spec.Dsa.Params => k.g) Value).symm

theorem checkingOperation_agrees {s t : State} (A : CheckingABI s) (B : CheckingABI t)
    (args : ∀ i<6, arg s i=arg t i) (SP : s.gpr .esp=t.gpr .esp)
    (P : (checkingParams s).p=(checkingParams t).p)
    (Q : (checkingParams s).q=(checkingParams t).q)
    (G : (checkingParams s).g=(checkingParams t).g)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa checkParameters s tr sf) (F : Exec isa checkParameters t ur tf) : tr=ur := by
  let L := checkingLayout s A
  have LayoutEq := checkingLayout_eq A B args SP P Q
  have DL := args 2 (by decide)
  refine checkingOperationWith_agrees A B args SP P Q checkSized ?_ E F
  apply (checkingSized_relCT L (arg s 2).toNat
    (by simp [L,checkingLayout,checkingInputs]) (by simp [L,checkingLayout,checkingInputs])
    (by simp [L,checkingLayout,checkingInputs]) (checkingInputs_shape _ _) rfl
    (Nat.le_trans (context_fits A.lengths) (Nat.mul_le_mul_right 8 A.scratchLength))).mono ?_
      (fun _ _ h => h)
  intro u v H
  refine ⟨checkingInstalled_ready A H.1,?_,?_⟩
  · simpa only [L,LayoutEq,DL] using checkingInstalled_ready B H.2
  · have V := checkingInstalled_generator B H.2
    have Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 4 (by decide))
    change operandValue u (argumentPointer s 4) (.input .g) (arg s 2).toNat = _
    rw [checkingInstalled_generator A H.1,G]
    simpa only [L,checkingLayout,Base,DL] using V.symm

end VG.Proof.Dsa.X86.Comb
