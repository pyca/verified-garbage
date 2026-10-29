module

public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Impl.Dsa.X86.CombGenerate
public import VerifiedGarbage.Proof.Dsa.X86.CheckingABI
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Core
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Dsa.X86.Installed
public import VerifiedGarbage.Proof.Framework.X86.Spill

import VerifiedGarbage.Proof.Dsa.X86.CheckingSized
import VerifiedGarbage.Proof.Dsa.X86.CheckingOperation
import VerifiedGarbage.Proof.Dsa.X86.CheckingResources
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.Comb.StagePower
import VerifiedGarbage.Proof.Dsa.X86.Comb.CanonicalFrame
import VerifiedGarbage.Proof.Dsa.X86.ValidateOne
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.GenerateDomain
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Dsa.X86.ScheduleFrame
/-! The checker returns its usual result and retains a canonical table on success. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/Parameters.lean`, which only this module imported.
section

/-! The public check constructs a canonical table while checking g^q = 1. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Ecdsa.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem subgroup_ok {base : Addr} {size pLen qLen p q g : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s)
    (G : CallerBuffer s base size (.input .g) pLen)
    (hg : operandValue s base (.input .g) pLen=g)
    (sizeComb : (layout ((pLen+7)/8) ((qLen+3)/4)).size≤size) :
    WP isa (subgroup pLen qLen) s fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf=flagW base (Layout.field .mask) s &&& mask32 (g^q%p=1) ∧
      canonical ((pLen+7)/8) ((qLen+3)/4) p g base sf.mem ∧ ScheduleFrame base size s sf := by
  have L := M.lengths
  have A := M.aligned
  have np : (pLen+7)/8≤48 := by omega
  unfold subgroup Generate.subgroupWith
  refine WP.seq (WP.mono (stagePower_ok true M (G.ready (M.context np))
    (M.qBuffer.ready (M.context np)) (by decide) sizeComb (fun h => Bool.noConfusion h))
    fun t ⟨Mt,V,C,F,E,_⟩ => ?_)
  have Y : operandValue t base (.local VG.Impl.Dsa.Layout.t) pLen=g^q%p := by
    unfold operandValue
    rw [local_pointer Mt.scr (by omega) (Nat.le_trans (Mt.wideFit (by decide)) Mt.extent),
      V,hg,M.qValue,VG.Proof.Dsa.decodeBE_encodeBE]
    exact Nat.lt_trans (Nat.mod_lt _ (by have := M.pLarge; omega)) M.valueBounds.1
  refine WP.mono (validateOne_ok Mt.scr Mt.saved rfl (by omega) (by omega) A.1
    (Mt.wideReady (by decide) np)) fun sf ⟨Ff,K,O⟩ => ?_
  have R := StageFrame.of_frame K (by decide) O np
  have Ef := R.execution (.inr ⟨rfl,rfl⟩)
  have Ct := C rfl
  rw [hg] at Ct
  exact ⟨Mt.keep Ef.mem Ef.keeps (by decide) (by decide),by unfold operandValue at Y; rw [Ff,F,Y],
    canonical_check (supported_widths M.widths) np Ct O,E.trans (Ef.schedule M.extent)⟩

theorem parameters_ok {base : Addr} {size pLen qLen p q g : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s)
    (G : CallerBuffer s base size (.input .g) pLen)
    (hg : operandValue s base (.input .g) pLen=g)
    (sizeComb : (layout ((pLen+7)/8) ((qLen+3)/4)).size≤size) :
    WP isa (parameters pLen qLen) s fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf=flagW base (Layout.field .mask) s &&&
        mask32 ((1<g ∧ g<p) ∧ (p-1)%q=0 ∧ g^q%p=1) ∧
      canonical ((pLen+7)/8) ((qLen+3)/4) p g base sf.mem ∧ ScheduleFrame base size s sf := by
  unfold parameters
  refine WP.seq (WP.mono (generateDomain_ok M G hg) fun t ⟨Mt,F,E⟩ => ?_)
  refine WP.mono (subgroup_ok Mt (E.buffer G (by decide))
    ((E.value G (by decide) M.extent).trans hg) sizeComb) fun sf ⟨Mf,Ff,C,Ef⟩ => ?_
  refine ⟨Mf,?_,C,(E.schedule M.extent).trans Ef⟩
  rw [Ff,F]
  simp only [BitVec.and_assoc,mask32_and,and_assoc]

end VG.Proof.Dsa.X86.Comb
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

def parameterContext (base : Addr) (pLen qLen : Nat) (params : List Byte) (mem : Mem) : Prop :=
  let value := Spec.Dsa.paramsBytes pLen qLen params
  canonical ((pLen+7)/8) ((qLen+3)/4) value.p value.g base mem

def checkContext (s : State) : Mem → Prop :=
  parameterContext (argumentPointer s 4) (arg s 2).toNat (arg s 3).toNat
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)

theorem context_fits {pLen qLen : Nat} (H : Spec.Dsa.lengthsValid pLen qLen) :
    (layout ((pLen+7)/8) ((qLen+3)/4)).size≤Spec.Dsa.scratchWords pLen*8 := by
  unfold Spec.Dsa.lengthsValid at H
  rcases H with ⟨rfl,rfl⟩|⟨rfl,(rfl|rfl|rfl)⟩|⟨rfl,rfl⟩ <;> decide

theorem checkingInstalled_spec {s t : State} (A : CheckingABI s)
    (I : Installed (argumentPointer s 4) ((arg s 5).toNat*8) Generate.checkArguments 0 2 3 s t) :
    WP isa (checkSized (arg s 2).toNat (arg s 3).toNat) t fun sf =>
      (sf.gpr .eax).toNat=(if Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
      Keeps powerClob t sf ∧ StackOutside (t.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat*8) t.mem sf.mem ∧
      (Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)=true → checkContext s sf.mem) ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 4)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 4)) regs Entry.savedRegisters := by
  have L : 0<(arg s 2).toNat ∧ 0<(arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Params,Bytes⟩ := I.input (by decide : (0,.p)∈Generate.checkArguments) A.keyBound
    (by rw [A.rd,A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr,Gptr,_⟩ := I.pointers (by decide)
  obtain ⟨P,Q,G,Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr
  refine checkingSizedWith_spec I.scr A.used A.lengths P Q G rfl rfl rfl
    (by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using A.keyLength) Value
    parameters (checkContext s) ((arg s 5).toNat*8) A.used ?_
  intro u M G hg
  have sizeComb : (layout (((arg s 2).toNat+7)/8) (((arg s 3).toNat+3)/4)).size≤(arg s 5).toNat*8 :=
    Nat.le_trans (context_fits A.lengths) (Nat.mul_le_mul_right 8 A.scratchLength)
  refine WP.mono (parameters_ok M G hg sizeComb) fun v ⟨Mv,F,C,E⟩ => ?_
  refine ⟨Mv,F,E,?_⟩
  unfold checkContext parameterContext
  rw [Value]
  exact C

theorem checkingOperation_spec {s : State} (A : CheckingABI s) :
    WP isa checkParameters s fun sf =>
      (sf.gpr .eax).toNat=(if Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
      abiPreserved s sf ∧
      StackOutside (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat*8) s.mem sf.mem ∧
      sf.rd=s.rd ∧ sf.wr=s.wr ∧
      (Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)=true → checkContext s sf.mem) :=
  checkingOperationWith_spec checkSized checkContext checkingInstalled_spec A

end VG.Proof.Dsa.X86.Comb
