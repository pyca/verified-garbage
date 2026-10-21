module

public import VerifiedGarbage.Proof.Mont.X86.PowerStep

public import VerifiedGarbage.Impl.Dsa.X86.CombGenerate
public import VerifiedGarbage.Proof.Dsa.X86.CheckingABI
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Core
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Dsa.X86.Installed
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Dsa.X86.Comb.Parameters
import VerifiedGarbage.Proof.Dsa.X86.CheckingSized
import VerifiedGarbage.Proof.Dsa.X86.CheckingOperation
import VerifiedGarbage.Proof.Dsa.X86.CheckingResources
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
import VerifiedGarbage.Proof.Dsa.X86.ABIResources

/-! The checker returns its usual result and retains a canonical table on success. -/

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
