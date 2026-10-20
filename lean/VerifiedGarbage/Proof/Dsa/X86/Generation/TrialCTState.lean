module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialState

/-! # Public trial candidates with private witnesses for the original machine state -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen

structure TrialPublic where
  base : Addr
  input : BitVec 32
  table : BitVec 32
  value : Nat
  index : Nat

def TrialAt (len entries : Nat) (p : TrialPublic) (t : State) : Prop :=
  ∃ s, TrialInputs s p.base p.input p.table len entries ∧ trialValue s p.input len = p.value ∧
    TrialLoopInv s p.base p.input p.table len p.index t

def TrialArgsAt (len entries : Nat) (p : TrialPublic) (t : State) : Prop :=
  ∃ s, TrialInputs s p.base p.input p.table len entries ∧ trialValue s p.input len = p.value ∧
    TrialContext s p.base t ∧ t.gpr .esi = BitVec.ofNat 32 (tabEntry p.index) ∧
    t.gpr .edi = BitVec.ofNat 32 (2 ^ 32 / tabEntry p.index) ∧
    t.gpr .ebp = p.input ∧ t.gpr .ecx = BitVec.ofNat 32 (len / 2)

def TrialReducedAt (p : TrialPublic) (t : State) : Prop :=
  TrialFrame t p.base ∧ t.gpr .ebx = BitVec.ofNat 32 (p.value % tabEntry p.index)
end VG.Proof.Dsa.X86.Generation
