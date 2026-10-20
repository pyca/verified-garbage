module

public import VerifiedGarbage.Proof.Ffdh.GenerationPolicy
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts

/-! Constant-table requirements follow the reviewed sampling policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

namespace KeyConstants

def consts : GenerationPolicy → List (String × List (BitVec 64))
  | .full => []
  | .vetted => VG.Impl.Ffdh.Arm.VettedGroups.tableConsts

def abi (sampling : GenerationPolicy) : Abi isa := VG.Arm.abi.withConsts (consts sampling)

theorem abi_full : abi .full = VG.Arm.abi := rfl

theorem abi_vetted : abi .vetted = VG.Arm.abi.withConsts VG.Impl.Ffdh.Arm.VettedGroups.tableConsts := rfl

def tablePtr (sampling : GenerationPolicy) (s : State) : BitVec 32 :=
  match sampling with
  | .full => 0
  | .vetted => s.syms VG.Impl.Ffdh.Arm.VettedGroups.tableSym

def regions (sampling : GenerationPolicy) (ptr : BitVec 32) : List Region :=
  match sampling with
  | .full => []
  | .vetted => [⟨State.addr ptr, 8 * VG.Impl.Ffdh.Arm.VettedGroups.tableWords.length⟩]

private theorem singleton_regions (name : String) (words : List (BitVec 64)) (s : State) :
    constRegs [(name, words)] s = [⟨State.addr (s.syms name), 8 * words.length⟩] := rfl

theorem regions_eq (sampling : GenerationPolicy) (s : State) :
    constRegs (consts sampling) s = regions sampling (tablePtr sampling s) := by
  cases sampling with
  | full => rfl
  | vetted =>
    simpa only [consts, VG.Impl.Ffdh.Arm.VettedGroups.tableConsts, regions, tablePtr] using
      singleton_regions VG.Impl.Ffdh.Arm.VettedGroups.tableSym VG.Impl.Ffdh.Arm.VettedGroups.tableWords s

def held (sampling : GenerationPolicy) (ptr : BitVec 32) (mem : Mem) : Prop :=
  Abi.constsHeld mem (fun _ => State.addr ptr) (consts sampling)

@[simp] theorem stackArg_stripConsts (K : List (String × List (BitVec 64))) (s : State) (i : Nat) :
    stackArg (stripConsts K s) i = stackArg s i := rfl

@[simp] theorem stackArgAddr_stripConsts (K : List (String × List (BitVec 64))) (s : State) (i : Nat) :
    stackArgAddr (stripConsts K s) i = stackArgAddr s i := rfl

end KeyConstants
end VG.Proof.Ffdh.Arm
