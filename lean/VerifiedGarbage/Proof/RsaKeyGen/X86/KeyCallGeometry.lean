module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSeparation
public import VerifiedGarbage.Proof.RsaKeyGen.X86.DisjointBounds
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Framework.Offset
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Isa

/-! # The shared reserved frame supplies the native arithmetic stack gap -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86

def callSp (s : State) : BitVec 32 := s.gpr .esp - 16#32

theorem CallLayout.privateNat {s : State} (A : CallLayout s) :
    (callSp s).toNat = (s.gpr .esp).toNat - 16 := sub_toNat (by have := A.low; omega)

theorem CallLayout.reservedNat {s : State} (A : CallLayout s) :
    (reservedRegion s).base.toNat = (s.gpr .esp).toNat - 68 := by
  change ((s.gpr .esp).setWidth 64 - 68#64).toNat = _
  rw [← Taint.sub_setWidth A.low, BitVec.toNat_setWidth, sub_toNat A.low,
    Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega)]

theorem workspace_stack {s : State} (h : contract.pre s) :
    StkOk (callSp s) (callEnvironment s).base (callEnvironment s).size := by
  have A := call_layout h
  have D := call_separation h
  have v := call_valid h
  have bank := v.bankFit
  have positive : 0 < (callEnvironment s).size := by
    unfold VG.Proof.Rsa.X86.Keys.arr VG.Impl.Rsa.X86.Keys.hdr at bank
    omega
  have bounds := disjoint_bounds positive (by decide : 0 < 68) D.stackWorkspace
  change (callEnvironment s).base.toNat + (callEnvironment s).size ≤ (reservedRegion s).base.toNat ∨
    (reservedRegion s).base.toNat + 68 ≤ (callEnvironment s).base.toNat at bounds
  rw [A.reservedNat] at bounds
  change 20 ≤ (callSp s).toNat ∧
    ((callSp s).toNat ≤ (callEnvironment s).base.toNat ∨
      (callEnvironment s).base.toNat + (callEnvironment s).size + 20 ≤ (callSp s).toNat)
  rw [A.privateNat]
  have := A.low
  omega

theorem workspace_deep {s : State} (h : contract.pre s) :
    KeyArgs.DeepStk (callSp s) (callEnvironment s).base (callEnvironment s).size := by
  have A := call_layout h
  have D := call_separation h
  have v := call_valid h
  have bank := v.bankFit
  have positive : 0 < (callEnvironment s).size := by
    unfold VG.Proof.Rsa.X86.Keys.arr VG.Impl.Rsa.X86.Keys.hdr at bank
    omega
  have bounds := disjoint_bounds positive (by decide : 0 < 68) D.stackWorkspace
  change (callEnvironment s).base.toNat + (callEnvironment s).size ≤ (reservedRegion s).base.toNat ∨
    (reservedRegion s).base.toNat + 68 ≤ (callEnvironment s).base.toNat at bounds
  rw [A.reservedNat] at bounds
  change 52 ≤ (callSp s).toNat ∧ (callSp s).toNat + 92 ≤ 2 ^ 32 ∧
    ((callSp s).toNat ≤ (callEnvironment s).base.toNat ∨
      (callEnvironment s).base.toNat + (callEnvironment s).size + 52 ≤ (callSp s).toNat)
  rw [A.privateNat]
  have := A.low
  have := A.argsFit
  omega

theorem CallLayout.savedSub {s : State} (A : CallLayout s) :
    (⟨(callSp s).setWidth 64, 16⟩ : Region).Sub (reservedRegion s) := by
  have reserved : reservedRegion s = below (s.gpr .esp) 68 := by
    unfold reservedRegion below
    rw [Taint.sub_setWidth A.low]
  rw [reserved]
  exact below_sub (by decide) A.low

end VG.Proof.RsaKeyGen.X86.Key
