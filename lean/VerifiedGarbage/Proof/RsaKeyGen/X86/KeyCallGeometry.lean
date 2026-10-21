module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSeparation
public import VerifiedGarbage.Proof.Mont.X86.Words
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

private theorem disjoint_bounds {a b : Addr} {n k : Nat}
    (positive : 0 < n) (otherPositive : 0 < k) (D : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) :
    a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  by_contra bad
  by_cases order : a.toNat ≤ b.toNat
  · apply D b
    · change (b - a).toNat + 1 ≤ n
      rw [BitVec.toNat_sub]
      have := a.isLt
      have := b.isLt
      omega
    · change (b - b).toNat + 1 ≤ k
      rw [BitVec.sub_self]
      change 0 + 1 ≤ k
      omega
  · apply D a
    · change (a - a).toNat + 1 ≤ n
      rw [BitVec.sub_self]
      change 0 + 1 ≤ n
      omega
    · change (a - b).toNat + 1 ≤ k
      rw [BitVec.toNat_sub]
      have := a.isLt
      have := b.isLt
      omega

theorem CallLayout.privateNat {s : State} (A : CallLayout s) :
    (callSp s).toNat = (s.gpr .esp).toNat - 16 := sub_toNat (by have := A.low; omega)

theorem CallLayout.reservedNat {s : State} (A : CallLayout s) :
    (reservedRegion s).base.toNat = (s.gpr .esp).toNat - 36 := by
  change ((s.gpr .esp).setWidth 64 - 36#64).toNat = _
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
  have bounds := disjoint_bounds positive (by decide : 0 < 36) D.stackWorkspace
  change (callEnvironment s).base.toNat + (callEnvironment s).size ≤ (reservedRegion s).base.toNat ∨
    (reservedRegion s).base.toNat + 36 ≤ (callEnvironment s).base.toNat at bounds
  rw [A.reservedNat] at bounds
  change 20 ≤ (callSp s).toNat ∧
    ((callSp s).toNat ≤ (callEnvironment s).base.toNat ∨
      (callEnvironment s).base.toNat + (callEnvironment s).size + 20 ≤ (callSp s).toNat)
  rw [A.privateNat]
  have := A.low
  omega

theorem CallLayout.savedSub {s : State} (A : CallLayout s) :
    (⟨(callSp s).setWidth 64, 16⟩ : Region).Sub (reservedRegion s) := by
  have reserved : reservedRegion s = below (s.gpr .esp) 36 := by
    unfold reservedRegion below
    rw [Taint.sub_setWidth A.low]
  rw [reserved]
  exact below_sub (by decide) A.low

end VG.Proof.RsaKeyGen.X86.Key
