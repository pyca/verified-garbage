module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABITable
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateGeometry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABISeparate

/-! # Signature separation yields the exact native candidate frame bounds -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

private theorem disjoint_bounds {a b : Addr} {n k : Nat}
    (_an : a.toNat + n ≤ 2 ^ 64) (_bk : b.toNat + k ≤ 2 ^ 64) (np : 0 < n) (kp : 0 < k)
    (D : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  by_contra bad
  have overlap : a.toNat < b.toNat + k ∧ b.toNat < a.toNat + n := by omega
  by_cases order : a.toNat ≤ b.toNat
  · apply D b
    · change (b - a).toNat + 1 ≤ n
      rw [BitVec.toNat_sub]
      omega
    · change (b - b).toNat + 1 ≤ k
      rw [BitVec.sub_self]; change 0 + 1 ≤ k; omega
  · apply D a
    · change (a - a).toNat + 1 ≤ n
      rw [BitVec.sub_self]; change 0 + 1 ≤ n; omega
    · change (a - b).toNat + 1 ≤ k
      rw [BitVec.toNat_sub]
      omega

theorem CallLayout.privateNat {s : State} (A : CallLayout s) :
    (callEnvironment s).p.toNat = (s.gpr .esp).toNat - 16 := sub_toNat (by have := A.low; omega)

theorem CallLayout.reservedNat {s : State} (A : CallLayout s) :
    (reservedRegion s).base.toNat = (s.gpr .esp).toNat - 152 := by
  change ((s.gpr .esp).setWidth 64 - 152#64).toNat = _
  rw [← Taint.sub_setWidth A.low, BitVec.toNat_setWidth, sub_toNat A.low,
    Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega)]

theorem CallLayout.workspaceStack {s : State} (A : CallLayout s) (Z : CallSizes s) (D : CallSeparation s) :
    (callEnvironment s).p.toNat ≤ (callEnvironment s).base.toNat ∨
    (callEnvironment s).base.toNat + (callEnvironment s).size + 136 ≤ (callEnvironment s).p.toNat := by
  have g := CandidateGeometry.geometry_valid (workspace := (callEnvironment s).base) Z.length Z.capacity
  have nonempty : 0 < (callEnvironment s).size := by
    have := g.headerFit
    change 256 ≤ 8 * (arg s 10).toNat at this
    change 0 < 8 * (arg s 10).toNat
    omega
  have far := D.stackFar (callEnvironment s).workspaceRegion (List.mem_append_left _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have fit : (callEnvironment s).base.toNat + (callEnvironment s).size ≤ 2 ^ 32 := by
    change ((arg s 9).setWidth 64).toNat + 8 * (arg s 10).toNat ≤ 2 ^ 32
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 9).isLt (by decide))]
    exact A.workspaceFit
  have rn : ((s.gpr .esp).setWidth 64 - 152#64).toNat = (s.gpr .esp).toNat - 152 := A.reservedNat
  have bounds := disjoint_bounds (Nat.le_trans fit (by decide)) (n := (callEnvironment s).size) (k := 152)
    (by rw [rn]; have := A.low; have := (s.gpr .esp).isLt; omega) nonempty (by decide) far
  rw [rn] at bounds
  rw [A.privateNat]
  have low := A.low
  change (callEnvironment s).base.toNat + (callEnvironment s).size ≤ (s.gpr .esp).toNat - 152 ∨
    (s.gpr .esp).toNat - 152 + 152 ≤ (callEnvironment s).base.toNat at bounds
  omega

end VG.Proof.RsaKeyGen.X86.Candidate
