module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.Framework.Offset

/-! # The sieve's private stack and candidate array fit the outer candidate frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

def Environment.sieveGeometry (E : Environment) : Sieve.Geometry :=
  ⟨E.p - 20#32, E.workspace + 256#32, E.table, E.width, VG.Impl.RsaKeyGen.X86.Sieve.tableCount E.width⟩

theorem Environment.Valid.candidateAddress {E : Environment} (v : E.Valid) :
    (E.workspace + 256#32).setWidth 64 = off E.base 256 := by
  have space := v.slotFit (j := 0) (by decide)
  change 256 + 0 * (8 * (E.width + 2)) + 8 * E.width ≤ E.size at space
  have width := v.width_bounds.1
  have fit := v.workspaceFit
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, off, Environment.base]
  change ((E.workspace.toNat + 256) % 2 ^ 32) % 2 ^ 64 =
    (E.workspace.toNat % 2 ^ 64 + 256) % 2 ^ 64
  have := E.workspace.isLt
  omega

theorem Environment.Valid.sieveCandidateSub {E : Environment} (v : E.Valid) :
    E.sieveGeometry.candidateRegion.Sub E.workspaceRegion := by
  change (⟨(E.workspace + 256#32).setWidth 64, 8 * E.width⟩ : Region).Sub E.workspaceRegion
  rw [v.candidateAddress]
  exact Offset.sub_base E.base (by
    have fit := v.slotFit (j := 0) (by decide)
    change 256 + 0 * (8 * (E.width + 2)) + 8 * E.width ≤ E.size at fit
    omega)

theorem Environment.Valid.sieveStackSub {E : Environment} (v : E.Valid) :
    E.sieveGeometry.stackRegion.Sub (below E.p 96) :=
  below_sub (by decide) v.low

theorem Environment.Valid.sieve_valid {E : Environment} (v : E.Valid) : E.sieveGeometry.Valid := by
  have width := v.width_bounds
  have candidateFit := v.slotFit (j := 0) (by decide)
  have candidateNat : (E.workspace + 256#32).toNat = E.workspace.toNat + 256 := by
    change 256 + 0 * (8 * (E.width + 2)) + 8 * E.width ≤ E.size at candidateFit
    rw [BitVec.toNat_add]
    change (E.workspace.toNat + 256) % 2 ^ 32 = E.workspace.toNat + 256
    have fit := v.workspaceFit
    have := E.workspace.isLt
    omega
  refine ⟨by change 0 < E.width; omega, width.2, ?_, ?_, ?_, v.tableFit, ?_, ?_⟩
  · change 0 < VG.Impl.RsaKeyGen.X86.Sieve.tableCount E.width
    unfold VG.Impl.RsaKeyGen.X86.Sieve.tableCount
    split <;> decide
  · change VG.Impl.RsaKeyGen.X86.Sieve.tableCount E.width ≤ 1024
    unfold VG.Impl.RsaKeyGen.X86.Sieve.tableCount
    split <;> decide
  · change (E.workspace + 256#32).toNat + 8 * E.width ≤ 2 ^ 32
    rw [candidateNat]
    have fit := v.workspaceFit
    change 256 + 0 * (8 * (E.width + 2)) + 8 * E.width ≤ E.size at candidateFit
    omega
  · exact ((v.stackFar E.workspaceRegion (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_left v.sieveCandidateSub).sub_right v.sieveStackSub
  · exact (v.stackFar E.tableRegion (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))).sub_right v.sieveStackSub

end VG.Proof.RsaKeyGen.X86.Candidate
