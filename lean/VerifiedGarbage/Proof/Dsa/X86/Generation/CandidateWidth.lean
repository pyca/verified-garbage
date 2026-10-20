module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateWidth
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.RandomScan

/-! # The first-byte width test equals the specification's full-width guard -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem candidateWidth_ok {s : State} {len p : Nat}
    (positive : 0 < len) (bound : p < 256 ^ len)
    (bytes : Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) len = Spec.Dsa.encodeBE len p)
    (read : InRegions (s.rd ++ s.wr) ((s.gpr .esi).setWidth 64) 1) :
    WP isa (.block candidateWidth) s fun t => t.cf = some (decide (p < 2 ^ (8 * len - 1))) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  have first : s.mem ((s.gpr .esi).setWidth 64) = (Spec.Dsa.encodeBE len p).getD 0 0 := by
    rw [← bytes]
    simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, positive]
  have value := VG.Proof.Dsa.Generation.candidate_firstByte positive bound
  rw [← first] at value
  unfold candidateWidth
  have addr : s.ea (at_ .esi 0) = (s.gpr .esi).setWidth 64 := by
    change (s.gpr .esi + 0#32).setWidth 64 = _
    rw [BitVec.add_zero]
  refine wp_load8 addr read fun a sa _ _ => wp_cmpi fun t at' cf _ => WP.block_nil ?_
  refine ⟨?_, at'.mem.trans sa.mem, sa.keeps.trans (at'.keeps _)⟩
  rw [cf, sa.gpr]
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
    (Nat.lt_trans (s.mem ((s.gpr .esi).setWidth 64)).isLt (by decide : 2 ^ 8 < 2 ^ 32))]
  exact congrArg some (decide_eq_decide.mpr value)
end VG.Proof.Dsa.X86.Generation
