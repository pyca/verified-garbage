module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArenaReady
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateStores
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate

/-! # Persist both products of the single-division candidate construction -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation.Layout

theorem candidatePersist_ok {G : GenerationGeometry} {s : State}
    (R : ArenaReady G s) (saved : s.mem.readW (off G.frameBase 20) 32 = G.parent)
    (di : s.gpr .edi = G.pointer arithmetic) :
    WP isa (candidateStores G.pLen) s fun t =>
      Spec.Rsa.bytesAt t.mem (off G.base p) G.pLen =
        Spec.Dsa.encodeBE G.pLen (wordsVal s.mem (off G.base arithmetic) candidateP (G.pLen / 8)) ∧
      Spec.Rsa.bytesAt t.mem (off G.base exponent) G.pLen =
        Spec.Dsa.encodeBE G.pLen (wordsVal s.mem (off G.base arithmetic) candidateQuotient (G.pLen / 8)) ∧
      ArenaReady G t ∧ Frame [G.part p G.pLen, G.part exponent G.pLen] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have width := G.width
  have lo : 4 ≤ G.pLen := by omega
  have hi : G.pLen ≤ 384 := by omega
  have words : G.pLen % 4 = 0 := by rcases width with h | h | h <;> rw [h] <;> decide
  have len : G.pLen = 8 * (G.pLen / 8) := by rcases width with h | h | h <;> rw [h] <;> decide
  have pr : p + G.pLen ≤ usedBytes G.pLen := by unfold p usedBytes domainCheck; omega
  have er : exponent + G.pLen ≤ usedBytes G.pLen := by unfold exponent usedBytes domainCheck; omega
  have ar : arithmetic + arithmeticBytes ≤ usedBytes G.pLen := by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega
  have ps : p < usedBytes G.pLen := by omega
  have es : exponent < usedBytes G.pLen := by omega
  have pa : (G.parent + BitVec.ofNat 32 p).setWidth 64 = off G.base p := G.pointer_addr ps
  have ea : (G.parent + BitVec.ofNat 32 exponent).setWidth 64 = off G.base exponent := G.pointer_addr es
  refine WP.mono (candidateStores_ok (n := G.pLen / 8) R.frame (R.arithmeticScr di) saved lo (by omega) words
    (by unfold candidateP arithmeticBytes; omega) (by unfold candidateQuotient arithmeticBytes; omega)
    (G.pointer_fit ps pr) (G.pointer_fit es er)
    (R.writePointer ps pr) (R.writePointer es er)
    (by rw [pa]; exact G.parts_disjoint pr ar (.inl (by unfold p arithmetic; omega)))
    (by rw [ea]; exact G.parts_disjoint er ar (.inl (by unfold exponent arithmetic; omega)))
    (by rw [pa]; exact G.frame_part pr)
    (by rw [pa, ea]; exact G.parts_disjoint pr er (.inl (by unfold p exponent; omega))))
    fun t ⟨pv, ev, O, K⟩ => ?_
  rw [pa] at pv
  rw [ea] at ev
  rw [pa, ea] at O
  exact ⟨pv, ev, R.keep K (by decide), O, K⟩
end VG.Proof.Dsa.X86.Generation
