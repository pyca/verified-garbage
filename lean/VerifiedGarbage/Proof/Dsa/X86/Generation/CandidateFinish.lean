module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Framework.Offset
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArenaReady
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateFromFrame
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidatePersist
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate

/-! # Construct and serialize p and its generator exponent with a single division -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation.Layout

theorem candidateFinish_ok {G : GenerationGeometry} {s : State} {qvalue : Nat}
    (R : ArenaReady G s) (saved : s.mem.readW (off G.frameBase 20) 32 = G.parent)
    (qval : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off G.base q) G.qLen) = qvalue)
    (qpos : 0 < qvalue) (qbound : 2 * qvalue < 2 ^ (32 * (2 * (G.pLen / 8)))) :
    WP isa (.seq (candidateComputeFromFrame G.pLen G.qLen (G.pLen / 8)) (candidateStores G.pLen)) s fun t =>
      let x := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off G.base shaped) G.pLen)
      Spec.Rsa.bytesAt t.mem (off G.base p) G.pLen = Spec.Dsa.encodeBE G.pLen (x + 1 - x % (2 * qvalue)) ∧
      Spec.Rsa.bytesAt t.mem (off G.base exponent) G.pLen =
        Spec.Dsa.encodeBE G.pLen ((x + 1 - x % (2 * qvalue) - 1) / qvalue) ∧
      ArenaReady G t ∧ Frame [G.part arithmetic arithmeticBytes, G.part p G.pLen, G.part exponent G.pLen] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have ar : arithmetic + arithmeticBytes ≤ usedBytes G.pLen := by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega
  refine WP.seq (WP.mono (candidateComputeFromFrame_ok R saved qval qpos qbound)
    fun a ⟨pv, ev, Ra, di, Oa, Ka⟩ => ?_)
  have parent : a.mem.readW (off G.frameBase 20) 32 = G.parent := by
    rw [Oa.readW (r := ⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩)
      (Offset.contains_base _ (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; decide) (by decide))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact G.frame_part ar) (by decide), saved]
  refine WP.mono (candidatePersist_ok Ra parent di) fun t ⟨pb, eb, Rt, Ot, Kt⟩ => ?_
  rw [wordsVal_eq_val32, pv] at pb
  rw [wordsVal_eq_val32, ev] at eb
  exact ⟨pb, eb, Rt, (Oa.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp)).trans
    (Ot.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)), Ka.trans (Kt.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
