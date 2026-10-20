module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory
import VerifiedGarbage.Proof.Framework.Offset
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArenaReady
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateCompute
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers

/-! # Construct p and its generator exponent in the concrete parameter arena -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation.Layout

theorem candidateComputeFromFrame_ok {G : GenerationGeometry} {s : State} {qvalue : Nat}
    (R : ArenaReady G s) (saved : s.mem.readW (off G.frameBase 20) 32 = G.parent)
    (qval : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off G.base q) G.qLen) = qvalue)
    (qpos : 0 < qvalue) (qbound : 2 * qvalue < 2 ^ (32 * (2 * (G.pLen / 8)))) :
    WP isa (candidateComputeFromFrame G.pLen G.qLen (G.pLen / 8)) s fun t =>
      let x := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off G.base shaped) G.pLen)
      val32 t.mem (off G.base arithmetic) candidateP (2 * (G.pLen / 8)) = x + 1 - x % (2 * qvalue) ∧
      val32 t.mem (off G.base arithmetic) candidateQuotient (2 * (G.pLen / 8)) =
        (x + 1 - x % (2 * qvalue) - 1) / qvalue ∧
      ArenaReady G t ∧ t.gpr .edi = G.pointer arithmetic ∧
      Frame [G.part arithmetic arithmeticBytes] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have pw := G.width
  have qw := G.qWidth
  have pmin : 4 ≤ G.pLen := by omega
  have pmax : G.pLen ≤ 384 := by omega
  have pwords : G.pLen % 4 = 0 := by rcases pw with h | h | h <;> rw [h] <;> decide
  have plen : G.pLen = 8 * (G.pLen / 8) := by rcases pw with h | h | h <;> rw [h] <;> decide
  have qwords : G.qLen % 4 = 0 := by rcases qw with h | h <;> rw [h] <;> decide
  have xroom : shaped + G.pLen ≤ usedBytes G.pLen := by unfold shaped usedBytes domainCheck; omega
  have qroom : q + G.qLen ≤ usedBytes G.pLen := by unfold q usedBytes domainCheck; omega
  have aroom : arithmetic + arithmeticBytes ≤ usedBytes G.pLen := by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega
  have xs : shaped < usedBytes G.pLen := by omega
  have qs : q < usedBytes G.pLen := by omega
  unfold candidateComputeFromFrame
  refine WP.seq (WP.mono (candidateArgs_ok R.frame saved) fun a ⟨si, cx, di, mem, Ka⟩ => ?_)
  change a.gpr .esi = G.pointer shaped at si
  change a.gpr .ecx = G.pointer q at cx
  change a.gpr .edi = G.pointer arithmetic at di
  have Ra := R.keep Ka (by decide)
  have S := Ra.arithmeticScr di
  refine WP.mono (candidateCompute_ok S (by omega) (by unfold arithmeticBytes; decide) (by omega)
    pmin (by omega) pwords (by omega) (by omega) qwords
    (by rw [si]; exact G.pointer_fit xs xroom) (by rw [cx]; exact G.pointer_fit qs qroom)
    (by intro d hd; rw [si]; exact Ra.readPointer xs xroom d 4 hd)
    (by intro d hd; rw [cx]; exact Ra.readPointer qs qroom d 4 hd)
    (by rw [si, G.pointer_addr xs]; exact G.parts_disjoint xroom aroom (.inl (by unfold shaped arithmetic; omega)))
    (by rw [cx, G.pointer_addr qs]; exact G.parts_disjoint qroom aroom (.inl (by unfold q arithmetic; omega)))
    (by rw [cx, G.pointer_addr qs, mem]; exact qval) qpos qbound)
    fun t ⟨pv, ev, O, Kt⟩ => ?_
  rw [si, G.pointer_addr xs, mem] at pv ev
  have K : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := (Ka.mono (by decide)).trans
    (Kt.mono (by decide))
  refine ⟨pv, ev, R.keep K (by decide), (Kt.1 _ (by decide)).trans di, ?_, K⟩
  rw [mem] at O
  have bounds : ∀ r ∈ ((candidateQuotient, 8 * (G.pLen / 8)) ::
      (candidateDivisor, 4 * (2 * (G.pLen / 8) + 1)) ::
      (candidateTemporary, 4 * (2 * (G.pLen / 8) + 1)) :: candidateWrites (2 * (G.pLen / 8))),
      r.1 + r.2 ≤ arithmeticBytes := by
    intro r hr
    simp only [candidateWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [candidateQuotient, candidateDivisor, candidateTemporary, candidateOriginal, candidateP, candidateRemainder, arithmeticBytes] <;>
      omega_using [pmax]
  have frame := sampleOuts_frame O (fun r hr => Nat.le_trans (bounds r hr) (by decide))
  apply frame.sub
  intro r hr
  obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hr
  exact ⟨G.part arithmetic arithmeticBytes, by simp, Offset.sub_base _ (bounds item hi)⟩
end VG.Proof.Dsa.X86.Generation
