module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRoundFrame
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory

/-! # A witness step retains the entropy buffer and the outer loop's fixed metadata -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen

theorem step_header32 {g : Geometry} (v : g.Valid) {s t : Mem}
    (F : WorkspaceFrame g (WitnessStep.ranges g) s t) {d : Nat} (index : d = 28 ∨ d = 32 ∨ d = 200) :
    w32 t g.W d = w32 s g.W d := by
  apply congrArg BitVec.toNat
  apply F.read32 (by have := v.headerFit; omega)
  intro r mem
  simp only [WitnessStep.ranges, List.mem_append, List.mem_singleton] at mem
  rcases mem with (rfl | mem) | mem
  · rcases index with rfl | rfl | rfl <;> omega
  · exact WitnessRound.ranges_apart32 (by rcases index with rfl | rfl | rfl <;> unfold WitnessRound.safeHeader <;> decide) r mem
  · simp only [WitnessCount.ranges, WitnessCount.nextRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases index with rfl | rfl | rfl <;> rcases mem with (rfl | rfl) | rfl <;>
      simp only [VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset,
        VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset] <;> omega

theorem StateAt.next {P : Parameters} (v : P.Valid) {s t : State} {k n : Nat} (S : StateAt P k n s)
    (T : Prepare.Data P.g P.candidate P.capacity P.p t)
    (used : w32 t.mem P.g.W 152 = P.start + P.bytes * k + P.bytes)
    (rounds : w32 t.mem P.g.W 176 = k + 1)
    (uniform : w32 t.mem P.g.W 192 = (mrSB P.candidate P.bytes P.start P.entropy (k + 1)).2)
    (atLoop : MrLoopAt P.candidate P.checks P.twos.1 P.twos.2 P.bytes P.start P.entropy (k + 1) (n - 1))
    (W : WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem)
    (F : Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem)
    (K : Keeps WitnessStep.clob s t) : StateAt P (k + 1) (n - 1) t := by
  refine ⟨T, ?_, ?_, ?_, (step_header32 v.geometry W (Or.inr (Or.inl rfl))).trans S.randLength,
    ?_, rounds, uniform, (step_header32 v.geometry W (Or.inr (Or.inr rfl))).trans S.checks, atLoop⟩
  · rw [K.2.1, K.2.2]; exact S.readable
  · exact (frame_bytesAt F (by
      intro r mem
      simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact v.randSeparate
      · exact v.randStackFar) (by have := v.randLenFit; omega)).trans S.entropy
  · exact (BitVec.eq_of_toNat_eq (step_header32 v.geometry W (Or.inl rfl))).trans S.randPtr
  · rw [used, Nat.mul_succ]; omega

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
