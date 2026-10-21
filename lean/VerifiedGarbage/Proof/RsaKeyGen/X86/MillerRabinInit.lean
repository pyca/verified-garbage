module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessChecks
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessChecks
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory

/-! # Initial counters establish the reviewed blinded-loop invariant -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen

theorem Parameters.primality {P : Parameters} (v : P.Valid) :
    Spec.RsaKeyGen.primalityTest P.candidate (P.entropy.drop P.bytes) =
      Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep P.candidate P.checks P.twos.1 P.twos.2)
        (1, 0) (P.entropy.drop P.bytes) := by
  unfold Spec.RsaKeyGen.primalityTest
  rw [ite_eq_right (by have := v.large; omega), ite_eq_right (by rw [v.odd]; decide),
    ite_eq_right (by have := v.large; omega), v.checks]
  rfl

theorem init_ok {P : Parameters} (v : P.Valid) {s : State}
    (S : Prepare.Data P.g P.candidate P.capacity P.p s)
    (readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen)
    (entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy)
    (randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand)
    (randLength : w32 s.mem P.g.W 32 = P.randLen)
    (used : w32 s.mem P.g.W 152 = P.bytes) (enough : P.bytes ≤ P.randLen) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.WitnessChecks.code P.g.w)) s fun t =>
      StateAt P 0 (itersOf P.bytes P.entropy.length
        (shapeOf (Spec.RsaKeyGen.primalityTest P.candidate (P.entropy.drop P.bytes))) P.bytes - 1) t ∧
      WorkspaceFrame P.g WitnessChecks.ranges s.mem t.mem ∧ Frame [⟨P.g.W, P.g.L⟩] s.mem t.mem ∧
      Keeps [.eax] s t := by
  refine WP.mono (WitnessChecks.code_ok v.geometry S) fun t ⟨T, roundsT, uniformT, checksT, O, K⟩ => ?_
  have rangesFit : ∀ r ∈ WitnessChecks.ranges, r.1 + r.2 ≤ P.g.L := by
    intro r mem
    simp only [WitnessChecks.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> have := v.geometry.headerFit <;> omega
  have W := WorkspaceFrame.of_outs S.ready.scratch.nowrap O
  have F := workspaceGlobalFrame O rangesFit
  have hdr {d : Nat} (bound : d + 4 ≤ 176) : w32 t.mem P.g.W d = w32 s.mem P.g.W d := by
    apply congrArg BitVec.toNat
    apply W.read32 (by have := v.geometry.headerFit; omega)
    intro r mem
    simp only [WitnessChecks.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> left <;> omega
  have primeAt := mrAt_zero (Parameters.primality v) v.witnessBytes
    (by have := v.geometry.minWidth; unfold Parameters.bytes; omega)
    (by rw [v.entropyLength]; exact enough)
  refine ⟨⟨T, ?_, ?_, ?_, (hdr (by decide)).trans randLength,
    by simpa only [Nat.zero_add, Nat.mul_one] using (hdr (d := 152) (by decide)).trans used,
    roundsT, uniformT, checksT, primeAt⟩, W, F, K⟩
  · rw [K.2.1, K.2.2]; exact readable
  · exact (frame_bytesAt F (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.randSeparate)
      (by have := v.randLenFit; omega)).trans entropy
  · exact (BitVec.eq_of_toNat_eq (hdr (d := 28) (by decide))).trans randPtr

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
