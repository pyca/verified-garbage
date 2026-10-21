module

public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.Data

/-! # Every scalar scratch word is within the round's permitted write footprint -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Proof.Mont

theorem scalar_roundRange (g : Geometry) {d : Nat} (scratch : scratchWord d) :
    ∃ R ∈ roundWrites g, R.1 ≤ d ∧ d + 4 ≤ R.1 + R.2 := by
  unfold scratchWord at scratch
  rcases scratch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(8, 8), by simp [roundWrites], by decide, by decide⟩
  · exact ⟨(8, 8), by simp [roundWrites], by decide, by decide⟩
  · exact ⟨(184, 8), by simp [roundWrites], by decide, by decide⟩
  · exact ⟨(184, 8), by simp [roundWrites], by decide, by decide⟩
  · exact ⟨(208, 8), by simp [roundWrites], by decide, by decide⟩
  · exact ⟨(208, 8), by simp [roundWrites], by decide, by decide⟩
  · exact ⟨(232, 8), by simp [roundWrites], by decide, by decide⟩
  · exact ⟨(232, 8), by simp [roundWrites], by decide, by decide⟩
  · exact ⟨(240, 8), by simp [roundWrites], by decide, by decide⟩
  · exact ⟨(240, 8), by simp [roundWrites], by decide, by decide⟩

theorem scalar_roundFrame {g : Geometry} {rs : List Nat} {m m' : Mem}
    (nowrap : g.W.toNat + g.L ≤ 2 ^ 32) (scratch : ∀ d ∈ rs, scratchWord d)
    (O : Outs g.W (rs.map fun d => (d, 4)) m m') :
    WorkspaceFrame g (roundWrites g) m m' := by
  apply (WorkspaceFrame.of_outs nowrap O).cover
  intro r mem
  obtain ⟨d, known, rfl⟩ := List.mem_map.mp mem
  exact scalar_roundRange g (scratch d known)

end VG.Proof.MillerRabin.X86
