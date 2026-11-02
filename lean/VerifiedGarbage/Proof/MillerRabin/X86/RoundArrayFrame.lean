module

public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame
import VerifiedGarbage.Proof.MillerRabin.X86.Data

/-! # Prepared products and table copies stay within the reviewed round footprint -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Proof.Mont

def roundArray (j : Nat) : Prop :=
  j = 2 ∨ j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 8 ∨ 11 ≤ j ∧ j < 27

theorem array_roundRange (g : Geometry) {j n : Nat} (allowed : roundArray j)
    (size : n ≤ 8 * (g.w + 2)) :
    ∃ R ∈ roundWrites g, R.1 ≤ g.array j ∧ g.array j + n ≤ R.1 + R.2 := by
  unfold roundArray at allowed
  rcases allowed with rfl | rfl | rfl | rfl | rfl | table
  · refine ⟨(g.array 2, 16 * (g.w + 2)), by simp [roundWrites], Nat.le_refl _, ?_⟩
    dsimp only
    omega
  · refine ⟨(g.array 2, 16 * (g.w + 2)), by simp [roundWrites], ?_, ?_⟩ <;>
      unfold Geometry.array Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes <;> omega
  · refine ⟨(g.array 5, 16 * (g.w + 2)), by simp [roundWrites], Nat.le_refl _, ?_⟩
    dsimp only
    omega
  · refine ⟨(g.array 5, 16 * (g.w + 2)), by simp [roundWrites], ?_, ?_⟩ <;>
      unfold Geometry.array Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes <;> omega
  · refine ⟨(g.array 8, 8 * (g.w + 2)), by simp [roundWrites], Nat.le_refl _, ?_⟩
    dsimp only
    omega
  · have lower := Nat.mul_le_mul_right (8 * (g.w + 2)) table.1
    have upper := g.strideBefore table.2
    refine ⟨(g.array 11, 128 * (g.w + 2)), by simp [roundWrites], ?_, ?_⟩ <;>
      unfold Geometry.array Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes at * <;> omega

theorem array_roundFrame {g : Geometry} {j : Nat} {m m' : Mem}
    (nowrap : g.W.toNat + g.L ≤ 2 ^ 32) (allowed : roundArray j)
    (O : Outside g.W (g.array j) (4 * g.words) m m') :
    WorkspaceFrame g (roundWrites g) m m' := by
  apply (WorkspaceFrame.of_outs nowrap (Outs.of_outside O (List.mem_singleton_self _))).cover
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  exact array_roundRange g allowed (by unfold Geometry.words; omega)

theorem mont_roundFrame {g : Geometry} {m m' : Mem}
    (O : WorkspaceFrame g (montWrites g 6) m m') : WorkspaceFrame g (roundWrites g) m m' := by
  apply O.cover
  intro r mem
  simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact array_roundRange g (j := 2) (by unfold roundArray; simp) (Nat.le_refl _)
  · exact array_roundRange g (j := 3) (by unfold roundArray; simp) (Nat.le_refl _)
  · exact array_roundRange g (j := 6) (by unfold roundArray; simp) (Nat.le_refl _)

end VG.Proof.MillerRabin.X86
