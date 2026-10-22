module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
import VerifiedGarbage.Proof.Framework.Offset

/-! # Convert the operational frame to the shared offset preservation relation -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

theorem Stage.workspace_keeps {σ s : State} {base : Addr} {bytes w len : Nat}
    (h : Stage base bytes w σ s) (size : bytes = 8 * len)
    (fit : Spec.Rsa.Mont.arrAt w 28 ≤ bytes) :
    Spec.Rsa.MontMul.Keeps base len (workingRanges w) σ.mem s.mem := by
  intro i hi outside
  have nw := h.context.ws.nowrap
  have inWs : (⟨base, bytes⟩ : Region).Contains (off base i) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  apply h.changed
  intro r hr hc
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    have bound := Nat.le_trans (working_bounds w p hp) fit
    have apart : Region.Disjoint ⟨off base i, 1⟩ ⟨off base p.1, p.2⟩ :=
      Offset.disjoint _ (by have := outside p hp; omega) (by omega) (by omega)
    exact apart _ (Region.contains_self _ _) hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [← h.stack] at hc
      exact h.context.apart _ inWs ((Offset.sub_base _ (by decide :
        VG.Impl.MillerRabin.X86.tableCursor + 4 ≤ VG.Impl.MillerRabin.X86.frameBytes)) _ hc)
    · rw [← h.stack] at hc
      exact h.room.apart _ hc inWs

end VG.Proof.MillerRabin.X86
