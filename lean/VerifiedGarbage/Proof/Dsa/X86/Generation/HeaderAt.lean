module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimePreparation
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactHeader
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Subspace
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.OutsFrame

/-! Install the compact header in its subspace and restore the parent pointer. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86

private theorem header_number_fit {n : Nat} (upper : n ≤ 48) :
    Spec.Rsa.Mont.arrAt n 28 ≤ Layout.arithmeticBytes := by
  simp only [Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes, Layout.arithmeticBytes]
  omega

theorem header_at {s : State} {base : Addr} {bytes n : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (lower : 4 ≤ n) (upper : n ≤ 48) :
    WP isa (.block (enterArithmetic ++ compactHeader n ++ leaveArithmetic)) s fun t =>
      Spec.MillerRabin.Layout Spec.MillerRabin.compact t.mem (off base Layout.arithmetic)
        (Layout.arithmeticBytes / 8) ∧
      Spec.Rsa.Mont.wOf t.mem (off base Layout.arithmetic) = n ∧
      Frame [⟨off base Layout.arithmetic, 256⟩] s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  have fit : Layout.arithmetic + Layout.arithmeticBytes ≤ bytes := capacity
  unfold enterArithmetic
  rw [List.append_assoc]
  refine WP.block_append (wp_addS rfl fun a A _ => WP.block_nil ?_)
  have child : Scr (a.withRegions a.rd [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩])
      (off base Layout.arithmetic) Layout.arithmeticBytes :=
    workspace_slice scr fit (by unfold Layout.arithmetic; omega) A.gpr (A.other .esp (by decide))
      (List.mem_singleton_self _)
  have write : Covers [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩] a.wr := by
    rw [A.wr]; exact workspace_slice_covers scr fit
  have work := compact_header child lower (by omega)
    (header_number_fit upper)
    (by decide : Layout.arithmeticBytes = 8 * (Layout.arithmeticBytes / 8))
  refine WP.block_append (WP.mono (workspace_wp work (Covers.append (Covers.refl _) write) write)
    fun b ⟨u, ⟨_, F, L, width, K⟩, eq⟩ => ?_)
  subst eq
  unfold leaveArithmetic
  refine wp_subS rfl fun t T _ => WP.block_nil ?_
  have restored : t.gpr .edi = s.gpr .edi := by
    rw [T.gpr, State.withRegions_gpr, K.1 .edi (by decide), State.withRegions_gpr, A.gpr,
      BitVec.add_sub_cancel]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [T.mem]; exact L
  · rw [T.mem]; exact width
  · rw [T.mem, ← A.mem]
    exact (Outs.of_outside F (List.mem_singleton_self _)).frame (by
      intro r hr; rw [List.mem_singleton.mp hr]; decide)
  · refine ⟨?_, ?_, ?_⟩
    · intro r hr
      by_cases di : r = .edi
      · subst di; exact restored
      · rw [T.other r di, State.withRegions_gpr, K.1 r hr, State.withRegions_gpr, A.other r di]
    · rw [T.rd, State.withRegions_rd, A.rd]
    · rw [T.wr, State.withRegions_wr, A.wr]

end VG.Proof.Dsa.X86.Generation
