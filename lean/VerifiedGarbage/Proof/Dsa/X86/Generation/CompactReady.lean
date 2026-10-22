module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SavedContext
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactTransferLayout
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparationFrame
import VerifiedGarbage.Proof.Mont.OutsFrame

/-! Transfer a saved candidate into the exact shared prepared-round representation. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86

private theorem compact_ranges_fit {n : Nat} (upper : n ≤ 48) :
    ∀ r ∈ transferRanges (compactTransfers n),
      Layout.arithmetic ≤ r.1 ∧ r.1 + r.2 ≤ Layout.arithmetic + Layout.arithmeticBytes := by
  intro r hr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
  have fit := (compact_transfers_fit upper ht).1
  refine ⟨?_, fit⟩
  simp only [compactTransfers, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [compactNumberTransfer, Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes] <;> omega

theorem compact_ready {s : State} {base : Addr} {bytes n candidate : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (C : SavedContext base n candidate s)
    (upper : n ≤ 48)
    (layout : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (off base Layout.arithmetic)
      (Layout.arithmeticBytes / 8))
    (width : Spec.Rsa.Mont.wOf s.mem (off base Layout.arithmetic) = n) :
    WP isa (transferWords (compactTransfers n)) s fun t =>
      SavedContext base n candidate t ∧
      Spec.MillerRabin.Layout Spec.MillerRabin.compact t.mem (off base Layout.arithmetic)
        (Layout.arithmeticBytes / 8) ∧
      Spec.Rsa.Mont.wOf t.mem (off base Layout.arithmetic) = n ∧
      Spec.Rsa.Mont.numAt t.mem (off base Layout.arithmetic) n 0 = candidate ∧
      Spec.Rsa.Mont.numAt t.mem (off base Layout.arithmetic) n 5 = 1 ∧
      Spec.Rsa.Mont.numAt t.mem (off base Layout.arithmetic) n 9 = 2 ^ (64 * n) % candidate ∧
      Spec.Rsa.Mont.numAt t.mem (off base Layout.arithmetic) n 10 = candidate - 2 ^ (64 * n) % candidate ∧
      Spec.Rsa.Mont.numAt t.mem (off base Layout.arithmetic) n 27 = Spec.MillerRabin.exponent candidate ∧
      word t.mem (off base Layout.arithmetic) (Spec.Rsa.Mont.arrAt n 27 + 8 * n) =
        BitVec.twoPow 64 ((Spec.Rsa.splitTwos (candidate - 1)).1 % 64) ∧
      Frame [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.mono (compact_numbers_shared scr upper capacity) fun t ⟨values, tail, F, K⟩ => ?_
  have frame : Frame [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩] s.mem t.mem :=
    (F.enclose (compact_ranges_fit upper)).frameAt (by decide)
  have CT := C.frame_keep K (by decide) (by decide) frame (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact parent_arithmetic_apart base (Nat.le_refl _))
  obtain ⟨L, W⟩ := compact_transfer_layout F layout
  rw [width] at W
  refine ⟨CT, L, W, ?_, ?_, ?_, ?_, ?_, tail.trans C.oneHot, frame, K⟩
  · exact (values (0, 0) (by simp)).trans C.parent.modulus.val
  · exact (values (5, 3) (by simp)).trans C.ordinary
  · exact (values (9, 6) (by simp)).trans C.one
  · exact (values (10, 7) (by simp)).trans C.minus
  · exact (values (27, 8) (by simp)).trans C.exponent

end VG.Proof.Dsa.X86.Generation
