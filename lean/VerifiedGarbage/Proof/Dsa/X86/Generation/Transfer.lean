module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Transfer
public import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Framework.Omega

/-! Transfer ranges fit the shared generation workspace and never overlap. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86

def TransferFits (bytes : Nat) (t : WordTransfer) : Prop :=
  t.destination + 4 * t.words ≤ bytes ∧ t.source + 4 * t.words ≤ bytes ∧
    (t.destination ≤ t.source ∨ t.source + 4 * t.words ≤ t.destination)

theorem candidate_transfer_fit {n : Nat} (hn : n ≤ 48) : TransferFits 40960 (candidateTransfer n) := by
  simp only [TransferFits, candidateTransfer, VG.Impl.Mont.X86.Dynamic.slot,
    VG.Impl.Mont.X86.Dynamic.stride, VG.Impl.Dsa.Generation.Layout.arithmetic]
  omega

theorem save_exponent_transfers_fit {n : Nat} (hn : n ≤ 48) {t : WordTransfer}
    (ht : t ∈ saveExponentTransfers n) : TransferFits 40960 t := by
  simp only [saveExponentTransfers, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;>
    simp only [TransferFits, VG.Impl.Mont.X86.Dynamic.slot, VG.Impl.Mont.X86.Dynamic.stride,
      VG.Impl.Dsa.Generation.Layout.arithmetic] <;> omega

theorem compact_transfers_fit {n : Nat} (hn : n ≤ 48) {t : WordTransfer}
    (ht : t ∈ compactTransfers n) : TransferFits 40960 t := by
  simp only [compactTransfers, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [TransferFits, compactNumberTransfer, VG.Impl.Mont.X86.Dynamic.slot,
      VG.Impl.Mont.X86.Dynamic.stride, VG.Impl.Dsa.Generation.Layout.arithmetic,
      VG.Spec.Rsa.Mont.arrAt, VG.Spec.Rsa.Mont.hdrBytes] <;> omega

theorem word_transfer {s : State} {base : Addr} {bytes : Nat} {t : WordTransfer}
    (scr : Scr s base bytes) (fit : TransferFits bytes t) :
    WP isa t.code s fun u =>
      val32 u.mem base t.destination t.words = val32 s.mem base t.source t.words ∧
      Keeps [.eax] s u ∧ Outside base t.destination (4 * t.words) s.mem u.mem :=
  VG.Proof.Weierstrass.X86.copy_ok t.words scr fit.1 fit.2.1 fit.2.2

end VG.Proof.Dsa.X86.Generation
