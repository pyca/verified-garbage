module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactNumbers
public import VerifiedGarbage.Proof.MillerRabin.Workspace
import VerifiedGarbage.Proof.Mont.Words32Parts
import VerifiedGarbage.Proof.Mont.Words32Offset

/-! Number transfers leave every compact header word unchanged. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86

theorem compact_transfer_header {m m' : Mem} {base : Addr} {n d : Nat}
    (F : Outs base (transferRanges (compactTransfers n)) m m') (hd : d + 8 ≤ 256) :
    word m' (off base Layout.arithmetic) d = word m (off base Layout.arithmetic) d := by
  apply BitVec.eq_of_toNat_eq
  rw [word_toNat_val32, val32_off, word_toNat_val32, val32_off]
  apply F.val32 ?_ (by unfold Layout.arithmetic; omega)
  intro r hr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
  simp only [compactTransfers, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> left <;>
    simp only [compactNumberTransfer, Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes] <;> omega

theorem compact_transfer_layout {m m' : Mem} {base : Addr} {n len : Nat}
    (F : Outs base (transferRanges (compactTransfers n)) m m')
    (L : Spec.MillerRabin.Layout Spec.MillerRabin.compact m (off base Layout.arithmetic) len) :
    Spec.MillerRabin.Layout Spec.MillerRabin.compact m' (off base Layout.arithmetic) len ∧
      Spec.Rsa.Mont.wOf m' (off base Layout.arithmetic) = Spec.Rsa.Mont.wOf m (off base Layout.arithmetic) := by
  apply VG.Proof.MillerRabin.Workspace.compact_layout_header_congr ?_ ?_ ?_ L
  · exact compact_transfer_header F (by decide : 48 + 8 ≤ 256)
  · intro j hj
    exact compact_transfer_header F (by unfold Spec.Rsa.Mont.arrWord; omega)
  · exact compact_transfer_header F (by decide : 224 + 8 ≤ 256)

end VG.Proof.Dsa.X86.Generation
