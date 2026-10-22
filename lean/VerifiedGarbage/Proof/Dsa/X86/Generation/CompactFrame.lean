module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactTransferLayout
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParentConstants
import VerifiedGarbage.Proof.Framework.Offset

/-! Compact header writes preserve candidate, constants and exponent arrays. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Proof.Mont

private theorem compact_array_bound {n j : Nat} (hn : n ≤ 48) (hj : j < 28) :
    Spec.Rsa.Mont.arrAt n j + 8 * n + 8 ≤ 12288 := by
  have scale := Nat.mul_le_mul (show j ≤ 27 by omega) (show 8 * (n + 2) ≤ 400 by omega)
  simp only [Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes]
  omega

theorem compact_frame_number {m m' : Mem} {base : Addr} {n j : Nat}
    (F : Frame [⟨base, 256⟩] m m') (hn : n ≤ 48) (hj : j < 28) :
    Spec.Rsa.Mont.numAt m' base n j = Spec.Rsa.Mont.numAt m base n j := by
  unfold Spec.Rsa.Mont.numAt
  apply congrArg BitVec.toNat
  have bound := compact_array_bound hn hj
  apply F.read (r := ⟨off base (Spec.Rsa.Mont.arrAt n j), 8 * n⟩) (Region.contains_self _ _) ?_ (by omega)
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base base (by simp only [Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes]; omega)
    (by omega)

theorem compact_frame_tail {m m' : Mem} {base : Addr} {n : Nat}
    (F : Frame [⟨base, 256⟩] m m') (hn : n ≤ 48) :
    word m' base (Spec.Rsa.Mont.arrAt n 27 + 8 * n) =
      word m base (Spec.Rsa.Mont.arrAt n 27 + 8 * n) := by
  have bound := compact_array_bound hn (show 27 < 28 by decide)
  apply F.readW (r := ⟨off base (Spec.Rsa.Mont.arrAt n 27 + 8 * n), 8⟩)
    (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base base (by simp only [Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes]; omega)
    (by omega)

theorem compact_inverse_input {s : VG.X86.State} {base : Addr} {n m : Nat}
    (C : ParentContext base n m s) (positive : 0 < n)
    (candidate : Spec.Rsa.Mont.numAt s.mem (off base VG.Impl.Dsa.Generation.Layout.arithmetic) n 0 = m) :
    (w32 s.mem (off base VG.Impl.Dsa.Generation.Layout.arithmetic) 256 * w32 s.mem base 0 + 1) % 2 ^ 32 = 0 := by
  have low := VG.Proof.MillerRabin.montNum_low32 s.mem
    (off base VG.Impl.Dsa.Generation.Layout.arithmetic) (j := 0) positive
  simp only [Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero, candidate] at low
  rw [low]
  have inverse : (m * w32 s.mem base 0 + 1) % 2 ^ 32 = 0 := C.inverse
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using inverse

end VG.Proof.Dsa.X86.Generation
