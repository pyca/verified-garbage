module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageProduct
public import VerifiedGarbage.Proof.MillerRabin.X86.OperandFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! # Live values preserved by an existing Montgomery call -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem product_frame_read {s : State} {m m' : Mem} {base : Addr} {bytes w o d n : Nat}
    (ctx : ProtectedContext s base bytes) (room : CallRoom (s.gpr .esp) base bytes)
    (hf : arrAt w 28 ≤ bytes) (ho : o < 28) (hd : d + n ≤ bytes)
    (out : d + n ≤ arrAt w o ∨ arrAt w o + 8 * w ≤ d)
    (temp : d + n ≤ scratch w ∨ scratch w + Spec.Rsa.MontMul.scratchBytes w ≤ d)
    (F : Frame [⟨off base (arrAt w o), 8 * w⟩,
      ⟨off base (scratch w), Spec.Rsa.MontMul.scratchBytes w⟩,
      below (s.gpr .esp) 40] m m') : m'.read (off base d) n = m.read (off base d) n := by
  have nw := ctx.ws.nowrap
  have fo := array_fits_bytes hf ho
  have fs : scratch w + Spec.Rsa.MontMul.scratchBytes w ≤ bytes :=
    Nat.le_trans (scratch_before_operand w (by decide : 5 ≤ 28)) hf
  refine F.read (r := ⟨off base d, n⟩) (Region.contains_self _ _) ?_ (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ out (by omega) (by omega)
  · exact Offset.disjoint _ temp (by omega) (by omega)
  · exact room.apart.symm.sub_left (Offset.sub_base _ hd)

theorem product_frame_num {s : State} {m m' : Mem} {base : Addr} {bytes w o a : Nat}
    (ctx : ProtectedContext s base bytes) (room : CallRoom (s.gpr .esp) base bytes)
    (hf : arrAt w 28 ≤ bytes) (ho : o < 28) (ha : 5 ≤ a ∧ a < 28) (hne : a ≠ o)
    (F : Frame [⟨off base (arrAt w o), 8 * w⟩,
      ⟨off base (scratch w), Spec.Rsa.MontMul.scratchBytes w⟩,
      below (s.gpr .esp) 40] m m') : numAt m' base w a = numAt m base w a := by
  have fa := array_fits_bytes hf ha.2
  unfold numAt
  rw [product_frame_read ctx room hf ho (by omega) (arrays_apart w hne)
    (.inr (scratch_before_operand w ha.1)) F]

theorem product_frame_stack {s : State} {m m' : Mem} {base : Addr} {bytes w o d n : Nat}
    (ctx : ProtectedContext s base bytes) (room : CallRoom (s.gpr .esp) base bytes)
    (hf : arrAt w 28 ≤ bytes) (ho : o < 28)
    (hd : d + n ≤ VG.Impl.MillerRabin.X86.frameBytes)
    (F : Frame [⟨off base (arrAt w o), 8 * w⟩,
      ⟨off base (scratch w), Spec.Rsa.MontMul.scratchBytes w⟩,
      below (s.gpr .esp) 40] m m') :
    m'.read (off (byteAddr (s.gpr .esp)) d) n = m.read (off (byteAddr (s.gpr .esp)) d) n := by
  have fo := array_fits_bytes hf ho
  have fs : scratch w + Spec.Rsa.MontMul.scratchBytes w ≤ bytes :=
    Nat.le_trans (scratch_before_operand w (by decide : 5 ≤ 28)) hf
  refine F.read (r := ⟨off (byteAddr (s.gpr .esp)) d, n⟩) (Region.contains_self _ _) ?_
    (by simp only [VG.Impl.MillerRabin.X86.frameBytes] at hd; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (ctx.apart.symm.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ (by omega))
  · exact (ctx.apart.symm.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ fs)
  · change Region.Disjoint ⟨off ((s.gpr .esp).setWidth 64) d, n⟩
      ⟨(s.gpr .esp - BitVec.ofNat 32 40).setWidth 64, 40⟩
    rw [Taint.sub_setWidth room.low]
    exact Offset.disjoint_below _ (by simp only [VG.Impl.MillerRabin.X86.frameBytes] at hd; omega)

theorem product_frame_header {s : State} {m m' : Mem} {base : Addr} {bytes w o d : Nat}
    (ctx : ProtectedContext s base bytes) (room : CallRoom (s.gpr .esp) base bytes)
    (hf : arrAt w 28 ≤ bytes) (ho : o < 28) (hd : d + 4 ≤ 256)
    (F : Frame [⟨off base (arrAt w o), 8 * w⟩,
      ⟨off base (scratch w), Spec.Rsa.MontMul.scratchBytes w⟩,
      below (s.gpr .esp) 40] m m') : m'.readW (off base d) 32 = m.readW (off base d) 32 := by
  have lo : 256 ≤ arrAt w o := Nat.le_add_right _ _
  have ls : 256 ≤ scratch w := Nat.le_add_right _ _
  have fit : d + 4 ≤ bytes := Nat.le_trans hd (Nat.le_trans (Nat.le_add_right _ _) hf)
  simpa only [Mem.readW] using congrArg (BitVec.setWidth 32)
    (product_frame_read ctx room hf ho fit (.inl (by omega)) (.inl (by omega)) F)

end VG.Proof.MillerRabin.X86
