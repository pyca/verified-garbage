module

public import VerifiedGarbage.Proof.MillerRabin.X86.SquareStep
import VerifiedGarbage.Proof.Framework.Offset

/-! # Live arrays and header words across repeated squarings -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem square_frame_read {s : State} {m m' : Mem} {base : Addr} {bytes w d n : Nat}
    (ctx : ProtectedContext s base bytes) (room : CallRoom (s.gpr .esp) base bytes)
    (hf : arrAt w 28 ≤ bytes) (hd : d + n ≤ bytes)
    (out : d + n ≤ arrAt w 6 ∨ arrAt w 6 + 8 * w ≤ d)
    (temp : d + n ≤ scratch w ∨ scratch w + Spec.Rsa.MontMul.scratchBytes w ≤ d)
    (headers : ∀ k ∈ [sE2, sF, sQ], d + n ≤ k ∨ k + 4 ≤ d)
    (F : Frame (squareAreas base w (s.gpr .esp)) m m') :
    m'.read (off base d) n = m.read (off base d) n := by
  have nw := ctx.ws.nowrap
  have fo := array_fits_bytes hf (show 6 < 28 by decide)
  have fs : scratch w + Spec.Rsa.MontMul.scratchBytes w ≤ bytes :=
    Nat.le_trans (scratch_before_operand w (by decide : 5 ≤ 28)) hf
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) hf
  refine F.read (r := ⟨off base d, n⟩) (Region.contains_self _ _) ?_ (by omega)
  intro r hr
  simp only [squareAreas, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint _ out (by omega) (by omega)
  · exact Offset.disjoint _ temp (by omega) (by omega)
  · exact room.apart.symm.sub_left (Offset.sub_base _ hd)
  · exact Offset.disjoint _ (headers sE2 (by simp)) (by omega) (by simp only [sE2]; omega)
  · exact Offset.disjoint _ (headers sF (by simp)) (by omega) (by simp only [sF]; omega)
  · exact Offset.disjoint _ (headers sQ (by simp)) (by omega) (by simp only [sQ]; omega)

theorem square_frame_num {s : State} {m m' : Mem} {base : Addr} {bytes w a : Nat}
    (ctx : ProtectedContext s base bytes) (room : CallRoom (s.gpr .esp) base bytes)
    (hf : arrAt w 28 ≤ bytes) (ha : 5 ≤ a ∧ a < 28) (hne : a ≠ 6)
    (F : Frame (squareAreas base w (s.gpr .esp)) m m') : numAt m' base w a = numAt m base w a := by
  have fa := array_fits_bytes hf ha.2
  have lo : 256 ≤ arrAt w a := Nat.le_add_right _ _
  unfold numAt
  rw [square_frame_read ctx room hf (by omega) (arrays_apart w hne)
    (.inr (scratch_before_operand w ha.1)) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> right <;> simp only [sE2, sF, sQ] <;> omega) F]

theorem square_frame_header {s : State} {m m' : Mem} {base : Addr} {bytes w d : Nat}
    (ctx : ProtectedContext s base bytes) (room : CallRoom (s.gpr .esp) base bytes)
    (hf : arrAt w 28 ≤ bytes) (hd : d + 4 ≤ 256)
    (headers : ∀ k ∈ [sE2, sF, sQ], d + 4 ≤ k ∨ k + 4 ≤ d)
    (F : Frame (squareAreas base w (s.gpr .esp)) m m') :
    m'.readW (off base d) 32 = m.readW (off base d) 32 := by
  have lo : 256 ≤ arrAt w 6 := Nat.le_add_right _ _
  have ls : 256 ≤ scratch w := Nat.le_add_right _ _
  have fit : d + 4 ≤ bytes := Nat.le_trans hd (Nat.le_trans (Nat.le_add_right _ _) hf)
  simpa only [Mem.readW] using congrArg (BitVec.setWidth 32)
    (square_frame_read ctx room hf fit (.inl (by omega)) (.inl (by omega)) headers F)

end VG.Proof.MillerRabin.X86
