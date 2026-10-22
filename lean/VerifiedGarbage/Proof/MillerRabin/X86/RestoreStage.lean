module

public import VerifiedGarbage.Proof.MillerRabin.X86.RestoredFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFacts
import VerifiedGarbage.Proof.Framework.Offset

/-! # Restore the original prefixes saved before the arithmetic began -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem restore_stack_read {s : State} {m m' : Mem} {base : Addr} {bytes w d n : Nat}
    (ctx : ProtectedContext s base bytes) (hf : arrAt w 28 ≤ bytes)
    (hd : d + n ≤ VG.Impl.MillerRabin.X86.frameBytes)
    (F : Frame [⟨off base (scratch w), 32⟩, ⟨off base (arrAt w 4), 8 * w⟩] m m') :
    m'.read (off (byteAddr (s.gpr .esp)) d) n = m.read (off (byteAddr (s.gpr .esp)) d) n := by
  have tailFit : scratch w + 32 ≤ bytes := by
    have := scratch_start w
    have := array_monotone w (show 2 ≤ 28 by decide)
    omega
  have arrayFit := array_fits_bytes hf (show 4 < 28 by decide)
  refine F.read (r := ⟨off (byteAddr (s.gpr .esp)) d, n⟩) (Region.contains_self _ _) ?_
    (by simp only [VG.Impl.MillerRabin.X86.frameBytes] at hd; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (ctx.apart.symm.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ tailFit)
  · exact (ctx.apart.symm.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ (by omega))

theorem restore_stage {σ s : State} {base : Addr} {bytes w len : Nat}
    (facts : RoundFacts σ base bytes w) (h : Stage base bytes w σ s) (size : bytes = 8 * len)
    (tail : σ.mem.read (off (byteAddr (σ.gpr .esp)) savedTail) 32 = σ.mem.read (off base (scratch w)) 32)
    (array : σ.mem.read (off (byteAddr (σ.gpr .esp)) savedArray) (8 * w) = σ.mem.read (off base (arrAt w 4)) (8 * w)) :
    WP isa restoreProtected s fun t =>
      Spec.MillerRabin.Keeps Spec.MillerRabin.compact base len w σ.mem t.mem ∧
      w32 t.mem base sF = w32 s.mem base sF ∧
      Frame [⟨off base (scratch w), 32⟩, ⟨off base (arrAt w 4), 8 * w⟩] s.mem t.mem ∧
      Keeps transferClobbers s t := by
  refine WP.mono (restoreProtected_ok h.context facts.lower facts.upper facts.fit (h.width facts.fit facts.width)) ?_
  rintro t ⟨tailT, arrayT, frame, keeps⟩
  rw [h.stack, h.read_stack facts.fit (by decide) (.inr (by decide)), tail] at tailT
  rw [h.stack, h.read_stack facts.fit (saved_array_fits_frame facts.upper) (.inr (by decide)), array] at arrayT
  refine ⟨restored_frame_keeps h size facts.fit frame tailT arrayT, ?_, frame, keeps⟩
  have nw := h.context.ws.nowrap
  have arrayFit := array_fits_bytes facts.fit (show 4 < 28 by decide)
  have lo : 256 ≤ arrAt w 4 := Nat.le_add_right _ _
  have temp : 256 ≤ scratch w := Nat.le_add_right _ _
  have fit := facts.fit
  have bounds : scratch w + 32 ≤ bytes := by
    have := scratch_start w
    have := array_monotone w (show 2 ≤ 28 by decide)
    omega
  have read := frame.readW (w := 32) (a := off base sF) (r := ⟨off base sF, 4⟩) (Region.contains_self _ _)
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inl (by change 236 ≤ scratch w; omega)) (by decide) (by omega)
      · exact Offset.disjoint _ (.inl (by change 236 ≤ arrAt w 4; omega)) (by decide) (by omega))
    (by decide)
  exact congrArg BitVec.toNat read

end VG.Proof.MillerRabin.X86
