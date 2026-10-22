module

public import VerifiedGarbage.Proof.MillerRabin.X86.ProtectedTail
public import VerifiedGarbage.Proof.MillerRabin.X86.ProtectedArray
import VerifiedGarbage.Proof.Framework.Offset

/-! # Both protected prefixes are retained before any Montgomery operation -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem saveProtected_ok {s : State} {base : Addr} {bytes w : Nat}
    (h : ProtectedContext s base bytes) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ bytes) (hwidth : s.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) :
    WP isa saveProtected s fun t =>
      t.mem.read (off (byteAddr (s.gpr .esp)) savedTail) 32 = s.mem.read (off base (scratch w)) 32 ∧
      t.mem.read (off (byteAddr (s.gpr .esp)) savedArray) (8 * w) = s.mem.read (off base (arrAt w 4)) (8 * w) ∧
      Frame [⟨off (byteAddr (s.gpr .esp)) savedTail, 32⟩,
        ⟨off (byteAddr (s.gpr .esp)) savedArray, 8 * w⟩] s.mem t.mem ∧
      Keeps transferClobbers s t := by
  have tailFit : savedTail + 32 ≤ VG.Impl.MillerRabin.X86.frameBytes := by decide
  have arrayFit := saved_array_fits_frame hu
  have scratchBound : scratch w + 32 ≤ bytes := by
    have := scratch_start w
    have := array_monotone w (show 2 ≤ 28 by decide)
    omega
  have arrayBound : arrAt w 4 + 8 * w ≤ bytes := by
    have := array_fits_bytes hf (show 4 < 28 by decide)
    omega
  have h52 : 52 ≤ bytes := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hf; omega
  have nw := h.ws.nowrap
  unfold saveProtected
  refine WP.seq (WP.mono (saveTail_ok h hf hwidth) fun u R₁ => ?_)
  have F₁ := R₁.frame
  have V₁ := R₁.value
  rw [h.stack_address (by decide)] at F₁
  rw [h.stack_address (by decide), ptr32_addr (by omega : base.toNat + scratch w < 2 ^ 32)] at V₁
  have huCtx := h.of_keeps R₁.keeps
  have widthU : u.mem.readW (off base 48) 32 = BitVec.ofNat 32 w := by
    rw [h.stack_frame_readW tailFit F₁ h52, hwidth]
  refine WP.mono (saveArray_ok huCtx hw hu hf widthU) fun t R₂ => ?_
  have F₂ := R₂.frame
  have V₂ := R₂.value
  have sp : u.gpr .esp = s.gpr .esp := R₁.keeps.1 _ (by decide)
  rw [huCtx.stack_address (by decide), sp] at F₂
  rw [huCtx.stack_address (by decide), sp,
    ptr32_addr (by omega : base.toNat + arrAt w 4 < 2 ^ 32),
    h.stack_frame_read tailFit F₁ arrayBound] at V₂
  have tailKeeps : t.mem.read (off (byteAddr (s.gpr .esp)) savedTail) 32 =
      u.mem.read (off (byteAddr (s.gpr .esp)) savedTail) 32 := by
    exact F₂.read (r := ⟨off (byteAddr (s.gpr .esp)) savedTail, 32⟩) (Region.contains_self _ _)
      (by
        intro r hr
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by simp only [savedArray]; omega))
      (by decide)
  exact ⟨tailKeeps.trans V₁, V₂,
    (F₁.mono (by simp)).trans (F₂.mono (by simp)), R₁.keeps.trans R₂.keeps⟩

end VG.Proof.MillerRabin.X86
