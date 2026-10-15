module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeLoadFrame
public import VerifiedGarbage.Proof.Dsa.X86.ShapeSaveParity

/-! # Inspecting the public p component before reusing its workspace -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem inspectP_ok {s : State} {base : Addr} {size len p : Nat}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384)
    (R : OperandReady s base 48 (.input .p) len)
    (hp : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) len) = p) :
    WP isa (.block (Shape.inspectP len)) s fun t =>
      shapeWord t base 32 = mask32 (Spec.Dsa.bitLength p = 1024) ∧
      shapeWord t base 36 = mask32 (Spec.Dsa.bitLength p = 2048) ∧
      shapeWord t base 40 = mask32 (Spec.Dsa.bitLength p = 3072) ∧
      (shapeWord t base 56).toNat % 2 = p % 2 ∧
      Keeps [.esi, .eax, .ebx, .edx] s t ∧ Outside base 0 (contextBytes 48) s.mem t.mem := by
  have hn : (len + 7) / 8 ≤ 48 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have hsaved : 8256 ≤ size := hz
  unfold Shape.inspectP
  refine WP.block_append (WP.mono (loadWidths_ok hs hz rfl h4 hmax R.toReadableComponent
    ((R.smaller hn).slot (by decide)) hp (by decide) (by decide) (by decide) (by decide))
    fun u ⟨Mu, P1, P2, P3, Ku, Ou⟩ => ?_)
  refine WP.mono (saveParity_ok (hs.of_keeps Ku (by decide)) (by omega) (by omega) Mu)
    fun t ⟨Pt, Kt, Ot⟩ => ?_
  refine ⟨?_, ?_, ?_, Pt, Ku.widen Kt, ?_⟩
  · rw [outside_shapeWord Ot (by decide) (.inl (by decide)), P1]
  · rw [outside_shapeWord Ot (by decide) (.inl (by decide)), P2]
  · rw [outside_shapeWord Ot (by decide) (.inl (by decide)), P3]
  · exact (loadWidths_whole Ou hn (by decide)).trans (Ot.mono (o' := 0) (n' := contextBytes 48) (by decide) (by decide))

end VG.Proof.Dsa.X86
