module

public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine

import VerifiedGarbage.Proof.Dsa.X86.ShapeLoadFrame
import VerifiedGarbage.Proof.Dsa.X86.ShapeLoadWidths
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
/-! # Inspecting the public p component before reusing its workspace -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/ShapeSaveParity.lean`, which only this module imported.
section

/-! # Saving p's parity before reusing the context to inspect q -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem saveParity_ok {s : State} {base : Addr} {size n m : Nat}
    (hs : Scr s base size) (hn : 0 < n) (hz : contextBytes n ≤ size)
    (hm : wordsVal s.mem base (slot n 0) n = m) :
    WP isa (.block (Shape.saveParity n)) s fun t =>
      (shapeWord t base 56).toNat % 2 = m % 2 ∧ Keeps [.eax] s t ∧ Outside base 56 4 s.mem t.mem := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have bh := slot_header n 9
  change 64 ≤ contextBytes n at bh
  simp only [stride] at b0
  unfold Shape.saveParity
  refine wp_movS (readSrc_sc hs (d := slot n 0) (by omega)) fun u uu _ => ?_
  have hu := hs.of_keeps uu.keeps (by decide)
  refine wp_storeS (hu.ea (d := 56) (by omega)) (hu.write (d := 56) (n := 4) (by omega)) fun t mt =>
    WP.block_nil ⟨?_, uu.keeps.trans (mt.keeps _), ?_⟩
  · rw [shapeWord, mt.mem, Mem.readW_writeW_self32, uu.gpr]
    have low := modulus_low hn hm
    change w32 s.mem base (slot n 0) % 2 = m % 2
    omega
  · rw [mt.mem, uu.mem]
    exact writeW32_outside _ _ _ (by decide)

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem inspectP_ok {s : State} {base : Addr} {size len p : Nat}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384)
    (hw4 : len % 4 = 0) (R : OperandReady s base 48 (.input .p) len)
    (hp : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) len) = p) :
    WP isa (Shape.inspectP len) s fun t =>
      shapeWord t base 32 = mask32 (Spec.Dsa.bitLength p = 1024) ∧
      shapeWord t base 36 = mask32 (Spec.Dsa.bitLength p = 2048) ∧
      shapeWord t base 40 = mask32 (Spec.Dsa.bitLength p = 3072) ∧
      (shapeWord t base 56).toNat % 2 = p % 2 ∧
      Keeps shapeClob s t ∧ Outside base 0 (contextBytes 48) s.mem t.mem := by
  have hn : (len + 7) / 8 ≤ 48 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have hsaved : 8256 ≤ size := hz
  unfold Shape.inspectP
  refine WP.seq (WP.mono (loadWidths_ok hs hz rfl h4 hmax hw4 R.toReadableComponent
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
