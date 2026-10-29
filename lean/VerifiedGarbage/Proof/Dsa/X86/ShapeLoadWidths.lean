module

public import VerifiedGarbage.Proof.Dsa.X86.CoreLoad
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags

import VerifiedGarbage.Proof.Dsa.X86.ShapeFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86.Width
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
/-! # Actual-width masks directly from an encoded DSA modulus -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/ShapeWidth.lean`, which only this module imported.
section

/-! # Saving actual-width checks in the public domain header -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem shapeWidth_ok {s : State} {base : Addr} {size n bits output : Nat}
    (hs : Scr s base size) (hn : 0 < n) (hz : contextBytes n ≤ size)
    (hb : 0 < bits) (ho : output + 4 ≤ size) :
    WP isa (Shape.saveWidth n bits output) s fun t =>
      shapeWord t base output = mask32 (Spec.Dsa.bitLength (wordsVal s.mem base (slot n 0) n) = bits) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      Outs base [(slot n 8, 8 * n), (output, 4)] s.mem t.mem := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  have sep := slot_le (n := n) (i := 0) (j := 8) (by decide)
  simp only [stride] at b0 b8 sep
  unfold Shape.saveWidth
  refine WP.seq (WP.mono (optionalWidth_ok hs hn (by omega) (by omega) hb (.inl (by omega)))
    fun u ⟨Vu, Ku, Ou⟩ => ?_)
  have hu := hs.of_keeps Ku (by decide)
  refine wp_storeS (hu.ea (by omega)) (hu.write ho) fun t mt => WP.block_nil ⟨?_, Ku.trans (mt.keeps _), ?_⟩
  · rw [shapeWord, mt.mem, Mem.readW_writeW_self32, Vu]
  · have Ot : Outside base output 4 u.mem t.mem := by
      rw [mt.mem]
      exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)
    exact (Outs.of_outside Ou (by simp)).trans (Outs.of_outside Ot (by simp))

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/ShapeThreeWidths.lean`, which only this module imported.
section

/-! # The three candidate widths of each DSA modulus -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem threeWidths_ok {s : State} {base : Addr} {size n a b c output : Nat}
    (hs : Scr s base size) (hn : 0 < n) (hz : contextBytes n ≤ size)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ho : output + 12 ≤ 64) :
    WP isa (Shape.threeWidths n a b c output) s fun t =>
      shapeWord t base output = mask32 (Spec.Dsa.bitLength (wordsVal s.mem base (slot n 0) n) = a) ∧
      shapeWord t base (output + 4) = mask32 (Spec.Dsa.bitLength (wordsVal s.mem base (slot n 0) n) = b) ∧
      shapeWord t base (output + 8) = mask32 (Spec.Dsa.bitLength (wordsVal s.mem base (slot n 0) n) = c) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧ Outs base [(slot n 8, 8 * n), (output, 12)] s.mem t.mem := by
  have bh := slot_header n 9
  change 64 ≤ contextBytes n at bh
  have fit : contextBytes n ≤ 2 ^ 64 := by have := hs.nowrap; omega
  unfold Shape.threeWidths
  refine WP.seq (WP.mono (shapeWidth_ok hs hn hz ha (by omega)) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  refine WP.seq (WP.mono (shapeWidth_ok (hs.of_keeps Ku (by decide)) hn hz hb (by omega))
    fun v ⟨Vv, Kv, Ov⟩ => ?_)
  refine WP.mono (shapeWidth_ok ((hs.of_keeps Ku (by decide)).of_keeps Kv (by decide)) hn hz hc (by omega))
    fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, ?_, ?_, (Ku.trans Kv).trans Kt, ?_⟩
  · rw [widthFrame_header Ot (by omega) (by omega), widthFrame_header Ov (by omega) (by omega), Vu]
  · rw [widthFrame_header Ot (by omega) (by omega), Vv, widthFrame_modulus Ou (by omega) fit]
  · rw [Vt, widthFrame_modulus Ov (by omega) fit, widthFrame_modulus Ou (by omega) fit]
  · exact ((widthFrame_widen Ou (Nat.le_refl _) (by omega)).trans
      (widthFrame_widen Ov (by omega) (by omega))).trans (widthFrame_widen Ot (by omega) (by omega))

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem loadWidths_ok {s : State} {base : Addr} {size len n m a b c output : Nat} {modulus : VG.Impl.Dsa.Layout.Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (hr : ReadableComponent s base (.input modulus) len)
    (hd : Region.Disjoint ⟨(pointerValue base s (.input modulus)).setWidth 64, len⟩ ⟨off base (slot n 0), 8 * n⟩)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ho : output + 12 ≤ 64) :
    WP isa (Shape.loadWidths len modulus a b c output) s fun t =>
      wordsVal t.mem base (slot n 0) n = m ∧
      shapeWord t base output = mask32 (Spec.Dsa.bitLength m = a) ∧
      shapeWord t base (output + 4) = mask32 (Spec.Dsa.bitLength m = b) ∧
      shapeWord t base (output + 8) = mask32 (Spec.Dsa.bitLength m = c) ∧
      Keeps shapeClob s t ∧
      Outs base [(slot n 0, 8 * n), (slot n 8, 8 * n), (output, 12)] s.mem t.mem := by
  have hn0 : 0 < n := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound (show n ≤ 48 by omega)
  have hsize : 8256 ≤ size := hz
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  simp only [stride] at b0
  unfold Shape.loadWidths
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreLoad_ok hs hz (by omega) h4 (by omega) hw4 hr hd)
    fun u ⟨Vu, Ku, Ou⟩ => ?_)
  rw [hm] at Vu
  refine WP.mono (threeWidths_ok (hs.of_keeps Ku (by decide)) hn0 (by omega) ha hb hc ho)
    fun t ⟨Va, Vb, Vc, Kt, Ot⟩ => ?_
  refine ⟨?_, by rw [Va, Vu], by rw [Vb, Vu], by rw [Vc, Vu], (Ku.mono (by decide)).widen Kt, ?_⟩
  · rw [widthFrame_modulus Ot ho (by omega), Vu]
  · have O1 : Outs base [(slot n 0, 8 * n), (slot n 8, 8 * n), (output, 12)] s.mem u.mem :=
      Outs.of_outside Ou (by simp)
    exact O1.trans (Ot.mono (by intro r hr; exact List.mem_cons_of_mem _ hr))

end VG.Proof.Dsa.X86
