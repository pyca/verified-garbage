module
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.X86.ShapeFrame
import VerifiedGarbage.Proof.Dsa.X86.ShapeWidth
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! # The three candidate widths of each DSA modulus -/

@[expose] public section
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
