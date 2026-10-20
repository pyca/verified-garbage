module

import VerifiedGarbage.Proof.Dsa.X86.ShapeThreeWidths
public import VerifiedGarbage.Proof.Dsa.X86.CoreLoad
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Dsa.X86.ShapeFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Actual-width masks directly from an encoded DSA modulus -/

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
