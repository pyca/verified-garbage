module

import VerifiedGarbage.Proof.Dsa.X86.CheckZero
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Zero checks on encoded DSA intermediates -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem validateZero_ok {s : State} {base : Addr} {size len n : Nat} {input : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (R : OperandReady s base n input len) (wantNonzero : Bool) :
    WP isa (Validate.zero len input wantNonzero) s fun t =>
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        (if wantNonzero then Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) len) ≠ 0
          else Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) len) = 0) ∧
      Keeps powerClob s t ∧
      Outs base [(0, contextBytes n), (Layout.field .mask, 4)] s.mem t.mem := by
  have hn48 : n ≤ 48 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hsize : 8256 ≤ size := hz
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  simp only [stride] at b5
  unfold Validate.zero
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreLoad_ok hs hz (by omega) h4 (by omega) hw4 R.toReadableComponent
    (R.slot (by decide))) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  have OWu := slotOutside_whole Ou (by decide)
  have Fu : flagW base (Layout.field .mask) u = flagW base (Layout.field .mask) s :=
    pointerValue_keep Ku (by decide) OWu (by omega) (.input .mask)
  refine WP.mono (checkZero_ok (hs.of_keeps Ku (by decide)) (by omega) (by omega)
    (by change 8248 ≤ size; omega) wantNonzero) fun t ⟨Vt, Kt, Ot⟩ => ?_
  exact ⟨by rw [Vt, Fu, Vu], (Ku.mono (by decide)).widen Kt,
    (Outs.of_outside OWu (by simp)).trans (Outs.of_outside Ot (by simp))⟩

end VG.Proof.Dsa.X86
