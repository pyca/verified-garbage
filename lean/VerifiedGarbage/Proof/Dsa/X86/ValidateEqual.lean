module
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame

import VerifiedGarbage.Proof.Dsa.X86.RawInputs
import VerifiedGarbage.Proof.Dsa.X86.ValidateMasks
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Equality validation of encoded DSA values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem validateEqual_ok {s : State} {base : Addr} {size len n : Nat} {a b : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b len) :
    WP isa (Validate.equalValues len a b) s fun t =>
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) =
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len)) ∧
      Keeps powerClob s t ∧
      Outs base [(0, contextBytes n), (Layout.field .mask, 4)] s.mem t.mem := by
  have hn48 : n ≤ 48 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hsize : 8256 ≤ size := hz
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  simp only [stride] at b5 b8
  unfold Validate.equalValues Validate.accumulate
  dsimp only
  rw [← hn]
  refine wp_seq_assoc (WP.seq (WP.mono (rawInputs_ok hs hz hn48 (by decide) (by decide) (by decide)
    h4 (by omega) h4 (by omega) hw4 hw4 Ra Rb) fun u ⟨Au, Bu, Ou, Ku⟩ => ?_))
  have Fu : flagW base (Layout.field .mask) u = flagW base (Layout.field .mask) s :=
    pointerValue_keep Ku (by decide) Ou (by omega) (.input .mask)
  refine WP.mono (accumulateEqual_ok (hs.of_keeps Ku (by decide)) (by omega) (by omega) (by omega)
    (by change 8248 ≤ size; omega)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  exact ⟨by rw [Vt, Fu, Au, Bu], (Ku.mono (by decide)).widen Kt,
    (Outs.of_outside Ou (by simp)).trans (Outs.of_outside Ot (by simp))⟩

end VG.Proof.Dsa.X86
