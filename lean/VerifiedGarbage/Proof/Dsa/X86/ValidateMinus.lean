module

import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Dsa.X86.CoreStore
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
import VerifiedGarbage.Proof.Dsa.X86.Minus
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! # Encoded p - 1 and q - 2 for domain checks and exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem validateMinus_ok {s : State} {base : Addr} {size len n m amount output : Nat} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (R : OperandReady s base n (.input modulus) len)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1) (ham : amount ≤ m)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Validate.minus len modulus amount output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len (m - amount) ∧
      Outs base [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t := by
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  simp only [stride] at b6
  unfold Validate.minus
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreSetup_ok hs hz hn h4 hmax hw4 R.toReadableComponent (R.slot (by decide)) hm hm1 hodd)
    fun u ⟨Cu, _, _, Ou, Ku⟩ => ?_)
  refine WP.seq (WP.mono (modulusMinus_ok Cu ham) fun v ⟨Cv, Vv, Ov, Kv⟩ => ?_)
  refine WP.mono (coreStore_ok Cv.scr hz hn.symm (by have := Cv.size_le; omega) h4 (by omega) hw4 ho (by omega))
    fun t ⟨Vt, Kt, Ot⟩ => ?_
  exact ⟨by rw [Vt, Vv], (Outs.of_outside (Ou.trans Ov) (by simp)).trans (Outs.of_outside Ot (by simp)),
    (Ku.trans (Kv.mono (by decide))).trans (Kt.mono (by decide))⟩

end VG.Proof.Dsa.X86
