module

import VerifiedGarbage.Proof.Dsa.X86.Layout
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
    (ham : amount ≤ m)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Validate.minus len modulus amount output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len (m - amount) ∧
      Outs base [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  simp only [stride] at b0
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  simp only [stride] at b6
  unfold Validate.minus
  dsimp only
  rw [← hn]
  have hn0 : 0 < n := by omega
  have hn48 : n ≤ 48 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hsaved : 8256 ≤ size := hz
  refine WP.seq (WP.mono (coreLoad_ok hs hz (by omega) h4 (by omega) hw4
    R.toReadableComponent (R.slot (by decide))) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  have Hu := hs.of_keeps Ku (by decide)
  have Oload : Outside base 0 (contextBytes n) s.mem u.mem :=
    slotOutside_whole Ou (by decide)
  refine WP.seq (WP.mono (modulusMinus_ok Hu hn0 (by omega) (Vu.trans hm) ham)
    fun v ⟨Vv, Ov, Kv⟩ => ?_)
  have Hv := Hu.of_keeps Kv (by decide)
  refine WP.mono (coreStore_ok Hv hz hn.symm (by omega) h4 (by omega) hw4 ho (by omega))
    fun t ⟨Vt, Kt, Ot⟩ => ?_
  exact ⟨by rw [Vt, Vv], (Outs.of_outside (Oload.trans Ov) (by simp)).trans (Outs.of_outside Ot (by simp)),
    ((Ku.mono (by decide)).trans (Kv.mono (by decide))).trans (Kt.mono (by decide))⟩

end VG.Proof.Dsa.X86
