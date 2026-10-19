module
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame

import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout

/-! # Paired component loading without assuming a valid modulus -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem rawInputs_ok {s : State} {base : Addr} {size n al bl i j : Nat} {a b : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (hn : n ≤ 48)
    (hi : i < 9) (hj : j < 9) (hij : i ≠ j)
    (ha4 : 4 ≤ al) (ha : al ≤ 8 * n) (hb4 : 4 ≤ bl) (hb : bl ≤ 8 * n) (hwa : al % 4 = 0) (hwb : bl % 4 = 0)
    (Ra : OperandReady s base n a al) (Rb : OperandReady s base n b bl) :
    WP isa (.seq (Core.load n al (slot n i) a) (Core.load n bl (slot n j) b)) s fun t =>
      wordsVal t.mem base (slot n i) n = Spec.Dsa.decodeBE
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) al) ∧
      wordsVal t.mem base (slot n j) n = Spec.Dsa.decodeBE
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) bl) ∧
      Outside base 0 (contextBytes n) s.mem t.mem ∧ Keeps loadClob s t := by
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have hsize : 8256 ≤ size := hz
  have bound (k : Nat) (hk : k < 9) : slot n k + 8 * n ≤ size := by
    have := slot_bound (n := n) hk
    simp only [stride] at *
    omega
  refine WP.seq (WP.mono (coreLoad_ok hs hz (bound i hi) ha4 ha hwa
    Ra.toReadableComponent (Ra.slot hi)) fun u ⟨Au, Ku, Ou⟩ => ?_)
  have OWu := slotOutside_whole Ou hi
  have Rbu := Rb.keep Ku (by decide) OWu hn
  refine WP.mono (coreLoad_ok (hs.of_keeps Ku (by decide)) hz (bound j hj) hb4 hb hwb
    Rbu.toReadableComponent (Rbu.slot hj)) fun t ⟨Bt, Kt, Ot⟩ => ?_
  refine ⟨?_, ?_, OWu.trans (slotOutside_whole Ot hj), Ku.trans Kt⟩
  · rw [slotOutside_val Ot hij (by have := bound i hi; have := hs.nowrap; omega), Au]
  · rw [Bt, Rb.bytes Ku (by decide) OWu hn]

end VG.Proof.Dsa.X86
