module

public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # Loading a pair of operands while retaining Montgomery constants -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem coreInputs_ok {s : State} {base : Addr} {size n m al bl : Nat} {a b : Pointer}
    (h : Context n m base size s) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (hn : n ≤ 48)
    (ha4 : 4 ≤ al) (ha : al ≤ 8 * n) (hb4 : 4 ≤ bl) (hb : bl ≤ 8 * n) (hwa : al % 4 = 0) (hwb : bl % 4 = 0)
    (Ra : OperandReady s base n a al) (Rb : OperandReady s base n b bl) :
    WP isa (.seq (Core.load n al (slot n 5) a) (Core.load n bl (slot n 8) b)) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 5) n = Spec.Dsa.decodeBE
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) al) ∧
      wordsVal t.mem base (slot n 8) n = Spec.Dsa.decodeBE
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) bl) ∧
      (∀ j, j = 3 ∨ j = 4 → wordsVal t.mem base (slot n j) n = wordsVal s.mem base (slot n j) n) ∧
      Outside base 0 (contextBytes n) s.mem t.mem ∧ Keeps loadClob s t := by
  have bound (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ 2 ^ 64 := by
    have := slot_bound (n := n) hj
    have := h.size_le
    have := h.scr.nowrap
    simp only [stride] at *
    omega
  refine WP.seq (WP.mono (coreLoadSlot_ok h hz (by decide) (by decide) ha4 ha hwa
    Ra.toReadableComponent (Ra.slot (by decide))) fun u ⟨Cu, Au, Ku, Ou⟩ => ?_)
  have OWu := slotOutside_whole Ou (by decide)
  have Rbu := Rb.keep Ku (by decide) OWu hn
  refine WP.mono (coreLoadSlot_ok Cu hz (by decide) (by decide) hb4 hb hwb Rbu.toReadableComponent
    (Rbu.slot (by decide))) fun t ⟨Ct, Bt, Kt, Ot⟩ => ?_
  refine ⟨Ct, ?_, ?_, ?_, OWu.trans (slotOutside_whole Ot (by decide)), Ku.trans Kt⟩
  · rw [slotOutside_val Ot (by decide) (bound 5 (by decide)), Au]
  · rw [Bt, Rb.bytes Ku (by decide) OWu hn]
  · intro j hj
    rw [slotOutside_val Ot (by omega) (bound j (by omega)),
      slotOutside_val Ou (by omega) (bound j (by omega))]

end VG.Proof.Dsa.X86
