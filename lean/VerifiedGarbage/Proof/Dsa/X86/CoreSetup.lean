module

public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! ### `Dsa.X86.CoreInputs`, which the modules that import this one used -/

section

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
    omega_arith
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
    rw [slotOutside_val Ot (by omega_using [hj]) (bound j (by omega_using [hj])),
      slotOutside_val Ou (by omega_using [hj]) (bound j (by omega_using [hj]))]

end VG.Proof.Dsa.X86

end

end

/-! # Reinitializing the shared context from a DSA modulus -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem setupRanges_whole {n : Nat} {base : Addr} {s t : State}
    (O : Outs base (setupRanges n) s.mem t.mem) : Outside base 0 (contextBytes n) s.mem t.mem := by
  have b1 := slot_bound (n := n) (i := 1) (by decide)
  have b2 := slot_bound (n := n) (i := 2) (by decide)
  have b3 := slot_bound (n := n) (i := 3) (by decide)
  have b4 := slot_bound (n := n) (i := 4) (by decide)
  have bh := slot_header n 9
  change 64 ≤ contextBytes n at bh
  simp only [stride] at b1 b2 b3 b4
  intro x hx
  apply O x
  intro r hr
  simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> omega_arith

theorem coreSetup_ok {s : State} {base : Addr} {size len n m : Nat} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (hr : ReadableComponent s base (.input modulus) len)
    (hd : Region.Disjoint ⟨(pointerValue base s (.input modulus)).setWidth 64, len⟩ ⟨off base (slot n 0), 8 * n⟩)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (Core.setup len modulus) s fun t =>
      Context n m base size t ∧ wordsVal t.mem base (slot n 3) n = 1 ∧
      wordsVal t.mem base (slot n 4) n = 2 ^ (128 * n) % m ∧
      Outside base 0 (contextBytes n) s.mem t.mem ∧ Keeps powerClob s t := by
  have hn0 : 0 < n := by omega_using [hn, h4]
  have hn48 : n ≤ 48 := by omega_using [hn, hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hsaved : 8256 ≤ size := hz
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  simp only [stride] at b0
  unfold Core.setup
  rw [← hn]
  refine WP.seq (WP.mono (coreLoad_ok hs hz (by omega_using [cb, hsaved, b0]) h4 (by omega_using [hn]) hw4 hr hd)
    fun u ⟨Vu, Ku, Ou⟩ => ?_)
  refine WP.mono (contextSetup_ok (hs.of_keeps Ku (by decide)) hn0 (by omega_using [hn48]) (by omega_using [cb, hsaved])
    (Vu.trans hm) hm1 hodd) fun t ⟨Ct, One, R2, Ot, Kt⟩ => ?_
  refine ⟨Ct, One, R2, ?_, (Ku.mono (by decide)).trans Kt⟩
  exact (Ou.mono (o' := 0) (n' := contextBytes n) (by omega_using []) (by omega_using [b0])).trans (setupRanges_whole Ot)

end VG.Proof.Dsa.X86
