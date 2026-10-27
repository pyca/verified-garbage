module
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame

import VerifiedGarbage.Proof.Dsa.X86.CorePowerFrame
import VerifiedGarbage.Proof.Dsa.X86.CoreStore
import VerifiedGarbage.Proof.Dsa.X86.MulCall
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout

/-! # Complete ordinary modular product call, including byte I/O

The modulus and both operands are loaded into the context's slots 0, 5 and
8, the width's shared product (`vg_dsa_mulmod_{n}`, `Mul.call_ok`) leaves
their product in slot 6, and it is stored as bytes. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

/-- The modulus and both operands, at full width, into slots 0, 5 and 8. -/
theorem coreLoadProduct_ok {s : State} {base : Addr} {size len n m : Nat} {a b : Pointer} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input modulus) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b len)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (contextRoom : contextBytes n ≤ size) :
    WP isa (Core.loadPower n len len modulus a b) s fun t =>
      wordsVal t.mem base (slot n 0) n = m ∧
      wordsVal t.mem base (slot n 5) n =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) ∧
      wordsVal t.mem base (slot n 8) n =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len) ∧
      Outside base 0 (contextBytes n) s.mem t.mem ∧ Keeps loadClob s t := by
  have hn48 : n ≤ 48 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hl : len ≤ 8 * n := by omega
  have nw := hs.nowrap
  have bound (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ contextBytes n := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by have := bound j hj; omega
  unfold Core.loadPower
  refine WP.seq (WP.mono (coreLoad_ok hs hz (bounds 0 (by decide)) h4 hl hw4
    Rq.toReadableComponent (Rq.slot (by decide))) fun u ⟨Mu, Ku, Ou⟩ => ?_)
  have Ou' := slotOutside_whole Ou (by decide)
  have Rau := Ra.keep Ku (by decide) Ou' hn48
  have Rbu := Rb.keep Ku (by decide) Ou' hn48
  refine WP.seq (WP.mono (coreLoad_ok (hs.of_keeps Ku (by decide)) hz
    (bounds 5 (by decide)) h4 hl hw4 Rau.toReadableComponent (Rau.slot (by decide)))
    fun v ⟨Av, Kv, Ov⟩ => ?_)
  have Ov' := slotOutside_whole Ov (by decide)
  have Rbv := Rbu.keep Kv (by decide) Ov' hn48
  have Ksv := Ku.trans Kv
  have Osv := Ou'.trans Ov'
  refine WP.mono (coreLoad_ok (hs.of_keeps Ksv (by decide)) hz (bounds 8 (by decide))
    h4 hl hw4 Rbv.toReadableComponent (Rbv.slot (by decide))) fun w ⟨Bw, Kw, Ow⟩ => ?_
  refine ⟨?_, ?_, ?_, Osv.trans (slotOutside_whole Ow (by decide)), Ksv.trans Kw⟩
  · rw [slotOutside_val Ow (by decide) (by have := bounds 0 (by decide); omega),
      slotOutside_val Ov (by decide) (by have := bounds 0 (by decide); omega), Mu, hm]
  · rw [slotOutside_val Ow (by decide) (by have := bounds 5 (by decide); omega), Av,
      Ra.bytes Ku (by decide) Ou' hn48]
  · rw [Bw, Rb.bytes Ksv (by decide) Osv hn48]

theorem coreProductMod_ok {s : State} {base : Addr} {size len n m output : Nat} {a b : Pointer} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (room : Pow.Room (s.gpr .esp) base size) (hused : usedBytes ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input modulus) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b len)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.productMod len modulus a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) *
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len) % m) ∧
      StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t := by
  have hn48 : n ≤ 48 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hl : len ≤ 8 * n := by omega
  have bound (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ contextBytes n := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by have := bound j hj; omega
  unfold Core.productMod
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreLoadProduct_ok hs hz hn h4 hmax hw4 Rq Ra Rb hm (by omega))
    fun w ⟨Mw, Aw, Bw, Opre, Ksw⟩ => ?_)
  have Wscr := hs.of_keeps Ksw (by decide)
  refine WP.seq (WP.mono (Mul.call_ok Wscr (by rw [Ksw.1 _ (by decide)]; exact room)
    (by omega) hused (by omega) hn48 Mw hm1 hodd) fun v ⟨Vv, Ov, Kv⟩ => ?_)
  refine WP.mono (coreStore_ok (Wscr.of_keeps Kv (by decide)) hz hn.symm
    (bounds 6 (by decide)) h4 hl hw4 ho (by have := bound 6 (by decide); omega)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨by rw [Vt, Vv, Aw, Bw], ?_, ?_⟩
  · rw [Ksw.1 _ (by decide)] at Ov
    have Of : StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] w.mem v.mem :=
      Ov.mono fun r hr => ⟨(0, contextBytes n), by simp, by omega,
        by simpa only [Nat.zero_add] using Pow.scratch_fits (Nat.le_refl _) r hr⟩
    exact ((StackOuts.of_outs (Outs.of_outside Opre (by simp))).trans Of).trans
      (StackOuts.of_outs (Outs.of_outside Ot (by simp)))
  · exact ((Ksw.mono (by decide)).trans (Kv.mono (by decide))).trans (Kt.mono (by decide))

theorem coreProduct_ok {s : State} {base : Addr} {size len n m output : Nat} {a b : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (room : Pow.Room (s.gpr .esp) base size) (hused : usedBytes ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input .q) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b len)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) len) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.product len a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) *
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len) % m) ∧
      StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t :=
  coreProductMod_ok hs hz room hused hn h4 hmax hw4 Rq Ra Rb hm hm1 hodd ho hfar

end VG.Proof.Dsa.X86
