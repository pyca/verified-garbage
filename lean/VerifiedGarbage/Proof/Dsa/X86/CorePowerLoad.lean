module
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Dsa.X86.StackFrame

import VerifiedGarbage.Proof.Dsa.X86.CoreStore
import VerifiedGarbage.Proof.Dsa.X86.CorePowerFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Complete modular exponentiation call, including byte I/O -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem coreLoadPower_ok {s : State} {base : Addr} {size len expLen n m : Nat} {a b : Pointer} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (he4 : 8 ≤ expLen) (he : expLen ≤ len) (hwe : expLen % 4 = 0)
    (Rq : OperandReady s base n (.input modulus) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b expLen)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (contextRoom : contextBytes n≤size) :
    WP isa (Core.loadPower n len expLen modulus a b) s fun t =>
      wordsVal t.mem base (slot n 0) n=m ∧
      wordsVal t.mem base (slot n 5) n=
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) ∧
      val32 t.mem base (slot n 8) ((expLen+3)/4)=
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) expLen) ∧
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
    (by omega) (by omega) hwe Rbv.toReadableComponent (Rbv.slot (by decide))) fun w ⟨Bw, Kw, Ow⟩ => ?_
  have Ksw := Ksv.trans Kw
  have Opre := Osv.trans (slotOutside_whole Ow (by decide))
  have Mw : wordsVal w.mem base (slot n 0) n = m := by
    rw [slotOutside_val Ow (by decide) (by have := bounds 0 (by decide); omega),
      slotOutside_val Ov (by decide) (by have := bounds 0 (by decide); omega), Mu, hm]
  have Aw : wordsVal w.mem base (slot n 5) n =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) := by
    rw [slotOutside_val Ow (by decide) (by have := bounds 5 (by decide); omega), Av,
      Ra.bytes Ku (by decide) Ou' hn48]
  rw [Rb.bytes Ksv (by decide) Osv hn48] at Bw
  have ek : (expLen + 3) / 4 ≤ 2 * n := by omega
  have Ew : val32 w.mem base (slot n 8) ((expLen + 3) / 4) =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) expLen) := by
    rw [wordsVal_eq_val32] at Bw
    rw [val32_prefix_of_lt ek (by rw [Bw]; exact decoded_exponent_fits _ _ _), Bw]
  exact ⟨Mw,Aw,Ew,Opre,Ksw⟩

end VG.Proof.Dsa.X86
