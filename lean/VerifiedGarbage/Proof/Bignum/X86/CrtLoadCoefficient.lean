module

public import VerifiedGarbage.Impl.Bignum.X86.CrtCore
public import VerifiedGarbage.Proof.Bignum.X86.CrtFrame
import VerifiedGarbage.Proof.Bignum.X86.CrtSlotFrame

/-! # Load the two residues and CRT inverse into the reusable arithmetic context -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Bignum.X86.Crt

theorem loadCoefficient_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes) :
    WP isa (loadCoefficient n) s fun t =>
      wordsVal t.mem base (slot n 0) n = wordsVal s.mem base (slot n pSlot) n ∧
      wordsVal t.mem base (slot n 5) n = wordsVal s.mem base (slot n mqSlot) n ∧
      wordsVal t.mem base (slot n 6) n = wordsVal s.mem base (slot n mpSlot) n ∧
      wordsVal t.mem base (slot n 8) n = wordsVal s.mem base (slot n inverseSlot) n ∧
      Outs base (arithmeticRanges n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have fit : size n ≤ 2 ^ 64 := by have := hs.nowrap; omega
  unfold loadCoefficient
  refine WP.seq (WP.mono (copySlot_ok hs hn hz (by decide) (by decide) (by decide)) fun u ⟨P, O, K⟩ => ?_)
  refine WP.seq (WP.mono (copySlot_ok (hs.of_keeps K (by decide)) hn hz
    (by decide) (by decide) (by decide)) fun v ⟨Q, Ov, Kv⟩ => ?_)
  have Ksv := K.trans Kv
  refine WP.seq (WP.mono (copySlot_ok (hs.of_keeps Ksv (by decide)) hn hz
    (by decide) (by decide) (by decide)) fun w ⟨Mp, Ow, Kw⟩ => ?_)
  have Ksw := Ksv.trans Kw
  refine WP.mono (copySlot_ok (hs.of_keeps Ksw (by decide)) hn hz
    (by decide) (by decide) (by decide)) fun t ⟨QI, Ot, Kt⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, (((slot_arithmetic_frame O (by decide) (by omega)).trans
    (slot_arithmetic_frame Ov (by decide) (by omega))).trans (slot_arithmetic_frame Ow (by decide) (by omega))).trans
      (slot_arithmetic_frame Ot (by decide) (by omega)), Ksw.trans Kt⟩
  · rw [slot_value Ot (by decide) (by decide) (by omega) (by omega) fit,
      slot_value Ow (by decide) (by decide) (by omega) (by omega) fit,
      slot_value Ov (by decide) (by decide) (by omega) (by omega) fit, P]
  · rw [slot_value Ot (by decide) (by decide) (by omega) (by omega) fit,
      slot_value Ow (by decide) (by decide) (by omega) (by omega) fit, Q,
      slot_value O (by decide) (by decide) (by omega) (by omega) fit]
  · rw [slot_value Ot (by decide) (by decide) (by omega) (by omega) fit, Mp,
      slot_value Ov (by decide) (by decide) (by omega) (by omega) fit,
      slot_value O (by decide) (by decide) (by omega) (by omega) fit]
  · rw [QI, slot_value Ow (by decide) (by decide) (by omega) (by omega) fit,
      slot_value Ov (by decide) (by decide) (by omega) (by omega) fit,
      slot_value O (by decide) (by decide) (by omega) (by omega) fit]

end VG.Proof.Bignum.X86.Crt
