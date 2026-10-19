module

public import VerifiedGarbage.Impl.Bignum.X86.CrtCore
public import VerifiedGarbage.Proof.Bignum.X86.CrtSlotFrame

/-! # Load one factor, base and exponent while preserving all original components -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Bignum.X86.Crt

theorem loadPower_ok {s : State} {base : Addr} {bytes n prime exponent : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes)
    (hp : 9 ≤ prime) (hp' : prime < 16) (he : 9 ≤ exponent) (he' : exponent < 16) :
    WP isa (loadPower n prime exponent) s fun t =>
      wordsVal t.mem base (slot n 0) n = wordsVal s.mem base (slot n prime) n ∧
      wordsVal t.mem base (slot n 5) n = wordsVal s.mem base (slot n inputSlot) n ∧
      wordsVal t.mem base (slot n 8) n = wordsVal s.mem base (slot n exponent) n ∧
      Outs base (arithmeticRanges n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have fit : size n ≤ 2 ^ 64 := by have := hs.nowrap; omega
  unfold loadPower
  refine WP.seq (WP.mono (copySlot_ok hs hn hz (by omega) (by decide) (by omega)) fun u ⟨P, O, K⟩ => ?_)
  refine WP.seq (WP.mono (copySlot_ok (hs.of_keeps K (by decide)) hn hz
    (by unfold inputSlot; decide) (by decide) (by unfold inputSlot; decide)) fun v ⟨X, Ov, Kv⟩ => ?_)
  have Ksv := K.trans Kv
  refine WP.mono (copySlot_ok (hs.of_keeps Ksv (by decide)) hn hz
    (by omega) (by decide) (by omega)) fun t ⟨E, Ot, Kt⟩ => ?_
  refine ⟨?_, ?_, ?_, ((slot_arithmetic_frame O (by decide) (by omega)).trans
    (slot_arithmetic_frame Ov (by decide) (by omega))).trans (slot_arithmetic_frame Ot (by decide) (by omega)), Ksv.trans Kt⟩
  · rw [slot_value Ot (by decide) (by decide) (by omega) (by omega) fit,
      slot_value Ov (by decide) (by decide) (by omega) (by omega) fit, P]
  · rw [slot_value Ot (by decide) (by decide) (by omega) (by omega) fit, X,
      slot_value O (by unfold inputSlot; decide) (by unfold inputSlot; decide) (by omega) (by omega) fit]
  · rw [E, slot_value Ov (by omega) (by omega) (by omega) (by omega) fit,
      slot_value O (by omega) (by omega) (by omega) (by omega) fit]

end VG.Proof.Bignum.X86.Crt
