module
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Writes

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Classify
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Loop
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Live
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Data

/-! # The key-generation controller's tests of its budgets, tape and status (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.PPC64LE.Generation (CtlAccess sign_sub status_guard)
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search

/-- A budget, at the controller's word `j`, compared with zero. -/
theorem budget_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {j n : Nat} (hj : j = 0 ∨ j = 1)
    (hv : (j, BitVec.ofNat 64 n) ∈ p.headers used keys scalars) (hn : n ≤ 128) :
    WP isa (.block [ldf .r9 j]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .d .r9) t = some (decide (n = 0)) := by
  have a := h.access
  have hw := h.header hv
  simp only [Bignum.word, off] at hw
  rcases hj with rfl | rfl <;> simp only [Nat.reduceMul, Nat.mul_zero, BitVec.add_zero] at hw <;>
  · refine WP.mono (WP.keep [.r9] (Q := fun t =>
      isa.eval (.zero .d .r9) t = some (decide (n = 0)) ∧ t.mem = s.mem) ?_ (by decide))
      fun _ ⟨⟨he, hm⟩, k⟩ => ⟨h.keep k hm, he⟩
    prun [ldf, h.r31, hw, a.ld 0 (by decide), a.ld 8 (by decide), a.ld0, BitVec.add_zero]
    refine (eval_zero _ _).trans ?_
    rw [RegUpd.gpr_write_self, ofNat_beq_zero (show n < 2 ^ 64 by omega)]

theorem keys_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [ldf .r9 0]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .d .r9) t = some (decide (keys = 0)) :=
  budget_guard h (j := 0) (.inl rfl) (by simp [KeyPublic.headers]) h.keys_le

theorem scalars_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [ldf .r9 1]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .d .r9) t = some (decide (scalars = 0)) :=
  budget_guard h (j := 1) (.inr rfl) (by simp [KeyPublic.headers]) h.scalars_le

/-- `room`'s bit: the sign of `a − l`, cleared when `a`'s top bit is set. -/
theorem room_bit {a l : Nat} (ha : a < 2 ^ 64) (hl : l < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63 ^^^
      (BitVec.ofNat 64 a >>> 63 &&& (BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63) =
      BitVec.ofNat 64 (if a < l then 1 else 0) := by
  by_cases h : a < 2 ^ 63
  · have ht : BitVec.ofNat 64 a >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      omega
    rw [ht, sign_sub h hl, BitVec.zero_and, BitVec.xor_zero]
  · have ht : BitVec.ofNat 64 a >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      omega
    have hd : (BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63 = 0#64 ∨
        (BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63 = 1#64 := by
      have : ((BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63).toNat < 2 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have := (BitVec.ofNat 64 a - BitVec.ofNat 64 l).isLt
        omega
      rcases (by omega : ((BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63).toNat = 0 ∨
          ((BitVec.ofNat 64 a - BitVec.ofNat 64 l) >>> 63).toNat = 1) with h0 | h1
      · exact .inl (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
      · exact .inr (BitVec.eq_of_toNat_eq (by rw [h1]; rfl))
    have hn : ¬a < l := by omega
    simp only [ht, hn, ↓reduceIte]
    rcases hd with hd | hd <;> rw [hd] <;> decide

/-- Whether the tape holds an attempt: `r12` is zero exactly then. -/
theorem room_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block room) s fun t =>
      KeyLive p original used keys scalars t ∧
        isa.eval (.zero .d .r12) t = some (decide (p.len ≤ p.randLen - used)) := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv10 := h.header (j := 10) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv10
  have hr : p.randLen < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
  have hk : p.len < 2 ^ 63 := by have := h.input.len_lt; omega
  have hb := room_bit (a := p.randLen - used) (show p.randLen - used < 2 ^ 64 by omega) hk
  refine WP.mono (WP.keep [.r9, .r10, .r11, .r12] (Q := fun t =>
    isa.eval (.zero .d .r12) t = some (decide (p.len ≤ p.randLen - used)) ∧ t.mem = s.mem) ?_
    (by decide)) fun _ ⟨⟨he, hm⟩, k⟩ => ⟨h.keep k hm, he⟩
  unfold room
  prun [ldf, h.r31, hv2, hv10, a.ld 16 (by decide), a.ld 80 (by decide), hb]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self]
  by_cases hs : p.randLen - used < p.len
  · simp only [hs, ↓reduceIte, show ¬p.len ≤ p.randLen - used by omega, decide_false]
    decide
  · simp only [hs, ↓reduceIte, show p.len ≤ p.randLen - used by omega, decide_true]
    decide

theorem key_status_lt (r : Spec.Ffdh.KeySearchResult) : r.status < 5 := by
  unfold Spec.Ffdh.KeySearchResult.status; split <;> decide

theorem key_status_ne (r : Spec.Ffdh.KeySearchResult) : r.status ≠ 4 := by
  unfold Spec.Ffdh.KeySearchResult.status; split <;> decide

theorem done_loop_guard {p : KeyPublic} {original s : State} {r : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original r s) :
    WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) s fun t =>
      isa.eval (.zero .d .r9) t = some false ∧ KeyDone p original r t := by
  have a := CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)
  refine WP.mono (status_guard a h.r31 h.status (key_status_lt r)) fun t ⟨⟨he, hm⟩, k⟩ =>
    ⟨?_, h.keep k hm⟩
  rw [he, decide_eq_false (key_status_ne r)]

theorem live_loop_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hs : word s.mem p.control 112 = 4) :
    WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) s fun t =>
      isa.eval (.zero .d .r9) t = some true ∧ KeyLive p original used keys scalars t :=
  WP.mono (status_guard (st := 4) h.access h.r31 hs (by decide))
    fun _ ⟨⟨he, hm⟩, k⟩ => ⟨he, h.keep k hm⟩

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
