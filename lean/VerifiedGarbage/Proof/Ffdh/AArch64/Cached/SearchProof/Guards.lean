module
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Writes

import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Entry

/-! # The key-generation controller's tests of its budgets, tape and status (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search
open VG.Impl.Bignum.AArch64 (movi)

theorem ofNat_beq_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h]
  exact Iff.rfl

/-- A budget, at the controller's word `j`, compared with zero. -/
theorem budget_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {j n : Nat} (hj : j = 0 ∨ j = 1)
    (hv : (j, BitVec.ofNat 64 n) ∈ p.headers used keys scalars) (hn : n ≤ 128) :
    WP isa (.block [ldf .x9 j]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .x .x9) t = some (decide (n = 0)) := by
  have a := h.access
  have hw := h.header hv
  simp only [Bignum.word, off] at hw
  rcases hj with rfl | rfl <;> simp only [Nat.reduceMul] at hw <;>
  · refine WP.mono (WP.keep [.x9] (Q := fun t =>
      isa.eval (.zero .x .x9) t = some (decide (n = 0)) ∧ t.mem = s.mem) ?_ (by decide) (by decide)
      (by decide +kernel)) fun _ ⟨⟨he, hm⟩, k⟩ => ⟨h.keep k hm, he⟩
    brun [ldf, h.x19, hw, a.ld 0 (by decide), a.ld 8 (by decide), a.ld0]
    simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq,
      ofNat_beq_zero (show n < 2 ^ 64 by omega)]

theorem keys_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [ldf .x9 0]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .x .x9) t = some (decide (keys = 0)) :=
  budget_guard h (j := 0) (.inl rfl) (by simp [KeyPublic.headers]) h.keys_le

theorem scalars_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [ldf .x9 1]) s fun t =>
      KeyLive p original used keys scalars t ∧ isa.eval (.zero .x .x9) t = some (decide (scalars = 0)) :=
  budget_guard h (j := 1) (.inr rfl) (by simp [KeyPublic.headers]) h.scalars_le

/-- Whether the tape holds less than an attempt. -/
theorem room_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block room) s fun t =>
      KeyLive p original used keys scalars t ∧
        isa.eval (.zero .x .x12) t = some (decide (p.randLen - used < p.len)) := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv10 := h.header (j := 10) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv10
  have hr : p.randLen < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
  have hk : p.len < 2 ^ 64 := by have := h.input.len_lt; omega
  refine WP.mono (WP.keep [.x9, .x10, .x11, .x12, .x13, .x14] (Q := fun t =>
    isa.eval (.zero .x .x12) t = some (decide (p.randLen - used < p.len)) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun _ ⟨⟨he, hm⟩, k⟩ => ⟨h.keep k hm, he⟩
  unfold room
  brun [ldf, h.x19, hv2, hv10, a.ld 16 (by decide), a.ld 80 (by decide), imm64 (show 0 < 65536 by decide),
    imm64 (show 1 < 65536 by decide), subs_ge (show p.randLen - used < 2 ^ 64 by omega) hk]
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  by_cases hb : p.len ≤ p.randLen - used
  · simp only [hb, decide_true, ite_true, show ¬p.randLen - used < p.len by omega, decide_false]
    decide
  · simp only [hb, decide_false, ite_false, show p.randLen - used < p.len by omega, decide_true,
      Bool.false_eq_true]
    decide

/-- The status word, minus 4. -/
theorem status_guard {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .x19 = B) {st : Nat}
    (hs : word s.mem B 112 = BitVec.ofNat 64 st) (hst : st < 5) :
    WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) s fun t =>
      (isa.eval (.zero .x .x9) t = some (decide (st = 4)) ∧ t.mem = s.mem) ∧ Keep [.x9] s t := by
  simp only [Bignum.word, off] at hs
  refine WP.keep [.x9] ?_ (by decide) (by decide) (by decide +kernel)
  brun [ldf, hb, hs, a.ld 112 (by decide)]
  have : ∀ st < 5, ((BitVec.ofNat 64 st - BitVec.ofNat 64 4) == 0) = decide (st = 4) := by decide
  have hb' := this st hst
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq,
    Option.some.injEq] at hb' ⊢
  exact hb'

theorem done_loop_guard {p : KeyPublic} {original s : State} {r : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original r s) :
    WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) s fun t =>
      isa.eval (.zero .x .x9) t = some false ∧ KeyDone p original r t := by
  have scr := h.input.control_scr (t := s) h.wr
  have a : CtlAccess s p.control := ⟨fun _ hd => scr.ld hd, fun _ hd => scr.st hd,
    by simpa only [off, BitVec.add_zero] using scr.ld (d := 0) (by decide),
    by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)⟩
  have hb : r.status < 5 := by unfold Spec.Ffdh.KeySearchResult.status; split <;> decide
  refine WP.mono (status_guard a h.x19 h.status hb) fun t ⟨⟨he, hm⟩, k⟩ => ⟨?_, h.keep k hm⟩
  rw [he]
  congr 1
  unfold Spec.Ffdh.KeySearchResult.status
  split <;> rfl

theorem live_loop_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hs : word s.mem p.control 112 = 4) :
    WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) s fun t =>
      isa.eval (.zero .x .x9) t = some true ∧ KeyLive p original used keys scalars t :=
  WP.mono (status_guard (st := 4) h.access h.x19 hs (by decide))
    fun _ ⟨⟨he, hm⟩, k⟩ => ⟨he, h.keep k hm⟩

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
