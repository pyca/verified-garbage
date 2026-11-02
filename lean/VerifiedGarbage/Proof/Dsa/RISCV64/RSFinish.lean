module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RSCtx
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Randomized DSA signing on RISC-V: after a call of `vg_dsa_sign`

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/Finish.lean`). `callFinish_ok`:
the result, a `u32`, zero-extended, is tested; a signature leaves the
status 1; a zero result spends an attempt, and leaves the status 4 while
one is left, else 0.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.RandomSign

/-- The zero extension of a register's low word. -/
theorem zx_toNat (x : BitVec 64) : ((x <<< 32) >>> 32).toNat = (x.setWidth 32).toNat := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, show 2 ^ 64 = 2 ^ 32 * 2 ^ 32 by rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (by decide)]

theorem zx_beq_zero {x : BitVec 64} {st : Nat} (h : (x.setWidth 32).toNat = st) :
    ((x <<< 32) >>> 32 == 0) = decide (st = 0) := by
  rw [← zx_toNat] at h
  by_cases hs : st = 0
  · subst hs
    simp only [decide_true, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq h
  · simp only [hs, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    rw [e] at h
    exact hs h.symm

/-- What `callFinish` leaves, after a call whose result's low word is `st`. -/
theorem callFinish_ok {s : State} {a st : Nat} (h6 : s.gpr .s6 = BitVec.ofNat 64 a) (ha : 1 ≤ a) (ha' : a ≤ 8)
    (h0 : ((s.gpr .a0).setWidth 32).toNat = st) :
    WP isa callFinish s fun t =>
      t.mem = s.mem ∧ Keep [.a0, .s6, .s10] s t ∧
        (st ≠ 0 → t.gpr .s10 = BitVec.ofNat 64 1 ∧ t.gpr .s6 = s.gpr .s6) ∧
        (st = 0 → t.gpr .s6 = BitVec.ofNat 64 (a - 1) ∧
          t.gpr .s10 = BitVec.ofNat 64 (if a - 1 = 0 then 0 else 4)) := by
  unfold callFinish
  refine WP.seq (WP.mono (WP.keep [.a0] (Q := fun t => t.mem = s.mem ∧ t.gpr .s6 = s.gpr .s6 ∧
    t.gpr .a0 = (s.gpr .a0 <<< 32) >>> 32) (by brun) (by decide) (by rfl)) fun t₀ ⟨⟨m0, b6, b0⟩, k0⟩ => ?_)
  refine WP.ite (decide (st = 0)) (by rw [Steps.eval_zero, b0, zx_beq_zero h0]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    refine WP.seq (WP.mono (WP.keep [.s6] (Q := fun t => t.mem = t₀.mem ∧ t.gpr .s6 = BitVec.ofNat 64 (a - 1))
      (by brun [b6, h6, VG.Offset.ofNat_sub_ofNat ha]) (by decide) (by rfl)) fun t₁ ⟨⟨m1, a6⟩, k1⟩ => ?_)
    refine WP.ite (decide (a - 1 ≠ 0)) (Steps.eval_nonzero_ofNat _ _ (by omega) a6) (fun hn => ?_) (fun hn => ?_)
    · simp only [decide_eq_true_eq] at hn
      refine WP.mono (WP.keep [.s10] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .s10 = BitVec.ofNat 64 4)
        (by brun [exec_li_lit (show 4 < 2048 by decide)]) (by decide) (by rfl))
        fun t ⟨⟨tm, t10⟩, k2⟩ => ⟨tm.trans (m1.trans m0), ((k0.trans k1).trans k2).mono (by decide),
          fun h => absurd hz h, fun _ => ⟨(k2.1 .s6 (by decide)).trans a6, by rw [t10, ite_eq_right hn]⟩⟩
    · simp only [decide_eq_false_iff_not, Decidable.not_not] at hn
      refine WP.mono (WP.keep [.s10] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .s10 = BitVec.ofNat 64 0)
        (by brun [exec_li_zero]; rfl) (by decide) (by rfl))
        fun t ⟨⟨tm, t10⟩, k2⟩ => ⟨tm.trans (m1.trans m0), ((k0.trans k1).trans k2).mono (by decide),
          fun h => absurd hz h, fun _ => ⟨(k2.1 .s6 (by decide)).trans a6, by rw [t10, ite_eq_left hn]⟩⟩
  · simp only [decide_eq_false_iff_not] at hz
    refine WP.mono (WP.keep [.s10] (Q := fun t => t.mem = t₀.mem ∧ t.gpr .s10 = BitVec.ofNat 64 1)
      (by brun [exec_li_lit (show 1 < 2048 by decide)]) (by decide) (by rfl))
      fun t ⟨⟨tm, t10⟩, k⟩ => ⟨tm.trans m0, (k0.trans k).mono (by decide),
        fun _ => ⟨t10, (k.1 .s6 (by decide)).trans b6⟩, fun h => absurd h hz⟩

end VG.Proof.Dsa.RISCV64.RS
