module

public import VerifiedGarbage.Proof.Bignum.Arm.Fios2.State
public import VerifiedGarbage.Impl.Bignum.Arm.Fios2
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.StepInv
import VerifiedGarbage.Proof.Bignum.Arm.FiosAdvance
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.FiosState

/-! The two-row scan's loop: two words an iteration over the middle `n - 2`. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem body_ok {s0 s : State} {a0 q0 a1 q1 base : BitVec 32} {size acc b mod n j : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n) (inv : Inv s0 a0 q0 a1 q1 base acc b mod n j j s)
    (hj : j + 4 ≤ n) :
    WP isa VG.Impl.Bignum.Arm.Fios2.body s fun t =>
      Inv s0 a0 q0 a1 q1 base acc b mod n (j + 2) (j + 2) t ∧ t.z = decide (j + 2 + 2 = n) := by
  have small : n < 2 ^ 32 := by have := ctx.workspace.nowrap; have := ctx.accFits; omega
  rw [VG.Impl.Bignum.Arm.Fios2.body, WP.seq_iff]
  have first := step_inv ctx inv (by omega) (by omega)
  rw [show 4 * (j - j) = 0 by omega] at first
  refine WP.mono first fun u iu => ?_
  rw [WP.seq_iff]
  have second := step_inv ctx iu (by omega) (by omega)
  rw [show 4 * (j + 1 - j) = 4 by omega] at second
  refine WP.mono second fun v iv => ?_
  refine WP.mono (Fios.advance_ok v 2 (Or.inr rfl)) ?_
  rintro t ⟨p0, p12, p4, count, zero, mem, rt⟩
  have keep (r : Reg) (h : r ∉ [.r0, .r12, .r4, .lr]) : t.gpr r = v.gpr r := rt.gpr r h
  refine ⟨⟨by omega, by omega, ?_, ?_, ?_, ?_, (keep .r1 (by decide)).trans iv.scalar0,
    (keep .r2 (by decide)).trans iv.quotient0, (keep .r9 (by decide)).trans iv.scalar1,
    (keep .r10 (by decide)).trans iv.quotient1, by rw [mem]; exact iv.outside, ?_,
    iv.rest.trans (rt.mono (by decide))⟩, ?_⟩
  · rw [p0, iv.outPtr, Offset.add_add]; congr 2
  · rw [p12, iv.bPtr, Offset.add_add]; congr 2
  · rw [p4, iv.mPtr, Offset.add_add]; congr 2
  · rw [count, iv.count, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]; congr 1
  · simp only [carries, mem, keep .r7 (by decide), keep .r8 (by decide), keep .r5 (by decide),
      keep .r11 (by decide)]
    exact iv.value
  · rw [zero, iv.count, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - 2 - j - 2 = 0 ↔ j + 2 + 2 = n by omega]

theorem loop_ok {s0 s : State} {a0 q0 a1 q1 base : BitVec 32} {size acc b mod n : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n) (inv : Inv s0 a0 q0 a1 q1 base acc b mod n 0 0 s)
    (positive : 4 ≤ n) (even : n % 2 = 0) :
    WP isa VG.Impl.Bignum.Arm.Fios2.loop s (Inv s0 a0 q0 a1 q1 base acc b mod n (n - 2) (n - 2)) := by
  let I := fun k t => ∃ j, j + 2 + 2 * k = n ∧ 0 < k ∧ Inv s0 a0 q0 a1 q1 base acc b mod n j j t
  unfold VG.Impl.Bignum.Arm.Fios2.loop
  refine WP.loop (M := isa) I ?_ ((n - 2) / 2) s ?_
  · intro k t h
    obtain ⟨j, hjk, hk, hj⟩ := h
    refine WP.mono (body_ok ctx hj (by omega)) ?_
    rintro u ⟨hu, hz⟩
    by_cases last : j + 2 + 2 = n
    · left
      refine ⟨?_, ?_⟩
      · change some (!u.z) = some false
        simp only [hz, last, decide_true, Bool.not_true]
      · have index : j + 2 = n - 2 := by omega
        simpa only [index] using hu
    · right
      refine ⟨?_, k - 1, by omega, j + 2, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, last, decide_false, Bool.not_false]
  · exact ⟨0, by omega, by omega, inv⟩

end VG.Proof.Bignum.Arm.Fios2
