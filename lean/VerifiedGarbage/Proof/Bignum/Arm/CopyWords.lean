module
public import VerifiedGarbage.Impl.Bignum.Arm.CopyWords
public import VerifiedGarbage.Proof.Bignum.Arm.SelectState

import VerifiedGarbage.Proof.Bignum.Arm.CopyWordBody
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
import VerifiedGarbage.Proof.Framework.Block

/-! # Termination and exact value of runtime-length word copying -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem copyWords_ok (s : State) {base : BitVec 32} {size o a n : Nat}
    (ctx : SubCtx s base size o a a n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp10 : s.gpr .r10 = base + BitVec.ofNat 32 a)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 a)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa copyWords s (SelectInv s base o a a n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ SelectInv s base o a a n i t
  rw [copyWords, WP.seq_iff]
  refine WP.mono (selectMask_ok s) ?_
  rintro u ⟨mask, keep⟩
  refine WP.loop (M := isa) inv ?_ n u ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (copyWordBody_ok ctx hi (by omega)) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_⟩
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (show Rest [.r4] s u from ⟨keep.regs, keep.rd, keep.wr, keep.sp⟩).mono (by simp [selectLoopClobbers])⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using (keep.regs .r0 (by simp)).trans hp0
    · simpa only [Nat.mul_zero, Nat.add_zero] using (keep.regs .r10 (by simp)).trans hp10
    · simpa only [Nat.mul_zero, Nat.add_zero] using (keep.regs .r12 (by simp)).trans hp12
    · simpa only [Nat.sub_zero] using (keep.regs .lr (by simp)).trans hcount
    · rw [keep.mem]; exact Outside.refl _ _ _ _
    · rw [keep.mem]; simp only [val32, ite_self]
    · rw [keep.regs .r11 (by simp)]; exact mask

end VG.Proof.Bignum.Arm
