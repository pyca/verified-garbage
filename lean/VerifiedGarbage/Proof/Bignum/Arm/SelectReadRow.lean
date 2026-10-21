module

public import VerifiedGarbage.Proof.Bignum.Arm.SelectReadState
public import VerifiedGarbage.Impl.Bignum.Arm.Select
import VerifiedGarbage.Proof.Bignum.Arm.SelectReadBody
import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Block

/-! A masked row reuses the RSA selector with an external read-only source. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem selectReadRow_ok (s : State) {dst src : BitVec 32} {n : Nat}
    (ctx : SelectReadCtx s dst src n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = dst) (hp10 : s.gpr .r10 = dst) (hp12 : s.gpr .r12 = src)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) (hc : (s.gpr .r11).toNat ≤ 1) :
    WP isa selectRow s (SelectReadInv s dst src n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ SelectReadInv s dst src n i t
  rw [selectRow, WP.seq_iff]
  refine WP.mono (selectMask_ok s) ?_
  rintro u ⟨mask, keep⟩
  refine WP.loop (M := isa) inv ?_ n u ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (selectReadBody_ok ctx hi (by omega) hc) ?_
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
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (show Rest [.r4] s u from ⟨keep.regs, keep.rd, keep.wr, keep.sp⟩).mono (by simp [selectLoopClobbers])⟩
    · simpa using
        (keep.regs .r0 (by simp)).trans hp0
    · simpa using
        (keep.regs .r10 (by simp)).trans hp10
    · simpa using
        (keep.regs .r12 (by simp)).trans hp12
    · simpa only [Nat.sub_zero] using (keep.regs .lr (by simp)).trans hcount
    · rw [keep.mem]; exact Outside.refl _ _ _ _
    · rw [keep.mem]; exact Frame.refl _ _
    · simp only [val32, ite_self]
    · rw [keep.regs .r11 (by simp)]; exact mask

end VG.Proof.Bignum.Arm
