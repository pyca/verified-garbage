module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateWidth
public import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Omega

/-! The leading byte's high bit matches the specification's candidate-width guard. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 VG.Impl.Bignum.AArch64

theorem candidateWidth_ok {s : State} {B pp : Addr} {Z w len p : Nat}
    (h : Ws s B Z w) (hptr : word s.mem B 160 = pp)
    (hlen : 0 < len) (hbound : p < 256 ^ len)
    (hbytes : Spec.Rsa.bytesAt s.mem pp len = Spec.Dsa.encodeBE len p)
    (hrd : InRegions (s.rd ++ s.wr) pp 1) :
    WP isa (.block Impl.Dsa.AArch64.Generation.candidateWidth) s fun t =>
      eval (.zero .x .x3) t = some (decide (p < 2 ^ (8 * len - 1))) ∧
      t.mem = s.mem ∧ Keep [.x1, .x3] s t := by
  have hfirst : s.mem pp = (Spec.Dsa.encodeBE len p).getD 0 0 := by
    rw [← hbytes]
    simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hlen]
  have he := VG.Proof.Dsa.Generation.candidate_firstByte hlen hbound
  rw [← hfirst] at he
  refine WP.mono (WP.keep [.x1, .x3] (Q := fun t =>
    eval (.zero .x .x3) t = some (decide (p < 2 ^ (8 * len - 1))) ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨⟨hc, hm⟩, hk⟩ => ⟨hc, hm, hk⟩
  unfold Impl.Dsa.AArch64.Generation.candidateWidth
  brun [h.x0, hdr_enc (by decide : 20 < 32),
    h.scr.ld (d := 160) (by have := h.h256; omega), hptr, hrd, eval, read_one,
    BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
    BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)]
  have hb := (s.mem pp).isLt
  have hshift : ((s.mem pp).setWidth 32 |>.setWidth 64) >>> 7 =
      (if (s.mem pp).toNat < 128 then (0#64) else (1#64)) := by
    by_cases ht : (s.mem pp).toNat < 128
    · rw [ite_eq_left ht]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
      change ((s.mem pp).toNat % 2 ^ 32 % 2 ^ 64) / 128 = 0
      omega
    · rw [ite_eq_right ht]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
      change ((s.mem pp).toNat % 2 ^ 32 % 2 ^ 64) / 128 = 1
      omega
  change ((BitVec.setWidth 64 (BitVec.setWidth 32 (s.mem pp)) >>> 7) == (0#64)) =
    decide (p < 2 ^ (8 * len - 1))
  rw [hshift]
  by_cases ht : (s.mem pp).toNat < 128
  · simp only [ite_eq_left ht, decide_eq_true (he.mp ht)]
    rfl
  · simp only [ite_eq_right ht,
      decide_eq_false (show ¬ p < 2 ^ (8 * len - 1) from fun hp => ht (he.mpr hp))]
    rfl

end VG.Proof.Dsa.AArch64.Generation
