module
public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math

/-! # Ordinary modular products through the selected Montgomery backend -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- The facts preserved by every arithmetic Montgomery call. -/
structure ModCtx (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (m : Nat) : Prop where
  good : Good s B Z w minv
  modulus : wv s.mem B (slot w aN) w = m
  inverse : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0

/-- Every tuple covered by the backend's constant-time interface also
preserves the modulus and its low-word inverse. -/
theorem mont_step (M : Mont) {s : State} {B : Addr} {Z w m : Nat} {minv : BitVec 64}
    (hc : ModCtx s B Z w minv m) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (huse : MmUse o a b) (hb : wv s.mem B (slot w b) w < m) :
    WP isa (M.mm o a b) s fun t =>
      ModCtx t B Z w minv m ∧ wv t.mem B (slot w o) w < m ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % m =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % m ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have valid : o < 8 ∧ a < 8 ∧ b < 8 ∧ o ≠ aN ∧ o ≠ aAcc ∧ o ≠ aTmp ∧
      a ≠ aAcc ∧ a ≠ aTmp ∧ b ≠ aAcc ∧ b ≠ aTmp := by
    simp only [MmUse, aR2, aY, aXm, aX, aOne, aN, aAcc, aTmp] at *
    omega
  obtain ⟨ho, ha, hb', hon, hoacc, hotmp, haacc, hatmp, hbacc, hbtmp⟩ := valid
  refine WP.mono (M.ok hc.good hZ hw hw' ho ha hb' hoacc hotmp haacc hatmp hbacc hbtmp hc.inverse
    (by rw [hc.modulus]; exact hb)) fun t ⟨hg, hlt, hval, hf, hk⟩ => ?_
  have hnZ : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hc.good.scr.nowrap; omega
  have hnmem := hf.wv_of_not_mem (show aN < 8 by decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; unfold aN aAcc aTmp at *; omega) hnZ
  have hnword := hf.word0_of_not_mem (show aN < 8 by decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; unfold aN aAcc aTmp at *; omega) hnZ (by omega)
  rw [hc.modulus] at hlt hval
  refine ⟨⟨hg, hnmem.trans hc.modulus, ?_⟩, hlt, hval, hf, hk⟩
  rw [hnword]
  exact hc.inverse

/-- The ordinary product core, including operands that are not reduced.
Only the modulus must be odd; no Fermat-inverse assumption is used. -/
theorem productCore_ok (M : Mont) {s : State} {B : Addr} {Z w m a b : Nat} {minv : BitVec 64}
    (hc : ModCtx s B Z w minv m) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (ha : wv s.mem B (slot w aX) w = a) (hb : wv s.mem B (slot w aXm) w = b)
    (hR2 : wv s.mem B (slot w aR2) w = (2 ^ (64 * w) * 2 ^ (64 * w)) % m)
    (hone : wv s.mem B (slot w aOne) w = 1) :
    WP isa (Arithmetic.productCore M.mm) s fun t =>
      ModCtx t B Z w minv m ∧ wv t.mem B (slot w aY) w = a * b % m ∧
      Arrays B w [aAcc, aTmp, aX, aXm, aY] s.mem t.mem ∧ Keep mmRegs s t := by
  have hnZ : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hc.good.scr.nowrap; omega
  have hR := coprime_pow2 hodd (64 * w)
  have hm0 : 0 < m := by omega
  unfold Arithmetic.productCore seqs
  refine WP.seq (WP.mono (mont_step M hc hZ hw hw' (by unfold MmUse; decide)
    (by rw [hR2]; exact Nat.mod_lt _ hm0)) fun s1 ⟨hc1, hl1, hv1, hf1, hk1⟩ => ?_)
  rw [ha, hR2] at hv1
  have v1 := VG.Proof.Dsa.mont_scale hR hv1
  rw [Nat.mod_eq_of_lt hl1] at v1
  have r21 : wv s1.mem B (slot w aR2) w = (2 ^ (64 * w) * 2 ^ (64 * w)) % m :=
    (hf1.wv_of_not_mem (by decide) (by decide) hnZ).trans hR2
  have b1 : wv s1.mem B (slot w aXm) w = b :=
    (hf1.wv_of_not_mem (by decide) (by decide) hnZ).trans hb
  have one1 : wv s1.mem B (slot w aOne) w = 1 :=
    (hf1.wv_of_not_mem (by decide) (by decide) hnZ).trans hone
  refine WP.seq (WP.mono (mont_step M hc1 hZ hw hw' (by unfold MmUse; decide)
    (by rw [r21]; exact Nat.mod_lt _ hm0)) fun s2 ⟨hc2, hl2, hv2, hf2, hk2⟩ => ?_)
  rw [b1, r21] at hv2
  have v2 := VG.Proof.Dsa.mont_scale hR hv2
  rw [Nat.mod_eq_of_lt hl2] at v2
  have a2 : wv s2.mem B (slot w aX) w = a * 2 ^ (64 * w) % m :=
    (hf2.wv_of_not_mem (by decide) (by decide) hnZ).trans v1
  have one2 : wv s2.mem B (slot w aOne) w = 1 :=
    (hf2.wv_of_not_mem (by decide) (by decide) hnZ).trans one1
  refine WP.seq (WP.mono (mont_step M hc2 hZ hw hw' (by unfold MmUse; decide)
    (by rw [a2]; exact Nat.mod_lt _ hm0)) fun s3 ⟨hc3, hl3, hv3, hf3, hk3⟩ => ?_)
  have a2mod : wv s2.mem B (slot w aX) w % m = a * 2 ^ (64 * w) % m := by rw [a2, Nat.mod_mod]
  have b2mod : wv s2.mem B (slot w aXm) w % m = b * 2 ^ (64 * w) % m := by rw [v2, Nat.mod_mod]
  have v3 := VG.Proof.Dsa.mont_product hR b2mod a2mod hv3
  have one3 : wv s3.mem B (slot w aOne) w = 1 :=
    (hf3.wv_of_not_mem (by decide) (by decide) hnZ).trans one2
  refine WP.mono (mont_step M hc3 hZ hw hw' (by unfold MmUse; decide)
    (by rw [one3]; exact hm)) fun t ⟨hct, hlt, hvt, hft, hkt⟩ => ?_
  rw [one3] at hvt
  have vt := VG.Proof.Dsa.mont_decode hR v3 hvt
  rw [Nat.mod_eq_of_lt hlt, Nat.mul_comm b a] at vt
  refine ⟨hct, vt, ?_, (((hk1.trans hk2).trans hk3).trans hkt).mono (by decide)⟩
  have f1 : Arrays B w [aAcc, aTmp, aX, aXm, aY] s.mem s1.mem := hf1.mono (by decide)
  have f2 : Arrays B w [aAcc, aTmp, aX, aXm, aY] s1.mem s2.mem := hf2.mono (by decide)
  have f3 : Arrays B w [aAcc, aTmp, aX, aXm, aY] s2.mem s3.mem := hf3.mono (by decide)
  have ft : Arrays B w [aAcc, aTmp, aX, aXm, aY] s3.mem t.mem := hft.mono (by decide)
  exact ((f1.trans f2).trans f3).trans ft

end VG.Proof.Dsa.AArch64
