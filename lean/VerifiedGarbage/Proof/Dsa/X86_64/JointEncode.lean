module
public import VerifiedGarbage.Proof.Dsa.X86_64.JointAdvance

import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # Encoding the two bases of joint DSA exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem jointEncode_ok (M : Mont) {s : State} {P : Addr} {w n g y : Nat} {minv : BitVec 64}
    (hc : JointCtx s P w n minv) (hw : 2 ≤ w) (hw' : w < 2 ^ 30)
    (hn : 1 < n) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hg : wv s.mem P (slot w aX) w = g) (hy : wv s.mem P (slot w aXm) w = y)
    (hone : wv s.mem P (slot w aOne) w = 1)
    (hr2 : wv s.mem P (slot w aR2) w = (2 ^ (64 * w) * 2 ^ (64 * w)) % n) :
    WP isa (Joint.encode M.mm) s fun u => JointCtx u P w n minv ∧
      JointBuildValues u.mem P w n g y 0 ∧
      Arrays P w [aAcc, aTmp, aX, aR2, aXm, aY, aOne] s.mem u.mem ∧ Keep mmRegs s u := by
  have hnow := hc.mod.good.scr.nowrap
  unfold Joint.encode seqs
  refine WP.seq (WP.mono (jointProduct_ok M hc hw hw' (by unfold MmUse; decide)
    (by rw [hone]; exact hn)) fun s1 ⟨hc1, hl1, hv1, hf1, hk1⟩ => ?_)
  rw [hone] at hv1
  have val1 : wv s1.mem P (slot w aY) w = 2 ^ (64 * w) % n := by
    have h2 : wv s.mem P (slot w aR2) w % n = 2 ^ (64 * w) * 2 ^ (64 * w) % n := by rw [hr2, Nat.mod_mod]
    have hv := VG.Proof.Dsa.mont_decode hR h2 hv1
    rwa [Nat.mod_eq_of_lt hl1] at hv
  have r21 := (hf1.wv_of_not_mem (by decide) (by decide) hnow).trans hr2
  have x1 := (hf1.wv_of_not_mem (by decide) (by decide) hnow).trans hg
  have y1 := (hf1.wv_of_not_mem (by decide) (by decide) hnow).trans hy
  refine WP.seq (WP.mono (jointProduct_ok M hc1 hw hw' (by unfold MmUse; decide)
    (by rw [r21]; exact Nat.mod_lt _ (by omega))) fun s2 ⟨hc2, hl2, hv2, hf2, hk2⟩ => ?_)
  rw [x1, r21] at hv2
  have val2 := VG.Proof.Dsa.mont_scale hR hv2
  rw [Nat.mod_eq_of_lt hl2] at val2
  have r22 := (hf2.wv_of_not_mem (by decide) (by decide) hnow).trans r21
  have y2 := (hf2.wv_of_not_mem (by decide) (by decide) hnow).trans y1
  have acc2 := (hf2.wv_of_not_mem (by decide) (by decide) hnow).trans val1
  refine WP.seq (WP.mono (jointProduct_ok M hc2 hw hw' (by unfold MmUse; decide)
    (by rw [r22]; exact Nat.mod_lt _ (by omega))) fun s3 ⟨hc3, hl3, hv3, hf3, hk3⟩ => ?_)
  rw [y2, r22] at hv3
  have val3 := VG.Proof.Dsa.mont_scale hR hv3
  rw [Nat.mod_eq_of_lt hl3] at val3
  have x3 := (hf3.wv_of_not_mem (by decide) (by decide) hnow).trans val2
  have acc3 := (hf3.wv_of_not_mem (by decide) (by decide) hnow).trans acc2
  refine WP.seq (WP.mono (jointCopy_ok hc3 hw hw' (by decide) (by decide) (by decide) (by decide))
    fun s4 ⟨hc4, hv4, hf4, hk4⟩ => ?_)
  have gen4 := hv4.trans x3
  have base4 := (hf4.wv_of_not_mem (by decide) (by decide) hnow).trans val3
  have acc4 := (hf4.wv_of_not_mem (by decide) (by decide) hnow).trans acc3
  refine WP.seq (WP.mono (jointCopy_ok hc4 hw hw' (by decide) (by decide) (by decide) (by decide))
    fun s5 ⟨hc5, hv5, hf5, hk5⟩ => ?_)
  have one5 := hv5.trans acc4
  have gen5 := (hf5.wv_of_not_mem (by decide) (by decide) hnow).trans gen4
  have base5 := (hf5.wv_of_not_mem (by decide) (by decide) hnow).trans base4
  have acc5 := (hf5.wv_of_not_mem (by decide) (by decide) hnow).trans acc4
  refine WP.mono (jointCopy_ok hc5 hw hw' (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hu, hv6, hf6, hk6⟩ => ?_
  have gen6 := (hf6.wv_of_not_mem (by decide) (by decide) hnow).trans gen5
  have base6 := (hf6.wv_of_not_mem (by decide) (by decide) hnow).trans base5
  have one6 := (hf6.wv_of_not_mem (by decide) (by decide) hnow).trans one5
  have acc6 := (hf6.wv_of_not_mem (by decide) (by decide) hnow).trans acc5
  have row6 := hv6.trans acc5
  refine ⟨hu, ⟨gen6, base6, one6, ?_, ?_⟩, ?_,
    (((((hk1.trans hk2).trans hk3).trans hk4).trans hk5).trans hk6).mono (by decide)⟩
  · simpa only [Nat.zero_div, Nat.pow_zero, Nat.one_mul] using row6
  · simpa only [Nat.zero_div, Nat.zero_mod, Nat.pow_zero, Nat.one_mul] using acc6
  exact (((((hf1.mono (by decide)).trans (hf2.mono (by decide))).trans
    (hf3.mono (by decide))).trans (hf4.mono (by decide))).trans (hf5.mono (by decide))).trans (hf6.mono (by decide))

end VG.Proof.Dsa.X86_64
