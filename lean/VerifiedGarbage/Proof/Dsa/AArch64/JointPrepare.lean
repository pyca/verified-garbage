module

public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
public import VerifiedGarbage.Proof.Dsa.AArch64.JointWindow
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Dsa.AArch64.JointBuildContext

import VerifiedGarbage.Proof.Dsa.AArch64.JointEncode
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Dsa.AArch64.JointAdvance
import VerifiedGarbage.Proof.Dsa.AArch64.JointEntries
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
/-! # Loading and preparing both bases for joint DSA exponentiation -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/JointBuild.lean`, which only this module imported.
section

/-! # Preparing the joint table and Montgomery accumulator -/

section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem JointTab.of_arrays {m m' : Mem} {P : Addr} {w n g y : Nat} {xs : List Nat}
    (h : JointTab m P w n g y) (hf : Arrays P w xs m m') (hxs : ∀ k ∈ xs, k < 8)
    (hn : P.toNat + (slot w 8 + tabBytes w) ≤ 2 ^ 64) : JointTab m' P w n g y :=
  ⟨(hf.hslot (by decide)).trans h.tab,
    fun k hk => (joint_arrays_entry hf hxs hn hk).symm ▸ h.lt k hk,
    fun k hk => (joint_arrays_entry hf hxs hn hk).symm ▸ h.val k hk⟩

theorem jointBuild_ok (M : Mont) {t : State} {P : Addr} {w n g y : Nat} {minv : BitVec 64}
    (hc : JointCtx t P w n minv) (hw : 2 ≤ w) (hw' : w < 2 ^ 30)
    (hn : 0 < n) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (h : JointBuildValues t.mem P w n g y 0) :
    WP isa (Joint.build M.mm) t fun u => JointCtx u P w n minv ∧
      JointTab u.mem P w n g y ∧ wv u.mem P (slot w aY) w = 2 ^ (64 * w) % n ∧
      wv u.mem P (slot w aOne) w = 1 ∧
      Frm P (workRanges w) t.mem u.mem ∧ Keep mmRegs t u := by
  have hnow := hc.scrT.nowrap
  have hsmall : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  unfold Joint.build Joint.tableInit seqs
  refine WP.seq (WP.mono (tabInit_ok hc.exp hw') fun v ⟨hm, hk⟩ => ?_)
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sTab) (off P (slot w 8)) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sTab)) (off P (slot w 8))) P
    (d := 8 * Crt.sEnt) (off P (slot w 8)) (by decide)
  rw [← hm] at o2
  have hf : Frm P (crtExpRanges w) t.mem v.mem :=
    (Frm.of_outside o1 (by simp [crtExpRanges])).trans
      (Frm.of_outside o2 (by simp [crtExpRanges, crtWinRanges]))
  have cv := hc.exp.of_frm hf hk.wr (hk.gpr .x0 (by decide))
  have vals : JointBuildValues v.mem P w n g y 0 := h.congr fun a ha => by
    have hab := slot_le (w := w) ha
    rw [o2.wv (Or.inr (hdr_lt_slot w a (by decide))) (by omega),
      o1.wv (Or.inr (hdr_lt_slot w a (by decide))) (by omega)]
  have h0 : JointBuildInv v P w n g y minv 0 v := by
    refine ⟨⟨⟨cv.good, cv.n, cv.inv⟩, cv.scrT⟩, vals, ?_, ?_, fun k hk => by omega,
      Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm, word_writeW_self]
  refine WP.seq (WP.mono (jointBuildSteps_ok M hw hw' hn hR (by decide) h0) fun s hs => ?_)
  have st : JointTab s.mem P w n g y := ⟨hs.tab,
    fun k hk => by rw [hs.entries k hk]; exact Nat.mod_lt _ hn,
    fun k hk => by rw [hs.entries k hk, Nat.mod_mod]⟩
  refine WP.seq (WP.mono (jointCopy_ok hs.ctx hw hw' (by decide) (by decide) (by decide) (by decide))
    fun s' ⟨hc', hv, hf', hk'⟩ => ?_)
  have sy : wv s'.mem P (slot w aY) w = 2 ^ (64 * w) % n := hv.trans hs.vals.one
  have st' := st.of_arrays hf' (by decide) hs.ctx.scrT.nowrap
  refine WP.mono (one_ok hc'.mod.good (Nat.le_refl _) hw (by omega) (by decide))
    fun u ⟨hu, hone, hfu, hku⟩ => ?_
  have uc : JointCtx u P w n minv := ⟨⟨hu,
    (hfu.wv_of_not_mem (by decide) (by decide) hc'.mod.good.scr.nowrap).trans hc'.mod.modulus,
    by rw [hfu.word0_of_not_mem (by decide) (by decide) hc'.mod.good.scr.nowrap (by omega)]; exact hc'.mod.inverse⟩,
    hc'.scrT.congr hku.wr⟩
  refine ⟨uc, st'.of_arrays hfu (by decide) hc'.scrT.nowrap,
    (hfu.wv_of_not_mem (by decide) (by decide) hc'.mod.good.scr.nowrap).trans sy, hone,
    ((exp_work hf).trans hs.frm).trans ((arrays_work hf' (by decide)).trans (arrays_work hfu (by decide))),
    (((hk.trans hs.keep).trans hk').trans hku).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem jointPrepare_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {gp yp : Addr} {gb yb : List Byte}
    (hg : word s.mem B (8 * arg) = gp)
    (hgl : word s.mem B (8 * argLen) = BitVec.ofNat 64 gb.length)
    (hgs : Src s B Z gp gb) (hg1 : 1 ≤ gb.length) (hgw : (gb.length + 7) / 8 ≤ wx)
    (hy : word s.mem B (8 * arg2) = yp)
    (hyl : word s.mem B (8 * arg2Len) = BitVec.ofNat 64 yb.length)
    (hys : Src s B Z yp yb) (hy1 : 1 ≤ yb.length) (hyw : (yb.length + 7) / 8 ≤ wx) :
    WP isa (Joint.prepare M.mm) s fun t =>
      SubCtx t B Z o w wx minv ∧ JointCtx t (off B o) wx m minv ∧
      JointTab t.mem (off B o) wx m (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE yb) ∧
      wv t.mem (off B o) (slot wx aY) wx = 2 ^ (64 * wx) % m ∧
      wv t.mem (off B o) (slot wx aOne) wx = 1 ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Joint.prepare seqs
  refine WP.seq (WP.mono (prepare_ok M hc hw2 hw48 hm hodd hn hinv)
    fun s1 ⟨hc1, hm1, ho1, hr1, hf1, hk1⟩ => ?_)
  refine WP.seq (WP.mono (load_mod_ok hc1 hm1 hw2 hwx hw30 (by decide) (by decide)
    (by decide) (by decide) ((work_parent hc hf1 (by decide)).trans hg)
    ((work_parent hc hf1 (by decide)).trans hgl) (work_source hc hf1 hk1 hgs)
    hg1 (by omega) hgw) fun s2 ⟨hc2, hm2, hg2, ha2, hf2, hk2⟩ => ?_)
  have hf12 := hf1.trans hf2
  have hk12 := (hk1.trans hk2).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  have ho2 := (ha2 aOne (by decide) (by decide)).trans ho1
  have hr2 := (ha2 aR2 (by decide) (by decide)).trans hr1
  refine WP.seq (WP.mono (load_mod_ok hc2 hm2 hw2 hwx hw30 (by decide) (by decide)
    (by decide) (by decide) ((work_parent hc hf12 (by decide)).trans hy)
    ((work_parent hc hf12 (by decide)).trans hyl) (work_source hc hf12 hk12 hys)
    hy1 (by omega) hyw) fun s3 ⟨hc3, hm3, hy3, ha3, hf3, hk3⟩ => ?_)
  have hg3 := (ha3 aX (by decide) (by decide)).trans hg2
  have ho3 := (ha3 aOne (by decide) (by decide)).trans ho2
  have hr3 := (ha3 aR2 (by decide) (by decide)).trans hr2
  have hr3' : wv s3.mem (off B o) (slot wx aR2) wx =
      (2 ^ (64 * wx) * 2 ^ (64 * wx)) % m := by
    rw [hr3, ← Nat.pow_add, show 64 * wx + 64 * wx = 128 * wx by omega]
  have hR := coprime_pow2 hodd (64 * wx)
  refine WP.seq (WP.mono (jointEncode_ok M ⟨hm3, hc3.scrT⟩ hw2 (by omega) hm hR hg3 hy3 ho3 hr3')
    fun s4 ⟨hc4, hv4, hf4, hk4⟩ => ?_)
  have hsub4 := arrays_context hc3 hf4 (by decide) hk4
  refine WP.mono (jointBuild_ok M hc4 hw2 (by omega) (by omega) hR hv4)
    fun t ⟨hct, ht, hyt, hot, hft, hkt⟩ => ?_
  exact ⟨hsub4.of_frmT hft (workRanges_ok wx) hkt.wr (hkt.gpr .x0 (by decide)),
    hct, ht, hyt, hot, (((hf12.trans hf3).trans (arrays_work hf4 (by decide))).trans hft),
    ((((hk12.trans hk3).trans hk4).trans hkt).mono (by decide))⟩

end VG.Proof.Dsa.AArch64
