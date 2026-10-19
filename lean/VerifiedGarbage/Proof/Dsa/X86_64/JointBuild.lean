module
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Proof.Dsa.X86_64.JointAdvance
public import VerifiedGarbage.Proof.Dsa.X86_64.JointWindow

import VerifiedGarbage.Proof.Dsa.X86_64.JointEntries
import VerifiedGarbage.Proof.Dsa.X86_64.Setup
import Mathlib.Tactic.Set

/-! # Preparing the joint table and Montgomery accumulator -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
  refine WP.seq (WP.mono (tabInit_ok hc.exp) fun v ⟨hm, hk⟩ => ?_)
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sTab) (off P (slot w 8)) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sTab)) (off P (slot w 8))) P
    (d := 8 * Crt.sEnt) (off P (slot w 8)) (by decide)
  rw [← hm] at o2
  have hf : Frm P (crtExpRanges w) t.mem v.mem :=
    (Frm.of_outside o1 (by simp [crtExpRanges])).trans
      (Frm.of_outside o2 (by simp [crtExpRanges, crtWinRanges]))
  have cv := hc.exp.of_frm hf hk.2.2 (hk.gpr (by decide))
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
    hc'.scrT.congr hku.2.2⟩
  refine ⟨uc, st'.of_arrays hfu (by decide) hc'.scrT.nowrap,
    (hfu.wv_of_not_mem (by decide) (by decide) hc'.mod.good.scr.nowrap).trans sy, hone,
    ((exp_work hf).trans hs.frm).trans ((arrays_work hf' (by decide)).trans (arrays_work hfu (by decide))),
    (((hk.trans hs.keep).trans hk').trans hku).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
