module

public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCalls
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.Call
public import VerifiedGarbage.Impl.Dsa.AArch64.Joint
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Dsa.AArch64.JointBuildContext
public import VerifiedGarbage.Proof.Dsa.AArch64.JointWindow
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.Joint
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
public import VerifiedGarbage.Proof.Dsa.AArch64.JointAdvance
import VerifiedGarbage.Proof.Dsa.AArch64.Setup

/-! ### `Dsa.AArch64.ReadyJoint`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.JointPower`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.JointPrepare`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.JointEntries`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.JointStore`, which this module and modules that import it used -/

section

/-! # Writing one entry of the joint exponentiation table -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- Any write inside the arithmetic prefix preserves its linked parent. -/
theorem joint_outside_work {P : Addr} {w a k : Nat} {m m' : Mem}
    (hf : Outside P a k m m') (ha : 136 ≤ a) (hk : a + k ≤ slot w 8 + tabBytes w) :
    Frm P (workRanges w) m m' := by
  intro x hx
  apply hf x
  have := hx (136, slot w 8 + tabBytes w - 136) (List.mem_singleton_self _)
  have hslot : 136 ≤ slot w 8 + tabBytes w := by unfold slot hdrBytes; omega_using []
  omega_using [ha, hk, this]

theorem jointStore_ok {t : State} {P : Addr} {w n j : Nat} {minv : BitVec 64}
    (hc : JointCtx t P w n minv) (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hj : j < 16)
    (he : word t.mem P (8 * Crt.sEnt) = off P (slot w (8 + j))) :
    WP isa (.seq (seqs (Crt.toEnt aY)) Crt.nextEnt) t fun u =>
      JointCtx u P w n minv ∧
      (∀ a < 8, wv u.mem P (slot w a) w = wv t.mem P (slot w a) w) ∧
      (∀ k < 32, k ≠ Crt.sEnt → word u.mem P (8 * k) = word t.mem P (8 * k)) ∧
      word u.mem P (8 * Crt.sEnt) = off P (slot w (8 + (j + 1))) ∧
      wv u.mem P (slot w (8 + j)) w = wv t.mem P (slot w aY) w ∧
      (∀ k < 16, k ≠ j → wv u.mem P (slot w (8 + k)) w = wv t.mem P (slot w (8 + k)) w) ∧
      Frm P (workRanges w) t.mem u.mem ∧ Keep mmRegs t u := by
  have hn := hc.scrT.nowrap
  have hend := ent_le w hj
  have helo := slot_mono w (show 8 ≤ 8 + j by omega_using [])
  have hsmall : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  refine WP.seq (WP.mono (toEnt_ok hc.exp hw hw' (by decide) hj he) fun v ⟨hv, hf, hk⟩ => ?_)
  have fexp : Frm P (crtExpRanges w) t.mem v.mem :=
    Frm.of_outside (hf.mono (o' := slot w 8) (n' := tabBytes w) helo (by omega_using [hend])) (by simp [crtExpRanges])
  have cv := hc.exp.of_frm fexp hk.wr (hk.gpr .x0 (by decide))
  have ve : word v.mem P (8 * Crt.sEnt) = off P (slot w (8 + j)) :=
    (hf.word (Or.inl (by have := hdr_lt_slot w 8 (show Crt.sEnt < 32 by decide); omega_using [helo, this])) (by decide)).trans he
  refine WP.mono (nextEnt_ok cv hw' ve) fun u ⟨hm, ku⟩ => ?_
  have ho := writeW_outside v.mem P (d := 8 * Crt.sEnt) (off P (slot w (8 + j) + 8 * (w + 2))) (by decide)
  rw [← hm] at ho
  have ff : Frm P (crtExpRanges w) v.mem u.mem := Frm.of_outside ho (by simp [crtExpRanges, crtWinRanges])
  have cu := cv.of_frm ff ku.wr (ku.gpr .x0 (by decide))
  have harray : ∀ a, slot w a + 8 * w ≤ slot w 8 + tabBytes w →
      wv u.mem P (slot w a) w = wv v.mem P (slot w a) w := fun a ha =>
    ho.wv (Or.inr (by have := hdr_lt_slot w a (show Crt.sEnt < 32 by decide); omega_using [this])) (by omega_using [hn, ha])
  refine ⟨⟨⟨cu.good, cu.n, cu.inv⟩, cu.scrT⟩, ?_, ?_, ?_, ?_, ?_, ?_, (hk.trans ku).mono (by decide)⟩
  · intro a ha
    have hab := slot_le (w := w) ha
    rw [harray a (by omega_using [hab]), hf.wv (Or.inl (by omega_using [helo, hab])) (by omega_using [hn, hab])]
  · intro k hk' hne
    rw [hm, hdrStore_hdr _ _ _ (by decide) hk' (Ne.symm hne)]
    exact hf.word (Or.inl (by have := hdr_lt_slot w 8 hk'; omega_using [helo, this])) (by omega_using [hk'])
  · rw [hm, word_writeW_self]
    congr 1
    simp only [slot, Nat.add_mul, Nat.one_mul]
    omega_using []
  · rw [harray (8 + j) (by omega_using [hend])]; exact hv
  · intro k hk' hne
    have hb := ent_le w hk'
    have hs := slot_sep (w := w) (show 8 + k ≠ 8 + j by omega_using [hne])
    rw [harray (8 + k) (by omega_using [hb])]
    exact hf.wv (by omega_using [hs]) (by omega_using [hn, hb])
  · exact (joint_outside_work hf (by omega_using [helo, hsmall]) (by omega_using [hend])).trans
      (joint_outside_work ho (by decide) (by have := hdr_lt_slot w 8 (show Crt.sEnt < 32 by decide); omega_using [this]))

end VG.Proof.Dsa.AArch64

end

end

/-! # Construction of all sixteen joint exponentiation table entries -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure JointBuildInv (t₀ : State) (P : Addr) (w n g y : Nat) (minv : BitVec 64)
    (j : Nat) (t : State) : Prop where
  ctx : JointCtx t P w n minv
  vals : JointBuildValues t.mem P w n g y j
  tab : word t.mem P (8 * Crt.sTab) = off P (slot w 8)
  ent : word t.mem P (8 * Crt.sEnt) = off P (slot w (8 + j))
  entries : ∀ k < j, wv t.mem P (slot w (8 + k)) w =
    (g ^ (k / 4) * y ^ (k % 4)) * 2 ^ (64 * w) % n
  frm : Frm P (workRanges w) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

theorem jointBuildStep_ok (M : Mont) {t₀ t : State} {P : Addr} {w n g y j : Nat} {minv : BitVec 64}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hn : 0 < n) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hj : j < 16) (h : JointBuildInv t₀ P w n g y minv j t) :
    WP isa (Joint.buildStep M.mm j) t (JointBuildInv t₀ P w n g y minv (j + 1)) := by
  unfold Joint.buildStep
  refine WP.seq (WP.mono (jointStore_ok h.ctx hw hw' hj h.ent)
    fun v ⟨hc, ha, hh, he, hv, ht, hf, hk⟩ => ?_)
  have vals := h.vals.congr ha
  have entries : ∀ k < j + 1, wv v.mem P (slot w (8 + k)) w =
      (g ^ (k / 4) * y ^ (k % 4)) * 2 ^ (64 * w) % n := by
    intro k hk'
    by_cases he : k = j
    · subst k; exact hv.trans h.vals.entry
    · exact (ht k (by omega_using [hj, hk']) he).trans (h.entries k (by omega_using [hk', he]))
  refine WP.mono (jointAdvance_ok M hc hw hw' hn hR vals) fun u ⟨hu, hvu, hfu, hku⟩ => ?_
  refine ⟨hu, hvu, (hfu.hslot (by decide)).trans ((hh _ (by decide) (by decide)).trans h.tab),
    (hfu.hslot (by decide)).trans he, ?_, (h.frm.trans hf).trans (arrays_work hfu (by decide)),
    ((h.keep.trans hk).trans hku).mono (by decide)⟩
  intro k hk'
  exact (joint_arrays_entry hfu (by decide) hc.scrT.nowrap (by omega_using [hj, hk'])).trans (entries k hk')

theorem jointBuildSteps_ok (M : Mont) {t₀ t : State} {P : Addr} {w n g y j count : Nat} {minv : BitVec 64}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hn : 0 < n) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hj : j + count ≤ 16) (h : JointBuildInv t₀ P w n g y minv j t) :
    WP isa (Joint.buildSteps M.mm j count) t (JointBuildInv t₀ P w n g y minv (j + count)) := by
  induction count generalizing j t with
  | zero => exact WP.block_nil h
  | succ count ih =>
    unfold Joint.buildSteps
    refine WP.seq (WP.mono (jointBuildStep_ok M hw hw' hn hR (by omega_using [hj]) h) fun u hu => ?_)
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using ih (j := j + 1) (by omega_using [hj]) hu

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.JointEncode`, which this module and modules that import it used -/

section

/-! # Encoding the two bases of joint DSA exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

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
  obtain val1 : wv s1.mem P (slot w aY) w = 2 ^ (64 * w) % n := by
    obtain h2 : wv s.mem P (slot w aR2) w % n = 2 ^ (64 * w) * 2 ^ (64 * w) % n := by rw [hr2, Nat.mod_mod]
    obtain hv := VG.Proof.Dsa.mont_decode hR h2 hv1
    rwa [Nat.mod_eq_of_lt hl1] at hv
  obtain r21 := (hf1.wv_of_not_mem (by decide) (by decide) hnow).trans hr2
  obtain x1 := (hf1.wv_of_not_mem (by decide) (by decide) hnow).trans hg
  obtain y1 := (hf1.wv_of_not_mem (by decide) (by decide) hnow).trans hy
  refine WP.seq (WP.mono (jointProduct_ok M hc1 hw hw' (by unfold MmUse; decide)
    (by rw [r21]; exact Nat.mod_lt _ (by omega_using [hn]))) fun s2 ⟨hc2, hl2, hv2, hf2, hk2⟩ => ?_)
  rw [x1, r21] at hv2
  obtain val2 := VG.Proof.Dsa.mont_scale hR hv2
  rw [Nat.mod_eq_of_lt hl2] at val2
  obtain r22 := (hf2.wv_of_not_mem (by decide) (by decide) hnow).trans r21
  obtain y2 := (hf2.wv_of_not_mem (by decide) (by decide) hnow).trans y1
  obtain acc2 := (hf2.wv_of_not_mem (by decide) (by decide) hnow).trans val1
  refine WP.seq (WP.mono (jointProduct_ok M hc2 hw hw' (by unfold MmUse; decide)
    (by rw [r22]; exact Nat.mod_lt _ (by omega_using [hn]))) fun s3 ⟨hc3, hl3, hv3, hf3, hk3⟩ => ?_)
  rw [y2, r22] at hv3
  obtain val3 := VG.Proof.Dsa.mont_scale hR hv3
  rw [Nat.mod_eq_of_lt hl3] at val3
  obtain x3 := (hf3.wv_of_not_mem (by decide) (by decide) hnow).trans val2
  obtain acc3 := (hf3.wv_of_not_mem (by decide) (by decide) hnow).trans acc2
  refine WP.seq (WP.mono (jointCopy_ok hc3 hw hw' (by decide) (by decide) (by decide) (by decide))
    fun s4 ⟨hc4, hv4, hf4, hk4⟩ => ?_)
  obtain gen4 := hv4.trans x3
  obtain base4 := (hf4.wv_of_not_mem (by decide) (by decide) hnow).trans val3
  obtain acc4 := (hf4.wv_of_not_mem (by decide) (by decide) hnow).trans acc3
  refine WP.seq (WP.mono (jointCopy_ok hc4 hw hw' (by decide) (by decide) (by decide) (by decide))
    fun s5 ⟨hc5, hv5, hf5, hk5⟩ => ?_)
  obtain one5 := hv5.trans acc4
  obtain gen5 := (hf5.wv_of_not_mem (by decide) (by decide) hnow).trans gen4
  obtain base5 := (hf5.wv_of_not_mem (by decide) (by decide) hnow).trans base4
  obtain acc5 := (hf5.wv_of_not_mem (by decide) (by decide) hnow).trans acc4
  refine WP.mono (jointCopy_ok hc5 hw hw' (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hu, hv6, hf6, hk6⟩ => ?_
  obtain gen6 := (hf6.wv_of_not_mem (by decide) (by decide) hnow).trans gen5
  obtain base6 := (hf6.wv_of_not_mem (by decide) (by decide) hnow).trans base5
  obtain one6 := (hf6.wv_of_not_mem (by decide) (by decide) hnow).trans one5
  obtain acc6 := (hf6.wv_of_not_mem (by decide) (by decide) hnow).trans acc5
  obtain row6 := hv6.trans acc5
  refine ⟨hu, ⟨gen6, base6, one6, ?_, ?_⟩, ?_,
    (((((hk1.trans hk2).trans hk3).trans hk4).trans hk5).trans hk6).mono (by decide)⟩
  · simpa only [Nat.zero_div, Nat.pow_zero, Nat.one_mul] using row6
  · simpa only [Nat.zero_div, Nat.zero_mod, Nat.pow_zero, Nat.one_mul] using acc6
  exact (((((hf1.mono (by decide)).trans (hf2.mono (by decide))).trans
    (hf3.mono (by decide))).trans (hf4.mono (by decide))).trans (hf5.mono (by decide))).trans (hf6.mono (by decide))

end VG.Proof.Dsa.AArch64

end

end

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
    hg1 (by omega_using [hw48, hgw]) hgw) fun s2 ⟨hc2, hm2, hg2, ha2, hf2, hk2⟩ => ?_)
  have hf12 := hf1.trans hf2
  have hk12 := (hk1.trans hk2).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  have ho2 := (ha2 aOne (by decide) (by decide)).trans ho1
  have hr2 := (ha2 aR2 (by decide) (by decide)).trans hr1
  refine WP.seq (WP.mono (load_mod_ok hc2 hm2 hw2 hwx hw30 (by decide) (by decide)
    (by decide) (by decide) ((work_parent hc hf12 (by decide)).trans hy)
    ((work_parent hc hf12 (by decide)).trans hyl) (work_source hc hf12 hk12 hys)
    hy1 (by omega_using [hw48, hyw]) hyw) fun s3 ⟨hc3, hm3, hy3, ha3, hf3, hk3⟩ => ?_)
  have hg3 := (ha3 aX (by decide) (by decide)).trans hg2
  have ho3 := (ha3 aOne (by decide) (by decide)).trans ho2
  have hr3 := (ha3 aR2 (by decide) (by decide)).trans hr2
  have hr3' : wv s3.mem (off B o) (slot wx aR2) wx =
      (2 ^ (64 * wx) * 2 ^ (64 * wx)) % m := by
    rw [hr3, ← Nat.pow_add, show 64 * wx + 64 * wx = 128 * wx by omega_using []]
  have hR := coprime_pow2 hodd (64 * wx)
  refine WP.seq (WP.mono (jointEncode_ok M ⟨hm3, hc3.scrT⟩ hw2 (by omega_using [hw48]) hm hR hg3 hy3 ho3 hr3')
    fun s4 ⟨hc4, hv4, hf4, hk4⟩ => ?_)
  have hsub4 := arrays_context hc3 hf4 (by decide) hk4
  refine WP.mono (jointBuild_ok M hc4 hw2 (by omega_using [hw48]) (by omega_using [hm]) hR hv4)
    fun t ⟨hct, ht, hyt, hot, hft, hkt⟩ => ?_
  exact ⟨hsub4.of_frmT hft (workRanges_ok wx) hkt.wr (hkt.gpr .x0 (by decide)),
    hct, ht, hyt, hot, (((hf12.trans hf3).trans (arrays_work hf4 (by decide))).trans hft),
    ((((hk12.trans hk3).trans hk4).trans hkt).mono (by decide))⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.JointRun`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.JointByte`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.JointWindows`, which this module and modules that import it used -/

section

/-! # Four joint windows consume two exponent bytes -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- After `j` windows of the bytes `v` (of `u`) and `z` (of `v`) from `t₀`,
where `Y ≡ g^E y^F R`. -/
structure JointWinInv (t₀ : State) (P : Addr) (w : Nat) (minv : BitVec 64)
    (n xc g y E F v z j : Nat) (t : State) : Prop where
  ctx : CExpCtx t P w minv n xc
  tab : JointTab t.mem P w n g y
  ylt : wv t.mem P (slot w aY) w < n
  val : wv t.mem P (slot w aY) w % n =
    (g ^ (E * 4 ^ j + v / 4 ^ (4 - j)) * y ^ (F * 4 ^ j + z / 4 ^ (4 - j))) * 2 ^ (64 * w) % n
  bytes : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 ((256 * v + z) * 4 ^ j)
  count : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (4 - j)
  frm : Frm P (crtWinRanges w) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

theorem jointWinStep_ok (M : Mont) {t s : State} {P : Addr} {w n xc g y E F v z j : Nat}
    {minv : BitVec 64} (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hv : v < 256) (hz : z < 256) (hj : j < 4)
    (h : JointWinInv t P w minv n xc g y E F v z j s) :
    WP isa (seqs (Joint.window M.mm)) s fun s' =>
      JointWinInv t P w minv n xc g y E F v z (j + 1) s' ∧ ((s'.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ 4) := by
  have hp : 4 ^ j ≤ 64 := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide
  refine WP.mono (jointWindow_ok M h.ctx h.tab hw hw' hR h.ylt h.val h.bytes
    (by have := Nat.mul_le_mul_left (256 * v + z) hp; omega_arith) h.count (by omega_arith))
    fun s' ⟨hc, ht, hy, hval, hb, hn, h3, hf, hk⟩ => ⟨⟨hc, ht, hy, ?_, ?_, ?_,
      h.frm.trans hf, (h.keep.trans hk).mono (by decide)⟩, ?_⟩
  · rw [hval, (VG.Proof.Dsa.joint_byte_step hv hz hj E F).1,
      (VG.Proof.Dsa.joint_byte_step hv hz hj E F).2]
  · rw [hb, Nat.pow_succ]; congr 1; ac_rfl
  · rw [hn]; congr 1
  · rw [h3, cnt_ne (by omega_arith)]; omega_arith

theorem jointWins_ok (M : Mont) {t : State} {P : Addr} {w n xc g y E F v z : Nat}
    {minv : BitVec 64} (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hv : v < 256) (hz : z < 256) (h : JointWinInv t P w minv n xc g y E F v z 0 t) :
    WP isa (.loop (seqs (Joint.window M.mm)) (.nonzero .x .x3)) t
      (JointWinInv t P w minv n xc g y E F v z 4) :=
  count_loop (cr := .x3) (n := 4) (by decide) (JointWinInv t P w minv n xc g y E F v z)
    (fun _ hj _ hI => jointWinStep_ok M hw hw' hR hv hz hj hI) h

end VG.Proof.Dsa.AArch64

end

end

/-! # Loading a pair of exponent bytes without secret-dependent addresses -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- After `i` bytes of both exponents (`L` bytes `eb` at `ep` and `fb` at
`fp`) from `t₀`. -/
structure JointByteInv (t₀ : State) (P : Addr) (w : Nat) (minv : BitVec 64)
    (n xc g y : Nat) (ep fp : Addr) (L : Nat) (eb fb : List Byte) (i : Nat) (t : State) : Prop where
  ctx : CExpCtx t P w minv n xc
  tab : JointTab t.mem P w n g y
  ylt : wv t.mem P (slot w aY) w < n
  val : wv t.mem P (slot w aY) w % n = (g ^ pre eb i * y ^ pre fb i) * 2 ^ (64 * w) % n
  idx : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i
  e : word t.mem P (8 * Crt.sExp) = ep
  f : word t.mem P (8 * Joint.sExp2) = fp
  len : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L
  frm : Frm P (crtExpRanges w) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- Both bytes into `sV`, and the window count 4. -/
theorem jointByteHead_ok {t : State} {P ep fp : Addr} {w n xc i : Nat} {minv : BitVec 64}
    (hc : CExpCtx t P w minv n xc)
    (hi : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i)
    (he : word t.mem P (8 * Crt.sExp) = ep) (hf : word t.mem P (8 * Joint.sExp2) = fp)
    {v z : Byte}
    (hrE : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1)
    (hrF : InRegions (t.rd ++ t.wr) (fp + BitVec.ofNat 64 i) 1)
    (hv : t.mem (ep + BitVec.ofNat 64 i) = v) (hz : t.mem (fp + BitVec.ofNat 64 i) = z) :
    WP isa (.block Joint.byteHead) t fun u =>
      u.mem = (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (256 * v.toNat + z.toNat))).writeW
        (off P (8 * Crt.sBit)) (BitVec.ofNat 64 4) ∧ Keep [.x3, .x4, .x5] t u := by
  have hv' := v.isLt
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [Joint.byteHead, hc.good.x0, hdr_enc (show Crt.sExp < 32 by decide), hdr_enc (show Crt.sI < 32 by decide),
    hdr_enc (show Joint.sExp2 < 32 by decide), hdr_enc (show Crt.sV < 32 by decide),
    hdr_enc (show Crt.sBit < 32 by decide), hc.ld (i := Crt.sExp) (by decide),
    hc.ld (i := Crt.sI) (by decide), hc.ld (i := Joint.sExp2) (by decide), he, hi, hf, hrE, hrF, zext_byte, hv, hz,
    shl_ofNat (show v.toNat * 2 ^ 8 < 2 ^ 64 by omega_arith), ofNat_add_ofNat,
    hc.st (i := Crt.sV) (by decide), hc.st (i := Crt.sBit) (by decide)]
  rw [show v.toNat * 2 ^ 8 + z.toNat = 256 * v.toNat + z.toNat by omega_arith]
  rfl

/-- Read one byte from each exponent, run four joint windows, and advance. -/
theorem jointByte_ok (M : Mont) {t₀ t : State} {P : Addr} {w n xc g y : Nat}
    {minv : BitVec 64} {ep fp : Addr} {L : Nat} {eb fb : List Byte} {i : Nat}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hL : eb.length = L) (hF : fb.length = L) (hL' : L < 2 ^ 31) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot w 8 + tabBytes w ≤ ofs P (ep + BitVec.ofNat 64 i))
    (frd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (fp + BitVec.ofNat 64 i) 1)
    (fbytes : ∀ i (h : i < L), t₀.mem (fp + BitVec.ofNat 64 i) = fb[i]'(by omega_arith))
    (fout : ∀ i < L, slot w 8 + tabBytes w ≤ ofs P (fp + BitVec.ofNat 64 i))
    (hI : JointByteInv t₀ P w minv n xc g y ep fp L eb fb i t) :
    WP isa (seqs [.block Joint.byteHead, .loop (seqs (Joint.window M.mm)) (.nonzero .x .x3),
      .block Joint.byteNext]) t fun t' =>
      JointByteInv t₀ P w minv n xc g y ep fp L eb fb (i + 1) t' ∧ ((t'.gpr .x3).toNat ≠ 0 ↔ i + 1 ≠ L) := by
  have hn := hI.ctx.scrT.nowrap
  let v := (eb[i]'(by omega_arith)).toNat
  let z := (fb[i]'(by omega_arith)).toNat
  obtain hv : v < 256 := (eb[i]'(by omega_arith)).isLt
  obtain hz : z < 256 := (fb[i]'(by omega_arith)).isLt
  obtain er : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.rd, hI.keep.wr]; exact hrd i hi
  obtain fr : InRegions (t.rd ++ t.wr) (fp + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.rd, hI.keep.wr]; exact frd i hi
  obtain ev : t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := (crtExpRanges_ok w r hr).2; have := hout i hi; omega_arith)]
    exact hbytes i hi
  obtain fv : t.mem (fp + BitVec.ofNat 64 i) = fb[i]'(by omega_arith) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := (crtExpRanges_ok w r hr).2; have := fout i hi; omega_arith)]
    exact fbytes i hi
  simp only [seqs]
  refine WP.seq (WP.mono (jointByteHead_ok hI.ctx hI.idx hI.e hI.f er fr ev fv)
    fun t₁ ⟨hm₁, k₁⟩ => ?_)
  obtain o1 := writeW_outside t.mem P (d := 8 * Crt.sV) (BitVec.ofNat 64 (256 * v + z)) (by decide)
  obtain o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (256 * v + z))) P
    (d := 8 * Crt.sBit) (BitVec.ofNat 64 4) (by decide)
  rw [← hm₁] at o2
  obtain f₁ : Frm P (crtWinRanges w) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [crtWinRanges])).trans (Frm.of_outside o2 (by simp [crtWinRanges]))
  obtain hc₁ := hI.ctx.of_win f₁ k₁.wr (k₁.gpr .x0 (by decide))
  obtain hY0 := slot_le (w := w) (show aY < 8 by decide)
  obtain hYe : wv t₁.mem P (slot w aY) w = wv t.mem P (slot w aY) w := by
    rw [o2.wv (by have := hdr_lt_slot w aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith),
      o1.wv (by have := hdr_lt_slot w aY (show Crt.sV < 32 by decide); omega_arith) (by omega_arith)]
  obtain hB0 : JointWinInv t₁ P w minv n xc g y (pre eb i) (pre fb i) v z 0 t₁ := by
    refine ⟨hc₁, hI.tab.of_win f₁ hn, hYe ▸ hI.ylt, ?_, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hYe, hI.val, Nat.pow_zero, Nat.mul_one, Nat.mul_one, Nat.sub_zero,
        Nat.div_eq_of_lt (show v < 4 ^ 4 from hv), Nat.div_eq_of_lt (show z < 4 ^ 4 from hz),
        Nat.add_zero, Nat.add_zero]
    · rw [o2.word (by decide) (by decide), word_writeW_self, Nat.pow_zero, Nat.mul_one]
    · rw [hm₁, word_writeW_self]
  refine WP.seq (WP.mono (jointWins_ok M hw hw' hR hv hz hB0) fun t₂ h₂ => ?_)
  -- The next byte.
  have hc₂ := h₂.ctx
  obtain hh₂ : ∀ k < 32, k ≠ Crt.sV → k ≠ Crt.sBit → k ≠ Crt.sNib → k ≠ Crt.sEnt → k ≠ Crt.sJ →
      word t₂.mem P (8 * k) = word t.mem P (8 * k) := fun k hk h1 h2 h3 h4 h5 => by
    rw [h₂.frm.word_eq (crtWinRanges_hdr w hk h1 h2 h3 h4 h5) (by omega_arith), hm₁,
      hdrStore_hdr (i := Crt.sBit) _ _ _ (by decide) hk (Ne.symm h2),
      hdrStore_hdr (i := Crt.sV) _ _ _ (by decide) hk (Ne.symm h1)]
  obtain hidx₂ := (hh₂ Crt.sI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI.idx
  obtain he₂ := (hh₂ Crt.sExp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI.e
  obtain hf₂ := (hh₂ Joint.sExp2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI.f
  obtain hlen₂ := (hh₂ Crt.sExpLen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    hI.len
  obtain hlen₂' : (t₂.mem.writeW (off P (8 * Crt.sI)) (BitVec.ofNat 64 (i + 1))).readW (off P (8 * Crt.sExpLen)) 64 =
      BitVec.ofNat 64 L := by
    rw [← hlen₂]; exact hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t' => t'.mem = t₂.mem.writeW (off P (8 * Crt.sI))
      (BitVec.ofNat 64 (i + 1)) ∧ t'.gpr .x3 = BitVec.ofNat 64 L - BitVec.ofNat 64 (i + 1)) (by
    brun [Joint.byteNext, hc₂.good.x0, hdr_enc (show Crt.sI < 32 by decide),
      hdr_enc (show Crt.sExpLen < 32 by decide),
      hc₂.ld (i := Crt.sI) (by decide), hc₂.st (i := Crt.sI) (by decide), hidx₂, ofNat_add_ofNat,
      hc₂.ld (i := Crt.sExpLen) (by decide), hlen₂']) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨hm', h3'⟩, k'⟩ => ⟨?_, ?_⟩
  · have o' := writeW_outside t₂.mem P (d := 8 * Crt.sI) (BitVec.ofNat 64 (i + 1)) (by decide)
    rw [← hm'] at o'
    obtain f' : Frm P (crtExpRanges w) t₂.mem t'.mem := Frm.of_outside o' (by simp [crtExpRanges])
    obtain hYe : wv t'.mem P (slot w aY) w = wv t₂.mem P (slot w aY) w :=
      o'.wv (by have := hdr_lt_slot w aY (show Crt.sI < 32 by decide); omega_arith) (by omega_arith)
    refine ⟨hc₂.of_frm f' k'.wr (k'.gpr .x0 (by decide)), ?_, hYe ▸ h₂.ylt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨by rw [o'.word (by decide) (by decide)]; exact h₂.tab.tab,
        fun j hj => by rw [o'.wv (by have := hdr_lt_slot w (8 + j) (show Crt.sI < 32 by decide); omega_arith)
          (by have := ent_le w hj; omega_arith)]; exact h₂.tab.lt j hj,
        fun j hj => by rw [o'.wv (by have := hdr_lt_slot w (8 + j) (show Crt.sI < 32 by decide); omega_arith)
          (by have := ent_le w hj; omega_arith)]; exact h₂.tab.val j hj⟩
    · rw [hYe, h₂.val, pre_succ eb (by omega_arith), pre_succ fb (by omega_arith)]
      simp only [Nat.reducePow, Nat.reduceSub, Nat.pow_zero, Nat.div_one]
      simp only [v, z]
      ac_rfl
    · rw [hm', word_writeW_self]
    · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact he₂
    · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact hf₂
    · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen₂
    · exact ((hI.frm.trans (f₁.mono (crtWinRanges_sub w))).trans
        (h₂.frm.mono (crtWinRanges_sub w))).trans f'
    · exact (((hI.keep.trans k₁).trans h₂.keep).trans k').mono (by decide)
  · rw [h3', VG.Offset.ofNat_sub_ofNat (show i + 1 ≤ L by omega_arith), cnt_ne (by omega_arith)]
    omega_arith

/-- Both equal-length exponent strings are scanned sequentially. -/
theorem jointBytes_ok (M : Mont) {t : State} {P : Addr} {w n xc g y : Nat}
    {minv : BitVec 64} {ep fp : Addr} {L : Nat} {eb fb : List Byte}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hL : eb.length = L) (hF : fb.length = L) (hL0 : 0 < L) (hL' : L < 2 ^ 31)
    (hrd : ∀ i < L, InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot w 8 + tabBytes w ≤ ofs P (ep + BitVec.ofNat 64 i))
    (frd : ∀ i < L, InRegions (t.rd ++ t.wr) (fp + BitVec.ofNat 64 i) 1)
    (fbytes : ∀ i (h : i < L), t.mem (fp + BitVec.ofNat 64 i) = fb[i]'(by omega_arith))
    (fout : ∀ i < L, slot w 8 + tabBytes w ≤ ofs P (fp + BitVec.ofNat 64 i))
    (h : JointByteInv t P w minv n xc g y ep fp L eb fb 0 t) :
    WP isa (Joint.bytes M.mm) t (JointByteInv t P w minv n xc g y ep fp L eb fb L) :=
  count_loop (cr := .x3) (n := L) hL0 (JointByteInv t P w minv n xc g y ep fp L eb fb)
    (fun _ hi _ hI => jointByte_ok M hw hw' hR hL hF hL' hi hrd hbytes hout frd fbytes fout hI) h

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.JointInit`, which this module and modules that import it used -/

section

/-! # Public exponent pointers for joint DSA verification -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def jointInitRanges : List (Nat × Nat) :=
  [(8 * Crt.sExp, 8), (8 * Joint.sExp2, 8), (8 * Crt.sExpLen, 8), (8 * Crt.sI, 8)]

theorem jointInit_ranges (w : Nat) : ∀ r ∈ jointInitRanges,
    136 ≤ r.1 ∧ r.1 + r.2 ≤ 256 ∧ r.1 + r.2 ≤ slot w 8 + tabBytes w := by
  have h : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  simp only [jointInitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [Crt.sExp, Joint.sExp2, Crt.sRem, Crt.sExpLen, Crt.sI, sFn] <;> omega_using [h]

/-- The memory after `expInit`. -/
def jointInitMem (m : Mem) (B : Addr) (o L : Nat) : Mem :=
  (((m.writeW (off (off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 L)).writeW
    (off (off B o) (8 * Crt.sExp)) (off B u)).writeW
    (off (off B o) (8 * Joint.sExp2)) (off B v)).writeW
    (off (off B o) (8 * Crt.sI)) (BitVec.ofNat 64 0)

theorem jointInit_raw {s : State} {B : Addr} {Z o w wx L : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hfield : 344 ≤ Z)
    (hl : word s.mem B Field.qLen.offset = BitVec.ofNat 64 L) :
    WP isa (.block Joint.expInit) s fun t =>
      t.mem = jointInitMem s.mem B o L ∧ Keep [.x3, .x4, .x5] s t := by
  have hparent : InRegions (s.rd ++ s.wr) (off B Field.qLen.offset) 8 := hc.scr.ld hfield
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [Joint.expInit, jointInitMem, hc.x0, hdr_enc (show Crt.sLink < 32 by decide),
    hdr_enc (show Crt.sExp < 32 by decide), hdr_enc (show Joint.sExp2 < 32 by decide),
    hdr_enc (show Crt.sExpLen < 32 by decide), hdr_enc (show Crt.sI < 32 by decide),
    hc.ld' (show Crt.sLink < 32 by decide), hc.link', hparent, hl,
    hc.st' (show Crt.sExp < 32 by decide), hc.st' (show Joint.sExp2 < 32 by decide),
    hc.st' (show Crt.sExpLen < 32 by decide), hc.st' (show Crt.sI < 32 by decide), off_off]
  rfl

theorem jointInit_frame {s t : State} {B : Addr} {o L : Nat}
    (hm : t.mem = jointInitMem s.mem B o L) :
    Frm (off B o) jointInitRanges s.mem t.mem := by
  rw [hm]
  exact (((Frm.of_outside (writeW_outside _ (off B o) _ (d := 8 * Crt.sExpLen) (by decide))
    (by simp [jointInitRanges])).trans
    (Frm.of_outside (writeW_outside _ (off B o) _ (d := 8 * Crt.sExp) (by decide))
      (by simp [jointInitRanges]))).trans
    (Frm.of_outside (writeW_outside _ (off B o) _ (d := 8 * Joint.sExp2) (by decide))
      (by simp [jointInitRanges]))).trans
    (Frm.of_outside (writeW_outside _ (off B o) _ (d := 8 * Crt.sI) (by decide))
      (by simp [jointInitRanges]))

theorem jointInit_ok {s : State} {B : Addr} {Z o w wx L n g y : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hmctx : JointCtx s (off B o) wx n minv)
    (htab : JointTab s.mem (off B o) wx n g y) (hfield : 344 ≤ Z)
    (hl : word s.mem B Field.qLen.offset = BitVec.ofNat 64 L) :
    WP isa (.block Joint.expInit) s fun t =>
      SubCtx t B Z o w wx minv ∧ JointCtx t (off B o) wx n minv ∧
      JointTab t.mem (off B o) wx n g y ∧
      (∀ j < 8, wv t.mem (off B o) (slot wx j) wx = wv s.mem (off B o) (slot wx j) wx) ∧
      word t.mem (off B o) (8 * Crt.sExp) = off B u ∧
      word t.mem (off B o) (8 * Joint.sExp2) = off B v ∧
      word t.mem (off B o) (8 * Crt.sExpLen) = BitVec.ofNat 64 L ∧
      word t.mem (off B o) (8 * Crt.sI) = BitVec.ofNat 64 0 ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (jointInit_raw hc hfield hl) fun t ⟨hm, hk⟩ => ?_
  have hf := jointInit_frame hm
  have hnow := hc.scrT.nowrap
  have hr := jointInit_ranges wx
  have harr : ∀ j < 24, wv t.mem (off B o) (slot wx j) wx =
      wv s.mem (off B o) (slot wx j) wx := by
    intro j hj
    have lo : 256 ≤ slot wx j := by unfold slot hdrBytes; omega_using []
    have hi : slot wx j + 8 * (wx + 2) ≤ slot wx 8 + tabBytes wx := by
      by_cases hj8 : j < 8
      · have := slot_le (w := wx) hj8; omega_using [this]
      · have := ent_le wx (show j - 8 < 16 by omega_using [hj])
        rw [show 8 + (j - 8) = j by omega_using [hj8]] at this
        exact this
    exact hf.wv_eq (fun r h => Or.inr (by have := hr r h; omega_using [lo, this])) (by omega_using [hnow, hi])
  have hct := hc.of_frmT hf (fun r h => ⟨(hr r h).1, (hr r h).2.2⟩) hk.wr (hk.gpr .x0 (by decide))
  have hinv : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf.word_eq (fun r h => Or.inr (by have := hr r h; unfold slot hdrBytes; omega_using [this])) (by
      have := slot_le (w := wx) (show aN < 8 by decide); omega_using [hnow, this])]
    exact hmctx.mod.inverse
  refine ⟨hct, ⟨⟨hct.good, (harr aN (by decide)).trans hmctx.mod.modulus, hinv⟩, hct.scrT⟩,
    ⟨?_, fun j hj => (harr (8 + j) (by omega_using [hj])).symm ▸ htab.lt j hj,
      fun j hj => (harr (8 + j) (by omega_using [hj])).symm ▸ htab.val j hj⟩,
    fun j hj => harr j (by omega_using [hj]), ?_, ?_, ?_, ?_, ?_, hk.mono (by decide)⟩
  · rw [hf.word_eq (by simp [jointInitRanges, Crt.sExp, Joint.sExp2, Crt.sRem, Crt.sExpLen,
      Crt.sI, Crt.sTab, sFn]) (by decide)]
    exact htab.tab
  · rw [hm, jointInitMem]
    simp (disch := decide) only [hdrStore_hdr, word_writeW_self]
  · rw [hm, jointInitMem]
    simp (disch := decide) only [hdrStore_hdr, word_writeW_self]
  · rw [hm, jointInitMem]
    simp (disch := decide) only [hdrStore_hdr, word_writeW_self]
  · rw [hm, jointInitMem, word_writeW_self]
  · intro x hx
    apply hf x
    intro r h
    have := hr r h
    have := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
    have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
    omega_arith

end VG.Proof.Dsa.AArch64

end

end

/-! # Joint exponentiation and conversion out of Montgomery representation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem joint_source_out {s : State} {B p : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) {bs : List Byte} (hs : Src s B Z p bs) :
    ∀ i < bs.length, slot wx 8 + tabBytes wx ≤ ofs (off B o) (p + BitVec.ofNat 64 i) := by
  intro i hi
  have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have := hc.hi
  have := hc.scr.nowrap
  have := hs.out i hi
  rcases ofs_rebase B (p + BitVec.ofNat 64 i) (o := o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩ <;> omega_arith

theorem jointRun_ok (M : Mont) {s : State} {B : Addr} {Z o w wx n g y : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hmctx : JointCtx s (off B o) wx n minv)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hn : 1 < n) (hodd : n % 2 = 1)
    (htab : JointTab s.mem (off B o) wx n g y)
    (hy : wv s.mem (off B o) (slot wx aY) wx = 2 ^ (64 * wx) % n)
    (hone : wv s.mem (off B o) (slot wx aOne) wx = 1)
    {eb fb : List Byte} (he : Src s B Z (off B u) eb) (hf : Src s B Z (off B v) fb)
    (hlen : fb.length = eb.length) (hL0 : 0 < eb.length) (hL' : eb.length < 2 ^ 31)
    (hfield : 344 ≤ Z) (hl : word s.mem B Field.qLen.offset = BitVec.ofNat 64 eb.length) :
    WP isa (Joint.run M.mm) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv n ∧
      wv t.mem (off B o) (slot wx aY) wx =
        (g ^ Spec.Dsa.decodeBE eb * y ^ Spec.Dsa.decodeBE fb) % n ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Joint.run seqs
  refine WP.seq (WP.mono (jointInit_ok hc hmctx htab hfield hl)
    fun s1 ⟨hc1, hm1, ht1, ha1, he1, hf1, hl1, hi1, hfrm1, hk1⟩ => ?_)
  have hsrc1 := work_source hc hfrm1 hk1 he
  have fsrc1 := work_source hc hfrm1 hk1 hf
  have hy1 := (ha1 aY (by decide)).trans hy
  have ho1 := (ha1 aOne (by decide)).trans hone
  have hR := coprime_pow2 hodd (64 * wx)
  have hI : JointByteInv s1 (off B o) wx minv n
      (wv s1.mem (off B o) (slot wx Crt.aXc) wx) g y (off B u) (off B v)
      eb.length eb fb 0 s1 := by
    refine ⟨hm1.exp, ht1, ?_, ?_, hi1, he1, hf1, hl1, Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hy1]; exact Nat.mod_lt _ (by omega_using [hn])
    · rw [hy1, Nat.mod_mod, pre_zero, pre_zero, Nat.pow_zero, Nat.pow_zero, Nat.one_mul]
  refine WP.seq (WP.mono (jointBytes_ok M hw hw' hR rfl hlen hL0 hL'
    hsrc1.rd hsrc1.val (joint_source_out hc1 hsrc1)
    (by simpa only [hlen] using fsrc1.rd) (by simpa only [hlen] using fsrc1.val)
    (by simpa only [hlen] using joint_source_out hc1 fsrc1) hI) fun s2 h2 => ?_)
  have hc2 := hc1.of_frmT h2.frm (crtExpRanges_ok wx) h2.keep.wr (h2.keep.gpr .x0 (by decide))
  have hm2 : ModCtx s2 (off B o) (slot wx 8) wx minv n := ⟨h2.ctx.good, h2.ctx.n, h2.ctx.inv⟩
  have hnow := hc1.good.scr.nowrap
  have honeSep := crtExpRanges_arr wx (j := aOne) (by decide) (by decide) (by decide) (by decide) (by decide)
  have honeSlot := slot_le (w := wx) (show aOne < 8 by decide)
  have ho2 : wv s2.mem (off B o) (slot wx aOne) wx = 1 :=
    (h2.frm.wv_eq (fun r h => by have := honeSep r h; omega_using [this]) (by omega_using [hnow, honeSlot])).trans ho1
  refine WP.mono (mont_step M hm2 (Nat.le_refl _) hw (by omega_using [hw']) (by unfold MmUse; decide)
    (by rw [ho2]; exact hn)) fun t ⟨hmt, hlt, hv, hft, hkt⟩ => ?_
  have hv2 := h2.val
  rw [← hlen, pre_len] at hv2
  rw [hlen, pre_len] at hv2
  rw [ho2] at hv
  have hresult := VG.Proof.Dsa.mont_decode hR hv2 hv
  rw [Nat.mod_eq_of_lt hlt] at hresult
  refine ⟨arrays_context hc2 hft (by decide) hkt, hmt, ?_,
    (hfrm1.trans (exp_work h2.frm)).trans (arrays_work hft (by decide)),
    ((hk1.trans h2.keep).trans hkt).mono (by decide)⟩
  simpa only [VG.Proof.Dsa.decodeBE_os2ip] using hresult

end VG.Proof.Dsa.AArch64

end

end

/-! # Loading and preparing both bases for joint DSA exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem jointPower_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1) (hparent : 344 ≤ o)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {gp yp : Addr} {gb yb : List Byte}
    (hg : word s.mem B (8 * arg) = gp)
    (hgl : word s.mem B (8 * argLen) = BitVec.ofNat 64 gb.length)
    (hgs : Src s B Z gp gb) (hg1 : 1 ≤ gb.length) (hgw : (gb.length + 7) / 8 ≤ wx)
    (hy : word s.mem B (8 * arg2) = yp)
    (hyl : word s.mem B (8 * arg2Len) = BitVec.ofNat 64 yb.length)
    (hys : Src s B Z yp yb) (hy1 : 1 ≤ yb.length) (hyw : (yb.length + 7) / 8 ≤ wx)
    {eb fb : List Byte} (he : Src s B Z (off B u) eb) (hf : Src s B Z (off B v) fb)
    (hlen : fb.length = eb.length) (hL0 : 0 < eb.length) (hL' : eb.length < 2 ^ 31)
    (hl : word s.mem B Field.qLen.offset = BitVec.ofNat 64 eb.length) :
    WP isa (Joint.power M.mm) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx =
        (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE eb) m *
         Spec.Dsa.powMod (Spec.Dsa.decodeBE yb) (Spec.Dsa.decodeBE fb) m) % m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Joint.power
  refine WP.seq (WP.mono (jointPrepare_ok M hc hw2 hw48 hwx hw30 hm hodd hn hinv
    hg hgl hgs hg1 hgw hy hyl hys hy1 hyw)
    fun s1 ⟨hc1, hm1, ht1, hy1, ho1, hf1, hk1⟩ => ?_)
  have hnow := hc.scr.nowrap
  have hhi := hc.hi
  have hsmall : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have hlen1 : word s1.mem B Field.qLen.offset = BitVec.ofNat 64 eb.length := by
    rw [hf1.word_below (fun r hr => (workRanges_ok wx r hr).2)
      (by omega_using [hnow, hhi]) (by omega_using [hnow, hhi, hsmall]) (show Field.qLen.offset + 8 ≤ o from hparent)]
    exact hl
  refine WP.mono (jointRun_ok M hc1 hm1 hw2 (by omega_using [hw48]) hm hodd ht1 hy1 ho1
    (work_source hc hf1 hk1 he) (work_source hc hf1 hk1 hf) hlen hL0 hL' (by omega_using [hparent, hhi]) hlen1)
    fun t ⟨hct, hmt, hv, hft, hkt⟩ => ⟨hct, hmt, ?_, hf1.trans hft, (hk1.trans hkt).mono (by decide)⟩
  simpa only [VG.Proof.Dsa.powMod_eq, Nat.mul_mod_mod, Nat.mod_mul_mod] using hv

end VG.Proof.Dsa.AArch64

end

end

/-! # Joint exponentiation preserving the DSA execution context -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/CoreJoint.lean`, which only this module imported.
section

/-! # Joint exponentiation in the DSA parent workspace -/

section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem coreJoint_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 16) (hparent : 344 ≤ o)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (houtp : pointerFits output.pointer) {ba bb : List Byte}
    (has : OperandBytes s B Z a ba) (hbs : OperandBytes s B Z b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    {eb fb : List Byte} (he : Src s B Z (off B u) eb) (hf : Src s B Z (off B v) fb)
    (hlen : fb.length = eb.length) (hL0 : 0 < eb.length) (hL' : eb.length < 2 ^ 31)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 eb.length)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Core.joint M.mm o a b output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
        Spec.Dsa.encodeBE k (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE eb) m *
          Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE fb) m % m) ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  apply call3_ok hg child hZ hlo hhi ho a b output ha hb houtp hl hk1 hk' hkw hout hprefix
  intro st hc hchild hargs hframe hk
  have hz : 176 ≤ Z := Nat.le_trans (by decide) hZ
  have hq : word st.mem B Field.qLen.offset = BitVec.ofNat 64 eb.length := by
    rw [hframe.word_eq (by simp [argumentRanges, Field.offset]) (by decide)]
    exact hql
  exact jointPower_ok M hc hw2 hw48 hwx hw30 hm hodd hparent hchild.modulus hchild.inverse
    hargs.1 (hargs.2.1.trans has.length) (arguments_source hframe hk hz has.source) ha1 haw
    hargs.2.2.1 (hargs.2.2.2.1.trans hbs.length) (arguments_source hframe hk hz hbs.source) hb1 hbw
    (arguments_source hframe hk hz he) (arguments_source hframe hk hz hf) hlen hL0 hL' hq

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem readyJoint_ok (M : Mont) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (hm : 1 < L.modulus) (hodd : L.modulus % 2 = 1)
    (a b : Operand) {ba bb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ ModulusSide.p.words L)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ ModulusSide.p.words L)
    {eb fb : List Byte}
    (he : OperandBytes s L.base activeBytes (Core.scalar u) eb)
    (hf : OperandBytes s L.base activeBytes (Core.scalar v) fb)
    (hel : eb.length = L.qLen) (hfl : fb.length = L.qLen)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + ModulusSide.p.length L ≤ usedBytes) :
    WP isa (Core.joint M.mm ModulusSide.p.offset a b ⟨.local d, ModulusSide.p.lengthField⟩) s
      (CallResult L .p d (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE eb) L.modulus *
        Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE fb) L.modulus % L.modulus) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := ModulusSide.p.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 16
    have : usedBytes < 2 ^ 16 := by decide
    omega_using [hend, this]
  refine WP.mono (coreJoint_ok M h.parent (h.child .p) (by decide) hlo hhi ho (by decide)
    hw2 hw48 hw48 (by decide) hm hodd a b ⟨.local d, ModulusSide.p.lengthField⟩ ha hb hdp
    has hbs ha1 haw hb1 hbw he.source hf.source (hel.trans hfl.symm).symm
    (by rw [hel]; exact L.widths.1) (by rw [hel]; have := L.widths; omega_using [this])
    (by simpa only [hel, ModulusSide.length, ModulusSide.lengthField] using h.length .q) (h.length .p) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall .p hp hc hf hk hd hend, hv, hf, hk⟩


end VG.Proof.Dsa.AArch64

end

end

/-! # Correctness of the complete DSA verification core -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure VerifyValues where
  generator : List Byte
  publicValue : List Byte
  signatureR : List Byte
  signatureS : List Byte
  digest : List Byte

def VerifyValues.value (L : ExecutionLayout) (data : VerifyValues) : Nat :=
  let ki := Spec.Dsa.powMod (Spec.Dsa.decodeBE data.signatureS) (L.subgroup - 2) L.subgroup
  let uu := (Spec.Dsa.decodeBE data.digest % L.subgroup) * ki % L.subgroup
  let vv := Spec.Dsa.decodeBE data.signatureR * ki % L.subgroup
  (Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) uu L.modulus *
    Spec.Dsa.powMod (Spec.Dsa.decodeBE data.publicValue) vv L.modulus % L.modulus) % L.subgroup

/-- All verification arithmetic runs for every signature; the entry point
combines the final equality with its accumulated validity mask. -/
theorem coreVerify_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : VerifyValues)
    (hg : OperandBytes s0 L.base usedBytes Core.generator data.generator)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue data.publicValue)
    (hr : OperandBytes s0 L.base usedBytes Core.signatureR data.signatureR)
    (hs : OperandBytes s0 L.base usedBytes Core.signatureS data.signatureS)
    (hz : OperandBytes s0 L.base usedBytes Core.digest data.digest)
    (hgl : data.generator.length = L.pLen) (hyl : data.publicValue.length = L.pLen)
    (hrl : data.signatureR.length = L.qLen) (hsl : data.signatureS.length = L.qLen)
    (hzl : data.digest.length < 2 ^ 64)
    (hqm : OperandBytes s0 L.base activeBytes (Core.scalar qMinusTwo) (Spec.Dsa.encodeBE L.qLen (L.subgroup - 2))) :
    WP isa (Core.verify M.mm) s0 fun s8 =>
      Ready L s8 ∧
      Spec.Rsa.bytesAt s8.mem (off L.base u) L.qLen = Spec.Dsa.encodeBE L.qLen (data.value L) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s8.mem ∧
      word s8.mem L.base Field.mask.offset = word s0.mem L.base Field.mask.offset ∧ Keep coreRegs s0 s8 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  have fitq (n : Nat) (h : n < L.subgroup) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.qLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hqf)
  have fitp (n : Nat) (h : n < L.modulus) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.pLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hpf)
  let ki := Spec.Dsa.powMod (Spec.Dsa.decodeBE data.signatureS) (L.subgroup - 2) L.subgroup
  let zz := Spec.Dsa.decodeBE data.digest % L.subgroup
  let uu := zz * ki % L.subgroup
  let vv := Spec.Dsa.decodeBE data.signatureR * ki % L.subgroup
  let tt := Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) uu L.modulus
  let tt2 := Spec.Dsa.powMod (Spec.Dsa.decodeBE data.publicValue) vv L.modulus
  let prod := tt * tt2 % L.modulus
  obtain hki : ki < L.subgroup := VG.Proof.Dsa.powMod_lt _ _ (by omega_arith)
  obtain hzz : zz < L.subgroup := Nat.mod_lt _ (by omega_arith)
  obtain huu : uu < L.subgroup := Nat.mod_lt _ (by omega_arith)
  obtain hvv : vv < L.subgroup := Nat.mod_lt _ (by omega_arith)
  obtain hprod : prod < L.modulus := Nat.mod_lt _ (by omega_arith)
  obtain ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega_arith
  obtain hi : inverse + L.qLen ≤ usedBytes := by unfold inverse usedBytes; omega_arith
  obtain hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega_arith
  obtain hz' : z + L.qLen ≤ usedBytes := by unfold z usedBytes; omega_arith
  obtain hv : v + L.qLen ≤ usedBytes := by unfold v usedBytes; omega_arith
  obtain hqmLen := encodeBE_length L.qLen (L.subgroup - 2)
  unfold Core.verify
  obtain step1 := readyPow_ok M h0 .q (by change 1 < L.subgroup; omega_arith) hoq
    Core.signatureS (Core.scalar qMinusTwo) (by trivial) (by change qMinusTwo < 2 ^ 16; decide)
    hs.active hqm (by rw [hsl]; omega_arith)
    (by simp only [hsl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hqmLen]; omega_arith) (by rw [hqmLen]; omega_arith) inverse (by decide) hi
  obtain step1' : WP isa (Core.pow M.mm qWorkspace Core.signatureS (Core.scalar qMinusTwo) (Core.scalar inverse)) s0
      (CallResult L .q inverse ki s0) := by
    simpa only [ki, Core.scalar, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value,
      fitq (L.subgroup - 2) (by omega_arith)] using step1
  refine WP.seq (WP.mono step1' fun s1 h1 => ?_)
  obtain hg1 := h1.external (by decide) hi hg
  obtain hy1 := h1.external (by decide) hi hy
  obtain hr1 := h1.external (by decide) hi hr
  obtain hz1 := h1.external (by decide) hi hz
  refine WP.seq (WP.mono (readyReduce_ok M h1.ready hq hoq Core.digest (by trivial) hz1.active hzl z (by decide) hz') fun s2 h2 => ?_)
  obtain hg2 := h2.external (by decide) hz' hg1
  obtain hy2 := h2.external (by decide) hz' hy1
  obtain hr2 := h2.external (by decide) hz' hr1
  obtain hi2 := h2.local (by decide) hz' (h1.output (by decide) hi)
    (by simp only [encodeBE_length, ModulusSide.length]; exact hi)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold inverse z; omega_arith))
  obtain step3 := readyProduct_ok M h2.ready .q (by change 1 < L.subgroup; omega_arith) hoq
    (Core.scalar z) (Core.scalar inverse) (by change z < 2 ^ 16; decide) (by change inverse < 2 ^ 16; decide)
    (h2.output (by decide) hz') hi2
    (by simp only [encodeBE_length, ModulusSide.length]; omega_arith)
    (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _)
    (by simp only [encodeBE_length, ModulusSide.length]; omega_arith)
    (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _) u (by decide) hu
  obtain step3' : WP isa (Core.product M.mm qWorkspace (Core.scalar z) (Core.scalar inverse) (Core.scalar u)) s2
      (CallResult L .q u uu s2) := by
    simpa only [Core.scalar, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.length, ModulusSide.value,
      show Spec.Dsa.decodeBE data.digest % L.subgroup = zz from rfl, fitq _ hzz, fitq _ hki, uu] using step3
  refine WP.seq (WP.mono step3' fun s3 h3 => ?_)
  obtain hg3 := h3.external (by decide) hu hg2
  obtain hy3 := h3.external (by decide) hu hy2
  obtain hr3 := h3.external (by decide) hu hr2
  obtain hi3 := h3.local (by decide) hu hi2
    (by simp only [encodeBE_length, ModulusSide.length]; exact hi)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold inverse u; omega_arith))
  obtain step4 := readyProduct_ok M h3.ready .q (by change 1 < L.subgroup; omega_arith) hoq
    Core.signatureR (Core.scalar inverse) (by trivial) (by change inverse < 2 ^ 16; decide) hr3.active hi3
    (by rw [hrl]; omega_arith) (by simp only [hrl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by simp only [encodeBE_length, ModulusSide.length]; omega_arith)
    (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _) v (by decide) hv
  obtain step4' : WP isa (Core.product M.mm qWorkspace Core.signatureR (Core.scalar inverse) (Core.scalar v)) s3
      (CallResult L .q v vv s3) := by
    simpa only [Core.scalar, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.length, ModulusSide.value,
      fitq _ hki, vv] using step4
  refine WP.seq (WP.mono step4' fun s4 h4 => ?_)
  obtain hg4 := h4.external (by decide) hv hg3
  obtain hy4 := h4.external (by decide) hv hy3
  obtain hu4 := h4.local (by decide) hv (h3.output (by decide) hu)
    (by simp only [encodeBE_length, ModulusSide.length]; exact hu)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold u v; omega_arith))
  obtain step5 := readyJoint_ok M h4.ready hp hop Core.generator Core.publicValue
    (by trivial) (by trivial) hg4.active hy4.active
    (by rw [hgl]; omega_arith) (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hyl]; omega_arith) (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    hu4 (h4.output (by decide) hv) (encodeBE_length _ _) (encodeBE_length _ _) t (by decide) ht
  obtain step5' : WP isa (Core.joint M.mm pWorkspace Core.generator Core.publicValue (Core.element t)) s4
      (CallResult L .p t prod s4) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.length, ModulusSide.value,
      fitq _ huu, fitq _ hvv, prod, tt, tt2] using step5
  refine WP.seq (WP.mono step5' fun s7 h7 => ?_)
  obtain step8 := readyReduce_ok M h7.ready hq hoq (Core.element t) (by change t < 2 ^ 16; decide)
    (h7.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega_arith) u (by decide) hu
  obtain step8' : WP isa (Core.reduce M.mm (Core.element t) (Core.scalar u)) s7
      (CallResult L .q u (data.value L) s7) := by
    simpa only [ModulusSide.length, fitp _ hprod, prod, tt, tt2, uu, vv, zz, ki, VerifyValues.value] using step8
  refine WP.mono step8' fun s8 h8 => ⟨h8.ready, h8.bytes, ?_, ?_, ?_⟩
  · exact (((((h1.scheduleFrame (by decide) hi).trans (h2.scheduleFrame (by decide) hz')).trans
      (h3.scheduleFrame (by decide) hu)).trans (h4.scheduleFrame (by decide) hv)).trans
      (h7.scheduleFrame (by decide) ht)).trans (h8.scheduleFrame (by decide) hu)
  · exact (h8.fields (by decide) hu .mask).trans ((h7.fields (by decide) ht .mask).trans
      ((h4.fields (by decide) hv .mask).trans ((h3.fields (by decide) hu .mask).trans
      ((h2.fields (by decide) hz' .mask).trans (h1.fields (by decide) hi .mask)))))
  · have k1 := h1.keep
    obtain k2 : Keep coreRegs s0 s2 := (k1.trans h2.keep).mono (by decide)
    obtain k3 : Keep coreRegs s0 s3 := (k2.trans h3.keep).mono (by decide)
    obtain k4 : Keep coreRegs s0 s4 := (k3.trans h4.keep).mono (by decide)
    obtain k7 : Keep coreRegs s0 s7 := (k4.trans h7.keep).mono (by decide)
    exact (k7.trans h8.keep).mono (by decide)

end VG.Proof.Dsa.AArch64
