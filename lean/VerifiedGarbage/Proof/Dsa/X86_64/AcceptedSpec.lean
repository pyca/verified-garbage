module

import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
public import VerifiedGarbage.Proof.Dsa.X86_64.CoreSign
public import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
import VerifiedGarbage.Proof.Dsa.X86_64.PublicCalls
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCalls
import VerifiedGarbage.Proof.Dsa.X86_64.Call
public import VerifiedGarbage.Impl.Dsa.X86_64.Joint
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Spec.Dsa
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Dsa.X86_64.JointBuildContext
public import VerifiedGarbage.Proof.Dsa.X86_64.JointWindow
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Dsa.Joint
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
public import VerifiedGarbage.Proof.Dsa.X86_64.JointAdvance
import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice

/-! ### `Dsa.X86_64.VerifyCompute`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.ReadyJoint`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.JointPower`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.JointPrepare`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.JointEntries`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.JointStore`, which this module and modules that import it used -/

section

/-! # Writing one entry of the joint exponentiation table -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
  have cv := hc.exp.of_frm fexp hk.2.2 (hk.gpr (by decide))
  have ve : word v.mem P (8 * Crt.sEnt) = off P (slot w (8 + j)) :=
    (hf.word (Or.inl (by have := hdr_lt_slot w 8 (show Crt.sEnt < 32 by decide); omega_using [helo, this])) (by decide)).trans he
  refine WP.mono (nextEnt_ok cv ve) fun u ⟨hm, ku⟩ => ?_
  have ho := writeW_outside v.mem P (d := 8 * Crt.sEnt) (off P (slot w (8 + j) + 8 * (w + 2))) (by decide)
  rw [← hm] at ho
  have ff : Frm P (crtExpRanges w) v.mem u.mem := Frm.of_outside ho (by simp [crtExpRanges, crtWinRanges])
  have cu := cv.of_frm ff ku.2.2 (ku.gpr (by decide))
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

end VG.Proof.Dsa.X86_64

end

end

/-! # Construction of all sixteen joint exponentiation table entries -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.JointEncode`, which this module and modules that import it used -/

section

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

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.JointBuild`, which this module and modules that import it used -/

section

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
  have hsmall : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
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
    rw [o2.wv (Or.inr (hdr_lt_slot w a (by decide))) (by omega_using [hnow, hab]),
      o1.wv (Or.inr (hdr_lt_slot w a (by decide))) (by omega_using [hnow, hab])]
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
  refine WP.mono (one_ok hc'.mod.good (Nat.le_refl _) hw (by omega_using [hw']) (by decide))
    fun u ⟨hu, hone, hfu, hku⟩ => ?_
  have uc : JointCtx u P w n minv := ⟨⟨hu,
    (hfu.wv_of_not_mem (by decide) (by decide) hc'.mod.good.scr.nowrap).trans hc'.mod.modulus,
    by rw [hfu.word0_of_not_mem (by decide) (by decide) hc'.mod.good.scr.nowrap (by omega_using [hw])]; exact hc'.mod.inverse⟩,
    hc'.scrT.congr hku.2.2⟩
  refine ⟨uc, st'.of_arrays hfu (by decide) hc'.scrT.nowrap,
    (hfu.wv_of_not_mem (by decide) (by decide) hc'.mod.good.scr.nowrap).trans sy, hone,
    ((exp_work hf).trans hs.frm).trans ((arrays_work hf' (by decide)).trans (arrays_work hfu (by decide))),
    (((hk.trans hs.keep).trans hk').trans hku).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Loading and preparing both bases for joint DSA exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
  exact ⟨hsub4.of_frmT hft (workRanges_ok wx) hkt.2.2 (hkt.gpr (by decide)),
    hct, ht, hyt, hot, (((hf12.trans hf3).trans (arrays_work hf4 (by decide))).trans hft),
    ((((hk12.trans hk3).trans hk4).trans hkt).mono (by decide))⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.JointRun`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.JointByte`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.JointWindows`, which this module and modules that import it used -/

section

/-! # Four joint windows consume two exponent bytes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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

theorem jointWinStep_ok (M : Mont) (Sq : MontS) {t s : State} {P : Addr} {w n xc g y E F v z j : Nat}
    {minv : BitVec 64} (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hv : v < 256) (hz : z < 256) (hj : j < 4)
    (h : JointWinInv t P w minv n xc g y E F v z j s) :
    WP isa (Joint.window Sq.mm M.mm) s fun s' => s'.zf = some (decide (j + 1 = 4)) ∧
      JointWinInv t P w minv n xc g y E F v z (j + 1) s' := by
  have hp : 4 ^ j ≤ 64 := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega_using [hj]) with rfl | rfl | rfl | rfl <;> decide
  refine WP.mono (jointWindow_ok M Sq h.ctx h.tab hw hw' hR h.ylt h.val h.bytes
    (by have := Nat.mul_le_mul_left (256 * v + z) hp; omega_using [hv, hz, this]) h.count (by omega_using [hj]) (by omega_using []))
    fun s' ⟨hc, ht, hy, hval, hb, hn, hz', hf, hk⟩ => ⟨?_, hc, ht, hy, ?_, ?_, ?_,
      h.frm.trans hf, (h.keep.trans hk).mono (by decide)⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega_using [hj])
  · rw [hval, (VG.Proof.Dsa.joint_byte_step hv hz hj E F).1,
      (VG.Proof.Dsa.joint_byte_step hv hz hj E F).2]
  · rw [hb, Nat.pow_succ]; congr 1; ac_rfl
  · rw [hn]; congr 1

theorem jointWins_ok (M : Mont) (Sq : MontS) {t : State} {P : Addr} {w n xc g y E F v z : Nat}
    {minv : BitVec 64} (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hv : v < 256) (hz : z < 256) (h : JointWinInv t P w minv n xc g y E F v z 0 t) :
    WP isa (.loop (Joint.window Sq.mm M.mm) .ne) t (JointWinInv t P w minv n xc g y E F v z 4) :=
  wp_upto (a := 0) (N := 4) (by decide) (JointWinInv t P w minv n xc g y E F v z)
    (fun _ _ hj _ hI => jointWinStep_ok M Sq hw hw' hR hv hz hj hI) (fun _ h => h) h

end VG.Proof.Dsa.X86_64

end

end

/-! # Loading a pair of exponent bytes without secret-dependent addresses -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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

theorem joint_pack (v z : Byte) :
    z.setWidth 64 + (v.setWidth 64 <<< 8) = BitVec.ofNat 64 (256 * v.toNat + z.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.reducePow]
  have hv := v.isLt
  have hz := z.isLt
  omega_arith

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
        (off P (8 * Crt.sBit)) (4 : BitVec 64) ∧ Keep [.rax, .rcx, .rdx, .rsi] t u := by
  unfold Joint.byteHead Joint.bytePointers Joint.byteValues
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .rsi] (Q := fun u =>
    u.mem = (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (256 * v.toNat + z.toNat))).writeW
      (off P (8 * Crt.sBit)) (4 : BitVec 64)) ?_ rfl) fun u ⟨h, k⟩ => ⟨h, k⟩
  xrun [List.cons_append, List.nil_append, State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sI) (by decide),
    hc.ld (i := Crt.sExp) (by decide), hc.ld (i := Joint.sExp2) (by decide),
    hc.st (i := Crt.sV) (by decide), hc.st (i := Crt.sBit) (by decide),
    hi, he, hf, byteRead, hrE, hrF, hv, hz, joint_pack]
  rfl

/-- Read one byte from each exponent, run four joint windows, and advance. -/
theorem jointByte_ok (M : Mont) (Sq : MontS) {t₀ t : State} {P : Addr} {w n xc g y : Nat}
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
    WP isa (seqs [.block Joint.byteHead, .loop (Joint.window Sq.mm M.mm) .ne,
      .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
        .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]) t fun t' =>
      t'.zf = some (decide (i + 1 = L)) ∧ JointByteInv t₀ P w minv n xc g y ep fp L eb fb (i + 1) t' := by
  have hn := hI.ctx.scrT.nowrap
  let v := (eb[i]'(by omega_arith)).toNat
  let z := (fb[i]'(by omega_arith)).toNat
  obtain hv : v < 256 := (eb[i]'(by omega_arith)).isLt
  obtain hz : z < 256 := (fb[i]'(by omega_arith)).isLt
  obtain er : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd i hi
  obtain fr : InRegions (t.rd ++ t.wr) (fp + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact frd i hi
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
    (d := 8 * Crt.sBit) (4 : BitVec 64) (by decide)
  rw [← hm₁] at o2
  obtain f₁ : Frm P (crtWinRanges w) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [crtWinRanges])).trans (Frm.of_outside o2 (by simp [crtWinRanges]))
  obtain hc₁ := hI.ctx.of_win f₁ k₁.2.2 (k₁.gpr (by decide))
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
    · rw [hm₁, word_writeW_self]; rfl
  refine WP.seq (WP.mono (jointWins_ok M Sq hw hw' hR hv hz hB0) fun t₂ h₂ => ?_)
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
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₂.mem.writeW (off P (8 * Crt.sI))
      (BitVec.ofNat 64 (i + 1)) ∧ t'.zf = some (decide (i + 1 = L))) (by
    xrun [State.ea, hdr, hc₂.good.rdi, hdrOff, hc₂.ld (i := Crt.sI) (by decide), hc₂.st (i := Crt.sI) (by decide),
      hidx₂, ofNat_add_one, hc₂.ld (i := Crt.sExpLen) (by decide), hlen₂',
      ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega_arith) (show L < 2 ^ 64 by omega_arith)]) rfl)
    fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨hz', ?_⟩
  obtain o' := writeW_outside t₂.mem P (d := 8 * Crt.sI) (BitVec.ofNat 64 (i + 1)) (by decide)
  rw [← hm'] at o'
  obtain f' : Frm P (crtExpRanges w) t₂.mem t'.mem := Frm.of_outside o' (by simp [crtExpRanges])
  obtain hY0 := slot_le (w := w) (show aY < 8 by decide)
  obtain hYe : wv t'.mem P (slot w aY) w = wv t₂.mem P (slot w aY) w :=
    o'.wv (by have := hdr_lt_slot w aY (show Crt.sI < 32 by decide); omega_arith) (by omega_arith)
  refine ⟨hc₂.of_frm f' k'.2.2 (k'.gpr (by decide)), ?_, hYe ▸ h₂.ylt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- Both equal-length exponent strings are scanned sequentially. -/
theorem jointBytes_ok (M : Mont) (Sq : MontS) {t : State} {P : Addr} {w n xc g y : Nat}
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
    WP isa (Joint.bytes Sq.mm M.mm) t (JointByteInv t P w minv n xc g y ep fp L eb fb L) :=
  wp_upto (a := 0) (N := L) hL0 (JointByteInv t P w minv n xc g y ep fp L eb fb)
    (fun _ _ hi _ hI => jointByte_ok M Sq hw hw' hR hL hF hL' hi hrd hbytes hout frd fbytes fout hI)
    (fun _ h => h) h

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.JointInit`, which this module and modules that import it used -/

section

/-! # Public exponent pointers for joint DSA verification -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def jointInitRanges : List (Nat × Nat) :=
  [(8 * Crt.sExp, 8), (8 * Joint.sExp2, 8), (8 * Crt.sExpLen, 8), (8 * Crt.sI, 8)]

theorem jointInit_ranges (w : Nat) : ∀ r ∈ jointInitRanges,
    136 ≤ r.1 ∧ r.1 + r.2 ≤ 256 ∧ r.1 + r.2 ≤ slot w 8 + tabBytes w := by
  have h : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  simp only [jointInitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [Crt.sExp, Joint.sExp2, Crt.sRem, Crt.sExpLen, Crt.sI, sFn] <;> omega_using [h]

theorem jointInit_raw {s : State} {B : Addr} {Z o w wx L : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hfield : 344 ≤ Z)
    (hl : word s.mem B Field.qLen.offset = BitVec.ofNat 64 L) :
    WP isa (.block Joint.expInit) s fun t =>
      t.mem = (((s.mem.writeW (off (off B o) (8 * Crt.sExp)) (off B u)).writeW
        (off (off B o) (8 * Joint.sExp2)) (off B v)).writeW
        (off (off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 L)).writeW
        (off (off B o) (8 * Crt.sI)) (BitVec.setWidth 64 (0 : BitVec 32)) ∧
      Keep [.rax, .rcx, .rdx] s t := by
  have hrd : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi =>
    hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi; omega_using [this])
  have hwr : ∀ i < 32, InRegions s.wr (off (off B o) (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot wx 8 hi; omega_using [this])
  have hparent : InRegions (s.rd ++ s.wr) (B + BitVec.ofInt 64 (Field.qLen.offset : Int)) 8 :=
    hc.scr.ld hfield
  have hval : s.mem.readW (B + BitVec.ofInt 64 (Field.qLen.offset : Int)) 64 = BitVec.ofNat 64 L := hl
  unfold Joint.expInit
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t =>
    t.mem = (((s.mem.writeW (off (off B o) (8 * Crt.sExp)) (off B u)).writeW
      (off (off B o) (8 * Joint.sExp2)) (off B v)).writeW
      (off (off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 L)).writeW
      (off (off B o) (8 * Crt.sI)) (BitVec.setWidth 64 (0 : BitVec 32))) ?_ rfl)
    fun t ⟨hm, hk⟩ => ⟨hm, hk⟩
  xrun [State.ea, hdr, hc.rdi, hdrOff, hrd Crt.sLink (by decide), hc.link,
    hparent, hval,
    hwr Crt.sExp (by decide), hwr Joint.sExp2 (by decide),
    hwr Crt.sExpLen (by decide), hwr Crt.sI (by decide)]
  rfl

theorem jointInit_frame {s t : State} {B : Addr} {o L : Nat}
    (hm : t.mem = (((s.mem.writeW (off (off B o) (8 * Crt.sExp)) (off B u)).writeW
      (off (off B o) (8 * Joint.sExp2)) (off B v)).writeW
      (off (off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 L)).writeW
      (off (off B o) (8 * Crt.sI)) (BitVec.setWidth 64 (0 : BitVec 32))) :
    Frm (off B o) jointInitRanges s.mem t.mem := by
  rw [hm]
  exact (((Frm.of_outside (writeW_outside _ (off B o) _ (d := 8 * Crt.sExp) (by decide))
    (by simp [jointInitRanges])).trans
    (Frm.of_outside (writeW_outside _ (off B o) _ (d := 8 * Joint.sExp2) (by decide))
      (by simp [jointInitRanges]))).trans
    (Frm.of_outside (writeW_outside _ (off B o) _ (d := 8 * Crt.sExpLen) (by decide))
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
  have hct := hc.of_frmT hf (fun r h => ⟨(hr r h).1, (hr r h).2.2⟩) hk.2.2 (hk.gpr (by decide))
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
  · rw [hm]
    simp (disch := decide) only [hdrStore_hdr, word_writeW_self]
  · rw [hm]
    simp (disch := decide) only [hdrStore_hdr, word_writeW_self]
  · rw [hm]
    simp (disch := decide) only [hdrStore_hdr, word_writeW_self]
  · rw [hm, word_writeW_self]; rfl
  · intro x hx
    apply hf x
    intro r h
    have := hr r h
    have := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
    have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
    omega_arith

end VG.Proof.Dsa.X86_64

end

end

/-! # Joint exponentiation and conversion out of Montgomery representation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem joint_source_out {s : State} {B p : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) {bs : List Byte} (hs : Src s B Z p bs) :
    ∀ i < bs.length, slot wx 8 + tabBytes wx ≤ ofs (off B o) (p + BitVec.ofNat 64 i) := by
  intro i hi
  have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have := hc.hi
  have := hc.scr.nowrap
  have := hs.out i hi
  rcases ofs_rebase B (p + BitVec.ofNat 64 i) (o := o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩ <;> omega_arith

theorem jointRun_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx n g y : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hmctx : JointCtx s (off B o) wx n minv)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hn : 1 < n) (hodd : n % 2 = 1)
    (htab : JointTab s.mem (off B o) wx n g y)
    (hy : wv s.mem (off B o) (slot wx aY) wx = 2 ^ (64 * wx) % n)
    (hone : wv s.mem (off B o) (slot wx aOne) wx = 1)
    {eb fb : List Byte} (he : Src s B Z (off B u) eb) (hf : Src s B Z (off B v) fb)
    (hlen : fb.length = eb.length) (hL0 : 0 < eb.length) (hL' : eb.length < 2 ^ 31)
    (hfield : 344 ≤ Z) (hl : word s.mem B Field.qLen.offset = BitVec.ofNat 64 eb.length) :
    WP isa (Joint.run Sq.mm M.mm) s fun t =>
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
  refine WP.seq (WP.mono (jointBytes_ok M Sq hw hw' hR rfl hlen hL0 hL'
    hsrc1.rd hsrc1.val (joint_source_out hc1 hsrc1)
    (by simpa only [hlen] using fsrc1.rd) (by simpa only [hlen] using fsrc1.val)
    (by simpa only [hlen] using joint_source_out hc1 fsrc1) hI) fun s2 h2 => ?_)
  have hc2 := hc1.of_frmT h2.frm (crtExpRanges_ok wx) h2.keep.2.2 (h2.keep.gpr (by decide))
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

end VG.Proof.Dsa.X86_64

end

end

/-! # Loading and preparing both bases for joint DSA exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem jointPower_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m : Nat}
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
    WP isa (Joint.power Sq.mm M.mm) s fun t =>
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
  refine WP.mono (jointRun_ok M Sq hc1 hm1 hw2 (by omega_using [hw48]) hm hodd ht1 hy1 ho1
    (work_source hc hf1 hk1 he) (work_source hc hf1 hk1 hf) hlen hL0 hL' (by omega_using [hparent, hhi]) hlen1)
    fun t ⟨hct, hmt, hv, hft, hkt⟩ => ⟨hct, hmt, ?_, hf1.trans hft, (hk1.trans hkt).mono (by decide)⟩
  simpa only [VG.Proof.Dsa.powMod_eq, Nat.mul_mod_mod, Nat.mod_mul_mod] using hv

end VG.Proof.Dsa.X86_64

end

end

/-! # Joint exponentiation preserving the DSA execution context -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/CoreJoint.lean`, which only this module imported.
section

/-! # Joint exponentiation in the DSA parent workspace -/

section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem coreJoint_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31) (hparent : 344 ≤ o)
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
    WP isa (Core.joint Sq.mm M.mm o a b output) s fun t =>
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
  exact jointPower_ok M Sq hc hw2 hw48 hwx hw30 hm hodd hparent hchild.modulus hchild.inverse
    hargs.1 (hargs.2.1.trans has.length) (arguments_source hframe hk hz has.source) ha1 haw
    hargs.2.2.1 (hargs.2.2.2.1.trans hbs.length) (arguments_source hframe hk hz hbs.source) hb1 hbw
    (arguments_source hframe hk hz he) (arguments_source hframe hk hz hf) hlen hL0 hL' hq

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem readyJoint_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s : State} (h : Ready L s)
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
    WP isa (Core.joint Sq.mm M.mm ModulusSide.p.offset a b ⟨.local d, ModulusSide.p.lengthField⟩) s
      (CallResult L .p d (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE eb) L.modulus *
        Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE fb) L.modulus % L.modulus) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := ModulusSide.p.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega_using [hend, this]
  refine WP.mono (coreJoint_ok M Sq h.parent (h.child .p) (by decide) hlo hhi ho (by decide)
    hw2 hw48 hw48 (by decide) hm hodd a b ⟨.local d, ModulusSide.p.lengthField⟩ ha hb hdp
    has hbs ha1 haw hb1 hbw he.source hf.source (hel.trans hfl.symm).symm
    (by rw [hel]; exact L.widths.1) (by rw [hel]; have := L.widths; omega_using [this])
    (by simpa only [hel, ModulusSide.length, ModulusSide.lengthField] using h.length .q) (h.length .p) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall .p hp hc hf hk hd hend, hv, hf, hk⟩


end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.PublicKey`, which this module and modules that import it used -/

section

/-! # Algebraic domain and public-key validation for DSA -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def publicAccepted (L : ExecutionLayout) (gb yb : List Byte) (valid : Bool) : Bool :=
  decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE yb) L.subgroup L.modulus = 1) &&
  (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) L.subgroup L.modulus = 1) &&
  (decide ((L.modulus - 1) % L.subgroup = 0) &&
  (decide (1 < Spec.Dsa.decodeBE yb ∧ Spec.Dsa.decodeBE yb < L.modulus) &&
  (decide (1 < Spec.Dsa.decodeBE gb ∧ Spec.Dsa.decodeBE gb < L.modulus) && valid))))

theorem publicKey_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb yb qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator gb)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hgl : gb.length = L.pLen) (hyl : yb.length = L.pLen) (hqlen : qb.length = L.qLen)
    (hqval : Spec.Dsa.decodeBE qb = L.subgroup)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.publicKey Sq.mm M.mm) s0 fun s10 =>
      Ready L s10 ∧ word s10.mem L.base Field.mask.offset = mask (publicAccepted L gb yb valid) ∧
      OperandBytes s10 L.base activeBytes (Core.scalar qMinusTwo) (Spec.Dsa.encodeBE L.qLen (L.subgroup - 2)) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s10.mem ∧ Keep coreRegs s0 s10 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  have fitq (n : Nat) (h : n < L.subgroup) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.qLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hqf)
  have fitp (n : Nat) (h : n < L.modulus) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.pLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hpf)
  obtain ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega_using [hpu]
  obtain hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega_using [hqu]
  obtain hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega_using [hqu]
  unfold Checks.publicKey Checks.publicPrefix
  refine WP.seq (WP.mono (readyRange_ok h0 .p Core.generator (by trivial) hg.active
    (by rw [hgl]; omega_using [hql, hqp]) (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true hm) fun s1 h1 => ?_)
  obtain hg1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg
  obtain hy1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy
  obtain hq1 := h1.preserve h0 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb
  refine WP.seq (WP.mono (readyRange_ok h1.ready .p Core.publicValue (by trivial) hy1.active
    (by rw [hyl]; omega_using [hql, hqp]) (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true h1.mask) fun s2 h2 => ?_)
  obtain hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  obtain hy2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy1
  obtain hq2 := h2.preserve h1.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq1
  refine WP.seq (WP.mono (readyMinus_ok h2.ready .p 1 (by decide) (by change 1 ≤ L.modulus; omega_using [hp])
    t (by decide) ht) fun s3 h3 => ?_)
  obtain hg3 := h3.external (by decide) ht hg2
  obtain hy3 := h3.external (by decide) ht hy2
  obtain hq3 := h3.external (by decide) ht hq2
  obtain hm3 := (h3.fields (by decide) ht .mask).trans h2.mask
  obtain step4 := readyReduce_ok M h3.ready hq hoq (Core.element t) (by change t < 2 ^ 31; decide)
    (h3.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hpu]) u (by decide) hu
  obtain step4' : WP isa (Core.reduce M.mm (Core.element t) (Core.scalar u)) s3
      (CallResult L .q u ((L.modulus - 1) % L.subgroup) s3) := by
    simpa only [ModulusSide.length, ModulusSide.value, fitp (L.modulus - 1) (by omega_using [hp])] using step4
  refine WP.seq (WP.mono step4' fun s4 h4 => ?_)
  obtain hg4 := h4.external (by decide) hu hg3
  obtain hy4 := h4.external (by decide) hu hy3
  obtain hq4 := h4.external (by decide) hu hq3
  obtain hm4 := (h4.fields (by decide) hu .mask).trans hm3
  refine WP.seq (WP.mono (readyZero_ok h4.ready (Core.scalar u) (by change u < 2 ^ 31; decide)
    (h4.output (by decide) hu) (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hqu]) false hm4) fun s5 h5 => ?_)
  obtain hziff : (∀ b ∈ Spec.Dsa.encodeBE L.qLen ((L.modulus - 1) % L.subgroup), b = 0) ↔
      (L.modulus - 1) % L.subgroup = 0 := by
    rw [← VG.Proof.Dsa.decodeBE_eq_zero, fitq _ (Nat.mod_lt _ (by omega_using [hq]))]
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length] at hm5
  simp only [hziff] at hm5
  obtain hg5 := h5.preserve h4.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg4
  obtain hy5 := h5.preserve h4.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy4
  obtain hq5 := h5.preserve h4.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq4
  refine WP.seq (WP.mono (readyMinus_ok h5.ready .q 2 (by decide) (by change 2 ≤ L.subgroup; omega_using [hq])
    qMinusTwo (by decide) hqm) fun s6 h6 => ?_)
  obtain hg6 := h6.external (by decide) hqm hg5
  obtain hy6 := h6.external (by decide) hqm hy5
  obtain hq6 := h6.external (by decide) hqm hq5
  obtain hm6 := (h6.fields (by decide) hqm .mask).trans hm5
  obtain step7 := readyPublicPow_ok M Sq h6.ready .p hp hop Core.generator ⟨.input .q, .qLen⟩ (by trivial) (by trivial)
    hg6.active hq6.active (by rw [hgl]; omega_using [hql, hqp])
    (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hqlen]; omega_using [hql]) (by rw [hqlen]; omega_using [hqu]) t (by decide) ht
  obtain step7' : WP isa (Core.publicPow Sq.mm M.mm pWorkspace Core.generator ⟨.input .q, .qLen⟩ (Core.element t)) s6
      (CallResult L .p t (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) L.subgroup L.modulus) s6) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value, hqval] using step7
  refine WP.seq (WP.mono step7' fun s7 h7 => ?_)
  obtain hy7 := h7.external (by decide) ht hy6
  obtain hq7 := h7.external (by decide) ht hq6
  obtain hqm7 := h7.local (by decide) ht (h6.output (by decide) hqm)
    (by simp only [encodeBE_length, ModulusSide.length]; exact hqm)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold qMinusTwo t; omega_using [hqu]))
  obtain hm7 := (h7.fields (by decide) ht .mask).trans hm6
  refine WP.seq (WP.mono (readyIsOne_ok h7.ready .p (Core.element t) (by change t < 2 ^ 31; decide)
    (h7.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql, hqp])
    (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _) hm7) fun s8 h8 => ?_)
  have hm8 := h8.mask
  simp only [ModulusSide.length, fitp _ (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hp]))] at hm8
  obtain hy8 := h8.preserve h7.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy7
  obtain hq8 := h8.preserve h7.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq7
  obtain hqm8 := h8.preserve h7.ready (Nat.le_refl _) (by decide) (by trivial) hqm7
  obtain step9 := readyPublicPow_ok M Sq h8.ready .p hp hop Core.publicValue ⟨.input .q, .qLen⟩ (by trivial) (by trivial)
    hy8.active hq8.active (by rw [hyl]; omega_using [hql, hqp])
    (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hqlen]; omega_using [hql]) (by rw [hqlen]; omega_using [hqu]) t (by decide) ht
  obtain step9' : WP isa (Core.publicPow Sq.mm M.mm pWorkspace Core.publicValue ⟨.input .q, .qLen⟩ (Core.element t)) s8
      (CallResult L .p t (Spec.Dsa.powMod (Spec.Dsa.decodeBE yb) L.subgroup L.modulus) s8) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value, hqval] using step9
  refine WP.seq (WP.mono step9' fun s9 h9 => ?_)
  obtain hqm9 := h9.local (by decide) ht hqm8
    (by simp only [encodeBE_length, ModulusSide.length]; exact hqm)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold qMinusTwo t; omega_using [hqu]))
  obtain hm9 := (h9.fields (by decide) ht .mask).trans hm8
  refine WP.mono (readyIsOne_ok h9.ready .p (Core.element t) (by change t < 2 ^ 31; decide)
    (h9.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql, hqp])
    (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _) hm9) fun s10 h10 => ?_
  obtain hqm10 := h10.preserve h9.ready (Nat.le_refl _) (by decide) (by trivial) hqm9
  refine ⟨h10.ready, ?_, hqm10, ?_, ?_⟩
  · have hm10 := h10.mask
    simp only [ModulusSide.length, ModulusSide.value,
      fitp _ (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hp]))] at hm10
    exact hm10
  · exact ((((((((h1.scheduleFrame.trans h2.scheduleFrame).trans (h3.scheduleFrame (by decide) ht)).trans (h4.scheduleFrame (by decide) hu)).trans h5.scheduleFrame).trans
      (h6.scheduleFrame (by decide) hqm)).trans (h7.scheduleFrame (by decide) ht)).trans h8.scheduleFrame).trans (h9.scheduleFrame (by decide) ht)).trans h10.scheduleFrame
  · have hk5 : Keep coreRegs s0 s5 :=
      ((((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).trans h5.keep).mono (by decide)
    obtain hk10 : Keep coreRegs s5 s10 :=
      ((((h6.keep.trans h7.keep).trans h8.keep).trans h9.keep).trans h10.keep).mono (by decide)
    exact (hk5.trans hk10).mono (by decide)

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.CoreVerify`, which this module and modules that import it used -/

section

/-! # Correctness of the complete six-operation DSA verification core -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
theorem coreVerify_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
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
    WP isa (Core.verify Sq.mm M.mm) s0 fun s8 =>
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
  obtain hki : ki < L.subgroup := VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hq])
  obtain hzz : zz < L.subgroup := Nat.mod_lt _ (by omega_using [hq])
  obtain huu : uu < L.subgroup := Nat.mod_lt _ (by omega_using [hq])
  obtain hvv : vv < L.subgroup := Nat.mod_lt _ (by omega_using [hq])
  obtain hprod : prod < L.modulus := Nat.mod_lt _ (by omega_using [hp])
  obtain ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega_using [hpu]
  obtain hi : inverse + L.qLen ≤ usedBytes := by unfold inverse usedBytes; omega_using [hqu]
  obtain hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega_using [hqu]
  obtain hz' : z + L.qLen ≤ usedBytes := by unfold z usedBytes; omega_using [hqu]
  obtain hv : v + L.qLen ≤ usedBytes := by unfold v usedBytes; omega_using [hqu]
  obtain hqmLen := encodeBE_length L.qLen (L.subgroup - 2)
  unfold Core.verify
  obtain step1 := readyPow_ok M Sq h0 .q (by change 1 < L.subgroup; omega_using [hq]) hoq
    Core.signatureS (Core.scalar qMinusTwo) (by trivial) (by change qMinusTwo < 2 ^ 31; decide)
    hs.active hqm (by rw [hsl]; omega_using [hql])
    (by simp only [hsl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hqmLen]; omega_using [hql]) (by rw [hqmLen]; omega_using [hqu]) inverse (by decide) hi
  obtain step1' : WP isa (Core.pow Sq.mm M.mm qWorkspace Core.signatureS (Core.scalar qMinusTwo) (Core.scalar inverse)) s0
      (CallResult L .q inverse ki s0) := by
    simpa only [ki, Core.scalar, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value,
      fitq (L.subgroup - 2) (by omega_using [hq])] using step1
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
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold inverse z; omega_using [hqu]))
  obtain step3 := readyProduct_ok M h2.ready .q (by change 1 < L.subgroup; omega_using [hq]) hoq
    (Core.scalar z) (Core.scalar inverse) (by change z < 2 ^ 31; decide) (by change inverse < 2 ^ 31; decide)
    (h2.output (by decide) hz') hi2
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _)
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
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
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold inverse u; omega_using [hqu]))
  obtain step4 := readyProduct_ok M h3.ready .q (by change 1 < L.subgroup; omega_using [hq]) hoq
    Core.signatureR (Core.scalar inverse) (by trivial) (by change inverse < 2 ^ 31; decide) hr3.active hi3
    (by rw [hrl]; omega_using [hql]) (by simp only [hrl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
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
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold u v; omega_using [hqu]))
  obtain step5 := readyJoint_ok M Sq h4.ready hp hop Core.generator Core.publicValue
    (by trivial) (by trivial) hg4.active hy4.active
    (by rw [hgl]; omega_using [hql, hqp]) (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hyl]; omega_using [hql, hqp]) (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    hu4 (h4.output (by decide) hv) (encodeBE_length _ _) (encodeBE_length _ _) t (by decide) ht
  obtain step5' : WP isa (Core.joint Sq.mm M.mm pWorkspace Core.generator Core.publicValue (Core.element t)) s4
      (CallResult L .p t prod s4) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.length, ModulusSide.value,
      fitq _ huu, fitq _ hvv, prod, tt, tt2] using step5
  refine WP.seq (WP.mono step5' fun s7 h7 => ?_)
  obtain step8 := readyReduce_ok M h7.ready hq hoq (Core.element t) (by change t < 2 ^ 31; decide)
    (h7.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hpu]) u (by decide) hu
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
  · exact (((((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).trans h7.keep).trans h8.keep).mono (by decide)

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.SignCompute`, which the modules that import this one used -/

section

/-! ### `Dsa.X86_64.PrivateKey`, which this module and modules that import it used -/

section

/-! # Private-key consistency and nonce-range validation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem privateKey_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hop : L.modulus % 2 = 1)
    {gb yb xb nb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator gb)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hx : OperandBytes s0 L.base usedBytes Core.privateScalar xb)
    (hn : OperandBytes s0 L.base usedBytes Core.nonce nb)
    (hgl : gb.length = L.pLen) (hyl : yb.length = L.pLen)
    (hxl : xb.length = L.qLen) (hnl : nb.length = L.qLen)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.privateKey Sq.mm M.mm) s0 fun s4 =>
      Ready L s4 ∧
      word s4.mem L.base Field.mask.offset =
        mask (decide (Spec.Dsa.encodeBE L.pLen (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE xb) L.modulus) = yb) &&
          (decide (0 < Spec.Dsa.decodeBE nb ∧ Spec.Dsa.decodeBE nb < L.subgroup) &&
          (decide (0 < Spec.Dsa.decodeBE xb ∧ Spec.Dsa.decodeBE xb < L.subgroup) && valid))) ∧
      Spec.Rsa.bytesAt s4.mem (off L.base qMinusTwo) L.qLen = Spec.Rsa.bytesAt s0.mem (off L.base qMinusTwo) L.qLen ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s4.mem ∧ Keep coreRegs s0 s4 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  obtain ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega_using [hpu]
  obtain hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega_using [hqu]
  obtain hqm0 := h0.readLocal .q qMinusTwo (by decide) hqm
  obtain hqml : (Spec.Rsa.bytesAt s0.mem (off L.base qMinusTwo) (ModulusSide.q.length L)).length = L.qLen := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, ModulusSide.length]
  unfold Checks.privateKey
  refine WP.seq (WP.mono (readyRange_ok h0 .q Core.privateScalar (by trivial) hx.active
    (by rw [hxl]; omega_using [hql]) (by simp only [hxl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm) fun s1 h1 => ?_)
  obtain hqm1 := h1.preserve h0 (Nat.le_refl _) (by decide) (by trivial) hqm0
  obtain hg1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg
  obtain hy1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy
  obtain hx1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.privateScalar]) hx
  obtain hn1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.nonce]) hn
  refine WP.seq (WP.mono (readyRange_ok h1.ready .q Core.nonce (by trivial) hn1.active
    (by rw [hnl]; omega_using [hql]) (by simp only [hnl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false h1.mask) fun s2 h2 => ?_)
  obtain hqm2 := h2.preserve h1.ready (Nat.le_refl _) (by decide) (by trivial) hqm1
  obtain hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  obtain hy2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy1
  obtain hx2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.privateScalar]) hx1
  refine WP.seq (WP.mono (readyPow_ok M Sq h2.ready .p hp hop Core.generator Core.privateScalar (by trivial) (by trivial)
    hg2.active hx2.active (by rw [hgl]; omega_using [hql, hqp])
    (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hxl]; omega_using [hql]) (by rw [hxl]; omega_using [hqu]) t (by decide) ht) fun s3 h3 => ?_)
  obtain hqm3 := h3.local (by decide) ht hqm2 (by rw [hqml]; exact hqm)
    (Or.inl (by rw [hqml]; unfold qMinusTwo t; omega_using [hqu]))
  obtain hy3 := h3.external (by decide) ht hy2
  obtain hm3 := (h3.fields (by decide) ht .mask).trans h2.mask
  refine WP.mono (readyEqual_ok h3.ready (Core.element t) Core.publicValue
    (by change t < 2 ^ 31; decide) (by trivial) (h3.output (by decide) ht) hy3.active
    (by simp only [encodeBE_length, ModulusSide.length, hyl])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql, hqp])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hpu]) false hm3) fun s4 h4 => ?_
  obtain hqm4 := h4.preserve h3.ready (Nat.le_refl _) (by decide) (by trivial) hqm3
  obtain hqm4bytes := operand_bytesAt hqm4
  rw [hqml] at hqm4bytes
  refine ⟨h4.ready, ?_, hqm4bytes, ((h1.scheduleFrame.trans h2.scheduleFrame).trans (h3.scheduleFrame (by decide) ht)).trans h4.scheduleFrame,
    (((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).mono (by decide)⟩
  have hm4 := h4.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length, ModulusSide.value] at hm4
  exact hm4

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.SigningKey`, which this module and modules that import it used -/

section

/-! # DSA signing domain validation without a redundant public-value power -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def signingKeyAccepted (L : ExecutionLayout) (gb yb : List Byte) (valid : Bool) : Bool :=
  decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) L.subgroup L.modulus = 1) &&
  (decide ((L.modulus - 1) % L.subgroup = 0) &&
  (decide (1 < Spec.Dsa.decodeBE yb ∧ Spec.Dsa.decodeBE yb < L.modulus) &&
  (decide (1 < Spec.Dsa.decodeBE gb ∧ Spec.Dsa.decodeBE gb < L.modulus) && valid)))

theorem signingKey_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb yb qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator gb)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hgl : gb.length = L.pLen) (hyl : yb.length = L.pLen) (hqlen : qb.length = L.qLen)
    (hqval : Spec.Dsa.decodeBE qb = L.subgroup)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.signingKey Sq.mm M.mm) s0 fun s8 =>
      Ready L s8 ∧ word s8.mem L.base Field.mask.offset = mask (signingKeyAccepted L gb yb valid) ∧
      OperandBytes s8 L.base activeBytes (Core.scalar qMinusTwo) (Spec.Dsa.encodeBE L.qLen (L.subgroup - 2)) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s8.mem ∧ Keep coreRegs s0 s8 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  have fitq (n : Nat) (h : n < L.subgroup) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.qLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hqf)
  have fitp (n : Nat) (h : n < L.modulus) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.pLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hpf)
  obtain ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega_using [hpu]
  obtain hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega_using [hqu]
  obtain hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega_using [hqu]
  unfold Checks.signingKey Checks.publicPrefix
  refine WP.seq (WP.mono (readyRange_ok h0 .p Core.generator (by trivial) hg.active
    (by rw [hgl]; omega_using [hql, hqp]) (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true hm) fun s1 h1 => ?_)
  obtain hg1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg
  obtain hy1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy
  obtain hq1 := h1.preserve h0 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb
  refine WP.seq (WP.mono (readyRange_ok h1.ready .p Core.publicValue (by trivial) hy1.active
    (by rw [hyl]; omega_using [hql, hqp]) (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true h1.mask) fun s2 h2 => ?_)
  obtain hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  obtain hq2 := h2.preserve h1.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq1
  refine WP.seq (WP.mono (readyMinus_ok h2.ready .p 1 (by decide) (by change 1 ≤ L.modulus; omega_using [hp])
    t (by decide) ht) fun s3 h3 => ?_)
  obtain hg3 := h3.external (by decide) ht hg2
  obtain hq3 := h3.external (by decide) ht hq2
  obtain hm3 := (h3.fields (by decide) ht .mask).trans h2.mask
  obtain step4 := readyReduce_ok M h3.ready hq hoq (Core.element t) (by change t < 2 ^ 31; decide)
    (h3.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hpu]) u (by decide) hu
  obtain step4' : WP isa (Core.reduce M.mm (Core.element t) (Core.scalar u)) s3
      (CallResult L .q u ((L.modulus - 1) % L.subgroup) s3) := by
    simpa only [ModulusSide.length, ModulusSide.value, fitp (L.modulus - 1) (by omega_using [hp])] using step4
  refine WP.seq (WP.mono step4' fun s4 h4 => ?_)
  obtain hg4 := h4.external (by decide) hu hg3
  obtain hq4 := h4.external (by decide) hu hq3
  obtain hm4 := (h4.fields (by decide) hu .mask).trans hm3
  refine WP.seq (WP.mono (readyZero_ok h4.ready (Core.scalar u) (by change u < 2 ^ 31; decide)
    (h4.output (by decide) hu) (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hqu]) false hm4) fun s5 h5 => ?_)
  obtain hziff : (∀ b ∈ Spec.Dsa.encodeBE L.qLen ((L.modulus - 1) % L.subgroup), b = 0) ↔
      (L.modulus - 1) % L.subgroup = 0 := by
    rw [← VG.Proof.Dsa.decodeBE_eq_zero, fitq _ (Nat.mod_lt _ (by omega_using [hq]))]
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length] at hm5
  simp only [hziff] at hm5
  obtain hg5 := h5.preserve h4.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg4
  obtain hq5 := h5.preserve h4.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq4
  refine WP.seq (WP.mono (readyMinus_ok h5.ready .q 2 (by decide) (by change 2 ≤ L.subgroup; omega_using [hq])
    qMinusTwo (by decide) hqm) fun s6 h6 => ?_)
  obtain hg6 := h6.external (by decide) hqm hg5
  obtain hq6 := h6.external (by decide) hqm hq5
  obtain hm6 := (h6.fields (by decide) hqm .mask).trans hm5
  obtain step7 := readyPublicPow_ok M Sq h6.ready .p hp hop Core.generator ⟨.input .q, .qLen⟩ (by trivial) (by trivial)
    hg6.active hq6.active (by rw [hgl]; omega_using [hql, hqp])
    (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hqlen]; omega_using [hql]) (by rw [hqlen]; omega_using [hqu]) t (by decide) ht
  obtain step7' : WP isa (Core.publicPow Sq.mm M.mm pWorkspace Core.generator ⟨.input .q, .qLen⟩ (Core.element t)) s6
      (CallResult L .p t (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) L.subgroup L.modulus) s6) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value, hqval] using step7
  refine WP.seq (WP.mono step7' fun s7 h7 => ?_)
  obtain hqm7 := h7.local (by decide) ht (h6.output (by decide) hqm)
    (by simp only [encodeBE_length, ModulusSide.length]; exact hqm)
    (Or.inl (by simp only [encodeBE_length, ModulusSide.length]; unfold qMinusTwo t; omega_using [hqu]))
  obtain hm7 := (h7.fields (by decide) ht .mask).trans hm6
  refine WP.mono (readyIsOne_ok h7.ready .p (Core.element t) (by change t < 2 ^ 31; decide)
    (h7.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql, hqp])
    (by simp only [encodeBE_length, ModulusSide.length]; exact Nat.le_refl _) hm7) fun s8 h8 => ?_
  have hm8 := h8.mask
  simp only [ModulusSide.length, fitp _ (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hp]))] at hm8
  obtain hqm8 := h8.preserve h7.ready (Nat.le_refl _) (by decide) (by trivial) hqm7
  refine ⟨h8.ready, hm8, hqm8, ?_, ?_⟩
  · exact ((((((h1.scheduleFrame.trans h2.scheduleFrame).trans (h3.scheduleFrame (by decide) ht)).trans (h4.scheduleFrame (by decide) hu)).trans h5.scheduleFrame).trans
      (h6.scheduleFrame (by decide) hqm)).trans (h7.scheduleFrame (by decide) ht)).trans h8.scheduleFrame
  · exact (((((((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).trans h5.keep).trans h6.keep).trans h7.keep).trans h8.keep).mono (by decide)

end VG.Proof.Dsa.X86_64

end

end

/-! # Signing computation, including every key and scalar rejection mask -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def privateAccepted (L : ExecutionLayout) (data : SignValues) (yb : List Byte) (valid : Bool) : Bool :=
  decide (Spec.Dsa.encodeBE L.pLen
    (Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) (Spec.Dsa.decodeBE data.privateScalar) L.modulus) = yb) &&
  (decide (0 < Spec.Dsa.decodeBE data.nonce ∧ Spec.Dsa.decodeBE data.nonce < L.subgroup) &&
  (decide (0 < Spec.Dsa.decodeBE data.privateScalar ∧ Spec.Dsa.decodeBE data.privateScalar < L.subgroup) &&
    publicAccepted L data.generator yb valid))

/-- The omitted public-value check follows from the generator check and the
private/public key equality, even when the domain integers are composite. -/
theorem privateAccepted_signingKey (L : ExecutionLayout) (data : SignValues)
    (yb : List Byte) (valid : Bool) (hp : 1 < L.modulus)
    (hpf : L.modulus ≤ 256 ^ L.pLen) :
    (decide (Spec.Dsa.encodeBE L.pLen
      (Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) (Spec.Dsa.decodeBE data.privateScalar) L.modulus) = yb) &&
    (decide (0 < Spec.Dsa.decodeBE data.nonce ∧ Spec.Dsa.decodeBE data.nonce < L.subgroup) &&
    (decide (0 < Spec.Dsa.decodeBE data.privateScalar ∧ Spec.Dsa.decodeBE data.privateScalar < L.subgroup) &&
      signingKeyAccepted L data.generator yb valid))) = privateAccepted L data yb valid := by
  by_cases he : Spec.Dsa.encodeBE L.pLen
      (Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) (Spec.Dsa.decodeBE data.privateScalar) L.modulus) = yb
  · by_cases hg : Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) L.subgroup L.modulus = 1
    · have hy : Spec.Dsa.decodeBE yb =
          Spec.Dsa.powMod (Spec.Dsa.decodeBE data.generator) (Spec.Dsa.decodeBE data.privateScalar) L.modulus := by
        rw [← he, decodeBE_encodeBE (Nat.lt_of_lt_of_le (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hp])) hpf)]
      have hsub : Spec.Dsa.powMod (Spec.Dsa.decodeBE yb) L.subgroup L.modulus = 1 := by
        rw [hy, VG.Proof.Dsa.powMod_eq, VG.Proof.Dsa.powMod_eq, ← Nat.pow_mod,
          ← Nat.pow_mul, Nat.mul_comm (Spec.Dsa.decodeBE data.privateScalar) L.subgroup,
          Nat.pow_mul, Nat.pow_mod,
          ← VG.Proof.Dsa.powMod_eq (Spec.Dsa.decodeBE data.generator) L.subgroup L.modulus, hg]
        simp [Nat.mod_eq_of_lt hp]
      simp only [privateAccepted, publicAccepted, signingKeyAccepted, hsub, decide_true, Bool.true_and]
    · simp [privateAccepted, publicAccepted, signingKeyAccepted, hg]
  · simp [privateAccepted, he]

def signAccepted (L : ExecutionLayout) (data : SignValues) (yb : List Byte) (valid : Bool) : Bool :=
  !decide (∀ b ∈ Spec.Dsa.encodeBE L.qLen (data.s L), b = 0) &&
  (!decide (∀ b ∈ Spec.Dsa.encodeBE L.qLen (data.r L), b = 0) && privateAccepted L data yb valid)

def signCompute (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  Checks.signingKey sq mul, Checks.privateKey sq mul, Core.sign sq mul,
  Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true]

theorem signCompute_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : SignValues) {yb qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator data.generator)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hx : OperandBytes s0 L.base usedBytes Core.privateScalar data.privateScalar)
    (hn : OperandBytes s0 L.base usedBytes Core.nonce data.nonce)
    (hz : OperandBytes s0 L.base usedBytes Core.digest data.digest)
    (hgl : data.generator.length = L.pLen) (hyl : yb.length = L.pLen) (hqlen : qb.length = L.qLen)
    (hxl : data.privateScalar.length = L.qLen) (hnl : data.nonce.length = L.qLen)
    (hzl : data.digest.length < 2 ^ 64) (hqval : Spec.Dsa.decodeBE qb = L.subgroup)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (signCompute Sq.mm M.mm) s0 fun s5 =>
      Ready L s5 ∧ word s5.mem L.base Field.mask.offset = mask (signAccepted L data yb valid) ∧
      Spec.Rsa.bytesAt s5.mem (off L.base r) L.qLen = Spec.Dsa.encodeBE L.qLen (data.r L) ∧
      Spec.Rsa.bytesAt s5.mem (off L.base s) L.qLen = Spec.Dsa.encodeBE L.qLen (data.s L) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s5.mem ∧ Keep coreRegs s0 s5 := by
  obtain ⟨hql, hqu, _, _⟩ := L.widths
  have hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega_using [hqu]
  have hr : r + L.qLen ≤ usedBytes := by unfold r usedBytes; omega_using [hqu]
  have hs : s + L.qLen ≤ usedBytes := by unfold s usedBytes; omega_using [hqu]
  unfold signCompute
  refine WP.seq (WP.mono (signingKey_ok M Sq h0 hp hq hop hoq hpf hqf hg hy hqb hgl hyl hqlen hqval hm)
    fun s1 ⟨h1, hm1, hqm1, hf1, hk1⟩ => ?_)
  have hg1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.generator]) hg
  have hy1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.publicValue]) hy
  have hx1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.privateScalar]) hx
  have hn1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.nonce]) hn
  have hz1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.digest]) hz
  refine WP.seq (WP.mono (privateKey_ok M Sq h1 hp hop hg1 hy1 hx1 hn1 hgl hyl hxl hnl hm1)
    fun s2 ⟨h2, hm2, hqm2bytes, hf2, hk2⟩ => ?_)
  rw [privateAccepted_signingKey L data yb valid hp hpf] at hm2
  have hg2 := h1.preserveExternal h2 hf2 hk2 (by decide) (by simp [stablePointer, Core.generator]) hg1
  have hx2 := h1.preserveExternal h2 hf2 hk2 (by decide) (by simp [stablePointer, Core.privateScalar]) hx1
  have hn2 := h1.preserveExternal h2 hf2 hk2 (by decide) (by simp [stablePointer, Core.nonce]) hn1
  have hz2 := h1.preserveExternal h2 hf2 hk2 (by decide) (by simp [stablePointer, Core.digest]) hz1
  have hqm1bytes := operand_bytesAt hqm1
  rw [encodeBE_length] at hqm1bytes
  have hqm2 := h2.encodedLocal .q qMinusTwo (L.subgroup - 2) (by decide) hqm (hqm2bytes.trans hqm1bytes)
  refine WP.seq (WP.mono (coreSign_ok M Sq h2 hp hq hop hoq hpf hqf data hg2 hn2 hx2 hz2 hgl hnl hxl hzl hqm2)
    fun s3 ⟨h3, hr3bytes, hs3bytes, hf3, hm3eq, hk3⟩ => ?_)
  have hm3 : word s3.mem L.base Field.mask.offset = mask (privateAccepted L data yb valid) := hm3eq.trans hm2
  have hr3 := h3.encodedLocal .q r (data.r L) (by decide) hr hr3bytes
  have hs3 := h3.encodedLocal .q s (data.s L) (by decide) hs hs3bytes
  refine WP.seq (WP.mono (readyZero_ok h3 (Core.scalar r) (by change r < 2 ^ 31; decide) hr3
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hqu]) true hm3) fun s4 h4 => ?_)
  have hr4 := h4.preserve h3 (Nat.le_refl _) (by decide) (by trivial) hr3
  have hs4 := h4.preserve h3 (Nat.le_refl _) (by decide) (by trivial) hs3
  refine WP.mono (readyZero_ok h4.ready (Core.scalar s) (by change s < 2 ^ 31; decide) hs4
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hqu]) true h4.mask) fun s5 h5 => ?_
  have hr5 := h5.preserve h4.ready (Nat.le_refl _) (by decide) (by trivial) hr4
  have hs5 := h5.preserve h4.ready (Nat.le_refl _) (by decide) (by trivial) hs4
  refine ⟨h5.ready, ?_, ?_, ?_, (((hf1.trans hf2).trans hf3).trans h4.scheduleFrame).trans h5.scheduleFrame,
    ((((hk1.trans hk2).trans hk3).trans h4.keep).trans h5.keep).mono (by decide)⟩
  · have hm5 := h5.mask
    simp only [↓reduceIte, ModulusSide.length] at hm5
    exact hm5
  · have hh := operand_bytesAt hr5
    rw [encodeBE_length] at hh
    exact hh
  · have hh := operand_bytesAt hs5
    rw [encodeBE_length] at hh
    exact hh

end VG.Proof.Dsa.X86_64

end

end

/-! # Verification computation, including domain, key and signature checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def verifyAccepted (L : ExecutionLayout) (data : VerifyValues) (valid : Bool) : Bool :=
  decide (Spec.Dsa.encodeBE L.qLen (data.value L) = data.signatureR) &&
  (decide (0 < Spec.Dsa.decodeBE data.signatureS ∧ Spec.Dsa.decodeBE data.signatureS < L.subgroup) &&
  (decide (0 < Spec.Dsa.decodeBE data.signatureR ∧ Spec.Dsa.decodeBE data.signatureR < L.subgroup) &&
    publicAccepted L data.generator data.publicValue valid))

def verifyCompute (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  Checks.publicKey sq mul, Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
  Core.verify sq mul, Checks.equal (Core.scalar u) Core.signatureR]

theorem verifyCompute_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : VerifyValues) {qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator data.generator)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue data.publicValue)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hr : OperandBytes s0 L.base usedBytes Core.signatureR data.signatureR)
    (hs : OperandBytes s0 L.base usedBytes Core.signatureS data.signatureS)
    (hz : OperandBytes s0 L.base usedBytes Core.digest data.digest)
    (hgl : data.generator.length = L.pLen) (hyl : data.publicValue.length = L.pLen)
    (hqlen : qb.length = L.qLen) (hrl : data.signatureR.length = L.qLen) (hsl : data.signatureS.length = L.qLen)
    (hzl : data.digest.length < 2 ^ 64) (hqval : Spec.Dsa.decodeBE qb = L.subgroup)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (verifyCompute Sq.mm M.mm) s0 fun s5 =>
      Ready L s5 ∧ word s5.mem L.base Field.mask.offset = mask (verifyAccepted L data valid) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s5.mem ∧ Keep coreRegs s0 s5 := by
  obtain ⟨hql, hqu, _, _⟩ := L.widths
  obtain hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega_using [hqu]
  unfold verifyCompute
  refine WP.seq (WP.mono (publicKey_ok M Sq h0 hp hq hop hoq hpf hqf hg hy hqb hgl hyl hqlen hqval hm)
    fun s1 ⟨h1, hm1, hqm1, hf1, hk1⟩ => ?_)
  obtain hg1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.generator]) hg
  obtain hy1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.publicValue]) hy
  obtain hr1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.signatureR]) hr
  obtain hs1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by trivial) hs
  obtain hz1 := h0.preserveExternal h1 hf1 hk1 (by decide) (by simp [stablePointer, Core.digest]) hz
  refine WP.seq (WP.mono (readyRange_ok h1 .q Core.signatureR (by trivial) hr1.active
    (by rw [hrl]; omega_using [hql]) (by simp only [hrl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm1) fun s2 h2 => ?_)
  obtain hg2 := h2.preserve h1 (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  obtain hy2 := h2.preserve h1 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy1
  obtain hr2 := h2.preserve h1 (by decide) (by decide) (by simp [stablePointer, Core.signatureR]) hr1
  obtain hs2 := h2.preserve h1 (by decide) (by decide) (by trivial) hs1
  obtain hz2 := h2.preserve h1 (by decide) (by decide) (by simp [stablePointer, Core.digest]) hz1
  obtain hqm2 := h2.preserve h1 (Nat.le_refl _) (by decide) (by trivial) hqm1
  refine WP.seq (WP.mono (readyRange_ok h2.ready .q Core.signatureS (by trivial) hs2.active
    (by rw [hsl]; omega_using [hql]) (by simp only [hsl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false h2.mask) fun s3 h3 => ?_)
  obtain hg3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg2
  obtain hy3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy2
  obtain hr3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.signatureR]) hr2
  obtain hs3 := h3.preserve h2.ready (by decide) (by decide) (by trivial) hs2
  obtain hz3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.digest]) hz2
  obtain hqm3 := h3.preserve h2.ready (Nat.le_refl _) (by decide) (by trivial) hqm2
  refine WP.seq (WP.mono (coreVerify_ok M Sq h3.ready hp hq hop hoq hpf hqf data hg3 hy3 hr3 hs3 hz3
    hgl hyl hrl hsl hzl hqm3) fun s4 ⟨h4, hu4bytes, hf4, hm4eq, hk4⟩ => ?_)
  obtain hr4 := h3.ready.preserveExternal h4 hf4 hk4 (by decide) (by simp [stablePointer, Core.signatureR]) hr3
  obtain hm4 := hm4eq.trans h3.mask
  obtain hu4 := h4.encodedLocal .q u (data.value L) (by decide) hu hu4bytes
  refine WP.mono (readyEqual_ok h4 (Core.scalar u) Core.signatureR
    (by change u < 2 ^ 31; decide) (by trivial) hu4 hr4.active
    (by simp only [encodeBE_length, ModulusSide.length, hrl])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hqu]) false hm4) fun s5 h5 => ?_
  refine ⟨h5.ready, ?_, (((hf1.trans h2.scheduleFrame).trans h3.scheduleFrame).trans hf4).trans h5.scheduleFrame,
    ((((hk1.trans h2.keep).trans h3.keep).trans hk4).trans h5.keep).mono (by decide)⟩
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length, ModulusSide.value] at hm5
  exact hm5

end VG.Proof.Dsa.X86_64

end

end

/-! # Connecting implementation acceptance masks with DSA's operational checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.Impl.Dsa.Layout

/-- The public checks express domain consistency and public-key validity;
no exact or probabilistic primality proposition appears in the proof. -/
theorem publicAccepted_spec (L : ExecutionLayout) (gb yb : List Byte)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1) :
    publicAccepted L gb yb true =
      (decide (Spec.Dsa.parametersValid ⟨L.modulus, L.subgroup, Spec.Dsa.decodeBE gb⟩) &&
        Spec.Dsa.keyValid ⟨⟨L.modulus, L.subgroup, Spec.Dsa.decodeBE gb⟩, Spec.Dsa.decodeBE yb, none⟩) := by
  have hqp := (VG.Proof.Dsa.supported_bounds hsize).2.2
  apply Bool.eq_iff_iff.mpr
  simp only [publicAccepted, Spec.Dsa.parametersValid, Spec.Dsa.keyValid,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.and_true, hsize, hop, hoq, hqp, true_and]
  simp only [and_assoc, and_left_comm, and_comm]

theorem privateAccepted_spec (L : ExecutionLayout) (data : SignValues) (yb : List Byte)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hyl : yb.length = L.pLen) :
    privateAccepted L data yb true =
      (decide (Spec.Dsa.parametersValid ⟨L.modulus, L.subgroup, Spec.Dsa.decodeBE data.generator⟩) &&
        Spec.Dsa.keyValid ⟨⟨L.modulus, L.subgroup, Spec.Dsa.decodeBE data.generator⟩,
          Spec.Dsa.decodeBE yb, some (Spec.Dsa.decodeBE data.privateScalar)⟩ &&
        decide (0 < Spec.Dsa.decodeBE data.nonce ∧ Spec.Dsa.decodeBE data.nonce < L.subgroup)) := by
  have hp := (VG.Proof.Dsa.supported_bounds hsize).1
  have hfit := Nat.lt_of_lt_of_le (VG.Proof.Dsa.powMod_lt (Spec.Dsa.decodeBE data.generator)
    (Spec.Dsa.decodeBE data.privateScalar) (by omega_using [hop] : 0 < L.modulus)) hpf
  unfold privateAccepted
  rw [publicAccepted_spec L data.generator yb hsize hop hoq]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, VG.Proof.Dsa.encodeBE_eq_bytes hyl hfit,
    Spec.Dsa.keyValid, beq_iff_eq, Bool.and_true]
  simp only [and_assoc, and_left_comm, and_comm]

theorem signAccepted_nonzero (L : ExecutionLayout) (data : SignValues) (yb : List Byte) (valid : Bool)
    (hq : 0 < L.subgroup) (hqf : L.subgroup ≤ 256 ^ L.qLen) :
    signAccepted L data yb valid =
      (decide (data.s L ≠ 0) && (decide (data.r L ≠ 0) && privateAccepted L data yb valid)) := by
  have hr : data.r L < L.subgroup := Nat.mod_lt _ hq
  have hs : data.s L < L.subgroup := Nat.mod_lt _ hq
  unfold signAccepted
  simp only [← VG.Proof.Dsa.decodeBE_eq_zero,
    VG.Proof.Dsa.decodeBE_encodeBE (Nat.lt_of_lt_of_le hr hqf),
    VG.Proof.Dsa.decodeBE_encodeBE (Nat.lt_of_lt_of_le hs hqf), decide_not]

theorem verifyAccepted_value (L : ExecutionLayout) (data : VerifyValues) (valid : Bool)
    (hq : 0 < L.subgroup) (hqf : L.subgroup ≤ 256 ^ L.qLen) (hrl : data.signatureR.length = L.qLen) :
    verifyAccepted L data valid =
      (decide (data.value L = Spec.Dsa.decodeBE data.signatureR) &&
      (decide (0 < Spec.Dsa.decodeBE data.signatureS ∧ Spec.Dsa.decodeBE data.signatureS < L.subgroup) &&
      (decide (0 < Spec.Dsa.decodeBE data.signatureR ∧ Spec.Dsa.decodeBE data.signatureR < L.subgroup) &&
        publicAccepted L data.generator data.publicValue valid))) := by
  have hv : data.value L < L.subgroup := Nat.mod_lt _ hq
  unfold verifyAccepted
  simp only [VG.Proof.Dsa.encodeBE_eq_bytes hrl (Nat.lt_of_lt_of_le hv hqf)]

end VG.Proof.Dsa.X86_64
