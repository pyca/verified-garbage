module

public import VerifiedGarbage.Proof.Dsa.AArch64.JointAdvance
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
public import VerifiedGarbage.Proof.Dsa.AArch64.JointBuildContext

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
