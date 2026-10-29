module

public import VerifiedGarbage.Proof.Dsa.X86_64.JointBuildContext
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame

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
  have hslot : 136 ≤ slot w 8 + tabBytes w := by unfold slot hdrBytes; omega
  omega

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
  have helo := slot_mono w (show 8 ≤ 8 + j by omega)
  have hsmall : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  refine WP.seq (WP.mono (toEnt_ok hc.exp hw hw' (by decide) hj he) fun v ⟨hv, hf, hk⟩ => ?_)
  have fexp : Frm P (crtExpRanges w) t.mem v.mem :=
    Frm.of_outside (hf.mono (o' := slot w 8) (n' := tabBytes w) helo (by omega)) (by simp [crtExpRanges])
  have cv := hc.exp.of_frm fexp hk.2.2 (hk.gpr (by decide))
  have ve : word v.mem P (8 * Crt.sEnt) = off P (slot w (8 + j)) :=
    (hf.word (Or.inl (by have := hdr_lt_slot w 8 (show Crt.sEnt < 32 by decide); omega)) (by decide)).trans he
  refine WP.mono (nextEnt_ok cv ve) fun u ⟨hm, ku⟩ => ?_
  have ho := writeW_outside v.mem P (d := 8 * Crt.sEnt) (off P (slot w (8 + j) + 8 * (w + 2))) (by decide)
  rw [← hm] at ho
  have ff : Frm P (crtExpRanges w) v.mem u.mem := Frm.of_outside ho (by simp [crtExpRanges, crtWinRanges])
  have cu := cv.of_frm ff ku.2.2 (ku.gpr (by decide))
  have harray : ∀ a, slot w a + 8 * w ≤ slot w 8 + tabBytes w →
      wv u.mem P (slot w a) w = wv v.mem P (slot w a) w := fun a ha =>
    ho.wv (Or.inr (by have := hdr_lt_slot w a (show Crt.sEnt < 32 by decide); omega)) (by omega)
  refine ⟨⟨⟨cu.good, cu.n, cu.inv⟩, cu.scrT⟩, ?_, ?_, ?_, ?_, ?_, ?_, (hk.trans ku).mono (by decide)⟩
  · intro a ha
    have hab := slot_le (w := w) ha
    rw [harray a (by omega), hf.wv (Or.inl (by omega)) (by omega)]
  · intro k hk' hne
    rw [hm, hdrStore_hdr _ _ _ (by decide) hk' (Ne.symm hne)]
    exact hf.word (Or.inl (by have := hdr_lt_slot w 8 hk'; omega)) (by omega)
  · rw [hm, word_writeW_self]
    congr 1
    simp only [slot, Nat.add_mul, Nat.one_mul]
    omega
  · rw [harray (8 + j) (by omega)]; exact hv
  · intro k hk' hne
    have hb := ent_le w hk'
    have hs := slot_sep (w := w) (show 8 + k ≠ 8 + j by omega)
    rw [harray (8 + k) (by omega)]
    exact hf.wv (by omega) (by omega)
  · exact (joint_outside_work hf (by omega) (by omega)).trans
      (joint_outside_work ho (by decide) (by have := hdr_lt_slot w 8 (show Crt.sEnt < 32 by decide); omega))

end VG.Proof.Dsa.X86_64
