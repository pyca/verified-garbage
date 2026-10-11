import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.R2

/-! # Montgomery setup for DSA, including leading-zero modulus limbs -/

namespace VG.Proof.Dsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Initialize an array to 1, without relying on its previous contents. -/
theorem one_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {a : Nat} (ha : a < 8) :
    WP isa (Arithmetic.small a 1) s fun t =>
      Good t B Z w minv ∧ wv t.mem B (slot w a) w = 1 ∧
      Arrays B w [a] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Arithmetic.small
  refine WP.seq (WP.mono (WP.keep [.r12, .rdx, .rcx]
    (Q := fun u => u.gpr .r12 = BitVec.ofNat 64 w ∧ u.gpr .rdx = 1 ∧
      u.gpr .rcx = 0 ∧ u.mem = s.mem) ?_ rfl) fun u ⟨⟨hu12, hu2, huc, hum⟩, hku⟩ => ?_)
  · xrun [State.ea, hdr, hg.rdi, hdrOff, hg.hdr.hw,
      hg.scr.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)]
  have hud : u.gpr .rdi = B := (hku.gpr (by decide)).trans hg.rdi
  have huh : Hdr u.mem B w minv := by rw [hum]; exact hg.hdr
  refine WP.mono (setWord_ok (hg.scr.congr hku.2.2) hud huh hZ hu12
    (by omega) hw' ha (by decide) (show 0 < w by omega) huc) fun t ⟨hv, hf, hk⟩ => ?_
  have hfa : Arrays B w [a] u.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self a) hf (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨⟨hg.scr.congr ((hku.trans hk).2.2), (hk.gpr (by decide)).trans hud,
      hfa.hdr huh⟩, ?_, ?_, (hku.trans hk).mono (by decide)⟩
  · simpa [hu2] using hv
  · rw [hum] at hfa
    exact hfa

/-- Computing the public doubling count preserves memory and the header. -/
theorem r2Count_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block Arithmetic.r2Count) s fun t =>
      Good t B Z w minv ∧ t.gpr .rcx = BitVec.ofNat 64 (128 * w) ∧
      t.mem = s.mem ∧ Keep [.rcx] s t := by
  refine WP.mono (WP.keep [.rcx] (Q := fun t =>
    t.gpr .rcx = BitVec.ofNat 64 (128 * w) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hc, hm⟩, hk⟩ => ⟨⟨hg.scr.congr hk.2.2,
      (hk.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩, hc, hm, hk⟩
  unfold Arithmetic.r2Count
  xrun [State.ea, hdr, hg.rdi, hdrOff, hg.hdr.hw,
    hg.scr.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)]
  simp only [BitVec.ofNat_add_ofNat]
  congr 1
  omega

/-- R² initialization, with no condition on the top limb of the modulus. -/
theorem constants_ok {s : State} {B : Addr} {Z w m : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw48 : w ≤ 48)
    (hn : wv s.mem B (slot w aN) w = m) (hm : 1 < m) :
    WP isa Arithmetic.constants s fun t =>
      Good t B Z w minv ∧ wv t.mem B (slot w aOne) w = 1 ∧
      wv t.mem B (slot w aR2) w = 2 ^ (128 * w) % m ∧
      Frm B ((slot w aOne, 8 * (w + 2)) :: r2Ranges w) s.mem t.mem ∧
      Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega
  have hnZ : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
  unfold Arithmetic.constants seqs
  refine WP.seq (WP.mono (one_ok hg hZ hw hw' (by decide)) fun u ⟨hu, hu1, hfu, hku⟩ => ?_)
  have un : wv u.mem B (slot w aN) w = m :=
    (hfu.wv_of_not_mem (by decide) (by decide) hnZ).trans hn
  refine WP.seq (WP.mono (one_ok hu hZ hw hw' (by decide)) fun v ⟨hv, hv1, hfv, hkv⟩ => ?_)
  have vn : wv v.mem B (slot w aN) w = m :=
    (hfv.wv_of_not_mem (by decide) (by decide) hnZ).trans un
  have vone : wv v.mem B (slot w aOne) w = 1 :=
    (hfv.wv_of_not_mem (by decide) (by decide) hnZ).trans hu1
  refine WP.seq (WP.mono (r2Count_ok hv hZ) fun v' ⟨hv', hvc, hvm, hkc⟩ => ?_)
  have v'n : wv v'.mem B (slot w aN) w = m := by rw [hvm]; exact vn
  have v'one : wv v'.mem B (slot w aOne) w = 1 := by rw [hvm]; exact vone
  have v'r2 : wv v'.mem B (slot w aR2) w = 1 := by rw [hvm]; exact hv1
  refine WP.mono (doubles_ok hv'.scr hv'.rdi hv'.hdr hZ hw hw'
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (show 1 ≤ 128 * w by omega) (show 128 * w < 2 ^ 31 by omega)
    hvc (by rw [v'r2, v'n]; exact hm)) fun t ⟨htv, hft, hht, hkt⟩ => ?_
  have ft : Frm B (r2Ranges w) v'.mem t.mem := hft
  refine ⟨⟨hg.scr.congr ((((hku.trans hkv).trans hkc).trans hkt).2.2),
      (hkt.gpr (by decide)).trans hv'.rdi, hht⟩, ?_, ?_, ?_,
      (((hku.trans hkv).trans hkc).trans hkt).mono (by decide)⟩
  · exact (ft.r2_wv hnZ (by decide) (by decide) (by decide) (by decide)).trans v'one
  · simpa only [v'r2, v'n, Nat.mul_one] using htv
  · have f1 : Frm B ((slot w aOne, 8 * (w + 2)) :: r2Ranges w) s.mem u.mem :=
      Frm.of_arrays hfu (by intro j hj; simp only [List.mem_singleton] at hj; subst j; simp)
    have f2 : Frm B ((slot w aOne, 8 * (w + 2)) :: r2Ranges w) u.mem v.mem :=
      Frm.of_arrays hfv (by intro j hj; simp only [List.mem_singleton] at hj; subst j; simp [r2Ranges])
    have f3 : Frm B ((slot w aOne, 8 * (w + 2)) :: r2Ranges w) v'.mem t.mem :=
      ft.mono (fun r hr => List.mem_cons_of_mem _ hr)
    rw [hvm] at f3
    exact (f1.trans f2).trans f3

end VG.Proof.Dsa.X86_64
