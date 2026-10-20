module

public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Montgomery setup for DSA: RSA's R² setup, with a doubling fallback for
leading-zero modulus limbs -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Initialize an array to 1, without relying on its previous contents. -/
theorem small_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {a : Nat} (ha : a < 8) {value : Nat} (hv16 : value < 2 ^ 16) :
    WP isa (Arithmetic.small a value) s fun t =>
      Good t B Z w minv ∧ wv t.mem B (slot w a) w = value ∧
      Arrays B w [a] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Arithmetic.small
  refine WP.seq (WP.mono (WP.keep [.x12, .x9, .x13]
    (Q := fun u => u.gpr .x12 = BitVec.ofNat 64 w ∧ u.gpr .x9 = BitVec.ofNat 64 value ∧
      u.gpr .x13 = 0 ∧ u.mem = s.mem) ?_ rfl rfl rfl) fun u ⟨⟨hu12, hu2, huc, hum⟩, hku⟩ => ?_)
  · brun [hg.x0, hdr_enc (show sW < 32 by decide), hg.hdr.hw,
      hg.scr.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hud : u.gpr .x0 = B := (hku.gpr .x0 (by decide)).trans hg.x0
  have huh : Hdr u.mem B w minv := by rw [hum]; exact hg.hdr
  refine WP.mono (setWord_ok (hg.scr.congr hku.wr) hud huh hZ hu12
    hw' ha (show 0 < w by omega) huc) fun t ⟨hv, hf, hk⟩ => ?_
  have hfa : Arrays B w [a] u.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self a) hf (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨⟨hg.scr.congr ((hku.trans hk).wr), (hk.gpr .x0 (by decide)).trans hud,
      hfa.hdr huh⟩, ?_, ?_, (hku.trans hk).mono (by decide)⟩
  · simpa [hu2, Nat.mod_eq_of_lt (show value < 2 ^ 64 by omega)] using hv
  · rw [hum] at hfa
    exact hfa

/-- Initialize an array to 1, without relying on its previous contents. -/
theorem one_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {a : Nat} (ha : a < 8) :
    WP isa (Arithmetic.small a 1) s fun t =>
      Good t B Z w minv ∧ wv t.mem B (slot w a) w = 1 ∧
      Arrays B w [a] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Arithmetic.small
  refine WP.seq (WP.mono (WP.keep [.x12, .x9, .x13]
    (Q := fun u => u.gpr .x12 = BitVec.ofNat 64 w ∧ u.gpr .x9 = 1 ∧
      u.gpr .x13 = 0 ∧ u.mem = s.mem) ?_ rfl rfl rfl) fun u ⟨⟨hu12, hu2, huc, hum⟩, hku⟩ => ?_)
  · brun [hg.x0, hdr_enc (show sW < 32 by decide), hg.hdr.hw,
      hg.scr.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)]
  have hud : u.gpr .x0 = B := (hku.gpr .x0 (by decide)).trans hg.x0
  have huh : Hdr u.mem B w minv := by rw [hum]; exact hg.hdr
  refine WP.mono (setWord_ok (hg.scr.congr hku.wr) hud huh hZ hu12
    hw' ha (show 0 < w by omega) huc) fun t ⟨hv, hf, hk⟩ => ?_
  have hfa : Arrays B w [a] u.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self a) hf (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨⟨hg.scr.congr ((hku.trans hk).wr), (hk.gpr .x0 (by decide)).trans hud,
      hfa.hdr huh⟩, ?_, ?_, (hku.trans hk).mono (by decide)⟩
  · simpa [hu2] using hv
  · rw [hum] at hfa
    exact hfa

/-- Computing the public doubling count preserves memory and the header. -/
theorem r2Count_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block Arithmetic.r2Count) s fun t =>
      Good t B Z w minv ∧ t.gpr .x13 = BitVec.ofNat 64 (128 * w) ∧
      t.mem = s.mem ∧ Keep [.x13] s t := by
  refine WP.mono (WP.keep [.x13] (Q := fun t =>
    t.gpr .x13 = BitVec.ofNat 64 (128 * w) ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hc, hm⟩, hk⟩ => ⟨⟨hg.scr.congr hk.wr,
      (hk.gpr .x0 (by decide)).trans hg.x0, by rw [hm]; exact hg.hdr⟩, hc, hm, hk⟩
  have shift : (BitVec.ofNat 64 w <<< 7 : BitVec 64) = BitVec.ofNat 64 (128 * w) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  unfold Arithmetic.r2Count
  brun [hg.x0, hdr_enc (show sW < 32 by decide), hg.hdr.hw, shift,
    hg.scr.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)]

/-- R² initialization, with no condition on the top limb of the modulus. -/
theorem doublingR2_ok {s : State} {B : Addr} {Z w m : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw48 : w ≤ 48)
    (hn : wv s.mem B (slot w aN) w = m) (hm : 1 < m) :
    WP isa Arithmetic.doublingR2 s fun t =>
      Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w = 2 ^ (128 * w) % m ∧
      Frm B (r2Ranges w) s.mem t.mem ∧
      Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega
  have hnZ : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
  unfold Arithmetic.doublingR2 seqs
  refine WP.seq (WP.mono (one_ok hg hZ hw hw' (by decide)) fun v ⟨hv, hv1, hfv, hkv⟩ => ?_)
  have vn : wv v.mem B (slot w aN) w = m :=
    (hfv.wv_of_not_mem (by decide) (by decide) hnZ).trans hn
  refine WP.seq (WP.mono (r2Count_ok hv hZ) fun v' ⟨hv', hvc, hvm, hkc⟩ => ?_)
  have v'n : wv v'.mem B (slot w aN) w = m := by rw [hvm]; exact vn
  have v'r2 : wv v'.mem B (slot w aR2) w = 1 := by rw [hvm]; exact hv1
  refine WP.mono (doubles_ok hv'.scr hv'.x0 hv'.hdr hZ hw hw'
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (show 1 ≤ 128 * w by omega) (show 128 * w < 2 ^ 31 by omega)
    hvc (by rw [v'r2, v'n]; exact hm)) fun t ⟨htv, hft, hht, hkt⟩ => ?_
  have ft : Frm B (r2Ranges w) v'.mem t.mem := hft
  refine ⟨⟨hg.scr.congr (((hkv.trans hkc).trans hkt).wr),
      (hkt.gpr .x0 (by decide)).trans hv'.x0, hht⟩, ?_, ?_,
      ((hkv.trans hkc).trans hkt).mono (by decide)⟩
  · simpa only [v'r2, v'n, Nat.mul_one] using htv
  · have f1 : Frm B (r2Ranges w) s.mem v.mem :=
      Frm.of_arrays hfv (by intro j hj; simp only [List.mem_singleton] at hj; subst j; simp [r2Ranges])
    rw [hvm] at ft
    exact f1.trans ft

theorem setup_top {s : State} {B : Addr} {w m : Nat} (hw : 2 ≤ w)
    (hn : wv s.mem B (slot w aN) w = m) :
    (word s.mem B (slot w aN + 8 * (w - 1))).toNat = m / 2 ^ (64 * (w - 1)) := by
  have hs : m = m % 2 ^ (64 * (w - 1)) +
      2 ^ (64 * (w - 1)) * (word s.mem B (slot w aN + 8 * (w - 1))).toNat := by
    have e : wv s.mem B (slot w aN) (w - 1 + 1) = m := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ w)]; exact hn
    rw [wv] at e
    have hlt := wv_lt s.mem B (slot w aN) (w - 1)
    rw [← e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hP := Nat.two_pow_pos (64 * (w - 1))
  have := Nat.mod_lt m hP
  rw [Nat.div_eq_of_lt_le (k := (word s.mem B (slot w aN + 8 * (w - 1))).toNat) ?_ ?_]
  · rw [Nat.mul_comm]; omega
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega

/-- The modulus' top word into `x3`. -/
theorem topWord_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa (.block Arithmetic.topWord) s fun t =>
      (t.gpr .x3 = word s.mem B (slot w aN + 8 * (w - 1)) ∧ t.mem = s.mem) ∧
      Keep [.x3, .x4, .x8, .x12] s t := by
  have hs := hg.scr
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; have := slot_le (w := w) (show 7 < 8 by decide); omega)
  have hsl := slot_le (w := w) (show aN < 8 by decide)
  have hw8 : (BitVec.ofNat 64 w - BitVec.ofNat 64 1) <<< 3 = BitVec.ofNat 64 (8 * (w - 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  refine WP.keep [.x3, .x4, .x8, .x12] ?_ (by decide) (by decide) (by decide +kernel)
  unfold Arithmetic.topWord
  brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aN < 32 by decide), hl sW (by decide),
    hl (sArr aN) (by decide), hg.hdr.hw, hg.hdr.harr aN (by decide), hw8, off_add,
    hs.ld (show slot w aN + 8 * (w - 1) + 8 ≤ Z by omega)]

/-- The fast path is used only when RSA's nonzero-top-word premise holds. -/
theorem constants_ok (M : Mont) {s : State} {B : Addr} {Z w m : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw48 : w ≤ 48)
    (hn : wv s.mem B (slot w aN) w = m) (hm : 1 < m) (hodd : m % 2 = 1)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa (Arithmetic.constants M.mm) s fun t =>
      Good t B Z w minv ∧ wv t.mem B (slot w aOne) w = 1 ∧
      wv t.mem B (slot w aR2) w = 2 ^ (128 * w) % m ∧
      Frm B ((slot w aOne, 8 * (w + 2)) :: r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnZ : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
  unfold Arithmetic.constants
  refine WP.seq (WP.mono (one_ok hg hZ hw (by omega) (by decide)) fun u ⟨hu, hu1, hfu, hku⟩ => ?_)
  have un := (hfu.wv_of_not_mem (show aN < 8 by decide) (by decide) hnZ).trans hn
  have ui : ((word u.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfu.word0_of_not_mem (by decide) (by decide) hnZ (by omega)]; exact hinv
  refine WP.seq (WP.mono (topWord_ok hu hZ hw (by omega)) fun z ⟨⟨hz3, hzm⟩, hkz⟩ => ?_)
  have hgZ : Good z B Z w minv := ⟨hu.scr.congr hkz.wr, (hkz.gpr _ (by decide)).trans hu.x0, hzm ▸ hu.hdr⟩
  have zn : wv z.mem B (slot w aN) w = m := hzm ▸ un
  have finish : ∀ t, (Good t B Z w minv ∧ wv t.mem B (slot w aR2) w = 2 ^ (128 * w) % m ∧
      Frm B (r2Ranges w) z.mem t.mem ∧ Keep mmRegs z t) →
      (Good t B Z w minv ∧ wv t.mem B (slot w aOne) w = 1 ∧
      wv t.mem B (slot w aR2) w = 2 ^ (128 * w) % m ∧
      Frm B ((slot w aOne, 8 * (w + 2)) :: r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t) := by
    intro t ⟨ht, hr, hf, hk⟩
    refine ⟨ht, ?_, hr, ?_, ((hku.trans hkz).trans hk).mono (by decide)⟩
    · rw [hf.r2_wv hnZ (by decide) (by decide) (by decide) (by decide), hzm]; exact hu1
    · have f1 : Frm B ((slot w aOne, 8 * (w + 2)) :: r2Ranges w) s.mem u.mem :=
        Frm.of_arrays hfu (by intro j hj; simp only [List.mem_singleton] at hj; subst j; simp)
      have f2 := hf.mono (fun r hr => List.mem_cons_of_mem (slot w aOne, 8 * (w + 2)) hr)
      rw [hzm] at f2
      exact f1.trans f2
  have htop := setup_top (s := u) hw un
  generalize he : decide (m / 2 ^ (64 * (w - 1)) = 0) = e
  refine WP.ite e (by rw [eval_zero, hz3, eq_zero_iff, htop, he])
    (fun _ => WP.mono (doublingR2_ok hgZ hZ hw hw48 zn hm) finish) (fun hc => ?_)
  have hlo : 2 ^ (64 * (w - 1)) ≤ m := by
    have hne := of_decide_eq_false (he.trans hc)
    by_contra h
    exact hne (Nat.div_eq_of_lt (by omega))
  refine WP.mono (r2_ok M hgZ hZ hw (by omega) zn (by rw [hzm]; exact ui) hodd hlo)
    fun t ⟨ht, hl, hr, hf, hk⟩ => finish t ⟨ht, ?_, hf, hk⟩
  rw [Nat.mod_eq_of_lt hl] at hr
  rw [← Nat.pow_add] at hr
  rw [show 64 * w + 64 * w = 128 * w by omega] at hr
  exact hr

end VG.Proof.Dsa.AArch64
