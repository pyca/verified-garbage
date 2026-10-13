module

public import VerifiedGarbage.Proof.Dsa.AArch64.Setup
public import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # RSA Montgomery setup with a fallback for padded DSA moduli -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

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
