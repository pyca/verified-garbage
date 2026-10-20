module
public import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Dsa.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.R2wFast
import VerifiedGarbage.Proof.Bignum.X86_64.Row

/-! # RSA Montgomery setup with a fallback for padded DSA moduli -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

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

theorem setupBases_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block Arithmetic.setupBases) s fun t =>
      Good t B Z w minv ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r10 = off B (slot w aN) ∧ t.mem = s.mem ∧ Keep [.r12, .r10] s t := by
  refine WP.mono (WP.keep [.r12, .r10] (Q := fun t =>
    t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r10 = off B (slot w aN) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨h12, h10, hm⟩, hk⟩ => ⟨⟨hg.scr.congr hk.2.2,
      (hk.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, h12, h10, hm, hk⟩
  unfold Arithmetic.setupBases
  xrun [State.ea, hdr, hg.rdi, hdrOff, hg.hdr.hw, hg.hdr.harr aN (by decide),
    hg.scr.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega),
    hg.scr.ld (show 8 * sArr aN + 8 ≤ Z by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega)]

theorem setupTest_ok {s : State} {B : Addr} {Z w m : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w)
    (hn : wv s.mem B (slot w aN) w = m)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h10 : s.gpr .r10 = off B (slot w aN)) :
    WP isa (.block Arithmetic.setupTest) s fun t =>
      t.zf = some (decide (m / 2 ^ (64 * (w - 1)) = 0)) ∧
      t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.zf = some (decide (m / 2 ^ (64 * (w - 1)) = 0)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩
  unfold Arithmetic.setupTest
  xrun [State.ea, ix, addrm8 h10 h12 (by omega),
    hg.scr.ld (show slot w aN + 8 * (w - 1) + 8 ≤ Z by
      have := slot_le (w := w) (show aN < 8 by decide); omega)]
  rw [← setup_top hw hn]
  simp only [VG.Proof.Bignum.word, BitVec.and_self]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj]
  rfl

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
  refine WP.seq (WP.mono (setupBases_ok hu hZ) fun v ⟨hv, h12, h10, hvm, hkv⟩ => ?_)
  have vn : wv v.mem B (slot w aN) w = m := hvm ▸ un
  refine WP.seq (WP.mono (setupTest_ok hv hZ hw vn h12 h10) fun z ⟨hz, hzm, hkz⟩ => ?_)
  have hgZ : Good z B Z w minv := ⟨hv.scr.congr hkz.2.2, (hkz.gpr (by decide)).trans hv.rdi, hzm ▸ hv.hdr⟩
  have zn : wv z.mem B (slot w aN) w = m := hzm ▸ vn
  have finish : ∀ t, (Good t B Z w minv ∧ wv t.mem B (slot w aR2) w = 2 ^ (128 * w) % m ∧
      Frm B (r2Ranges w) z.mem t.mem ∧ Keep mmRegs z t) →
      (Good t B Z w minv ∧ wv t.mem B (slot w aOne) w = 1 ∧
      wv t.mem B (slot w aR2) w = 2 ^ (128 * w) % m ∧
      Frm B ((slot w aOne, 8 * (w + 2)) :: r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t) := by
    intro t ⟨ht, hr, hf, hk⟩
    refine ⟨ht, ?_, hr, ?_, (((hku.trans hkv).trans hkz).trans hk).mono (by decide)⟩
    · rw [hf.r2_wv hnZ (by decide) (by decide) (by decide) (by decide), hzm, hvm]; exact hu1
    · have f1 : Frm B ((slot w aOne, 8 * (w + 2)) :: r2Ranges w) s.mem u.mem :=
        Frm.of_arrays hfu (by intro j hj; simp only [List.mem_singleton] at hj; subst j; simp)
      have f2 := hf.mono (fun r hr => List.mem_cons_of_mem (slot w aOne, 8 * (w + 2)) hr)
      rw [hzm, hvm] at f2
      exact f1.trans f2
  generalize he : decide (m / 2 ^ (64 * (w - 1)) = 0) = e at hz
  refine WP.ite e (by simp only [eval, hz]) (fun _ => WP.mono (doublingR2_ok hgZ hZ hw hw48 zn hm) finish) (fun hc => ?_)
  have hlo : 2 ^ (64 * (w - 1)) ≤ m := by
    have hne := of_decide_eq_false (he.trans hc)
    by_contra h
    exact hne (Nat.div_eq_of_lt (by omega))
  refine WP.mono (R2w.choice_ok M hgZ hZ hw (by omega) zn
    (by rw [hzm, hvm]; exact ui) ((hkz.gpr (by decide)).trans h12)
    ((hkz.gpr (by decide)).trans h10) hodd hlo) fun t ⟨ht, hl, hr, hf, hk⟩ => finish t ⟨ht, ?_, hf, hk⟩
  rw [Nat.mod_eq_of_lt hl] at hr
  rw [← Nat.pow_add] at hr
  rw [show 64 * w + 64 * w = 128 * w by omega] at hr
  exact hr

end VG.Proof.Dsa.X86_64
