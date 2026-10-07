import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc

/-! The aligned reduction and general fallback share the same arithmetic result. -/
namespace VG.Proof.Bignum.X86_64.AdxSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem and7 (w : Nat) (hw : w < 2 ^ 64) :
    BitVec.ofNat 64 w &&& 7 = BitVec.ofNat 64 (w % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat]
  omega

theorem redcTest_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw : w < 2 ^ 64) :
    WP isa (.block AdxSquare.redcTest) s fun t =>
      t.zf = some (decide (w % 8 = 0)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hl := hs.ld (show 8 * sW + 8 ≤ Z by
    have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.zf = some (decide (w % 8 = 0)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold AdxSquare.redcTest
  xrun [State.ea, hdr, hdi, hdrOff, hl, hH.hw, and7 w hw]
  change ((BitVec.ofNat 64 w &&& 7) - BitVec.ofNat 64 0 == 0) = _
  rw [and7 w hw]
  exact ofNat_sub_beq (by omega) (by decide)

theorem redcChoice_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa AdxSquare.redcChoice s fun t =>
      (∃ q < 2 ^ (64 * w), 2 ^ (64 * w) * wv t.mem B (slot w aTmp) (w + 2) =
        wv s.mem B (slot w aAcc + 16) (2 * w) + q * wv s.mem B (slot w aN) w) ∧
      Outside B (slot w aAcc) (16 * w + 32) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxSquare.redcChoice
  refine WP.seq (WP.mono (redcTest_ok hs hdi hH hZ (by omega)) fun a ⟨hz, hm, ka⟩ => ?_)
  have sa := hs.congr ka.2.2
  have da := (ka.gpr (by decide)).trans hdi
  have ha := hm ▸ hH
  have inv : ((word a.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by rw [hm]; exact hinv
  by_cases h8 : w % 8 = 0
  · refine WP.ite true (by simp [eval, hz, h8]) (fun _ => ?_) (by simp)
    refine WP.mono (AdxRotate8.redc_ok sa da ha hZ (show w = 8 * (w / 8) by omega) (by omega))
      fun t ⟨vt, ot, kt⟩ => ?_
    have v := vt inv
    rw [hm] at v ot
    exact ⟨v, ot, (ka.trans kt).mono (by decide)⟩
  · refine WP.ite false (by simp [eval, hz, h8]) (by simp) (fun _ => ?_)
    refine WP.mono (redc_ok sa da ha hZ hw1 hw inv) fun t ⟨vt, ot, kt⟩ => ?_
    rw [hm] at vt ot
    exact ⟨vt, ot.mono (by omega) (by omega), (ka.trans kt).mono (by decide)⟩
end VG.Proof.Bignum.X86_64.AdxSquare
