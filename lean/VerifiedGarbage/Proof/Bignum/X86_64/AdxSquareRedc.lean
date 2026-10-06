import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcLoop
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep

/-! Montgomery reduction of the square, before its final subtraction. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem redcSetup_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block AdxSquare.redcSetup) s fun t =>
      t.gpr .r8 = off B (slot w aAcc + 16) ∧ t.gpr .r9 = off B (slot w aN) ∧
      t.gpr .rbp = BitVec.ofNat 64 w ∧ t.gpr .r10 = 0 ∧ t.mem = s.mem ∧ Keep [.r8, .r9, .rbp, .r10] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.r8, .r9, .rbp, .r10] (Q := fun t =>
      t.gpr .r8 = off B (slot w aAcc + 16) ∧ t.gpr .r9 = off B (slot w aN) ∧
      t.gpr .rbp = BitVec.ofNat 64 w ∧ t.gpr .r10 = 0 ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold AdxSquare.redcSetup
  xrun [State.ea, hdr, hdi, hdrOff, hl (sArr aAcc) (by decide), hl (sArr aN) (by decide), hl sW (by decide),
    hH.harr aAcc (by decide), hH.harr aN (by decide), hH.hw, off_add16]

theorem redcFinish_ok {s : State} {B : Addr} {Z e w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (hbp : s.gpr .rbp = BitVec.ofNat 64 w) (hZ : e + 8 * (w + 2) ≤ Z) :
    WP isa (.block AdxSquare.redcFinish) s fun t =>
      wv t.mem B e (w + 2) = wv s.mem B e w + 2 ^ (64 * w) * (s.gpr .r10).toNat ∧
      Outside B (e + 8 * w) 16 s.mem t.mem ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = (s.mem.writeW (off B (e + 8 * w)) (s.gpr .r10)).writeW (off B (e + 8 * w + 8)) (0 : BitVec 64)) ?_ rfl)
    fun t ⟨hm, kt⟩ => ?_
  · unfold AdxSquare.redcFinish
    xrun [State.ea, ix, addr0 h8 hbp, addr8 h8 hbp,
      hs.st (show e + 8 * w + 8 ≤ Z by omega), hs.st (show e + 8 * w + 8 + 8 ≤ Z by omega)]
    rfl
  · obtain ⟨hv, ho⟩ := write2 s.mem B (e + 8 * w) (s.gpr .r10) 0 (by omega)
    rw [← hm] at hv ho
    refine ⟨?_, ho, kt⟩
    rw [wv_add, hv, ho.wv (by omega) (by omega)]
    simp

/-- REDC's exact relation: the result times the Montgomery radix is the
input plus a multiple `q < R` of the modulus. -/
theorem redc_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa AdxSquare.redc s fun t =>
      (∃ q < 2 ^ (64 * w), 2 ^ (64 * w) * wv t.mem B (slot w aTmp) (w + 2) =
        wv s.mem B (slot w aAcc + 16) (2 * w) + q * wv s.mem B (slot w aN) w) ∧
      Outside B (slot w aAcc + 16) (8 * (2 * w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have hA := slot_le (w := w) (show aTmp < 8 by decide)
  have hAT : slot w aAcc + 16 + 8 * w = slot w aTmp := by unfold slot aAcc aTmp; omega
  unfold AdxSquare.redc
  refine WP.seq (WP.mono (redcSetup_ok hs hdi hH hZ) fun s₁ ⟨h8, h9, hbp, h10, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (redcRows_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi)
    (hm₁ ▸ hH) hZ h8 h9 hbp h10 hw1 hw (by rw [hm₁]; exact hinv)) fun s₂ hI => ?_)
  have h8₂ := hI.r8
  rw [hAT] at h8₂
  have k12 := k₁.trans hI.keep
  refine WP.mono (redcFinish_ok hI.scr h8₂ ((hI.keep.gpr (by decide)).trans hbp) (by omega))
    fun t ⟨hv, ho, kt⟩ => ?_
  obtain ⟨q, hq, heq⟩ := hI.val
  rw [hAT, show 2 * w - w = w by omega, hm₁] at heq
  have o₁ := hI.out
  rw [hm₁] at o₁
  refine ⟨⟨q, hq, ?_⟩, ?_, (k12.trans kt).mono (by decide)⟩
  · rw [hv]; exact heq
  · exact (o₁.mono (o' := slot w aAcc + 16) (n' := 8 * (2 * w + 2)) (Nat.le_refl _) (by omega)).trans
      (ho.mono (o' := slot w aAcc + 16) (n' := 8 * (2 * w + 2)) (by omega) (by omega))

end VG.Proof.Bignum.X86_64.AdxSquare
