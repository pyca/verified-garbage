module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeSetup
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MontPrep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup

/-! Prepare R² and the inverse without a nonzero-top-limb assumption. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Proof.Ffdh.AArch64.ParameterCandidate
open VG.Proof.MlKem.AArch64 (Keep)

theorem primeR2_ok (M : Mont) {s : State} {B : Addr} {Z w N : Nat}
    (h : Ws s B Z w) (hw48 : w ≤ 48)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hN1 : 1 < N) :
    WP isa (Impl.Dsa.AArch64.Generation.primeR2 M.mm) s fun t =>
      Ws t B Z w ∧
      ((word t.mem B (slot w aN)).toNat * (word t.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
      wv t.mem B (slot w aN) w = N ∧
      wv t.mem B (slot w aOne) w = 1 ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (mpRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := h.scr.nowrap
  have hZ := h.hZ
  have hZ16 : 256 + 16 * (8 * (w + 2)) ≤ Z := by simpa only [slot, hdrBytes] using hZ
  have hodd0 : (word s.mem B (slot w aN)).toNat % 2 = 1 := by
    have e := wv_add s.mem B (slot w aN) 1 (w - 1)
    rw [show 1 + (w - 1) = w by have := h.w1; omega, hn] at e
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e
    omega
  unfold Impl.Dsa.AArch64.Generation.primeR2
  refine WP.seq (WP.mono (msHead_ok h hodd0) fun u ⟨⟨hinv, hm, _, _, _⟩, ku⟩ => ?_)
  have ou : Outside B (8 * sMinv) 8 s.mem u.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by simp only [sMinv]; omega)
  have fu : Frm B (mpRanges w) s.mem u.mem := Frm.of_outside ou (by simp [mpRanges])
  have hu : Ws u B Z w := h.congr' fu (mpRanges_kmut w) ku (by decide)
  have hnu : wv u.mem B (slot w aN) w = N := by
    rw [ou.wv (by simp only [slot, hdrBytes, aN, sMinv]; omega)
      (by simp only [slot, hdrBytes, aN]; omega)]; exact hn
  have hword : word u.mem B (slot w aN) = word s.mem B (slot w aN) :=
    ou.word (by simp only [slot, hdrBytes, aN, sMinv]; omega)
      (by simp only [slot, hdrBytes, aN]; omega)
  refine WP.mono (constants_ok M hu.good.1 hu.good.2 h.w1 hw48 hnu hN1 hodd
    (by rw [hword]; exact hinv)) fun t ⟨_, hone, hr2, ft, kt⟩ => ?_
  have ft' : Frm B (mpTail w) u.mem t.mem := ft.mono (by simp [mpTail, r2Ranges])
  obtain ⟨he, hw, hv⟩ := mp_fix ft' hnw hZ
  refine ⟨hu.congr' ft' (mpTail_kmut w) kt (by decide), ?_, hv.trans hnu, hone, ?_,
    fu.trans (ft'.mono fun r hr => List.mem_cons_of_mem _ hr), (ku.trans kt).mono (by decide)⟩
  · rw [hw, he, hword]; exact hinv
  · rw [← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega]
    exact hr2

end VG.Proof.Dsa.AArch64.Generation
