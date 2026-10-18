module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetup
public import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Framework.Omega

/-! External tape and witness writes preserve all prepared workspace words. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64

theorem ModulusReady.of_words {s t : State} {B : Addr} {Z w N : Nat}
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hm : ∀ d, d + 8 ≤ Z → word t.mem B d = word s.mem B d)
    (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = B) : ModulusReady t B Z w N := by
  have h256 := h.ws.h256
  have hw := h.ws.w1
  have fixed (a : Nat) (ha : a < 16) : wv t.mem B (slot w a) w = wv s.mem B (slot w a) w := by
    have hb := h.ws.sl ha
    exact wv_congr fun i hi => hm _ (by omega)
  refine ⟨⟨h.ws.scr.congr hwr, h0,
    (hm _ (by simp only [sW]; omega)).trans h.ws.hw,
    (hm _ (by simp only [sStride, sFn]; omega)).trans h.ws.hS,
    fun j hj => (hm _ (by simp only [sArr]; omega)).trans (h.ws.harr j hj),
    h.ws.hZ, h.ws.w1, h.ws.w2⟩, ?_, (fixed aN (by decide)).trans h.modulus,
    (fixed aOne (by decide)).trans h.one, (fixed aR2 (by decide)).trans h.r2,
    (fixed aR1 (by decide)).trans h.r1, (fixed aRm1 (by decide)).trans h.rm1, ⟨?_, ?_⟩⟩
  · rw [hm _ (by have := h.ws.sl (show aN < 16 by decide); omega),
      hm _ (by simp only [sMinv]; omega)]
    exact h.inverse
  · have he : wv t.mem B (slot w aE) w = wv s.mem B (slot w aE) w :=
      wv_congr fun i hi => hm _ (by omega)
    exact he.trans h.exponent.e
  · exact (hm (slot w aE + 8 * w) (by omega)).trans h.exponent.l

end VG.Proof.Dsa.AArch64.Generation
