module

public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSq
import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified
import VerifiedGarbage.Proof.Framework.Omega

/-! # Existing Montgomery contexts satisfy the callable's prepared contract -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum.AArch64.MontFn (numAt_eq)

theorem ctx_width {s : State} {B : Addr} {Z w c bm : Nat} (hc : MrCtx s B Z w c bm) :
    Proof.Rsa.Mont.wOf s.mem B = w := by
  change (word s.mem B (8 * sW)).toNat = w
  rw [hc.ws.hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hc.ws.w2; omega_arith)]

theorem prepared_of_ctx {s : State} {B : Addr} {Z w c bm : Nat}
    (hc : MrCtx s B Z w c bm) (he : ECtx s.mem B w c)
    (ho : c % 2 = 1) (h3 : 3 ≤ c) (hx : wv s.mem B (slot w aXm) w < c) :
    Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.compact s.mem B := by
  have hw := ctx_width hc
  have hn : Proof.Rsa.Mont.numAt s.mem B w 0 = c := (numAt_eq s.mem B w 0).trans hc.n
  simp only [Proof.MillerRabin.Round.Prepared, hw, hn, Proof.MillerRabin.Round.compact]
  refine ⟨h3, ho, hc.inv, ?_, ?_, ?_, ?_, ?_⟩
  · rw [numAt_eq]
    exact hx
  · rw [numAt_eq]
    exact hc.r1
  · rw [numAt_eq]
    exact hc.rm1
  · rw [numAt_eq]
    simpa only [Proof.MillerRabin.Round.exponent, Proof.MillerRabin.Round.shift, mrE, mrSig, sigOf, mrA, aE] using he.e
  · exact he.l

theorem layout_of_ctx {s : State} {B : Addr} {Z w c bm : Nat}
    (hc : MrCtx s B Z w c bm) (h4 : 4 ≤ w) (h128 : w ≤ 128) :
    Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.compact s.mem B (32 + 28 * (w + 2)) := by
  simp only [Proof.MillerRabin.Round.Layout, ctx_width hc, Proof.MillerRabin.Round.compact,
    Proof.Rsa.Mont.Layout, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  refine ⟨Or.inr trivial, ⟨by omega_arith, by omega_arith, by omega_arith, ?_⟩,
    h4, h128, ?_, hc.ws.hS⟩
  · intro j hj
    exact hc.ws.harr j hj
  · change 256 + 28 * (8 * (w + 2)) ≤ 8 * (32 + 28 * (w + 2))
    omega_arith

end VG.Proof.MillerRabin.AArch64
