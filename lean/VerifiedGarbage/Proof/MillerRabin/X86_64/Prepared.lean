module

public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Existing Montgomery contexts satisfy the callable's prepared contract -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum.X86_64.MontFn (numAt_eq)

theorem ctx_width {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64} (hc : MrCtx s B Z w mi c bm) (h128 : w ≤ 128) :
    Proof.Rsa.Mont.wOf s.mem B = w := by
  change (word s.mem B (8 * sW)).toNat = w
  rw [hc.good.hdr.hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]

theorem prepared_of_ctx {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (h128 : w ≤ 128)
    (ho : c % 2 = 1) (h3 : 3 ≤ c) (hx : wv s.mem B (slot w aXm) w < c) :
    Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.extended s.mem B := by
  have hw := ctx_width hc h128
  have hn : Proof.Rsa.Mont.numAt s.mem B w 0 = c := (numAt_eq s.mem B w 0).trans hc.n
  simp only [Proof.MillerRabin.Round.Prepared, hw, hn, Proof.MillerRabin.Round.extended]
  refine ⟨h3, ho, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((word s.mem B (slot w aN)).toNat * (word s.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0
    rw [hc.good.hdr.hminv]
    exact hc.inv
  · rw [numAt_eq]
    exact hx
  · rw [numAt_eq]
    exact hc.r1
  · rw [numAt_eq]
    exact hc.rm1
  · rw [numAt_eq]
    simpa only [Proof.MillerRabin.Round.exponent, Proof.MillerRabin.Round.shift, mrE, mrSig, sigOf, mrA, aE] using he.e
  · exact he.l

theorem layout_of_ctx {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (h4 : 4 ≤ w) (h128 : w ≤ 128) :
    Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.extended s.mem B (32 + 28 * (w + 2)) := by
  simp only [Proof.MillerRabin.Round.Layout, ctx_width hc h128, Proof.MillerRabin.Round.extended,
    Proof.Rsa.Mont.Layout, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  refine ⟨Or.inl trivial, ⟨by omega_arith, by omega_arith, by omega_arith, ?_⟩,
    h4, h128, ?_, True.intro⟩
  · intro j hj
    exact hc.good.hdr.harr j hj
  · change 256 + 27 * (8 * (w + 2)) ≤ 8 * (32 + 28 * (w + 2))
    omega_arith

end VG.Proof.MillerRabin.X86_64
