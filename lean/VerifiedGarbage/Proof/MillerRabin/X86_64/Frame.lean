module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Core
import VerifiedGarbage.Proof.Framework.Omega

/-! # The shared round preserves the prepared modulus and exponent -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.Impl.Bignum VG.Proof.Bignum VG.Proof.RsaKeyGen.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.Bignum.Public
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

theorem core_keeps {B : Addr} {n w : Nat} {m m' : Mem}
    (hn : 8 * n ≤ 2 ^ 64) (hf : Frm B (coreRanges w) m m') :
    Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B n w m m' := by
  intro i hi hh ha ht
  have h22h := hh 22 (by simp [Proof.MillerRabin.Round.extended])
  have h26h := hh 26 (by simp [Proof.MillerRabin.Round.extended])
  have h27h := hh 27 (by simp [Proof.MillerRabin.Round.extended])
  have h28h := hh 28 (by simp [Proof.MillerRabin.Round.extended])
  have h31h := hh 31 (by simp [Proof.MillerRabin.Round.extended])
  have h2a := ha 2 (by simp [Proof.MillerRabin.Round.extended])
  have h3a := ha 3 (by simp [Proof.MillerRabin.Round.extended])
  have h5a := ha 5 (by simp [Proof.MillerRabin.Round.extended])
  have h6a := ha 6 (by simp [Proof.MillerRabin.Round.extended])
  have h9a := ha 9 (by simp [Proof.MillerRabin.Round.extended])
  apply hf
  simp only [ofs, Mem.sub_ofNat_toNat B (by omega : i < 2 ^ 64)]
  intro r hr
  simp only [coreRanges, tabRanges, VG.Proof.RsaKeyGen.X86_64.expRanges, winRanges, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl)
  all_goals
    simp only [Proof.MillerRabin.Round.extended, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at ht
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at h2a h3a h5a h6a h9a
    simp only [slot, hdrBytes, tabBytes, aAcc, aTmp, aY, aXm, kG, kFlag, kPlen,
      kV, kT0, kBits, kT2, kWords, kT1, sFn]
    omega_arith

end VG.Proof.MillerRabin.X86_64
