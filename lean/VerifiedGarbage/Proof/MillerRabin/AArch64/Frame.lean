module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Core
import VerifiedGarbage.Proof.Framework.Omega

/-! # The shared round preserves the prepared modulus and exponent -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.Impl.Bignum VG.Proof.Bignum VG.Proof.RsaKeyGen.AArch64
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Bignum.Public

theorem core_keeps {B : Addr} {n w : Nat} {m m' : Mem}
    (hn : 8 * n ≤ 2 ^ 64) (hf : Frm B (coreRanges w) m m') :
    Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B n w m m' := by
  intro i hi hh ha ht
  have h23h := hh 23 (by simp [Proof.MillerRabin.Round.compact])
  have h26h := hh 26 (by simp [Proof.MillerRabin.Round.compact])
  have h29h := hh 29 (by simp [Proof.MillerRabin.Round.compact])
  have h30h := hh 30 (by simp [Proof.MillerRabin.Round.compact])
  have h1h := hh 1 (by simp [Proof.MillerRabin.Round.compact])
  have h2a := ha 2 (by simp [Proof.MillerRabin.Round.compact])
  have h3a := ha 3 (by simp [Proof.MillerRabin.Round.compact])
  have h5a := ha 5 (by simp [Proof.MillerRabin.Round.compact])
  have h6a := ha 6 (by simp [Proof.MillerRabin.Round.compact])
  have h8a := ha 8 (by simp [Proof.MillerRabin.Round.compact])
  apply hf
  simp only [ofs, Mem.sub_ofNat_toNat B (by omega : i < 2 ^ 64)]
  intro r hr
  simp only [coreRanges, tabRanges, VG.Proof.RsaKeyGen.AArch64.expRanges, winRanges, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl)
  all_goals
    simp only [Proof.MillerRabin.Round.compact, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at ht
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at h2a h3a h5a h6a h8a
    simp only [slot, hdrBytes, aT0, aAcc, aTmp, aY, aXm, kG, kFlag, kPlen,
      kV, kT0, kBits, kT2, kWords, kT1, sFn, sCnt]
    omega_arith

end VG.Proof.MillerRabin.AArch64
