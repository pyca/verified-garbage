module
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Contract
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Round
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.MillerRabin.AArch64.Context
import VerifiedGarbage.Proof.MillerRabin.AArch64.Finish
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified
import VerifiedGarbage.Proof.MillerRabin.AArch64.Frame

/-! # Correctness of the callable prepared round on AArch64 -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.MillerRabin.AArch64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.MontFn (numAt_eq)

private theorem result32 (p : Bool) :
    ((BitVec.ofNat 64 p.toNat).setWidth 32).toNat = if p then 1 else 0 := by
  cases p <;> decide

private theorem exponent_fits {s : State} {B : Addr} {Z w c bm : Nat}
    (h : MrCtx s B Z w c bm) : mrE c < 16 ^ (16 * w) := by
  change mrE c < (2 ^ 4) ^ (16 * w)
  rw [← Nat.pow_mul,
    show 4 * (16 * w) = 64 * w by omega_arith]
  have hc : c < 2 ^ (64 * w) := h.n ▸ wv_lt s.mem B (slot w aN) w
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hc)

theorem round_correct (M : Mont) (s : State) (h : roundContract.pre s) :
    ∃ tr t, Exec isa (round M.mm) s tr t ∧ abiPreserved s t ∧ roundContract.post s t := by
  obtain ⟨h4, h128, hEZ, bm, hc, hE, hodd, h3, hx⟩ := initial_ctx h
  let B := s.gpr .x0
  let w := Proof.Rsa.Mont.wOf s.mem B
  let c := Proof.Rsa.Mont.numAt s.mem B w 0
  have hR := coprime_pow2 hodd (64 * w)
  obtain ⟨b, -, hb⟩ := witness_exists hR hx
  have hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c := by
    simpa only [VG.Proof.Bignum.powMod_eq, Nat.pow_one] using hb
  suffices hw : WP isa (round M.mm) s fun t => abiPreserved s t ∧ roundPost s t by
    obtain ⟨tr, t, he, ha, hp⟩ := hw
    exact ⟨tr, t, he, ha, hp⟩
  unfold VG.Impl.MillerRabin.AArch64.round
  refine WP.seq (WP.mono (core_ok M h128 hEZ hc hE hodd h3 (exponent_fits hc) hX)
    fun t ⟨ht, _, hp, hf, hk⟩ => ?_)
  refine WP.mono (returnFlag_ok ht.ws hp) fun u ⟨hm, hr, ku⟩ => ⟨?_, ?_⟩
  · have k := hk.trans ku
    exact ⟨fun r hmem => k.gpr r (by revert r; decide), k.sp, k.vcs⟩
  · refine ⟨?_, ?_⟩
    · intro b' hb'
      have hm' : Proof.MillerRabin.Round.round c b = Proof.MillerRabin.Round.round c b' := by
        apply round_eq_of_mont (by have hc3 : 3 ≤ c := h3; omega_arith : 0 < c) hR
        rw [← hb, ← hb']
        exact (numAt_eq s.mem B w aXm).symm
      rw [hr, result32, hm']
    · rw [hm]
      exact core_keeps (by have := hc.ws.scr.nowrap; change 8 * (s.gpr .x1).toNat ≤ 2 ^ 64; omega_arith) hf

end VG.Proof.MillerRabin.AArch64
