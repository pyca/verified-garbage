module

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedRound
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
import VerifiedGarbage.Proof.Framework.Omega

/-! # Constant time of RSA's round with a shared prepared kernel -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MillerRabin.AArch64 (Kernel)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)

private def RoundReady (p : RP) :=
  VG.Proof.MillerRabin.AArch64.Caller.Before ⟨p.L.B, p.L.Z, p.L.w⟩

private theorem prefix_ct (M : Mont) : RelCT isa (Two R0)
    (seqs (mrWitness ++ ([M.mm aXm aX aR2, copyA aB aXm] : List (Prog isa)))) (Two RoundReady) := by
  refine two_post (ct_app' (by simp [mrWitness]) (by simp)
    witP1_ct (by
      simpa only [seqs] using (RelCT.seq (preMul_ct M) copyB_ct).mono
        (fun _ _ h => h) (fun _ _ _ => True.intro))) ?_
  rintro p s ⟨h4, h128, hEZ, c, bm, r, i, uni, ch, hc, he, hR2, hc1, hsh, hR, hU, hK, hsrc, hlen, -⟩
  obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_arith) hsh
  have hn := hc.ws.scr.nowrap
  refine WP.mono (sharedWitness_ok M h4 h128 hc hR2 hsh.1 hc1 hb hR hU hK hsrc hlen) ?_
  rintro t ⟨hct, hx, _, _, _, hf, _⟩
  refine ⟨h4, h128, hEZ, c, _, (wtOf c p.L.w p.u r).1, hct,
    he.of_frm hf (fun r hr => Or.inr ?_) (by omega_arith), hsh.1, by have := hsh.1; omega_arith, ?_⟩
  · apply roundRanges_lt p.L.w r
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))
  · simpa only [wtOf, Nat.mod_mul_mod] using hx

private theorem mid_ct (M : Mont) (R : Kernel) : RelCT isa (Two R0)
    (seqs ((mrWitness ++ ([M.mm aXm aX aR2, copyA aB aXm] : List (Prog isa))) ++ R.run)) (Two Rmid) := by
  refine two_post (ct_app' (by simp [mrWitness]) R.nonempty (prefix_ct M)
    (two_map (fun p : RP => (⟨p.L.B, p.L.Z, p.L.w⟩ : VG.Proof.Bignum.AArch64.Ws))
      (fun _ _ h => h) R.ct)) ?_
  rintro p s ⟨h4, h128, hEZ, c, bm, r, i, uni, ch, hc, he, hR2, hc1, hsh, hR, hU, hK, hsrc, hlen, hI, hN, hC, _, _, _, hp⟩
  exact WP.mono (sharedMid_ok M R h4 h128 hEZ hc he hR2 hc1 hsh hR hU hK hsrc hlen hI hN hC)
    fun t ⟨⟨_, hct⟩, _, hf, _⟩ => ⟨hct.ws, by rw [hf, hp]⟩

theorem sharedRound_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two R0) (seqs (mrRoundWith M.mm R.run)) fun _ _ => True := by
  simp only [mrRoundWith]
  exact ct_app' (by simp [mrWitness]) (by simp) (mid_ct M R) roundTail_ct

end VG.Proof.RsaKeyGen.AArch64
