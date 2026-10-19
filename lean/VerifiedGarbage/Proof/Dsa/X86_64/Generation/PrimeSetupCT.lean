module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ExponentCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ExponentCT
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-! # Constant-time preparation of every shared primality-round input -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem primeConstants_exponent (M : Mont) {p : PrimeParams} {s : State} (h : PrimeR2Ready p s) :
    WP isa (Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants M.mm) s (ExponentBefore p) := by
  obtain ⟨mi, h, hone, hr2⟩ := h
  have hnw := h.good.scr.nowrap
  have hNfit := Nat.le_trans (slot_le (w := p.w) (show aN < 8 by decide)) p.dims.z
  refine WP.mono (prepareConstants_ok M h.good p.dims.z p.dims.x
    (by have := p.dims.w4; omega) (by have := p.dims.w128; omega) h.modulus h.inverse
    hone p.odd (by have := p.n3; omega) hr2) fun t ⟨ht, _, _, hf, _⟩ => ?_
  refine ⟨⟨mi, ht⟩, ?_⟩
  rw [hf.wv_eq (by simp only [constantRanges]; rng_disj) (by omega)]
  exact h.modulus

theorem primeSetup_ct (M : Mont) : RelCT isa (Two PrimeSetupBefore)
    (Impl.Dsa.X86_64.Generation.primeSetup M.mm) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.primeSetup
  exact RelCT.seq (two_post (primeR2_ct M) (fun _ _ h => primeR2_ready M h))
    (RelCT.seq (two_post (primeConstants_ct M) (fun _ _ h => primeConstants_exponent M h)) primeExponent_ct)

end VG.Proof.Dsa.X86_64.Generation
