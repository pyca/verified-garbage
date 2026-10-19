module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyR1CT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2CT

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NegateR1CT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NegateR1CT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # Constant-time derivation of the prepared Montgomery constants -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64

def PrimeR2Ready (p : PrimeParams) (s : State) : Prop :=
  ∃ mi, ModCtx s p.B p.Z p.w mi p.N ∧ wv s.mem p.B (slot p.w aOne) p.w = 1 ∧
    wv s.mem p.B (slot p.w aR2) p.w = 2 ^ (64 * p.w) * 2 ^ (64 * p.w) % p.N

theorem primeR2_ready (M : Mont) {p : PrimeParams} {s : State} (h : PrimeSetupBefore p s) :
    WP isa (Impl.Dsa.X86_64.Generation.primeR2 M.mm) s (PrimeR2Ready p) := by
  obtain ⟨mi, hg⟩ := h.1
  exact WP.mono (primeR2_ok M hg p.dims.z (by have := p.dims.w4; omega) h.2.2 h.2.1 p.odd
    (by have := p.n3; omega)) fun _ ⟨mi', ht, hi, hn, hone, hr2, _⟩ =>
      ⟨mi', ⟨ht, hn, hi⟩, hone, hr2⟩

theorem primeMontOne_good (M : Mont) {p : PrimeParams} {s : State} (h : PrimeR2Ready p s) :
    WP isa (M.mm aY aR2 aOne) s (PrimeGood p) := by
  obtain ⟨mi, h, hone, _⟩ := h
  exact WP.mono (M.mm_ok h.good p.dims.z (by have := p.dims.w4; omega)
    (by have := p.dims.w128; omega) (o := aY) (a := aR2) (b := aOne)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h.inverse (by rw [hone, h.modulus]; have := p.n3; omega)) fun _ ht => ⟨mi, ht.1⟩

theorem primeConstants_ct (M : Mont) : RelCT isa (Two PrimeR2Ready)
    (Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants M.mm) (fun _ _ => True) := by
  unfold Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants
  refine RelCT.seq (two_post
    (two_map (fun p : PrimeParams => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun p s h => by
      obtain ⟨mi, h, _⟩ := h; exact ⟨mi, h.good, p.dims.z⟩)
      (M.ct (o := aY) (a := aR2) (b := aOne) (by unfold MmUse; decide)))
    (fun _ _ h => primeMontOne_good M h)) ?_
  exact RelCT.seq (two_post copyR1_ct (fun _ _ h => copyR1_good h)) negateR1_ct

end VG.Proof.Dsa.X86_64.Generation
