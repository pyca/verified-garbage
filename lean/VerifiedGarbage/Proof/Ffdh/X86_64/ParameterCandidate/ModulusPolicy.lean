module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseRounds
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareState
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: the shared complete modulus policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

theorem modulusPolicy_ok (M : Mont) (R : R2Impl M) (K : Kernel)
    {p : CandidateP} {used : Nat} {q : Bool} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s)
    (hg : Good s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi)
    (hp : PhaseHeader p q s)
    (hn : wv s.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q)
    (ho : p.phaseValue q % 2 = 1) :
    WP isa (modulusPolicy M.mm R.code K.run) s (PhaseRoundsPost p used q s) := by
  unfold modulusPolicy
  refine WP.seq (WP.mono (prepareModulus_state_ok M R h hg hp hn ho)
    fun u ⟨mi', hu, hr, hp', hs, hf, ku⟩ => ?_)
  refine WP.mono (rounds_state_ok M K hu hp' ho hr)
    fun t ⟨n, hn', ht, hdi, hl, hresult, hs', hf', kt⟩ => ?_
  exact ⟨n, hn', ht, hdi, hl, hresult, hs.trans hs', hf.trans hf', (ku.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
