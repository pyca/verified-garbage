module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRound
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessMont

/-! # DSA invokes the same verified windowed Miller–Rabin round as RSA -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem round_ok (M : Mont) (K : Kernel) {s : State} {B : Addr} {Z w N a : Nat} {mi : BitVec 64}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w) (hZ : slot w 28 ≤ Z) (hr : Caller.Room s B Z)
    (ho : N % 2 = 1) (hN : 3 ≤ N) (ha : wv s.mem B (slot w aXm) w = a) :
    WP isa (Impl.Ffdh.X86_64.ParameterCandidate.witnessRound M.mm K.run) s fun t =>
      ModulusReady t B Z w mi N ∧
      word t.mem B (8 * kFlag) = mask (Spec.RsaKeyGen.mrIteration N
        (Spec.Rsa.splitTwos (N - 1)).1 (Spec.Rsa.splitTwos (N - 1)).2 a) ∧
      WorkFrame B (witnessRoundRanges w) [below (s.gpr .rsp) 128] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Ffdh.X86_64.ParameterCandidate.witnessRound
  refine WP.seq (WP.mono (witnessMont_ok M h hd ho (by omega) ha) fun u ⟨hu, hxm, hf, hk⟩ => ?_)
  have hsp : u.gpr .rsp = s.gpr .rsp := hk.gpr (by decide)
  have hru : Caller.Room u B Z := ⟨by rw [hsp]; exact hr.size, by rw [hsp]; exact hr.disjoint⟩
  refine WP.mono (sharedRound_ok K hu hd hZ hru ho hN hxm) fun t ⟨ht, hflag, hft, kt⟩ => ?_
  rw [hsp] at hft
  exact ⟨ht, hflag, (hf.work.mono (fun r hr => List.mem_append_left _ hr)).trans
    (hft.mono (fun r hr => List.mem_append_right _ hr)), (hk.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
