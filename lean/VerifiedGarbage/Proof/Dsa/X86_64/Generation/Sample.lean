module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Sample
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TestWitness
public import VerifiedGarbage.Proof.Bignum.WorkFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadWitness
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRound
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessMont

/-! ### `Dsa.X86_64.Generation.Round`, which the modules that import this one used -/

section

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
  refine WP.seq (WP.mono (witnessMont_ok M h hd ho (by omega_using [hN]) ha) fun u ⟨hu, hxm, hf, hk⟩ => ?_)
  have hsp : u.gpr .rsp = s.gpr .rsp := hk.gpr (by decide)
  have hru : Caller.Room u B Z := ⟨by rw [hsp]; exact hr.size, by rw [hsp]; exact hr.disjoint⟩
  refine WP.mono (sharedRound_ok K hu hd hZ hru ho hN hxm) fun t ⟨ht, hflag, hft, kt⟩ => ?_
  rw [hsp] at hft
  exact ⟨ht, hflag, (hf.work.mono (fun r hr => List.mem_append_left _ hr)).trans
    (hft.mono (fun r hr => List.mem_append_right _ hr)), (hk.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Native DSA witness selection implements RSA's exact sampler -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Dsa.Generation

theorem sampleWitness_ok {B p : Addr} {Z w N : Nat} {mi : BitVec 64} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N mi bs s) (hd : MrDims B Z w) (hodd : N % 2 = 1)
    (hlen : 2 ≤ bs.length) (hmax : bs.length < 2 ^ 31) (hkw : (bs.length + 7) / 8 ≤ w)
    (hbits : Spec.RsaKeyGen.bitLength (N - 1) = 8 * bs.length) :
    WP isa (Impl.Dsa.X86_64.Generation.sampleWitness) s fun t =>
      ModulusReady t B Z w mi N ∧
      wv t.mem B (slot w aXm) w = (Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs)).1 ∧
      word t.mem B (8 * kU) = mask (Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs)).2 ∧
      WorkFrame B (testRanges w) [⟨p, bs.length⟩] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.sampleWitness
  refine WP.seq (WP.mono (testWitness_ok h hd hodd (by omega_using [hlen]) hmax hkw)
    fun u ⟨hu, hxu, huu, hzu, hfu, ku⟩ => ?_)
  refine WP.ite (!decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1))
    (by simp [eval, hzu]) (fun hbad => ?_) (fun hgood => ?_)
  · have hb : ¬ (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1) := by
      simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using hbad
    have hspec := forcedWitnessBytes_spec hlen hbits hb
    have hfl := forcedWitnessBytes_length hlen
    refine WP.seq (WP.mono (forceSample_ok hu hd hlen (by omega_using [hmax])) fun v ⟨hv, huv, hfv, kv⟩ => ?_)
    refine WP.mono (loadWitness_ok hv.ready hd (by decide) (by decide) hv.ptr hv.len hv.source
      (by rw [hfl]; omega_using [hlen]) (by rwa [hfl]) (by rwa [hfl])) fun t ⟨ht, hxt, hft, kt⟩ => ?_
    refine ⟨ht, ?_, ?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
    · simpa only [hspec] using hxt
    · rw [hft.word_eq (by rng_disj) (by change 248 ≤ 2 ^ 64; decide), huv, huu, hspec]
      simp [hb]
    · exact ((hfu.work).trans (hfv.mono (by simp))).trans
        (hft.work.mono (by simp [testRanges]))
  · have hg : 2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1 := by simpa using hgood
    have hfit : Spec.Rsa.os2ip bs < 2 ^ (8 * bs.length) := by
      rw [← VG.Proof.Bignum.pow256_eq]
      exact VG.Proof.Rsa.lt_of_os2ip bs
    have hspec : Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs) = (Spec.Rsa.os2ip bs, true) := by
      simp only [Spec.RsaKeyGen.witness, hbits, Nat.mod_eq_of_lt hfit, ite_eq_left hg]
    refine WP.block_nil ⟨hu.ready, ?_, ?_, hfu.work, ku⟩
    · simpa only [hspec] using hxu
    · rw [huu, hspec]; simp [hg]

end VG.Proof.Dsa.X86_64.Generation
