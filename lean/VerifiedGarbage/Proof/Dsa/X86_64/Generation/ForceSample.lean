module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleState
public import VerifiedGarbage.Proof.Bignum.WorkFrame
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Memory
import VerifiedGarbage.Proof.Framework.Omega

/-! # The forced branch replaces the draw while preserving the uniform flag -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Dsa.Generation

theorem forceSample_ok {B p : Addr} {Z w N : Nat} {mi : BitVec 64} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N mi bs s) (hd : MrDims B Z w)
    (hlen : 2 ≤ bs.length) (hmax : bs.length < 2 ^ 32) :
    WP isa (Impl.Dsa.X86_64.Generation.forceStoredWitness kOut bs.length) s fun t =>
      SampleState B p Z w N mi (forcedWitnessBytes bs) t ∧
      word t.mem B (8 * kU) = word s.mem B (8 * kU) ∧
      WorkFrame B [] [⟨p, bs.length⟩] s.mem t.mem ∧ Keep [.rax, .rbx] s t := by
  have hz : 256 ≤ Z := by have := hd.z; simp only [slot, hdrBytes] at this; omega
  have hfl := forcedWitnessBytes_length hlen
  refine WP.mono (forceStoredWitness_ok h.ready hd (by decide) h.ptr hlen hmax h.writable h.source.out)
    fun t ⟨ht, hbytes, hf, hwords, hk⟩ => ?_
  rw [h.bytes] at hbytes
  refine ⟨⟨ht, (hwords _ (by change 136 ≤ Z; omega)).trans h.ptr,
    ?_, ?_, ?_⟩, hwords _ (by change 248 ≤ Z; omega), ?_, hk⟩
  · rw [hfl, hwords _ (by change 152 ≤ Z; omega)]; exact h.len
  · refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => h.source.out i (by rwa [hfl] at hi)⟩
    · rw [hk.2.1, hk.2.2]
      exact h.source.rd i (by rwa [hfl] at hi)
    · have hi' : i < bs.length := by rwa [hfl] at hi
      have hb := bytesAt_read t.mem p hi'
      simpa only [hbytes] using hb
  · intro i hi
    rw [hk.2.2]
    exact h.writable i (by rwa [hfl] at hi)
  · intro x hx _
    apply hf
    intro i hi he
    subst x
    apply hx ⟨p, bs.length⟩ (by simp)
    apply (Region.contains_self p bs.length).byte
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
    exact hi

end VG.Proof.Dsa.X86_64.Generation
