module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleState
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.StoredWitness
public import VerifiedGarbage.Proof.Bignum.WorkFrame
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Sample
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith

/-! The forced branch changes the draw and preserves its nonuniform flag. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Proof.Dsa.Generation

theorem forceSample_ok {B p : Addr} {Z w N : Nat} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N bs s) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hlen : 2 ≤ bs.length) (hmax : bs.length < 4096) :
    WP isa (Impl.Dsa.AArch64.Generation.forceStoredWitness bs.length) s fun t =>
      SampleState B p Z w N (forcedWitnessBytes bs) t ∧
      word t.mem B (8 * kU) = word s.mem B (8 * kU) ∧
      WorkFrame B [] [⟨p, bs.length⟩] s.mem t.mem ∧ Keep [.x1, .x3, .x4] s t := by
  have hz := h.ready.ws.h256
  have hfl := forcedWitnessBytes_length hlen
  refine WP.mono (forceStoredWitness_ok h.ready hEZ h.ptr hlen hmax h.writable h.source.out)
    fun t ⟨ht, hbytes, hf, hwords, hk⟩ => ?_
  rw [h.bytes] at hbytes
  refine ⟨⟨ht, (hwords _ (by simp only [kOut, sFn]; omega)).trans h.ptr,
    ?_, ?_, ?_⟩, hwords _ (by simp only [kU]; omega), ?_, hk⟩
  · rw [hfl, hwords _ (by simp only [kUsedP, sFn]; omega)]; exact h.len
  · refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => h.source.out i (by rwa [hfl] at hi)⟩
    · rw [hk.rd, hk.wr]
      exact h.source.rd i (by rwa [hfl] at hi)
    · have hi' : i < bs.length := by rwa [hfl] at hi
      have hb : t.mem (off p i) = (Spec.Rsa.bytesAt t.mem p bs.length)[i]'(by simpa only [bytesAt_length] using hi') := by
        simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, off]
      simpa only [hbytes] using hb
  · intro i hi
    rw [hk.wr]
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

end VG.Proof.Dsa.AArch64.Generation
