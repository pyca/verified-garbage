module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeSlice
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleState
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Memory
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopy
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # A whole tape draw supplies the sampler and preserves all loop arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem drawBuffer_ok {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeState P mi used s) (hroom : used + P.drawBytes ≤ P.rand.length) :
    WP isa (Impl.Dsa.X86_64.Generation.drawCopy) s fun t =>
      PrimeState P mi (used + P.drawBytes) t ∧
      SampleState P.B P.p P.Z P.w P.N mi (P.drawSlice used) t ∧
      WorkFrame P.B [(8 * kUsed, 8)] (primeExtras P) s.mem t.mem ∧ Keep mmRegs s t := by
  have hlen := P.slice_length hroom
  have hs : Src s P.B P.Z (off P.rp (used + (P.drawBytes - (P.drawSlice used).length))) (P.drawSlice used) := by
    rw [hlen]; exact h.slice_source
  have hw : ∀ i < (P.drawSlice used).length, InRegions s.wr (off P.p i) 1 := by
    rw [hlen]; exact h.writable
  have hout : Region.Disjoint ⟨P.B, P.Z⟩ ⟨P.p, (P.drawSlice used).length⟩ := by
    rw [hlen]; exact P.bufferSeparate
  have hd := drawCopy_ok h.ready P.dims (by rw [hlen]; exact P.len2)
    (by rw [hlen]; exact P.lenDraw) P.drawMax h.rand h.ptr h.used h.draw (by rw [hlen]; exact h.len) hs hw hout (by simpa only [hlen, PrimeParams.drawStart] using P.slice_separate hroom)
  rw [hlen] at hd
  refine WP.mono hd fun t ⟨ht, hbytes, hused, hf, hk⟩ => ?_
  have hft : WorkFrame P.B [(8 * kUsed, 8)] (primeExtras P) s.mem t.mem := by
    intro x hx hr
    exact hf x (fun r hmem => hx r (by
      simp only [List.mem_singleton] at hmem; subst r; simp [primeExtras])) hr
  have hzt : 256 ≤ P.Z := P.z256
  have hpt : PrimeState P mi (used + P.drawBytes) t := h.advance ht hused hft hk
    (by simp only [List.mem_singleton, forall_eq]; change 208 ≤ P.Z; omega)
    (by
      intro k hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj)
  refine ⟨hpt, ⟨ht, hpt.ptr, ?_, ?_, ?_⟩, hft, hk⟩
  · rw [hlen]; exact hpt.len
  · refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => P.bufferOutside i (by rwa [hlen] at hi)⟩
    · obtain ⟨r, hr, hc⟩ := hpt.writable i (by rwa [hlen] at hi)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · have hb := bytesAt_read t.mem P.p (n := P.len) (i := i) (by rwa [hlen] at hi)
      simpa only [hbytes] using hb
  · rw [hlen]; exact hpt.writable

end VG.Proof.Dsa.X86_64.Generation
