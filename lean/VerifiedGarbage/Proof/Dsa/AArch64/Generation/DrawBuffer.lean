module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeSlice
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleState
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawPrepared
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-! # A whole tape draw supplies the sampler and preserves all loop arguments -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaKeyGen.AArch64

theorem drawBuffer_ok {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeState P used s) (hroom : used + P.drawBytes ≤ P.rand.length) :
    WP isa (Impl.Dsa.AArch64.Generation.drawCopy P.len P.drawBytes) s fun t =>
      PrimeState P (used + P.drawBytes) t ∧
      SampleState P.B P.p P.Z P.w P.N (P.drawSlice used) t ∧
      WorkFrame P.B [(8 * kUsed, 8)] (primeExtras P) s.mem t.mem ∧ Keep mmRegs s t := by
  have hlen := P.slice_length hroom
  have hs : Src s P.B P.Z (off P.rp (used + (P.drawBytes - (P.drawSlice used).length))) (P.drawSlice used) := by
    rw [hlen]; exact h.slice_source hroom
  have hw : ∀ i < (P.drawSlice used).length, InRegions s.wr (off P.p i) 1 := by
    rw [hlen]; exact h.writable
  have hd := drawPrepared_ok h.ready P.exponentRoom
    (by rw [hlen]; exact P.lenDraw) (by have := P.drawMax; omega)
    h.rand h.used h.ptr hs hw (by rw [hlen]; exact P.bufferOutside)
    (by simpa only [hlen, PrimeParams.drawStart] using P.slice_separate hroom)
  rw [hlen] at hd
  refine WP.mono hd fun t ⟨ht, hbytes, hused, hf, hk⟩ => ?_
  have hft : WorkFrame P.B [(8 * kUsed, 8)] (primeExtras P) s.mem t.mem := by
    intro x hx hr
    exact hf x (fun r hmem => hx r (by
      simp only [List.mem_singleton] at hmem; subst r; simp [primeExtras])) hr
  have hzt : 256 ≤ P.Z := P.z256
  have hpt : PrimeState P (used + P.drawBytes) t := h.advance ht hused hft hk
    (by simp only [List.mem_singleton, forall_eq]; change 224 ≤ P.Z; omega)
    (by
      intro k hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨hpt, ⟨ht, hpt.ptr, ?_, ?_, ?_⟩, hft, hk⟩
  · rw [hlen]; exact hpt.len
  · refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => P.bufferOutside i (by rwa [hlen] at hi)⟩
    · obtain ⟨r, hr, hc⟩ := hpt.writable i (by rwa [hlen] at hi)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · have hb : t.mem (off P.p i) = (Spec.Rsa.bytesAt t.mem P.p P.len)[i]'(by rw [bytesAt_length]; rwa [hlen] at hi) := by
        simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, off]
      simpa only [hbytes] using hb
  · rw [hlen]; exact hpt.writable

end VG.Proof.Dsa.AArch64.Generation
