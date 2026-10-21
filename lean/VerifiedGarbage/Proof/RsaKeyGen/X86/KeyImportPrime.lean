module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadFrames
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.Framework.Omega

/-! # Prime import through the retained public key arguments -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem Input.importPrime {E : Environment} {s : State} {i out : Nat}
    (h : Input E s) (index : i = 2 ∨ i = 3) (ho : out < 32) (persistent : 15 ≤ out) :
    WP isa (loadPrime E.n (8 * i) out) s fun t =>
      Input E t ∧ Frame [E.workspaceRegion] s.mem t.mem ∧
      num t.mem E.base E.n out = Spec.Rsa.os2ip
        (Spec.Rsa.bytesAt s.mem (E.outputRegion i).base (E.outputRegion i).len) ∧
      num t.mem E.base E.n out < 2 ^ (32 * E.k) ∧
      (∀ j, 1 ≤ j → j < 32 → j ≠ out → num t.mem E.base E.n j = num s.mem E.base E.n j) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have widths := h.valid.widths
  have hi : i < 7 := by omega
  have len : E.outputLength i = 4 * E.k := by
    unfold Environment.outputLength
    split <;> omega
  have pointer : s.mem.readW (off E.base (8 * i)) 32 = E.out i := by
    have H := h.arguments (2 * i) (by omega)
    rw [show 4 * (2 * i) = 8 * i by omega] at H
    rcases index with rfl | rfl <;> exact H
  have readable : InRegions (s.rd ++ s.wr) ((E.out i).setWidth 64) (4 * E.k) := by
    obtain ⟨r, hr, contains⟩ := h.outWrite i hi
    refine ⟨r, List.mem_append_right _ hr, ?_⟩
    change r.Contains ((E.out i).setWidth 64) (E.outputLength i) at contains
    rwa [len] at contains
  refine WP.mono (loadPrime_ok h.ws widths.2.2.1 widths.2.2.2.1
    (by rcases index with rfl | rfl <;> decide) ho persistent pointer
    (by rw [← len]; exact h.valid.outFit i hi) readable
    (by simpa only [Environment.outputRegion, Environment.workspaceRegion, len] using h.valid.outputScratch i hi))
    fun t ⟨ht, O, value, bound, K⟩ => ?_
  have small : E.k ≤ E.n := by omega
  have frame := loadPrime_stage_frame small O
  refine ⟨h.afterStage ht K frame, stage_scratch_frame h.ws (by simp only [List.mem_singleton]; rintro j rfl; exact ho) frame,
    ?_, bound, ?_, K⟩
  · simpa only [Environment.outputRegion, len] using value
  · intro j positive hj different
    exact loadPrime_preserves_num small positive different (h.ws.fit64 hj) O

end VG.Proof.RsaKeyGen.X86.Key
