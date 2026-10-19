module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Proof.Bignum.WorkFrame
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Framework.Omega

/-! # Preserve a prepared modulus across writes to separate byte buffers -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem ready_of_work {s t : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    {rs : List (Nat × Nat)} {extra : List Region}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hf : WorkFrame B rs extra s.mem t.mem)
    (hx : ∀ r ∈ extra, Region.Disjoint ⟨B, Z⟩ r)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = B)
    (hh : ∀ r ∈ rs, 128 ≤ r.1)
    (ha : ∀ j ∈ [aN, aOne, aR2, aR1, aRm1], ∀ r ∈ rs,
      slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j)
    (he : ∀ r ∈ rs, slot w aE + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w aE) :
    ModulusReady t B Z w mi N := by
  have hn := h.good.scr.nowrap
  have hz : 256 ≤ Z := by have := hd.z; simp only [slot, hdrBytes] at this; omega
  have hword : ∀ d, d + 8 ≤ 128 → word t.mem B d = word s.mem B d := by
    intro d hd'
    exact hf.word_eq (fun r hr => Or.inl (Nat.le_trans hd' (hh r hr))) (by omega) hn hx
  have hhdr : Hdr t.mem B w mi := by
    refine ⟨(hword _ (by decide)).trans h.good.hdr.hw,
      (hword _ (by decide)).trans h.good.hdr.hminv, ?_⟩
    intro j hj
    exact (hword _ (by unfold sArr; omega)).trans (h.good.hdr.harr j hj)
  have hread : ∀ j ∈ [aN, aOne, aR2, aR1, aRm1], slot w j + 8 * w ≤ Z := by
    intro j hj
    have hj' : j ≤ aRm1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    have hs := VG.Proof.Rsa.slot_mono (w := w) hj'
    omega_using [hs, hd.x]
  have hval : ∀ j ∈ [aN, aOne, aR2, aR1, aRm1], wv t.mem B (slot w j) w = wv s.mem B (slot w j) w :=
    fun j hj => hf.wv_eq (ha j hj) (hread j hj) hn hx
  refine ⟨⟨h.good.scr.congr hwr, hdi, hhdr⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.word_eq (fun r hr => by have := ha aN (by simp) r hr; have := hd.w4; omega)
      (by have := hread aN (by simp); have := hd.w4; omega) hn hx]
    exact h.inv
  · rw [hval aN (by simp)]; exact h.n
  · rw [hval aOne (by simp)]; exact h.one
  · rw [hval aR2 (by simp)]; exact h.r2
  · rw [hval aR1 (by simp)]; exact h.r1
  · rw [hval aRm1 (by simp)]; exact h.rm1
  · have hE := aE_fits hd
    refine ⟨?_, ?_⟩
    · rw [hf.wv_eq (fun r hr => by have := he r hr; omega) (by omega) hn hx]
      exact h.exponent.e
    · rw [hf.word_eq (fun r hr => by have := he r hr; omega) (by omega) hn hx]
      exact h.exponent.l

end VG.Proof.Dsa.X86_64.Generation
