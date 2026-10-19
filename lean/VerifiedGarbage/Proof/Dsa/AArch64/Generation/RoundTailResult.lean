module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundTail
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! The round completion policy retains the prepared modulus for retries. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem roundTail_result {s : State} {B : Addr} {Z w N : Nat} 
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    {f u : Bool} {i uni ch : Nat}
    (hF : word s.mem B (8 * kFlag) = mask f) (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hU : word s.mem B (8 * kU) = mask u) (hUni : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni)
    (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch)
    (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) (hch : ch < 2 ^ 62) :
    WP isa Impl.Dsa.AArch64.Generation.roundTail s fun t =>
      ModulusReady t B Z w N ∧
      word t.mem B (8 * kStat) = BitVec.ofNat 64 (if f then (if i + 1 < 17 ∨ uni + u.toNat < ch then 4 else 1) else 3) ∧
      (f = true → word t.mem B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem B (8 * kUni) = BitVec.ofNat 64 (uni + u.toNat)) ∧
      Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.roundTail
  refine WP.mono (VG.Proof.RsaKeyGen.AArch64.roundTail_ok h.ws hF hI hU hUni hC hi huni hch)
    fun t ⟨hm, hk⟩ => ?_
  have hf : Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s.mem t.mem := by
    rw [hm]
    have wI := Frm.of_outside (rs := [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)])
      (writeW_outside s.mem B (BitVec.ofNat 64 (i + 1)) (d := 8 * kI) (by decide)) (by simp)
    cases f
    · exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by decide)) (by simp)
    · exact (wI.trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by decide)) (by simp))).trans
        (Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by decide)) (by simp))
  refine ⟨h.of_frm hEZ hf ?_ hk (by decide) ?_ ?_ ?_, ?_, ?_, hf, hk⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact KMut.hdr (by decide)
  · intro a ha r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      right <;> simp only [slot, hdrBytes, kI, kElen, kUni, kP, kStat, sFn] <;> omega_arith
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> left <;> decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      right <;> simp only [slot, hdrBytes, aE, kI, kElen, kUni, kP, kStat, sFn] <;> omega_arith
  · rw [hm]; cases f <;> simp only [↓reduceIte, Bool.false_eq_true, word_writeW_self]
  · intro htrue
    rw [hm, htrue]
    simp only [↓reduceIte]
    constructor
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]


end VG.Proof.Dsa.AArch64.Generation
