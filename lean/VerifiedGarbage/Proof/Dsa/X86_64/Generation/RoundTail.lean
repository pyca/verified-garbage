module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.RoundTail
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Round
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRound
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega

/-! # Reuse RSA's verified completion rule with DSA's uniform-round count -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem roundTail_ok {s : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    {f u : Bool} {i uni ch : Nat}
    (hF : word s.mem B (8 * kFlag) = mask f) (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hU : word s.mem B (8 * kU) = mask u) (hUni : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni)
    (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch)
    (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) (hch : ch < 2 ^ 62) :
    WP isa Impl.Dsa.X86_64.Generation.roundTail s fun t =>
      ModulusReady t B Z w mi N ∧
      word t.mem B (8 * kStat) = BitVec.ofNat 64 (if f then (if i + 1 < 17 ∨ uni + u.toNat < ch then 4 else 1) else 3) ∧
      (f = true → word t.mem B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem B (8 * kUni) = BitVec.ofNat 64 (uni + u.toNat)) ∧
      Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s.mem t.mem ∧ Keep [.rax, .rcx, .rdx] s t := by
  unfold Impl.Dsa.X86_64.Generation.roundTail
  refine WP.mono (VG.Proof.RsaKeyGen.X86_64.roundTail_ok h.good hd.z hF hI hU hUni hC hi huni hch)
    fun t ⟨hm, hk⟩ => ?_
  have hf : Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s.mem t.mem := by
    rw [hm]
    have wI := Frm.of_outside (rs := [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)])
      (writeW_outside s.mem B (BitVec.ofNat 64 (i + 1)) (d := 8 * kI) (by decide)) (by simp)
    cases f
    · exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by decide)) (by simp)
    · exact (wI.trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by decide)) (by simp))).trans
        (Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by decide)) (by simp))
  refine ⟨h.of_frm hd hf hk ((hk.gpr (by decide)).trans h.good.rdi)
    (by rng_disj) (by rng_disj) (by rng_disj), ?_, ?_, hf, hk⟩
  · rw [hm]; cases f <;> simp only [↓reduceIte, Bool.false_eq_true, word_writeW_self]
  · intro htrue
    rw [hm, htrue]
    simp only [↓reduceIte]
    constructor
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]

end VG.Proof.Dsa.X86_64.Generation
