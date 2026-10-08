import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Verified
import VerifiedGarbage.Proof.Rsa.X86_64.Calls

/-!
# `vg_rsa_keygen_candidate` on x86-64, with Montgomery multiplication by calls

As the RSA functions (`Proof/Rsa/X86_64/Calls.lean`): the candidate test's
code with calls of `vg_rsa_mont_mul` runs as its inlined form, but for the
return address.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Spec.Rsa (bytesAt wordsAt)

theorem cand_implies8 : candContract.Implies (Spec.RsaKeyGen.candidateContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, candContract, candPre,
      stackArgs_five, List.append_eq] at h
    sig_pre [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, candContract, candPre,
      stackArgs_five, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, candContract, candPre,
      stackArgs_five, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs,
    candContract, candPre, candPost, candRes, stackArgs_five, List.append_eq]
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, candContract, candPub,
      candLeak, stackArgs_five, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4⟩ := h
    refine ⟨hdi, hsi, hdx, hcx, h8, h9, hsp, fun i hi => ?_, hl⟩
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2
    · exact a3
    · exact a4
  sat := by sig_implies_sat [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs,
    candContract, candPre, stackArgs_five, List.append_eq] [candSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using candSat

theorem cand_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : candContract.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : candContract.post s b) :
    candContract.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hn₁, hn₂, -⟩ := hs
  have hm₁ := Clear.miss_wr hc (by rw [hwr]; simp) hn₁ (Nat.le_refl _)
  have hm₂ := Clear.miss_wr hc (by rw [hwr]; simp) hn₂ (Nat.le_refl _)
  simp only [candContract, candPost, State.patch_gpr] at hp ⊢
  rw [patch_mem, bytesAt_overlay hm₁, wordsAt_overlay fun i hi => hm₂ i (by omega)]
  exact hp

theorem candidate_call_verified (M : Mont) {c : Prog isa} (hc : c.InlineOk = true)
    (hin : c.inline = VG.Impl.RsaKeyGen.X86_64.Candidate.code M.mm)
    (hmx : (VG.Impl.RsaKeyGen.X86_64.Candidate.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.RsaKeyGen.candidateContract abi 8) :=
  Proof.Rsa.X86_64.Verified.of_inline_sig hc (hin ▸ code_correct M hmx) (hin ▸ code_constantTime M) cand_implies8
    (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h) cand_patch

end VG.Proof.RsaKeyGen.X86_64
