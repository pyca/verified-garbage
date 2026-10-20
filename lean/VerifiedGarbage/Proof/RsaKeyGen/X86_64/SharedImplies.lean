module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedContract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Implies
import VerifiedGarbage.Proof.Framework.Omega

/-! # The existing shared contract grants room for the nested call -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64
open VG.Spec.Rsa (bytesAt wordsAt)

private theorem clear128 {s : State}
    (h : (Spec.RsaKeyGen.candidateContract abi 128).pre s) :
    Clear (below (s.gpr .rsp) 128) s := by
  simp only [Spec.RsaKeyGen.candidateContract, Sig.contract] at h
  split at h
  · exact h.elim
  · obtain ⟨_, hrd, hwr, _, hres, _⟩ := h
    intro r hr
    have hh : below (s.gpr .rsp) 128 ∈ abi.reserved 128 s := by
      simp [abi, stackBelow, below]
    rcases List.mem_append.mp hr with hr | hr
    · rw [show s.rd = abi.rd s from rfl, hrd] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact (hres _ hh a (List.mem_filter.mp ha).1).symm
    · rw [show s.wr = abi.wr s from rfl, hwr] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact (hres _ hh a (List.mem_filter.mp ha).1).symm

theorem sharedCand_implies : sharedCandContract.Implies (Spec.RsaKeyGen.candidateContract abi 128) where
  pre := by
    intro s h
    have hc : candPre s := by
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
    have hclear := clear128 h
    have hsize : 128 ≤ (s.gpr .rsp).toNat := by
      have hh := h
      sig_pre [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs,
        stackArgs_five, List.append_eq] at hh
      sig_split hh
      omega_arith
    have hw := hc.2.2.1
    exact ⟨hc, ⟨⟨hsize, hclear _ (by
      apply List.mem_append_right
      rw [hw]
      simp)⟩, rfl, hclear⟩⟩
  post := by sig_implies_post [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs,
    sharedCandContract, candPost, candRes, stackArgs_five, List.append_eq]
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, sharedCandContract, candPub,
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

end VG.Proof.RsaKeyGen.X86_64
