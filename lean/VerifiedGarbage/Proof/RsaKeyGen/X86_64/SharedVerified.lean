module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedSafety
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCTCode
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `RsaKeyGen.X86_64.SharedImplies`, which only this module used -/

section

/-! ### `RsaKeyGen.X86_64.Implies`, which only this module used -/

section

/-!
# A candidate for an RSA prime on x86-64: the shared contract implies `candContract`
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64

/-- A state meeting the precondition: a 32-byte prime, a one-byte `e`, no
`p`, no randomness, the stack arguments at `0x6008`. -/
def candSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 32 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .r9 => 0x4000
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6021 then 0x80 else if a = 0x6028 then 0x20 else if a = 0x6029 then 0x02 else 0
  rd := [⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x6008, 40⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x8000, 4352⟩]

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4] := rfl

end VG.Proof.RsaKeyGen.X86_64

end

end


/-! # The existing shared contract grants room for the nested call -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64
open VG.Spec.Rsa (bytesAt wordsAt)

private theorem clear128 {s : State}
    (h : (Proof.RsaKeyGen.candidateContract abi 128).pre s) :
    Clear (below (s.gpr .rsp) 128) s := by
  simp only [Proof.RsaKeyGen.candidateContract, Sig.contract] at h
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

theorem sharedCand_implies : sharedCandContract.Implies (Proof.RsaKeyGen.candidateContract abi 128) where
  pre := by
    intro s h
    have hc : candPre s := by
      sig_pre [Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig, abi, argRegs, candContract, candPre,
        stackArgs_five, List.append_eq] at h
      sig_pre [Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig, abi, argRegs, candContract, candPre,
        stackArgs_five, List.append_eq] at h
      sig_split h
      sig_reduce [Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig, abi, argRegs, candContract, candPre,
        stackArgs_five, List.append_eq]
      sig_and_intros
      sig_close
      all_goals with_reducible assumption
    have hclear := clear128 h
    have hsize : 128 ≤ (s.gpr .rsp).toNat := by
      have hh := h
      sig_pre [Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig, abi, argRegs,
        stackArgs_five, List.append_eq] at hh
      sig_split hh
      omega_arith
    have hw := hc.2.2.1
    exact ⟨hc, ⟨⟨hsize, hclear _ (by
      apply List.mem_append_right
      rw [hw]
      simp)⟩, rfl, hclear⟩⟩
  post := by sig_implies_post [Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig, abi, argRegs,
    sharedCandContract, candPost, candRes, stackArgs_five, List.append_eq]
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig, abi, argRegs, sharedCandContract, candPub,
      candLeak, stackArgs_five, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4⟩ := h
    refine ⟨hdi, hsi, hdx, hcx, h8, h9, hsp, fun i hi => ?_, hl⟩
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2
    · exact a3
    · exact a4
  sat := by sig_implies_sat [Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig, abi, argRegs,
    candContract, candPre, stackArgs_five, List.append_eq] [candSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using candSat

end VG.Proof.RsaKeyGen.X86_64

end

end


/-! # Verify the RSA candidate against the existing shared ABI contract -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem sharedCandidate_verified (v : RoundImpl) : Verified target (sharedCandidateCode v)
    (Proof.RsaKeyGen.candidateContract abi 128) := by
  have hmc : MmCalls v.mont v.mm := ⟨v.mmOk, v.mmInline⟩
  exact Verified.of_correct
    (sharedCode_correct v.mont hmc (Kernel.called v) (sharedCandidate_ctl v))
    (sharedCode_constantTime v.mont hmc (Kernel.called v)) sharedCand_implies

end VG.Proof.RsaKeyGen.X86_64
