import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# A candidate for an RSA prime on x86-64: the shared contract implies `candContract`
-/

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
  mem a := if a = 0x6021 then 0x80 else if a = 0x6028 then 0x00 else if a = 0x6029 then 0x02 else 0
  rd := [⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x6008, 40⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x8000, 4096⟩]

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4] := rfl

theorem cand_implies : candContract.Implies (Spec.RsaKeyGen.candidateContract abi) where
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

end VG.Proof.RsaKeyGen.X86_64
