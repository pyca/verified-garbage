import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# A candidate for an RSA prime on AArch64: the shared contract implies `candContract`
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64

/-- A state meeting the precondition: a 32-byte prime, a one-byte `e`, no
`p`, no randomness, the stack arguments at `0x6000`. -/
def candSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 32 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | .x5 => 0x4000 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6009 then 0x80 else if a = 0x6010 then 0x00 else if a = 0x6011 then 0x02 else 0
  rd := [⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x6000, 24⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x8000, 4096⟩]

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem cand_implies : candContract.Implies (Spec.RsaKeyGen.candidateContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, candContract, candPre,
      stackArgs_three, List.append_eq] at h
    sig_pre [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, candContract, candPre,
      stackArgs_three, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, candContract, candPre,
      stackArgs_three, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs,
    candContract, candPre, candPost, candRes, stackArgs_three, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, candContract, candPub,
      candLeak, stackArgs_three, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2⟩ := h
    refine ⟨?_, hsp, fun i hi => ?_, hl⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
    · rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact a0
      · exact a1
      · exact a2
  sat := by sig_implies_sat [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs,
    candContract, candPre, stackArgs_three, List.append_eq] [candSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using candSat

end VG.Proof.RsaKeyGen.AArch64
