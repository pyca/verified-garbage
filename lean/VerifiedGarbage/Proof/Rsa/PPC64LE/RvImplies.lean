module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvContract
public import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_recover_primes` on PPC64LE: the shared contract implies `rvP` -/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE

/-- A state meeting `rvP.pre`: a 512-bit modulus, one-byte exponents, and
the stack arguments at `sp + 96 = 0x6060`. -/
def rvSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1100 | .r6 => 64 | .r7 => 0x2000 | .r8 => 64 | .r9 => 0x3000
    | .r10 => 1 | _ => 0
  lr := 0
  sp := 0x6000
  mem a := if a = 0x6061 then 0x32 else if a = 0x6068 then 1 else if a = 0x6071 then 0x80
    else if a = 0x6078 then 0x20 else if a = 0x6079 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3200, 1⟩, ⟨0x6060, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x8000, 8448⟩]

theorem stackArgs_four (s : State) :
    List.map (stackArg s) (List.range 4) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

theorem rv_implies : rvP.Implies (Spec.Rsa.recoverPrimesContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rvP, stackArgs_four,
      List.append_eq] at h
    sig_pre [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rvP, stackArgs_four,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rvP, stackArgs_four,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | omega
  post := by
    sig_implies_post [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rvP,
      stackArgs_four, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rvP, stackArgs_four,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_four, stackArgs_four, a0, a1, a2, a3], hl⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rvP,
      stackArgs_four, List.append_eq] [rvSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using rvSatState

end VG.Proof.Rsa.PPC64LE.Recover
