module

import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreCT
public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreE
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_private_precompute` on RISC-V: verified against the shared contract

`fnContract` states the shared contract on the registers and the stack
(`pp_implies`); with correctness (`fn_correct`) and constant time (`fn_ct`),
the code is verified (`pp_verified`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64

/-- A state meeting `fnContract.pre`: a 512-bit modulus, one-byte factors,
`pre` at `0x1000`, and the stack arguments at `sp = 0x6000`: the working
space at `0x8000`, of 1056 words. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 20 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x3000 | .a5 => 1 | .a6 => 0x3100
    | .a7 => 1 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6001 then 0x80 else if a = 0x6008 then 0x20 else if a = 0x6009 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x6000, 16⟩]
  wr := [⟨0x1000, 160⟩, ⟨0x8000, 8448⟩]

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem pp_implies : fnContract.Implies (Spec.Rsa.privatePrecomputeContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, fnContract,
      stackArgs_two, List.append_eq] at h
    sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, fnContract,
      stackArgs_two, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, fnContract,
      stackArgs_two, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | omega
  post := by
    sig_implies_post [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs,
      fnContract, stackArgs_two, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, fnContract,
      stackArgs_two, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_two, stackArgs_two, a0, a1],
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs,
      fnContract, stackArgs_two, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState

/-- `vg_rsa_private_precompute`. -/
theorem pp_verified :
    Verified target VG.Impl.Bignum.RISCV64.PrivPre.code (Spec.Rsa.privatePrecomputeContract abi) :=
  Verified.of_correct fn_correct fn_ct pp_implies

end VG.Proof.Bignum.RISCV64.PrivPre
