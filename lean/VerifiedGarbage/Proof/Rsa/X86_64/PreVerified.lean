module

public import VerifiedGarbage.Proof.Rsa.X86_64.PreCTCode
import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyImplies

/-!
# `vg_rsa_private_precompute` on x86-64: verified against the shared contract

`ppContract` states the shared contract on the registers and the stack
(`pp_implies`); the code is correct (`ppCode_correct`) and constant time
(`ppCode_constantTime`) against it (`pp_verified`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- A state meeting `ppContract.pre`: a 512-bit modulus, one-byte primes,
`pre` at `0x1000`, and the stack arguments at `0x6008`. -/
def ppSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 20 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6020 then 0x20
    else if a = 0x6009 then 0x40 else if a = 0x6010 then 1 else if a = 0x6019 then 0x80
    else if a = 0x6021 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x6008, 32⟩]
  wr := [⟨0x1000, 160⟩, ⟨0x8000, 8448⟩]

theorem pp_implies : ppContract.Implies (Spec.Rsa.privatePrecomputeContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq] at h
    sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, ppOf, stackArgs_four, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3⟩ := h
    have hn := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
    refine ⟨?_, a0, a1, a2, a3, hn⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq] [ppSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using ppSatState

/-- `vg_rsa_private_precompute`, given that its code never loads MXCSR
(which the registration file evaluates). -/
theorem pp_verified (hmx : Impl.Rsa.X86_64.PrivPre.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target Impl.Rsa.X86_64.PrivPre.code (Spec.Rsa.privatePrecomputeContract abi) :=
  Verified.of_correct (ppCode_correct hmx) ppCode_constantTime pp_implies

end VG.Proof.Rsa.X86_64.Key
