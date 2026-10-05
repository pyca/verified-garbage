import VerifiedGarbage.Proof.Rsa.X86_64.KeyCode
import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified
import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_check_key` on x86-64: the shared contract

`keyContract` states the shared contract on the registers and the stack
(`key_implies`).
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Proof.Bignum.X86_64

/-- A state meeting `keyContract.pre`: a 512-bit modulus, one-byte `e`, `d`,
primes, exponents and `qInv`, and the stack arguments at `0x6008`. -/
def keySatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else if a = 0x6010 then 1 else if a = 0x6019 then 0x41
    else if a = 0x6020 then 1 else if a = 0x6029 then 0x42 else if a = 0x6030 then 1
    else if a = 0x6039 then 0x43 else if a = 0x6040 then 1 else if a = 0x6049 then 0x44
    else if a = 0x6050 then 1 else if a = 0x6059 then 0x80 else if a = 0x6061 then 0x04 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩,
    ⟨0x4400, 1⟩, ⟨0x6008, 96⟩]
  wr := [⟨0x8000, 8192⟩]

theorem key_implies : keyContract.Implies (Spec.Rsa.checkKeyContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, keyContract, stackArgs_twelve, List.append_eq] at h
    sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, keyContract, stackArgs_twelve, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, keyContract, stackArgs_twelve, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, keyContract, keyOf, stackArgs_twelve, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, keyContract, stackArgs_twelve, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hsi]) hl
    refine ⟨?_, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, keyContract, stackArgs_twelve, List.append_eq] [keySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using keySatState

end VG.Proof.Rsa.X86_64.Key
