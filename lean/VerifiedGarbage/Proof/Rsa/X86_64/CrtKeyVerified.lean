import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTCode
import VerifiedGarbage.Proof.Rsa.X86_64.KeyImplies

/-!
# `vg_rsa_check_crt_key` on x86-64: verified against the shared contract

`ckContract` states the shared contract on the registers and the stack
(`ck_implies`); the code is correct (`ckCode_correct`) and constant time
(`ckCode_constantTime`) against it (`ck_verified`).
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

/-- A state meeting `ckContract.pre`: a 512-bit modulus, one-byte `e`,
primes, exponents and `qInv`, and the stack arguments at `0x6008`. -/
def ckSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else if a = 0x6010 then 1 else if a = 0x6019 then 0x41
    else if a = 0x6020 then 1 else if a = 0x6029 then 0x42 else if a = 0x6030 then 1
    else if a = 0x6039 then 0x43 else if a = 0x6040 then 1 else if a = 0x6049 then 0x80
    else if a = 0x6051 then 0x04 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩,
    ⟨0x6008, 80⟩]
  wr := [⟨0x8000, 8192⟩]

theorem ck_implies : ckContract.Implies (Spec.Rsa.checkCrtKeyContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, ckContract, stackArgs_ten, List.append_eq] at h
    sig_pre [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, ckContract, stackArgs_ten, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, ckContract, stackArgs_ten, List.append_eq]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, ckContract, ckOf, stackArgs_ten, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, ckContract, stackArgs_ten, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hsi]) hl
    refine ⟨?_, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, ckContract, stackArgs_ten, List.append_eq] [ckSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using ckSatState

/-- `vg_rsa_check_crt_key`, given that its code never loads MXCSR (which the
registration file evaluates). -/
theorem ck_verified (hmx : Impl.Rsa.X86_64.CheckCrtKey.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target Impl.Rsa.X86_64.CheckCrtKey.code (Spec.Rsa.checkCrtKeyContract abi) :=
  Verified.of_correct (ckCode_correct hmx) ckCode_constantTime ck_implies

end VG.Proof.Rsa.X86_64.Key
