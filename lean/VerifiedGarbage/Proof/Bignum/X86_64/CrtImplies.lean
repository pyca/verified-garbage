module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Rsa.Contract

/-!
# RSA with the CRT on x86-64: the shared contract

`crtContract` states the shared contract on the registers and the stack
(`crt_implies`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64

theorem stackArgs_twelve (s : State) :
    List.map (stackArg s) (List.range 12) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11] := rfl

/-- A state meeting `crtContract.pre`: a 512-bit modulus, one-byte primes,
exponents and `qInv`, and the stack arguments at `0x6008`. -/
def crtSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 64
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x6060 then 0x20
    else bif Nat.beq a.toNat 0x6009 then 0x40 else bif Nat.beq a.toNat 0x6010 then 1
    else bif Nat.beq a.toNat 0x6019 then 0x41 else bif Nat.beq a.toNat 0x6020 then 1
    else bif Nat.beq a.toNat 0x6029 then 0x42 else bif Nat.beq a.toNat 0x6030 then 1
    else bif Nat.beq a.toNat 0x6039 then 0x43 else bif Nat.beq a.toNat 0x6040 then 1
    else bif Nat.beq a.toNat 0x6049 then 0x44 else bif Nat.beq a.toNat 0x6050 then 1
    else bif Nat.beq a.toNat 0x6059 then 0x80 else bif Nat.beq a.toNat 0x6061 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x4000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x6008, 96⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8448⟩]

theorem crt_implies : crtContract.Implies (Proof.Rsa.privateCrtContract abi) where
  pre := by
    intro s h
    sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    sig_split h
    sig_reduce [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq, List.range, List.range.loop]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
    refine ⟨?_, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq] [crtSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using crtSatState

end VG.Proof.Bignum.X86_64
