module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Correct
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.CT3

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: verified against the shared contract

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecVerified.lean`): `fnContract` states the
shared contract's postcondition on the registers and the stack
(`dec_implies`); with correctness (`code_correct`) and constant time
(`code_ct`), `code` is verified for the stack its frame and
`vg_rsa_private_checked`'s use (`dec_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt

/-- The shared contract, its postcondition on the registers and the stack. -/
def fnContract : Contract isa where
  pre := (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes).pre
  post := fnPost
  pub := (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes).pub

/-- A state meeting the precondition: a 64-byte modulus, input and `out`,
one-byte exponents, primes, CRT exponents and `qInv`, and the stack
arguments at `sp`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x1100 | .a3 => 0x2000 | .a4 => 64 | .a5 => 0x3000
    | .a6 => 1 | .a7 => 0x3100 | _ => 0
  sp := 0x10000
  mem a :=
    bif Nat.beq a.toNat 0x10000 then 1 else bif Nat.beq a.toNat 0x10009 then 0x40
    else bif Nat.beq a.toNat 0x10010 then 0x40 else bif Nat.beq a.toNat 0x10019 then 0x41
    else bif Nat.beq a.toNat 0x10020 then 1 else bif Nat.beq a.toNat 0x10029 then 0x42
    else bif Nat.beq a.toNat 0x10030 then 1 else bif Nat.beq a.toNat 0x10039 then 0x43
    else bif Nat.beq a.toNat 0x10040 then 1 else bif Nat.beq a.toNat 0x10049 then 0x44
    else bif Nat.beq a.toNat 0x10050 then 1 else bif Nat.beq a.toNat 0x10059 then 0x45
    else bif Nat.beq a.toNat 0x10060 then 1 else bif Nat.beq a.toNat 0x1006A then 0x02
    else bif Nat.beq a.toNat 0x10070 then 0x20 else bif Nat.beq a.toNat 0x10071 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x4000, 64⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩,
    ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x10000, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x20000, 8448⟩]

theorem dec_implies : fnContract.Implies (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, RISCV64.abi,
      RISCV64.argRegs, fnContract, fnPost, stackArgs_fifteen, List.append_eq, dBytes, cOf]
  pub := fun _ _ _ _ h => h
  sat := by
    sig_implies_sat [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, RISCV64.abi,
      RISCV64.argRegs, fnContract, stackArgs_fifteen, List.append_eq]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

/-- `vg_rsa_pkcs1_decrypt`. -/
theorem dec_verified : Verified RISCV64.target code (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes) :=
  Verified.of_correct code_correct code_ct dec_implies

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
