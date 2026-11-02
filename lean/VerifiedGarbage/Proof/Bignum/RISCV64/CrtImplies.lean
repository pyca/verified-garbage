module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtFn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Rsa.Contract

/-!
# The RSA private-key operation on RISC-V: the shared contract

`fnContract` states the shared contract of `vg_rsa_private_crt` on the
registers and the stack (`crt_implies`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

/-- A state meeting `fnContract.pre`: a 64-byte modulus and input, one-byte
primes, exponents and `qInv`, and the stack arguments at `0x10000`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x3000 | .a5 => 64
    | .a6 => 0x4000 | .a7 => 1 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10001 then 0x41 else bif Nat.beq a.toNat 0x10008 then 1
    else bif Nat.beq a.toNat 0x10011 then 0x42 else bif Nat.beq a.toNat 0x10018 then 1
    else bif Nat.beq a.toNat 0x10021 then 0x43 else bif Nat.beq a.toNat 0x10028 then 1
    else bif Nat.beq a.toNat 0x10031 then 0x44 else bif Nat.beq a.toNat 0x10038 then 1
    else bif Nat.beq a.toNat 0x10042 then 0x02 else bif Nat.beq a.toNat 0x10048 then 0x20
    else bif Nat.beq a.toNat 0x10049 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x4000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x10000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8448⟩]

theorem crt_implies : fnContract.Implies (Proof.Rsa.privateCrtContract RISCV64.abi) where
  pre := by
    intro s h
    sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_ten, List.append_eq] at h
    sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_ten, List.append_eq] at h
    sig_split h
    sig_reduce [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_ten, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, RISCV64.abi, RISCV64.argRegs,
      fnContract, stackArgs_ten, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_ten, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    refine ⟨?_, hsp, by simp only [stackArgs_ten, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9],
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [RISCV64.argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  sat := by
    sig_implies_sat [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, RISCV64.abi, RISCV64.argRegs,
      fnContract, stackArgs_ten, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using satState

end VG.Proof.Bignum.RISCV64.Crt
