module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Front
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_keygen_key` on RISC-V: the postcondition on the registers and the stack

`fnPost`: `keyContract`'s postcondition, on the argument registers (`n`,
`n_len`, `d`, `d_len`, `p`, `p_len`, `q`, `q_len` in `a0`–`a7`) and the
stack arguments (`dp`, `dp_len`, `dq`, `dq_len`, `qinv`, `qinv_len`, `e`,
`e_len`, `scratch`, `scratch_len`), as PPC64LE's `keyP`
(`Proof/RsaKeyGen/PPC64LE/Key/Contract.lean`). `fnContract`: the shared
contract with it; `key_implies`: it implies the shared contract.
-/

-- separate module: `key_implies` is not re-checked with every change to the correctness proof

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Key

open VG VG.RISCV64

/-- The key from the primes, from the caller's memory. -/
abbrev resOf (s : State) : Except Spec.RsaKeyGen.Failure (List (List Byte)) ⊕ Unit :=
  Spec.RsaKeyGen.keyOp (s.gpr .a5).toNat (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 7).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a5).toNat)

/-- The seven outputs' bytes in `m`. -/
abbrev outBytes (s : State) (m : Mem) : List (List Byte) :=
  [Spec.Rsa.bytesAt m (s.gpr .a0) (s.gpr .a1).toNat, Spec.Rsa.bytesAt m (s.gpr .a2) (s.gpr .a1).toNat,
    Spec.Rsa.bytesAt m (s.gpr .a4) (s.gpr .a5).toNat, Spec.Rsa.bytesAt m (s.gpr .a6) (s.gpr .a5).toNat,
    Spec.Rsa.bytesAt m (stackArg s 0) (s.gpr .a5).toNat, Spec.Rsa.bytesAt m (stackArg s 2) (s.gpr .a5).toNat,
    Spec.Rsa.bytesAt m (stackArg s 4) (s.gpr .a5).toNat]

/-- Zeros at the seven outputs in `m`. -/
abbrev outZero (s : State) (m : Mem) : Prop :=
  Spec.Rsa.bytesAt m (s.gpr .a0) (s.gpr .a1).toNat = List.replicate (s.gpr .a1).toNat 0 ∧
    Spec.Rsa.bytesAt m (s.gpr .a2) (s.gpr .a1).toNat = List.replicate (s.gpr .a1).toNat 0 ∧
    Spec.Rsa.bytesAt m (s.gpr .a4) (s.gpr .a5).toNat = List.replicate (s.gpr .a5).toNat 0 ∧
    Spec.Rsa.bytesAt m (s.gpr .a6) (s.gpr .a5).toNat = List.replicate (s.gpr .a5).toNat 0 ∧
    Spec.Rsa.bytesAt m (stackArg s 0) (s.gpr .a5).toNat = List.replicate (s.gpr .a5).toNat 0 ∧
    Spec.Rsa.bytesAt m (stackArg s 2) (s.gpr .a5).toNat = List.replicate (s.gpr .a5).toNat 0 ∧
    Spec.Rsa.bytesAt m (stackArg s 4) (s.gpr .a5).toNat = List.replicate (s.gpr .a5).toNat 0

/-- `keyContract`'s postcondition, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  ((s'.gpr .a0).setWidth 32).toNat = Spec.RsaKeyGen.keyStatus (resOf s) ∧
    match resOf s with
    | .inl (.ok ys) => outBytes s s'.mem = ys
    | _ => outZero s s'.mem

/-- The shared contract, its postcondition on the registers and the stack. -/
def fnContract : Contract isa where
  pre := (Spec.RsaKeyGen.keyContract RISCV64.abi).pre
  post := fnPost
  pub := (Spec.RsaKeyGen.keyContract RISCV64.abi).pub

/-- A state meeting the precondition: 32-byte primes, a one-byte exponent, the
outputs at `0x1000`–`0x1600`, `e` at `0x1700`, the working space at
`0x20000`, and the stack arguments at `sp = 0x10000`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x1100 | .a3 => 64 | .a4 => 0x1200 | .a5 => 32
    | .a6 => 0x1300 | .a7 => 32 | _ => 0
  sp := 0x10000
  mem a :=
    bif Nat.beq a.toNat 0x10001 then 0x14 else bif Nat.beq a.toNat 0x10008 then 0x20
    else bif Nat.beq a.toNat 0x10011 then 0x15 else bif Nat.beq a.toNat 0x10018 then 0x20
    else bif Nat.beq a.toNat 0x10021 then 0x16 else bif Nat.beq a.toNat 0x10028 then 0x20
    else bif Nat.beq a.toNat 0x10031 then 0x17 else bif Nat.beq a.toNat 0x10038 then 1
    else bif Nat.beq a.toNat 0x10042 then 0x02 else bif Nat.beq a.toNat 0x10048 then 0x20
    else bif Nat.beq a.toNat 0x10049 then 0x04 else 0
  rd := [⟨0x1700, 1⟩, ⟨0x10000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x1200, 32⟩, ⟨0x1300, 32⟩, ⟨0x1400, 32⟩, ⟨0x1500, 32⟩, ⟨0x1600, 32⟩,
    ⟨0x20000, 8448⟩]

theorem key_implies : fnContract.Implies (Spec.RsaKeyGen.keyContract RISCV64.abi) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, RISCV64.abi, RISCV64.argRegs,
      fnContract, fnPost, stackArgs_ten, List.append_eq]
  pub := fun _ _ _ _ h => h
  sat := by
    sig_implies_sat [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, RISCV64.abi, RISCV64.argRegs,
      fnContract, stackArgs_ten, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read,
        Spec.RsaKeyGen.primeLenValid, Spec.Rsa.scratchWords] using satState

end VG.Proof.RsaKeyGen.RISCV64.Key
