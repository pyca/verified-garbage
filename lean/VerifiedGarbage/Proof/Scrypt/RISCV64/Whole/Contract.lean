module

public import VerifiedGarbage.Spec.Scrypt.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Spec.Scrypt.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval

/-!
# scrypt on RISC-V: the contract

Untrusted: the contract the proof of `vg_scrypt` is written against
(`scryptRV`), as on PPC64LE (`Proof/Scrypt/PPC64LE/Whole/Contract.lean`),
with 1248 bytes of stack below the stack pointer (`stackBytes`: our 256-byte
frame and the 992 bytes PBKDF2 uses below it). It implies the shared contract
of `Spec/` (`scrypt_implies`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.Whole

open VG VG.RISCV64

/-- The bytes of stack below the stack pointer the function uses. -/
abbrev stackBytes : Nat := 1248

/-- `vg_scrypt(password = a0, password_len = a1, salt = a2, salt_len = a3,
r = a4, b = a5, blen = a6, v = a7, vlen, scratch, slen, out, out_len)`, the
last five on the caller's stack. -/
def scryptRV : Contract isa where
  pre s :=
    let vlen := stackArg s 0
    let sc := stackArg s 1
    let slen := stackArg s 2
    let out := stackArg s 3
    let ol := stackArg s 4
    let r := (s.gpr .a4).toNat
    let pwR : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let saltR : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let bR : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat * 128⟩
    let vR : Region := ⟨s.gpr .a7, vlen.toNat * 128⟩
    let scR : Region := ⟨sc, slen.toNat * 128⟩
    let outR : Region := ⟨out, ol.toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 40⟩
    let stack : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩
    stackBytes ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧
    s.rd = [pwR, saltR, args] ∧ s.wr = [bR, vR, scR, outR] ∧
    pwR.Disjoint bR ∧ pwR.Disjoint vR ∧ pwR.Disjoint scR ∧ pwR.Disjoint outR ∧
    saltR.Disjoint bR ∧ saltR.Disjoint vR ∧ saltR.Disjoint scR ∧ saltR.Disjoint outR ∧
    bR.Disjoint vR ∧ bR.Disjoint scR ∧ bR.Disjoint outR ∧ bR.Disjoint args ∧
    vR.Disjoint scR ∧ vR.Disjoint outR ∧ vR.Disjoint args ∧
    scR.Disjoint outR ∧ scR.Disjoint args ∧ outR.Disjoint args ∧
    stack.Disjoint pwR ∧ stack.Disjoint saltR ∧ stack.Disjoint bR ∧ stack.Disjoint vR ∧
    stack.Disjoint scR ∧ stack.Disjoint outR ∧
    (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a5).toNat + (s.gpr .a6).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .a7).toNat + vlen.toNat * 128 ≤ 2 ^ 64 ∧
    sc.toNat + slen.toNat * 128 ≤ 2 ^ 64 ∧ out.toNat + ol.toNat ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .a6).toNat % r = 0 ∧ vlen.toNat % r = 0 ∧
    Spec.Scrypt.valid (vlen.toNat / r) r ((s.gpr .a6).toNat / r) ol.toNat ∧
    ol.toNat ≤ (2 ^ 32 - 1) * 32 ∧ slen.toNat = r + 16
  post s s' :=
    let r := (s.gpr .a4).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
      (Spec.Scrypt.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) ((stackArg s 0).toNat / r) r
      ((s.gpr .a6).toNat / r) (stackArg s 4).toNat =
      some (Spec.Scrypt.bytesAt s'.mem (stackArg s 3) (stackArg s 4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
    stackArg s₁ 4 = stackArg s₂ 4 ∧ s₁.sp = s₂.sp ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .a0) (s₁.gpr .a1).toNat)
        (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat) (s₁.gpr .a4).toNat
        ((s₁.gpr .a6).toNat / (s₁.gpr .a4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₁.gpr .a4).toNat ((stackArg s₁ 0).toNat / (s₁.gpr .a4).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .a0) (s₂.gpr .a1).toNat)
        (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat) (s₂.gpr .a4).toNat
        ((s₂.gpr .a6).toNat / (s₂.gpr .a4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₂.gpr .a4).toNat ((stackArg s₂ 0).toNat / (s₂.gpr .a4).toNat))

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt; the stack arguments are the
doublewords at `0x90000`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x10000 | .a2 => 0x20000 | .a4 => 1 | .a5 => 0x30000 | .a6 => 1 | .a7 => 0x40000
    | _ => 0
  sp := 0x90000
  mem a := bif Nat.beq a.toNat 0x90000 then 2 else bif Nat.beq a.toNat 0x9000A then 5
    else bif Nat.beq a.toNat 0x90010 then 17 else bif Nat.beq a.toNat 0x9001A then 6
    else bif Nat.beq a.toNat 0x90020 then 1 else 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90000, 40⟩]
  wr := [⟨0x30000, 128⟩, ⟨0x40000, 256⟩, ⟨0x50000, 2176⟩, ⟨0x60000, 1⟩]

theorem scrypt_implies : scryptRV.Implies (Spec.Scrypt.scryptContract RISCV64.abi stackBytes) := by
  sig_implies [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, scryptRV, below, RISCV64.abi,
    RISCV64.argRegs, List.getD, List.range, List.range.loop]
    [satState, RISCV64.stackArg, RISCV64.stackArgAddr, Mem.readW, Mem.read]
    using satState

end VG.Proof.Scrypt.RISCV64.Whole
