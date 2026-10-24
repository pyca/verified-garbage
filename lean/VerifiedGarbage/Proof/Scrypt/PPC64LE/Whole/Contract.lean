module

public import VerifiedGarbage.Spec.Scrypt.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Spec.Scrypt.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval

/-!
# scrypt on PPC64LE: the contract

Untrusted: the contract the proof of `vg_scrypt` is written against
(`scryptPPC`), as on AArch64 (`Proof/Scrypt/AArch64/Whole/Steps.lean`), with
1120 bytes of stack below the stack pointer (`stackBytes`: our 112-byte frame
and the 1008 bytes PBKDF2 uses below it). It implies the shared contract of
`Spec/` (`scrypt_implies`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.PPC64LE.Whole

open VG VG.PPC64LE

/-- The bytes of stack below the stack pointer the function uses. -/
abbrev stackBytes : Nat := 1120

/-- `vg_scrypt(password = r3, password_len = r4, salt = r5, salt_len = r6,
r = r7, b = r8, blen = r9, v = r10, vlen, scratch, slen, out, out_len)`, the
last five in the caller's Parameter Save Area. -/
def scryptPPC : Contract isa where
  pre s :=
    let vlen := stackArg s 0
    let sc := stackArg s 1
    let slen := stackArg s 2
    let out := stackArg s 3
    let ol := stackArg s 4
    let r := (s.gpr .r7).toNat
    let pwR : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let saltR : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let bR : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 128⟩
    let vR : Region := ⟨s.gpr .r10, vlen.toNat * 128⟩
    let scR : Region := ⟨sc, slen.toNat * 128⟩
    let outR : Region := ⟨out, ol.toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 40⟩
    let stack : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩
    stackBytes ≤ s.sp.toNat ∧ s.sp.toNat + 136 ≤ 2 ^ 64 ∧
    s.rd = [pwR, saltR, args] ∧ s.wr = [bR, vR, scR, outR] ∧
    pwR.Disjoint bR ∧ pwR.Disjoint vR ∧ pwR.Disjoint scR ∧ pwR.Disjoint outR ∧
    saltR.Disjoint bR ∧ saltR.Disjoint vR ∧ saltR.Disjoint scR ∧ saltR.Disjoint outR ∧
    bR.Disjoint vR ∧ bR.Disjoint scR ∧ bR.Disjoint outR ∧ bR.Disjoint args ∧
    vR.Disjoint scR ∧ vR.Disjoint outR ∧ vR.Disjoint args ∧
    scR.Disjoint outR ∧ scR.Disjoint args ∧ outR.Disjoint args ∧
    stack.Disjoint pwR ∧ stack.Disjoint saltR ∧ stack.Disjoint bR ∧ stack.Disjoint vR ∧
    stack.Disjoint scR ∧ stack.Disjoint outR ∧
    (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .r10).toNat + vlen.toNat * 128 ≤ 2 ^ 64 ∧
    sc.toNat + slen.toNat * 128 ≤ 2 ^ 64 ∧ out.toNat + ol.toNat ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .r9).toNat % r = 0 ∧ vlen.toNat % r = 0 ∧
    Spec.Scrypt.valid (vlen.toNat / r) r ((s.gpr .r9).toNat / r) ol.toNat ∧
    ol.toNat ≤ (2 ^ 32 - 1) * 32 ∧ slen.toNat = r + 16
  post s s' :=
    let r := (s.gpr .r7).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
      (Spec.Scrypt.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) ((stackArg s 0).toNat / r) r
      ((s.gpr .r9).toNat / r) (stackArg s 4).toNat =
      some (Spec.Scrypt.bytesAt s'.mem (stackArg s 3) (stackArg s 4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
    stackArg s₁ 4 = stackArg s₂ 4 ∧ s₁.sp = s₂.sp ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat)
        (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat) (s₁.gpr .r7).toNat
        ((s₁.gpr .r9).toNat / (s₁.gpr .r7).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₁.gpr .r7).toNat ((stackArg s₁ 0).toNat / (s₁.gpr .r7).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat)
        (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat) (s₂.gpr .r7).toNat
        ((s₂.gpr .r9).toNat / (s₂.gpr .r7).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₂.gpr .r7).toNat ((stackArg s₂ 0).toNat / (s₂.gpr .r7).toNat))

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt; the stack arguments are the
doublewords at `0x90060`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x10000 | .r5 => 0x20000 | .r7 => 1 | .r8 => 0x30000 | .r9 => 1 | .r10 => 0x40000
    | _ => 0
  lr := 0
  sp := 0x90000
  mem a := bif Nat.beq a.toNat 0x90060 then 2 else bif Nat.beq a.toNat 0x9006A then 5 else bif Nat.beq a.toNat 0x90070 then 17
    else bif Nat.beq a.toNat 0x9007A then 6 else bif Nat.beq a.toNat 0x90080 then 1 else 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90060, 40⟩]
  wr := [⟨0x30000, 128⟩, ⟨0x40000, 256⟩, ⟨0x50000, 2176⟩, ⟨0x60000, 1⟩]

theorem scrypt_implies : scryptPPC.Implies (Spec.Scrypt.scryptContract PPC64LE.abi stackBytes) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, scryptPPC,
          PPC64LE.abi, PPC64LE.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, scryptPPC,
          PPC64LE.abi, PPC64LE.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, scryptPPC,
          PPC64LE.abi, PPC64LE.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, scryptPPC,
          PPC64LE.abi, PPC64LE.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, scryptPPC,
          PPC64LE.abi, PPC64LE.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        sig_split h
        rename_i hsp hlk h0 h1 h2 h3 h4 h5 h6 h7 a0 a1 a2 a3
        exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, h, hsp, hlk⟩
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, PPC64LE.abi, PPC64LE.argRegs,
          _root_.List.range, _root_.List.range.loop, List.append_eq, satState] [satState] using satState }

end VG.Proof.Scrypt.PPC64LE.Whole
