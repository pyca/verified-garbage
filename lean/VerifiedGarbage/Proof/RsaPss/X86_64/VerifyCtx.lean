module

import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
public import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-!
# RSASSA-PSS verification on x86-64: the contract on the registers

`verifyK G` states `Spec.RsaPss.verifyContract G G` (with the stack the
frame and the calls use, `verifyStack`) on the registers and the stack
(`verify_implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer: the frame, the return address of its
calls, and the stack of `checkEncoding`, the one that uses any. -/
def verifyStack : Nat := 392 + 8 + 400

variable (G : Spec.Mgf1.Hash)

/-- `verify(n = rdi, n_len = rsi, e = rdx, e_len = rcx, digest = r8, sig = r9,
sig_len = [rsp + 8], salt_len, any_salt_len, scratch, scratch_len = [rsp + 40])`. -/
def verifyK : Contract isa where
  pre s :=
    let n : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let e : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let dg : Region := ⟨s.gpr .r8, G.len⟩
    let sg : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 40⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩
    verifyStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧
      s.rd = [n, e, dg, sg, args] ∧ s.wr = [scr] ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ dg.Disjoint scr ∧ sg.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint dg ∧ ret.Disjoint sg ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
      stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint dg ∧ stk.Disjoint sg ∧ stk.Disjoint scr ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + G.len ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rsi).toNat ∧ 1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat ∧
      (stackArg s 0).toNat = (s.gpr .rsi).toNat ∧
      Spec.RsaPss.publicScratchWords (s.gpr .rsi).toNat ≤ (stackArg s 4).toNat
  post s s' :=
    (s'.gpr .rax).setWidth 32 = if Spec.RsaPss.verify G G (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) G.len)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .rsi).toNat)
        (Spec.RsaPss.expectedSaltLen (stackArg s 1) ((stackArg s 2).setWidth 32)) then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      (stackArg s₁ 2).setWidth 32 = (stackArg s₂ 2).setWidth 32 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
      stackArg s₁ 4 = stackArg s₂ 4 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat

/-- A state meeting `verifyK.pre`: a 512-bit modulus, a one-byte `e`, a
digest, and the stack arguments at `0x10008`. -/
def verifySatState : State where
  gpr r := match r with
    | .rdi => 0x2000 | .rsi => 64 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4600 | .r9 => 0x4000
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10028 then 0x20
    else if a = 0x10008 then 0x40 else if a = 0x10022 then 0x02 else if a = 0x10029 then 0x08 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4600, G.len⟩, ⟨0x4000, 64⟩, ⟨0x10008, 40⟩]
  wr := [⟨0x20000, 2080 * 8⟩]

end VG.Proof.RsaPss.X86_64
