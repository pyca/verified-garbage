module

public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: the contract

Untrusted: the contract `pbkdf2` is proved against, which implies the shared
`VG.Spec.Hmac.Instance.pbkdf2Contract` (`Shared.lean`). `SH` is a streaming
hash function and `F` the bytes of stack below the stack pointer the code
and its callees use. `c` is the low 32 bits of `a4`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open Spec.Sha256 (bytesAt)

variable (SH : Spec.Hmac.StreamingHash) (F : Nat)

/-- `pbkdf2(password, password_len, salt, salt_len, c, out, out_len)`. -/
def pbkR : Contract isa where
  pre s :=
    let pw : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let salt : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let out : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
    let stack : Region := below s.sp F
    s.rd = [pw, salt] ∧ s.wr = [out] ∧ pw.Disjoint out ∧ salt.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ F ≤ s.sp.toNat ∧ stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint out ∧
    (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧
    0 < ((s.gpr .a4).setWidth 32).toNat ∧ (s.gpr .a6).toNat ≤ (2 ^ 32 - 1) * SH.digestBytes
  post s s' :=
    Spec.Pbkdf2.pbkdf2Hmac SH (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
      (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) ((s.gpr .a4).setWidth 32).toNat (s.gpr .a6).toNat =
      some (bytesAt s'.mem (s.gpr .a5) (s.gpr .a6).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ (s₁.gpr .a4).setWidth 32 = (s₂.gpr .a4).setWidth 32 ∧
    s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.sp = s₂.sp

end VG.Proof.Pbkdf2.Whole.RISCV64
