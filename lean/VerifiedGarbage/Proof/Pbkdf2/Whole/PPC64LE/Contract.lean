module

public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call

/-!
# PBKDF2 over any streaming hash function on PPC64LE, the whole derivation: the contract

Untrusted: the contract `pbkdf2` is proved against, which implies the shared
`Proof.Pbkdf2.pbkdf2ScratchContract` (`Shared.lean`). `SH` is a streaming
hash function, `Wi` the bytes of scratch space and `F` the bytes of stack
below the stack pointer the code and its callees use. `c` is the low 32 bits
of `r7`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open Spec.Sha256 (bytesAt)

variable (SH : Spec.Hmac.StreamingHash) (Wi F : Nat)

/-- `pbkdf2(password, password_len, salt, salt_len, c, out, out_len, scratch)`. -/
def pbkG : Contract isa where
  pre s :=
    let pw : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let salt : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let out : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let scratch : Region := ⟨s.gpr .r10, Wi⟩
    s.rd = [pw, salt] ∧ s.wr = [out, scratch] ∧
    pw.Disjoint out ∧ pw.Disjoint scratch ∧ salt.Disjoint out ∧ salt.Disjoint scratch ∧ out.Disjoint scratch ∧
    F ≤ s.sp.toNat ∧ (below s.sp F).Disjoint pw ∧ (below s.sp F).Disjoint salt ∧
    (below s.sp F).Disjoint out ∧ (below s.sp F).Disjoint scratch ∧
    (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + Wi ≤ 2 ^ 64 ∧
    0 < ((s.gpr .r7).setWidth 32).toNat ∧ (s.gpr .r9).toNat ≤ (2 ^ 32 - 1) * SH.digestBytes
  post s s' :=
    Spec.Pbkdf2.pbkdf2Hmac SH (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
      (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) ((s.gpr .r7).setWidth 32).toNat (s.gpr .r9).toNat =
      some (bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ (s₁.gpr .r7).setWidth 32 = (s₂.gpr .r7).setWidth 32 ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp

end VG.Proof.Pbkdf2.Whole.PPC64LE
