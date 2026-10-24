module

import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Spec.Pbkdf2

/-!
# PBKDF2 over any streaming hash function on PPC64LE: the contracts

Untrusted: the contract `iterate` is proved against, which implies the
shared `VG.Spec.Pbkdf2.iterateContract` (`Shared.lean`). `SH` is a streaming
hash function, `Wi` the bytes of scratch space and `F` the bytes of stack
below the stack pointer the code and its callees use. `n` is the low 32 bits
of `r5`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Stream.PPC64LE

open VG.PPC64LE
open Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)
open Spec.Sha256 (bytesAt)

variable (SH : StreamingHash) (Wi F : Nat)

/-- `iterate(key, u, n, t, scratch)`. -/
def iterG : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 2 * SH.stateBytes⟩
    let u : Region := ⟨s.gpr .r4, SH.digestBytes⟩
    let t : Region := ⟨s.gpr .r6, SH.digestBytes⟩
    let scratch : Region := ⟨s.gpr .r7, Wi⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    F ≤ s.sp.toNat ∧ (below s.sp F).Disjoint key ∧ (below s.sp F).Disjoint u ∧
    (below s.sp F).Disjoint t ∧ (below s.sp F).Disjoint scratch
  post s s' := ∀ k0, k0.length = SH.H.blockSize →
    SH.Repr s.mem (s.gpr .r3) (xorPad k0 ipad) →
    SH.Repr s.mem (s.gpr .r3 + BitVec.ofNat 64 SH.stateBytes) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .r6) SH.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey SH.H k0) ((s.gpr .r5).setWidth 32).toNat
        (bytesAt s.mem (s.gpr .r4) SH.digestBytes) (bytesAt s.mem (s.gpr .r6) SH.digestBytes)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ (s₁.gpr .r5).setWidth 32 = (s₂.gpr .r5).setWidth 32 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

end VG.Proof.Pbkdf2.Stream.PPC64LE
