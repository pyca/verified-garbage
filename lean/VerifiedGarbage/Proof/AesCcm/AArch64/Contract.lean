import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-CCM on AArch64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ccm/Contract.lean`, which imply these
(`Verified.lean`). A call (`bl`) stores nothing in memory, so no stack is
used; `seal` and `open` read their last two arguments from the stack, which
they may only read.
-/

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- The two arguments on the stack. -/
abbrev args (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- What `vg_aes_ccm_seal` and `vg_aes_ccm_open` need: `(schedule = x0,
rounds = x1, nonce = x2, nonce_len = x3, aad = x4, aad_len = x5, data = x6,
len = x7, work = [sp], tag_len = [sp + 8])`. -/
def onePre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .x0, 240⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let work : Region := ⟨stackArg s 0, 2560⟩
  s.rd = [sch, nonce, aad, args s] ∧ s.wr = [data, work] ∧
    sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s) ∧ work.Disjoint (args s) ∧
    (s.gpr .x0).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 16 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1) ∧
    valid (stackArg s 1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat = true

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧ ∀ i < 2, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_ccm_seal`. -/
def sealAArch64 : Contract isa where
  pre := onePre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (stackArg s 1).toNat
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat, bytesAt s'.mem (stackArg s 0) (stackArg s 1).toNat)
  pub := onePub

/-- What `vg_aes_ccm_open` computes, for the arguments of `s`. -/
def openRes (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (stackArg s 1).toNat
    (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- The result of `vg_aes_ccm_open`: `x0` and the `n` bytes of `out` for the
result `r` of the decryption-verification. -/
def openOut (r : Option (List Byte)) (x0 : BitVec 64) (out : List Byte) (n : Nat) : Prop :=
  match r with
  | some pt => x0.setWidth 32 = 1 ∧ out = pt
  | none => x0.setWidth 32 = 0 ∧ out = zeros n

/-- `vg_aes_ccm_open`. -/
def openAArch64 : Contract isa where
  pre := onePre
  post s s' := openOut (openRes s) (s'.gpr .x0) (bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat) (s.gpr .x7).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧
    [if (openRes s₁).isSome = true then 1 else 0] = [if (openRes s₂).isSome = true then 1 else 0]

end VG.Proof.AesCcm.AArch64
