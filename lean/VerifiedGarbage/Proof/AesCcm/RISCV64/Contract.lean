module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Ccm

/-!
# AES-CCM on RISC-V: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ccm/Contract.lean`, which imply these
(`Verified.lean`), with a 2560-byte `work` buffer appended
(`Proof/AesCcm/Scratch.lean`). A call (`jal`) stores nothing in memory, so no
stack is used; `seal` and `open` read their last three arguments from the
stack, which they may only read, at the stack pointer, which is aligned, as
`work` is (`Abi.alignsU64`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- The three arguments on the stack. -/
abbrev args (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- What `vg_aes_ccm_seal` and `vg_aes_ccm_open` both need, but for the
permissions: `(schedule = a0, rounds = a1, nonce = a2, nonce_len = a3,
aad = a4, aad_len = a5, data = a6, len = a7, tag = [sp], tag_len = [sp + 8],
work = [sp + 16])`, the stack pointer and `work` aligned. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .a0, 240⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let data : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s) ∧ work.Disjoint (args s) ∧
    (s.gpr .a0).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ (stackArgAddr s 0).toNat + 24 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧
    (stackArg s 2).toNat % 8 = 0 ∧ rounds (s.gpr .a1) ∧
    valid (stackArg s 1).toNat (s.gpr .a3).toNat (s.gpr .a5).toNat (s.gpr .a7).toNat = true

/-- What `vg_aes_ccm_seal` needs: `oneLay`, with `tag` the `tag_len` bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .a0, 240⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let data : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [sch, nonce, aad, args s] ∧ s.wr = [data, tag, work] ∧ oneLay s

/-- What `vg_aes_ccm_open` needs: `oneLay`, with the received tag the
`tag_len` bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .a0, 240⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let data : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [sch, nonce, aad, tag, args s] ∧ s.wr = [data, work] ∧ oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp ∧ ∀ i < 3, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_ccm_seal`. -/
def sealRISCV64 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (stackArg s 1).toNat
        (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
        (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) =
      (bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat, bytesAt s'.mem (stackArg s 0) (stackArg s 1).toNat)
  pub := onePub

/-- What `vg_aes_ccm_open` computes, for the arguments of `s`. -/
def openRes (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (stackArg s 1).toNat
    (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
    (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- The result of `vg_aes_ccm_open`: `a0` and the `n` bytes of `out` for the
result `r` of the decryption-verification. -/
def openOut (r : Option (List Byte)) (a0 : BitVec 64) (out : List Byte) (n : Nat) : Prop :=
  match r with
  | some pt => a0.setWidth 32 = 1 ∧ out = pt
  | none => a0.setWidth 32 = 0 ∧ out = zeros n

/-- What `vg_aes_ccm_open` may leak (`Spec.Ccm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬rounds (s.gpr .a1) then [] else [if (openRes s).isSome = true then 1 else 0]

/-- `vg_aes_ccm_open`. -/
def openRISCV64 : Contract isa where
  pre := openPre
  post s s' := openOut (openRes s) (s'.gpr .a0) (bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat) (s.gpr .a7).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesCcm.RISCV64
