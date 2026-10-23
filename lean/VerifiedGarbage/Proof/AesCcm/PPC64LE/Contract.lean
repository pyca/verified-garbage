module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Ccm

/-!
# AES-CCM on PPC64LE: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ccm/Contract.lean`, which imply these
(`Verified.lean`), with a 2560-byte `work` buffer appended
(`Proof/AesCcm/Scratch.lean`). A call (`bl`) stores nothing in memory, so no
stack is used; `seal` and `open` read their last three arguments from the
stack, which they may only read.
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- The three arguments on the stack. -/
abbrev args (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- What `vg_aes_ccm_seal` and `vg_aes_ccm_open` both need, but for the
permissions: `(schedule = r3, rounds = r4, nonce = r5, nonce_len = r6,
aad = r7, aad_len = r8, data = r9, len = r10, tag = [sp + 96],
tag_len = [sp + 104], work = [sp + 112])`. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .r3, 240⟩
  let nonce : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  let aad : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s) ∧ work.Disjoint (args s) ∧
    (s.gpr .r3).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ (stackArgAddr s 0).toNat + 24 ≤ 2 ^ 64 ∧ rounds (s.gpr .r4) ∧
    valid (stackArg s 1).toNat (s.gpr .r6).toNat (s.gpr .r8).toNat (s.gpr .r10).toNat = true

/-- What `vg_aes_ccm_seal` needs: `oneLay`, with `tag` the `tag_len` bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .r3, 240⟩
  let nonce : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  let aad : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [sch, nonce, aad, args s] ∧ s.wr = [data, tag, work] ∧ oneLay s

/-- What `vg_aes_ccm_open` needs: `oneLay`, with the received tag the
`tag_len` bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .r3, 240⟩
  let nonce : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  let aad : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [sch, nonce, aad, tag, args s] ∧ s.wr = [data, work] ∧ oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp ∧ ∀ i < 3, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_ccm_seal`. -/
def sealPPC64LE : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (stackArg s 1).toNat
        (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
        (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) =
      (bytesAt s'.mem (s.gpr .r9) (s.gpr .r10).toNat, bytesAt s'.mem (stackArg s 0) (stackArg s 1).toNat)
  pub := onePub

/-- What `vg_aes_ccm_open` computes, for the arguments of `s`. -/
def openRes (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (stackArg s 1).toNat
    (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
    (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- The result of `vg_aes_ccm_open`: `r3` and the `n` bytes of `out` for the
result `r` of the decryption-verification. -/
def openOut (r : Option (List Byte)) (r3 : BitVec 64) (out : List Byte) (n : Nat) : Prop :=
  match r with
  | some pt => r3.setWidth 32 = 1 ∧ out = pt
  | none => r3.setWidth 32 = 0 ∧ out = zeros n

/-- What `vg_aes_ccm_open` may leak (`Spec.Ccm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬rounds (s.gpr .r4) then [] else [if (openRes s).isSome = true then 1 else 0]

/-- `vg_aes_ccm_open`. -/
def openPPC64LE : Contract isa where
  pre := openPre
  post s s' := openOut (openRes s) (s'.gpr .r3) (bytesAt s'.mem (s.gpr .r9) (s.gpr .r10).toNat) (s.gpr .r10).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesCcm.PPC64LE
