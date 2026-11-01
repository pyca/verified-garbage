module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Spec.GcmSiv

/-!
# AES-GCM-SIV on RISC-V: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/GcmSiv/Contract.lean`, which imply these
(`Verified.lean`), with a 3840-byte `work` buffer appended
(`Proof/AesGcmSiv/Scratch.lean`), its address the one stack argument. A call
stores nothing in memory; `vg_ghash`'s frame takes the 2048 bytes below the
stack pointer, which every buffer is apart from (AES-GCM's `stkOk`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.GcmSiv (ctxCiph keyLen encryptWith decryptWith zeros)
open VG.Proof.AesGcm.RISCV64 (stkOk stkAll rounds)

/-- The stack argument, `work`. -/
abbrev args (s : State) : Region := ⟨stackArgAddr s 0, 8⟩

/-- What `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` both need, but for
the permissions: `(schedule = a0, rounds = a1, nonce = a2, aad = a3,
aad_len = a4, data = a5, len = a6, tag = a7, work = [sp])`. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .a0, 240⟩
  let nonce : Region := ⟨s.gpr .a2, 12⟩
  let aad : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
  let data : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
  let tag : Region := ⟨s.gpr .a7, 16⟩
  let work : Region := ⟨stackArg s 0, 3840⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s) ∧ work.Disjoint (args s) ∧
    (s.gpr .a0).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a7).toNat + 16 ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 3840 ≤ 2 ^ 64 ∧
    (stackArgAddr s 0).toNat + 8 ≤ 2 ^ 64 ∧ (stackArg s 0).toNat % 8 = 0 ∧ rounds (s.gpr .a1) ∧
    stkOk s [sch, nonce, aad, data, tag, work, args s]

/-- What `vg_aes_gcm_siv_seal` needs: `oneLay`, with `tag` the 16 bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .a0, 240⟩
  let nonce : Region := ⟨s.gpr .a2, 12⟩
  let aad : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
  let data : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
  let tag : Region := ⟨s.gpr .a7, 16⟩
  let work : Region := ⟨stackArg s 0, 3840⟩
  s.rd = [sch, nonce, aad, args s] ∧ s.wr = [data, tag, work] ∧ tag.Disjoint (args s) ∧ oneLay s

/-- What `vg_aes_gcm_siv_open` needs: `oneLay`, with the received tag the 16
bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .a0, 240⟩
  let nonce : Region := ⟨s.gpr .a2, 12⟩
  let aad : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
  let data : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
  let tag : Region := ⟨s.gpr .a7, 16⟩
  let work : Region := ⟨stackArg s 0, 3840⟩
  s.rd = [sch, nonce, aad, tag, args s] ∧ s.wr = [data, work] ∧ oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- `vg_aes_gcm_siv_seal`. -/
def sealRISCV64 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (keyLen (s.gpr .a1).toNat)
        (bytesAt s.mem (s.gpr .a2) 12) (bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)
        (bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) =
      (bytesAt s'.mem (s.gpr .a5) (s.gpr .a6).toNat, bytesAt s'.mem (s.gpr .a7) 16)
  pub := onePub

/-- What `vg_aes_gcm_siv_open` computes, for the arguments of `s`. -/
abbrev openRes (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (keyLen (s.gpr .a1).toNat)
    (bytesAt s.mem (s.gpr .a2) 12) (bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)
    (bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) (bytesAt s.mem (s.gpr .a7) 16)

/-- The result of `vg_aes_gcm_siv_open`: `a0` and the `n` bytes of the data
for the result `r` of the decryption. -/
def openOut (r : Option (List Byte)) (a0 : BitVec 64) (out : List Byte) (n : Nat) : Prop :=
  match r with
  | some pt => a0.setWidth 32 = 1 ∧ out = pt
  | none => a0.setWidth 32 = 0 ∧ out = zeros n

/-- `vg_aes_gcm_siv_open`. It does not branch on whether the tag is right,
so its runs are related without the leak the shared contract allows. -/
def openRISCV64 : Contract isa where
  pre := openPre
  post s s' := openOut (openRes s) (s'.gpr .a0) (bytesAt s'.mem (s.gpr .a5) (s.gpr .a6).toNat) (s.gpr .a6).toNat
  pub := onePub

end VG.Proof.AesGcmSiv.RISCV64
