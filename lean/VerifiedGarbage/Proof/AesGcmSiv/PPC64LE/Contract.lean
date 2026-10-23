module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Spec.GcmSiv

/-!
# AES-GCM-SIV on PPC64LE: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/GcmSiv/Contract.lean`, which imply these
(`Verified.lean`), with a 3824-byte `work` buffer appended
(`Proof/AesGcmSiv/Scratch.lean`), its address the one stack argument. A call
(`bl`) stores nothing in memory, so no stack is used.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.GcmSiv (ctxCiph keyLen encryptWith decryptWith zeros)

/-- The stack argument, `work`. -/
abbrev args (s : State) : Region := ⟨stackArgAddr s 0, 8⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 14

/-- What `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` both need, but for
the permissions: `(schedule = r3, rounds = r4, nonce = r5, aad = r6,
aad_len = r7, data = r8, len = r9, tag = r10, work = [sp + 96])`. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .r3, 240⟩
  let nonce : Region := ⟨s.gpr .r5, 12⟩
  let aad : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let tag : Region := ⟨s.gpr .r10, 16⟩
  let work : Region := ⟨stackArg s 0, 3824⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s) ∧ work.Disjoint (args s) ∧
    (s.gpr .r3).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r10).toNat + 16 ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 3824 ≤ 2 ^ 64 ∧
    (stackArgAddr s 0).toNat + 8 ≤ 2 ^ 64 ∧ rounds (s.gpr .r4)

/-- What `vg_aes_gcm_siv_seal` needs: `oneLay`, with `tag` the 16 bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .r3, 240⟩
  let nonce : Region := ⟨s.gpr .r5, 12⟩
  let aad : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let tag : Region := ⟨s.gpr .r10, 16⟩
  let work : Region := ⟨stackArg s 0, 3824⟩
  s.rd = [sch, nonce, aad, args s] ∧ s.wr = [data, tag, work] ∧ tag.Disjoint (args s) ∧ oneLay s

/-- What `vg_aes_gcm_siv_open` needs: `oneLay`, with the received tag the 16
bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .r3, 240⟩
  let nonce : Region := ⟨s.gpr .r5, 12⟩
  let aad : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let tag : Region := ⟨s.gpr .r10, 16⟩
  let work : Region := ⟨stackArg s 0, 3824⟩
  s.rd = [sch, nonce, aad, tag, args s] ∧ s.wr = [data, work] ∧ oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- `vg_aes_gcm_siv_seal`. -/
def sealPPC64LE : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (keyLen (s.gpr .r4).toNat)
        (bytesAt s.mem (s.gpr .r5) 12) (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat) =
      (bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat, bytesAt s'.mem (s.gpr .r10) 16)
  pub := onePub

/-- What `vg_aes_gcm_siv_open` computes, for the arguments of `s`. -/
abbrev openRes (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (keyLen (s.gpr .r4).toNat)
    (bytesAt s.mem (s.gpr .r5) 12) (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat) (bytesAt s.mem (s.gpr .r10) 16)

/-- The result of `vg_aes_gcm_siv_open`: `r3` and the `n` bytes of the data
for the result `r` of the decryption. -/
def openOut (r : Option (List Byte)) (r3 : BitVec 64) (out : List Byte) (n : Nat) : Prop :=
  match r with
  | some pt => r3.setWidth 32 = 1 ∧ out = pt
  | none => r3.setWidth 32 = 0 ∧ out = zeros n

/-- `vg_aes_gcm_siv_open`. It does not branch on whether the tag is right,
so its runs are related without the leak the shared contract allows. -/
def openPPC64LE : Contract isa where
  pre := openPre
  post s s' := openOut (openRes s) (s'.gpr .r3) (bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat) (s.gpr .r9).toNat
  pub := onePub

end VG.Proof.AesGcmSiv.PPC64LE
