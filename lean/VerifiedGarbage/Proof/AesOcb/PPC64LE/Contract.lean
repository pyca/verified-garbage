module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Ocb

/-!
# AES-OCB on PPC64LE: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ocb/Contract.lean`, with the working space as a
last argument (`Proof/AesOcb/Scratch.lean`), which imply these
(`Verified.lean`). As on AArch64 (`Proof/AesOcb/AArch64/Contract.lean`): a
call (`bl`) stores nothing in memory, so no stack is used; `seal` and `open`
read `tag`, `tag_len` and `work` from the Parameter Save Area, at
`sp + 96`, which they may only read.
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (ctxCiph ctxInv ctxLstar encryptWith decryptWith lengthsOk zeros)

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- The key context. -/
abbrev aCtx (s : State) : Region := ⟨s.gpr .r3, 256⟩

/-- The nonce. -/
abbrev aNonce (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩

/-- The associated data. -/
abbrev aAad (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩

/-- The data. -/
abbrev aData (s : State) : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩

/-- The tag. -/
abbrev aTag (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩

/-- The working space. -/
abbrev aWork (s : State) : Region := ⟨stackArg s 2, 2560⟩

/-- What `vg_aes_ocb_seal` and `vg_aes_ocb_open` need of their arguments
`(ctx = r3, rounds = r4, nonce = r5, nonce_len = r6, aad = r7, aad_len = r8,
data = r9, len = r10, tag = [sp + 96], tag_len = [sp + 104], work = [sp + 112])`, but
for what they may access. -/
def oneFacts (s : State) : Prop :=
  (aCtx s).Disjoint (aData s) ∧ (aCtx s).Disjoint (aWork s) ∧ (aNonce s).Disjoint (aData s) ∧
    (aNonce s).Disjoint (aWork s) ∧ (aAad s).Disjoint (aData s) ∧ (aAad s).Disjoint (aWork s) ∧
    (aTag s).Disjoint (aData s) ∧ (aTag s).Disjoint (aWork s) ∧
    (aData s).Disjoint (aWork s) ∧ (aData s).Disjoint (args s 3) ∧ (aWork s).Disjoint (args s 3) ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 120 ≤ 2 ^ 64 ∧ rounds (s.gpr .r4) ∧
    lengthsOk (stackArg s 1).toNat (s.gpr .r6).toNat = true

/-- What `vg_aes_ocb_seal` needs: it may write the data, the tag and the
working space. -/
def sealPreA (s : State) : Prop :=
  s.rd = [aCtx s, aNonce s, aAad s, args s 3] ∧ s.wr = [aData s, aTag s, aWork s] ∧
    (aTag s).Disjoint (args s 3) ∧ (aCtx s).Disjoint (aTag s) ∧ (aNonce s).Disjoint (aTag s) ∧
    (aAad s).Disjoint (aTag s) ∧ oneFacts s

/-- What `vg_aes_ocb_open` needs: it may write the data and the working
space, and read the tag. -/
def openPreA (s : State) : Prop :=
  s.rd = [aCtx s, aNonce s, aAad s, aTag s, args s 3] ∧ s.wr = [aData s, aWork s] ∧ oneFacts s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp ∧ ∀ i < 3, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_ocb_seal`. -/
def sealPPC64LE : Contract isa where
  pre := sealPreA
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (ctxLstar s.mem (s.gpr .r3)) (stackArg s 1).toNat
        (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
        (bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat) =
      (bytesAt s'.mem (s.gpr .r9) (s.gpr .r10).toNat, bytesAt s'.mem (stackArg s 0) (stackArg s 1).toNat)
  pub := onePub

/-- `OCB-DECRYPT` of what `vg_aes_ocb_open` is given. -/
def openOut (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (ctxInv s.mem (s.gpr .r3) (s.gpr .r4).toNat)
    (ctxLstar s.mem (s.gpr .r3)) (stackArg s 1).toNat (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
    (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- What `vg_aes_ocb_open` may leak (`Spec.Ocb.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬rounds (s.gpr .r4) then [] else [if (openOut s).isSome then 1 else 0]

/-- `vg_aes_ocb_open`. -/
def openPPC64LE : Contract isa where
  pre := openPreA
  post s s' :=
    match openOut s with
    | some pt => (s'.gpr .r3).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .r9) (s.gpr .r10).toNat = pt
    | none => (s'.gpr .r3).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .r9) (s.gpr .r10).toNat = zeros (s.gpr .r10).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesOcb.PPC64LE
