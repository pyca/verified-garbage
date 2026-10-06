import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-OCB on AArch64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ocb/Contract.lean`, with the working space as a
last argument (`Proof/AesOcb/Scratch.lean`), which imply these
(`Verified.lean`). A call (`bl`) stores nothing in memory, so no stack is
used; `seal` and `open` read `tag`, `tag_len` and `work` from the stack,
which they may only read.
-/

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (ctxCiph ctxInv ctxLstar encryptWith decryptWith lengthsOk zeros KeyRepr)

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- The key context. -/
abbrev aCtx (s : State) : Region := ⟨s.gpr .x0, 256⟩

/-- The nonce. -/
abbrev aNonce (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩

/-- The associated data. -/
abbrev aAad (s : State) : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩

/-- The data. -/
abbrev aData (s : State) : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩

/-- The tag. -/
abbrev aTag (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩

/-- The working space. -/
abbrev aWork (s : State) : Region := ⟨stackArg s 2, 2560⟩

/-- What `vg_aes_ocb_seal` and `vg_aes_ocb_open` need of their arguments
`(ctx = x0, rounds = x1, nonce = x2, nonce_len = x3, aad = x4, aad_len = x5,
data = x6, len = x7, tag = [sp], tag_len = [sp + 8], work = [sp + 16])`, but
for what they may access. -/
def oneFacts (s : State) : Prop :=
  (aCtx s).Disjoint (aData s) ∧ (aCtx s).Disjoint (aWork s) ∧ (aNonce s).Disjoint (aData s) ∧
    (aNonce s).Disjoint (aWork s) ∧ (aAad s).Disjoint (aData s) ∧ (aAad s).Disjoint (aWork s) ∧
    (aTag s).Disjoint (aData s) ∧ (aTag s).Disjoint (aWork s) ∧
    (aData s).Disjoint (aWork s) ∧ (aData s).Disjoint (args s 3) ∧ (aWork s).Disjoint (args s 3) ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 24 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1) ∧
    lengthsOk (stackArg s 1).toNat (s.gpr .x3).toNat = true

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
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧ ∀ i < 3, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_ocb_seal`. -/
def sealAArch64 : Contract isa where
  pre := sealPreA
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxLstar s.mem (s.gpr .x0)) (stackArg s 1).toNat
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat) =
      (bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat, bytesAt s'.mem (stackArg s 0) (stackArg s 1).toNat)
  pub := onePub

/-- `OCB-DECRYPT` of what `vg_aes_ocb_open` is given. -/
def openOut (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxInv s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    (ctxLstar s.mem (s.gpr .x0)) (stackArg s 1).toNat (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- What `vg_aes_ocb_open` may leak (`Spec.Ocb.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬rounds (s.gpr .x1) then [] else [if (openOut s).isSome then 1 else 0]

/-- `vg_aes_ocb_open`. -/
def openAArch64 : Contract isa where
  pre := openPreA
  post s s' :=
    match openOut s with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = zeros (s.gpr .x7).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

/-- `vg_aes_ocb_init(key = x0, key_len = x1, ctx = x2, scratch = x3)`. -/
def initAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let ctx : Region := ⟨s.gpr .x2, 256⟩
    let scr : Region := ⟨s.gpr .x3, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (s.gpr .x2).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 16 ∨ (s.gpr .x1).toNat = 24 ∨ (s.gpr .x1).toNat = 32)
  post s s' := KeyRepr s'.mem (s.gpr .x2) (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.AesOcb.AArch64
