import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-OCB on AArch64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ocb/Contract.lean`, which imply these
(`Verified.lean`). A call (`bl`) stores nothing in memory, so no stack is
used; `seal` and `open` read `work` and `tag_len` from the stack, which they
may only read.
-/

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (ctxCiph ctxInv ctxLstar encryptWith decryptWith lengthsOk zeros KeyRepr)

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- What `vg_aes_ocb_seal` and `vg_aes_ocb_open` need: `(ctx = x0, rounds = x1,
nonce = x2, nonce_len = x3, aad = x4, aad_len = x5, data = x6, len = x7,
work = [sp], tag_len = [sp + 8])`. -/
def onePre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let work : Region := ⟨stackArg s 0, 2560⟩
  s.rd = [ctx, nonce, aad, args s 2] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s 2) ∧ work.Disjoint (args s 2) ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 16 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1) ∧
    lengthsOk (stackArg s 1).toNat (s.gpr .x3).toNat = true

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧ ∀ i < 2, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_ocb_seal`. -/
def sealAArch64 : Contract isa where
  pre := onePre
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

/-- `vg_aes_ocb_open`. -/
def openAArch64 : Contract isa where
  pre := onePre
  post s s' :=
    match openOut s with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = zeros (s.gpr .x7).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ (openOut s₁).isSome = (openOut s₂).isSome

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
