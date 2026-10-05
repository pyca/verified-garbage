import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# AES-OCB on x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ocb/Contract.lean`, with the working space as a
last argument (`Proof/AesOcb/Scratch.lean`), which imply these
(`Verified.lean`). The functions call `vg_aes_encrypt_blocks`,
`vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch`, which use no stack: the
return address of a call is in the 8 bytes below the stack pointer (`stk8`),
which no buffer overlaps, nor the return address (`ret`).
-/

namespace VG.Proof.AesOcb

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (ctxCiph ctxInv ctxLstar encryptWith decryptWith lengthsOk zeros KeyRepr)

/-- The return address. -/
abbrev ret (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- The stack the calls use. -/
abbrev stk8 (s : State) : Region := below (s.gpr .rsp) 8

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 64 := stackArg s i

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (s : State) : Prop :=
  (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14

/-- The key context. -/
abbrev aCtx (s : State) : Region := ⟨s.gpr .rdi, 256⟩

/-- The nonce. -/
abbrev aNonce (s : State) : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩

/-- The associated data. -/
abbrev aAad (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩

/-- The data. -/
abbrev aData (s : State) : Region := ⟨arg s 0, (arg s 1).toNat⟩

/-- The tag. -/
abbrev aTag (s : State) : Region := ⟨arg s 2, (arg s 3).toNat⟩

/-- The working space. -/
abbrev aWork (s : State) : Region := ⟨arg s 4, 2560⟩

/-- What `vg_aes_ocb_seal` and `vg_aes_ocb_open` need of their arguments
`(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8,
aad_len = r9, data = [rsp + 8], len = [rsp + 16], tag = [rsp + 24],
tag_len = [rsp + 32], work = [rsp + 40])`, but for what they may access. -/
def oneFacts (s : State) : Prop :=
  (aCtx s).Disjoint (aData s) ∧ (aCtx s).Disjoint (aWork s) ∧ (aNonce s).Disjoint (aData s) ∧
    (aNonce s).Disjoint (aWork s) ∧ (aAad s).Disjoint (aData s) ∧ (aAad s).Disjoint (aWork s) ∧
    (aTag s).Disjoint (aData s) ∧ (aTag s).Disjoint (aWork s) ∧
    (aData s).Disjoint (aWork s) ∧ (aData s).Disjoint (args s 5) ∧ (aWork s).Disjoint (args s 5) ∧
    (ret s).Disjoint (aData s) ∧ (ret s).Disjoint (aWork s) ∧ (ret s).Disjoint (aTag s) ∧
    (stk8 s).Disjoint (aCtx s) ∧ (stk8 s).Disjoint (aNonce s) ∧ (stk8 s).Disjoint (aAad s) ∧
    (stk8 s).Disjoint (aData s) ∧ (stk8 s).Disjoint (aWork s) ∧ (stk8 s).Disjoint (aTag s) ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 64 ∧
    (arg s 4).toNat + 2560 ≤ 2 ^ 64 ∧ 8 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧
    rounds s ∧ lengthsOk (arg s 3).toNat (s.gpr .rcx).toNat = true

/-- What `vg_aes_ocb_seal` needs: it may write the data, the tag and the
working space. -/
def sealPreX (s : State) : Prop :=
  s.rd = [aCtx s, aNonce s, aAad s, args s 5] ∧ s.wr = [aData s, aTag s, aWork s] ∧
    (aTag s).Disjoint (args s 5) ∧ (aCtx s).Disjoint (aTag s) ∧ (aNonce s).Disjoint (aTag s) ∧
    (aAad s).Disjoint (aTag s) ∧ oneFacts s

/-- What `vg_aes_ocb_open` needs: it may write the data and the working
space, and read the tag. -/
def openPreX (s : State) : Prop :=
  s.rd = [aCtx s, aNonce s, aAad s, aTag s, args s 5] ∧ s.wr = [aData s, aWork s] ∧ oneFacts s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `OCB-DECRYPT` of what `vg_aes_ocb_open` is given. -/
def openOut (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxInv s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (ctxLstar s.mem (s.gpr .rdi)) (arg s 3).toNat (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (arg s 0) (arg s 1).toNat)
    (bytesAt s.mem (arg s 2) (arg s 3).toNat)

/-- `vg_aes_ocb_seal`. -/
def sealX86_64 : Contract isa where
  pre := sealPreX
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxLstar s.mem (s.gpr .rdi)) (arg s 3).toNat
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (bytesAt s.mem (arg s 0) (arg s 1).toNat) =
      (bytesAt s'.mem (arg s 0) (arg s 1).toNat, bytesAt s'.mem (arg s 2) (arg s 3).toNat)
  pub := onePub

/-- What `vg_aes_ocb_open` may leak (`Spec.Ocb.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬rounds s then [] else [if (openOut s).isSome then 1 else 0]

/-- `vg_aes_ocb_open`. -/
def openX86_64 : Contract isa where
  pre := openPreX
  post s s' :=
    match openOut s with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (arg s 0) (arg s 1).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (arg s 0) (arg s 1).toNat = zeros (arg s 1).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

/-- `vg_aes_ocb_init(key = rdi, key_len = rsi, ctx = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ctx : Region := ⟨s.gpr .rdx, 256⟩
    let scr : Region := ⟨s.gpr .rcx, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (ret s).Disjoint ctx ∧ (ret s).Disjoint scr ∧
      (stk8 s).Disjoint key ∧ (stk8 s).Disjoint ctx ∧ (stk8 s).Disjoint scr ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 256 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 2560 ≤ 2 ^ 64 ∧ 8 ≤ (s.gpr .rsp).toNat ∧
      ((s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32)
  post s s' := KeyRepr s'.mem (s.gpr .rdx) (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.AesOcb
