import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# AES-OCB on x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ocb/Contract.lean`, which imply these
(`Verified.lean`). The functions call `vg_aes_encrypt_blocks`,
`vg_aes_decrypt_blocks` and `vg_aes_expand_key`, which use no stack: the
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

/-- What `vg_aes_ocb_seal` and `vg_aes_ocb_open` need: `(ctx = rdi,
rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8, aad_len = r9,
data = [rsp + 8], len = [rsp + 16], work = [rsp + 24], tag_len = [rsp + 32])`. -/
def onePre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let work : Region := ⟨arg s 2, 2560⟩
  s.rd = [ctx, nonce, aad, args s 4] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s 4) ∧ work.Disjoint (args s 4) ∧
    (ret s).Disjoint data ∧ (ret s).Disjoint work ∧
    (stk8 s).Disjoint ctx ∧ (stk8 s).Disjoint nonce ∧ (stk8 s).Disjoint aad ∧ (stk8 s).Disjoint data ∧
    (stk8 s).Disjoint work ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧
    (arg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ 8 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧
    rounds s ∧ lengthsOk (arg s 3).toNat (s.gpr .rcx).toNat = true

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- `OCB-DECRYPT` of what `vg_aes_ocb_open` is given. -/
def openOut (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxInv s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (ctxLstar s.mem (s.gpr .rdi)) (arg s 3).toNat (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (arg s 0) (arg s 1).toNat)
    (bytesAt s.mem (arg s 2) (arg s 3).toNat)

/-- `vg_aes_ocb_seal`. -/
def sealX86_64 : Contract isa where
  pre := onePre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxLstar s.mem (s.gpr .rdi)) (arg s 3).toNat
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (bytesAt s.mem (arg s 0) (arg s 1).toNat) =
      (bytesAt s'.mem (arg s 0) (arg s 1).toNat, bytesAt s'.mem (arg s 2) (arg s 3).toNat)
  pub := onePub

/-- `vg_aes_ocb_open`. -/
def openX86_64 : Contract isa where
  pre := onePre
  post s s' :=
    match openOut s with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (arg s 0) (arg s 1).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (arg s 0) (arg s 1).toNat = zeros (arg s 1).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ (openOut s₁).isSome = (openOut s₂).isSome

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
