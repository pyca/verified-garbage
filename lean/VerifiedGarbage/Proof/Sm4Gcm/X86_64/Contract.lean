module

public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Callee
public import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# SM4-GCM on x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Sm4/Gcm/Contract.lean` with the working space as an
argument, which imply these (`Verified.lean`), as AES-GCM's
(`Proof/AesGcm/X86_64/Contract.lean`). Every function calls others, which use
the `stkN` bytes below the stack pointer (`stk`) that no buffer overlaps, nor
the return address (`ret`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr ctxH gctr inc32 j0 fullTag tagLenOk encryptWith openResult)
open VG.Spec.Sm4.Gcm (KeyRepr ctxCiph)

/-- The return address. -/
abbrev ret (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- The stack the calls use. -/
abbrev stk (s : State) : Region := below (s.gpr .rsp) X86_64.stkN

/-- The stack pointer leaves room for the calls. -/
abbrev spOk (s : State) : Prop := X86_64.stkN ≤ (s.gpr .rsp).toNat

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 64 := stackArg s i

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

/-- `vg_sm4_gcm_init(key = rdi, ctx = rsi, scratch = rdx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 16⟩
    let ctx : Region := ⟨s.gpr .rsi, 256⟩
    let scr : Region := ⟨s.gpr .rdx, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧ (ret s).Disjoint ctx ∧ (ret s).Disjoint scr ∧
      (stk s).Disjoint key ∧ (stk s).Disjoint ctx ∧ (stk s).Disjoint scr ∧
      (s.gpr .rdi).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 256 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + 2560 ≤ 2 ^ 64 ∧ spOk s
  post s s' := KeyRepr s'.mem (s.gpr .rsi) (bytesAt s.mem (s.gpr .rdi) 16)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-- What `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt` need:
`(ctx = rdi, state = rsi, aad_len = rdx, text_len = rcx, data = r8, len = r9,
scratch = [rsp + 8])`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let st : Region := ⟨s.gpr .rsi, 80⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let scr : Region := ⟨arg s 0, 2560⟩
  s.rd = [ctx, args s 1] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ st.Disjoint (args s 1) ∧ data.Disjoint scr ∧
    data.Disjoint (args s 1) ∧ scr.Disjoint (args s 1) ∧
    (ret s).Disjoint st ∧ (ret s).Disjoint data ∧ (ret s).Disjoint scr ∧
    (stk s).Disjoint ctx ∧ (stk s).Disjoint st ∧ (stk s).Disjoint data ∧ (stk s).Disjoint scr ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + 2560 ≤ 2 ^ 64 ∧
    spOk s ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncryptX86_64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi)
    let h := ctxH s.mem (s.gpr .rdi)
    ∀ iv a p, StreamRepr s.mem (s.gpr .rsi) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      s.gpr .rdx = BitVec.ofNat 64 a.length → (s.gpr .rcx).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      StreamRepr s'.mem (s.gpr .rsi) ciph h iv a c ∧ bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = c.drop p.length
  pub := streamCryptPub

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecryptX86_64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi)
    let h := ctxH s.mem (s.gpr .rdi)
    ∀ iv a c, StreamRepr s.mem (s.gpr .rsi) ciph h iv a c →
      s.gpr .rdx = BitVec.ofNat 64 a.length → (s.gpr .rcx).toNat = c.length →
      let c' := c ++ bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
      StreamRepr s'.mem (s.gpr .rsi) ciph h iv a c' ∧
        bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := streamCryptPub

/-- What `vg_sm4_gcm_stream_finish` needs: `(ctx = rdi, state = rsi, aad_len = rdx,
text_len = rcx, tag = r8, work = r9)`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let st : Region := ⟨s.gpr .rsi, 80⟩
  let tag : Region := ⟨s.gpr .r8, 16⟩
  let work : Region := ⟨s.gpr .r9, 2560⟩
  s.rd = [ctx] ∧ s.wr = [st, tag, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint work ∧ st.Disjoint work ∧ tag.Disjoint st ∧
    tag.Disjoint work ∧ (ret s).Disjoint st ∧ (ret s).Disjoint tag ∧ (ret s).Disjoint work ∧
    (stk s).Disjoint ctx ∧ (stk s).Disjoint st ∧ (stk s).Disjoint tag ∧ (stk s).Disjoint work ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + 2560 ≤ 2 ^ 64 ∧ spOk s

/-- What `vg_sm4_gcm_stream_verify` needs: `(ctx = rdi, state = rsi, aad_len = rdx,
text_len = rcx, tag = r8, tag_len = r9, work = [rsp + 8])`. -/
def verifyPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let st : Region := ⟨s.gpr .rsi, 80⟩
  let tag : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let work : Region := ⟨arg s 0, 2560⟩
  s.rd = [ctx, tag, args s 1] ∧ s.wr = [st, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint work ∧ tag.Disjoint st ∧ tag.Disjoint work ∧
    st.Disjoint (args s 1) ∧ work.Disjoint (args s 1) ∧
    (ret s).Disjoint st ∧ (ret s).Disjoint work ∧
    (stk s).Disjoint ctx ∧ (stk s).Disjoint st ∧ (stk s).Disjoint tag ∧ (stk s).Disjoint work ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + 2560 ≤ 2 ^ 64 ∧
    spOk s ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64

/-- `vg_sm4_gcm_stream_finish`. -/
def streamFinishX86_64 : Contract isa where
  pre := finPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi)
    let h := ctxH s.mem (s.gpr .rdi)
    ∀ iv a c, StreamRepr s.mem (s.gpr .rsi) ciph h iv a c →
      s.gpr .rdx = BitVec.ofNat 64 a.length → (s.gpr .rcx).toNat = c.length →
      bytesAt s'.mem (s.gpr .r8) 16 = fullTag ciph h iv a c
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_sm4_gcm_stream_verify`. -/
def streamVerifyX86_64 : Contract isa where
  pre := verifyPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi)
    let h := ctxH s.mem (s.gpr .rdi)
    let tl := (s.gpr .r9).toNat
    ∀ iv a c, StreamRepr s.mem (s.gpr .rsi) ciph h iv a c →
      s.gpr .rdx = BitVec.ofNat 64 a.length → (s.gpr .rcx).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (s.gpr .r8) tl then (s'.gpr .rax).setWidth 32 = 1
      else (s'.gpr .rax).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    arg s₁ 0 = arg s₂ 0

/-- What `vg_sm4_gcm_seal` and `vg_sm4_gcm_open` both need, but for `tag` and
the permissions: `(ctx = rdi, nonce = rsi, nonce_len = rdx, aad = rcx,
aad_len = r8, data = r9, len = [rsp + 8], tag = [rsp + 16])`, `work` the
`w`-th argument on the stack, and `n` arguments there. -/
def oneLay (w n : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let nonce : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
  let aad : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let work : Region := ⟨arg s w, 2560⟩
  ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s n) ∧ work.Disjoint (args s n) ∧
    (ret s).Disjoint data ∧ (ret s).Disjoint work ∧
    (stk s).Disjoint ctx ∧ (stk s).Disjoint nonce ∧ (stk s).Disjoint aad ∧ (stk s).Disjoint data ∧
    (stk s).Disjoint work ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (arg s 0).toNat ≤ 2 ^ 64 ∧
    (arg s w).toNat + 2560 ≤ 2 ^ 64 ∧ spOk s ∧ (s.gpr .rsp).toNat + 8 * (n + 1) ≤ 2 ^ 64

/-- What `vg_sm4_gcm_seal` needs: `oneLay`, with `tag` a 16-byte buffer to
write and `work = [rsp + 24]`. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let nonce : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
  let aad : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let tag : Region := ⟨arg s 1, 16⟩
  let work : Region := ⟨arg s 2, 2560⟩
  s.rd = [ctx, nonce, aad, args s 3] ∧ s.wr = [data, tag, work] ∧ oneLay 2 3 s ∧
    tag.Disjoint data ∧ tag.Disjoint work ∧ tag.Disjoint (args s 3) ∧ (ret s).Disjoint tag ∧
    (stk s).Disjoint tag ∧ (arg s 1).toNat + 16 ≤ 2 ^ 64

/-- What `vg_sm4_gcm_open` needs: `oneLay`, with the received tag the
`tag_len = [rsp + 24]` bytes at `tag`, to read, and `work = [rsp + 32]`. -/
def openPre (s : State) : Prop :=
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let tag : Region := ⟨arg s 1, (arg s 2).toNat⟩
  let work : Region := ⟨arg s 3, 2560⟩
  s.rd = [⟨s.gpr .rdi, 256⟩, ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, tag, args s 4] ∧
    s.wr = [data, work] ∧ oneLay 3 4 s ∧
    tag.Disjoint data ∧ tag.Disjoint work ∧ (stk s).Disjoint tag ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 64

def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < n, arg s₁ i = arg s₂ i

/-- `vg_sm4_gcm_seal`. -/
def sealX86_64 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .rdi)) (ctxH s.mem (s.gpr .rdi)) 16
        (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (bytesAt s.mem (s.gpr .r9) (arg s 0).toNat)
        (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) =
      (bytesAt s'.mem (s.gpr .r9) (arg s 0).toNat, bytesAt s'.mem (arg s 1) 16)
  pub := onePub 3

/-- What `vg_sm4_gcm_open` may leak (`Spec.Sm4.Gcm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  [if (openResult (ctxCiph s.mem (s.gpr .rdi)) (ctxH s.mem (s.gpr .rdi)) (arg s 2).toNat
      (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (bytesAt s.mem (s.gpr .r9) (arg s 0).toNat)
      (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (bytesAt s.mem (arg s 1) (arg s 2).toNat)).isSome
    then 1 else 0]

/-- `vg_sm4_gcm_open`. -/
def openX86_64 : Contract isa where
  pre := openPre
  post s s' :=
    match openResult (ctxCiph s.mem (s.gpr .rdi)) (ctxH s.mem (s.gpr .rdi)) (arg s 2).toNat
        (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (bytesAt s.mem (s.gpr .r9) (arg s 0).toNat)
        (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (bytesAt s.mem (arg s 1) (arg s 2).toNat) with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .r9) (arg s 0).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .r9) (arg s 0).toNat = bytesAt s.mem (s.gpr .r9) (arg s 0).toNat
  pub s₁ s₂ := onePub 4 s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.Sm4Gcm
