module

public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Callee

/-!
# SM4-GCM on AArch64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Sm4/Gcm/Contract.lean`, which imply these
(`Verified.lean`). As AES-GCM's (`Proof/AesGcm/AArch64/Contract.lean`), but
with the 3264 bytes of stack below the stack pointer that the callees use
(`stk`), apart from every buffer; `seal` and `open` read their last
arguments from the stack, which they may only read.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr gctr inc32 j0 fullTag tagLenOk encryptWith openResult)
open VG.Spec.Sm4.Gcm (KeyRepr ctxCiph)
open VG.Spec.Gcm (ctxH)

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

/-- `vg_sm4_gcm_init(key = x0, ctx = x1, scratch = x2)`. -/
def initAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 16⟩
    let ctx : Region := ⟨s.gpr .x1, 256⟩
    let scr : Region := ⟨s.gpr .x2, 768⟩
    3264 ≤ s.sp.toNat ∧ s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (stk s.sp).Disjoint key ∧ (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint scr ∧
      (s.gpr .x0).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 768 ≤ 2 ^ 64
  post s s' := KeyRepr s'.mem (s.gpr .x1) (bytesAt s.mem (s.gpr .x0) 16)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

/-- What `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt` need:
`(ctx = x0, state = x1, aad_len = x2, text_len = x3, data = x4, len = x5, scratch = x6)`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let st : Region := ⟨s.gpr .x1, 80⟩
  let data : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let scr : Region := ⟨s.gpr .x6, 768⟩
  3264 ≤ s.sp.toNat ∧ s.rd = [ctx] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ data.Disjoint scr ∧
    (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint st ∧ (stk s.sp).Disjoint data ∧ (stk s.sp).Disjoint scr ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 768 ≤ 2 ^ 64

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.sp = s₂.sp

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncryptAArch64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0)
    let h := ctxH s.mem (s.gpr .x0)
    ∀ iv a p, StreamRepr s.mem (s.gpr .x1) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      s.gpr .x2 = BitVec.ofNat 64 a.length → (s.gpr .x3).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
      StreamRepr s'.mem (s.gpr .x1) ciph h iv a c ∧ bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = c.drop p.length
  pub := streamCryptPub

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecryptAArch64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0)
    let h := ctxH s.mem (s.gpr .x0)
    ∀ iv a c, StreamRepr s.mem (s.gpr .x1) ciph h iv a c →
      s.gpr .x2 = BitVec.ofNat 64 a.length → (s.gpr .x3).toNat = c.length →
      let c' := c ++ bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat
      StreamRepr s'.mem (s.gpr .x1) ciph h iv a c' ∧
        bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := streamCryptPub

/-- What `vg_sm4_gcm_stream_finish` needs: `(ctx = x0, state = x1, aad_len = x2,
text_len = x3, tag = x4, work = x5)`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let st : Region := ⟨s.gpr .x1, 80⟩
  let tag : Region := ⟨s.gpr .x4, 16⟩
  let work : Region := ⟨s.gpr .x5, 768⟩
  3264 ≤ s.sp.toNat ∧ s.rd = [ctx] ∧ s.wr = [st, tag, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint work ∧ st.Disjoint tag ∧ st.Disjoint work ∧
    tag.Disjoint work ∧
    (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint st ∧ (stk s.sp).Disjoint tag ∧ (stk s.sp).Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + 768 ≤ 2 ^ 64

/-- `vg_sm4_gcm_stream_finish`. -/
def streamFinishAArch64 : Contract isa where
  pre := finPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0)
    let h := ctxH s.mem (s.gpr .x0)
    ∀ iv a c, StreamRepr s.mem (s.gpr .x1) ciph h iv a c →
      s.gpr .x2 = BitVec.ofNat 64 a.length → (s.gpr .x3).toNat = c.length →
      bytesAt s'.mem (s.gpr .x4) 16 = fullTag ciph h iv a c
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

/-- What `vg_sm4_gcm_stream_verify` needs: `(ctx = x0, state = x1, aad_len = x2,
text_len = x3, tag = x4, tag_len = x5, work = x6)`. -/
def verPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let st : Region := ⟨s.gpr .x1, 80⟩
  let tag : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let work : Region := ⟨s.gpr .x6, 768⟩
  3264 ≤ s.sp.toNat ∧ s.rd = [ctx, tag] ∧ s.wr = [st, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint tag ∧ st.Disjoint work ∧ tag.Disjoint work ∧
    (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint st ∧ (stk s.sp).Disjoint tag ∧ (stk s.sp).Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 768 ≤ 2 ^ 64

/-- `vg_sm4_gcm_stream_verify`. -/
def streamVerifyAArch64 : Contract isa where
  pre := verPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0)
    let h := ctxH s.mem (s.gpr .x0)
    let tl := (s.gpr .x5).toNat
    ∀ iv a c, StreamRepr s.mem (s.gpr .x1) ciph h iv a c →
      s.gpr .x2 = BitVec.ofNat 64 a.length → (s.gpr .x3).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (s.gpr .x4) tl then (s'.gpr .x0).setWidth 32 = 1
      else (s'.gpr .x0).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.sp = s₂.sp

/-- What `vg_sm4_gcm_seal` needs: `(ctx = x0, nonce = x1, nonce_len = x2, aad = x3, aad_len = x4,
data = x5, len = x6, tag = x7, work = [sp])`. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
  let aad : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let tag : Region := ⟨s.gpr .x7, 16⟩
  let work : Region := ⟨stackArg s 0, 768⟩
  3264 ≤ s.sp.toNat ∧ s.rd = [ctx, nonce, aad, args s 1] ∧ s.wr = [data, tag, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    nonce.Disjoint work ∧ aad.Disjoint data ∧ aad.Disjoint tag ∧ aad.Disjoint work ∧ data.Disjoint tag ∧
    data.Disjoint work ∧ data.Disjoint (args s 1) ∧ tag.Disjoint work ∧ tag.Disjoint (args s 1) ∧
    work.Disjoint (args s 1) ∧
    (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint nonce ∧ (stk s.sp).Disjoint aad ∧ (stk s.sp).Disjoint data ∧
    (stk s.sp).Disjoint tag ∧ (stk s.sp).Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x7).toNat + 16 ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 768 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 ≤ 2 ^ 64

/-- The public arguments of `seal` and `open`, with `n` on the stack. -/
def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧ ∀ i < n, stackArg s₁ i = stackArg s₂ i

/-- `vg_sm4_gcm_seal`. -/
def sealAArch64 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .x0)) (ctxH s.mem (s.gpr .x0)) 16
        (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
        (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) =
      (bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat, bytesAt s'.mem (s.gpr .x7) 16)
  pub := onePub 1

/-- What `vg_sm4_gcm_open` needs: `(ctx = x0, nonce = x1, nonce_len = x2, aad = x3, aad_len = x4,
data = x5, len = x6, tag = x7, tag_len = [sp], work = [sp + 8])`. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
  let aad : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let tag : Region := ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  let work : Region := ⟨stackArg s 1, 768⟩
  3264 ≤ s.sp.toNat ∧ s.rd = [ctx, nonce, aad, tag, args s 2] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧
    data.Disjoint work ∧ data.Disjoint (args s 2) ∧ tag.Disjoint work ∧ work.Disjoint (args s 2) ∧
    (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint nonce ∧ (stk s.sp).Disjoint aad ∧ (stk s.sp).Disjoint data ∧
    (stk s.sp).Disjoint tag ∧ (stk s.sp).Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
    (stackArg s 1).toNat + 768 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 2 ≤ 2 ^ 64

/-- What `vg_sm4_gcm_open` computes, for the arguments of `s`. -/
def openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .x0)) (ctxH s.mem (s.gpr .x0)) (stackArg s 0).toNat
    (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
    (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat)

/-- What `vg_sm4_gcm_open` may leak: whether it succeeds. -/
def openLeakOf (s : State) : List Nat := [if (openRes s).isSome = true then 1 else 0]

/-- `vg_sm4_gcm_open`. -/
def openAArch64 : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat = bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
  pub s₁ s₂ := onePub 2 s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂

end VG.Proof.Sm4Gcm.AArch64
