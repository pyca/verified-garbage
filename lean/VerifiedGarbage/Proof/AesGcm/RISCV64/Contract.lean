module

public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Call

/-!
# AES-GCM on RISCV64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Gcm/Contract.lean`, which imply these
(`Verified.lean`). Each function calls `vg_ghash`, whose frame takes 2048
bytes of stack below the stack pointer (`stkOk`); the buffers of `u64` are
8-byte aligned.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr KeyRepr ctxCiph ctxH gctr inc32 j0 fullTag tagLenOk encryptWith openResult)

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- The stack pointer is aligned, and the 2048 bytes below it, which
`vg_ghash`'s frame uses, are apart from the buffers `rs`. -/
def stkOk (s : State) (rs : List Region) : Prop :=
  s.sp.toNat % 16 = 0 ∧ 2048 ≤ s.sp.toNat ∧ ∀ r ∈ rs, (below s.sp 2048).Disjoint r

/-- `vg_aes_gcm_init(key = a0, key_len = a1, ctx = a2, scratch = a3)`. -/
def initRISCV64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let ctx : Region := ⟨s.gpr .a2, 256⟩
    let scr : Region := ⟨s.gpr .a3, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (s.gpr .a2).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 16 ∨ (s.gpr .a1).toNat = 24 ∨ (s.gpr .a1).toNat = 32) ∧
      (s.gpr .a2).toNat % 8 = 0 ∧ (s.gpr .a3).toNat % 8 = 0
  post s s' := KeyRepr s'.mem (s.gpr .a2) (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `vg_aes_gcm_stream_init(ctx = a0, nonce = a1, nonce_len = a2, state = a3, scratch = a4)`. -/
def streamInitRISCV64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .a0, 256⟩
    let nonce : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    let st : Region := ⟨s.gpr .a3, 80⟩
    let scr : Region := ⟨s.gpr .a4, 2560⟩
    s.rd = [ctx, nonce] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧ st.Disjoint scr ∧
      (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + 2560 ≤ 2 ^ 64 ∧
      stkOk s [ctx, nonce, st, scr] ∧ (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a3).toNat % 8 = 0 ∧
      (s.gpr .a4).toNat % 8 = 0
  post s s' := ∀ ciph, StreamRepr s'.mem (s.gpr .a3) ciph (ctxH s.mem (s.gpr .a0))
    (bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat) [] []
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

/-- `vg_aes_gcm_stream_aad(ctx = a0, state = a1, aad_len = a2, data = a3, len = a4, scratch = a5)`. -/
def streamAadRISCV64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .a0, 256⟩
    let st : Region := ⟨s.gpr .a1, 80⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2560⟩
    s.rd = [ctx, data] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ data.Disjoint st ∧ data.Disjoint scr ∧ st.Disjoint scr ∧
      (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a1).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat + 2560 ≤ 2 ^ 64 ∧
      stkOk s [ctx, data, st, scr] ∧ (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a1).toNat % 8 = 0 ∧
      (s.gpr .a5).toNat % 8 = 0
  post s s' := ∀ ciph iv a, StreamRepr s.mem (s.gpr .a1) ciph (ctxH s.mem (s.gpr .a0)) iv a [] →
    s.gpr .a2 = BitVec.ofNat 64 a.length →
    StreamRepr s'.mem (s.gpr .a1) ciph (ctxH s.mem (s.gpr .a0)) iv
      (a ++ bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) []
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

/-- What `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` need:
`(ctx = a0, rounds = a1, state = a2, aad_len = a3, text_len = a4, data = a5, len = a6,
scratch = a7)`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let st : Region := ⟨s.gpr .a2, 80⟩
  let data : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
  let scr : Region := ⟨s.gpr .a7, 2560⟩
  s.rd = [ctx] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ data.Disjoint scr ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + 2560 ≤ 2 ^ 64 ∧
    rounds (s.gpr .a1) ∧ stkOk s [ctx, st, data, scr] ∧ (s.gpr .a0).toNat % 8 = 0 ∧
    (s.gpr .a2).toNat % 8 = 0 ∧ (s.gpr .a7).toNat % 8 = 0

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncryptRISCV64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat
    let h := ctxH s.mem (s.gpr .a0)
    ∀ iv a p, StreamRepr s.mem (s.gpr .a2) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      s.gpr .a3 = BitVec.ofNat 64 a.length → (s.gpr .a4).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)
      StreamRepr s'.mem (s.gpr .a2) ciph h iv a c ∧ bytesAt s'.mem (s.gpr .a5) (s.gpr .a6).toNat = c.drop p.length
  pub := streamCryptPub

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecryptRISCV64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat
    let h := ctxH s.mem (s.gpr .a0)
    ∀ iv a c, StreamRepr s.mem (s.gpr .a2) ciph h iv a c →
      s.gpr .a3 = BitVec.ofNat 64 a.length → (s.gpr .a4).toNat = c.length →
      let c' := c ++ bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat
      StreamRepr s'.mem (s.gpr .a2) ciph h iv a c' ∧
        bytesAt s'.mem (s.gpr .a5) (s.gpr .a6).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := streamCryptPub

/-- What `vg_aes_gcm_stream_finish` needs: `(ctx = a0, rounds = a1, state = a2, aad_len = a3,
text_len = a4, tag = a5, scratch = a6)`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let st : Region := ⟨s.gpr .a2, 80⟩
  let tag : Region := ⟨s.gpr .a5, 16⟩
  let scr : Region := ⟨s.gpr .a6, 2560⟩
  s.rd = [ctx] ∧ s.wr = [st, tag, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint scr ∧ st.Disjoint tag ∧ st.Disjoint scr ∧
    tag.Disjoint scr ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .a6).toNat + 2560 ≤ 2 ^ 64 ∧ rounds (s.gpr .a1) ∧ stkOk s [ctx, st, tag, scr] ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a2).toNat % 8 = 0 ∧ (s.gpr .a6).toNat % 8 = 0

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinishRISCV64 : Contract isa where
  pre := finPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat
    let h := ctxH s.mem (s.gpr .a0)
    ∀ iv a c, StreamRepr s.mem (s.gpr .a2) ciph h iv a c →
      s.gpr .a3 = BitVec.ofNat 64 a.length → (s.gpr .a4).toNat = c.length →
      bytesAt s'.mem (s.gpr .a5) 16 = fullTag ciph h iv a c
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.sp = s₂.sp

/-- What `vg_aes_gcm_stream_verify` needs: `(ctx = a0, rounds = a1, state = a2, aad_len = a3,
text_len = a4, tag = a5, tag_len = a6, scratch = a7)`. -/
def verPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let st : Region := ⟨s.gpr .a2, 80⟩
  let tag : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
  let scr : Region := ⟨s.gpr .a7, 2560⟩
  s.rd = [ctx, tag] ∧ s.wr = [st, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint scr ∧ st.Disjoint tag ∧ st.Disjoint scr ∧ tag.Disjoint scr ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + 2560 ≤ 2 ^ 64 ∧ rounds (s.gpr .a1) ∧
    stkOk s [ctx, tag, st, scr] ∧ (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a2).toNat % 8 = 0 ∧
    (s.gpr .a7).toNat % 8 = 0

/-- `vg_aes_gcm_stream_verify`. -/
def streamVerifyRISCV64 : Contract isa where
  pre := verPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat
    let h := ctxH s.mem (s.gpr .a0)
    let tl := (s.gpr .a6).toNat
    ∀ iv a c, StreamRepr s.mem (s.gpr .a2) ciph h iv a c →
      s.gpr .a3 = BitVec.ofNat 64 a.length → (s.gpr .a4).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (s.gpr .a5) tl then (s'.gpr .a0).setWidth 32 = 1
      else (s'.gpr .a0).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp

/-- The first `n` stack arguments, at `sp`. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

/-- What `vg_aes_gcm_seal` needs: `(ctx = a0, rounds = a1, nonce = a2, nonce_len = a3, aad = a4,
aad_len = a5, data = a6, len = a7, tag = [sp], scratch = [sp + 8])`. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let data : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let scr : Region := ⟨stackArg s 1, 2560⟩
  s.rd = [ctx, nonce, aad, args s 2] ∧ s.wr = [data, tag, scr] ∧
    ctx.Disjoint data ∧ ctx.Disjoint scr ∧ nonce.Disjoint data ∧ nonce.Disjoint scr ∧
    aad.Disjoint data ∧ aad.Disjoint scr ∧ data.Disjoint tag ∧
    data.Disjoint scr ∧ data.Disjoint (args s 2) ∧ tag.Disjoint scr ∧ scr.Disjoint (args s 2) ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 1).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 16 ≤ 2 ^ 64 ∧ rounds (s.gpr .a1) ∧
    stkOk s [ctx, nonce, aad, data, tag, scr, args s 2] ∧ (s.gpr .a0).toNat % 8 = 0 ∧
    (stackArg s 1).toNat % 8 = 0

/-- The public arguments of `seal` and `open`, with `n` on the stack. -/
def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp ∧
    ∀ i < n, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_gcm_seal`. -/
def sealRISCV64 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (ctxH s.mem (s.gpr .a0)) 16
        (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
        (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) =
      (bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat, bytesAt s'.mem (stackArg s 0) 16)
  pub := onePub 2

/-- What `vg_aes_gcm_open` needs: `(ctx = a0, rounds = a1, nonce = a2, nonce_len = a3, aad = a4,
aad_len = a5, data = a6, len = a7, tag = [sp], tag_len = [sp + 8], scratch = [sp + 16])`. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let data : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let scr : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [ctx, nonce, aad, tag, args s 3] ∧ s.wr = [data, scr] ∧
    ctx.Disjoint data ∧ ctx.Disjoint scr ∧ nonce.Disjoint data ∧ nonce.Disjoint scr ∧
    aad.Disjoint data ∧ aad.Disjoint scr ∧ data.Disjoint tag ∧
    data.Disjoint scr ∧ data.Disjoint (args s 3) ∧ tag.Disjoint scr ∧ scr.Disjoint (args s 3) ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧
    s.sp.toNat + 24 ≤ 2 ^ 64 ∧ rounds (s.gpr .a1) ∧ stkOk s [ctx, nonce, aad, data, tag, scr, args s 3] ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ (stackArg s 2).toNat % 8 = 0

/-- What `vg_aes_gcm_open` computes, in a state. -/
abbrev openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (ctxH s.mem (s.gpr .a0)) (stackArg s 1).toNat
    (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
    (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- `vg_aes_gcm_open`: the result in the low 32 bits of `a0`. It may leak
whether it succeeds. -/
def openRISCV64 : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .a0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat = pt
    | none => (s'.gpr .a0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat = bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat
  pub s₁ s₂ := onePub 3 s₁ s₂ ∧ (rounds (s₁.gpr .a1) → (openRes s₁).isSome = (openRes s₂).isSome)

end VG.Proof.AesGcm.RISCV64
