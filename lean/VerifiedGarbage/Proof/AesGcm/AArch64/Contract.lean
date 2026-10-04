import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-GCM on AArch64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Gcm/Contract.lean`, which imply these
(`Verified.lean`). A call (`bl`) stores nothing in memory, so no stack is
used; `seal` and `open` read their last arguments from the stack, which they
may only read.
-/

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr KeyRepr ctxCiph ctxH gctr inc32 j0 fullTag tagLenOk zeros encryptWith openResult)

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- `vg_aes_gcm_init(key = x0, key_len = x1, ctx = x2, scratch = x3)`. -/
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

/-- `vg_aes_gcm_stream_init(ctx = x0, nonce = x1, nonce_len = x2, state = x3, scratch = x4)`. -/
def streamInitAArch64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .x0, 256⟩
    let nonce : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
    let st : Region := ⟨s.gpr .x3, 80⟩
    let scr : Region := ⟨s.gpr .x4, 2560⟩
    s.rd = [ctx, nonce] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧ st.Disjoint scr ∧
      (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 2560 ≤ 2 ^ 64
  post s s' := ∀ ciph, StreamRepr s'.mem (s.gpr .x3) ciph (ctxH s.mem (s.gpr .x0))
    (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) [] []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `vg_aes_gcm_stream_aad(ctx = x0, state = x1, aad_len = x2, data = x3, len = x4, scratch = x5)`. -/
def streamAadAArch64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .x0, 256⟩
    let st : Region := ⟨s.gpr .x1, 80⟩
    let data : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scr : Region := ⟨s.gpr .x5, 2560⟩
    s.rd = [ctx, data] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ data.Disjoint st ∧ data.Disjoint scr ∧ st.Disjoint scr ∧
      (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x1).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 2560 ≤ 2 ^ 64
  post s s' := ∀ ciph iv a, StreamRepr s.mem (s.gpr .x1) ciph (ctxH s.mem (s.gpr .x0)) iv a [] →
    s.gpr .x2 = BitVec.ofNat 64 a.length →
    StreamRepr s'.mem (s.gpr .x1) ciph (ctxH s.mem (s.gpr .x0)) iv
      (a ++ bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

/-- What `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` need:
`(ctx = x0, rounds = x1, state = x2, aad_len = x3, text_len = x4, data = x5, len = x6,
scratch = x7)`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let st : Region := ⟨s.gpr .x2, 80⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let scr : Region := ⟨s.gpr .x7, 2560⟩
  s.rd = [ctx] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ data.Disjoint scr ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + 2560 ≤ 2 ^ 64 ∧
    rounds (s.gpr .x1)

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncryptAArch64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
    let h := ctxH s.mem (s.gpr .x0)
    ∀ iv a p, StreamRepr s.mem (s.gpr .x2) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      s.gpr .x3 = BitVec.ofNat 64 a.length → (s.gpr .x4).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
      StreamRepr s'.mem (s.gpr .x2) ciph h iv a c ∧ bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat = c.drop p.length
  pub := streamCryptPub

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecryptAArch64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
    let h := ctxH s.mem (s.gpr .x0)
    ∀ iv a c, StreamRepr s.mem (s.gpr .x2) ciph h iv a c →
      s.gpr .x3 = BitVec.ofNat 64 a.length → (s.gpr .x4).toNat = c.length →
      let c' := c ++ bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
      StreamRepr s'.mem (s.gpr .x2) ciph h iv a c' ∧
        bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := streamCryptPub

/-- What `vg_aes_gcm_stream_finish` needs: `(ctx = x0, rounds = x1, state = x2, aad_len = x3,
text_len = x4, tag = x5, work = x6)`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let st : Region := ⟨s.gpr .x2, 80⟩
  let tag : Region := ⟨s.gpr .x5, 16⟩
  let work : Region := ⟨s.gpr .x6, 2560⟩
  s.rd = [ctx] ∧ s.wr = [st, tag, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint work ∧ st.Disjoint tag ∧ st.Disjoint work ∧
    tag.Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .x6).toNat + 2560 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1)

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinishAArch64 : Contract isa where
  pre := finPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
    let h := ctxH s.mem (s.gpr .x0)
    ∀ iv a c, StreamRepr s.mem (s.gpr .x2) ciph h iv a c →
      s.gpr .x3 = BitVec.ofNat 64 a.length → (s.gpr .x4).toNat = c.length →
      bytesAt s'.mem (s.gpr .x5) 16 = fullTag ciph h iv a c
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.sp = s₂.sp

/-- What `vg_aes_gcm_stream_verify` needs: `(ctx = x0, rounds = x1, state = x2, aad_len = x3,
text_len = x4, tag = x5, tag_len = x6, work = x7)`. -/
def verPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let st : Region := ⟨s.gpr .x2, 80⟩
  let tag : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let work : Region := ⟨s.gpr .x7, 2560⟩
  s.rd = [ctx, tag] ∧ s.wr = [st, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint tag ∧ st.Disjoint work ∧ tag.Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + 2560 ≤ 2 ^ 64 ∧
    rounds (s.gpr .x1)

/-- `vg_aes_gcm_stream_verify`. -/
def streamVerifyAArch64 : Contract isa where
  pre := verPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
    let h := ctxH s.mem (s.gpr .x0)
    let tl := (s.gpr .x6).toNat
    ∀ iv a c, StreamRepr s.mem (s.gpr .x2) ciph h iv a c →
      s.gpr .x3 = BitVec.ofNat 64 a.length → (s.gpr .x4).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (s.gpr .x5) tl then (s'.gpr .x0).setWidth 32 = 1
      else (s'.gpr .x0).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp

/-- What `vg_aes_gcm_seal` and `vg_aes_gcm_open` need of their common arguments:
`(ctx = x0, rounds = x1, nonce = x2, nonce_len = x3, aad = x4, aad_len = x5, data = x6,
len = x7, …)`, with `n` arguments on the stack and `work` the `w`-th. -/
def oneCore (n w : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let work : Region := ⟨stackArg s w, 2560⟩
  ctx ∈ s.rd ∧ nonce ∈ s.rd ∧ aad ∈ s.rd ∧ args s n ∈ s.rd ∧ data ∈ s.wr ∧ work ∈ s.wr ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s n) ∧ work.Disjoint (args s n) ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s w).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * n ≤ 2 ^ 64 ∧ rounds (s.gpr .x1)

/-- What `vg_aes_gcm_seal` needs: its common arguments, `tag = [sp]` and `work = [sp + 8]`. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let work : Region := ⟨stackArg s 1, 2560⟩
  s.rd = [ctx, nonce, aad, args s 2] ∧ s.wr = [data, tag, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ data.Disjoint tag ∧
    data.Disjoint work ∧ data.Disjoint (args s 2) ∧ tag.Disjoint work ∧ work.Disjoint (args s 2) ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 1).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 2 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1)

/-- The public arguments of `seal` and `open`, with `n` on the stack. -/
def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧ ∀ i < n, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_gcm_seal`. -/
def sealAArch64 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) 16
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat, bytesAt s'.mem (stackArg s 0) 16)
  pub := onePub 2

/-- What `vg_aes_gcm_open` needs: its common arguments, `tag = [sp]`, `tag_len = [sp + 8]` and
`work = [sp + 16]`. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [ctx, nonce, aad, tag, args s 3] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s 3) ∧ tag.Disjoint work ∧ work.Disjoint (args s 3) ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 3 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1)

/-- What `vg_aes_gcm_open` computes, for the arguments of `s`. -/
def openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) (stackArg s 1).toNat
    (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- What `vg_aes_gcm_open` may leak: whether it succeeds, for `rounds` of 10, 12 or 14. -/
def openLeakOf (s : State) : List Nat :=
  if ¬rounds (s.gpr .x1) then [] else [if (openRes s).isSome = true then 1 else 0]

/-- `vg_aes_gcm_open`. -/
def openAArch64 : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat
  pub s₁ s₂ := onePub 3 s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂

end VG.Proof.AesGcm.AArch64
