module

public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# SM4-GCM on PPC64LE: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/Contract.lean`), for SM4-GCM's signatures, which have
no number of rounds, with AES-GCM's working space of 2560 bytes and SM4's of
3264 (`sm4`), the argument after it. The artifacts'
contracts are the shared ones of `Spec/Sm4/Gcm/Contract.lean`, which imply
these (`Verified.lean`). No stack is used.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr ctxH gctr inc32 j0 fullTag tagLenOk encryptWith openResult)
open VG.Spec.Sm4.Gcm (KeyRepr ctxCiph)

/-- AES-GCM's working space's bytes. -/
abbrev scrBytes : Nat := 2560

/-- SM4's working space's bytes. -/
abbrev xBytes : Nat := 3264

/-- `vg_sm4_gcm_init(key = r3, ctx = r4, scratch = r5, sm4 = r6)`. -/
def initPPC64LE : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 16⟩
    let ctx : Region := ⟨s.gpr .r4, 256⟩
    let scr : Region := ⟨s.gpr .r5, scrBytes⟩
    let sm4 : Region := ⟨s.gpr .r6, xBytes⟩
    s.rd = [key] ∧ s.wr = [ctx, scr, sm4] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (s.gpr .r3).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 256 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + scrBytes ≤ 2 ^ 64 ∧
      key.Disjoint sm4 ∧ ctx.Disjoint sm4 ∧ scr.Disjoint sm4 ∧ (s.gpr .r6).toNat + xBytes ≤ 2 ^ 64
  post s s' := KeyRepr s'.mem (s.gpr .r4) (bytesAt s.mem (s.gpr .r3) 16)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- What `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt` need:
`(ctx = r3, state = r4, aad_len = r5, text_len = r6, data = r7, len = r8, scratch = r9,
sm4 = r10)`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let st : Region := ⟨s.gpr .r4, 80⟩
  let data : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let scr : Region := ⟨s.gpr .r9, scrBytes⟩
  let sm4 : Region := ⟨s.gpr .r10, xBytes⟩
  s.rd = [ctx] ∧ s.wr = [st, data, scr, sm4] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ data.Disjoint scr ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + scrBytes ≤ 2 ^ 64 ∧
    ctx.Disjoint sm4 ∧ st.Disjoint sm4 ∧ data.Disjoint sm4 ∧ scr.Disjoint sm4 ∧
    (s.gpr .r10).toNat + xBytes ≤ 2 ^ 64

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncryptPPC64LE : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .r3)
    let h := ctxH s.mem (s.gpr .r3)
    ∀ iv a p, StreamRepr s.mem (s.gpr .r4) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      s.gpr .r5 = BitVec.ofNat 64 a.length → (s.gpr .r6).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
      StreamRepr s'.mem (s.gpr .r4) ciph h iv a c ∧ bytesAt s'.mem (s.gpr .r7) (s.gpr .r8).toNat = c.drop p.length
  pub := streamCryptPub

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecryptPPC64LE : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .r3)
    let h := ctxH s.mem (s.gpr .r3)
    ∀ iv a c, StreamRepr s.mem (s.gpr .r4) ciph h iv a c →
      s.gpr .r5 = BitVec.ofNat 64 a.length → (s.gpr .r6).toNat = c.length →
      let c' := c ++ bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat
      StreamRepr s'.mem (s.gpr .r4) ciph h iv a c' ∧
        bytesAt s'.mem (s.gpr .r7) (s.gpr .r8).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := streamCryptPub

/-- What `vg_sm4_gcm_stream_finish` needs: `(ctx = r3, state = r4, aad_len = r5, text_len = r6,
tag = r7, scratch = r8, sm4 = r9)`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let st : Region := ⟨s.gpr .r4, 80⟩
  let tag : Region := ⟨s.gpr .r7, 16⟩
  let scr : Region := ⟨s.gpr .r8, scrBytes⟩
  let sm4 : Region := ⟨s.gpr .r9, xBytes⟩
  s.rd = [ctx] ∧ s.wr = [st, tag, scr, sm4] ∧
    ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint scr ∧ st.Disjoint tag ∧ st.Disjoint scr ∧
    tag.Disjoint scr ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + scrBytes ≤ 2 ^ 64 ∧
    ctx.Disjoint sm4 ∧ st.Disjoint sm4 ∧ tag.Disjoint sm4 ∧ scr.Disjoint sm4 ∧
    (s.gpr .r9).toNat + xBytes ≤ 2 ^ 64

/-- `vg_sm4_gcm_stream_finish`. -/
def streamFinishPPC64LE : Contract isa where
  pre := finPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .r3)
    let h := ctxH s.mem (s.gpr .r3)
    ∀ iv a c, StreamRepr s.mem (s.gpr .r4) ciph h iv a c →
      s.gpr .r5 = BitVec.ofNat 64 a.length → (s.gpr .r6).toNat = c.length →
      bytesAt s'.mem (s.gpr .r7) 16 = fullTag ciph h iv a c
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.sp = s₂.sp

/-- What `vg_sm4_gcm_stream_verify` needs: `(ctx = r3, state = r4, aad_len = r5, text_len = r6,
tag = r7, tag_len = r8, scratch = r9, sm4 = r10)`. -/
def verPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let st : Region := ⟨s.gpr .r4, 80⟩
  let tag : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let scr : Region := ⟨s.gpr .r9, scrBytes⟩
  let sm4 : Region := ⟨s.gpr .r10, xBytes⟩
  s.rd = [ctx, tag] ∧ s.wr = [st, scr, sm4] ∧
    ctx.Disjoint st ∧ ctx.Disjoint scr ∧ st.Disjoint tag ∧ st.Disjoint scr ∧ tag.Disjoint scr ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + scrBytes ≤ 2 ^ 64 ∧
    ctx.Disjoint sm4 ∧ st.Disjoint sm4 ∧ tag.Disjoint sm4 ∧ scr.Disjoint sm4 ∧
    (s.gpr .r10).toNat + xBytes ≤ 2 ^ 64

/-- `vg_sm4_gcm_stream_verify`. -/
def streamVerifyPPC64LE : Contract isa where
  pre := verPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .r3)
    let h := ctxH s.mem (s.gpr .r3)
    let tl := (s.gpr .r8).toNat
    ∀ iv a c, StreamRepr s.mem (s.gpr .r4) ciph h iv a c →
      s.gpr .r5 = BitVec.ofNat 64 a.length → (s.gpr .r6).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (s.gpr .r7) tl then (s'.gpr .r3).setWidth 32 = 1
      else (s'.gpr .r3).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp

/-- The first `n` stack arguments, at `sp + 96`. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

/-- What `vg_sm4_gcm_seal` needs: `(ctx = r3, nonce = r4, nonce_len = r5, aad = r6, aad_len = r7,
data = r8, len = r9, tag = r10, scratch = [sp + 96], sm4 = [sp + 104])`. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let nonce : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
  let aad : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let tag : Region := ⟨s.gpr .r10, 16⟩
  let scr : Region := ⟨stackArg s 0, scrBytes⟩
  let sm4 : Region := ⟨stackArg s 1, xBytes⟩
  s.rd = [ctx, nonce, aad, args s 2] ∧ s.wr = [data, tag, scr, sm4] ∧
    ctx.Disjoint data ∧ ctx.Disjoint scr ∧ nonce.Disjoint data ∧ nonce.Disjoint scr ∧
    aad.Disjoint data ∧ aad.Disjoint scr ∧ data.Disjoint tag ∧
    data.Disjoint scr ∧ data.Disjoint (args s 2) ∧ tag.Disjoint scr ∧ scr.Disjoint (args s 2) ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r10).toNat + 16 ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + scrBytes ≤ 2 ^ 64 ∧ s.sp.toNat + 112 ≤ 2 ^ 64 ∧
    ctx.Disjoint sm4 ∧ nonce.Disjoint sm4 ∧ aad.Disjoint sm4 ∧ data.Disjoint sm4 ∧ tag.Disjoint sm4 ∧
    scr.Disjoint sm4 ∧ sm4.Disjoint (args s 2) ∧ (stackArg s 1).toNat + xBytes ≤ 2 ^ 64

/-- The public arguments of `seal` and `open`, with `n` on the stack. -/
def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp ∧
    ∀ i < n, stackArg s₁ i = stackArg s₂ i

/-- `vg_sm4_gcm_seal`. -/
def sealPPC64LE : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .r3)) (ctxH s.mem (s.gpr .r3)) 16
        (bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat) (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat) =
      (bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat, bytesAt s'.mem (s.gpr .r10) 16)
  pub := onePub 2

/-- What `vg_sm4_gcm_open` needs: `(ctx = r3, nonce = r4, nonce_len = r5, aad = r6, aad_len = r7,
data = r8, len = r9, tag = r10, tag_len = [sp + 96], scratch = [sp + 104], sm4 = [sp + 112])`. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let nonce : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
  let aad : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let tag : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
  let scr : Region := ⟨stackArg s 1, scrBytes⟩
  let sm4 : Region := ⟨stackArg s 2, xBytes⟩
  s.rd = [ctx, nonce, aad, tag, args s 3] ∧ s.wr = [data, scr, sm4] ∧
    ctx.Disjoint data ∧ ctx.Disjoint scr ∧ nonce.Disjoint data ∧ nonce.Disjoint scr ∧
    aad.Disjoint data ∧ aad.Disjoint scr ∧ data.Disjoint tag ∧
    data.Disjoint scr ∧ data.Disjoint (args s 3) ∧ tag.Disjoint scr ∧ scr.Disjoint (args s 3) ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + scrBytes ≤ 2 ^ 64 ∧
    s.sp.toNat + 120 ≤ 2 ^ 64 ∧
    ctx.Disjoint sm4 ∧ nonce.Disjoint sm4 ∧ aad.Disjoint sm4 ∧ data.Disjoint sm4 ∧ tag.Disjoint sm4 ∧
    scr.Disjoint sm4 ∧ sm4.Disjoint (args s 3) ∧ (stackArg s 2).toNat + xBytes ≤ 2 ^ 64

/-- What `vg_sm4_gcm_open` computes, in a state. -/
abbrev openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .r3)) (ctxH s.mem (s.gpr .r3)) (stackArg s 0).toNat
    (bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat) (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat) (bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)

/-- `vg_sm4_gcm_open`: the result in the low 32 bits of `r3`. It may leak
whether it succeeds. -/
def openPPC64LE : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .r3).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = pt
    | none => (s'.gpr .r3).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
  pub s₁ s₂ := onePub 3 s₁ s₂ ∧ (openRes s₁).isSome = (openRes s₂).isSome

end VG.Proof.Sm4Gcm.PPC64LE
