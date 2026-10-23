module

public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-GCM on PPC64LE: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Gcm/Contract.lean`, which imply these
(`Verified.lean`). A call (`bl`) stores nothing in memory, so no stack is
used.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr KeyRepr ctxCiph ctxH gctr inc32 j0 fullTag tagLenOk encryptWith openResult)

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- `vg_aes_gcm_init(key = r3, key_len = r4, ctx = r5, scratch = r6)`. -/
def initPPC64LE : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let ctx : Region := ⟨s.gpr .r5, 256⟩
    let scr : Region := ⟨s.gpr .r6, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (s.gpr .r5).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 16 ∨ (s.gpr .r4).toNat = 24 ∨ (s.gpr .r4).toNat = 32)
  post s s' := KeyRepr s'.mem (s.gpr .r5) (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- `vg_aes_gcm_stream_init(ctx = r3, nonce = r4, nonce_len = r5, state = r6, scratch = r7)`. -/
def streamInitPPC64LE : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .r3, 256⟩
    let nonce : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
    let st : Region := ⟨s.gpr .r6, 80⟩
    let scr : Region := ⟨s.gpr .r7, 2560⟩
    s.rd = [ctx, nonce] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧ st.Disjoint scr ∧
      (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + 2560 ≤ 2 ^ 64
  post s s' := ∀ ciph, StreamRepr s'.mem (s.gpr .r6) ciph (ctxH s.mem (s.gpr .r3))
    (bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat) [] []
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

/-- `vg_aes_gcm_stream_aad(ctx = r3, state = r4, aad_len = r5, data = r6, len = r7, scratch = r8)`. -/
def streamAadPPC64LE : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .r3, 256⟩
    let st : Region := ⟨s.gpr .r4, 80⟩
    let data : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 2560⟩
    s.rd = [ctx, data] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ data.Disjoint st ∧ data.Disjoint scr ∧ st.Disjoint scr ∧
      (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r4).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 2560 ≤ 2 ^ 64
  post s s' := ∀ ciph iv a, StreamRepr s.mem (s.gpr .r4) ciph (ctxH s.mem (s.gpr .r3)) iv a [] →
    s.gpr .r5 = BitVec.ofNat 64 a.length →
    StreamRepr s'.mem (s.gpr .r4) ciph (ctxH s.mem (s.gpr .r3)) iv
      (a ++ bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat) []
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.sp = s₂.sp

/-- What `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` need:
`(ctx = r3, rounds = r4, state = r5, aad_len = r6, text_len = r7, data = r8, len = r9,
scratch = r10)`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let st : Region := ⟨s.gpr .r5, 80⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let scr : Region := ⟨s.gpr .r10, 2560⟩
  s.rd = [ctx] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ data.Disjoint scr ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + 2560 ≤ 2 ^ 64 ∧
    rounds (s.gpr .r4)

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncryptPPC64LE : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat
    let h := ctxH s.mem (s.gpr .r3)
    ∀ iv a p, StreamRepr s.mem (s.gpr .r5) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      s.gpr .r6 = BitVec.ofNat 64 a.length → (s.gpr .r7).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      StreamRepr s'.mem (s.gpr .r5) ciph h iv a c ∧ bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = c.drop p.length
  pub := streamCryptPub

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecryptPPC64LE : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat
    let h := ctxH s.mem (s.gpr .r3)
    ∀ iv a c, StreamRepr s.mem (s.gpr .r5) ciph h iv a c →
      s.gpr .r6 = BitVec.ofNat 64 a.length → (s.gpr .r7).toNat = c.length →
      let c' := c ++ bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
      StreamRepr s'.mem (s.gpr .r5) ciph h iv a c' ∧
        bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := streamCryptPub

/-- What `vg_aes_gcm_stream_finish` needs: `(ctx = r3, rounds = r4, state = r5, aad_len = r6,
text_len = r7, tag = r8, scratch = r9)`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let st : Region := ⟨s.gpr .r5, 80⟩
  let tag : Region := ⟨s.gpr .r8, 16⟩
  let scr : Region := ⟨s.gpr .r9, 2560⟩
  s.rd = [ctx] ∧ s.wr = [st, tag, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint scr ∧ st.Disjoint tag ∧ st.Disjoint scr ∧
    tag.Disjoint scr ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + 2560 ≤ 2 ^ 64 ∧ rounds (s.gpr .r4)

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinishPPC64LE : Contract isa where
  pre := finPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat
    let h := ctxH s.mem (s.gpr .r3)
    ∀ iv a c, StreamRepr s.mem (s.gpr .r5) ciph h iv a c →
      s.gpr .r6 = BitVec.ofNat 64 a.length → (s.gpr .r7).toNat = c.length →
      bytesAt s'.mem (s.gpr .r8) 16 = fullTag ciph h iv a c
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.sp = s₂.sp

/-- What `vg_aes_gcm_stream_verify` needs: `(ctx = r3, rounds = r4, state = r5, aad_len = r6,
text_len = r7, tag = r8, tag_len = r9, scratch = r10)`. -/
def verPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let st : Region := ⟨s.gpr .r5, 80⟩
  let tag : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let scr : Region := ⟨s.gpr .r10, 2560⟩
  s.rd = [ctx, tag] ∧ s.wr = [st, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint scr ∧ st.Disjoint tag ∧ st.Disjoint scr ∧ tag.Disjoint scr ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + 2560 ≤ 2 ^ 64 ∧ rounds (s.gpr .r4)

/-- `vg_aes_gcm_stream_verify`. -/
def streamVerifyPPC64LE : Contract isa where
  pre := verPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat
    let h := ctxH s.mem (s.gpr .r3)
    let tl := (s.gpr .r9).toNat
    ∀ iv a c, StreamRepr s.mem (s.gpr .r5) ciph h iv a c →
      s.gpr .r6 = BitVec.ofNat 64 a.length → (s.gpr .r7).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (s.gpr .r8) tl then (s'.gpr .r3).setWidth 32 = 1
      else (s'.gpr .r3).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp

/-- The first `n` stack arguments, at `sp + 96`. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

/-- What `vg_aes_gcm_seal` needs: `(ctx = r3, rounds = r4, nonce = r5, nonce_len = r6, aad = r7,
aad_len = r8, data = r9, len = r10, tag = [sp + 96], scratch = [sp + 104])`. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let nonce : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  let aad : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let scr : Region := ⟨stackArg s 1, 2560⟩
  s.rd = [ctx, nonce, aad, args s 2] ∧ s.wr = [data, tag, scr] ∧
    ctx.Disjoint data ∧ ctx.Disjoint scr ∧ nonce.Disjoint data ∧ nonce.Disjoint scr ∧
    aad.Disjoint data ∧ aad.Disjoint scr ∧ data.Disjoint tag ∧
    data.Disjoint scr ∧ data.Disjoint (args s 2) ∧ tag.Disjoint scr ∧ scr.Disjoint (args s 2) ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
    (stackArg s 1).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 112 ≤ 2 ^ 64 ∧ rounds (s.gpr .r4)

/-- The public arguments of `seal` and `open`, with `n` on the stack. -/
def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp ∧
    ∀ i < n, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_gcm_seal`. -/
def sealPPC64LE : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (ctxH s.mem (s.gpr .r3)) 16
        (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
        (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) =
      (bytesAt s'.mem (s.gpr .r9) (s.gpr .r10).toNat, bytesAt s'.mem (stackArg s 0) 16)
  pub := onePub 2

/-- What `vg_aes_gcm_open` needs: `(ctx = r3, rounds = r4, nonce = r5, nonce_len = r6, aad = r7,
aad_len = r8, data = r9, len = r10, tag = [sp + 96], tag_len = [sp + 104], scratch = [sp + 112])`. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let nonce : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  let aad : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let scr : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [ctx, nonce, aad, tag, args s 3] ∧ s.wr = [data, scr] ∧
    ctx.Disjoint data ∧ ctx.Disjoint scr ∧ nonce.Disjoint data ∧ nonce.Disjoint scr ∧
    aad.Disjoint data ∧ aad.Disjoint scr ∧ data.Disjoint tag ∧
    data.Disjoint scr ∧ data.Disjoint (args s 3) ∧ tag.Disjoint scr ∧ scr.Disjoint (args s 3) ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧
    s.sp.toNat + 120 ≤ 2 ^ 64 ∧ rounds (s.gpr .r4)

/-- What `vg_aes_gcm_open` computes, in a state. -/
abbrev openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (ctxH s.mem (s.gpr .r3)) (stackArg s 1).toNat
    (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
    (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- `vg_aes_gcm_open`: the result in the low 32 bits of `r3`. It may leak
whether it succeeds. -/
def openPPC64LE : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .r3).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .r9) (s.gpr .r10).toNat = pt
    | none => (s'.gpr .r3).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .r9) (s.gpr .r10).toNat = bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat
  pub s₁ s₂ := onePub 3 s₁ s₂ ∧ (rounds (s₁.gpr .r4) → (openRes s₁).isSome = (openRes s₂).isSome)

end VG.Proof.AesGcm.PPC64LE
