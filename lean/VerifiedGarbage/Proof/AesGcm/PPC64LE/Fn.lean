module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.J0
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `AesGcm.PPC64LE.Contract`, which the modules that import this one used -/

section

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
    let scr : Region := ⟨s.gpr .r6, 288⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (s.gpr .r5).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 288 ≤ 2 ^ 64 ∧
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
    let scr : Region := ⟨s.gpr .r7, 288⟩
    s.rd = [ctx, nonce] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧ st.Disjoint scr ∧
      (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + 288 ≤ 2 ^ 64
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
    let scr : Region := ⟨s.gpr .r8, 288⟩
    s.rd = [ctx, data] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ data.Disjoint st ∧ data.Disjoint scr ∧ st.Disjoint scr ∧
      (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r4).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 288 ≤ 2 ^ 64
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
  let scr : Region := ⟨s.gpr .r10, 288⟩
  s.rd = [ctx] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ data.Disjoint scr ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + 288 ≤ 2 ^ 64 ∧
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
  let scr : Region := ⟨s.gpr .r9, 288⟩
  s.rd = [ctx] ∧ s.wr = [st, tag, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint scr ∧ st.Disjoint tag ∧ st.Disjoint scr ∧
    tag.Disjoint scr ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + 288 ≤ 2 ^ 64 ∧ rounds (s.gpr .r4)

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
  let scr : Region := ⟨s.gpr .r10, 288⟩
  s.rd = [ctx, tag] ∧ s.wr = [st, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint scr ∧ st.Disjoint tag ∧ st.Disjoint scr ∧ tag.Disjoint scr ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + 288 ≤ 2 ^ 64 ∧ rounds (s.gpr .r4)

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

end

end

/-!
# AES-GCM on PPC64LE: the functions' entry and exit

Untrusted: everything here is checked by Lean. Every function saves our
caller's `r18`–`r31` and its return address in `W` on entry (`save_ok`,
`Spill.save_ok`) and restores them on exit (`restore_ok`), which with the
other nonvolatile registers (`r2`, `r14`–`r17`, which the pieces keep:
`Env`) gives `abiPreserved`. Also here: the layout from the disjointness of
the buffers (`Lay.of`), and that the pieces never write the saved slots.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)

/-- Where `save` puts our caller's registers and return address. -/
def SavedAt (m : Mem) (w : Addr) (s₀ : State) : Prop :=
  Spill.Saved w s₀.gpr saved m ∧ m.readW (w + BitVec.ofNat 64 lrO) 64 = s₀.lr

/-- The saved registers' and return address's slots. -/
abbrev savedR (w : Addr) : Region := ⟨w + BitVec.ofNat 64 128, 120⟩

theorem saved_bound : ∀ p ∈ saved, 128 ≤ p.2 ∧ p.2 + 8 ≤ 240 := by decide

theorem saved_fits : Spill.Fits saved := by decide

theorem save_eq (b : Reg) :
    save b = Spill.saveCode b saved ++ ([.mflr .r0, .store .d .r0 b lrO, mov .r31 b] : List Instr) := rfl

theorem restore_eq :
    restore = ([mov .r12 .r31, .load .d .r0 .r12 lrO, .mtlr .r0] : List Instr) ++
      Spill.restoreCode .r12 saved := rfl

/-- Saving the registers and the return address in `W`, at `b`. -/
theorem save_ok {s : State} {b : Reg} {n : Nat} (hb0 : b ≠ .r0) (hw : Covers [⟨s.gpr b, n⟩] s.wr)
    (hn : 248 ≤ n := by decide) :
    WP isa (.block (save b)) s fun s' =>
      (∀ r, r ≠ .r0 → r ≠ .r31 → s'.gpr r = s.gpr r) ∧ s'.gpr .r31 = s.gpr b ∧
      Keeps' s s' ∧ SavedAt s'.mem (s.gpr b) s ∧ Frame [savedR (s.gpr b)] s.mem s'.mem := by
  replace hw := covers_prefix hw hn
  rw [save_eq]
  refine Spill.save_ok hb0 (fun p hp => by have := saved_bound p hp; revert p; decide)
    (fun p hp => in_off hw (by have := saved_bound p hp; omega_using [this]) (by decide)) ?_
  generalize hM : Spill.saveMem s.mem (s.gpr b) s.gpr saved = M
  have hl := in_off hw (show lrO + 8 ≤ 248 by decide) (by decide)
  have hb0' : (b = .r0) = False := eq_false hb0
  simp only [lrO] at hl
  crun [lrO, hb0', hl, mov, BitVec.or_self, write_8]
  refine ⟨fun r a c => by simp [a, c], ⟨rfl, rfl, rfl, rfl⟩, ⟨?_, ?_⟩, ?_⟩
  · have hS := Spill.saveMem_saved saved_fits s.mem (s.gpr b) s.gpr
    rw [hM] at hS
    refine hS.frame (rs := [⟨s.gpr b + BitVec.ofNat 64 240, 8⟩])
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun p hp r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have := saved_bound p hp
    exact Offset.disjoint _ (.inl (by omega_using [this])) (by omega_using [this]) (by decide)
  · simp only [lrO]; exact Mem.readW_writeW_self64 _ _ _
  · rw [← hM]
    exact (Spill.saveMem_frame (lo := 128) (n := 120) (fun p hp => by have := saved_bound p hp; omega_using [this])
      (by decide) _ _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide)
        (by decide))

/-- The saved slots stay as they are, outside a frame. -/
theorem SavedAt.frame {m m' : Mem} {w : Addr} {s₀ : State} (h : SavedAt m w s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savedR w).Disjoint r) : SavedAt m' w s₀ := by
  refine ⟨h.1.frame hf fun p hp r hr => (hd r hr).sub_left ?_, ?_⟩
  · have := saved_bound p hp
    exact Offset.sub _ (by omega_using [this]) (by omega_using [this])
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide)
      (by decide))) (by decide)]
    exact h.2

/-- The end of every function: our caller's registers and return address
restored, from `W` in `r31`. -/
theorem restore_ok {s s₀ : State} {w : Addr} (h31 : s.gpr .r31 = w)
    {n : Nat} (hr : Covers [⟨w, n⟩] (s.rd ++ s.wr)) (hs : SavedAt s.mem w s₀) (hsp : s.sp = s₀.sp)
    (hk : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s.gpr r = s₀.gpr r) (hn : 248 ≤ n := by decide) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  replace hr := covers_prefix hr hn
  rw [restore_eq]
  have hl := in_off hr (show lrO + 8 ≤ 248 by decide) (by decide)
  have h₁ : WP isa (.block [mov .r12 .r31, .load .d .r0 .r12 lrO, .mtlr .r0]) s fun s₁ =>
      s₁.gpr .r12 = w ∧ s₁.lr = s₀.lr ∧ (∀ r, r ≠ .r0 → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
    have hl' := hs.2
    simp only [lrO] at hl hl'
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, mov, State.write, addr,
      State.load, Size.bytes, BitVec.setWidth_eq, h31, hl, BitVec.or_self, Proof.Gcm.PPC64LE.read_8,
      hl', Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq, ne_eq,
      not_false_eq_true, Nat.reduceLT, Nat.reducePow, Nat.reduceMod, ↓reduceIte, and_self, implies_true,
      lrO, true_and, and_true]
    exact fun r a b => by simp [a, b]
  refine WP.block_append (WP.mono h₁ fun s₁ ⟨h12, hlr, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ => ?_)
  refine WP.mono (Spill.restore_wp (by decide) h12 (fun p hp => by have := saved_bound p hp; revert p; decide)
    (by decide) (fun p hp => by
      rw [hrd₁, hwr₁]; exact in_off hr (by have := saved_bound p hp; omega_using [this]) (by decide))
    (hm₁ ▸ hs.1)) fun s' h => ?_
  refine ⟨⟨fun r hr => h.gpr_of ?_, by rw [h.sp, hsp₁, hsp], by rw [h.lr, hlr]⟩,
    by rw [h.mem, hm₁], ?_, by rw [h.rd, hrd₁], by rw [h.wr, hwr₁]⟩
  · by_cases hm : r ∈ saved.map Prod.fst
    · exact .inl hm
    · right
      have hr' : r ∈ [Reg.r2, .r14, .r15, .r16, .r17] := by revert hm hr; revert r; decide
      rw [hg₁ r (by revert hr'; revert r; decide) (by revert hr'; revert r; decide), hk r hr']
  · rw [h.other _ (by decide), hg₁ _ (by decide) (by decide)]

/-- The layout, from the disjointness of the context, the state and `W` (of
at least the 288 bytes the pieces use). -/
theorem Lay.of {c st w : Addr} {n : Nat} (cw : c.toNat + 256 ≤ 2 ^ 64) (sw : st.toNat + 80 ≤ 2 ^ 64)
    (ww : w.toNat + n ≤ 2 ^ 64) (cs : (⟨c, 256⟩ : Region).Disjoint ⟨st, 80⟩)
    (cW : (⟨c, 256⟩ : Region).Disjoint ⟨w, n⟩) (sW : (⟨st, 80⟩ : Region).Disjoint ⟨w, n⟩)
    (hn : 288 ≤ n := by decide) :
    Lay c st w :=
  ⟨cw, sw, by omega_using [ww, hn], cs, cW.sub_right (Region.sub_prefix hn),
    sW.sub_right (Region.sub_prefix (by omega_using [hn])),
    sW.sub_right (Offset.sub_base _ (by omega_using [hn]))⟩

/-- A run that satisfies `R`, and for each `i` with `P i`, `Q i`. -/
theorem WP.forall_det {c : Prog isa} {s : State} {ι : Sort _} {P : ι → Prop} {Q : ι → State → Prop}
    {R : State → Prop} (h₀ : WP isa c s R) (h : ∀ i, P i → WP isa c s (Q i)) :
    WP isa c s fun s' => R s' ∧ ∀ i, P i → Q i s' := by
  obtain ⟨t, s', e, r⟩ := h₀
  refine ⟨t, s', e, r, fun i hi => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h i hi
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

theorem toNat_mod16 (n : Nat) : (BitVec.ofNat 64 n).toNat % 16 = n % 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

theorem ctxH_eq (m : Mem) (p : Addr) : Spec.Gcm.ctxH m p = Spec.Gcm.blockAt m (p + BitVec.ofNat 64 240) :=
  rfl

section
variable {c st w : Addr} (L : Lay c st w)
include L

omit L in
theorem saved_w {d k : Nat} (hd : d + k ≤ 288) (ho : d + k ≤ 128 ∨ 248 ≤ d) :
    (savedR w).Disjoint ⟨w + BitVec.ofNat 64 d, k⟩ :=
  Lay.w_w (by omega_using [ho]) (by decide) hd

theorem Lay.saved_st {d k : Nat} (hd : d + k ≤ 80) : (savedR w).Disjoint ⟨st + BitVec.ofNat 64 d, k⟩ :=
  (L.st_w hd (.inr ⟨by decide, by decide⟩)).symm

theorem saved_absFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) :
    ∀ r ∈ absFrame st w yo, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact L.saved_st (by omega_using [hyo])
  · exact L.saved_st (by decide)

theorem saved_j0Frame : ∀ r ∈ j0Frame st w, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 80) (by decide)
  · exact saved_w (by decide) (.inl (by decide))

end

end VG.Proof.AesGcm.PPC64LE
