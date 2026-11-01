module

public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Call

/-!
# SM4-GCM on RISC-V: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Sm4/Gcm/Contract.lean`, which imply these
(`Verified.lean`). They are AES-GCM's (`Proof/AesGcm/RISCV64/Contract.lean`)
with SM4's key context and no number of rounds, so with the arguments one
register earlier. The functions call `vg_sm4_ctr32`, whose frame takes 3232
bytes of stack below the stack pointer, `vg_sm4_expand_key` (3168) and
`vg_ghash` (2048) (`stkOk3`); the buffers of `u64` are 8-byte aligned.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr ctxH gctr inc32 j0 fullTag tagLenOk encryptWith openResult)
open VG.Spec.Sm4.Gcm (KeyRepr ctxCiph)
open VG.Proof.AesGcm.RISCV64 (args onePub)

/-- The 3232 bytes below `sp` are apart from each of `rs`. -/
def stkAll3 (sp : Addr) : List Region → Prop
  | [] => True
  | r :: rs => (below sp 3232).Disjoint r ∧ stkAll3 sp rs

theorem stkAll3_mem {sp : Addr} : ∀ {rs : List Region}, stkAll3 sp rs → ∀ {r : Region}, r ∈ rs →
    (below sp 3232).Disjoint r
  | _ :: _, h, _, .head _ => h.1
  | _ :: _, h, _, .tail _ hr => stkAll3_mem h.2 hr

/-- The stack pointer is aligned, and the 3232 bytes below it, which the
callees' frames use, are apart from the buffers `rs`. -/
def stkOk3 (s : State) (rs : List Region) : Prop :=
  s.sp.toNat % 16 = 0 ∧ 3232 ≤ s.sp.toNat ∧ stkAll3 s.sp rs

/-- `vg_sm4_gcm_init(key = a0, ctx = a1, scratch = a2)`. -/
def initRISCV64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 16⟩
    let ctx : Region := ⟨s.gpr .a1, 256⟩
    let scr : Region := ⟨s.gpr .a2, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (s.gpr .a0).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 256 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + 2560 ≤ 2 ^ 64 ∧ stkOk3 s [key, ctx, scr] ∧
      (s.gpr .a1).toNat % 8 = 0 ∧ (s.gpr .a2).toNat % 8 = 0
  post s s' := KeyRepr s'.mem (s.gpr .a1) (bytesAt s.mem (s.gpr .a0) 16)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

/-- What `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt` need:
`(ctx = a0, state = a1, aad_len = a2, text_len = a3, data = a4, len = a5, scratch = a6)`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let st : Region := ⟨s.gpr .a1, 80⟩
  let data : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let scr : Region := ⟨s.gpr .a6, 2560⟩
  s.rd = [ctx] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ data.Disjoint scr ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + 2560 ≤ 2 ^ 64 ∧
    stkOk3 s [ctx, st, data, scr] ∧ (s.gpr .a0).toNat % 8 = 0 ∧
    (s.gpr .a1).toNat % 8 = 0 ∧ (s.gpr .a6).toNat % 8 = 0

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.sp = s₂.sp

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncryptRISCV64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .a0)
    let h := ctxH s.mem (s.gpr .a0)
    ∀ iv a p, StreamRepr s.mem (s.gpr .a1) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      s.gpr .a2 = BitVec.ofNat 64 a.length → (s.gpr .a3).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
      StreamRepr s'.mem (s.gpr .a1) ciph h iv a c ∧ bytesAt s'.mem (s.gpr .a4) (s.gpr .a5).toNat = c.drop p.length
  pub := streamCryptPub

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecryptRISCV64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .a0)
    let h := ctxH s.mem (s.gpr .a0)
    ∀ iv a c, StreamRepr s.mem (s.gpr .a1) ciph h iv a c →
      s.gpr .a2 = BitVec.ofNat 64 a.length → (s.gpr .a3).toNat = c.length →
      let c' := c ++ bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat
      StreamRepr s'.mem (s.gpr .a1) ciph h iv a c' ∧
        bytesAt s'.mem (s.gpr .a4) (s.gpr .a5).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := streamCryptPub

/-- What `vg_sm4_gcm_stream_finish` needs: `(ctx = a0, state = a1, aad_len = a2, text_len = a3,
tag = a4, scratch = a5)`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let st : Region := ⟨s.gpr .a1, 80⟩
  let tag : Region := ⟨s.gpr .a4, 16⟩
  let scr : Region := ⟨s.gpr .a5, 2560⟩
  s.rd = [ctx] ∧ s.wr = [st, tag, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint scr ∧ st.Disjoint tag ∧ st.Disjoint scr ∧
    tag.Disjoint scr ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .a5).toNat + 2560 ≤ 2 ^ 64 ∧ stkOk3 s [ctx, st, tag, scr] ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a1).toNat % 8 = 0 ∧ (s.gpr .a5).toNat % 8 = 0

/-- `vg_sm4_gcm_stream_finish`. -/
def streamFinishRISCV64 : Contract isa where
  pre := finPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .a0)
    let h := ctxH s.mem (s.gpr .a0)
    ∀ iv a c, StreamRepr s.mem (s.gpr .a1) ciph h iv a c →
      s.gpr .a2 = BitVec.ofNat 64 a.length → (s.gpr .a3).toNat = c.length →
      bytesAt s'.mem (s.gpr .a4) 16 = fullTag ciph h iv a c
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

/-- What `vg_sm4_gcm_stream_verify` needs: `(ctx = a0, state = a1, aad_len = a2, text_len = a3,
tag = a4, tag_len = a5, scratch = a6)`. -/
def verPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let st : Region := ⟨s.gpr .a1, 80⟩
  let tag : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let scr : Region := ⟨s.gpr .a6, 2560⟩
  s.rd = [ctx, tag] ∧ s.wr = [st, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint scr ∧ st.Disjoint tag ∧ st.Disjoint scr ∧ tag.Disjoint scr ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + 2560 ≤ 2 ^ 64 ∧
    stkOk3 s [ctx, tag, st, scr] ∧ (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a1).toNat % 8 = 0 ∧
    (s.gpr .a6).toNat % 8 = 0

/-- `vg_sm4_gcm_stream_verify`. -/
def streamVerifyRISCV64 : Contract isa where
  pre := verPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .a0)
    let h := ctxH s.mem (s.gpr .a0)
    let tl := (s.gpr .a5).toNat
    ∀ iv a c, StreamRepr s.mem (s.gpr .a1) ciph h iv a c →
      s.gpr .a2 = BitVec.ofNat 64 a.length → (s.gpr .a3).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (s.gpr .a4) tl then (s'.gpr .a0).setWidth 32 = 1
      else (s'.gpr .a0).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.sp = s₂.sp

/-- What `vg_sm4_gcm_seal` needs: `(ctx = a0, nonce = a1, nonce_len = a2, aad = a3,
aad_len = a4, data = a5, len = a6, tag = a7, scratch = [sp])`. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let nonce : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
  let aad : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
  let data : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
  let tag : Region := ⟨s.gpr .a7, 16⟩
  let scr : Region := ⟨stackArg s 0, 2560⟩
  s.rd = [ctx, nonce, aad, args s 1] ∧ s.wr = [data, tag, scr] ∧
    ctx.Disjoint data ∧ ctx.Disjoint scr ∧ nonce.Disjoint data ∧ nonce.Disjoint scr ∧
    aad.Disjoint data ∧ aad.Disjoint scr ∧ data.Disjoint tag ∧
    data.Disjoint scr ∧ data.Disjoint (args s 1) ∧ tag.Disjoint scr ∧ scr.Disjoint (args s 1) ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a7).toNat + 16 ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 ≤ 2 ^ 64 ∧
    stkOk3 s [ctx, nonce, aad, data, tag, scr, args s 1] ∧ (s.gpr .a0).toNat % 8 = 0 ∧
    (stackArg s 0).toNat % 8 = 0

/-- `vg_sm4_gcm_seal`. -/
def sealRISCV64 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .a0)) (ctxH s.mem (s.gpr .a0)) 16
        (bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat) (bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)
        (bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) =
      (bytesAt s'.mem (s.gpr .a5) (s.gpr .a6).toNat, bytesAt s'.mem (s.gpr .a7) 16)
  pub := onePub 1

/-- What `vg_sm4_gcm_open` needs: `(ctx = a0, nonce = a1, nonce_len = a2, aad = a3,
aad_len = a4, data = a5, len = a6, tag = a7, tag_len = [sp], scratch = [sp + 8])`. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let nonce : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
  let aad : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
  let data : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
  let tag : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
  let scr : Region := ⟨stackArg s 1, 2560⟩
  s.rd = [ctx, nonce, aad, tag, args s 2] ∧ s.wr = [data, scr] ∧
    ctx.Disjoint data ∧ ctx.Disjoint scr ∧ nonce.Disjoint data ∧ nonce.Disjoint scr ∧
    aad.Disjoint data ∧ aad.Disjoint scr ∧ data.Disjoint tag ∧
    data.Disjoint scr ∧ data.Disjoint (args s 2) ∧ tag.Disjoint scr ∧ scr.Disjoint (args s 2) ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + 2560 ≤ 2 ^ 64 ∧
    s.sp.toNat + 16 ≤ 2 ^ 64 ∧ stkOk3 s [ctx, nonce, aad, data, tag, scr, args s 2] ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ (stackArg s 1).toNat % 8 = 0

/-- What `vg_sm4_gcm_open` computes, in a state. -/
abbrev openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .a0)) (ctxH s.mem (s.gpr .a0)) (stackArg s 0).toNat
    (bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat) (bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)
    (bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) (bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)

/-- `vg_sm4_gcm_open`: the result in the low 32 bits of `a0`. It may leak
whether it succeeds. -/
def openRISCV64 : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .a0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .a5) (s.gpr .a6).toNat = pt
    | none => (s'.gpr .a0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .a5) (s.gpr .a6).toNat = bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat
  pub s₁ s₂ := onePub 2 s₁ s₂ ∧ (openRes s₁).isSome = (openRes s₂).isSome

end VG.Proof.Sm4Gcm.RISCV64
