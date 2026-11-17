module

public import VerifiedGarbage.Proof.AesGcm.X86.Fn
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `AesGcm.X86.Contract`, which this module and modules that import it used -/

section

/-!
# AES-GCM on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Gcm/Contract.lean`, which imply these
(`Verified.lean`). The arguments are on the stack, from `[esp + 4]`
(cdecl), and may be overwritten (`writeArgs`); each call pushes its
arguments and the return address below `esp`: 32 bytes for
`vg_aes_ctr32_to` (in place), 24 for `vg_ghash` (all `stream_init` and `stream_aad`
call), which no buffer overlaps, nor the return address.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr KeyRepr ctxCiph ctxH gctr inc32 j0 fullTag tagLenOk zeros encryptWith openResult)

/-- Whether the stack argument `i` holds 10, 12 or 14. -/
abbrev roundsOk (s : State) (i : Nat) : Prop :=
  (arg s i).toNat = 10 ∨ (arg s i).toNat = 12 ∨ (arg s i).toNat = 14

/-- All `n` stack arguments are public, and the stack pointer. -/
def pubN (n : Nat) (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < n, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_init(key, key_len, ctx, scratch)`. -/
def initPre (s : State) : Prop :=
  let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
  let ctx : Region := ⟨(arg s 2).setWidth 64, 256⟩
  let scr : Region := ⟨(arg s 3).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 16⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩
  s.rd = [key] ∧ s.wr = [ctx, scr, args] ∧
  key.Disjoint ctx ∧ key.Disjoint scr ∧ key.Disjoint args ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧
  scr.Disjoint args ∧
  ret.Disjoint key ∧ ret.Disjoint ctx ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint key ∧ stack.Disjoint ctx ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + 256 ≤ 2 ^ 32 ∧
  (arg s 3).toNat + 2560 ≤ 2 ^ 32 ∧ 32 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
  ((arg s 1).toNat = 16 ∨ (arg s 1).toNat = 24 ∨ (arg s 1).toNat = 32)

def initX86 : Contract isa where
  pre := initPre
  post s s' := KeyRepr s'.mem ((arg s 2).setWidth 64) (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub := pubN 4

/-- `vg_aes_gcm_stream_init(ctx, nonce, nonce_len, state, scratch)`. -/
def streamInitPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let nonce : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
  let st : Region := ⟨(arg s 3).setWidth 64, 80⟩
  let scr : Region := ⟨(arg s 4).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 20⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 24, 24⟩
  s.rd = [ctx, nonce] ∧ s.wr = [st, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧
  nonce.Disjoint args ∧ st.Disjoint scr ∧ st.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint nonce ∧ ret.Disjoint st ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint nonce ∧ stack.Disjoint st ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
  (arg s 3).toNat + 80 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 2560 ≤ 2 ^ 32 ∧ 24 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 24 ≤ 2 ^ 32

def streamInitX86 : Contract isa where
  pre := streamInitPre
  post s s' := ∀ ciph, StreamRepr s'.mem ((arg s 3).setWidth 64) ciph (ctxH s.mem ((arg s 0).setWidth 64))
    (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat) [] []
  pub := pubN 5

/-- `vg_aes_gcm_stream_aad(ctx, state, aad_len (2 words), data, len, scratch)`. -/
def streamAadPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let st : Region := ⟨(arg s 1).setWidth 64, 80⟩
  let data : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
  let scr : Region := ⟨(arg s 6).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 28⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 24, 24⟩
  s.rd = [ctx, data] ∧ s.wr = [st, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ st.Disjoint data ∧ st.Disjoint scr ∧
  st.Disjoint args ∧ data.Disjoint scr ∧ data.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint st ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint st ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 80 ≤ 2 ^ 32 ∧
  (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + 2560 ≤ 2 ^ 32 ∧ 24 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 32 ≤ 2 ^ 32

def streamAadX86 : Contract isa where
  pre := streamAadPre
  post s s' := ∀ ciph iv a, StreamRepr s.mem ((arg s 1).setWidth 64) ciph (ctxH s.mem ((arg s 0).setWidth 64)) iv a [] →
    arg s 3 ++ arg s 2 = BitVec.ofNat 64 a.length →
    StreamRepr s'.mem ((arg s 1).setWidth 64) ciph (ctxH s.mem ((arg s 0).setWidth 64)) iv
      (a ++ bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) []
  pub := pubN 7

/-- `vg_aes_gcm_stream_encrypt` and `_decrypt(ctx, rounds, state, aad_len, text_len, data, len, scratch)`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let st : Region := ⟨(arg s 2).setWidth 64, 80⟩
  let data : Region := ⟨(arg s 7).setWidth 64, (arg s 8).toNat⟩
  let scr : Region := ⟨(arg s 9).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 40⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩
  s.rd = [ctx] ∧ s.wr = [st, data, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ st.Disjoint data ∧
  st.Disjoint scr ∧ st.Disjoint args ∧ data.Disjoint scr ∧ data.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint st ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint st ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 80 ≤ 2 ^ 32 ∧
  (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32 ∧ (arg s 9).toNat + 2560 ≤ 2 ^ 32 ∧ 32 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 44 ≤ 2 ^ 32 ∧ roundsOk s 1

def streamEncryptX86 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
    let h := ctxH s.mem ((arg s 0).setWidth 64)
    ∀ iv a p, StreamRepr s.mem ((arg s 2).setWidth 64) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      arg s 4 ++ arg s 3 = BitVec.ofNat 64 a.length → (arg s 6 ++ arg s 5).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat)
      StreamRepr s'.mem ((arg s 2).setWidth 64) ciph h iv a c ∧
        bytesAt s'.mem ((arg s 7).setWidth 64) (arg s 8).toNat = c.drop p.length
  pub := pubN 10

def streamDecryptX86 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
    let h := ctxH s.mem ((arg s 0).setWidth 64)
    ∀ iv a c, StreamRepr s.mem ((arg s 2).setWidth 64) ciph h iv a c →
      arg s 4 ++ arg s 3 = BitVec.ofNat 64 a.length → (arg s 6 ++ arg s 5).toNat = c.length →
      let c' := c ++ bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat
      StreamRepr s'.mem ((arg s 2).setWidth 64) ciph h iv a c' ∧
        bytesAt s'.mem ((arg s 7).setWidth 64) (arg s 8).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := pubN 10

/-- `vg_aes_gcm_stream_finish(ctx, rounds, state, aad_len, text_len, tag, work)`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let st : Region := ⟨(arg s 2).setWidth 64, 80⟩
  let tag : Region := ⟨(arg s 7).setWidth 64, 16⟩
  let scr : Region := ⟨(arg s 8).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 36⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩
  s.rd = [ctx] ∧ s.wr = [st, tag, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ st.Disjoint tag ∧
  st.Disjoint scr ∧ st.Disjoint args ∧ tag.Disjoint scr ∧ tag.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint st ∧ ret.Disjoint tag ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint st ∧ stack.Disjoint tag ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 80 ≤ 2 ^ 32 ∧ (arg s 7).toNat + 16 ≤ 2 ^ 32 ∧
  (arg s 8).toNat + 2560 ≤ 2 ^ 32 ∧ 32 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 40 ≤ 2 ^ 32 ∧ roundsOk s 1

def streamFinishX86 : Contract isa where
  pre := finPre
  post s s' :=
    let ciph := ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
    let h := ctxH s.mem ((arg s 0).setWidth 64)
    ∀ iv a c, StreamRepr s.mem ((arg s 2).setWidth 64) ciph h iv a c →
      arg s 4 ++ arg s 3 = BitVec.ofNat 64 a.length → (arg s 6 ++ arg s 5).toNat = c.length →
      bytesAt s'.mem ((arg s 7).setWidth 64) 16 = fullTag ciph h iv a c
  pub := pubN 9

/-- `vg_aes_gcm_stream_verify(ctx, rounds, state, aad_len, text_len, tag, tag_len, work)`. -/
def verifyPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let st : Region := ⟨(arg s 2).setWidth 64, 80⟩
  let tag : Region := ⟨(arg s 7).setWidth 64, (arg s 8).toNat⟩
  let scr : Region := ⟨(arg s 9).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 40⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩
  s.rd = [ctx, tag] ∧ s.wr = [st, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ tag.Disjoint st ∧ tag.Disjoint scr ∧
  tag.Disjoint args ∧ st.Disjoint scr ∧ st.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint st ∧ ret.Disjoint tag ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint st ∧ stack.Disjoint tag ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 80 ≤ 2 ^ 32 ∧ (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32 ∧
  (arg s 9).toNat + 2560 ≤ 2 ^ 32 ∧ 32 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 44 ≤ 2 ^ 32 ∧ roundsOk s 1

def streamVerifyX86 : Contract isa where
  pre := verifyPre
  post s s' :=
    let ciph := ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
    let h := ctxH s.mem ((arg s 0).setWidth 64)
    ∀ iv a c, StreamRepr s.mem ((arg s 2).setWidth 64) ciph h iv a c →
      arg s 4 ++ arg s 3 = BitVec.ofNat 64 a.length → (arg s 6 ++ arg s 5).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk (arg s 8).toNat ∧ t.take (arg s 8).toNat = bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat then
        (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1
      else (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0
  pub := pubN 10

/-- `vg_aes_gcm_seal(ctx, rounds, nonce, nonce_len, aad, aad_len, data, len, tag, work)`. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let nonce : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  let aad : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
  let data : Region := ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩
  let tag : Region := ⟨(arg s 8).setWidth 64, 16⟩
  let scr : Region := ⟨(arg s 9).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 40⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩
  s.rd = [ctx, nonce, aad] ∧ s.wr = [data, tag, scr, args] ∧
  ctx.Disjoint data ∧ ctx.Disjoint tag ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ nonce.Disjoint data ∧
  nonce.Disjoint tag ∧ nonce.Disjoint scr ∧ nonce.Disjoint args ∧ aad.Disjoint data ∧ aad.Disjoint tag ∧
  aad.Disjoint scr ∧ aad.Disjoint args ∧ data.Disjoint tag ∧ data.Disjoint scr ∧ data.Disjoint args ∧
  tag.Disjoint scr ∧ tag.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧ ret.Disjoint tag ∧
  ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint nonce ∧ stack.Disjoint aad ∧ stack.Disjoint data ∧
  stack.Disjoint tag ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
  (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
  (arg s 8).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 9).toNat + 2560 ≤ 2 ^ 32 ∧ 32 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 44 ≤ 2 ^ 32 ∧ roundsOk s 1

def sealX86 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (ctxH s.mem ((arg s 0).setWidth 64)) 16
        (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
        (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) =
      (bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat, bytesAt s'.mem ((arg s 8).setWidth 64) 16)
  pub := pubN 10

/-- `vg_aes_gcm_open(ctx, rounds, nonce, nonce_len, aad, aad_len, data, len, tag, tag_len, work)`. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let nonce : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  let aad : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
  let data : Region := ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩
  let tag : Region := ⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩
  let scr : Region := ⟨(arg s 10).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 44⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩
  s.rd = [ctx, nonce, aad, tag] ∧ s.wr = [data, scr, args] ∧
  ctx.Disjoint data ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ nonce.Disjoint data ∧ nonce.Disjoint scr ∧
  nonce.Disjoint args ∧ aad.Disjoint data ∧ aad.Disjoint scr ∧ aad.Disjoint args ∧ data.Disjoint tag ∧
  data.Disjoint scr ∧ data.Disjoint args ∧ tag.Disjoint scr ∧ tag.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧ ret.Disjoint tag ∧
  ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint nonce ∧ stack.Disjoint aad ∧ stack.Disjoint data ∧
  stack.Disjoint tag ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
  (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
  (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32 ∧ (arg s 10).toNat + 2560 ≤ 2 ^ 32 ∧ 32 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 48 ≤ 2 ^ 32 ∧ roundsOk s 1

/-- What `open` computes. -/
abbrev openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (ctxH s.mem ((arg s 0).setWidth 64))
    (arg s 9).toNat (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
    (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat) (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat)
    (bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat)

def openX86 : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧ bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = pt
    | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧
      bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat
  pub s₁ s₂ := pubN 11 s₁ s₂ ∧ (openRes s₁).isSome = (openRes s₂).isSome

/-- The `u32` a function returns, from `edx:eax`: `eax`. -/
theorem ret32_eq (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt b.isLt]
  omega_using []

end VG.Proof.AesGcm.X86

end

end

/-!
# AES-GCM on x86: from the contracts to the pieces

Untrusted: everything here is checked by Lean. What the functions' proofs
share: the public data of a run (`pubOf`: the stack pointer and the stack
arguments), a `Pc` with no state satisfying it (`Pc.vacuous`), and facts
about the regions of the contracts.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

/-- The public data of a run with `n` stack arguments. -/
def pubOf (n : Nat) (s : State) : BitVec 32 × (Nat → BitVec 32) :=
  (s.gpr .esp, fun i => if i < n then arg s i else 0)

theorem pubOf_eq {n : Nat} {s₁ s₂ : State} (h : pubN n s₁ s₂) : pubOf n s₁ = pubOf n s₂ := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [pubOf, h₁, Prod.mk.injEq, true_and]
  funext i
  split
  · next hi => exact h₂ i hi
  · rfl

theorem pubOf_arg {n : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : pubOf n s = p) {i : Nat}
    (hi : i < n) : arg s i = p.2 i := by
  rw [← h]; simp only [pubOf, hi, ↓reduceIte]

theorem pubOf_esp {n : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : pubOf n s = p) :
    s.gpr .esp = p.1 := by
  rw [← h]; rfl

/-- The public data of a run with `n` stack arguments, with the arguments `i`
and `n - 1` (`W`, the last) exchanged: the pieces of the functions that take
`W` last find it at `i`. -/
def pubSw (n i : Nat) (s : State) : BitVec 32 × (Nat → BitVec 32) :=
  (s.gpr .esp, fun k => if k < n then arg s (if k = i then n - 1 else if k = n - 1 then i else k) else 0)

theorem pubSw_eq {n i : Nat} (hi : i < n) {s₁ s₂ : State} (h : pubN n s₁ s₂) : pubSw n i s₁ = pubSw n i s₂ := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [pubSw, h₁, Prod.mk.injEq, true_and]
  funext k
  split
  · next hk => exact h₂ _ (by split <;> (try split) <;> omega_arith)
  · rfl

theorem pubSw_arg {n i : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : pubSw n i s = p) {k : Nat}
    (hk : k < n) (hi : k ≠ i) (hn : k + 1 ≠ n) : arg s k = p.2 k := by
  rw [← h]; simp only [pubSw, hk, hi, show k ≠ n - 1 by omega_using [hk, hn], ↓reduceIte]

/-- `W`, at `i`. -/
theorem pubSw_W {n i m : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : pubSw n i s = p)
    (hi : i < n) (hm : n = m + 1) : arg s m = p.2 i := by
  rw [← h]; simp only [pubSw, hi, ↓reduceIte, show n - 1 = m by omega_using [hm]]

/-- The argument `i`, at `n - 1`. -/
theorem pubSw_last {n i m : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : pubSw n i s = p)
    (hi : i < n) (hm : n = m + 1) : arg s i = p.2 m := by
  rw [← h]
  simp only [pubSw, show m < n by omega_using [hm], show n - 1 = m by omega_using [hm], ↓reduceIte]
  by_cases e : m = i
  · subst e; simp
  · simp [e]

theorem pubSw_esp {n i : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : pubSw n i s = p) :
    s.gpr .esp = p.1 := by
  rw [← h]; rfl

/-- A piece from states none of which satisfies `P`. -/
theorem Pc.vacuous {α : Sort _} {P Q : α → State → Prop} {c : Prog isa} (h : ∀ a s, ¬ P a s) : Pc P c Q :=
  ⟨fun a s hs => absurd hs (h a s), RelCT.of_false fun _ _ ⟨⟨a, h₁⟩, _⟩ => h a _ h₁⟩

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := BitVec.eq_of_toNat_eq (by simp)

/-- The low word of a 64-bit length, modulo 16. -/
theorem lo_mod16 {hi lo : BitVec 32} {n : Nat} (h : hi ++ lo = BitVec.ofNat 64 n) : lo.toNat % 16 = n % 16 := by
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq] at e
  have hl := lo.isLt
  have e2 := congrArg (· % 2 ^ 32) e
  simp only [Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.zero_or, Nat.mod_eq_of_lt hl] at e2
  rw [e2, Nat.mod_mod_of_dvd _ (by decide), Nat.mod_mod_of_dvd _ (by decide)]

/-- The stack the contracts reserve, as the calls see it. -/
theorem below_eq {SP : BitVec 32} {k : Nat} (h : k ≤ SP.toNat) :
    (⟨SP.setWidth 64 - BitVec.ofNat 64 k, k⟩ : Region) = below SP k := by
  simp only [below]; rw [Taint.sub_setWidth h]

theorem ret_below {SP : BitVec 32} {k : Nat} (h : k ≤ SP.toNat) : (⟨w64 SP, 4⟩ : Region).Disjoint (below SP k) := by
  rw [← below_eq h]; exact Offset.base_disjoint_below _ (by omega_using [h])

/-- The return address stays where it is, outside a frame. -/
theorem ret_kept {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {SP : BitVec 32}
    (hd : ∀ r ∈ rs, (⟨w64 SP, 4⟩ : Region).Disjoint r) : m'.readW (w64 SP) 32 = m.readW (w64 SP) 32 :=
  hf.readW (r := ⟨w64 SP, 4⟩) (Region.contains_self _ _) hd (by decide)

theorem ofNat_lit (n : Nat) : (OfNat.ofNat n : Addr) = BitVec.ofNat 64 n := rfl

theorem ctxH_eq (m : Mem) (p : Addr) : Spec.Gcm.ctxH m p = Spec.Gcm.blockAt m (p + BitVec.ofNat 64 240) := rfl

end VG.Proof.AesGcm.X86

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86

theorem argsR_eq (s : State) (n : Nat) : argsR (s.gpr .esp) n = ⟨argAddr s 0, 4 * n⟩ := rfl

/-- The entry's first block: `W`, from the stack argument `w`, into `eax`. -/
theorem arg0_ok {s : State} {w : Nat} (hin : InRegions (s.rd ++ s.wr) (argA (s.gpr .esp) w) 4) :
    WP isa (.block [.mov .eax (argOp w)]) s fun s' => s'.gpr .eax = arg s w ∧ s'.gpr .esp = s.gpr .esp := by
  refine WP.of_runBlock ⟨_, by xrun [hin], ?_, ?_⟩
  · regs []; rfl
  · regs []

/-- The entry's stack arguments may be read. -/
theorem argIn_of {s : State} {n : Nat} (hA : Covers [argsR (s.gpr .esp) n] (s.rd ++ s.wr))
    (fa : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) {i : Nat} (hi : i < n) :
    InRegions (s.rd ++ s.wr) (argA (s.gpr .esp) i) 4 :=
  hA _ _ ⟨_, List.mem_singleton_self _, argA_contains hi fa⟩

end VG.Proof.AesGcm.X86

namespace VG.Proof.AesGcm.X86

open VG VG.X86
open VG.Spec.Gcm (StreamRepr)

/-- A streaming state is what it is outside a frame. -/
theorem streamRepr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 80⟩ : Region).Disjoint r) {ciph : Spec.Gcm.Block → Spec.Gcm.Block} {h : Spec.Gcm.Block}
    {iv a c : List Byte} (hr : StreamRepr m p ciph h iv a c) : StreamRepr m' p ciph h iv a c := by
  have sub : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ rs, (⟨p + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hk r hr => (hd r hr).sub_left (Offset.sub_base _ hk)
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hr ⊢
  obtain ⟨hj, ha, hc⟩ := hr
  have e0 := blockAt_frame hf (sub (d := 0) (k := 16) (by decide))
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e0
  refine ⟨by rw [e0, hj], ha.congr (blockAt_frame hf (sub (by decide)))
    (bytesAt_frame hf (sub (d := 32) (k := (Spec.Gcm.ghashInput a c).length % 16) (by omega_using [])) (by omega_using [])),
    hc.congr (blockAt_frame hf (sub (by decide))) (blockAt_frame hf (sub (by decide)))⟩

end VG.Proof.AesGcm.X86

namespace VG.Proof.AesGcm.X86

open VG VG.X86

/-- A piece proven for each `i`, of code that does not depend on it: its
postcondition for all of them. -/
theorem Pc.forall {α ι : Sort _} [Inhabited ι] {P : α → State → Prop} {Q : ι → α → State → Prop} {c : Prog isa}
    (h : ∀ i, Pc P c (Q i)) : Pc P c (fun a s => ∀ i, Q i a s) := by
  refine ⟨fun a s hs => ?_, (h default).ct⟩
  obtain ⟨t, s', e, -⟩ := (h default).wp a s hs
  refine ⟨t, s', e, fun i => ?_⟩
  obtain ⟨t', s'', e', q⟩ := (h i).wp a s hs
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

end VG.Proof.AesGcm.X86
