import VerifiedGarbage.Proof.AesGcm.X86.Fn
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Cmac.Dbl32

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Contract`. -/
section

/-!
# AES-GCM on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Gcm/Contract.lean`, which imply these
(`Verified.lean`). The arguments are on the stack, from `[esp + 4]`
(cdecl), and may be overwritten (`writeArgs`); each call pushes its
arguments and the return address below `esp`: 28 bytes for
`vg_aes_ctr32`, 24 for `vg_ghash` (all `stream_init` and `stream_aad`
call), which no buffer overlaps, nor the return address.
-/

namespace VG.Proof.AesGcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr KeyRepr ctxCiph ctxH gctr inc32 j0 fullTag tagLenOk zeros encryptWith openResult)

/-- Whether the stack argument `i` holds 10, 12 or 14. -/
abbrev roundsOk (s : State) (i : Nat) : Prop :=
  (VG.X86.arg s i).toNat = 10 ∨ (VG.X86.arg s i).toNat = 12 ∨ (VG.X86.arg s i).toNat = 14

/-- All `n` stack arguments are public, and the stack pointer. -/
def pubN (n : Nat) (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < n, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `vg_aes_gcm_init(key, key_len, ctx, scratch)`. -/
def initPre (s : State) : Prop :=
  let key : Region := ⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩
  let ctx : Region := ⟨(VG.X86.arg s 2).setWidth 64, 256⟩
  let scr : Region := ⟨(VG.X86.arg s 3).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 16⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 28, 28⟩
  s.rd = [key] ∧ s.wr = [ctx, scr, args] ∧
  key.Disjoint ctx ∧ key.Disjoint scr ∧ key.Disjoint args ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧
  scr.Disjoint args ∧
  ret.Disjoint key ∧ ret.Disjoint ctx ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint key ∧ stack.Disjoint ctx ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (VG.X86.arg s 0).toNat + (VG.X86.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + 256 ≤ 2 ^ 32 ∧
  (VG.X86.arg s 3).toNat + 2560 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
  ((VG.X86.arg s 1).toNat = 16 ∨ (VG.X86.arg s 1).toNat = 24 ∨ (VG.X86.arg s 1).toNat = 32)

def initX86 : Contract isa where
  pre := VG.Proof.AesGcm.X86.initPre
  post s s' := KeyRepr s'.mem ((VG.X86.arg s 2).setWidth 64) (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat)
  pub := VG.Proof.AesGcm.X86.pubN 4

/-- `vg_aes_gcm_stream_init(ctx, nonce, nonce_len, state, scratch)`. -/
def streamInitPre (s : State) : Prop :=
  let ctx : Region := ⟨(VG.X86.arg s 0).setWidth 64, 256⟩
  let nonce : Region := ⟨(VG.X86.arg s 1).setWidth 64, (VG.X86.arg s 2).toNat⟩
  let st : Region := ⟨(VG.X86.arg s 3).setWidth 64, 80⟩
  let scr : Region := ⟨(VG.X86.arg s 4).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 20⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 24, 24⟩
  s.rd = [ctx, nonce] ∧ s.wr = [st, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧
  nonce.Disjoint args ∧ st.Disjoint scr ∧ st.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint nonce ∧ ret.Disjoint st ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint nonce ∧ stack.Disjoint st ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (VG.X86.arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + (VG.X86.arg s 2).toNat ≤ 2 ^ 32 ∧
  (VG.X86.arg s 3).toNat + 80 ≤ 2 ^ 32 ∧ (VG.X86.arg s 4).toNat + 2560 ≤ 2 ^ 32 ∧ 24 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 24 ≤ 2 ^ 32

def streamInitX86 : Contract isa where
  pre := VG.Proof.AesGcm.X86.streamInitPre
  post s s' := ∀ ciph, StreamRepr s'.mem ((VG.X86.arg s 3).setWidth 64) ciph (ctxH s.mem ((VG.X86.arg s 0).setWidth 64))
    (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 1).setWidth 64) (VG.X86.arg s 2).toNat) [] []
  pub := VG.Proof.AesGcm.X86.pubN 5

/-- `vg_aes_gcm_stream_aad(ctx, state, aad_len (2 words), data, len, scratch)`. -/
def streamAadPre (s : State) : Prop :=
  let ctx : Region := ⟨(VG.X86.arg s 0).setWidth 64, 256⟩
  let st : Region := ⟨(VG.X86.arg s 1).setWidth 64, 80⟩
  let data : Region := ⟨(VG.X86.arg s 4).setWidth 64, (VG.X86.arg s 5).toNat⟩
  let scr : Region := ⟨(VG.X86.arg s 6).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 28⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 24, 24⟩
  s.rd = [ctx, data] ∧ s.wr = [st, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ st.Disjoint data ∧ st.Disjoint scr ∧
  st.Disjoint args ∧ data.Disjoint scr ∧ data.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint st ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint st ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (VG.X86.arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + 80 ≤ 2 ^ 32 ∧
  (VG.X86.arg s 4).toNat + (VG.X86.arg s 5).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 6).toNat + 2560 ≤ 2 ^ 32 ∧ 24 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 32 ≤ 2 ^ 32

def streamAadX86 : Contract isa where
  pre := VG.Proof.AesGcm.X86.streamAadPre
  post s s' := ∀ ciph iv a, StreamRepr s.mem ((VG.X86.arg s 1).setWidth 64) ciph (ctxH s.mem ((VG.X86.arg s 0).setWidth 64)) iv a [] →
    VG.X86.arg s 3 ++ VG.X86.arg s 2 = BitVec.ofNat 64 a.length →
    StreamRepr s'.mem ((VG.X86.arg s 1).setWidth 64) ciph (ctxH s.mem ((VG.X86.arg s 0).setWidth 64)) iv
      (a ++ VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 4).setWidth 64) (VG.X86.arg s 5).toNat) []
  pub := VG.Proof.AesGcm.X86.pubN 7

/-- `vg_aes_gcm_stream_encrypt` and `_decrypt(ctx, rounds, state, aad_len, text_len, data, len, scratch)`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨(VG.X86.arg s 0).setWidth 64, 256⟩
  let st : Region := ⟨(VG.X86.arg s 2).setWidth 64, 80⟩
  let data : Region := ⟨(VG.X86.arg s 7).setWidth 64, (VG.X86.arg s 8).toNat⟩
  let scr : Region := ⟨(VG.X86.arg s 9).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 40⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 28, 28⟩
  s.rd = [ctx] ∧ s.wr = [st, data, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ st.Disjoint data ∧
  st.Disjoint scr ∧ st.Disjoint args ∧ data.Disjoint scr ∧ data.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint st ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint st ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (VG.X86.arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + 80 ≤ 2 ^ 32 ∧
  (VG.X86.arg s 7).toNat + (VG.X86.arg s 8).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 9).toNat + 2560 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 44 ≤ 2 ^ 32 ∧ VG.Proof.AesGcm.X86.roundsOk s 1

def streamEncryptX86 : Contract isa where
  pre := VG.Proof.AesGcm.X86.streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat
    let h := ctxH s.mem ((VG.X86.arg s 0).setWidth 64)
    ∀ iv a p, StreamRepr s.mem ((VG.X86.arg s 2).setWidth 64) ciph h iv a (gctr ciph (inc32 (VG.Spec.Gcm.j0 h iv)) p) →
      VG.X86.arg s 4 ++ VG.X86.arg s 3 = BitVec.ofNat 64 a.length → (VG.X86.arg s 6 ++ VG.X86.arg s 5).toNat = p.length →
      let c := gctr ciph (inc32 (VG.Spec.Gcm.j0 h iv)) (p ++ VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 7).setWidth 64) (VG.X86.arg s 8).toNat)
      StreamRepr s'.mem ((VG.X86.arg s 2).setWidth 64) ciph h iv a c ∧
        VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 7).setWidth 64) (VG.X86.arg s 8).toNat = c.drop p.length
  pub := VG.Proof.AesGcm.X86.pubN 10

def streamDecryptX86 : Contract isa where
  pre := VG.Proof.AesGcm.X86.streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat
    let h := ctxH s.mem ((VG.X86.arg s 0).setWidth 64)
    ∀ iv a c, StreamRepr s.mem ((VG.X86.arg s 2).setWidth 64) ciph h iv a c →
      VG.X86.arg s 4 ++ VG.X86.arg s 3 = BitVec.ofNat 64 a.length → (VG.X86.arg s 6 ++ VG.X86.arg s 5).toNat = c.length →
      let c' := c ++ VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 7).setWidth 64) (VG.X86.arg s 8).toNat
      StreamRepr s'.mem ((VG.X86.arg s 2).setWidth 64) ciph h iv a c' ∧
        VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 7).setWidth 64) (VG.X86.arg s 8).toNat = (gctr ciph (inc32 (VG.Spec.Gcm.j0 h iv)) c').drop c.length
  pub := VG.Proof.AesGcm.X86.pubN 10

/-- `vg_aes_gcm_stream_finish(ctx, rounds, state, aad_len, text_len, tag, work)`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨(VG.X86.arg s 0).setWidth 64, 256⟩
  let st : Region := ⟨(VG.X86.arg s 2).setWidth 64, 80⟩
  let tag : Region := ⟨(VG.X86.arg s 7).setWidth 64, 16⟩
  let scr : Region := ⟨(VG.X86.arg s 8).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 36⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 28, 28⟩
  s.rd = [ctx] ∧ s.wr = [st, tag, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ st.Disjoint tag ∧
  st.Disjoint scr ∧ st.Disjoint args ∧ tag.Disjoint scr ∧ tag.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint st ∧ ret.Disjoint tag ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint st ∧ stack.Disjoint tag ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (VG.X86.arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + 80 ≤ 2 ^ 32 ∧ (VG.X86.arg s 7).toNat + 16 ≤ 2 ^ 32 ∧
  (VG.X86.arg s 8).toNat + 2560 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 40 ≤ 2 ^ 32 ∧ VG.Proof.AesGcm.X86.roundsOk s 1

def streamFinishX86 : Contract isa where
  pre := VG.Proof.AesGcm.X86.finPre
  post s s' :=
    let ciph := ctxCiph s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat
    let h := ctxH s.mem ((VG.X86.arg s 0).setWidth 64)
    ∀ iv a c, StreamRepr s.mem ((VG.X86.arg s 2).setWidth 64) ciph h iv a c →
      VG.X86.arg s 4 ++ VG.X86.arg s 3 = BitVec.ofNat 64 a.length → (VG.X86.arg s 6 ++ VG.X86.arg s 5).toNat = c.length →
      VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 7).setWidth 64) 16 = fullTag ciph h iv a c
  pub := VG.Proof.AesGcm.X86.pubN 9

/-- `vg_aes_gcm_stream_verify(ctx, rounds, state, aad_len, text_len, tag, tag_len, work)`. -/
def verifyPre (s : State) : Prop :=
  let ctx : Region := ⟨(VG.X86.arg s 0).setWidth 64, 256⟩
  let st : Region := ⟨(VG.X86.arg s 2).setWidth 64, 80⟩
  let tag : Region := ⟨(VG.X86.arg s 7).setWidth 64, (VG.X86.arg s 8).toNat⟩
  let scr : Region := ⟨(VG.X86.arg s 9).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 40⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 28, 28⟩
  s.rd = [ctx, tag] ∧ s.wr = [st, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ tag.Disjoint st ∧ tag.Disjoint scr ∧
  tag.Disjoint args ∧ st.Disjoint scr ∧ st.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint st ∧ ret.Disjoint tag ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint st ∧ stack.Disjoint tag ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (VG.X86.arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + 80 ≤ 2 ^ 32 ∧ (VG.X86.arg s 7).toNat + (VG.X86.arg s 8).toNat ≤ 2 ^ 32 ∧
  (VG.X86.arg s 9).toNat + 2560 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 44 ≤ 2 ^ 32 ∧ VG.Proof.AesGcm.X86.roundsOk s 1

def streamVerifyX86 : Contract isa where
  pre := VG.Proof.AesGcm.X86.verifyPre
  post s s' :=
    let ciph := ctxCiph s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat
    let h := ctxH s.mem ((VG.X86.arg s 0).setWidth 64)
    ∀ iv a c, StreamRepr s.mem ((VG.X86.arg s 2).setWidth 64) ciph h iv a c →
      VG.X86.arg s 4 ++ VG.X86.arg s 3 = BitVec.ofNat 64 a.length → (VG.X86.arg s 6 ++ VG.X86.arg s 5).toNat = c.length →
      let t := fullTag ciph h iv a c
      if VG.Spec.Gcm.tagLenOk (VG.X86.arg s 8).toNat ∧ t.take (VG.X86.arg s 8).toNat = VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 7).setWidth 64) (VG.X86.arg s 8).toNat then
        (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1
      else (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0
  pub := VG.Proof.AesGcm.X86.pubN 10

/-- `vg_aes_gcm_seal(ctx, rounds, nonce, nonce_len, aad, aad_len, data, len, tag, work)`. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨(VG.X86.arg s 0).setWidth 64, 256⟩
  let nonce : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
  let aad : Region := ⟨(VG.X86.arg s 4).setWidth 64, (VG.X86.arg s 5).toNat⟩
  let data : Region := ⟨(VG.X86.arg s 6).setWidth 64, (VG.X86.arg s 7).toNat⟩
  let tag : Region := ⟨(VG.X86.arg s 8).setWidth 64, 16⟩
  let scr : Region := ⟨(VG.X86.arg s 9).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 40⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 28, 28⟩
  s.rd = [ctx, nonce, aad] ∧ s.wr = [data, tag, scr, args] ∧
  ctx.Disjoint data ∧ ctx.Disjoint tag ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ nonce.Disjoint data ∧
  nonce.Disjoint tag ∧ nonce.Disjoint scr ∧ nonce.Disjoint args ∧ aad.Disjoint data ∧ aad.Disjoint tag ∧
  aad.Disjoint scr ∧ aad.Disjoint args ∧ data.Disjoint tag ∧ data.Disjoint scr ∧ data.Disjoint args ∧
  tag.Disjoint scr ∧ tag.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧ ret.Disjoint tag ∧
  ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint nonce ∧ stack.Disjoint aad ∧ stack.Disjoint data ∧
  stack.Disjoint tag ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (VG.X86.arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧
  (VG.X86.arg s 4).toNat + (VG.X86.arg s 5).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 6).toNat + (VG.X86.arg s 7).toNat ≤ 2 ^ 32 ∧
  (VG.X86.arg s 8).toNat + 16 ≤ 2 ^ 32 ∧ (VG.X86.arg s 9).toNat + 2560 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 44 ≤ 2 ^ 32 ∧ VG.Proof.AesGcm.X86.roundsOk s 1

def sealX86 : Contract isa where
  pre := VG.Proof.AesGcm.X86.sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat) (ctxH s.mem ((VG.X86.arg s 0).setWidth 64)) 16
        (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat) (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat)
        (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 4).setWidth 64) (VG.X86.arg s 5).toNat) =
      (VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat, VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 8).setWidth 64) 16)
  pub := VG.Proof.AesGcm.X86.pubN 10

/-- `vg_aes_gcm_open(ctx, rounds, nonce, nonce_len, aad, aad_len, data, len, tag, tag_len, work)`. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨(VG.X86.arg s 0).setWidth 64, 256⟩
  let nonce : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
  let aad : Region := ⟨(VG.X86.arg s 4).setWidth 64, (VG.X86.arg s 5).toNat⟩
  let data : Region := ⟨(VG.X86.arg s 6).setWidth 64, (VG.X86.arg s 7).toNat⟩
  let tag : Region := ⟨(VG.X86.arg s 8).setWidth 64, (VG.X86.arg s 9).toNat⟩
  let scr : Region := ⟨(VG.X86.arg s 10).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 44⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 28, 28⟩
  s.rd = [ctx, nonce, aad, tag] ∧ s.wr = [data, scr, args] ∧
  ctx.Disjoint data ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ nonce.Disjoint data ∧ nonce.Disjoint scr ∧
  nonce.Disjoint args ∧ aad.Disjoint data ∧ aad.Disjoint scr ∧ aad.Disjoint args ∧ data.Disjoint tag ∧
  data.Disjoint scr ∧ data.Disjoint args ∧ tag.Disjoint scr ∧ tag.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧ ret.Disjoint tag ∧
  ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint nonce ∧ stack.Disjoint aad ∧ stack.Disjoint data ∧
  stack.Disjoint tag ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (VG.X86.arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧
  (VG.X86.arg s 4).toNat + (VG.X86.arg s 5).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 6).toNat + (VG.X86.arg s 7).toNat ≤ 2 ^ 32 ∧
  (VG.X86.arg s 8).toNat + (VG.X86.arg s 9).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 10).toNat + 2560 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 48 ≤ 2 ^ 32 ∧ VG.Proof.AesGcm.X86.roundsOk s 1

/-- What `open` computes. -/
abbrev openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat) (ctxH s.mem ((VG.X86.arg s 0).setWidth 64))
    (VG.X86.arg s 9).toNat (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat)
    (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat) (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 4).setWidth 64) (VG.X86.arg s 5).toNat)
    (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 8).setWidth 64) (VG.X86.arg s 9).toNat)

def openX86 : Contract isa where
  pre := VG.Proof.AesGcm.X86.openPre
  post s s' :=
    match VG.Proof.AesGcm.X86.openRes s with
    | some pt => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧ VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat = pt
    | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧
      VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat = VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat
  pub s₁ s₂ := VG.Proof.AesGcm.X86.pubN 11 s₁ s₂ ∧ (VG.Proof.AesGcm.X86.openRes s₁).isSome = (VG.Proof.AesGcm.X86.openRes s₂).isSome

/-- The `u32` a function returns, from `edx:eax`: `eax`. -/
theorem ret32_eq (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt b.isLt]
  omega

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Top`. -/
section

/-!
# AES-GCM on x86: from the contracts to the pieces

Untrusted: everything here is checked by Lean. What the functions' proofs
share: the public data of a run (`pubOf`: the stack pointer and the stack
arguments), a `Pc` with no state satisfying it (`Pc.vacuous`), and facts
about the regions of the contracts.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

/-- The public data of a run with `n` stack arguments. -/
def pubOf (n : Nat) (s : State) : BitVec 32 × (Nat → BitVec 32) :=
  (s.gpr .esp, fun i => if i < n then arg s i else 0)

theorem pubOf_eq {n : Nat} {s₁ s₂ : State} (h : VG.Proof.AesGcm.X86.pubN n s₁ s₂) : VG.Proof.AesGcm.X86.pubOf n s₁ = VG.Proof.AesGcm.X86.pubOf n s₂ := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [VG.Proof.AesGcm.X86.pubOf, h₁, Prod.mk.injEq, true_and]
  funext i
  split
  · next hi => exact h₂ i hi
  · rfl

theorem pubOf_arg {n : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : VG.Proof.AesGcm.X86.pubOf n s = p) {i : Nat}
    (hi : i < n) : arg s i = p.2 i := by
  rw [← h]; simp only [VG.Proof.AesGcm.X86.pubOf, hi, ↓reduceIte]

theorem pubOf_esp {n : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : VG.Proof.AesGcm.X86.pubOf n s = p) :
    s.gpr .esp = p.1 := by
  rw [← h]; rfl

/-- The public data of a run with `n` stack arguments, with the arguments `i`
and `n - 1` (`W`, the last) exchanged: the pieces of the functions that take
`W` last find it at `i`. -/
def pubSw (n i : Nat) (s : State) : BitVec 32 × (Nat → BitVec 32) :=
  (s.gpr .esp, fun k => if k < n then arg s (if k = i then n - 1 else if k = n - 1 then i else k) else 0)

theorem pubSw_eq {n i : Nat} (hi : i < n) {s₁ s₂ : State} (h : VG.Proof.AesGcm.X86.pubN n s₁ s₂) : VG.Proof.AesGcm.X86.pubSw n i s₁ = VG.Proof.AesGcm.X86.pubSw n i s₂ := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [VG.Proof.AesGcm.X86.pubSw, h₁, Prod.mk.injEq, true_and]
  funext k
  split
  · next hk => exact h₂ _ (by split <;> (try split) <;> omega)
  · rfl

theorem pubSw_arg {n i : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : VG.Proof.AesGcm.X86.pubSw n i s = p) {k : Nat}
    (hk : k < n) (hi : k ≠ i) (hn : k + 1 ≠ n) : arg s k = p.2 k := by
  rw [← h]; simp only [VG.Proof.AesGcm.X86.pubSw, hk, hi, show k ≠ n - 1 by omega, ↓reduceIte]

/-- `W`, at `i`. -/
theorem pubSw_W {n i m : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : VG.Proof.AesGcm.X86.pubSw n i s = p)
    (hi : i < n) (hm : n = m + 1) : arg s m = p.2 i := by
  rw [← h]; simp only [VG.Proof.AesGcm.X86.pubSw, hi, ↓reduceIte, show n - 1 = m by omega]

/-- The argument `i`, at `n - 1`. -/
theorem pubSw_last {n i m : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : VG.Proof.AesGcm.X86.pubSw n i s = p)
    (hi : i < n) (hm : n = m + 1) : arg s i = p.2 m := by
  rw [← h]
  simp only [VG.Proof.AesGcm.X86.pubSw, show m < n by omega, show n - 1 = m by omega, ↓reduceIte]
  by_cases e : m = i
  · subst e; simp
  · simp [e]

theorem pubSw_esp {n i : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : VG.Proof.AesGcm.X86.pubSw n i s = p) :
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
  rw [← VG.Proof.AesGcm.X86.below_eq h]; exact Offset.base_disjoint_below _ (by omega)

/-- The return address stays where it is, outside a frame. -/
theorem ret_kept {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {SP : BitVec 32}
    (hd : ∀ r ∈ rs, (⟨w64 SP, 4⟩ : Region).Disjoint r) : m'.readW (w64 SP) 32 = m.readW (w64 SP) 32 :=
  hf.readW (r := ⟨w64 SP, 4⟩) (Region.contains_self _ _) hd (by decide)

theorem ofNat_lit (n : Nat) : (OfNat.ofNat n : Addr) = BitVec.ofNat 64 n := rfl

theorem ctxH_eq (m : Mem) (p : Addr) : Spec.Gcm.ctxH m p = Spec.Gcm.blockAt m (p + BitVec.ofNat 64 240) := rfl

theorem toNat_mod16_64 (n : Nat) : (BitVec.ofNat 64 n).toNat % 16 = n % 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

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
  rw [Proof.Gcm.streamRepr_iff, VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.ofNat_lit] at hr ⊢
  obtain ⟨hj, ha, hc⟩ := hr
  have e0 := blockAt_frame hf (sub (d := 0) (k := 16) (by decide))
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e0
  refine ⟨by rw [e0, hj], ha.congr (blockAt_frame hf (sub (by decide)))
    (bytesAt_frame hf (sub (d := 32) (k := (Spec.Gcm.ghashInput a c).length % 16) (by omega)) (by omega)),
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Tag`. -/
section

/-!
# AES-GCM on x86: the tag (`tag`)

Untrusted: everything here is checked by Lean. `tag o …` absorbs the
lengths block (`lens 16`), copies the accumulator to `W + o` and encrypts
it there with `vg_aes_ctr32` from the counter block `J₀` (at the state's
first block): `GHASH ⊕ CIPH_K(J₀)` (`tag_pc`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ofBytes toBytes)
open VG.Proof.Gcm (lensBlock)
open VG.Proof.Cmac (le4 store4)

theorem bytesAt_toBytes (m : Mem) (p : Addr) : bytesAt m p 16 = toBytes (blockAt m p) :=
  (Cmac.toBytes_ofBytes (length_bytesAt _ _ _)).symm

theorem bytesAt16 (m : Mem) (p : Addr) : bytesAt m p 16 = bytesAt m p 4 ++ bytesAt m (p + BitVec.ofNat 64 4) 4 ++
    bytesAt m (p + BitVec.ofNat 64 8) 4 ++ bytesAt m (p + BitVec.ofNat 64 12) 4 := by
  rw [show (16 : Nat) = 4 + 12 from rfl, bytesAt_add, show (12 : Nat) = 4 + 8 from rfl, bytesAt_add,
    show (8 : Nat) = 4 + 4 from rfl, bytesAt_add, add_ofNat_assoc, add_ofNat_assoc, List.append_assoc,
    List.append_assoc]

/-- The regions `tag o` writes. -/
abbrev tagFrame (St W SP : BitVec 32) (o : Nat) : List Region :=
  [⟨w64 St, 32⟩, ⟨w64 W + BitVec.ofNat 64 96, 16⟩, ⟨w64 W + BitVec.ofNat 64 o, 16⟩, wsR W, below SP 28]

/-- Before `tag o al ah tl th`. -/
structure TagIn (Ctx St W SP : BitVec 32) (R : Nat) (al ah tl th : Nat) (alo ahi tlo thi : BitVec 32) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  sl : LensSlots W al ah tl th alo ahi tlo thi s.mem
  rounds : RoundsAt s.mem W R

/-- After: the tag at `W + o`, from `m₀`. -/
structure TagOut (Ctx St W SP : BitVec 32) (R o aN tN : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  rounds : RoundsAt s.mem W R
  out : bytesAt s.mem (w64 W + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom (Hk m₀ Ctx) (blockAt m₀ (w64 St + BitVec.ofNat 64 16)) [ofBytes (lensBlock aN tN)] ^^^
      ciphOf m₀ Ctx R (blockAt m₀ (w64 St)))
  frame : Frame (VG.Proof.AesGcm.X86.tagFrame St W SP o) m₀ s.mem

/-- After the lengths block and the copy, from `m₀`. -/
structure TagMid (Ctx St W SP : BitVec 32) (R o aN tN : Nat) (m₀ : Mem) (s : State) : Prop where
  ready : CtrReady Ctx St W SP R St (W + BitVec.ofNat 32 o) 1 s
  acc : blockAt s.mem (w64 W + BitVec.ofNat 64 o) =
    ghashFrom (Hk m₀ Ctx) (blockAt m₀ (w64 St + BitVec.ofNat 64 16)) [ofBytes (lensBlock aN tN)]
  j : blockAt s.mem (w64 St) = blockAt m₀ (w64 St)
  ciph : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R
  frame : Frame (VG.Proof.AesGcm.X86.tagFrame St W SP o) m₀ s.mem

section
variable {Ctx St W SP : BitVec 32} (L : Lay Ctx St W SP 28)
include L

omit L in
theorem t_tagFrame {o : Nat} {m m' : Mem} (h : Frame (tFrame St W SP 28 16) m m') :
    Frame (VG.Proof.AesGcm.X86.tagFrame St W SP o) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base (w64 St) (show 16 + 16 ≤ 32 by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨wsR W, by simp, fun _ h => h⟩
    · exact ⟨below SP 28, by simp, fun _ h => h⟩

/-- The copy of the accumulator to `W + o`, and the arguments of `vg_aes_ctr32`. -/
theorem tagCopy_ok {R o aN tN : Nat} (ho : o = 0 ∨ o = 112) {m₀ : Mem} {s : State}
    (he : Env Ctx St W SP s) (hR : RoundsAt s.mem W R)
    (hacc : blockAt s.mem (w64 St + BitVec.ofNat 64 16) =
      ghashFrom (Hk m₀ Ctx) (blockAt m₀ (w64 St + BitVec.ofNat 64 16)) [ofBytes (lensBlock aN tN)])
    (hj : blockAt s.mem (w64 St) = blockAt m₀ (w64 St)) (hc : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R)
    (hf : Frame (VG.Proof.AesGcm.X86.tagFrame St W SP o) m₀ s.mem) :
    WP isa (.block [.mov .eax (.mem (at_ .esi 16)), .mov .ecx (.mem (at_ .esi 20)), .mov .edx (.mem (at_ .esi 24)),
      .mov .ebx (.mem (at_ .esi 28)), .store (at_ .ebp o) .eax, .store (at_ .ebp (o + 4)) .ecx,
      .store (at_ .ebp (o + 8)) .edx, .store (at_ .ebp (o + 12)) .ebx, .mov .ebx (.reg .ebp),
      .alu .add .ebx (imm o), .mov .edi (imm 1), .mov .eax (slot ctxO), .mov .ecx (slot roundsO),
      .mov .edx (.reg .esi), .alu .add .ebp (imm scrO)]) s (VG.Proof.AesGcm.X86.TagMid Ctx St W SP R o aN tN m₀) := by
  have r₁ := hR.1
  rw [slotv_eq] at r₁
  have ho' : o + 16 ≤ 128 := by omega
  generalize hw0 : s.mem.readW (w64 St + BitVec.ofNat 64 16) 32 = w0
  generalize hw1 : s.mem.readW (w64 St + BitVec.ofNat 64 20) 32 = w1
  generalize hw2 : s.mem.readW (w64 St + BitVec.ofNat 64 24) 32 = w2
  generalize hw3 : s.mem.readW (w64 St + BitVec.ofNat 64 28) 32 = w3
  have hctx := he.ctx
  have hm4 : ∀ v : BitVec 32, store4 s.mem (w64 W + BitVec.ofNat 64 o) w0 w1 w2 v =
      (((s.mem.writeW (w64 W + BitVec.ofNat 64 o) w0).writeW (w64 W + BitVec.ofNat 64 (o + 4)) w1).writeW
        (w64 W + BitVec.ofNat 64 (o + 8)) w2).writeW (w64 W + BitVec.ofNat 64 (o + 12)) v := fun v => by
    simp only [store4, add_ofNat_assoc]
  refine WP.of_runBlock ⟨_, by xrun [he.esi, he.ebp, L.aS, L.aW, he.stIn', he.wIn, he.wIn', readW_writeW_off,
    hctx, r₁, hw0, hw1, hw2, hw3, ← hm4], ?_⟩
  generalize hM : store4 s.mem (w64 W + BitVec.ofNat 64 o) w0 w1 w2 w3 = M
  have f₄ : Frame [⟨w64 W + BitVec.ofNat 64 o, 16⟩] s.mem M := by rw [← hM]; exact Cmac.frame_store4 _ _ _ _ _
  have sK : ∀ {q}, 128 ≤ q → q + 4 ≤ 2560 → slotv M W q = slotv s.mem W q := fun h₁ h₂ =>
    slot_frame f₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by omega)
  have dS : ∀ {a k : Nat}, a + k ≤ 80 → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 o, 16⟩ : Region)],
      (⟨w64 St + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r := fun hak r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rcases ho with rfl | rfl
    · exact L.st_w hak (.inl (by decide))
    · exact L.st_w hak (.inr ⟨by decide, by decide⟩)
  have hR' : RoundsAt M W R := ⟨by rw [sK (by decide) (by decide)]; exact hR.1, hR.2⟩
  have eW := L.aW (o := o) (by omega)
  have eS : w64 (St + BitVec.ofNat 32 0) = w64 St := by rw [L.aS (by decide)]; exact BitVec.add_zero _
  refine ⟨⟨by regs []; exact (sK (q := 144) (by decide) (by decide)).trans hctx,
    by regs []; exact (sK (q := 148) (by decide) (by decide)).trans hR.1, by regs [he.esi], by regs [he.ebp], by regs [], by regs [he.ebp],
    by regs [he.esi], by regs [he.esp], he.ctxR, he.stW, he.wW, by simp only [mem_setReg, mem_arithFlags, mem_setMem]; exact (sK (q := 144) (by decide) (by decide)).trans hctx,
    by simp only [mem_setReg, mem_arithFlags, mem_setMem]; exact hR', by have := L.fs; omega, by rw [L.nW (by omega)]; have := L.fw; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (by simpa using he.stC (d := 0) (n := 16) (by decide) : Covers [⟨w64 St, 16⟩] s.wr)
  · rw [eW]; exact (he.wC (d := o) (n := 16 * 1) (by omega) : Covers _ s.wr)
  · rw [eW]; have := dS (a := 0) (k := 16) (by decide) _ (List.mem_singleton_self _); simpa using this
  · exact L.cs.sub_right (Region.sub_prefix (by decide))
  · rw [eW]; exact L.ctx_w (a := 0) (n := 256) (d := o) (k := 16 * 1) (by decide) (by omega) |> fun h => by simpa using h
  · simpa using L.st_w (a := 0) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)
  · rw [eW]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · simpa using L.stk_st (a := 0) (n := 16) (by decide)
  · rw [eW]; exact L.stk_w (by omega)
  · simpa using (L.st_w (a := 0) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · rw [eW]; exact Lay.w_w (.inr (by omega)) (by decide) (by omega)
  · simp only [mem_setReg, mem_arithFlags, mem_setMem]
    rw [← hM, blockAt, Cmac.bytesAt_store4, ← hw0, ← hw1, ← hw2, ← hw3, Cmac.le4_readW, Cmac.le4_readW,
      Cmac.le4_readW, Cmac.le4_readW, ← hacc, blockAt]
    congr 1
    rw [VG.Proof.AesGcm.X86.bytesAt16, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]
  · simp only [mem_setReg, mem_arithFlags, mem_setMem]
    have := blockAt_frame f₄ (dS (a := 0) (k := 16) (by decide))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this, hj]
  · simp only [mem_setReg, mem_arithFlags, mem_setMem]
    rw [ciph_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.ctx_w (a := 0) (n := 256) (d := o) (k := 16) (by decide) (by omega) |> fun h => by simpa using h)
      hR.2, hc]
  · simp only [mem_setReg, mem_arithFlags, mem_setMem]
    exact hf.trans (f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩)

theorem kept_tFrame : ∀ r ∈ tFrame St W SP 28 16, (keptR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem ctx_tFrame' : ∀ r ∈ tFrame St W SP 28 16, (⟨w64 Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw.sub_right (Lay.wSub (by decide))
  · exact L.cw.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

theorem tag_pc {R o al ah tl th : Nat} (ho : o = 0 ∨ o = 112) (hc : LensAt 16 al ah tl th)
    {alo ahi tlo thi : BitVec 32} :
    Pc (fun (m₀ : Mem) s => VG.Proof.AesGcm.X86.TagIn Ctx St W SP R al ah tl th alo ahi tlo thi s ∧ s.mem = m₀) (tag vg.callees o al ah tl th)
      (VG.Proof.AesGcm.X86.TagOut Ctx St W SP R o (val64 alo ahi) (val64 tlo thi) ·) := by
  refine Pc.seq (Pc.lift (lens_pc L hc) (fun m₀ _ => m₀) fun m₀ s ⟨h, hm⟩ => ⟨⟨h.env, h.sl⟩, hm⟩) ?_
  have hw : ∀ (m₀ : Mem) s', (∃ s, (VG.Proof.AesGcm.X86.TagIn Ctx St W SP R al ah tl th alo ahi tlo thi s ∧ s.mem = m₀) ∧
      LensOut Ctx St W SP 28 16 (val64 alo ahi) (val64 tlo thi) m₀ s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr) →
      WP isa (.block [.mov .eax (.mem (at_ .esi 16)), .mov .ecx (.mem (at_ .esi 20)), .mov .edx (.mem (at_ .esi 24)),
        .mov .ebx (.mem (at_ .esi 28)), .store (at_ .ebp o) .eax, .store (at_ .ebp (o + 4)) .ecx,
        .store (at_ .ebp (o + 8)) .edx, .store (at_ .ebp (o + 12)) .ebx, .mov .ebx (.reg .ebp),
        .alu .add .ebx (imm o), .mov .edi (imm 1), .mov .eax (slot ctxO), .mov .ecx (slot roundsO),
        .mov .edx (.reg .esi), .alu .add .ebp (imm scrO)]) s' (VG.Proof.AesGcm.X86.TagMid Ctx St W SP R o (val64 alo ahi) (val64 tlo thi) m₀) :=
    fun m₀ s' ⟨s, ⟨h, hm⟩, lo, _, _⟩ => by
      subst hm
      have hj : blockAt s'.mem (w64 St) = blockAt s.mem (w64 St) := by
        have := blockAt_frame lo.frame (p := w64 St + BitVec.ofNat 64 0) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
          · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
          · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
          · exact (L.stk_st (by decide)).symm
        simpa using this
      exact VG.Proof.AesGcm.X86.tagCopy_ok L ho lo.env (rounds_frame lo.frame (VG.Proof.AesGcm.X86.kept_tFrame L) h.rounds) lo.out hj
        (ciph_frame lo.frame (VG.Proof.AesGcm.X86.ctx_tFrame' L) h.rounds.2) (VG.Proof.AesGcm.X86.t_tagFrame lo.frame)
  have hr : ∀ (m₀ m₁ : Mem) s₁ s₂, (∃ s, (VG.Proof.AesGcm.X86.TagIn Ctx St W SP R al ah tl th alo ahi tlo thi s ∧ s.mem = m₀) ∧
      LensOut Ctx St W SP 28 16 (val64 alo ahi) (val64 tlo thi) m₀ s₁ ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr) →
      (∃ s, (VG.Proof.AesGcm.X86.TagIn Ctx St W SP R al ah tl th alo ahi tlo thi s ∧ s.mem = m₁) ∧
      LensOut Ctx St W SP 28 16 (val64 alo ahi) (val64 tlo thi) m₁ s₂ ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr) →
      ∀ r ∈ [Reg.esi, .ebp], s₁.gpr r = s₂.gpr r := fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.env.esi, h₂.env.esi]
    · rw [h₁.env.ebp, h₂.env.ebp]
  refine Pc.seq (Q := VG.Proof.AesGcm.X86.TagMid Ctx St W SP R o (val64 alo ahi) (val64 tlo thi)) ?_ ?_
  · rcases ho with rfl | rfl
    · exact Pc.taint [.esi, .ebp] hw hr (by taint_decide)
    · exact Pc.taint [.esi, .ebp] hw hr (by taint_decide)
  refine Pc.mono (Pc.of (I := CtrReady Ctx St W SP R St (W + BitVec.ofNat 32 o) 1) (fun _ h => ctrW_ok L rfl h)
    (ctrW_ct L rfl) _ fun _ _ h => h.ready) (fun _ _ h => h) fun m₀ s' ⟨s, h, g⟩ => ?_
  have eW := L.aW (o := o) (by omega)
  have eS : w64 St = w64 St := rfl
  have go := g.out
  rw [eW, blocksAt_one, blocksAt_one, h.ciph] at go
  have hb := congrArg (fun l => List.getD l 0 0) go
  simp only [List.getD_cons_zero] at hb
  rw [Proof.Gcm.ctr32_getD _ _ _ (by simp)] at hb
  simp only [List.getD_cons_zero, Nat.repeat] at hb
  have gf := g.frame
  rw [eW] at gf
  refine ⟨g.env, g.rounds, by rw [VG.Proof.AesGcm.X86.bytesAt_toBytes, hb, h.acc, h.j], h.frame.trans (gf.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨below SP 28, by simp, fun _ h => h⟩

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Cmp`. -/
section

/-!
# AES-GCM on x86: checking a tag

Untrusted: everything here is checked by Lean. `tagLenOk` decides the tag
length (`tagLenOk_pc`), `recv` copies the received tag, padded with zeros
(`recv_ok`), `cmp o` the computed one and compares them without a branch
(`cmp_ok`), and `tagOut o` copies a computed tag to the caller's buffer
(`tagOut_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)

theorem or_eq_zero32' (a b : BitVec 32) : (a ||| b = 0) ↔ (a = 0 ∧ b = 0) := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_or] at this
    have := Nat.or_eq_zero_iff.mp this
    exact ⟨BitVec.eq_of_toNat_eq (by simpa using this.1), BitVec.eq_of_toNat_eq (by simpa using this.2)⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- What `tagLenOk` keeps of the state it starts from. -/
structure TlPost (t : Nat) (s₀ s : State) (c : Bool) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  other : ∀ r, r ≠ .ebx → r ≠ .ecx → s.gpr r = s₀.gpr r
  ebx : s.gpr .ebx = BitVec.ofNat 32 t
  ecx : s.gpr .ecx = BitVec.ofNat 32 (if c then 1 else 0)

theorem tagLenOk_pc {W : BitVec 32} {t : Nat} (ht : t < 2 ^ 32) :
    Pc (fun (s₀ : State) s => s = s₀ ∧ s.gpr .ebp = W ∧
        w64 (W + BitVec.ofNat 32 tglO) = w64 W + BitVec.ofNat 64 tglO ∧
        InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 tglO) 4 ∧ slotv s.mem W tglO = BitVec.ofNat 32 t)
      tagLenOk (fun s₀ s => VG.Proof.AesGcm.X86.TlPost t s₀ s (Spec.Gcm.tagLenOk t) ∧ s.zf = some (!Spec.Gcm.tagLenOk t)) := by
  -- The first comparison.
  refine Pc.seq (Q := fun s₀ s => VG.Proof.AesGcm.X86.TlPost t s₀ s false ∧ s.zf = some (decide (t = 4)))
    (Pc.taint [.ebp] (fun s₀ s ⟨hs, hb, ha, hin, hv⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide)) ?_
  · subst hs
    rw [slotv_eq] at hv
    simp only [tglO] at hin hv ha
    refine WP.of_runBlock ⟨_, by xrun [hb, ha, hin, hv], ⟨by mems [], by mems [], by mems [], fun r h₁ h₂ => ?_, by regs [],
      by regs []; rfl⟩, ?_⟩
    · simp only [gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂, gpr_arithFlags]
    · mems []; rw [sub_beq32 ht (by decide)]
  -- `ecx := 1` if `t = 4`.
  refine Pc.seq (Q := fun s₀ s => VG.Proof.AesGcm.X86.TlPost t s₀ s (decide (t = 4))) ?_ ?_
  · refine Pc.ite (decide (t = 4)) (fun _ _ h => h.2) (fun h4 => ?_) (fun h4 => ?_)
    · exact Pc.taint [] (fun s₀ s ⟨h, _⟩ => WP.of_runBlock ⟨_, by xrun [], ⟨by mems [h.mem], by mems [h.rd],
        by mems [h.wr], fun r h₁ h₂ => by simp only [gpr_setReg_of_ne _ _ h₂]; exact h.other r h₁ h₂, by regs [h.ebx],
        by regs [h4]; rfl⟩⟩)
        (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    · exact Pc.mono Pc.nil (fun _ _ h => h) fun _ _ ⟨h, _⟩ => by rw [h4]; exact h
  -- The second.
  refine Pc.seq (Q := fun s₀ s => VG.Proof.AesGcm.X86.TlPost t s₀ s (decide (t = 4)) ∧ s.zf = some (decide (t = 8)))
    (Pc.taint [] (fun s₀ s h => WP.of_runBlock ⟨_, by xrun [h.ebx], ⟨by mems [h.mem], by mems [h.rd], by mems [h.wr],
      fun r h₁ h₂ => by regs [h.other r h₁ h₂], by regs [h.ebx], by regs [h.ecx]⟩, by
        mems []; rw [sub_beq32 ht (by decide)]⟩) (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)) ?_
  refine Pc.seq (Q := fun s₀ s => VG.Proof.AesGcm.X86.TlPost t s₀ s (decide (t = 4) || decide (t = 8))) ?_ ?_
  · refine Pc.ite (decide (t = 8)) (fun _ _ h => h.2) (fun h8 => ?_) (fun h8 => ?_)
    · exact Pc.taint [] (fun s₀ s ⟨h, _⟩ => WP.of_runBlock ⟨_, by xrun [], ⟨by mems [h.mem], by mems [h.rd],
        by mems [h.wr], fun r h₁ h₂ => by simp only [gpr_setReg_of_ne _ _ h₂]; exact h.other r h₁ h₂, by regs [h.ebx],
        by regs [h8]; simp⟩⟩)
        (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    · exact Pc.mono Pc.nil (fun _ _ h => h) fun _ _ ⟨h, _⟩ => by rw [h8, Bool.or_false]; exact h
  -- `12 ≤ t ≤ 16`.
  refine Pc.seq (Q := fun s₀ s => VG.Proof.AesGcm.X86.TlPost t s₀ s (decide (t = 4) || decide (t = 8)) ∧ s.cf = some (decide (t < 12)))
    (Pc.taint [] (fun s₀ s h => WP.of_runBlock ⟨_, by xrun [h.ebx], ⟨by mems [h.mem], by mems [h.rd], by mems [h.wr],
      fun r h₁ h₂ => by regs [h.other r h₁ h₂], by regs [h.ebx], by regs [h.ecx]⟩, by
        mems []; simp [toNat_ofNat32 ht]⟩) (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)) ?_
  refine Pc.seq (Q := fun s₀ s => VG.Proof.AesGcm.X86.TlPost t s₀ s (Spec.Gcm.tagLenOk t)) ?_ ?_
  · refine Pc.ite (decide (t < 12)) (fun _ _ h => h.2) (fun hl => ?_) (fun hl => ?_)
    · refine Pc.mono Pc.nil (fun _ _ h => h) fun _ _ ⟨h, _⟩ => ?_
      have hl' : t < 12 := by simpa using hl
      have : Spec.Gcm.tagLenOk t = (decide (t = 4) || decide (t = 8)) := by
        rw [Bool.eq_iff_iff]; simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
          decide_eq_true_eq]; constructor <;> intro h <;> omega
      rw [this]; exact h
    refine Pc.seq (Q := fun s₀ s => VG.Proof.AesGcm.X86.TlPost t s₀ s (decide (t = 4) || decide (t = 8)) ∧
        s.cf = some (decide (t < 17)))
      (Pc.taint [] (fun s₀ s ⟨h, _⟩ => WP.of_runBlock ⟨_, by xrun [h.ebx], ⟨by mems [h.mem], by mems [h.rd],
        by mems [h.wr], fun r h₁ h₂ => by regs [h.other r h₁ h₂], by regs [h.ebx], by regs [h.ecx]⟩, by
          mems []; simp [toNat_ofNat32 ht]⟩) (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)) ?_
    refine Pc.ite (decide (t < 17)) (fun _ _ h => h.2) (fun hu => ?_) (fun hu => ?_)
    · have hl' : ¬ t < 12 := by simpa using hl
      have hu' : t < 17 := by simpa using hu
      have : Spec.Gcm.tagLenOk t = true := by
        simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]; omega
      rw [this]
      exact Pc.taint [] (fun s₀ s ⟨h, _⟩ => WP.of_runBlock ⟨_, by xrun [], ⟨by mems [h.mem], by mems [h.rd],
        by mems [h.wr], fun r h₁ h₂ => by simp only [gpr_setReg_of_ne _ _ h₂]; exact h.other r h₁ h₂, by regs [h.ebx],
        by regs []; rfl⟩⟩)
        (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    · refine Pc.mono Pc.nil (fun _ _ h => h) fun _ _ ⟨h, _⟩ => ?_
      have hl' : ¬ t < 12 := by simpa using hl
      have hu' : ¬ t < 17 := by simpa using hu
      have : Spec.Gcm.tagLenOk t = (decide (t = 4) || decide (t = 8)) := by
        rw [Bool.eq_iff_iff]; simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
          decide_eq_true_eq]; constructor <;> intro h <;> omega
      rw [this]; exact h
  -- `ZF`.
  refine Pc.taint [] (fun s₀ s h => WP.of_runBlock ⟨_, by xrun [h.ecx], ⟨by mems [h.mem], by mems [h.rd],
    by mems [h.wr], fun r h₁ h₂ => by regs [h.other r h₁ h₂], by regs [h.ebx], by regs [h.ecx]⟩, ?_⟩)
    (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
  mems []
  cases Spec.Gcm.tagLenOk t <;> rfl

/-- `W` and where the tags are compared, for a run with `ebp = W`. -/
structure WEnv (W : BitVec 32) (s : State) : Prop where
  ebp : s.gpr .ebp = W
  wW : Covers [⟨w64 W, 2560⟩] s.wr
  fw : W.toNat + 2560 ≤ 2 ^ 32

theorem WEnv.keep {W : BitVec 32} {s s' : State} (h : VG.Proof.AesGcm.X86.WEnv W s) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86.WEnv W s' := ⟨by rw [hbp, h.ebp], by rw [hwr]; exact h.wW, h.fw⟩

theorem WEnv.aW {W : BitVec 32} {s : State} (h : VG.Proof.AesGcm.X86.WEnv W s) {o : Nat} (ho : o < 2560) :
    w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := w64_add (by have := h.fw; omega)

theorem WEnv.wIn {W : BitVec 32} {s : State} (h : VG.Proof.AesGcm.X86.WEnv W s) {o n : Nat} (ho : o + n ≤ 2560) :
    InRegions s.wr (w64 W + BitVec.ofNat 64 o) n := in_off h.wW ho (by decide)

theorem WEnv.wIn' {W : BitVec 32} {s : State} (h : VG.Proof.AesGcm.X86.WEnv W s) {o n : Nat} (ho : o + n ≤ 2560) :
    InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) n := in_left (h.wIn ho)

/-- The bytes at `p` after `zero4` there, then `xs` (at most 16) copied there. -/
theorem bytesAt_pad (m : Mem) (p : Addr) (xs : List Byte) (hx : xs.length ≤ 16) :
    bytesAt (writeBytes (Cmac.zero4 m p) p xs) p 16 = xs ++ zeros (16 - xs.length) := by
  rw [bytesAt_writeBytes_prefix _ _ _ hx (by decide)]
  congr 1
  have z := zero4_bytes' m p
  rw [show (16 : Nat) = xs.length + (16 - xs.length) by omega, bytesAt_add] at z
  have := congrArg (List.drop xs.length) z
  rwa [List.drop_left' (length_bytesAt _ _ _), show xs.length + (16 - xs.length) = 16 by omega, zeros,
    List.drop_replicate] at this

/-- The copy of the `t` bytes at `S` to `W + d`, zeroed first. -/
theorem padLoop_ok {W S : BitVec 32} {d t : Nat} {m : Mem} {s : State} (he : VG.Proof.AesGcm.X86.WEnv W s)
    (hm : s.mem = Cmac.zero4 m (w64 W + BitVec.ofNat 64 d)) (hdi : s.gpr .edi = S)
    (hdx : s.gpr .edx = W + BitVec.ofNat 32 d) (hcx : s.gpr .ecx = BitVec.ofNat 32 t) (ht1 : 1 ≤ t)
    (ht : t ≤ 16) (sR : Covers [⟨w64 S, t⟩] (s.rd ++ s.wr)) (fS : S.toNat + t ≤ 2 ^ 32)
    (sd : (⟨w64 S, t⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, 16⟩) (hd : d + 16 ≤ 2560) :
    WP isa copyLoop s fun s' => bytesAt s'.mem (w64 W + BitVec.ofNat 64 d) 16 =
        bytesAt m (w64 S) t ++ zeros (16 - t) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 d, 16⟩] m s'.mem ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ed := he.aW (o := d) (by omega)
  have hfw := he.fw
  have c₂ : Covers [⟨w64 W + BitVec.ofNat 64 d, t⟩] s.wr := covers_off he.wW (by omega) (by decide)
  have sd' : (⟨w64 S, t⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, t⟩ :=
    sd.sub_right (Region.sub_prefix (by omega))
  have lp : LoopPre s S (W + BitVec.ofNat 32 d) t := by
    refine ⟨hdi, hdx, hcx, ht1, by omega, fS, by rw [toNat_add32 (by omega)]; omega, sR, by rw [ed]; exact c₂, ?_⟩
    rw [ed]; exact sd'
  refine WP.mono (copyLoop_ok s lp) fun s' c => ?_
  have cm := c.mem
  rw [ed, hm] at cm
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 d, 16⟩] m (Cmac.zero4 m (w64 W + BitVec.ofNat 64 d)) :=
    Cmac.frame_store4 _ _ _ _ _
  have hS : bytesAt (Cmac.zero4 m (w64 W + BitVec.ofNat 64 d)) (w64 S) t = bytesAt m (w64 S) t :=
    bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sd) (by omega)
  have hlen := length_bytesAt (Cmac.zero4 m (w64 W + BitVec.ofNat 64 d)) (w64 S) t
  refine ⟨?_, ?_, c.other, c.rd, c.wr⟩
  · rw [cm, VG.Proof.AesGcm.X86.bytesAt_pad _ _ _ (by rw [hlen]; exact ht), hS, length_bytesAt]
  · rw [cm]
    exact fz.trans (writeBytes_frame _ _ _ (by
      rw [hlen]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega))

theorem le4_inj {a b : BitVec 32} (h : Cmac.le4 a = Cmac.le4 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hk : i / 8 < 4 := by omega
  have e := congrArg (fun l => l.getD (i / 8) 0) h
  simp only [Cmac.getD_le4 _ hk] at e
  have := congrArg (fun x => x.getLsbD (i % 8)) e
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true, Bool.true_and] at this
  rwa [show 8 * (i / 8) + i % 8 = i by omega] at this

theorem xor_eq_zero32 (a b : BitVec 32) : (a ^^^ b = 0) ↔ a = b := by
  constructor
  · intro h
    have := congrArg (· ^^^ b) h
    simpa [BitVec.xor_assoc] using this
  · intro h; subst h; simp

/-- Four words equal, if and only if their XORs `or`ed are zero. -/
theorem xor4_eq_zero (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 32) :
    ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃) = 0) ↔ (a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃) := by
  simp only [VG.Proof.AesGcm.X86.or_eq_zero32', VG.Proof.AesGcm.X86.xor_eq_zero32, and_assoc]

/-- Sixteen bytes equal, if and only if their four words are. -/
theorem bytes16_eq (m : Mem) (p q : Addr) :
    bytesAt m p 16 = bytesAt m q 16 ↔ (m.readW p 32 = m.readW q 32 ∧
      m.readW (p + BitVec.ofNat 64 4) 32 = m.readW (q + BitVec.ofNat 64 4) 32 ∧
      m.readW (p + BitVec.ofNat 64 8) 32 = m.readW (q + BitVec.ofNat 64 8) 32 ∧
      m.readW (p + BitVec.ofNat 64 12) 32 = m.readW (q + BitVec.ofNat 64 12) 32) := by
  rw [VG.Proof.AesGcm.X86.bytesAt16, VG.Proof.AesGcm.X86.bytesAt16, ← Cmac.le4_readW, ← Cmac.le4_readW, ← Cmac.le4_readW, ← Cmac.le4_readW,
    ← Cmac.le4_readW, ← Cmac.le4_readW, ← Cmac.le4_readW, ← Cmac.le4_readW]
  constructor
  · intro h
    simp only [List.append_assoc] at h
    obtain ⟨h₀, h⟩ := List.append_inj h (by simp [Cmac.length_le4])
    obtain ⟨h₁, h⟩ := List.append_inj h (by simp [Cmac.length_le4])
    obtain ⟨h₂, h₃⟩ := List.append_inj h (by simp [Cmac.length_le4])
    exact ⟨VG.Proof.AesGcm.X86.le4_inj h₀, VG.Proof.AesGcm.X86.le4_inj h₁, VG.Proof.AesGcm.X86.le4_inj h₂, VG.Proof.AesGcm.X86.le4_inj h₃⟩
  · rintro ⟨h₀, h₁, h₂, h₃⟩; rw [h₀, h₁, h₂, h₃]

theorem cmpTail_ok {W : BitVec 32} {s : State} (he : VG.Proof.AesGcm.X86.WEnv W s) :
    WP isa (.block cmpTail) s fun s' => s'.gpr .eax = BitVec.ofNat 32
        (if bytesAt s.mem (w64 W + BitVec.ofNat 64 vO) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 rO) 16
          then 1 else 0) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) := by
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => he.aW ho
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn' ho
  refine WP.of_runBlock ⟨_, by xrun [cmpTail, he.ebp, aW, rIn], ?_, ?_, ?_, ?_, ?_⟩
  · regs []
    simp only [VG.Proof.AesGcm.X86.bytes16_eq, add_ofNat_assoc, Nat.reduceAdd]
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 240) 32 = a₀
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 244) 32 = a₁
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 248) 32 = a₂
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 252) 32 = a₃
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 196) 32 = b₀
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 200) 32 = b₁
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 204) 32 = b₂
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 208) 32 = b₃
    have e := VG.Proof.AesGcm.X86.xor4_eq_zero a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
    by_cases h : a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simp only [and_self, ↓reduceIte, BitVec.xor_self, BitVec.or_self]
      decide
    · have h0 : (a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃) ≠ 0 := fun h' => h (e.mp h')
      have hne : ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat ≠ 0 := fun h' =>
        h0 (BitVec.eq_of_toNat_eq (by simpa using h'))
      have hlt : ¬ ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat < (BitVec.ofNat 32 1).toNat := by
        rw [BitVec.toNat_ofNat]; omega
      simp only [h, ↓reduceIte, decide_eq_false hlt]
      rfl
  · mems []
  · mems []
  · mems []
  · intro r h₁ h₂
    simp only [gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂, gpr_arithFlags, gpr_setFlags]

/-- `zero4 d` folded. -/
theorem zero4_fold (m : Mem) (W : BitVec 32) (d : Nat) :
    (((m.writeW (w64 W + BitVec.ofNat 64 d) (BitVec.ofNat 32 0)).writeW (w64 W + BitVec.ofNat 64 (d + 4))
      (BitVec.ofNat 32 0)).writeW (w64 W + BitVec.ofNat 64 (d + 8)) (BitVec.ofNat 32 0)).writeW
      (w64 W + BitVec.ofNat 64 (d + 12)) (BitVec.ofNat 32 0) = Cmac.zero4 m (w64 W + BitVec.ofNat 64 d) := by
  simp only [Cmac.zero4, Cmac.store4, add_ofNat_assoc]; rfl

/-- `recv`: the `t` bytes at `T` (kept at `W + tpO`), padded, at `W + rO`. -/
theorem recv_ok {W T : BitVec 32} {t : Nat} {s : State} (he : VG.Proof.AesGcm.X86.WEnv W s) (hv : slotv s.mem W tglO = BitVec.ofNat 32 t)
    (hT : slotv s.mem W tpO = T) (tR : Covers [⟨w64 T, t⟩] (s.rd ++ s.wr)) (fT : T.toNat + t ≤ 2 ^ 32)
    (tw : (⟨w64 T, t⟩ : Region).Disjoint ⟨w64 W, 2560⟩) (ht1 : 1 ≤ t) (ht : t ≤ 16) :
    WP isa recv s fun s' => bytesAt s'.mem (w64 W + BitVec.ofNat 64 rO) 16 = bytesAt s.mem (w64 T) t ++ zeros (16 - t) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 rO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => he.aW ho
  have wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn ho
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn' ho
  rw [slotv_eq] at hv hT
  simp only [tglO, tpO] at hv hT
  have hz := VG.Proof.AesGcm.X86.zero4_fold s.mem W 196
  simp only [Nat.reduceAdd] at hz
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 196, 16⟩] s.mem (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 196)) :=
    Cmac.frame_store4 _ _ _ _ _
  have hv' : (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 196)).readW (w64 W + BitVec.ofNat 64 180) 32 =
      BitVec.ofNat 32 t := by
    rw [slot_frame (W := W) (o := 180) fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (W := W) (a := 180) (n := 4) (d := 196) (k := 16) (by decide) (by decide) (by decide))]
    exact hv
  have hT' : (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 196)).readW (w64 W + BitVec.ofNat 64 212) 32 = T := by
    rw [slot_frame (W := W) (o := 212) fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (W := W) (a := 212) (n := 4) (d := 196) (k := 16) (by decide) (by decide) (by decide))]
    exact hT
  refine WP.seq (WP.of_runBlock ⟨_, by xrun [recv, zero4, he.ebp, aW, wIn, rIn, readW_writeW_off, hv, hz, hv', hT'], ?_⟩)
  refine WP.mono (VG.Proof.AesGcm.X86.padLoop_ok (S := T) (d := 196) (t := t) (m := s.mem) (he.keep (by regs []) (by mems []))
    (by mems []) (by regs []) (by regs [he.ebp]) (by regs []) ht1 ht (by mems []; exact tR) fT
    (tw.sub_right (Lay.wSub (by decide))) (by decide)) fun s' ⟨b, f, g, rd, wr⟩ => ⟨?_, f, ?_, ?_, ?_, ?_, ?_⟩
  · exact b
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; regs []
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; regs []
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; regs []
  · rw [rd]; mems []
  · rw [wr]; mems []

theorem recv_ct {I : State → Prop} {W T : BitVec 32} {t : Nat}
    (h : ∀ s, I s → VG.Proof.AesGcm.X86.WEnv W s ∧ slotv s.mem W tglO = BitVec.ofNat 32 t ∧ slotv s.mem W tpO = T) : CT I recv := by
  refine CT.seq (J := fun s => s.gpr .edi = T ∧ s.gpr .edx = W + BitVec.ofNat 32 rO ∧ s.gpr .ecx = BitVec.ofNat 32 t)
    (CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h _ h₁).1.ebp, (h _ h₂).1.ebp]) (by taint_decide))
    (fun s hs => ?_) (copyLoop_ct fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2])
  obtain ⟨he, hv, hT⟩ := h s hs
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => he.aW ho
  have wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn ho
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn' ho
  rw [slotv_eq] at hv hT
  simp only [tglO, tpO] at hv hT
  exact WP.of_runBlock ⟨_, by xrun [zero4, he.ebp, aW, wIn, rIn, readW_writeW_off, hv, hT], by regs [],
    by regs [he.ebp], by regs []⟩

/-- `cmp o`: the first `t` bytes at `W + o`, padded, compared with the 16 at `W + rO`. -/
theorem cmp_ok {W : BitVec 32} {t o : Nat} {s : State} (he : VG.Proof.AesGcm.X86.WEnv W s) (hv : slotv s.mem W tglO = BitVec.ofNat 32 t)
    (ht1 : 1 ≤ t) (ht : t ≤ 16) (ho : o + 16 ≤ vO) :
    WP isa (cmp o) s fun s' => s'.gpr .eax = BitVec.ofNat 32
        (if bytesAt s.mem (w64 W + BitVec.ofNat 64 o) t ++ zeros (16 - t) =
            bytesAt s.mem (w64 W + BitVec.ofNat 64 rO) 16 then 1 else 0) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 vO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => he.aW ho
  have wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn ho
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn' ho
  rw [slotv_eq] at hv
  simp only [tglO] at hv
  simp only [vO] at ho
  have hz := VG.Proof.AesGcm.X86.zero4_fold s.mem W 240
  simp only [Nat.reduceAdd] at hz
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 240, 16⟩] s.mem (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 240)) :=
    Cmac.frame_store4 _ _ _ _ _
  have hv' : (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 240)).readW (w64 W + BitVec.ofNat 64 180) 32 =
      BitVec.ofNat 32 t := by
    rw [slot_frame (W := W) (o := 180) fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (W := W) (a := 180) (n := 4) (d := 240) (k := 16) (by decide) (by decide) (by decide))]
    exact hv
  refine WP.seq (WP.of_runBlock ⟨_, by xrun [zero4, he.ebp, aW, wIn, rIn, readW_writeW_off, hv, hz, hv'], ?_⟩)
  have eo := aW (o := o) (by omega)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86.padLoop_ok (S := W + BitVec.ofNat 32 o) (d := 240) (t := t) (m := s.mem)
    (he.keep (by regs []) (by mems [])) (by mems []) (by regs [he.ebp]) (by regs [he.ebp]) (by regs []) ht1 ht
    (by mems []; rw [eo]; exact covers_left (covers_off he.wW (by omega) (by decide)))
    (by have := he.fw; rw [toNat_add32 (by omega)]; omega) (by rw [eo]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
    (by decide)) fun s' ⟨b, f, g, rd, wr⟩ => ?_)
  have he' : VG.Proof.AesGcm.X86.WEnv W s' := ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide)]; regs [he.ebp],
    by rw [wr]; mems [he.wW], he.fw⟩
  refine WP.mono (VG.Proof.AesGcm.X86.cmpTail_ok he') fun s'' ⟨a, m, rd', wr', g'⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hr : bytesAt s'.mem (w64 W + BitVec.ofNat 64 rO) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 rO) 16 :=
      bytesAt_frame f (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (W := W) (a := 196) (n := 16) (d := 240) (k := 16) (by decide) (by decide) (by decide))
        (by decide)
    simp only [vO] at a
    rw [a, b, hr, eo]
  · rw [m]; exact f
  · rw [g' _ (by decide) (by decide), g _ (by decide) (by decide) (by decide) (by decide)]; regs []
  · rw [g' _ (by decide) (by decide), g _ (by decide) (by decide) (by decide) (by decide)]; regs []
  · rw [g' _ (by decide) (by decide), g _ (by decide) (by decide) (by decide) (by decide)]; regs []
  · rw [rd', rd]; mems []
  · rw [wr', wr]; mems []

theorem cmp_ct {I : State → Prop} {W : BitVec 32} {t o : Nat} (ho : o = 0 ∨ o = uO)
    (h : ∀ s, I s → VG.Proof.AesGcm.X86.WEnv W s ∧ slotv s.mem W tglO = BitVec.ofNat 32 t) : CT I (cmp o) := by
  have hb : CT I (.block (zero4 vO ++ [.mov .edi (.reg .ebp), .alu .add .edi (imm o), .mov .edx (.reg .ebp),
      .alu .add .edx (imm vO), .mov .ecx (slot tglO)])) := by
    rcases ho with rfl | rfl <;>
    exact CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h _ h₁).1.ebp, (h _ h₂).1.ebp]) (by taint_decide)
  refine CT.seq (J := fun s => s.gpr .edi = W + BitVec.ofNat 32 o ∧ s.gpr .edx = W + BitVec.ofNat 32 vO ∧
      s.gpr .ecx = BitVec.ofNat 32 t ∧ s.gpr .ebp = W) hb
    (fun s hs => ?_) (CT.taint [.edi, .edx, .ecx, .ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide))
  obtain ⟨he, hv⟩ := h s hs
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => he.aW ho
  have wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn ho
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn' ho
  rw [slotv_eq] at hv
  simp only [tglO] at hv
  exact WP.of_runBlock ⟨_, by xrun [zero4, he.ebp, aW, wIn, rIn, readW_writeW_off, hv], by regs [he.ebp],
    by regs [he.ebp], by regs [], by regs [he.ebp]⟩

/-- `tagOut o`: the 16 bytes at `W + o` copied to `T` (kept at `W + tpO`). -/
theorem tagOut_ok {W T : BitVec 32} {o : Nat} {s : State} (he : VG.Proof.AesGcm.X86.WEnv W s) (ho : o + 16 ≤ 2560)
    (hT : slotv s.mem W tpO = T) (tW : Covers [⟨w64 T, 16⟩] s.wr) (fT : T.toNat + 16 ≤ 2 ^ 32) :
    WP isa (tagOut o) s fun s' => bytesAt s'.mem (w64 T) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 o) 16 ∧
      Frame [⟨w64 T, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => he.aW ho
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn' ho
  have aT : ∀ {k}, k < 16 → w64 (T + BitVec.ofNat 32 k) = w64 T + BitVec.ofNat 64 k := fun hk => w64_add (by omega)
  have tIn : ∀ {k}, k + 4 ≤ 16 → InRegions s.wr (w64 T + BitVec.ofNat 64 k) 4 := fun hk => in_off tW hk (by decide)
  rw [slotv_eq] at hT
  simp only [tpO] at hT
  have hs := store4_eq s.mem T 0
  simp only [Nat.reduceAdd] at hs
  refine WP.seq (WP.of_runBlock ⟨_, by xrun [he.ebp, aW, rIn, hT], ?_⟩)
  refine WP.of_runBlock ⟨_, by xrun [aT, tIn], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems [hs]
    rw [show w64 T + 0#64 = w64 T from BitVec.add_zero _, Cmac.bytesAt_store4, Cmac.bytesAt_split4, Cmac.le4_readW,
      Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]
  · mems [hs]
    rw [show w64 T + 0#64 = w64 T from BitVec.add_zero _]
    exact Cmac.frame_store4 _ _ _ _ _
  · regs []
  · regs []
  · regs []
  · mems []
  · mems []

theorem tagOut_ct {I : State → Prop} {W T : BitVec 32} {o : Nat} (ho : o = 0)
    (h : ∀ s, I s → VG.Proof.AesGcm.X86.WEnv W s ∧ slotv s.mem W tpO = T) : CT I (tagOut o) := by
  subst ho
  refine CT.seq (J := fun s => s.gpr .edi = T)
    (CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h _ h₁).1.ebp, (h _ h₂).1.ebp]) (by taint_decide))
    (fun s hs => ?_) (CT.taint [.edi] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide))
  obtain ⟨he, hT⟩ := h s hs
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => he.aW ho
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn' ho
  rw [slotv_eq] at hT
  simp only [tpO] at hT
  exact WP.of_runBlock ⟨_, by xrun [he.ebp, aW, rIn, hT], by regs []⟩

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.FinTag`. -/
section

/-!
# AES-GCM on x86: the tag of a streaming state (`finTag`)

Untrusted: everything here is checked by Lean. `finTag o` pads what GHASH
buffered (`text_len mod 16` bytes, or `aad_len mod 16` if there is no text)
and absorbs it (`flush 16`), then writes the tag to `W + o` (`tag`): the
full tag of the message the state represents (`finTag_pc`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes toBytes StreamRepr fullTag ghashInput)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem lensBlock_mod (a t : Nat) : lensBlock (a % 2 ^ 64) t = lensBlock a t := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (a % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * a)]
  congr 2
  omega

theorem val64_eq (lo hi : BitVec 32) : val64 lo hi = (hi ++ lo).toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

/-- The length of what GHASH buffered, modulo 16. -/
theorem ghashInput_mod {a c : List Byte} :
    (ghashInput a c).length % 16 = (if c = [] then a.length else c.length) % 16 := by
  by_cases hc : c = []
  · simp [ghashInput, hc]
  · rw [Proof.Gcm.ghashInput_of_ne hc]
    simp only [hc, ↓reduceIte, List.length_append, Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod a.length
    omega

theorem or_eq_zero32 (a b : BitVec 32) : (a ||| b = 0) ↔ (a = 0 ∧ b = 0) := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_or] at this
    have := Nat.or_eq_zero_iff.mp this
    exact ⟨BitVec.eq_of_toNat_eq (by simpa using this.1), BitVec.eq_of_toNat_eq (by simpa using this.2)⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Which length's remainder GHASH buffered: `text_len`'s, or `aad_len`'s if there is no text. -/
theorem buffered_mod {al ah xl xh : BitVec 32} {a c : List Byte} (hl : ah ++ al = BitVec.ofNat 64 a.length)
    (ht : (xh ++ xl).toNat = c.length) :
    (ghashInput a c).length % 16 = (if (xl ||| xh == 0) = true then al else xl).toNat % 16 := by
  rw [VG.Proof.AesGcm.X86.ghashInput_mod]
  have e := VG.Proof.AesGcm.X86.val64_eq xl xh
  simp only [val64] at e
  by_cases hc : c = []
  · subst hc
    have h0 : xl = 0 ∧ xh = 0 := by
      simp only [List.length_nil] at ht
      exact ⟨BitVec.eq_of_toNat_eq (by simp; omega), BitVec.eq_of_toNat_eq (by simp; omega)⟩
    obtain ⟨rfl, rfl⟩ := h0
    simp only [↓reduceIte, BitVec.or_self, beq_self_eq_true]
    exact (VG.Proof.AesGcm.X86.lo_mod16 hl).symm
  · have hne : (xl ||| xh == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, VG.Proof.AesGcm.X86.or_eq_zero32]
      rintro ⟨rfl, rfl⟩
      exact hc (List.eq_nil_of_length_eq_zero (by simp at ht; omega))
    simp only [hc, ↓reduceIte, hne, Bool.false_eq_true]
    omega

/-- The kept lengths and rounds `finTag` reads. -/
structure FinIn (Ctx St W SP : BitVec 32) (R : Nat) (al ah xl xh : BitVec 32) (s : State) : Prop where
  env : Env Ctx St W SP s
  al : slotv s.mem W alO = al
  ah : slotv s.mem W ahO = ah
  xl : slotv s.mem W xlO = xl
  xh : slotv s.mem W xhO = xh
  rounds : RoundsAt s.mem W R

/-- After `finTag o`: the tag of what the state represented, from `m₀`. -/
structure FinOut (Ctx St W SP : BitVec 32) (R o : Nat) (al ah xl xh : BitVec 32) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  rounds : RoundsAt s.mem W R
  frame : Frame (VG.Proof.AesGcm.X86.tagFrame St W SP o) m₀ s.mem
  tag : ∀ iv a c, StreamRepr m₀ (w64 St) (ciphOf m₀ Ctx R) (Hk m₀ Ctx) iv a c → ah ++ al = BitVec.ofNat 64 a.length →
    (xh ++ xl).toNat = c.length → bytesAt s.mem (w64 W + BitVec.ofNat 64 o) 16 = fullTag (ciphOf m₀ Ctx R) (Hk m₀ Ctx) iv a c

theorem FinIn.keep {Ctx St W SP : BitVec 32} {R : Nat} {al ah xl xh : BitVec 32} {s s' : State}
    (h : VG.Proof.AesGcm.X86.FinIn Ctx St W SP R al ah xl xh s) (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi)
    (hsp : s'.gpr .esp = s.gpr .esp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesGcm.X86.FinIn Ctx St W SP R al ah xl xh s' :=
  ⟨h.env.keep hbp hsi hsp hrd hwr (by rw [hm]), by rw [hm]; exact h.al, by rw [hm]; exact h.ah, by rw [hm]; exact h.xl,
    by rw [hm]; exact h.xh, by rw [hm]; exact h.rounds⟩

section
variable {Ctx St W SP : BitVec 32} (L : Lay Ctx St W SP 28)
include L

theorem finTag_pc {R o : Nat} (ho : o = 0 ∨ o = 112) {al ah xl xh : BitVec 32} :
    Pc (fun (m₀ : Mem) s => VG.Proof.AesGcm.X86.FinIn Ctx St W SP R al ah xl xh s ∧ s.mem = m₀) (finTag vg.callees o)
      (VG.Proof.AesGcm.X86.FinOut Ctx St W SP R o al ah xl xh ·) := by
  generalize hv : (if (xl ||| xh == 0) = true then al else xl) = v
  refine Pc.seq (Q := fun m₀ s => (VG.Proof.AesGcm.X86.FinIn Ctx St W SP R al ah xl xh s ∧ s.mem = m₀) ∧ s.gpr .eax = xl ∧
      s.gpr .ecx = al ∧ s.zf = some (xl ||| xh == 0))
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  · have he := h.env
    have h1 := h.xl; have h2 := h.al; have h3 := h.xh
    rw [slotv_eq] at h1 h2 h3
    refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn', h1, h2, h3], ⟨h.keep (by regs []) (by regs [])
      (by regs []) (by mems []) (by mems []) (by mems []), by mems []; exact hm⟩, by regs [], by regs [], by mems []⟩
  refine Pc.seq (Q := fun m₀ s => (VG.Proof.AesGcm.X86.FinIn Ctx St W SP R al ah xl xh s ∧ s.mem = m₀) ∧ s.gpr .eax = v) ?_ ?_
  · refine Pc.ite (xl ||| xh == 0) (fun _ _ h => h.2.2.2) (fun ht => ?_) (fun hf => ?_)
    · refine Pc.taint [] (fun m₀ s ⟨⟨h, hm⟩, _, hc, _⟩ => WP.of_runBlock ⟨_, by xrun [], ⟨h.keep (by regs [])
        (by regs []) (by regs []) (by mems []) (by mems []) (by mems []), by mems []; exact hm⟩, by
          rw [← hv, ht]; regs [hc]; rfl⟩) (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    · exact Pc.mono Pc.nil (fun _ _ h => h) fun _ _ ⟨h, ha, _, _⟩ => ⟨h, by rw [← hv, hf]; exact ha⟩
  refine Pc.seq (Q := fun m₀ s => VG.Proof.AesGcm.X86.FinIn Ctx St W SP R al ah xl xh s ∧
      slotv s.mem W bO = BitVec.ofNat 32 (v.toNat % 16) ∧ Frame [⟨w64 W + BitVec.ofNat 64 bO, 4⟩] m₀ s.mem)
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨h, hm⟩, ha⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.env.ebp, h₂.1.1.env.ebp]) (by taint_decide)) ?_
  · have he := h.env
    have hand := and15 v
    refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn, ha], ?_⟩
    have fb : Frame [⟨w64 W + BitVec.ofNat 64 bO, 4⟩] s.mem
        (s.mem.writeW (w64 W + BitVec.ofNat 64 bO) (v &&& BitVec.ofNat 32 15)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have sK : ∀ {q}, 128 ≤ q → q + 4 ≤ 240 → slotv (s.mem.writeW (w64 W + BitVec.ofNat 64 bO)
        (v &&& BitVec.ofNat 32 15)) W q = slotv s.mem W q := fun h₁ h₂ =>
      slot_frame fb fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by simp only [bO]; omega)) (by omega) (by decide)
    refine ⟨⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by
        simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact sK (by decide) (by decide)),
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sK (by decide) (by decide)]; exact h.al,
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sK (by decide) (by decide)]; exact h.ah,
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sK (by decide) (by decide)]; exact h.xl,
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sK (by decide) (by decide)]; exact h.xh,
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact ⟨(sK (q := 148) (by decide) (by decide)).trans
        h.rounds.1, h.rounds.2⟩⟩, ?_, ?_⟩
    · simp only [mem_setMem, mem_setReg, mem_arithFlags, slotv_eq, Mem.readW_writeW_self32]; exact hand
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [← hm]; exact fb
  refine Pc.seq (Pc.lift (flush_pc L (yo := 16) (.inr rfl) (b := v.toNat % 16) (Nat.mod_lt _ (by decide)))
    (fun _ s => s.mem) fun m₀ s h => ⟨⟨h.1.env, h.2.1⟩, rfl⟩) ?_
  refine Pc.mono (Pc.lift (VG.Proof.AesGcm.X86.tag_pc L (al := alO) (ah := ahO) (tl := xlO) (th := xhO) ho
      (.inr (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)) (alo := al) (ahi := ah) (tlo := xl) (thi := xh))
    (fun _ s => s.mem) fun m₀ s' ⟨s, ⟨h, _, _⟩, fo, _, _⟩ => ⟨⟨fo.env, ?_, rounds_frame fo.frame (VG.Proof.AesGcm.X86.kept_tFrame L)
      h.rounds⟩, rfl⟩) (fun _ _ h => h) fun m₀ s'' ⟨s', ⟨s, ⟨h, hb, fb⟩, fo, _, _⟩, tg, _, _⟩ => ?_
  · refine ⟨tg.env, tg.rounds, ?_, fun iv a c hr hl ht => ?_⟩
    · refine (fb.sub fun r hr => ?_).trans ((VG.Proof.AesGcm.X86.t_tagFrame fo.frame).trans tg.frame)
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩
    rw [Proof.Gcm.streamRepr_iff, VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.ofNat_lit] at hr
    obtain ⟨hj, ha, -⟩ := hr
    have dS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 bO, 4⟩ : Region)],
        (⟨w64 St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
    have hHs : Hk s.mem Ctx = Hk m₀ Ctx := blockAt_frame fb fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
    have hx := VG.Proof.AesGcm.X86.buffered_mod hl ht
    rw [hv] at hx
    have ha₁ : Absorbed s.mem (w64 St + BitVec.ofNat 64 16) (w64 St + BitVec.ofNat 64 32) (Hk s.mem Ctx)
        (ghashInput a c) := by
      rw [hHs]
      exact ha.congr (blockAt_frame fb (dS (by decide))) (bytesAt_frame fb (dS (d := 32)
        (k := (ghashInput a c).length % 16) (by omega)) (by omega))
    have hab := fo.abs _ hx ha₁
    have acc := hab.1
    rw [show ghashInput a c ++ zeros (padLen (ghashInput a c).length) = padded a c from rfl,
      Proof.Gcm.whole_of_mod (Proof.Gcm.length_padded a c), List.take_of_length_le (Nat.le_refl _)] at acc
    have hH' : Hk s'.mem Ctx = Hk s.mem Ctx := blockAt_frame fo.frame (ctx_tFrame L (.inr rfl))
    have hC : ciphOf s'.mem Ctx R = ciphOf m₀ Ctx R := by
      rw [ciph_frame fo.frame (VG.Proof.AesGcm.X86.ctx_tFrame' L) h.rounds.2, ciph_frame fb (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide))) h.rounds.2]
    have hJ : blockAt s'.mem (w64 St) = blockAt m₀ (w64 St) := by
      have e₁ := blockAt_frame fo.frame (p := w64 St + BitVec.ofNat 64 0) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
        · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
        · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
        · exact (L.stk_st (by decide)).symm
      have e₂ := blockAt_frame fb (dS (d := 0) (k := 16) (by decide))
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e₁ e₂
      rw [e₁, e₂]
    have hva : val64 al ah = a.length % 2 ^ 64 := by rw [VG.Proof.AesGcm.X86.val64_eq, hl, BitVec.toNat_ofNat]
    have hvx : val64 xl xh = c.length := by rw [VG.Proof.AesGcm.X86.val64_eq, ht]
    rw [tg.out, hH', hHs, acc, hC, hJ, hj, hva, hvx, VG.Proof.AesGcm.X86.lensBlock_mod, hHs, Proof.Gcm.fullTag_eq]
  · have sl : ∀ {q}, 112 ≤ q → q + 4 ≤ 240 → slotv s'.mem W q = slotv s.mem W q := fun h₁ h₂ =>
      slot_frame fo.frame (slot_tFrame L (.inr rfl) h₁ h₂)
    exact ⟨by rw [sl (by decide) (by decide)]; exact h.al, by rw [sl (by decide) (by decide)]; exact h.ah,
      by rw [sl (by decide) (by decide)]; exact h.xl, by rw [sl (by decide) (by decide)]; exact h.xh⟩

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.Init`. -/
section

/-!
# AES-GCM on x86: `vg_aes_gcm_init`

Untrusted: everything here is checked by Lean. The key schedule
(`vg_aes_expand_key_scratch`), then the hash subkey `CIPH_K(0¹²⁸)` (`vg_aes_ctr32`
on a zero block, with a zero counter block at `T`), as one `Pc`
(`init_pc`): correct (`init_correct`) and constant time (`init_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt KeyRepr)

theorem shr2 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 2 = BitVec.ofNat 32 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- The facts of `init`'s precondition about the public data `p` alone. -/
structure InitPure (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  kc : (⟨w64 (p.2 0), (p.2 1).toNat⟩ : Region).Disjoint ⟨w64 (p.2 2), 256⟩
  kw : (⟨w64 (p.2 0), (p.2 1).toNat⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  cw : (⟨w64 (p.2 2), 256⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  r_c : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 2), 256⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  k_k : (below p.1 28).Disjoint ⟨w64 (p.2 0), (p.2 1).toNat⟩
  k_c : (below p.1 28).Disjoint ⟨w64 (p.2 2), 256⟩
  k_w : (below p.1 28).Disjoint ⟨w64 (p.2 3), 2560⟩
  fk : (p.2 0).toNat + (p.2 1).toNat ≤ 2 ^ 32
  fc : (p.2 2).toNat + 256 ≤ 2 ^ 32
  fw : (p.2 3).toNat + 2560 ≤ 2 ^ 32
  sp : 28 ≤ p.1.toNat
  len : (p.2 1).toNat = 16 ∨ (p.2 1).toNat = 24 ∨ (p.2 1).toNat = 32

theorem initPure_of {p : BitVec 32 × (Nat → BitVec 32)} {s : State} (h : VG.Proof.AesGcm.X86.initPre s) (hp : VG.Proof.AesGcm.X86.pubOf 4 s = p) :
    VG.Proof.AesGcm.X86.InitPure p := by
  simp only [VG.Proof.AesGcm.X86.initPre] at h
  obtain ⟨-, -, d_kc, d_kw, -, d_cw, -, -, -, r_c, r_w, -, k_k, k_c, k_w, -, fk, fc, fw, sp, -, hl⟩ := h
  rw [VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.below_eq sp] at k_k k_c k_w
  have a0 := VG.Proof.AesGcm.X86.pubOf_arg hp (i := 0) (by decide); have a1 := VG.Proof.AesGcm.X86.pubOf_arg hp (i := 1) (by decide)
  have a2 := VG.Proof.AesGcm.X86.pubOf_arg hp (i := 2) (by decide); have a3 := VG.Proof.AesGcm.X86.pubOf_arg hp (i := 3) (by decide)
  have e := VG.Proof.AesGcm.X86.pubOf_esp hp
  simp only [a0, a1, a2, a3, e] at d_kc d_kw d_cw r_c r_w k_k k_c k_w fk fc fw sp hl
  exact ⟨d_kc, d_kw, d_cw, r_c, r_w, k_k, k_c, k_w, fk, fc, fw, sp, hl⟩

/-- `ctx` and `W` and the stack apart, at offsets. -/
theorem InitPure.cw' {p : BitVec 32 × (Nat → BitVec 32)} (h : VG.Proof.AesGcm.X86.InitPure p) {a n d k : Nat} (ha : a + n ≤ 256)
    (hd : d + k ≤ 2560) :
    (⟨w64 (p.2 2) + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 (p.2 3) + BitVec.ofNat 64 d, k⟩ :=
  (h.cw.sub_left (Lay.ctxSub ha)).sub_right (Lay.wSub hd)

abbrev initTail : List Instr :=
  [.mov .ecx (argOp 1), .mov .ebx (.reg .ecx), .shift .shr .ebx 2, .alu .add .ebx (imm 6), .mov .eax (argOp 0),
    .mov .edx (.reg .esi), .alu .add .ebp (imm scrO)]

abbrev initMid : List Instr :=
  unscr ++ [.mov .eax (imm 0), .store (at_ .esi 240) .eax, .store (at_ .esi 244) .eax,
      .store (at_ .esi 248) .eax, .store (at_ .esi 252) .eax] ++ zero4 tO ++
      [.mov .eax (.reg .esi), .mov .ecx (.reg .ebx), .mov .edx (.reg .ebp), .alu .add .edx (imm tO),
        .mov .ebx (.reg .esi), .alu .add .ebx (imm 240), .mov .edi (imm 1), .alu .add .ebp (imm scrO)]

theorem init_eq : init vg.callees = .seq (entry 3 (([.mov .esi (argOp 2)] : List Instr) ++
    (([] : List (Nat × Nat)).flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ VG.Proof.AesGcm.X86.initTail)))
    (.seq (keyCall vg.callees) (.seq (.block VG.Proof.AesGcm.X86.initMid) (.seq (ctrCall vg.callees) (.block (unscr ++ restore))))) := rfl

/-- After the entry: the arguments of `vg_aes_expand_key_scratch`. -/
structure IEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : VG.Proof.AesGcm.X86.initPre s₀
  pub : VG.Proof.AesGcm.X86.pubOf 4 s₀ = p
  call : KeyCall s (p.2 0) (p.2 2) (p.2 3 + BitVec.ofNat 32 512) (p.2 1).toNat
  ebx : s.gpr .ebx = BitVec.ofNat 32 ((p.2 1).toNat / 4 + 6)
  esi : s.gpr .esi = p.2 2
  esp : s.gpr .esp = p.1
  saved : SavedAt s.mem (p.2 3) s₀
  frame : Frame [⟨w64 (p.2 3) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem iEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => VG.Proof.AesGcm.X86.initPre s₀ ∧ VG.Proof.AesGcm.X86.pubOf 4 s₀ = p ∧ s = s₀)
      (entry 3 (([.mov .esi (argOp 2)] : List Instr) ++ (([] : List (Nat × Nat)).flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ VG.Proof.AesGcm.X86.initTail)))
      (VG.Proof.AesGcm.X86.IEnt p) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have hc := VG.Proof.AesGcm.X86.initPure_of hpre hpub
    have hp := hpre
    simp only [VG.Proof.AesGcm.X86.initPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, d_wa, -, -, -, -, -, -, -, -, -, -, -, -, fa, -⟩ := hp
    have a : ∀ i, i < 4 → arg s₀ i = p.2 i := fun i hi => VG.Proof.AesGcm.X86.pubOf_arg hpub hi
    have esp := VG.Proof.AesGcm.X86.pubOf_esp hpub
    have wW : Covers [⟨w64 (arg s₀ 3), 2560⟩] s₀.wr := by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 4] (s₀.rd ++ s₀.wr) := by
      rw [VG.Proof.AesGcm.X86.argsR_eq, hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 4).Disjoint ⟨w64 (arg s₀ 3), 2560⟩ := by rw [VG.Proof.AesGcm.X86.argsR_eq]; exact d_wa.symm
    refine entry_ok [] VG.Proof.AesGcm.X86.initTail (by decide) (by decide) (by decide) (by decide) rfl rfl wW rA aw (by omega)
      (by rw [a 3 (by decide)]; exact hc.fw) fun s₂ e => ?_
    have i₁ : InRegions (s₂.rd ++ s₂.wr) (argA (s₀.gpr .esp) 1) 4 := by
      rw [e.rd, e.wr]; exact VG.Proof.AesGcm.X86.argIn_of rA (by omega) (by decide)
    have i₀ : InRegions (s₂.rd ++ s₂.wr) (argA (s₀.gpr .esp) 0) 4 := by
      rw [e.rd, e.wr]; exact VG.Proof.AesGcm.X86.argIn_of rA (by omega) (by decide)
    have v₁ := e.args 1 (by decide)
    have v₀ := e.args 0 (by decide)
    have hL : (p.2 1).toNat < 2 ^ 32 := (p.2 1).isLt
    have hsh : arg s₀ 1 >>> 2 + BitVec.ofNat 32 6 = BitVec.ofNat 32 ((p.2 1).toNat / 4 + 6) := by
      rw [a 1 (by decide), ← VG.Proof.AesGcm.X86.ofNat_toNat32 (p.2 1), VG.Proof.AesGcm.X86.shr2 hL, ofNat_add_ofNat32, toNat_ofNat32 hL]
    refine ⟨_, by xrun [e.esp, i₁, i₀, v₁, v₀, e.esi, e.ebp], ?_⟩
    have eS := w64_add (x := p.2 3) (k := 512) (by have := hc.fw; omega)
    have bsub : Region.Sub (below p.1 20) (below p.1 28) := VG.X86.below_sub (by decide) hc.sp
    have hrd' : s₀.rd = [⟨w64 (p.2 0), (p.2 1).toNat⟩] := by rw [hrd, a 0 (by decide), a 1 (by decide)]
    have hwr' : s₀.wr = [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩] := by
      rw [hwr, a 2 (by decide), a 3 (by decide)]
    refine ⟨hpre, hpub, ⟨by regs [v₀]; exact a 0 (by decide),
      by regs [v₁]; rw [a 1 (by decide)]; exact (VG.Proof.AesGcm.X86.ofNat_toNat32 _).symm,
      by regs [e.esi]; exact a 2 (by decide), by regs [e.ebp]; rw [a 3 (by decide)],
      hc.len, by regs [e.esp, esp]; have := hc.sp; omega, hc.kc.sub_right (Region.sub_prefix (by decide)),
      by rw [eS]; exact hc.kw.sub_right (Lay.wSub (by decide)),
      by rw [eS]; exact (hc.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)),
      by regs [e.esp, esp]; exact hc.k_k.sub_left bsub,
      by regs [e.esp, esp]; exact (hc.k_c.sub_left bsub).sub_right (Region.sub_prefix (by decide)),
      by regs [e.esp, esp]; rw [eS]; exact (hc.k_w.sub_left bsub).sub_right (Lay.wSub (by decide)),
      hc.fk, by have := hc.fc; omega, by rw [toNat_add32 (by have := hc.fw; omega)]; have := hc.fw; omega,
      by mems [e.rd, e.wr, hrd']; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), ?_⟩, by regs [hsh], by regs [e.esi]; exact a 2 (by decide),
      by regs [e.esp, esp], by mems []; rw [← a 3 (by decide)]; exact e.saved,
      by mems []; rw [← a 3 (by decide)]; exact e.frame, by mems [e.rd], by mems [e.wr]⟩
    rw [eS]
    mems [e.wr, hwr']
    have c₁ : Covers [⟨w64 (p.2 2), 240⟩] [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩] := by
      have := covers_off (p := w64 (p.2 2)) (k := 256) (d := 0) (n := 240)
        (rs := [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩]) (VG.Proof.AesGcm.X86.covers_of_mem (by simp)) (by decide)
        (by decide)
      simpa using this
    exact covers_cons c₁ (covers_cons (covers_off (p := w64 (p.2 3)) (k := 2560) (d := 512) (n := 512)
      (VG.Proof.AesGcm.X86.covers_of_mem (by simp)) (by decide) (by decide)) covers_nil)
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 3 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [VG.Proof.AesGcm.X86.pubOf_esp h₁, VG.Proof.AesGcm.X86.pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    subst s
    have hp := hpre
    simp only [VG.Proof.AesGcm.X86.initPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fa, -⟩ := hp
    have rA : Covers [argsR (s₀.gpr .esp) 4] (s₀.rd ++ s₀.wr) := by
      rw [VG.Proof.AesGcm.X86.argsR_eq, hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
    exact WP.mono (VG.Proof.AesGcm.X86.arg0_ok (VG.Proof.AesGcm.X86.argIn_of rA (by omega) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact VG.Proof.AesGcm.X86.pubOf_arg hpub (by decide), by rw [sp]; exact VG.Proof.AesGcm.X86.pubOf_esp hpub⟩

/-- After the key schedule and `initMid`: the arguments of `vg_aes_ctr32` for `H`. -/
structure IMid (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  ent : ∃ s₁, VG.Proof.AesGcm.X86.IEnt p s₀ s₁ ∧ Frame [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, below p.1 28] s₁.mem s.mem
  call : CtrCall s (p.2 2) (p.2 3 + BitVec.ofNat 32 96) (p.2 2 + BitVec.ofNat 32 240) (p.2 3 + BitVec.ofNat 32 512)
    ((p.2 1).toNat / 4 + 6) 1
  esp : s.gpr .esp = p.1
  sched : bytesAt s.mem (w64 (p.2 2)) (16 * ((p.2 1).toNat / 4 + 6 + 1)) =
    Spec.Aes.expandKey (bytesAt s₀.mem (w64 (p.2 0)) (p.2 1).toNat)
  zt : blockAt s.mem (w64 (p.2 3) + BitVec.ofNat 64 96) = 0
  zh : blockAt s.mem (w64 (p.2 2) + BitVec.ofNat 64 240) = 0
  saved : SavedAt s.mem (p.2 3) s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem rounds_of_len {L : Nat} (h : L = 16 ∨ L = 24 ∨ L = 32) : L / 4 + 6 = 10 ∨ L / 4 + 6 = 12 ∨ L / 4 + 6 = 14 := by
  rcases h with rfl | rfl | rfl <;> decide

theorem iMid_ok {p : BitVec 32 × (Nat → BitVec 32)} (hc : VG.Proof.AesGcm.X86.InitPure p) {s₀ s₁ s : State} (h : VG.Proof.AesGcm.X86.IEnt p s₀ s₁)
    (g : KeyPost s₁ (p.2 0) (p.2 2) (p.2 3 + BitVec.ofNat 32 512) (p.2 1).toNat s) :
    WP isa (.block VG.Proof.AesGcm.X86.initMid) s (VG.Proof.AesGcm.X86.IMid p s₀) := by
  have eS := w64_add (x := p.2 3) (k := 512) (by have := hc.fw; omega)
  have eT := w64_add (x := p.2 3) (k := 96) (by have := hc.fw; omega)
  have eH := w64_add (x := p.2 2) (k := 240) (by have := hc.fc; omega)
  have bp : s.gpr .ebp = p.2 3 + BitVec.ofNat 32 512 := by rw [g.saved .ebp (by decide), h.call.ebp]
  have si : s.gpr .esi = p.2 2 := by rw [g.saved .esi (by decide), h.esi]
  have bx : s.gpr .ebx = BitVec.ofNat 32 ((p.2 1).toNat / 4 + 6) := by rw [g.saved .ebx (by decide), h.ebx]
  have sp : s.gpr .esp = p.1 := by rw [g.saved .esp (by decide), h.esp]
  have hwr : s.wr = s₀.wr := by rw [g.wr, h.wr]
  have hp := h.pre
  simp only [VG.Proof.AesGcm.X86.initPre] at hp
  have hwr₀ : s₀.wr = [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩] := by
    rw [hp.2.1, VG.Proof.AesGcm.X86.pubOf_arg h.pub (i := 2) (by decide), VG.Proof.AesGcm.X86.pubOf_arg h.pub (i := 3) (by decide)]
  have wC : Covers [⟨w64 (p.2 2), 256⟩] s.wr := by rw [hwr, hwr₀]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
  have wW : Covers [⟨w64 (p.2 3), 2560⟩] s.wr := by rw [hwr, hwr₀]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
  have hb0 : p.2 3 + BitVec.ofNat 32 512 - BitVec.ofNat 32 512 = p.2 3 := BitVec.add_sub_cancel _ _
  have aC : ∀ {o}, o < 256 → w64 (p.2 2 + BitVec.ofNat 32 o) = w64 (p.2 2) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by have := hc.fc; omega)
  have aW : ∀ {o}, o < 2560 → w64 (p.2 3 + BitVec.ofNat 32 o) = w64 (p.2 3) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by have := hc.fw; omega)
  have cIn : ∀ {d}, d + 4 ≤ 256 → InRegions s.wr (w64 (p.2 2) + BitVec.ofNat 64 d) 4 :=
    fun hd => in_off wC hd (by decide)
  have wIn : ∀ {d}, d + 4 ≤ 2560 → InRegions s.wr (w64 (p.2 3) + BitVec.ofNat 64 d) 4 :=
    fun hd => in_off wW hd (by decide)
  have hzC : ∀ m : Mem, Cmac.zero4 m (w64 (p.2 2) + BitVec.ofNat 64 240) =
      (((m.writeW (w64 (p.2 2) + BitVec.ofNat 64 240) (BitVec.ofNat 32 0)).writeW (w64 (p.2 2) + BitVec.ofNat 64 244)
      (BitVec.ofNat 32 0)).writeW (w64 (p.2 2) + BitVec.ofNat 64 248) (BitVec.ofNat 32 0)).writeW
      (w64 (p.2 2) + BitVec.ofNat 64 252) (BitVec.ofNat 32 0) := fun m => by
    simp only [Cmac.zero4, Cmac.store4, add_ofNat_assoc]; rfl
  have hzW : ∀ m : Mem, Cmac.zero4 m (w64 (p.2 3) + BitVec.ofNat 64 96) =
      (((m.writeW (w64 (p.2 3) + BitVec.ofNat 64 96) (BitVec.ofNat 32 0)).writeW (w64 (p.2 3) + BitVec.ofNat 64 100)
      (BitVec.ofNat 32 0)).writeW (w64 (p.2 3) + BitVec.ofNat 64 104) (BitVec.ofNat 32 0)).writeW
      (w64 (p.2 3) + BitVec.ofNat 64 108) (BitVec.ofNat 32 0) := fun m => by
    simp only [Cmac.zero4, Cmac.store4, add_ofNat_assoc]; rfl
  refine WP.of_runBlock ⟨_, by xrun [VG.Proof.AesGcm.X86.initMid, unscr, bp, si, bx, hb0, aC, aW, cIn, wIn, zero4, ← hzC, ← hzW], ?_⟩
  generalize hZ₁ : Cmac.zero4 s.mem (w64 (p.2 2) + BitVec.ofNat 64 240) = Z₁
  generalize hZ₂ : Cmac.zero4 Z₁ (w64 (p.2 3) + BitVec.ofNat 64 96) = Z₂
  have f₁ : Frame [⟨w64 (p.2 2) + BitVec.ofNat 64 240, 16⟩] s.mem Z₁ := by
    rw [← hZ₁]; exact Cmac.frame_store4 _ _ _ _ _
  have f₂ : Frame [⟨w64 (p.2 3) + BitVec.ofNat 64 96, 16⟩] Z₁ Z₂ := by rw [← hZ₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hfit := hc.fc
  have hfw := hc.fw
  have hsp := hc.sp
  have bsub : Region.Sub (below p.1 20) (below p.1 28) := VG.X86.below_sub (by decide) hsp
  have gf := g.frame
  rw [h.esp, eS] at gf
  have go := g.out
  have dK : ∀ r ∈ [(⟨w64 (p.2 3) + BitVec.ofNat 64 128, 2432⟩ : Region)],
      (⟨w64 (p.2 0), (p.2 1).toNat⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hc.kw.sub_right (Lay.wSub (by decide))
  rw [bytesAt_frame h.frame dK (by have := hc.fk; omega)] at go
  have hR := VG.Proof.AesGcm.X86.rounds_of_len hc.len
  have hRb : 16 * ((p.2 1).toNat / 4 + 6 + 1) ≤ 240 := by rcases hR with h' | h' | h' <;> omega
  have dZ : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 240, 16⟩ : Region)],
      (⟨w64 (p.2 2), 16 * ((p.2 1).toNat / 4 + 6 + 1)⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := Offset.disjoint (w64 (p.2 2)) (d := 0) (n := 16 * ((p.2 1).toNat / 4 + 6 + 1)) (e := 240) (k := 16)
      (.inl (by omega)) (by omega) (by omega)
    simpa using this
  have dZ₂ : ∀ r ∈ [(⟨w64 (p.2 3) + BitVec.ofNat 64 96, 16⟩ : Region)],
      (⟨w64 (p.2 2), 16 * ((p.2 1).toNat / 4 + 6 + 1)⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hc.cw.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))
  have hsv : SavedAt Z₂ (p.2 3) s₀ := by
    refine ((h.saved.frame gf fun r hr => ?_).frame f₁ fun r hr => ?_).frame f₂ fun r hr => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ((hc.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))).symm
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact ((hc.k_w.sub_left bsub).sub_right (Lay.wSub (by decide))).symm
    · simp only [List.mem_singleton] at hr; subst hr; exact (hc.cw' (by decide) (by decide)).symm
    · simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  have kc := hc.cw' (a := 0) (n := 240) (d := 96) (k := 16) (by decide) (by decide)
  have ks := hc.cw' (a := 0) (n := 240) (d := 512) (k := 2048) (by decide) (by decide)
  have cd := hc.cw' (a := 240) (n := 16) (d := 96) (k := 16) (by decide) (by decide)
  have ds := hc.cw' (a := 240) (n := 16) (d := 512) (k := 2048) (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at kc ks
  have hwr' := hwr
  rw [hwr₀] at hwr'
  have rC : Covers [⟨w64 (p.2 2), 240⟩] (s.rd ++ s.wr) := by
    have := covers_off (p := w64 (p.2 2)) (k := 256) (d := 0) (n := 240) (rs := s.wr) wC (by decide) (by decide)
    exact covers_left (by simpa using this)
  refine ⟨⟨s₁, h, ?_⟩, ⟨by regs [si], by regs [bx], by regs [], by regs [si], by regs [], by regs [],
    hR, by regs [sp]; omega, by rw [eT]; exact kc, ?_, by rw [eS]; exact ks,
    by rw [eT, eH]; exact cd.symm, by rw [eT, eS]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide),
    by rw [eH, eS]; exact ds, by regs [sp]; exact hc.k_c.sub_right (Region.sub_prefix (by decide)),
    by regs [sp]; rw [eT]; exact hc.k_w.sub_right (Lay.wSub (by decide)),
    by regs [sp]; rw [eH]; exact hc.k_c.sub_right (Lay.ctxSub (by decide)),
    by regs [sp]; rw [eS]; exact hc.k_w.sub_right (Lay.wSub (by decide)),
    by omega, by rw [toNat_add32 (by omega)]; omega, by rw [toNat_add32 (by omega)]; omega,
    by rw [toNat_add32 (by omega)]; omega, by mems []; exact rC, ?_⟩, by regs [sp], ?_, ?_, ?_, ?_, by mems [g.rd, h.rd],
    by mems [g.wr, h.wr]⟩
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    refine (gf.sub fun r hr => ?_).trans ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
      · exact ⟨_, by simp, bsub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Lay.ctxSub (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
  · rw [eH]
    have := Offset.disjoint (w64 (p.2 2)) (d := 0) (n := 240) (e := 240) (k := 16 * 1) (.inl (by omega)) (by omega)
      (by omega)
    simpa using this
  · mems []
    rw [eT, eH, eS]
    exact covers_cons (covers_off wW (by decide) (by decide)) (covers_cons (covers_off wC (by decide) (by decide))
      (covers_cons (covers_off wW (by decide) (by decide)) covers_nil))
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [bytesAt_frame f₂ dZ₂ (by omega), bytesAt_frame f₁ dZ (by omega)]
    exact go
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [← hZ₂, blockAt, zero4_bytes', ofBytes_zeros]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [blockAt_frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cd, ← hZ₁, blockAt, zero4_bytes', ofBytes_zeros]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact hsv

theorem init_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => VG.Proof.AesGcm.X86.initPre s₀ ∧ VG.Proof.AesGcm.X86.pubOf 4 s₀ = p ∧ s = s₀) (init vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ initX86.post s₀ s') := by
  by_cases hex : ∃ s₀, VG.Proof.AesGcm.X86.initPre s₀ ∧ VG.Proof.AesGcm.X86.pubOf 4 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have hc := VG.Proof.AesGcm.X86.initPure_of hz hzp
  rw [VG.Proof.AesGcm.X86.init_eq]
  refine Pc.seq (VG.Proof.AesGcm.X86.iEntry_pc p) ?_
  refine Pc.seq (Pc.of (I := fun s => KeyCall s (p.2 0) (p.2 2) (p.2 3 + BitVec.ofNat 32 512) (p.2 1).toNat ∧
    s.gpr .esp = p.1) (fun s h => (key_call vg) h.1) (key_ct vg fun s h => h) _ fun _ _ h => ⟨h.call, h.esp⟩) ?_
  refine Pc.seq (Q := VG.Proof.AesGcm.X86.IMid p) (Pc.taint [.esi, .ebp] (fun s₀ s ⟨s₁, h, g⟩ => VG.Proof.AesGcm.X86.iMid_ok hc h g)
    (fun _ _ s₁ s₂ ⟨t₁, h₁, g₁⟩ ⟨t₂, h₂, g₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [g₁.saved .esi (by decide), g₂.saved .esi (by decide), h₁.esi, h₂.esi]
      · rw [g₁.saved .ebp (by decide), g₂.saved .ebp (by decide), h₁.call.ebp, h₂.call.ebp]) (by taint_decide)) ?_
  refine Pc.seq (Pc.of (I := fun s => CtrCall s (p.2 2) (p.2 3 + BitVec.ofNat 32 96) (p.2 2 + BitVec.ofNat 32 240)
    (p.2 3 + BitVec.ofNat 32 512) ((p.2 1).toNat / 4 + 6) 1 ∧ s.gpr .esp = p.1) (fun s h => (ctr_call vg) h.1)
    (ctr_ct vg fun s h => h) _ fun _ _ h => ⟨h.call, h.esp⟩) ?_
  refine Pc.taint [.ebp] (fun s₀ s' ⟨s, hm, g⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, h₁, g₁⟩ ⟨_, h₂, g₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [g₁.saved .ebp (by decide), g₂.saved .ebp (by decide), h₁.call.ebp, h₂.call.ebp]) (by taint_decide)
  obtain ⟨s₁, h₁, fE⟩ := hm.ent
  have eS := w64_add (x := p.2 3) (k := 512) (by have := hc.fw; omega)
  have eT := w64_add (x := p.2 3) (k := 96) (by have := hc.fw; omega)
  have eH := w64_add (x := p.2 2) (k := 240) (by have := hc.fc; omega)
  have bp : s'.gpr .ebp = p.2 3 + BitVec.ofNat 32 512 := by rw [g.saved .ebp (by decide), hm.call.ebp]
  have hb0 : p.2 3 + BitVec.ofNat 32 512 - BitVec.ofNat 32 512 = p.2 3 := BitVec.add_sub_cancel _ _
  have gf := g.frame
  rw [hm.esp, eT, eH, eS] at gf
  have hsp := hc.sp
  have dC : ∀ {a k : Nat}, a + k ≤ 240 → ∀ r ∈ [(⟨w64 (p.2 3) + BitVec.ofNat 64 96, 16⟩ : Region),
      ⟨w64 (p.2 2) + BitVec.ofNat 64 240, 16 * 1⟩, ⟨w64 (p.2 3) + BitVec.ofNat 64 512, 2048⟩, below p.1 28],
      (⟨w64 (p.2 2) + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hc.cw' (by omega) (by decide)
    · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    · exact hc.cw' (by omega) (by decide)
    · exact (hc.k_c.sub_right (Lay.ctxSub (by omega))).symm
  have hsv : SavedAt s'.mem (p.2 3) s₀ := hm.saved.frame gf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact (hc.cw' (by decide) (by decide)).symm
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact ((hc.k_w.sub_right (Lay.wSub (by decide)))).symm
  have rG : ∀ r ∈ [(⟨w64 (p.2 3) + BitVec.ofNat 64 96, 16⟩ : Region),
      ⟨w64 (p.2 2) + BitVec.ofNat 64 240, 16 * 1⟩, ⟨w64 (p.2 3) + BitVec.ofNat 64 512, 2048⟩, below p.1 28],
      (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hc.r_w.sub_right (Lay.wSub (by decide))
    · exact hc.r_c.sub_right (Lay.ctxSub (by decide))
    · exact hc.r_w.sub_right (Lay.wSub (by decide))
    · exact VG.Proof.AesGcm.X86.ret_below hsp
  have rF : ∀ r ∈ [(⟨w64 (p.2 2), 256⟩ : Region), ⟨w64 (p.2 3), 2560⟩, below p.1 28],
      (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hc.r_c
    · exact hc.r_w
    · exact VG.Proof.AesGcm.X86.ret_below hsp
  have rE : ∀ r ∈ [(⟨w64 (p.2 3) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.r_w.sub_right (Lay.wSub (by decide))
  have hret : s'.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [VG.Proof.AesGcm.X86.pubOf_esp h₁.pub, VG.Proof.AesGcm.X86.ret_kept gf rG, VG.Proof.AesGcm.X86.ret_kept fE rF, VG.Proof.AesGcm.X86.ret_kept h₁.frame rE]
  have hwr₀ : s'.wr = s₀.wr := by rw [g.wr, hm.wr]
  have hp := h₁.pre
  simp only [VG.Proof.AesGcm.X86.initPre] at hp
  have wW : Covers [⟨w64 (p.2 3), 2560⟩] s'.wr := by
    rw [hwr₀, hp.2.1, VG.Proof.AesGcm.X86.pubOf_arg h₁.pub (i := 3) (by decide)]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
  refine WP.block_append (WP.of_runBlock ⟨_, by xrun [unscr, bp, hb0], ?_⟩)
  refine WP.mono (exit_ok (W := p.2 3) (by regs []) (by regs [g.saved .esp (by decide), hm.esp, VG.Proof.AesGcm.X86.pubOf_esp h₁.pub])
    (by mems []; exact covers_left wW) hc.fw (by mems []; exact hsv) (by mems []; exact hret))
    fun s'' ⟨abi, m'', _, _, _⟩ => ⟨abi, ?_⟩
  have hA : ∀ i, i < 4 → arg s₀ i = p.2 i := fun i hi => VG.Proof.AesGcm.X86.pubOf_arg h₁.pub hi
  show KeyRepr s''.mem _ _
  rw [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide), m'']
  simp only [mem_setMem, mem_setReg, mem_arithFlags]
  have hlen := length_bytesAt s₀.mem (w64 (p.2 0)) (p.2 1).toNat
  have hR := VG.Proof.AesGcm.X86.rounds_of_len hc.len
  have hRb : 16 * ((p.2 1).toNat / 4 + 6 + 1) ≤ 240 := by rcases hR with h' | h' | h' <;> omega
  have hs : bytesAt s'.mem (w64 (p.2 2)) (16 * ((p.2 1).toNat / 4 + 6 + 1)) =
      Spec.Aes.expandKey (bytesAt s₀.mem (w64 (p.2 0)) (p.2 1).toNat) := by
    have := dC (a := 0) (k := 16 * ((p.2 1).toNat / 4 + 6 + 1)) (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [bytesAt_frame gf this (by omega)]; exact hm.sched
  refine ⟨by rw [hlen]; exact hs, ?_⟩
  have go := g.out
  rw [eH, eT, blocksAt_one, blocksAt_one, hm.zh, hm.zt, hm.sched] at go
  have hb := congrArg (fun l => List.getD l 0 0) go
  simp only [List.getD_cons_zero] at hb
  rw [Proof.Gcm.ctr32_getD _ _ _ (by simp)] at hb
  simp only [List.getD_cons_zero, Nat.repeat, BitVec.zero_xor] at hb
  rw [VG.Proof.AesGcm.X86.ctxH_eq, hb]
  simp only [Spec.Gcm.aes, hlen, Spec.Aes.rounds]
  exact BitVec.zero_xor

theorem init_correct (s : State) (hs : initX86.pre s) :
    ∃ t s', Exec isa (init vg.callees) s t s' ∧ abiPreserved s s' ∧ initX86.post s s' :=
  (VG.Proof.AesGcm.X86.init_pc (VG.Proof.AesGcm.X86.pubOf 4 s)).wp s s ⟨hs, rfl, rfl⟩

theorem init_ct : ConstantTime isa initX86.pre initX86.pub (init vg.callees) :=
  Pc.constantTime (VG.Proof.AesGcm.X86.pubOf 4) (fun _ _ _ _ h => VG.Proof.AesGcm.X86.pubOf_eq h) VG.Proof.AesGcm.X86.init_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.J0`. -/
section

/-!
# AES-GCM on x86: the pre-counter block (`j0`)

Untrusted: everything here is checked by Lean. `j0` writes `J₀` for the
`nO`-byte nonce at `dO` to the state: its words and `0x00000001` for a
12-byte nonce (`j012_pc`), and otherwise GHASH of the nonce padded with
zeros and the lengths block, with `absorb`, `flush` and `lens` on the
accumulator at the state's first block (`j0hash_pc`). `initState` then
zeroes the accumulator and writes the first counter block `inc₃₂(J₀)`
(`initState_pc`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (le4 store4)

theorem inc32_words (a b c d : BitVec 32) : inc32 (a ++ b ++ c ++ d) = a ++ b ++ c ++ (d + 1) := by
  have h₁ : (a ++ b ++ c ++ d).extractLsb' 32 96 = a ++ b ++ c := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    simp only [show ¬ (32 + i < 32) by omega, ite_false, show 32 + i - 32 = i by omega]
  have h₂ : (a ++ b ++ c ++ d).extractLsb' 0 32 = d := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp [hi]
  simp only [inc32, h₁, h₂]

theorem le4_one : le4 (BitVec.ofNat 32 0x01000000) = [0, 0, 0, 1] := by decide

/-- A block from the bytes of its four little-endian words. -/
theorem ofBytes_le4 (a b c d : BitVec 32) :
    ofBytes (le4 a ++ le4 b ++ le4 c ++ le4 d) = byteRev32 a ++ byteRev32 b ++ byteRev32 c ++ byteRev32 d := by
  have h := Cmac.le4_rev4 (byteRev32 a) (byteRev32 b) (byteRev32 c) (byteRev32 d)
  rw [Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32,
    Cmac.byteRev32_byteRev32] at h
  rw [h, Cmac.ofBytes_toBytes]

/-- The regions `j0` writes. -/
abbrev j0Frame (St W SP : BitVec 32) (K : Nat) : List Region :=
  [⟨w64 St, 80⟩, ⟨w64 W + BitVec.ofNat 64 96, 16⟩, wsR W, below SP K]

/-- Before `j0`: the `n`-byte nonce at `D`. -/
structure J0In (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  dO : slotv s.mem W dO = D
  nO : slotv s.mem W nO = BitVec.ofNat 32 n
  nl : slotv s.mem W nlO = BitVec.ofNat 32 n
  z : slotv s.mem W zO = 0
  nlt : n < 2 ^ 32
  data : DataOk St W SP K s D n

/-- `J₀` written, from `m₀`. -/
structure J0Mid (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  j0 : blockAt s.mem (w64 St) = Spec.Gcm.j0 (Hk m₀ Ctx) (bytesAt m₀ (w64 D) n)
  frame : Frame (VG.Proof.AesGcm.X86.j0Frame St W SP K) m₀ s.mem

/-- After `j0`: `J₀`, the accumulator zeroed and the first counter block. -/
structure J0Out (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  j0 : blockAt s.mem (w64 St) = Spec.Gcm.j0 (Hk m₀ Ctx) (bytesAt m₀ (w64 D) n)
  y : blockAt s.mem (w64 St + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (w64 St + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 (Hk m₀ Ctx) (bytesAt m₀ (w64 D) n))
  frame : Frame (VG.Proof.AesGcm.X86.j0Frame St W SP K) m₀ s.mem

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K)
include L

theorem ctx_j0Frame : ∀ r ∈ VG.Proof.AesGcm.X86.j0Frame St W SP K, (⟨w64 Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs.sub_left (Lay.ctxSub (by decide))
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

theorem kept_j0Frame : ∀ r ∈ VG.Proof.AesGcm.X86.j0Frame St W SP K, (keptR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

omit L in
theorem st_j0Frame {m m' : Mem} {d k : Nat} (h : Frame [⟨w64 St + BitVec.ofNat 64 d, k⟩] m m') (hk : d + k ≤ 80) :
    Frame (VG.Proof.AesGcm.X86.j0Frame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., by simpa using Lay.stSub (St := w64 St) hk⟩

/-- `J₀` of a 12-byte nonce, after `edi := D`. -/
theorem j012b_ok {D : BitVec 32} {s : State} (he : Env Ctx St W SP s) (hd : DataOk St W SP K s D 12)
    (hdi : s.gpr .edi = D) :
    ∃ s', runBlock isa [.mov .eax (.mem (at_ .edi 0)), .mov .ecx (.mem (at_ .edi 4)), .mov .edx (.mem (at_ .edi 8)),
        .store (at_ .esi 0) .eax, .store (at_ .esi 4) .ecx, .store (at_ .esi 8) .edx,
        .mov .eax (imm 0x01000000), .store (at_ .esi 12) .eax] s = some s' ∧
      s'.mem = store4 s.mem (w64 St) (s.mem.readW (w64 D) 32) (s.mem.readW (w64 D + BitVec.ofNat 64 4) 32)
        (s.mem.readW (w64 D + BitVec.ofNat 64 8) 32) (BitVec.ofNat 32 0x01000000) ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have r₀ := in_off hd.rd (show 0 + 4 ≤ 12 by decide) (by decide)
  have r₁ := in_off hd.rd (show 4 + 4 ≤ 12 by decide) (by decide)
  have r₂ := in_off hd.rd (show 8 + 4 ≤ 12 by decide) (by decide)
  have e₀ : w64 (D + BitVec.ofNat 32 0) = w64 D + BitVec.ofNat 64 0 := hd.ptr (by decide)
  have e₁ : w64 (D + BitVec.ofNat 32 4) = w64 D + BitVec.ofNat 64 4 := hd.ptr (by decide)
  have e₂ : w64 (D + BitVec.ofNat 32 8) = w64 D + BitVec.ofNat 64 8 := hd.ptr (by decide)
  refine ⟨_, by xrun [hdi, he.esi, e₀, e₁, e₂, r₀, r₁, r₂, L.aS, he.stIn], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setMem, mem_setReg, store4, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  · regs []
  · regs []
  · regs []
  all_goals rfl

theorem j012_pc {D : BitVec 32} :
    Pc (fun (m₀ : Mem) s => VG.Proof.AesGcm.X86.J0In Ctx St W SP K D 12 s ∧ s.mem = m₀) j012 (VG.Proof.AesGcm.X86.J0Mid Ctx St W SP K D 12 ·) := by
  refine Pc.seq (Q := fun m₀ s => (VG.Proof.AesGcm.X86.J0In Ctx St W SP K D 12 s ∧ s.mem = m₀) ∧ s.gpr .edi = D)
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  · have he := h.env
    have hd := h.dO
    refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn', hd], ⟨⟨?_, ?_, ?_, ?_, ?_, h.nlt, ?_⟩, ?_⟩, ?_⟩
    · exact he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems [])
    · mems []; exact h.dO
    · mems []; exact h.nO
    · mems []; exact h.nl
    · mems []; exact h.z
    · exact h.data.of_eq (by mems []) (by mems [])
    · mems []; exact hm
    · regs [hd]
  refine Pc.taint [.edi, .esi] (fun m₀ s ⟨⟨h, hm⟩, hdi⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2, h₂.2]
    · rw [h₁.1.1.env.esi, h₂.1.1.env.esi]) (by taint_decide)
  have he := h.env
  obtain ⟨s', run, m', bp, si, sp, rd, wr⟩ := VG.Proof.AesGcm.X86.j012b_ok L he h.data hdi
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f : Frame [⟨w64 St + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem := by
    rw [m']; simpa using Cmac.frame_store4 (m := s.mem) (w64 St) _ _ _ _
  refine ⟨he.keep bp si sp rd wr (slot_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm),
    ?_, by rw [← hm]; exact VG.Proof.AesGcm.X86.st_j0Frame f (by decide)⟩
  · have hH : Hk s.mem Ctx = Hk m₀ Ctx := by rw [hm]
    have hb : bytesAt s.mem (w64 D) 12 = bytesAt s.mem (w64 D) 4 ++ bytesAt s.mem (w64 D + BitVec.ofNat 64 4) 4 ++
        bytesAt s.mem (w64 D + BitVec.ofNat 64 8) 4 := by
      rw [show (12 : Nat) = 4 + 8 from rfl, bytesAt_add, show (8 : Nat) = 4 + 4 from rfl, bytesAt_add,
        add_ofNat_assoc, List.append_assoc]
    rw [← hm, Proof.Gcm.j0_12 _ (length_bytesAt _ _ _), blockAt, m', Cmac.bytesAt_store4, Cmac.le4_readW,
      Cmac.le4_readW, Cmac.le4_readW, VG.Proof.AesGcm.X86.le4_one, hb]

theorem initState_ok {D : BitVec 32} {n : Nat} {m₀ : Mem} {s : State} (h : VG.Proof.AesGcm.X86.J0Mid Ctx St W SP K D n m₀ s) :
    WP isa (.block initState) s (VG.Proof.AesGcm.X86.J0Out Ctx St W SP K D n m₀) := by
  have he := h.env
  have e0 : w64 St + BitVec.ofNat 64 0 = w64 St := BitVec.add_zero _
  have i0 : InRegions s.wr (w64 St) 4 := by have := he.stIn (d := 0) (n := 4) (by decide); rwa [e0] at this
  have i0' : InRegions (s.rd ++ s.wr) (w64 St) 4 := by
    have := he.stIn' (d := 0) (n := 4) (by decide); rwa [e0] at this
  generalize hw0 : s.mem.readW (w64 St) 32 = w0
  generalize hw1 : s.mem.readW (w64 St + BitVec.ofNat 64 4) 32 = w1
  generalize hw2 : s.mem.readW (w64 St + BitVec.ofNat 64 8) 32 = w2
  generalize hw3 : s.mem.readW (w64 St + BitVec.ofNat 64 12) 32 = w3
  obtain ⟨s', run, m', bp, si, sp, rd, wr⟩ : ∃ s', runBlock isa initState s = some s' ∧
      s'.mem = store4 (store4 s.mem (w64 St + BitVec.ofNat 64 48) w0 w1 w2 (byteRev32 (byteRev32 w3 + 1)))
        (w64 St + BitVec.ofNat 64 16) 0 0 0 0 ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
    refine ⟨_, by xrun [initState, he.esi, L.aS, e0, i0, i0', he.stIn, he.stIn', readW_writeW_off, hw0, hw1, hw2,
      hw3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setMem, mem_setReg, mem_arithFlags, store4, add_ofNat_assoc, Nat.reduceAdd, bswap_eq]
      rfl
    · regs []
    · regs []
    · regs []
    all_goals rfl
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f₄ := Cmac.frame_store4 (m := s.mem) (w64 St + BitVec.ofNat 64 48) w0 w1 w2 (byteRev32 (byteRev32 w3 + 1))
  have fz := Cmac.frame_store4 (m := store4 s.mem (w64 St + BitVec.ofNat 64 48) w0 w1 w2
    (byteRev32 (byteRev32 w3 + 1))) (w64 St + BitVec.ofNat 64 16) 0 0 0 0
  rw [← m'] at fz
  have ff : Frame (VG.Proof.AesGcm.X86.j0Frame St W SP K) s.mem s'.mem :=
    (VG.Proof.AesGcm.X86.st_j0Frame f₄ (by decide)).trans (VG.Proof.AesGcm.X86.st_j0Frame fz (by decide))
  have d16 : ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 16, 16⟩ : Region)], (⟨w64 St + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  have d48 : ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region)], (⟨w64 St + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  have hJ : blockAt s'.mem (w64 St) = blockAt s.mem (w64 St) := by
    have := (blockAt_frame fz d16).trans (blockAt_frame f₄ d48)
    rwa [e0] at this
  refine ⟨he.keep bp si sp rd wr (slot_frame ff fun r hr =>
      (VG.Proof.AesGcm.X86.kept_j0Frame L r hr).sub_left (Offset.sub _ (by decide) (by decide))), by rw [hJ, h.j0], ?_, ?_,
    h.frame.trans ff⟩
  · rw [blockAt, m', show store4 _ (w64 St + BitVec.ofNat 64 16) 0 0 0 0 =
      Cmac.zero4 (store4 s.mem (w64 St + BitVec.ofNat 64 48) w0 w1 w2 (byteRev32 (byteRev32 w3 + 1)))
        (w64 St + BitVec.ofNat 64 16) from rfl, zero4_bytes', ofBytes_zeros]
  · rw [blockAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inr (by decide)) (by decide) (by decide)),
      blockAt, Cmac.bytesAt_store4, VG.Proof.AesGcm.X86.ofBytes_le4, Cmac.byteRev32_byteRev32, ← h.j0, blockAt, Cmac.ofBytes_rev4,
      hw0, hw1, hw2, hw3, VG.Proof.AesGcm.X86.inc32_words]

omit L in
theorem abs_j0Frame {m m' : Mem} (h : Frame (absFrame St W SP K 0) m m') : Frame (VG.Proof.AesGcm.X86.j0Frame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using Lay.stSub (St := w64 St) (d := 0) (n := 16) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., by simpa using Lay.stSub (St := w64 St) (d := 32) (n := 16) (by decide)⟩
    · exact ⟨wsR W, by simp, fun _ h => h⟩
    · exact ⟨below SP K, by simp, fun _ h => h⟩

omit L in
theorem t_j0Frame {m m' : Mem} (h : Frame (tFrame St W SP K 0) m m') : Frame (VG.Proof.AesGcm.X86.j0Frame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using Lay.stSub (St := w64 St) (d := 0) (n := 16) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨wsR W, by simp, fun _ h => h⟩
    · exact ⟨below SP K, by simp, fun _ h => h⟩

omit L in
theorem pslot_j0Frame {m m' : Mem} (h : Frame [pslotR W] m m') : Frame (VG.Proof.AesGcm.X86.j0Frame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wsR W, by simp, pslot_ws W⟩

/-- The kept slots `j0hash` reads. -/
abbrev J0Slots (W : BitVec 32) (n : Nat) (m : Mem) : Prop :=
  slotv m W nlO = BitVec.ofNat 32 n ∧ slotv m W zO = 0

/-- Part of the way through `j0hash`: `x` absorbed into the accumulator at the
state's first block. -/
structure J0H (Ctx St W SP : BitVec 32) (K : Nat) (n : Nat) (x : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  sl : VG.Proof.AesGcm.X86.J0Slots W n s.mem
  abs : Absorbed s.mem (w64 St + BitVec.ofNat 64 0) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx) x
  hk : Hk s.mem Ctx = Hk m₀ Ctx
  frame : Frame (VG.Proof.AesGcm.X86.j0Frame St W SP K) m₀ s.mem

theorem j0z_ok {D : BitVec 32} {n : Nat} {m₀ : Mem} {s : State} (h : VG.Proof.AesGcm.X86.J0In Ctx St W SP K D n s) (hm : s.mem = m₀) :
    WP isa (.block [.mov .eax (imm 0), .store (at_ .esi 0) .eax, .store (at_ .esi 4) .eax, .store (at_ .esi 8) .eax,
      .store (at_ .esi 12) .eax, .store (at_ .ebp bO) .eax]) s fun s' =>
      AbsIn Ctx St W SP K D n 0 s' ∧ VG.Proof.AesGcm.X86.J0H Ctx St W SP K n [] m₀ s' ∧ bytesAt s'.mem (w64 D) n = bytesAt m₀ (w64 D) n := by
  have he := h.env
  subst hm
  have hz : Cmac.zero4 s.mem (w64 St + BitVec.ofNat 64 0) = (((s.mem.writeW (w64 St + BitVec.ofNat 64 0)
      (BitVec.ofNat 32 0)).writeW (w64 St + BitVec.ofNat 64 4) (BitVec.ofNat 32 0)).writeW
      (w64 St + BitVec.ofNat 64 8) (BitVec.ofNat 32 0)).writeW (w64 St + BitVec.ofNat 64 12) (BitVec.ofNat 32 0) := by
    simp only [Cmac.zero4, store4, add_ofNat_assoc]; rfl
  refine WP.of_runBlock ⟨_, by xrun [he.esi, he.ebp, L.aS, L.aW, he.stIn, he.wIn], ?_⟩
  simp only [mem_setMem, mem_setReg, gpr_setMem, rd_setMem, wr_setMem, rd_setReg, wr_setReg, ← hz]
  generalize hZ : Cmac.zero4 s.mem (w64 St + BitVec.ofNat 64 0) = Z at *
  have fz : Frame [⟨w64 St + BitVec.ofNat 64 0, 16⟩] s.mem Z := by rw [← hZ]; exact Cmac.frame_store4 _ _ _ _ _
  have fb : Frame [⟨w64 W + BitVec.ofNat 64 bO, 4⟩] Z (Z.writeW (w64 W + BitVec.ofNat 64 bO) (BitVec.ofNat 32 0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fb' : Frame [pslotR W] Z (Z.writeW (w64 W + BitVec.ofNat 64 bO) (BitVec.ofNat 32 0)) :=
    fb.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hf : Frame (VG.Proof.AesGcm.X86.j0Frame St W SP K) s.mem (Z.writeW (w64 W + BitVec.ofNat 64 bO) (BitVec.ofNat 32 0)) :=
    (VG.Proof.AesGcm.X86.st_j0Frame fz (by decide)).trans (VG.Proof.AesGcm.X86.pslot_j0Frame fb')
  have sl : ∀ {o}, 96 ≤ o → o + 4 ≤ 2560 → (o + 4 ≤ bO ∨ bO + 4 ≤ o) →
      slotv (Z.writeW (w64 W + BitVec.ofNat 64 bO) (BitVec.ofNat 32 0)) W o = slotv s.mem W o := fun h₁ h₂ h₃ => by
    rw [slotv_eq, slot_frame fb fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w h₃ (by omega) (by decide)]
    exact slot_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨h₁, h₂⟩)).symm
  have dZ : ∀ r ∈ VG.Proof.AesGcm.X86.j0Frame St W SP K, (⟨w64 D, n⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.data.st
    · exact h.data.w.sub_right (Lay.wSub (by decide))
    · exact h.data.w.sub_right (Lay.wSub (by decide))
    · exact h.data.stk.symm
  have hD := bytesAt_frame hf dZ (by have := h.data.fit; omega)
  have he' : Env Ctx St W SP (setMem ((s.setReg .eax (BitVec.ofNat 32 0)))
      (Z.writeW (w64 W + BitVec.ofNat 64 bO) (BitVec.ofNat 32 0))) :=
    he.keep (by regs []) (by regs []) (by regs []) rfl rfl (by
      simp only [mem_setMem]; exact slot_frame hf fun r hr =>
        (VG.Proof.AesGcm.X86.kept_j0Frame L r hr).sub_left (Offset.sub _ (by decide) (by decide)))
  refine ⟨⟨he', ?_, ?_, ?_, by decide, h.nlt, h.data.of_eq rfl rfl⟩, ⟨he', ⟨?_, ?_⟩, ?_, ?_, hf⟩, hD⟩
  · rw [mem_setMem, sl (by decide) (by decide) (by decide)]; exact h.dO
  · rw [mem_setMem, sl (by decide) (by decide) (by decide)]; exact h.nO
  · simp only [mem_setMem, slotv_eq, Mem.readW_writeW_self32]
  · rw [mem_setMem, sl (by decide) (by decide) (by decide)]; exact h.nl
  · rw [mem_setMem, sl (by decide) (by decide) (by decide)]; exact h.z
  · refine Proof.Gcm.absorbed_nil _ ?_
    rw [mem_setMem, blockAt_frame fb fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
      blockAt, ← hZ, zero4_bytes', ofBytes_zeros]
  · exact blockAt_frame hf (VG.Proof.AesGcm.X86.ctx_j0Frame L)

theorem j0a_pc {D : BitVec 32} {n : Nat} (hnlt : n < 2 ^ 32) :
    Pc (fun (m₀ : Mem) s => AbsIn Ctx St W SP K D n 0 s ∧ VG.Proof.AesGcm.X86.J0H Ctx St W SP K n [] m₀ s ∧
        bytesAt s.mem (w64 D) n = bytesAt m₀ (w64 D) n) (absorb vg.callees 0)
      (fun m₀ s => VG.Proof.AesGcm.X86.J0H Ctx St W SP K n (bytesAt m₀ (w64 D) n) m₀ s) := by
  refine Pc.mono (Pc.lift (absorb_pc L (yo := 0) (.inl rfl) (by decide) hnlt) (fun _ s => s.mem)
    fun m₀ s h => ⟨h.1, rfl⟩) (fun _ _ h => h) fun m₀ s' ⟨s, ⟨_, hh, hD⟩, ho, _, _⟩ => ?_
  have hk := hk_frame L (.inl rfl) ho.frame
  refine ⟨ho.env, ⟨?_, ?_⟩, ?_, by rw [hk, hh.hk], hh.frame.trans (VG.Proof.AesGcm.X86.abs_j0Frame ho.frame)⟩
  · rw [slotv_eq, slot_frame ho.frame (slot_absFrame L (.inl rfl) (by decide) (by decide))]; exact hh.sl.1
  · rw [slotv_eq, slot_frame ho.frame (slot_absFrame L (.inl rfl) (by decide) (by decide))]; exact hh.sl.2
  · have := ho.abs [] rfl (by rw [hh.hk]; exact hh.abs)
    rwa [List.nil_append, hD, hh.hk] at this

theorem J0H.wslot {n : Nat} {x : List Byte} {m₀ : Mem} {s s' : State} (h : VG.Proof.AesGcm.X86.J0H Ctx St W SP K n x m₀ s) {o : Nat}
    (ho₁ : 240 ≤ o) (ho₂ : o + 4 ≤ 2560) {v : BitVec 32}
    (hm : s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 o) v)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86.J0H Ctx St W SP K n x m₀ s' := by
  have fb : Frame [⟨w64 W + BitVec.ofNat 64 o, 4⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hf : Frame (VG.Proof.AesGcm.X86.j0Frame St W SP K) s.mem s'.mem := fb.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wsR W, by simp, Offset.sub _ (by omega) (by omega)⟩
  have dS : ∀ {a k : Nat}, a + k ≤ 80 → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region)],
      (⟨w64 St + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r := fun hak r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hak (.inr ⟨by omega, ho₂⟩)
  have sK : ∀ {q}, 128 ≤ q → q + 4 ≤ 240 → slotv s'.mem W q = slotv s.mem W q := fun h₁ h₂ =>
    slot_frame fb fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) ho₂
  have hk : Hk s'.mem Ctx = Hk s.mem Ctx := blockAt_frame fb fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by omega)
  refine ⟨h.env.keep hbp hsi hsp hrd hwr (sK (by decide) (by decide)),
    ⟨by rw [sK (by decide) (by decide)]; exact h.sl.1, by rw [sK (by decide) (by decide)]; exact h.sl.2⟩,
    h.abs.congr (blockAt_frame fb (dS (by decide))) (bytesAt_frame fb (dS (by omega)) (by omega)),
    by rw [hk, h.hk], h.frame.trans hf⟩

theorem j0b_pc {n : Nat} (hnlt : n < 2 ^ 32) {x : Mem → List Byte} :
    Pc (fun (m₀ : Mem) s => VG.Proof.AesGcm.X86.J0H Ctx St W SP K n (x m₀) m₀ s)
      (.block [.mov .eax (slot nlO), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax])
      (fun m₀ s => VG.Proof.AesGcm.X86.J0H Ctx St W SP K n (x m₀) m₀ s ∧ slotv s.mem W bO = BitVec.ofNat 32 (n % 16)) := by
  refine Pc.taint [.ebp] (fun m₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  have he := h.env
  have hn := h.sl.1
  have hand := and15 (BitVec.ofNat 32 n)
  rw [toNat_ofNat32 hnlt] at hand
  refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn, he.wIn', hn], ?_, ?_⟩
  · exact h.wslot L (o := bO) (v := BitVec.ofNat 32 n &&& BitVec.ofNat 32 15) (by decide) (by decide) (by mems [])
      (by regs []) (by regs []) (by regs []) (by mems []) (by mems [])
  · mems [slotv_eq, hand]

theorem j0c_pc {D : BitVec 32} {n : Nat} :
    Pc (fun (m₀ : Mem) s => VG.Proof.AesGcm.X86.J0H Ctx St W SP K n (bytesAt m₀ (w64 D) n) m₀ s ∧
        slotv s.mem W bO = BitVec.ofNat 32 (n % 16)) (flush vg.callees 0)
      (fun m₀ s => VG.Proof.AesGcm.X86.J0H Ctx St W SP K n (bytesAt m₀ (w64 D) n ++ zeros (padLen n)) m₀ s) := by
  refine Pc.mono (Pc.lift (flush_pc L (yo := 0) (.inl rfl) (b := n % 16) (Nat.mod_lt _ (by decide)))
    (fun _ s => s.mem) fun m₀ s h => ⟨⟨h.1.env, h.2⟩, rfl⟩) (fun _ _ h => h) fun m₀ s' ⟨s, ⟨hh, _⟩, ho, _, _⟩ => ?_
  have hk : Hk s'.mem Ctx = Hk s.mem Ctx := blockAt_frame ho.frame (ctx_tFrame L (.inl rfl))
  refine ⟨ho.env, ⟨?_, ?_⟩, ?_, by rw [hk, hh.hk], hh.frame.trans (VG.Proof.AesGcm.X86.t_j0Frame ho.frame)⟩
  · rw [slotv_eq, slot_frame ho.frame (slot_tFrame L (.inl rfl) (by decide) (by decide))]; exact hh.sl.1
  · rw [slotv_eq, slot_frame ho.frame (slot_tFrame L (.inl rfl) (by decide) (by decide))]; exact hh.sl.2
  · have := ho.abs (bytesAt m₀ (w64 D) n) (by rw [length_bytesAt]) (by rw [hh.hk]; exact hh.abs)
    rwa [length_bytesAt, hh.hk] at this

theorem j0d_pc {D : BitVec 32} {n : Nat} (hnlt : n < 2 ^ 32) (hn : n ≠ 12) :
    Pc (fun (m₀ : Mem) s => VG.Proof.AesGcm.X86.J0H Ctx St W SP K n (bytesAt m₀ (w64 D) n ++ zeros (padLen n)) m₀ s)
      (lens vg.callees 0 zO zO nlO zO) (VG.Proof.AesGcm.X86.J0Mid Ctx St W SP K D n ·) := by
  refine Pc.mono (Pc.lift (lens_pc L (yo := 0) (al := zO) (ah := zO) (tl := nlO) (th := zO)
    (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) (alo := 0) (ahi := 0) (tlo := BitVec.ofNat 32 n) (thi := 0))
    (fun _ s => s.mem) fun m₀ s h => ⟨⟨h.env, h.sl.2, h.sl.2, h.sl.1, h.sl.2⟩, rfl⟩) (fun _ _ h => h)
    fun m₀ s' ⟨s, hh, ho, _, _⟩ => ?_
  refine ⟨ho.env, ?_, hh.frame.trans (VG.Proof.AesGcm.X86.t_j0Frame ho.frame)⟩
  have hl : (bytesAt m₀ (w64 D) n ++ zeros (padLen n)).length % 16 = 0 := by
    rw [List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod n
  have ha := hh.abs.1
  rw [Proof.Gcm.whole_of_mod hl, List.take_of_length_le (Nat.le_refl _)] at ha
  have hv : val64 (BitVec.ofNat 32 n) 0 = n := by simp [val64, toNat_ofNat32 hnlt]
  have hz : val64 0 0 = 0 := rfl
  have := ho.out
  rw [ha, hh.hk, hv, hz] at this
  have e0 : w64 St + BitVec.ofNat 64 0 = w64 St := BitVec.add_zero _
  rw [e0] at this
  rw [this, Proof.Gcm.j0_eq _ (by rw [length_bytesAt]; exact hn), length_bytesAt]

theorem j0hash_pc {D : BitVec 32} {n : Nat} (hnlt : n < 2 ^ 32) (hn : n ≠ 12) :
    Pc (fun (m₀ : Mem) s => VG.Proof.AesGcm.X86.J0In Ctx St W SP K D n s ∧ s.mem = m₀) (j0hash vg.callees) (VG.Proof.AesGcm.X86.J0Mid Ctx St W SP K D n ·) := by
  refine Pc.seq (Pc.taint [.ebp, .esi] (fun m₀ s ⟨h, hm⟩ => VG.Proof.AesGcm.X86.j0z_ok L h hm) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.env.ebp, h₂.1.env.ebp]
    · rw [h₁.1.env.esi, h₂.1.env.esi]) (by taint_decide)) ?_
  exact Pc.seq (VG.Proof.AesGcm.X86.j0a_pc L hnlt) (Pc.seq (VG.Proof.AesGcm.X86.j0b_pc L hnlt (x := fun m₀ => bytesAt m₀ (w64 D) n))
    (Pc.seq (VG.Proof.AesGcm.X86.j0c_pc L) (VG.Proof.AesGcm.X86.j0d_pc L hnlt hn)))

theorem j0_pc {D : BitVec 32} {n : Nat} :
    Pc (fun (m₀ : Mem) s => VG.Proof.AesGcm.X86.J0In Ctx St W SP K D n s ∧ s.mem = m₀) (j0 vg.callees) (VG.Proof.AesGcm.X86.J0Out Ctx St W SP K D n ·) := by
  refine Pc.seq (Q := fun m₀ s => (VG.Proof.AesGcm.X86.J0In Ctx St W SP K D n s ∧ s.mem = m₀) ∧ s.zf = some (decide (n = 12)))
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  · have he := h.env
    have hl := h.nl
    refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn', hl], ⟨⟨?_, ?_, ?_, ?_, ?_, h.nlt, ?_⟩, ?_⟩, ?_⟩
    · exact he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems [])
    · mems []; exact h.dO
    · mems []; exact h.nO
    · mems []; exact h.nl
    · mems []; exact h.z
    · exact h.data.of_eq (by mems []) (by mems [])
    · mems []; exact hm
    · mems []; rw [sub_beq32 h.nlt (by decide)]
  refine Pc.seq (Q := fun m₀ s => VG.Proof.AesGcm.X86.J0Mid Ctx St W SP K D n m₀ s) ?_
    (Pc.taint [.esi] (fun m₀ s h => VG.Proof.AesGcm.X86.initState_ok L h) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.esi, h₂.env.esi]) (by taint_decide))
  refine Pc.ite (decide (n = 12)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact Pc.mono (VG.Proof.AesGcm.X86.j012_pc L) (fun _ _ h => h.1) fun _ _ h => h
  · have h12 : n ≠ 12 := by simpa using hf
    by_cases hlt : n < 2 ^ 32
    · exact Pc.mono (VG.Proof.AesGcm.X86.j0hash_pc L hlt h12) (fun _ _ h => h.1) fun _ _ h => h
    · exact Pc.vacuous fun _ _ h => hlt h.1.1.nlt

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.OneEntry`. -/
section

/-!
# AES-GCM on x86: the entry of `seal` and `open`

Untrusted: everything here is checked by Lean. The precondition of `seal`
and `open` (`OP`), the layout it gives in terms of the public data (`OL`),
what holds of the working space from the entry to the exit (`OEnv`, which
the pieces keep as they write only within `D :: oF p`), and the entry
(`oneEntry_pc`). The state is at `W + 16`. `W` is the last argument, which
the pieces find at 8 in the public data (`pubSw`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph)

/-- The state of `seal` and `open`, at `W + 16`. -/
abbrev stOf (W : BitVec 32) : BitVec 32 := W + BitVec.ofNat 32 16

/-- What the precondition of `seal` and `open` (with `nA` arguments, `W` the
last, `w`) gives. -/
structure OP (nA w : Nat) (s : State) : Prop where
  cR : Covers [⟨w64 (arg s 0), 256⟩] (s.rd ++ s.wr)
  nR : Covers [⟨w64 (arg s 2), (arg s 3).toNat⟩] (s.rd ++ s.wr)
  aR : Covers [⟨w64 (arg s 4), (arg s 5).toNat⟩] (s.rd ++ s.wr)
  dW : Covers [⟨w64 (arg s 6), (arg s 7).toNat⟩] s.wr
  wW : Covers [⟨w64 (arg s w), 2560⟩] s.wr
  argR : Covers [⟨argAddr s 0, 4 * nA⟩] (s.rd ++ s.wr)
  c_d : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s 6), (arg s 7).toNat⟩
  c_w : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  n_d : (⟨w64 (arg s 2), (arg s 3).toNat⟩ : Region).Disjoint ⟨w64 (arg s 6), (arg s 7).toNat⟩
  n_w : (⟨w64 (arg s 2), (arg s 3).toNat⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  a_d : (⟨w64 (arg s 4), (arg s 5).toNat⟩ : Region).Disjoint ⟨w64 (arg s 6), (arg s 7).toNat⟩
  a_w : (⟨w64 (arg s 4), (arg s 5).toNat⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  d_w : (⟨w64 (arg s 6), (arg s 7).toNat⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  d_a : (⟨w64 (arg s 6), (arg s 7).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 4 * nA⟩
  w_a : (⟨w64 (arg s w), 2560⟩ : Region).Disjoint ⟨argAddr s 0, 4 * nA⟩
  r_d : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 6), (arg s 7).toNat⟩
  r_w : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  k_c : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 0), 256⟩
  k_n : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 2), (arg s 3).toNat⟩
  k_a : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 4), (arg s 5).toNat⟩
  k_d : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 6), (arg s 7).toNat⟩
  k_w : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s w), 2560⟩
  fc : (arg s 0).toNat + 256 ≤ 2 ^ 32
  fn : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  fa : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  fd : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  fw : (arg s w).toNat + 2560 ≤ 2 ^ 32
  sp : 28 ≤ (s.gpr .esp).toNat
  fg : (s.gpr .esp).toNat + 4 + 4 * nA ≤ 2 ^ 32
  rounds : VG.Proof.AesGcm.X86.roundsOk s 1

theorem op_of_seal {s : State} (h : VG.Proof.AesGcm.X86.sealPre s) : VG.Proof.AesGcm.X86.OP 10 9 s := by
  simp only [VG.Proof.AesGcm.X86.sealPre] at h
  obtain ⟨hrd, hwr, c_d, -, c_w, -, n_d, -, n_w, -, a_d, -, a_w, -, -, d_w, d_a, -, -, w_a, -, -, -, r_d, -, r_w, -,
    k_c, k_n, k_a, k_d, -, k_w, -, fc, fn, fa, fd, -, fw, sp, fg, hR⟩ := h
  rw [VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.below_eq sp] at k_c k_n k_a k_d k_w
  exact ⟨by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp),
    by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp),
    by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), c_d, c_w, n_d,
    n_w, a_d, a_w, d_w, d_a, w_a, r_d, r_w, k_c, k_n, k_a, k_d, k_w, fc, fn, fa, fd, fw, sp, by omega, hR⟩

/-- The tag `seal` writes. -/
theorem sealPre_tag {s : State} (h : VG.Proof.AesGcm.X86.sealPre s) : Covers [⟨w64 (arg s 8), 16⟩] s.wr ∧
    (arg s 8).toNat + 16 ≤ 2 ^ 32 ∧ (⟨w64 (arg s 8), 16⟩ : Region).Disjoint ⟨w64 (arg s 9), 2560⟩ ∧
    (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 8), 16⟩ ∧
    (⟨w64 (arg s 6), (arg s 7).toNat⟩ : Region).Disjoint ⟨w64 (arg s 8), 16⟩ := by
  simp only [VG.Proof.AesGcm.X86.sealPre] at h
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, -, -, d_t, -, -, t_w, -, -, -, -, -, -, r_t, -, -, -, -, -, -, -, -, -,
    -, -, -, -, ft, -, -, -, -⟩ := h
  exact ⟨by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), ft, t_w, r_t, d_t⟩

theorem op_of_open {s : State} (h : VG.Proof.AesGcm.X86.openPre s) : VG.Proof.AesGcm.X86.OP 11 10 s := by
  simp only [VG.Proof.AesGcm.X86.openPre] at h
  obtain ⟨hrd, hwr, c_d, c_w, -, n_d, n_w, -, a_d, a_w, -, -, d_w, d_a, -, -, w_a, -, -, -, r_d, -, r_w, -, k_c, k_n,
    k_a, k_d, -, k_w, -, fc, fn, fa, fd, -, fw, sp, fg, hR⟩ := h
  rw [VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.below_eq sp] at k_c k_n k_a k_d k_w
  exact ⟨by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp),
    by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp),
    by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), c_d, c_w, n_d,
    n_w, a_d, a_w, d_w, d_a, w_a, r_d, r_w, k_c, k_n, k_a, k_d, k_w, fc, fn, fa, fd, fw, sp, by omega, hR⟩

/-- The tag `open` reads. -/
theorem openPre_tag {s : State} (h : VG.Proof.AesGcm.X86.openPre s) :
    Covers [⟨w64 (arg s 8), (arg s 9).toNat⟩] (s.rd ++ s.wr) ∧ (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32 ∧
      (⟨w64 (arg s 8), (arg s 9).toNat⟩ : Region).Disjoint ⟨w64 (arg s 10), 2560⟩ ∧
      (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 8), (arg s 9).toNat⟩ := by
  simp only [VG.Proof.AesGcm.X86.openPre] at h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, t_w, -, -, -, -, -, -, -, -, -, -, -, -, -, k_t, -, -, -, -, -,
    -, ft, -, sp, -, -⟩ := h
  rw [VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.below_eq sp] at k_t
  exact ⟨by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), ft, t_w, k_t⟩

theorem stOf_w64 {W : BitVec 32} (hw : W.toNat + 2560 ≤ 2 ^ 32) : w64 (VG.Proof.AesGcm.X86.stOf W) = w64 W + BitVec.ofNat 64 16 :=
  w64_add (by omega)

/-- The layout of `seal` and `open`, for the public data `p`. -/
structure OL (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  L : Lay (p.2 0) (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28
  c_d : (⟨w64 (p.2 0), 256⟩ : Region).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  n_d : (⟨w64 (p.2 2), (p.2 3).toNat⟩ : Region).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  n_w : (⟨w64 (p.2 2), (p.2 3).toNat⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩
  a_d : (⟨w64 (p.2 4), (p.2 5).toNat⟩ : Region).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  a_w : (⟨w64 (p.2 4), (p.2 5).toNat⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩
  d_w : (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩
  r_d : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩
  k_n : (below p.1 28).Disjoint ⟨w64 (p.2 2), (p.2 3).toNat⟩
  k_a : (below p.1 28).Disjoint ⟨w64 (p.2 4), (p.2 5).toNat⟩
  k_d : (below p.1 28).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  fn : (p.2 2).toNat + (p.2 3).toNat ≤ 2 ^ 32
  fa : (p.2 4).toNat + (p.2 5).toNat ≤ 2 ^ 32
  fd : (p.2 6).toNat + (p.2 7).toNat ≤ 2 ^ 32
  rounds : (p.2 1).toNat = 10 ∨ (p.2 1).toNat = 12 ∨ (p.2 1).toNat = 14

theorem OP.ol {nA w : Nat} (hw : nA = w + 1) (h9 : 9 ≤ w) {s : State} (h : VG.Proof.AesGcm.X86.OP nA w s)
    {p : BitVec 32 × (Nat → BitVec 32)} (hp : VG.Proof.AesGcm.X86.pubSw nA 8 s = p) : VG.Proof.AesGcm.X86.OL p := by
  have a : ∀ i, i < 8 → arg s i = p.2 i := fun i hi => VG.Proof.AesGcm.X86.pubSw_arg hp (by omega) (by omega) (by omega)
  have aW : arg s w = p.2 8 := VG.Proof.AesGcm.X86.pubSw_W hp (by omega) hw
  have esp : s.gpr .esp = p.1 := VG.Proof.AesGcm.X86.pubSw_esp hp
  obtain ⟨-, -, -, -, -, -, c_d, c_w, n_d, n_w, a_d, a_w, d_w, -, -, r_d, r_w, k_c, k_n, k_a, k_d, k_w, fc, fn, fa,
    fd, fw, sp, -, hR⟩ := h
  have e := fun i hi => a i hi
  simp only [e 0 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
    e 6 (by omega), e 7 (by omega), aW, esp] at c_d c_w n_d n_w a_d a_w d_w r_d r_w k_c k_n
  simp only [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
    e 6 (by omega), e 7 (by omega), aW, esp, VG.Proof.AesGcm.X86.roundsOk] at k_a k_d k_w fc fn fa fd fw sp hR
  have hs := VG.Proof.AesGcm.X86.stOf_w64 fw
  have sw : (⟨w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)), 80⟩ : Region).Sub ⟨w64 (p.2 8), 2560⟩ := by
    rw [hs]; exact Lay.wSub (by decide)
  refine ⟨⟨fc, by rw [toNat_add32 (by omega)]; omega, fw, by decide, by decide, sp,
    c_w.sub_right sw, c_w, ?_, ?_, k_c, k_w.sub_right sw, k_w⟩, c_d, n_d, n_w, a_d, a_w, d_w,
    r_d, r_w, k_n, k_a, k_d, fn, fa, fd, hR⟩
  · rw [hs]
    have := Lay.w_w (W := p.2 8) (a := 16) (n := 80) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  · rw [hs]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)

/-- The regions of `W` and the stack the pieces write (but the tag at `W`). -/
abbrev oF (p : BitVec 32 × (Nat → BitVec 32)) : List Region :=
  [⟨w64 (p.2 8) + BitVec.ofNat 64 16, 112⟩, ⟨w64 (p.2 8) + BitVec.ofNat 64 auxO, 4⟩, ⟨w64 (p.2 8) + BitVec.ofNat 64 rO, 16⟩, wsR (p.2 8),
    below p.1 28]

/-- Those, the data and the first block of `W`: what `OEnv` survives. -/
abbrev oFF (p : BitVec 32 × (Nat → BitVec 32)) : List Region :=
  ⟨w64 (p.2 8), 16⟩ :: ⟨w64 (p.2 6), (p.2 7).toNat⟩ :: VG.Proof.AesGcm.X86.oF p

/-- What holds from the entry of `seal` or `open` to the exit. -/
structure OEnv (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  env : Env (p.2 0) (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 s
  rounds : RoundsAt s.mem (p.2 8) (p.2 1).toNat
  aadO : slotv s.mem (p.2 8) aadO = p.2 4
  alO : slotv s.mem (p.2 8) alO = p.2 5
  dataO : slotv s.mem (p.2 8) dataO = p.2 6
  lenO : slotv s.mem (p.2 8) lenO = p.2 7
  zO : slotv s.mem (p.2 8) zO = 0
  nlO : slotv s.mem (p.2 8) nlO = p.2 3
  tp : slotv s.mem (p.2 8) tpO = arg s₀ 8
  saved : SavedAt s.mem (p.2 8) s₀
  ret : s.mem.readW (w64 p.1) 32 = s₀.mem.readW (w64 p.1) 32
  ciph : ciphOf s.mem (p.2 0) (p.2 1).toNat = ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat
  hk : Hk s.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0))
  aad : bytesAt s.mem (w64 (p.2 4)) (p.2 5).toNat = bytesAt s₀.mem (w64 (p.2 4)) (p.2 5).toNat
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  nIn : Covers [⟨w64 (p.2 2), (p.2 3).toNat⟩] (s.rd ++ s.wr)
  aIn : Covers [⟨w64 (p.2 4), (p.2 5).toNat⟩] (s.rd ++ s.wr)
  dIn : Covers [⟨w64 (p.2 6), (p.2 7).toNat⟩] s.wr

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : VG.Proof.AesGcm.X86.OL p)
include G

/-- A part of the kept values, outside what the pieces write. -/
theorem slot_oF {o n : Nat} (h₁ : 128 ≤ o)
    (h₂ : o + n ≤ auxO ∨ (auxO + 4 ≤ o ∧ o + n ≤ rO) ∨ (rO + 16 ≤ o ∧ o + n ≤ 240)) :
    ∀ r ∈ VG.Proof.AesGcm.X86.oFF p, (⟨w64 (p.2 8) + BitVec.ofNat 64 o, n⟩ : Region).Disjoint r := by
  simp only [auxO, rO] at h₂
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := Lay.w_w (W := p.2 8) (a := o) (n := n) (d := 0) (k := 16) (.inr (by omega)) (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  · exact (G.d_w.sub_right (Lay.wSub (by omega))).symm
  · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (by simp only [auxO]; omega) (by omega) (by decide)
  · exact Lay.w_w (by simp only [rO]; omega) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (G.L.stk_w (by omega)).symm

/-- The context, outside what the pieces write. -/
theorem ctx_oF : ∀ r ∈ VG.Proof.AesGcm.X86.oFF p, (⟨w64 (p.2 0), 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact G.L.cw.sub_right (Region.sub_prefix (by decide))
  · exact G.c_d
  · exact G.L.cw.sub_right (Lay.wSub (by decide))
  · exact G.L.cw.sub_right (Lay.wSub (by decide))
  · exact G.L.cw.sub_right (Lay.wSub (by decide))
  · exact G.L.cw.sub_right (Lay.wSub (by decide))
  · exact G.L.kc.symm

/-- The additional data, outside what the pieces write. -/
theorem aad_oF : ∀ r ∈ VG.Proof.AesGcm.X86.oFF p, (⟨w64 (p.2 4), (p.2 5).toNat⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact G.a_w.sub_right (Region.sub_prefix (by decide))
  · exact G.a_d
  · exact G.a_w.sub_right (Lay.wSub (by decide))
  · exact G.a_w.sub_right (Lay.wSub (by decide))
  · exact G.a_w.sub_right (Lay.wSub (by decide))
  · exact G.a_w.sub_right (Lay.wSub (by decide))
  · exact G.k_a.symm

/-- The return address, outside what the pieces write. -/
theorem ret_oF : ∀ r ∈ VG.Proof.AesGcm.X86.oFF p, (⟨w64 p.1, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact G.r_w.sub_right (Region.sub_prefix (by decide))
  · exact G.r_d
  · exact G.r_w.sub_right (Lay.wSub (by decide))
  · exact G.r_w.sub_right (Lay.wSub (by decide))
  · exact G.r_w.sub_right (Lay.wSub (by decide))
  · exact G.r_w.sub_right (Lay.wSub (by decide))
  · exact VG.Proof.AesGcm.X86.ret_below G.L.sp

/-- `OEnv` after code that writes within `oFF p` and keeps the registers. -/
theorem OEnv.frame {s₀ s s' : State} (h : VG.Proof.AesGcm.X86.OEnv p s₀ s)
    (hf : Frame (VG.Proof.AesGcm.X86.oFF p) s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86.OEnv p s₀ s' := by
  have sl : ∀ o, 128 ≤ o → (o + 4 ≤ auxO ∨ (auxO + 4 ≤ o ∧ o + 4 ≤ rO) ∨ (rO + 16 ≤ o ∧ o + 4 ≤ 240)) →
      slotv s'.mem (p.2 8) o = slotv s.mem (p.2 8) o := fun o h₁ h₂ => by
    rw [slotv_eq, slotv_eq]; exact slot_frame hf (VG.Proof.AesGcm.X86.slot_oF G h₁ h₂)
  have hR := G.rounds
  refine ⟨h.env.keep hbp hsi hsp hrd hwr ?_, ⟨by rw [sl _ (by decide) (by decide)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [sl _ (by decide) (by decide)]; exact h.aadO, by rw [sl _ (by decide) (by decide)]; exact h.alO,
    by rw [sl _ (by decide) (by decide)]; exact h.dataO, by rw [sl _ (by decide) (by decide)]; exact h.lenO,
    by rw [sl _ (by decide) (by decide)]; exact h.zO, by rw [sl _ (by decide) (by decide)]; exact h.nlO,
    by rw [sl _ (by decide) (by decide)]; exact h.tp, h.saved.frame hf fun r hr => ?_, by rw [VG.Proof.AesGcm.X86.ret_kept hf (VG.Proof.AesGcm.X86.ret_oF G)]; exact h.ret,
    by rw [ciph_frame hf (VG.Proof.AesGcm.X86.ctx_oF G) hR]; exact h.ciph,
    by rw [show Hk s'.mem (p.2 0) = Hk s.mem (p.2 0) from blockAt_frame hf fun r hr =>
      (VG.Proof.AesGcm.X86.ctx_oF G r hr).sub_left (Lay.ctxSub (by decide))]; exact h.hk,
    by rw [bytesAt_frame hf (VG.Proof.AesGcm.X86.aad_oF G) (by omega)]; exact h.aad, by rw [hrd]; exact h.rd, by rw [hwr]; exact h.wr,
    by rw [hrd, hwr]; exact h.nIn, by rw [hrd, hwr]; exact h.aIn, by rw [hwr]; exact h.dIn⟩
  · have := sl ctxO (by decide) (by decide); rwa [slotv_eq, slotv_eq] at this
  · exact VG.Proof.AesGcm.X86.slot_oF G (o := 128) (n := 16) (by decide) (by decide) r hr

theorem OEnv.frameE {s₀ s s' : State} (h : VG.Proof.AesGcm.X86.OEnv p s₀ s)
    (hf : Frame (VG.Proof.AesGcm.X86.oFF p) s.mem s'.mem)
    (he : Env (p.2 0) (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86.OEnv p s₀ s' :=
  h.frame G hf (by rw [he.ebp, h.env.ebp]) (by rw [he.esi, h.env.esi]) (by rw [he.esp, h.env.esp]) hrd hwr

/-- A part of the state, in `W`. -/
theorem st_eq {d : Nat} : w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 d = w64 (p.2 8) + BitVec.ofNat 64 (16 + d) := by
  rw [VG.Proof.AesGcm.X86.stOf_w64 G.L.fw, Offset.add_add]

omit G in
/-- A part of `W` the pieces write. -/
theorem w_sub_oF {d k : Nat} (h₁ : 16 ≤ d) (h₂ : d + k ≤ 128) :
    ∃ r' ∈ VG.Proof.AesGcm.X86.oF p, Region.Sub ⟨w64 (p.2 8) + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨⟨w64 (p.2 8) + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ h₁ (by omega)⟩

theorem st_sub_oF {d k : Nat} (h : d + k ≤ 80) :
    ∃ r' ∈ VG.Proof.AesGcm.X86.oF p, Region.Sub ⟨w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 d, k⟩ r' := by
  rw [VG.Proof.AesGcm.X86.st_eq G]; exact VG.Proof.AesGcm.X86.w_sub_oF (by omega) (by omega)

theorem st0_sub_oF {k : Nat} (h : k ≤ 80) : ∃ r' ∈ VG.Proof.AesGcm.X86.oF p, Region.Sub ⟨w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)), k⟩ r' := by
  rw [VG.Proof.AesGcm.X86.stOf_w64 G.L.fw]; exact VG.Proof.AesGcm.X86.w_sub_oF (by omega) (by omega)

omit G in
theorem ws_sub_oF : ∃ r' ∈ VG.Proof.AesGcm.X86.oF p, Region.Sub (wsR (p.2 8)) r' :=
  ⟨_, by simp, fun _ h => h⟩

omit G in
theorem stk_sub_oF : ∃ r' ∈ VG.Proof.AesGcm.X86.oF p, Region.Sub (below p.1 28) r' :=
  ⟨_, by simp, fun _ h => h⟩

omit G in
theorem pslot_sub_oF : ∃ r' ∈ VG.Proof.AesGcm.X86.oF p, Region.Sub (pslotR (p.2 8)) r' :=
  ⟨_, by simp, pslot_ws _⟩

omit G in
theorem Frame.oD {m m' : Mem} (h : Frame (VG.Proof.AesGcm.X86.oF p) m m') : Frame (VG.Proof.AesGcm.X86.oFF p) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)

omit G in
theorem Frame.oDD {m m' : Mem} (h : Frame (⟨w64 (p.2 6), (p.2 7).toNat⟩ :: VG.Proof.AesGcm.X86.oF p) m m') : Frame (VG.Proof.AesGcm.X86.oFF p) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

omit G in
theorem d_sub_oF :
    ∃ r' ∈ ⟨w64 (p.2 6), (p.2 7).toNat⟩ :: VG.Proof.AesGcm.X86.oF p, Region.Sub ⟨w64 (p.2 6), (p.2 7).toNat⟩ r' :=
  ⟨_, by simp, fun _ h => h⟩

end

/-! ## The entry -/

abbrev oKeeps : List (Nat × Nat) :=
  [(0, ctxO), (1, roundsO), (2, dO), (3, nO), (3, nlO), (4, aadO), (5, alO), (6, dataO), (7, lenO)]

abbrev oPre : List Instr := [.mov .esi (.reg .ebp), .alu .add .esi (imm stO)]

abbrev oTail : List Instr := [.mov .eax (imm 0), .store (at_ .ebp zO) .eax]

theorem oneEntry_eq (w : Nat) (ex : List (Nat × Nat)) :
    oneEntry w (ex.flatMap (fun (p : Nat × Nat) => VG.Impl.AesGcm.X86.keep p.1 p.2)) =
      entry w (VG.Proof.AesGcm.X86.oPre ++ ((VG.Proof.AesGcm.X86.oKeeps ++ ex).flatMap (fun (p : Nat × Nat) => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ VG.Proof.AesGcm.X86.oTail)) := by
  simp only [oneEntry, VG.Proof.AesGcm.X86.oKeeps, VG.Proof.AesGcm.X86.oPre, VG.Proof.AesGcm.X86.oTail, List.cons_append, List.flatMap_cons, List.append_assoc, List.nil_append]

/-- The end of the entry: `zO` zeroed. -/
theorem oTail_ok {W : BitVec 32} {s : State} (hbp : s.gpr .ebp = W) (hw : Covers [⟨w64 W, 2560⟩] s.wr)
    (fw : W.toNat + 2560 ≤ 2 ^ 32) :
    ∃ s', runBlock isa VG.Proof.AesGcm.X86.oTail s = some s' ∧ Frame [⟨w64 W + BitVec.ofNat 64 zO, 4⟩] s.mem s'.mem ∧
      slotv s'.mem W zO = 0 ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => w64_add (by omega)
  have wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := fun ho => in_off hw ho (by decide)
  have f₁ : Frame [⟨w64 W + BitVec.ofNat 64 zO, 4⟩] s.mem
      (s.mem.writeW (w64 W + BitVec.ofNat 64 zO) (BitVec.ofNat 32 0)) :=
    (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Region.contains_self _ _)
  exact ⟨_, by xrun [hbp, aW, wIn], by mems []; exact f₁, by mems [slotv_eq]; rfl, by regs [], by regs [], by regs [],
    by mems [], by mems []⟩

/-- After the entry of `seal` or `open`: the nonce ready for `j0`, and the
inputs as they were. -/
structure OEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  o : VG.Proof.AesGcm.X86.OEnv p s₀ s
  dO : slotv s.mem (p.2 8) dO = p.2 2
  nO : slotv s.mem (p.2 8) nO = p.2 3
  iv : bytesAt s.mem (w64 (p.2 2)) (p.2 3).toNat = bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat
  data : bytesAt s.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat
  frame : Frame [⟨w64 (p.2 8) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem

/-- The entry of `seal` and `open` (with `nA` arguments, `W` the last, `w`),
copying also the arguments `ex`, `tag` (the argument 8) among them. -/
theorem oneEntry_pc (nA w : Nat) (hw : nA = w + 1) (h9 : 9 ≤ w) (ex : List (Nat × Nat))
    (hex : ∀ q ∈ ex, q.1 < nA ∧ 144 ≤ q.2 ∧ q.2 + 4 ≤ 2560 ∧ q.2 % 4 = 0 ∧ (q.2 + 4 ≤ zO ∨ zO + 4 ≤ q.2))
    (hnd : ((VG.Proof.AesGcm.X86.oKeeps ++ ex).map (·.2)).Nodup) (htp : (8, tpO) ∈ ex) (Pre : State → Prop)
    (hPre : ∀ s, Pre s → VG.Proof.AesGcm.X86.OP nA w s) (p : BitVec 32 × (Nat → BitVec 32)) (G : VG.Proof.AesGcm.X86.OL p)
    {hh₀ hh : Taint.Hint VG.X86.taint.T}
    (ht₀ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .eax (argOp w)]) hh₀).isSome = true)
    (ht : (VG.X86.taint.check (τr [.eax, .esp]) (.block (saveAt ++ (VG.Proof.AesGcm.X86.oPre ++
      ((VG.Proof.AesGcm.X86.oKeeps ++ ex).flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ VG.Proof.AesGcm.X86.oTail)))) hh).isSome = true) :
    Pc (fun (s₀ : State) s => Pre s₀ ∧ VG.Proof.AesGcm.X86.pubSw nA 8 s₀ = p ∧ s = s₀)
      (oneEntry w (ex.flatMap (fun (p : Nat × Nat) => VG.Impl.AesGcm.X86.keep p.1 p.2)))
      (fun s₀ s => VG.Proof.AesGcm.X86.OEnt p s₀ s ∧ (∀ q ∈ ex, slotv s.mem (p.2 8) q.2 = arg s₀ q.1) ∧ VG.Proof.AesGcm.X86.pubSw nA 8 s₀ = p ∧
        Pre s₀) := by
  rw [VG.Proof.AesGcm.X86.oneEntry_eq]
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have h := hPre _ hpre
    have a : ∀ i, i < 8 → arg s₀ i = p.2 i := fun i hi => VG.Proof.AesGcm.X86.pubSw_arg hpub (by omega) (by omega) (by omega)
    have aW : arg s₀ w = p.2 8 := VG.Proof.AesGcm.X86.pubSw_W hpub (by omega) hw
    have esp := VG.Proof.AesGcm.X86.pubSw_esp hpub
    have fw := h.fw
    rw [aW] at fw
    have wW : Covers [⟨w64 (p.2 8), 2560⟩] s₀.wr := by rw [← aW]; exact h.wW
    have rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by rw [VG.Proof.AesGcm.X86.argsR_eq]; exact h.argR
    have aw : (argsR (s₀.gpr .esp) nA).Disjoint ⟨w64 (p.2 8), 2560⟩ := by
      rw [VG.Proof.AesGcm.X86.argsR_eq, ← aW]; exact h.w_a.symm
    have hok : ∀ q ∈ VG.Proof.AesGcm.X86.oKeeps, q.1 < 8 ∧ 144 ≤ q.2 ∧ q.2 + 4 ≤ 2560 ∧ q.2 % 4 = 0 ∧
        (q.2 + 4 ≤ zO ∨ zO + 4 ≤ q.2) := by decide
    have hps : ∀ q ∈ VG.Proof.AesGcm.X86.oKeeps ++ ex, q.1 < nA ∧ 144 ≤ q.2 ∧ q.2 + 4 ≤ 2560 ∧ q.2 % 4 = 0 := fun q hq => by
      rcases List.mem_append.mp hq with hq | hq
      · have := hok q hq; exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := hex q hq; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
    refine entry_gen (St := VG.Proof.AesGcm.X86.stOf (p.2 8)) _ (VG.Proof.AesGcm.X86.oKeeps ++ ex) _ (by omega) hps hnd aW wW rA aw h.fg fw
      (fun s₁ bp sp rd wr _ => ⟨_, by xrun [bp], by regs [bp], fun r hr => by
        simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ hr], by mems [], by mems [], by mems []⟩) fun s₂ e => ?_
    obtain ⟨s₃, run, f₃, z₃, bp₃, si₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesGcm.X86.oTail_ok (W := p.2 8) e.ebp (by rw [e.wr]; exact wW) fw
    have L := G.L
    -- What the tail writes.
    have st : ∀ o, 128 ≤ o → o + 4 ≤ 2560 → (o + 4 ≤ zO ∨ zO + 4 ≤ o) →
        slotv s₃.mem (p.2 8) o = slotv s₂.mem (p.2 8) o := fun o h₁ h₂ h₃ => by
      rw [slotv_eq, slotv_eq]
      refine slot_frame f₃ fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      simp only [zO] at h₃
      exact Lay.w_w (by simp only [zO]; omega) (by omega) (by decide)
    have f₃' : Frame [⟨w64 (p.2 8) + BitVec.ofNat 64 128, 2432⟩] s₂.mem s₃.mem := f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    have fE : Frame [⟨w64 (p.2 8) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s₃.mem := e.frame.trans f₃'
    have dE : ∀ {q : Addr} {n : Nat}, (⟨q, n⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩ →
        ∀ r ∈ [(⟨w64 (p.2 8) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨q, n⟩ : Region).Disjoint r :=
      fun hq r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hq.sub_right (Lay.wSub (by decide))
    have slR : ∀ q ∈ VG.Proof.AesGcm.X86.oKeeps ++ ex, slotv s₃.mem (p.2 8) q.2 = arg s₀ q.1 := fun q hq => by
      have hz : q.2 + 4 ≤ zO ∨ zO + 4 ≤ q.2 := by
        rcases List.mem_append.mp hq with hq | hq
        · exact (hok q hq).2.2.2.2
        · exact (hex q hq).2.2.2.2
      rw [st _ (by have := (hps q hq).2.1; omega) (hps q hq).2.2.1 hz, e.slots q hq]
    have sl : ∀ q ∈ VG.Proof.AesGcm.X86.oKeeps, slotv s₃.mem (p.2 8) q.2 = p.2 q.1 := fun q hq => by
      rw [slR q (List.mem_append_left _ hq), a _ (hok q hq).1]
    have hR := G.rounds
    have he : Env (p.2 0) (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 s₃ := by
      refine ⟨by rw [bp₃, e.ebp], by rw [si₃, e.esi], by rw [sp₃, e.esp, esp], ?_, ?_, by rw [wr₃, e.wr]; exact wW,
        by have := sl (0, ctxO) (by simp); rwa [slotv_eq] at this⟩
      · rw [rd₃, wr₃, e.rd, e.wr, ← a 0 (by omega)]; exact h.cR
      · rw [wr₃, e.wr, VG.Proof.AesGcm.X86.stOf_w64 fw]; exact covers_off wW (by decide) (by decide)
    refine ⟨s₃, run, ⟨⟨he, ⟨by rw [sl (1, roundsO) (by simp), VG.Proof.AesGcm.X86.ofNat_toNat32], hR⟩, sl (4, aadO) (by simp),
      sl (5, alO) (by simp), sl (6, dataO) (by simp), sl (7, lenO) (by simp), z₃, sl (3, nlO) (by simp),
      slR (8, tpO) (List.mem_append_right _ htp), ?_, ?_, ?_, ?_, ?_, by rw [rd₃, e.rd], by rw [wr₃, e.wr], ?_, ?_, ?_⟩,
      sl (2, dO) (by simp), sl (3, nO) (by simp), ?_, ?_, fE⟩, fun q hq => slR q (List.mem_append_right _ hq), hpub,
      hpre⟩
    · exact e.saved.frame f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [← esp, VG.Proof.AesGcm.X86.ret_kept fE (dE (by rw [esp]; exact G.r_w))]
    · exact ciph_frame fE (dE G.L.cw) hR
    · rw [VG.Proof.AesGcm.X86.ctxH_eq]; exact blockAt_frame fE (dE (G.L.cw.sub_left (Lay.ctxSub (by decide))))
    · exact bytesAt_frame fE (dE G.a_w) (by omega)
    · rw [rd₃, wr₃, e.rd, e.wr, ← a 2 (by omega), ← a 3 (by omega)]; exact h.nR
    · rw [rd₃, wr₃, e.rd, e.wr, ← a 4 (by omega), ← a 5 (by omega)]; exact h.aR
    · rw [wr₃, e.wr, ← a 6 (by omega), ← a 7 (by omega)]; exact h.dW
    · exact bytesAt_frame fE (dE G.n_w) (by omega)
    · exact bytesAt_frame fE (dE G.d_w) (by omega)
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 8 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [VG.Proof.AesGcm.X86.pubSw_esp h₁, VG.Proof.AesGcm.X86.pubSw_esp h₂]) ht₀) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) ht)
    subst s
    have h := hPre _ hpre
    have rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by rw [VG.Proof.AesGcm.X86.argsR_eq]; exact h.argR
    exact WP.mono (VG.Proof.AesGcm.X86.arg0_ok (VG.Proof.AesGcm.X86.argIn_of rA h.fg (by omega))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact VG.Proof.AesGcm.X86.pubSw_W hpub (by omega) hw, by rw [sp]; exact VG.Proof.AesGcm.X86.pubSw_esp hpub⟩

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.OneAad`. -/
section

/-!
# AES-GCM on x86: `J₀` and the additional data of `seal` and `open`

Untrusted: everything here is checked by Lean. `oneAad` (`oneAad_pc`):
`J₀` and the first counter block (`j0`), then the additional data absorbed
(`absorb 16`) and padded (`flush 16`), all within `oF p`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph zeros padLen inc32)
open VG.Proof.Gcm (Absorbed)

/-- After `oneAad`: `J₀`, the additional data absorbed and padded, and the
first counter block. -/
structure OAad (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  o : VG.Proof.AesGcm.X86.OEnv p s₀ s
  j : blockAt s.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8))) =
    Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat)
  y : Absorbed s.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 32)
    (ctxH s₀.mem (w64 (p.2 0)))
    (bytesAt s₀.mem (w64 (p.2 4)) (p.2 5).toNat ++ zeros (padLen (p.2 5).toNat))
  cb : blockAt s.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 48) =
    inc32 (Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat))

/-- What holds between the pieces of `oneAad`: `J₀` and the first counter
block written, within `oF p` since `sE`. -/
structure OJ (p : BitVec 32 × (Nat → BitVec 32)) (sE s₀ s : State) : Prop where
  ent : VG.Proof.AesGcm.X86.OEnt p s₀ sE
  o : VG.Proof.AesGcm.X86.OEnv p s₀ s
  fr : Frame (VG.Proof.AesGcm.X86.oF p) sE.mem s.mem
  j : blockAt s.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8))) =
    Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat)
  cb : blockAt s.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 48) =
    inc32 (Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat))

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : VG.Proof.AesGcm.X86.OL p)
include G

/-- The arguments of a piece from two kept slots: `dO := [so]`, `nO := [sl]`, `bO := 0`. -/
theorem setP_ok {so sl : Nat} (h₁ : 128 ≤ so) (h₂ : so + 4 ≤ 240) (h₃ : 128 ≤ sl) (h₄ : sl + 4 ≤ 240)
    {s : State} (he : Env (p.2 0) (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 s) :
    ∃ s', runBlock isa [.mov .eax (slot so), .store (at_ .ebp dO) .eax, .mov .eax (slot sl),
        .store (at_ .ebp nO) .eax, .mov .eax (imm 0), .store (at_ .ebp bO) .eax] s = some s' ∧
      slotv s'.mem (p.2 8) dO = slotv s.mem (p.2 8) so ∧ slotv s'.mem (p.2 8) nO = slotv s.mem (p.2 8) sl ∧
      slotv s'.mem (p.2 8) bO = 0 ∧ Frame [pslotR (p.2 8)] s.mem s'.mem ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have L := G.L
  have ho : so < 2560 := by omega
  have hl : sl < 2560 := by omega
  have r₁ := he.wIn' (d := so) (n := 4) (by omega)
  have r₂ := he.wIn' (d := sl) (n := 4) (by omega)
  have e₁ : (s.mem.writeW (w64 (p.2 8) + BitVec.ofNat 64 dO) (s.mem.readW (w64 (p.2 8) + BitVec.ofNat 64 so) 32)).readW
      (w64 (p.2 8) + BitVec.ofNat 64 sl) 32 = s.mem.readW (w64 (p.2 8) + BitVec.ofNat 64 sl) 32 :=
    readW_writeW_off _ _ _ (by simp only [dO]; omega) (by omega) (by decide)
  refine ⟨_, by xrun [he.ebp, L.aW ho, L.aW hl, L.aW, he.wIn, r₁, r₂, e₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems [slotv_eq]
  · mems [slotv_eq]
  · mems [slotv_eq]; rfl
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    exact pslot_write (pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide)
      (by decide) _) (by decide) (by decide) _
  · regs []
  · regs []
  · regs []
  · mems []
  · mems []

/-- `bO := [sl] mod 16`. -/
theorem setB_ok {sl : Nat} (h₃ : 128 ≤ sl) (h₄ : sl + 4 ≤ 240) {s : State}
    (he : Env (p.2 0) (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 s) :
    ∃ s', runBlock isa [.mov .eax (slot sl), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax] s = some s' ∧
      slotv s'.mem (p.2 8) bO = BitVec.ofNat 32 ((slotv s.mem (p.2 8) sl).toNat % 16) ∧
      Frame [pslotR (p.2 8)] s.mem s'.mem ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have L := G.L
  have hl : sl < 2560 := by omega
  have r₂ := he.wIn' (d := sl) (n := 4) (by omega)
  have hand := and15 (s.mem.readW (w64 (p.2 8) + BitVec.ofNat 64 sl) 32)
  refine ⟨_, by xrun [he.ebp, L.aW hl, L.aW, he.wIn, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems [slotv_eq]; rw [hand]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    exact pslot_write (Frame.refl _ _) (by decide) (by decide) _
  · regs []
  · regs []
  · regs []
  · mems []
  · mems []

theorem j0Frame_oF : ∀ r ∈ VG.Proof.AesGcm.X86.j0Frame (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28, ∃ r' ∈ VG.Proof.AesGcm.X86.oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcm.X86.st0_sub_oF G (by decide)
  · exact VG.Proof.AesGcm.X86.w_sub_oF (by decide) (by decide)
  · exact VG.Proof.AesGcm.X86.ws_sub_oF
  · exact VG.Proof.AesGcm.X86.stk_sub_oF

theorem absFrame_oF : ∀ r ∈ absFrame (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28 16, ∃ r' ∈ VG.Proof.AesGcm.X86.oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcm.X86.st_sub_oF G (by decide)
  · exact VG.Proof.AesGcm.X86.st_sub_oF G (by decide)
  · exact VG.Proof.AesGcm.X86.ws_sub_oF
  · exact VG.Proof.AesGcm.X86.stk_sub_oF

theorem tFrame_oF : ∀ r ∈ tFrame (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28 16, ∃ r' ∈ VG.Proof.AesGcm.X86.oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcm.X86.st_sub_oF G (by decide)
  · exact VG.Proof.AesGcm.X86.w_sub_oF (by decide) (by decide)
  · exact VG.Proof.AesGcm.X86.ws_sub_oF
  · exact VG.Proof.AesGcm.X86.stk_sub_oF

/-- A block of the state that `absorb 16` and `flush 16` keep (`J₀`, the counter block). -/
theorem st_absFrame {d : Nat} (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 80)) :
    ∀ r ∈ absFrame (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28 16,
      (⟨w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact G.L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (G.L.stk_st (by omega)).symm

theorem st_tFrame {d : Nat} (hd : d + 16 ≤ 16 ∨ (32 ≤ d ∧ d + 16 ≤ 80)) :
    ∀ r ∈ tFrame (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28 16,
      (⟨w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact G.L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact G.L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (G.L.stk_st (by omega)).symm

theorem st_pslot {d : Nat} (hd : d + 16 ≤ 80) :
    ∀ r ∈ [pslotR (p.2 8)], (⟨w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact G.L.st_w (by omega) (.inr ⟨by decide, by decide⟩)

theorem oneAad_pc :
    Pc (fun (b : State × State) s => VG.Proof.AesGcm.X86.OEnt p b.1 s ∧ s = b.2) (oneAad vg.callees)
      (fun b s' => VG.Proof.AesGcm.X86.OAad p b.1 s' ∧ Frame (VG.Proof.AesGcm.X86.oF p) b.2.mem s'.mem) := by
  have L := G.L
  have sW : (⟨w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)), 80⟩ : Region).Sub ⟨w64 (p.2 8), 2560⟩ := by
    rw [VG.Proof.AesGcm.X86.stOf_w64 L.fw]; exact Lay.wSub (by decide)
  -- `J₀`.
  refine Pc.seq (Q := fun b s => VG.Proof.AesGcm.X86.OJ p b.2 b.1 s ∧
      blockAt s.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 16) = 0)
    (Pc.mono (Pc.lift (VG.Proof.AesGcm.X86.j0_pc L (D := p.2 2) (n := (p.2 3).toNat)) (fun _ s => s.mem) fun b s ⟨h, _⟩ =>
      ⟨⟨h.o.env, h.dO, by rw [h.nO, VG.Proof.AesGcm.X86.ofNat_toNat32], by rw [h.o.nlO, VG.Proof.AesGcm.X86.ofNat_toNat32], h.o.zO, (p.2 3).isLt,
        ⟨h.o.nIn, G.fn, G.n_w.sub_right sW, G.n_w, G.k_n⟩⟩, rfl⟩) (fun _ _ h => h)
      fun b s ⟨sE, ⟨h, hs⟩, ho, rd, wr⟩ => by
        subst hs
        exact ⟨⟨h, h.o.frameE G (Frame.oD (ho.frame.sub (VG.Proof.AesGcm.X86.j0Frame_oF G))) ho.env rd wr,
          ho.frame.sub (VG.Proof.AesGcm.X86.j0Frame_oF G), by rw [ho.j0, h.o.hk, h.iv], by rw [ho.cb, h.o.hk, h.iv]⟩, ho.y⟩) ?_
  -- The additional data's arguments.
  refine Pc.seq (Q := fun b s => VG.Proof.AesGcm.X86.OJ p b.2 b.1 s ∧
      blockAt s.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 16) = 0 ∧
      AbsIn (p.2 0) (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28 (p.2 4) (p.2 5).toNat 0 s)
    (Pc.taint [.ebp] (fun b s ⟨h, y0⟩ => ?_) (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)) ?_
  · obtain ⟨s', run, d, n, bz, f, bp, si, sp, rd, wr⟩ := VG.Proof.AesGcm.X86.setP_ok G (so := aadO) (sl := alO) (by decide) (by decide)
      (by decide) (by decide) h.o.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have fo : Frame (VG.Proof.AesGcm.X86.oF p) s.mem s'.mem := f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesGcm.X86.pslot_sub_oF
    have o' := h.o.frame G (Frame.oD fo) bp si sp rd wr
    refine ⟨⟨h.ent, o', h.fr.trans fo, by
        have e := blockAt_frame f (VG.Proof.AesGcm.X86.st_pslot G (d := 0) (by decide)); rw [BitVec.add_zero] at e; rw [e]; exact h.j,
        by rw [blockAt_frame f (VG.Proof.AesGcm.X86.st_pslot G (by decide))]; exact h.cb⟩,
      by rw [blockAt_frame f (VG.Proof.AesGcm.X86.st_pslot G (by decide))]; exact y0, ⟨o'.env, by rw [d]; exact h.o.aadO,
        by rw [n, h.o.alO, VG.Proof.AesGcm.X86.ofNat_toNat32], by rw [bz]; rfl, by decide, (p.2 5).isLt,
        ⟨o'.aIn, G.fa, G.a_w.sub_right sW, G.a_w, G.k_a⟩⟩⟩
  -- Absorbed.
  refine Pc.seq (Q := fun b s => VG.Proof.AesGcm.X86.OJ p b.2 b.1 s ∧
      Absorbed s.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (bytesAt b.1.mem (w64 (p.2 4)) (p.2 5).toNat))
    (Pc.mono (Pc.lift (absorb_pc L (yo := 16) (.inr rfl) (b := 0) (by decide) (p.2 5).isLt) (fun _ s => s.mem)
      fun b s ⟨_, _, ha⟩ => ⟨ha, rfl⟩) (fun _ _ h => h)
      fun b s' ⟨s, ⟨h, y0, _⟩, ho, rd, wr⟩ => ⟨⟨h.ent, h.o.frameE G
        (Frame.oD (ho.frame.sub (VG.Proof.AesGcm.X86.absFrame_oF G))) ho.env rd wr, h.fr.trans (ho.frame.sub (VG.Proof.AesGcm.X86.absFrame_oF G)), ?_, ?_⟩,
        ?_⟩) ?_
  · have := blockAt_frame ho.frame (VG.Proof.AesGcm.X86.st_absFrame G (d := 0) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this]; exact h.j
  · rw [blockAt_frame ho.frame (VG.Proof.AesGcm.X86.st_absFrame G (.inr ⟨by decide, by decide⟩))]; exact h.cb
  · have := ho.abs [] rfl (Proof.Gcm.absorbed_nil _ y0)
    rwa [List.nil_append, h.o.hk, h.o.aad] at this
  -- `bO`.
  refine Pc.seq (Q := fun b s => VG.Proof.AesGcm.X86.OJ p b.2 b.1 s ∧
      Absorbed s.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (bytesAt b.1.mem (w64 (p.2 4)) (p.2 5).toNat) ∧
      slotv s.mem (p.2 8) bO = BitVec.ofNat 32 ((p.2 5).toNat % 16))
    (Pc.taint [.ebp] (fun b s ⟨h, ha⟩ => ?_) (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)) ?_
  · obtain ⟨s', run, bz, f, bp, si, sp, rd, wr⟩ := VG.Proof.AesGcm.X86.setB_ok G (sl := alO) (by decide) (by decide) h.o.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have fo : Frame (VG.Proof.AesGcm.X86.oF p) s.mem s'.mem := f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesGcm.X86.pslot_sub_oF
    have o' := h.o.frame G (Frame.oD fo) bp si sp rd wr
    have hl := length_bytesAt b.1.mem (w64 (p.2 4)) (p.2 5).toNat
    refine ⟨⟨h.ent, o', h.fr.trans fo, by
        have e := blockAt_frame f (VG.Proof.AesGcm.X86.st_pslot G (d := 0) (by decide)); rw [BitVec.add_zero] at e; rw [e]; exact h.j,
        by rw [blockAt_frame f (VG.Proof.AesGcm.X86.st_pslot G (by decide))]; exact h.cb⟩,
      ha.congr (blockAt_frame f (VG.Proof.AesGcm.X86.st_pslot G (by decide))) (bytesAt_frame f (fun r hr =>
        (VG.Proof.AesGcm.X86.st_pslot G (d := 32) (by decide) r hr).sub_left (Region.sub_prefix (by omega))) (by omega)),
      by rw [bz, h.o.alO]⟩
  -- Padded.
  refine Pc.mono (Pc.lift (flush_pc L (yo := 16) (.inr rfl) (b := (p.2 5).toNat % 16) (Nat.mod_lt _ (by decide)))
    (fun _ s => s.mem) fun b s ⟨h, _, hb⟩ => ⟨⟨h.o.env, hb⟩, rfl⟩) (fun _ _ h => h)
    fun b s' ⟨s, ⟨h, ha, _⟩, ho, rd, wr⟩ => ⟨⟨h.o.frameE G
      (Frame.oD (ho.frame.sub (VG.Proof.AesGcm.X86.tFrame_oF G))) ho.env rd wr, ?_, ?_, ?_⟩, h.fr.trans (ho.frame.sub (VG.Proof.AesGcm.X86.tFrame_oF G))⟩
  · have := blockAt_frame ho.frame (VG.Proof.AesGcm.X86.st_tFrame G (d := 0) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this]; exact h.j
  · have hl := length_bytesAt b.1.mem (w64 (p.2 4)) (p.2 5).toNat
    have := ho.abs _ (by rw [hl]) (by rw [h.o.hk]; exact ha)
    rwa [h.o.hk, hl] at this
  · rw [blockAt_frame ho.frame (VG.Proof.AesGcm.X86.st_tFrame G (.inr ⟨by decide, by decide⟩))]; exact h.cb

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.OneTag`. -/
section

/-!
# AES-GCM on x86: the data and the tag of `seal` and `open`

Untrusted: everything here is checked by Lean. `oneCrypt` (`oneCrypt_pc`):
the data XORed with the keystream from a counter block; and `oneTag o`
(`oneTag_pc`): the data absorbed and padded, then the tag into `W + o`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph zeros padLen inc32 ghash ghashFrom blocks toBytes ofBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)

theorem oneCrypt_eq : (oneCrypt vg.callees) = .seq (.block [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax,
    .mov .eax (slot lenO), .store (at_ .ebp nO) .eax, .mov .eax (imm 0), .store (at_ .ebp bO) .eax]) (crypt vg.callees) := rfl

theorem oneTag_eq (o : Nat) : (oneTag vg.callees) o = .seq (.block [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax,
    .mov .eax (slot lenO), .store (at_ .ebp nO) .eax, .mov .eax (imm 0), .store (at_ .ebp bO) .eax])
  (.seq (absorb vg.callees 16)
  (.seq (.block [.mov .eax (slot lenO), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax])
  (.seq (flush vg.callees 16) (tag vg.callees o alO zO lenO zO)))) := rfl

/-- What GHASH has absorbed before the data: the additional data, padded. -/
abbrev xA (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : List Byte :=
  bytesAt s₀.mem (w64 (p.2 4)) (p.2 5).toNat ++ zeros (padLen (p.2 5).toNat)

/-- `J₀`. -/
abbrev jOf (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : Block :=
  Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat)

/-- Before `oneTag o`. -/
structure OTIn (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  o : VG.Proof.AesGcm.X86.OEnv p s₀ s
  j : blockAt s.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8))) = VG.Proof.AesGcm.X86.jOf p s₀
  y : Absorbed s.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 32)
    (ctxH s₀.mem (w64 (p.2 0))) (VG.Proof.AesGcm.X86.xA p s₀)

/-- The regions `oneTag o` writes: the state's first three blocks, `T`, the
tag at `W + o`, the working space and the stack. -/
abbrev oT (p : BitVec 32 × (Nat → BitVec 32)) (o : Nat) : List Region :=
  [⟨w64 (p.2 8) + BitVec.ofNat 64 16, 48⟩, ⟨w64 (p.2 8) + BitVec.ofNat 64 96, 16⟩,
    ⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩, wsR (p.2 8), below p.1 28]

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : VG.Proof.AesGcm.X86.OL p)
include G

omit G in
theorem pslot_oF {m m' : Mem} (f : Frame [pslotR (p.2 8)] m m') : Frame (VG.Proof.AesGcm.X86.oF p) m m' :=
  f.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesGcm.X86.pslot_sub_oF

theorem crFrame_oF : ∀ r ∈ crFrame (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28 (p.2 6) (p.2 7).toNat,
    ∃ r' ∈ ⟨w64 (p.2 6), (p.2 7).toNat⟩ :: VG.Proof.AesGcm.X86.oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcm.X86.d_sub_oF
  · obtain ⟨r', h₁, h₂⟩ := VG.Proof.AesGcm.X86.st_sub_oF G (d := 48) (k := 32) (by decide)
    exact ⟨r', List.mem_cons_of_mem _ h₁, h₂⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The data, writable, for `crypt`. -/
theorem dataW_of {s₀ s : State} (h : VG.Proof.AesGcm.X86.OEnv p s₀ s) :
    DataW (p.2 0) (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28 s (p.2 6) (p.2 7).toNat :=
  ⟨⟨covers_left h.dIn, G.fd, G.d_w.sub_right (by rw [VG.Proof.AesGcm.X86.stOf_w64 G.L.fw]; exact Lay.wSub (by decide)), G.d_w, G.k_d⟩,
    h.dIn, G.c_d⟩

theorem oneCrypt_pc (icb : State → Block) :
    Pc (fun (b : State × State) s => (VG.Proof.AesGcm.X86.OEnv p b.1 s ∧
        CtrS s.mem (VG.Proof.AesGcm.X86.stOf (p.2 8)) (ctxCiph b.1.mem (w64 (p.2 0)) (p.2 1).toNat) (icb b.1) 0) ∧ s = b.2) (oneCrypt vg.callees)
      (fun b s' => VG.Proof.AesGcm.X86.OEnv p b.1 s' ∧
        bytesAt s'.mem (w64 (p.2 6)) (p.2 7).toNat =
          xorKs (ctxCiph b.1.mem (w64 (p.2 0)) (p.2 1).toNat) (icb b.1) 0 (bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat) ∧
        Frame (crFrame (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28 (p.2 6) (p.2 7).toNat) b.2.mem s'.mem) := by
  have L := G.L
  rw [VG.Proof.AesGcm.X86.oneCrypt_eq]
  refine Pc.seq (Q := fun b s₁ => VG.Proof.AesGcm.X86.OEnv p b.1 s₁ ∧
      CrIn (p.2 0) (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28 (p.2 1).toNat (p.2 6) (p.2 7).toNat 0 s₁ ∧
      CtrS s₁.mem (VG.Proof.AesGcm.X86.stOf (p.2 8)) (ctxCiph b.1.mem (w64 (p.2 0)) (p.2 1).toNat) (icb b.1) 0 ∧
      Frame [pslotR (p.2 8)] b.2.mem s₁.mem)
    (Pc.taint [.ebp] (fun b s ⟨⟨h, hc⟩, hs⟩ => ?_) (fun _ _ s₁ s₂ ⟨⟨h₁, _⟩, _⟩ ⟨⟨h₂, _⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)) ?_
  · subst hs
    obtain ⟨s', run, d, n, bz, f, bp, si, sp, rd, wr⟩ := VG.Proof.AesGcm.X86.setP_ok G (so := dataO) (sl := lenO) (by decide) (by decide)
      (by decide) (by decide) h.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have o' := h.frame G (Frame.oD (VG.Proof.AesGcm.X86.pslot_oF f)) bp si sp rd wr
    refine ⟨o', ⟨o'.env, by rw [d]; exact h.dataO, by rw [n, h.lenO, VG.Proof.AesGcm.X86.ofNat_toNat32], by rw [bz]; rfl,
      (p.2 7).isLt, VG.Proof.AesGcm.X86.dataW_of G o', o'.rounds⟩, ?_, f⟩
    exact hc.congr (blockAt_frame f (VG.Proof.AesGcm.X86.st_pslot G (by decide))) (blockAt_frame f (VG.Proof.AesGcm.X86.st_pslot G (by decide)))
  refine Pc.mono (Pc.lift (Pc.forall fun (c : Block) => crypt_pc L rfl (R := (p.2 1).toNat) (D := p.2 6)
    (n := (p.2 7).toNat) (P := 0) (icb := c)) (fun _ s => s.mem) fun b s ⟨_, hi, _⟩ => ⟨hi, rfl⟩)
    (fun _ _ h => h) fun b s' ⟨s₁, ⟨h₁, hi, hc, f⟩, ho, rd, wr⟩ => ?_
  have hco := ho (icb b.1)
  have hf : Frame (⟨w64 (p.2 6), (p.2 7).toNat⟩ :: VG.Proof.AesGcm.X86.oF p) s₁.mem s'.mem := hco.frame.sub (VG.Proof.AesGcm.X86.crFrame_oF G)
  refine ⟨h₁.frameE G (Frame.oDD hf) hco.env rd wr, ?_, ?_⟩
  · have := hco.out (by rw [h₁.ciph]; exact hc)
    rwa [h₁.ciph, bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact G.d_w.sub_right (Lay.wSub (by decide))) (by have := G.fd; omega)] at this
  · exact (f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wsR (p.2 8), by simp, pslot_ws _⟩).trans hco.frame

theorem tagFrame_oF {o : Nat} : ∀ r ∈ VG.Proof.AesGcm.X86.tagFrame (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 o,
    ∃ r' ∈ ⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩ :: VG.Proof.AesGcm.X86.oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have c : ∀ {r : Region}, (∃ r' ∈ VG.Proof.AesGcm.X86.oF p, Region.Sub r r') →
      ∃ r' ∈ ⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩ :: VG.Proof.AesGcm.X86.oF p, Region.Sub r r' :=
    fun ⟨r', h₁, h₂⟩ => ⟨r', List.mem_cons_of_mem _ h₁, h₂⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact c (VG.Proof.AesGcm.X86.st0_sub_oF G (by decide))
  · exact c (VG.Proof.AesGcm.X86.w_sub_oF (by decide) (by decide))
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact c VG.Proof.AesGcm.X86.ws_sub_oF
  · exact c VG.Proof.AesGcm.X86.stk_sub_oF

omit G in
theorem wo_oFF {o : Nat} (ho : o = 0 ∨ o = 112) {m m' : Mem}
    (h : Frame (⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩ :: VG.Proof.AesGcm.X86.oF p) m m') : Frame (VG.Proof.AesGcm.X86.oFF p) m m' := by
  refine h.sub fun r hr => ?_
  rcases List.mem_cons.mp hr with rfl | hr
  · rcases ho with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by rw [BitVec.add_zero]; exact fun _ h => h⟩
    · exact ⟨⟨w64 (p.2 8) + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ h => h⟩

theorem OTIn.pslot {s₀ s s' : State} (h : VG.Proof.AesGcm.X86.OTIn p s₀ s) (f : Frame [pslotR (p.2 8)] s.mem s'.mem)
    (bp : s'.gpr .ebp = s.gpr .ebp) (si : s'.gpr .esi = s.gpr .esi) (sp : s'.gpr .esp = s.gpr .esp)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) : VG.Proof.AesGcm.X86.OTIn p s₀ s' := by
  have hl : (VG.Proof.AesGcm.X86.xA p s₀).length % 16 = 0 := by
    simp only [VG.Proof.AesGcm.X86.xA, List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  refine ⟨h.o.frame G (Frame.oD (VG.Proof.AesGcm.X86.pslot_oF f)) bp si sp rd wr, ?_, h.y.congr (blockAt_frame f (VG.Proof.AesGcm.X86.st_pslot G
    (by decide))) (by rw [hl]; rfl)⟩
  have e := blockAt_frame f (VG.Proof.AesGcm.X86.st_pslot G (d := 0) (by decide)); rw [BitVec.add_zero] at e; rw [e]; exact h.j

theorem st_sub_oT {o d k : Nat} (h : d + k ≤ 48) :
    ∃ r' ∈ VG.Proof.AesGcm.X86.oT p o, Region.Sub ⟨w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 d, k⟩ r' := by
  rw [VG.Proof.AesGcm.X86.st_eq G]; exact ⟨_, List.mem_cons_self .., Offset.sub _ (by omega) (by omega)⟩

theorem st0_sub_oT {o k : Nat} (h : k ≤ 48) : ∃ r' ∈ VG.Proof.AesGcm.X86.oT p o, Region.Sub ⟨w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)), k⟩ r' := by
  rw [VG.Proof.AesGcm.X86.stOf_w64 G.L.fw]; exact ⟨_, List.mem_cons_self .., Offset.sub _ (by omega) (by omega)⟩

omit G in
theorem pslot_oT {o : Nat} {m m' : Mem} (f : Frame [pslotR (p.2 8)] m m') : Frame (VG.Proof.AesGcm.X86.oT p o) m m' :=
  f.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wsR (p.2 8), by simp, pslot_ws _⟩

theorem absFrame_oT {o : Nat} : ∀ r ∈ absFrame (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28 16, ∃ r' ∈ VG.Proof.AesGcm.X86.oT p o, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcm.X86.st_sub_oT G (by decide)
  · exact VG.Proof.AesGcm.X86.st_sub_oT G (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem tFrame_oT {o : Nat} : ∀ r ∈ tFrame (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28 16, ∃ r' ∈ VG.Proof.AesGcm.X86.oT p o, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcm.X86.st_sub_oT G (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem tagFrame_oT {o : Nat} : ∀ r ∈ VG.Proof.AesGcm.X86.tagFrame (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 o, ∃ r' ∈ VG.Proof.AesGcm.X86.oT p o, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcm.X86.st0_sub_oT G (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

omit G in
theorem oT_oF {o : Nat} {m m' : Mem} (h : Frame (VG.Proof.AesGcm.X86.oT p o) m m') :
    Frame (⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩ :: VG.Proof.AesGcm.X86.oF p) m m' := by
  refine h.sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨w64 (p.2 8) + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨w64 (p.2 8) + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The counter block, apart from what `oneTag o` writes. -/
theorem cb_oT {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ VG.Proof.AesGcm.X86.oT p o, (⟨w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
  rw [VG.Proof.AesGcm.X86.st_eq G]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rcases ho with rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (G.L.stk_w (by decide)).symm

theorem oneTag_pc {o : Nat} (ho : o = 0 ∨ o = 112) :
    Pc (fun (b : State × State) s => VG.Proof.AesGcm.X86.OTIn p b.1 s ∧ s = b.2) (oneTag vg.callees o)
      (fun b s' => VG.Proof.AesGcm.X86.OEnv p b.1 s' ∧
        bytesAt s'.mem (w64 (p.2 8) + BitVec.ofNat 64 o) 16 =
          toBytes (ghashFrom (ctxH b.1.mem (w64 (p.2 0))) (ghash (ctxH b.1.mem (w64 (p.2 0)))
            (blocks (VG.Proof.AesGcm.X86.xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat ++
              zeros (padLen (VG.Proof.AesGcm.X86.xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat).length))))
            [ofBytes (lensBlock (p.2 5).toNat (p.2 7).toNat)] ^^^
            ctxCiph b.1.mem (w64 (p.2 0)) (p.2 1).toNat (VG.Proof.AesGcm.X86.jOf p b.1)) ∧
        Frame (VG.Proof.AesGcm.X86.oT p o) b.2.mem s'.mem) := by
  have L := G.L
  have hl : ∀ s₀, (VG.Proof.AesGcm.X86.xA p s₀).length % 16 = 0 := fun s₀ => by
    simp only [VG.Proof.AesGcm.X86.xA, List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  rw [VG.Proof.AesGcm.X86.oneTag_eq]
  -- The data's arguments.
  refine Pc.seq (Q := fun b s₁ => VG.Proof.AesGcm.X86.OTIn p b.1 s₁ ∧
      AbsIn (p.2 0) (VG.Proof.AesGcm.X86.stOf (p.2 8)) (p.2 8) p.1 28 (p.2 6) (p.2 7).toNat 0 s₁ ∧
      Frame [pslotR (p.2 8)] b.2.mem s₁.mem)
    (Pc.taint [.ebp] (fun b s ⟨h, hs⟩ => ?_) (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)) ?_
  · subst hs
    obtain ⟨s', run, d, n, bz, f, bp, si, sp, rd, wr⟩ := VG.Proof.AesGcm.X86.setP_ok G (so := dataO) (sl := lenO) (by decide) (by decide)
      (by decide) (by decide) h.o.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have h' := h.pslot G f bp si sp rd wr
    exact ⟨h', ⟨h'.o.env, by rw [d]; exact h.o.dataO, by rw [n, h.o.lenO, VG.Proof.AesGcm.X86.ofNat_toNat32], by rw [bz]; rfl,
      by decide, (p.2 7).isLt, (VG.Proof.AesGcm.X86.dataW_of G h'.o).ok⟩, f⟩
  -- Absorbed.
  refine Pc.seq (Q := fun b s₂ => VG.Proof.AesGcm.X86.OEnv p b.1 s₂ ∧
      blockAt s₂.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8))) = VG.Proof.AesGcm.X86.jOf p b.1 ∧
      Absorbed s₂.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (VG.Proof.AesGcm.X86.xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat) ∧
      Frame (VG.Proof.AesGcm.X86.oT p o) b.2.mem s₂.mem)
    (Pc.mono (Pc.lift (absorb_pc L (yo := 16) (.inr rfl) (b := 0) (by decide) (p.2 7).isLt) (fun _ s => s.mem)
      fun b s ⟨_, ha, _⟩ => ⟨ha, rfl⟩) (fun _ _ h => h)
      fun b s₂ ⟨s₁, ⟨h₁, _, f⟩, ho, rd, wr⟩ => ⟨h₁.o.frameE G
        (Frame.oD (ho.frame.sub (VG.Proof.AesGcm.X86.absFrame_oF G))) ho.env rd wr, ?_, ?_,
        (VG.Proof.AesGcm.X86.pslot_oT f).trans (ho.frame.sub (VG.Proof.AesGcm.X86.absFrame_oT G))⟩) ?_
  · have := blockAt_frame ho.frame (VG.Proof.AesGcm.X86.st_absFrame G (d := 0) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this]; exact h₁.j
  · have := ho.abs (VG.Proof.AesGcm.X86.xA p b.1) (hl b.1) (by rw [h₁.o.hk]; exact h₁.y)
    rwa [h₁.o.hk, bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact G.d_w.sub_right (Lay.wSub (by decide))) (by have := G.fd; omega)] at this
  -- `bO`.
  refine Pc.seq (Q := fun b s₃ => VG.Proof.AesGcm.X86.OEnv p b.1 s₃ ∧
      blockAt s₃.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8))) = VG.Proof.AesGcm.X86.jOf p b.1 ∧
      Absorbed s₃.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (VG.Proof.AesGcm.X86.xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat) ∧
      Frame (VG.Proof.AesGcm.X86.oT p o) b.2.mem s₃.mem ∧ slotv s₃.mem (p.2 8) bO = BitVec.ofNat 32 ((p.2 7).toNat % 16))
    (Pc.taint [.ebp] (fun b s₂ ⟨h₂, hj, ha, f⟩ => ?_) (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)) ?_
  · obtain ⟨s', run, bz, f', bp, si, sp, rd, wr⟩ := VG.Proof.AesGcm.X86.setB_ok G (sl := lenO) (by decide) (by decide) h₂.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have hx : (VG.Proof.AesGcm.X86.xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat).length % 16 < 16 :=
      Nat.mod_lt _ (by decide)
    refine ⟨h₂.frame G (Frame.oD (VG.Proof.AesGcm.X86.pslot_oF f')) bp si sp rd wr, ?_,
      ha.congr (blockAt_frame f' (VG.Proof.AesGcm.X86.st_pslot G (by decide))) (bytesAt_frame f' (fun r hr =>
        (VG.Proof.AesGcm.X86.st_pslot G (d := 32) (by decide) r hr).sub_left (Region.sub_prefix (by omega))) (by omega)),
      f.trans (VG.Proof.AesGcm.X86.pslot_oT f'), by rw [bz, h₂.lenO]⟩
    have e := blockAt_frame f' (VG.Proof.AesGcm.X86.st_pslot G (d := 0) (by decide)); rw [BitVec.add_zero] at e; rw [e]; exact hj
  -- Padded.
  refine Pc.seq (Q := fun b s₄ => VG.Proof.AesGcm.X86.OEnv p b.1 s₄ ∧
      blockAt s₄.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8))) = VG.Proof.AesGcm.X86.jOf p b.1 ∧
      Absorbed s₄.mem (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 16) (w64 (VG.Proof.AesGcm.X86.stOf (p.2 8)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (VG.Proof.AesGcm.X86.xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat ++
          zeros (padLen (VG.Proof.AesGcm.X86.xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat).length)) ∧
      Frame (VG.Proof.AesGcm.X86.oT p o) b.2.mem s₄.mem)
    (Pc.mono (Pc.lift (flush_pc L (yo := 16) (.inr rfl) (b := (p.2 7).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun _ s => s.mem) fun b s ⟨h, _, _, _, hb⟩ => ⟨⟨h.env, hb⟩, rfl⟩) (fun _ _ h => h)
      fun b s₄ ⟨s₃, ⟨h₃, hj, ha, f, _⟩, ho, rd, wr⟩ => ⟨h₃.frameE G
        (Frame.oD (ho.frame.sub (VG.Proof.AesGcm.X86.tFrame_oF G))) ho.env rd wr, ?_, ?_, f.trans (ho.frame.sub (VG.Proof.AesGcm.X86.tFrame_oT G))⟩) ?_
  · have := blockAt_frame ho.frame (VG.Proof.AesGcm.X86.st_tFrame G (d := 0) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this]; exact hj
  · have hx : (VG.Proof.AesGcm.X86.xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat).length % 16 = (p.2 7).toNat % 16 := by
      rw [List.length_append, length_bytesAt]; have := hl b.1; omega
    have := ho.abs _ hx (by rw [h₃.hk]; exact ha)
    rwa [h₃.hk] at this
  -- The tag.
  refine Pc.mono (Pc.lift (VG.Proof.AesGcm.X86.tag_pc L ho (.inr (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)) (R := (p.2 1).toNat) (alo := p.2 5)
    (ahi := 0) (tlo := p.2 7) (thi := 0)) (fun _ s => s.mem)
    fun b s ⟨h, _, _, _⟩ => ⟨⟨h.env, ⟨h.alO, h.zO, h.lenO, h.zO⟩, h.rounds⟩, rfl⟩) (fun _ _ h => h)
    fun b s₅ ⟨s₄, ⟨h₄, hj, ha, f⟩, ho', rd, wr⟩ => ⟨h₄.frameE G
      (VG.Proof.AesGcm.X86.wo_oFF ho (ho'.frame.sub (VG.Proof.AesGcm.X86.tagFrame_oF G))) ho'.env rd wr, ?_,
      f.trans (ho'.frame.sub (VG.Proof.AesGcm.X86.tagFrame_oT G))⟩
  have hX : (VG.Proof.AesGcm.X86.xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat ++
      zeros (padLen (VG.Proof.AesGcm.X86.xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat).length)).length % 16 = 0 := by
    rw [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  rw [ho'.out, h₄.hk, h₄.ciph, hj, Proof.Gcm.Absorbed.whole_eq ha hX]
  simp only [val64, show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add]

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.StreamAad`. -/
section

/-!
# AES-GCM on x86: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. The entry, the additional
data absorbed into GHASH (`absorb 16`) and the exit, as one `Pc`
(`streamAad_pc`): correct (`streamAad_correct`) and constant time
(`streamAad_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)
open VG.Proof.Gcm (Absorbed Ctr)

abbrev aadTail : List Instr := [.mov .eax (argOp 2), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax]
abbrev aadKeeps : List (Nat × Nat) := [(0, ctxO), (4, dO), (5, nO)]

theorem streamAad_eq : (streamAad vg.callees) = .seq (entry 6 (([.mov .esi (argOp 1)] : List Instr) ++
    (aadKeeps.flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ VG.Proof.AesGcm.X86.aadTail))) (.seq (absorb vg.callees 16) (.block restore)) := rfl

theorem streamAad_lay {s : State} (h : VG.Proof.AesGcm.X86.streamAadPre s) :
    Lay (arg s 0) (arg s 1) (arg s 6) (s.gpr .esp) 24 := by
  simp only [VG.Proof.AesGcm.X86.streamAadPre] at h
  obtain ⟨-, -, d_cs, d_cw, -, -, d_sw, -, -, -, -, -, -, -, -, -, k_c, k_s, -, k_w, -, fc, fs, -, fw, sp, -⟩ := h
  rw [VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.below_eq sp] at k_c k_s k_w
  exact ⟨fc, fs, fw, Nat.le_refl _, by decide, sp, d_cs, d_cw, d_sw.sub_right (Region.sub_prefix (by decide)),
    d_sw.sub_right (Lay.wSub (by decide)), k_c, k_s, k_w⟩

/-- After the entry: the additional data ready for `absorb 16`. -/
structure AadIn (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : VG.Proof.AesGcm.X86.streamAadPre s₀
  pub : VG.Proof.AesGcm.X86.pubOf 7 s₀ = p
  abs : AbsIn (p.2 0) (p.2 1) (p.2 6) p.1 24 (p.2 4) (p.2 5).toNat ((p.2 2).toNat % 16) s
  saved : SavedAt s.mem (p.2 6) s₀
  frame : Frame [⟨w64 (p.2 6) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem aadEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => VG.Proof.AesGcm.X86.streamAadPre s₀ ∧ VG.Proof.AesGcm.X86.pubOf 7 s₀ = p ∧ s = s₀)
      (entry 6 (([.mov .esi (argOp 1)] : List Instr) ++ (aadKeeps.flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ VG.Proof.AesGcm.X86.aadTail)))
      (VG.Proof.AesGcm.X86.AadIn p) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have L := VG.Proof.AesGcm.X86.streamAad_lay hpre
    have hp := hpre
    simp only [VG.Proof.AesGcm.X86.streamAadPre] at hp
    obtain ⟨hrd, hwr, d_cs, d_cw, d_ca, d_sd, d_sw, d_sa, d_dw, d_da, d_wa, -, -, -, -, -, k_c, k_s, k_d, k_w, k_a,
      fc, fs, fd, fw, sp, fa⟩ := hp
    have a : ∀ i, i < 7 → arg s₀ i = p.2 i := fun i hi => VG.Proof.AesGcm.X86.pubOf_arg hpub hi
    have esp := VG.Proof.AesGcm.X86.pubOf_esp hpub
    rw [VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.below_eq sp] at k_d
    have wW : Covers [⟨w64 (arg s₀ 6), 2560⟩] s₀.wr := by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 7] (s₀.rd ++ s₀.wr) := by
      rw [VG.Proof.AesGcm.X86.argsR_eq, hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 7).Disjoint ⟨w64 (arg s₀ 6), 2560⟩ := by rw [VG.Proof.AesGcm.X86.argsR_eq]; exact d_wa.symm
    refine entry_ok VG.Proof.AesGcm.X86.aadKeeps VG.Proof.AesGcm.X86.aadTail (by decide) (by decide) (by decide) (by decide) rfl rfl wW rA aw
      (by omega) fw fun s₂ e => ?_
    have he : Env (arg s₀ 0) (arg s₀ 1) (arg s₀ 6) (s₀.gpr .esp) s₂ :=
      ⟨e.ebp, e.esi, e.esp, by rw [e.rd, e.wr, hrd]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp),
        by rw [e.wr, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), by rw [e.wr]; exact wW,
        e.slots (0, ctxO) (by simp)⟩
    have i₂ : InRegions (s₂.rd ++ s₂.wr) (argA (s₀.gpr .esp) 2) 4 := by
      rw [e.rd, e.wr]; exact VG.Proof.AesGcm.X86.argIn_of rA (by omega) (by decide)
    have v₂ := e.args 2 (by decide)
    have hand := and15 (arg s₀ 2)
    refine ⟨_, by xrun [e.esp, i₂, v₂, he.ebp, L.aW, he.wIn], ?_⟩
    have hf : Frame [⟨w64 (arg s₀ 6) + BitVec.ofNat 64 bO, 4⟩] s₂.mem
        (s₂.mem.writeW (w64 (arg s₀ 6) + BitVec.ofNat 64 bO) (arg s₀ 2 &&& BitVec.ofNat 32 15)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have sl : ∀ {o}, 128 ≤ o → o + 4 ≤ 280 → slotv (s₂.mem.writeW (w64 (arg s₀ 6) + BitVec.ofNat 64 bO)
        (arg s₀ 2 &&& BitVec.ofNat 32 15)) (arg s₀ 6) o = slotv s₂.mem (arg s₀ 6) o := fun h₁ h₂ =>
      slot_frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    refine ⟨hpre, hpub, ?_, ?_, ?_, by mems [e.rd], by mems [e.wr]⟩
    rotate_left
    · rw [← a 6 (by decide)]
      simp only [mem_setMem, mem_setReg, mem_arithFlags]
      exact e.saved.frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [← a 6 (by decide)]
      simp only [mem_setMem, mem_setReg, mem_arithFlags]
      exact e.frame.trans (hf.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)
    rw [← a 0 (by decide), ← a 1 (by decide), ← a 2 (by decide), ← a 4 (by decide), ← a 5 (by decide),
      ← a 6 (by decide), ← esp]
    refine ⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) ?_, ?_, ?_, ?_,
      Nat.mod_lt _ (by decide), (arg s₀ 5).isLt, ⟨?_, fd, d_sd.symm, d_dw, k_d⟩⟩
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact sl (by decide) (by decide)
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sl (by decide) (by decide)]
      exact e.slots (4, dO) (by simp)
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sl (by decide) (by decide)]
      rw [e.slots (5, nO) (by simp), VG.Proof.AesGcm.X86.ofNat_toNat32]
    · simp only [mem_setMem, mem_setReg, mem_arithFlags, slotv_eq, Mem.readW_writeW_self32]
      rw [hand]
    · mems [e.rd, e.wr, hrd]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 6 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [VG.Proof.AesGcm.X86.pubOf_esp h₁, VG.Proof.AesGcm.X86.pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    subst s
    have hp := hpre
    simp only [VG.Proof.AesGcm.X86.streamAadPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fa⟩ := hp
    have rA : Covers [argsR (s₀.gpr .esp) 7] (s₀.rd ++ s₀.wr) := by
      rw [VG.Proof.AesGcm.X86.argsR_eq, hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
    exact WP.mono (VG.Proof.AesGcm.X86.arg0_ok (VG.Proof.AesGcm.X86.argIn_of rA (by omega) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact VG.Proof.AesGcm.X86.pubOf_arg hpub (by decide), by rw [sp]; exact VG.Proof.AesGcm.X86.pubOf_esp hpub⟩

/-- The facts of the precondition the exit needs, in terms of the public data. -/
theorem aad_ret {p : BitVec 32 × (Nat → BitVec 32)} {s₀ : State} (h : VG.Proof.AesGcm.X86.streamAadPre s₀) (hp : VG.Proof.AesGcm.X86.pubOf 7 s₀ = p) :
    (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 1), 80⟩ ∧ (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 6), 2560⟩ ∧
      24 ≤ p.1.toNat := by
  simp only [VG.Proof.AesGcm.X86.streamAadPre] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, r_s, -, r_w, -, -, -, -, -, -, -, -, -, -, sp, -⟩ := h
  rw [VG.Proof.AesGcm.X86.pubOf_arg hp (i := 1) (by decide), VG.Proof.AesGcm.X86.pubOf_arg hp (i := 6) (by decide), VG.Proof.AesGcm.X86.pubOf_esp hp] at *
  exact ⟨r_s, r_w, sp⟩

theorem streamAad_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => VG.Proof.AesGcm.X86.streamAadPre s₀ ∧ VG.Proof.AesGcm.X86.pubOf 7 s₀ = p ∧ s = s₀) (streamAad vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamAadX86.post s₀ s') := by
  by_cases hex : ∃ s₀, VG.Proof.AesGcm.X86.streamAadPre s₀ ∧ VG.Proof.AesGcm.X86.pubOf 7 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : Lay (p.2 0) (p.2 1) (p.2 6) p.1 24 := by
    have := VG.Proof.AesGcm.X86.streamAad_lay hz
    rwa [VG.Proof.AesGcm.X86.pubOf_arg hzp (i := 0) (by decide), VG.Proof.AesGcm.X86.pubOf_arg hzp (i := 1) (by decide),
      VG.Proof.AesGcm.X86.pubOf_arg hzp (i := 6) (by decide), VG.Proof.AesGcm.X86.pubOf_esp hzp] at this
  obtain ⟨r_s, r_w, sp⟩ := VG.Proof.AesGcm.X86.aad_ret hz hzp
  rw [VG.Proof.AesGcm.X86.streamAad_eq]
  refine Pc.seq (VG.Proof.AesGcm.X86.aadEntry_pc p) (Pc.seq (Pc.lift (absorb_pc L (yo := 16) (.inr rfl) (Nat.mod_lt _ (by decide))
    (p.2 5).isLt) (fun _ s => s.mem) fun s₀ s h => ⟨h.abs, rfl⟩) ?_)
  refine Pc.taint [.ebp] (fun s₀ s ⟨s₁, h₁, ho, rd, wr⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  have he := ho.env
  have esp := VG.Proof.AesGcm.X86.pubOf_esp h₁.pub
  have a : ∀ i, i < 7 → arg s₀ i = p.2 i := fun i hi => VG.Proof.AesGcm.X86.pubOf_arg h₁.pub hi
  -- What the entry and `absorb` write.
  have fE := h₁.frame
  have fA := ho.frame
  have dE : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [(⟨w64 (p.2 6) + BitVec.ofNat 64 128, 2432⟩ : Region)],
      (⟨w64 (p.2 1) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
  have dA : ∀ {d k : Nat}, (d + k ≤ 16 ∨ (48 ≤ d ∧ d + k ≤ 80)) → ∀ r ∈ absFrame (p.2 1) (p.2 6) p.1 24 16,
      (⟨w64 (p.2 1) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega)).symm
  have hsv : SavedAt s.mem (p.2 6) s₀ := h₁.saved.frame fA fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
  have rA : ∀ r ∈ absFrame (p.2 1) (p.2 6) p.1 24 16, (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact r_s.sub_right (Lay.stSub (by decide))
    · exact r_s.sub_right (Lay.stSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact VG.Proof.AesGcm.X86.ret_below sp
  have rE : ∀ r ∈ [(⟨w64 (p.2 6) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact r_w.sub_right (Lay.wSub (by decide))
  have hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [esp, VG.Proof.AesGcm.X86.ret_kept fA rA, VG.Proof.AesGcm.X86.ret_kept fE rE]
  refine WP.mono (exit_ok he.ebp (by rw [he.esp, esp]) (covers_left he.wW) L.fw hsv hret)
    fun s' ⟨abi, m', _, _, _⟩ => ⟨abi, fun ciph iv x hr hl => ?_⟩
  have hp := h₁.pre
  simp only [VG.Proof.AesGcm.X86.streamAadPre] at hp
  obtain ⟨-, -, -, -, -, -, -, -, d_dw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fd, -, -, -⟩ := hp
  rw [a 4 (by decide), a 5 (by decide), a 6 (by decide)] at d_dw
  rw [a 4 (by decide), a 5 (by decide)] at fd
  rw [a 0 (by decide), a 1 (by decide)] at hr
  rw [a 0 (by decide), a 1 (by decide), a 4 (by decide), a 5 (by decide)]
  rw [Proof.Gcm.streamRepr_iff, VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.ofNat_lit] at hr ⊢
  obtain ⟨hj, ha, hc⟩ := hr
  have hH : Hk s₁.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0)) := by
    rw [VG.Proof.AesGcm.X86.ctxH_eq]
    exact blockAt_frame fE fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hD : bytesAt s₁.mem (w64 (p.2 4)) (p.2 5).toNat = bytesAt s₀.mem (w64 (p.2 4)) (p.2 5).toNat :=
    bytesAt_frame (p := w64 (p.2 4)) (n := (p.2 5).toNat) fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d_dw.sub_right (Lay.wSub (d := 128) (n := 2432) (by decide))) (by omega)
  have hx : x.length % 16 = (p.2 2).toNat % 16 := by rw [← a 2 (by decide), VG.Proof.AesGcm.X86.lo_mod16 hl]
  rw [Proof.Gcm.ghashInput_nil] at ha ⊢
  rw [m']
  refine ⟨?_, ?_, ?_⟩
  · rw [← hj]
    have e₁ := blockAt_frame fA (dA (d := 0) (k := 16) (.inl (by decide)))
    have e₂ := blockAt_frame fE (dE (d := 0) (k := 16) (by decide))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e₁ e₂
    rw [e₁, e₂]
  · have ha₁ : Absorbed s₁.mem (w64 (p.2 1) + BitVec.ofNat 64 16) (w64 (p.2 1) + BitVec.ofNat 64 32)
        (Hk s₁.mem (p.2 0)) x := by
      rw [hH]
      exact ha.congr (blockAt_frame fE (dE (by decide))) (bytesAt_frame fE (dE (d := 32) (k := x.length % 16) (by omega)) (by omega))
    have := ho.abs x hx ha₁
    rwa [hH, hD] at this
  · exact hc.congr (by rw [blockAt_frame fA (dA (.inr ⟨by decide, by decide⟩)),
      blockAt_frame fE (dE (by decide))]) (by rw [blockAt_frame fA (dA (.inr ⟨by decide, by decide⟩)),
      blockAt_frame fE (dE (by decide))])

theorem streamAad_correct (s : State) (hs : streamAadX86.pre s) :
    ∃ t s', Exec isa (streamAad vg.callees) s t s' ∧ abiPreserved s s' ∧ streamAadX86.post s s' :=
  (VG.Proof.AesGcm.X86.streamAad_pc (VG.Proof.AesGcm.X86.pubOf 7 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamAad_ct : ConstantTime isa streamAadX86.pre streamAadX86.pub (streamAad vg.callees) :=
  Pc.constantTime (VG.Proof.AesGcm.X86.pubOf 7) (fun _ _ _ _ h => VG.Proof.AesGcm.X86.pubOf_eq h) VG.Proof.AesGcm.X86.streamAad_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.TextAbsorb`. -/
section

/-!
# AES-GCM on x86: the ciphertext into GHASH (`textAbsorb`)

Untrusted: everything here is checked by Lean. `textAbsorb` absorbs the
`len` bytes at `data` (the ciphertext) into GHASH, after padding the
additional data if they are the first text (`textAbsorb_pc`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ghashInput)
open VG.Proof.Gcm (Absorbed)

theorem append_toNat32 (hi lo : BitVec 32) : (hi ++ lo).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

/-- No text so far: both words of its length are 0. -/
theorem nil_of_len {xl xh : BitVec 32} {c : List Byte} (ht : (xh ++ xl).toNat = c.length) :
    (xl ||| xh == 0) = decide (c = []) := by
  rw [VG.Proof.AesGcm.X86.append_toNat32] at ht
  by_cases hc : c = []
  · subst hc
    have h0 : xl = 0 ∧ xh = 0 :=
      ⟨BitVec.eq_of_toNat_eq (by simp at ht ⊢; omega), BitVec.eq_of_toNat_eq (by simp at ht ⊢; omega)⟩
    obtain ⟨rfl, rfl⟩ := h0
    rfl
  · have hl : c.length ≠ 0 := fun h => hc (List.eq_nil_of_length_eq_zero h)
    simp only [hc, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_or] at this
    obtain ⟨h1, h2⟩ := Nat.or_eq_zero_iff.mp this
    omega

/-- The regions `textAbsorb` writes. -/
abbrev taFrame (St W SP : BitVec 32) (K : Nat) : List Region :=
  [⟨w64 St + BitVec.ofNat 64 16, 32⟩, ⟨w64 W + BitVec.ofNat 64 96, 16⟩, wsR W, below SP K]

/-- The kept values `textAbsorb` reads. -/
structure TaSl (W : BitVec 32) (D : BitVec 32) (n : Nat) (al xl xh : BitVec 32) (m : Mem) : Prop where
  data : slotv m W dataO = D
  len : slotv m W lenO = BitVec.ofNat 32 n
  al : slotv m W alO = al
  xl : slotv m W xlO = xl
  xh : slotv m W xhO = xh

theorem TaSl.frame {W D : BitVec 32} {n : Nat} {al xl xh : BitVec 32} {m m' : Mem} (h : VG.Proof.AesGcm.X86.TaSl W D n al xl xh m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (keptR W).Disjoint r) : VG.Proof.AesGcm.X86.TaSl W D n al xl xh m' := by
  have k : ∀ {o}, 128 ≤ o → o + 4 ≤ 240 → slotv m' W o = slotv m W o := fun h₁ h₂ =>
    slot_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))
  exact ⟨by rw [k (by decide) (by decide)]; exact h.data, by rw [k (by decide) (by decide)]; exact h.len,
    by rw [k (by decide) (by decide)]; exact h.al, by rw [k (by decide) (by decide)]; exact h.xl,
    by rw [k (by decide) (by decide)]; exact h.xh⟩

/-- Before `textAbsorb`: `n` bytes of text at `D`. -/
structure TaIn (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) (al xl xh : BitVec 32) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  sl : VG.Proof.AesGcm.X86.TaSl W D n al xl xh s.mem
  nlt : n < 2 ^ 32
  data : DataOk St W SP K s D n

/-- What GHASH absorbs of a message with additional data `a` and text `c`, of the lengths kept. -/
abbrev TaLen (al ah xl xh : BitVec 32) (a c : List Byte) : Prop :=
  ah ++ al = BitVec.ofNat 64 a.length ∧ (xh ++ xl).toNat = c.length

/-- After `textAbsorb`, from `m₀`. -/
structure TaOut (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) (al ah xl xh : BitVec 32) (m₀ : Mem)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  frame : Frame (VG.Proof.AesGcm.X86.taFrame St W SP K) m₀ s.mem
  abs : ∀ a c, VG.Proof.AesGcm.X86.TaLen al ah xl xh a c →
    Absorbed m₀ (w64 St + BitVec.ofNat 64 16) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx) (ghashInput a c) →
    Absorbed s.mem (w64 St + BitVec.ofNat 64 16) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx)
      (ghashInput a (c ++ bytesAt m₀ (w64 D) n))

/-- After the padding of the additional data, if the text so far is empty. -/
structure TaMid (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) (al ah xl xh : BitVec 32) (m₀ : Mem)
    (s : State) : Prop where
  ta : VG.Proof.AesGcm.X86.TaIn Ctx St W SP K D n al xl xh s
  hk : Hk s.mem Ctx = Hk m₀ Ctx
  bytes : bytesAt s.mem (w64 D) n = bytesAt m₀ (w64 D) n
  frame : Frame (VG.Proof.AesGcm.X86.taFrame St W SP K) m₀ s.mem
  abs : ∀ a c, VG.Proof.AesGcm.X86.TaLen al ah xl xh a c →
    Absorbed m₀ (w64 St + BitVec.ofNat 64 16) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx) (ghashInput a c) →
    Absorbed s.mem (w64 St + BitVec.ofNat 64 16) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx)
      (if c = [] then a ++ zeros (padLen a.length) else ghashInput a c)

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K)
include L

theorem kept_taFrame : ∀ r ∈ VG.Proof.AesGcm.X86.taFrame St W SP K, (keptR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem ctx_taFrame : ∀ r ∈ VG.Proof.AesGcm.X86.taFrame St W SP K, (⟨w64 Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw.sub_right (Lay.wSub (by decide))
  · exact L.cw.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

omit L in
theorem data_taFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataOk St W SP K s D n) :
    ∀ r ∈ VG.Proof.AesGcm.X86.taFrame St W SP K, (⟨w64 D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.stk.symm

omit L in
theorem abs_taFrame {m m' : Mem} (h : Frame (absFrame St W SP K 16) m m') : Frame (VG.Proof.AesGcm.X86.taFrame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨wsR W, by simp, fun _ h => h⟩
    · exact ⟨below SP K, by simp, fun _ h => h⟩

omit L in
theorem t_taFrame {m m' : Mem} (h : Frame (tFrame St W SP K 16) m m') : Frame (VG.Proof.AesGcm.X86.taFrame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨wsR W, by simp, fun _ h => h⟩
    · exact ⟨below SP K, by simp, fun _ h => h⟩

omit L in
theorem pslot_taFrame {m m' : Mem} (h : Frame [pslotR W] m m') : Frame (VG.Proof.AesGcm.X86.taFrame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wsR W, by simp, pslot_ws W⟩

omit L in
theorem ta_keep {D : BitVec 32} {n : Nat} {al xl xh : BitVec 32} {s s' : State}
    (h : VG.Proof.AesGcm.X86.TaIn Ctx St W SP K D n al xl xh s) (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi)
    (hsp : s'.gpr .esp = s.gpr .esp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesGcm.X86.TaIn Ctx St W SP K D n al xl xh s' :=
  ⟨h.env.keep hbp hsi hsp hrd hwr (by rw [hm]), by rw [hm]; exact h.sl, h.nlt, h.data.of_eq hrd hwr⟩

theorem textAbsorb_pc {D : BitVec 32} {n : Nat} {al ah xl xh : BitVec 32} :
    Pc (fun (m₀ : Mem) s => VG.Proof.AesGcm.X86.TaIn Ctx St W SP K D n al xl xh s ∧ s.mem = m₀) (textAbsorb vg.callees)
      (VG.Proof.AesGcm.X86.TaOut Ctx St W SP K D n al ah xl xh ·) := by
  by_cases hnlt : n < 2 ^ 32
  swap
  · exact Pc.vacuous fun _ _ h => hnlt h.1.nlt
  refine Pc.seq (Q := fun m₀ s => (VG.Proof.AesGcm.X86.TaIn Ctx St W SP K D n al xl xh s ∧ s.mem = m₀) ∧ s.zf = some (decide (n = 0)))
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => WP.mono (VG.Proof.AesGcm.X86.test_ok L h.env .eax lenO (by decide) h.sl.len h.nlt)
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨VG.Proof.AesGcm.X86.ta_keep h (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) m rd wr,
          by rw [m, hm]⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (n = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨h.env, by rw [hm]; exact Frame.refl _ _,
      fun a c _ ha => ?_⟩
    rw [hm]; simpa [bytesAt] using ha
  have hn0 : n ≠ 0 := by simpa using hf
  -- Whether there is text so far.
  refine Pc.seq (Q := fun m₀ s => (VG.Proof.AesGcm.X86.TaIn Ctx St W SP K D n al xl xh s ∧ s.mem = m₀) ∧
      s.zf = some (xl ||| xh == 0))
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨h, hm⟩, _⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.env.ebp, h₂.1.1.env.ebp]) (by taint_decide)) ?_
  · have he := h.env
    have h1 := h.sl.xl; have h2 := h.sl.xh
    rw [slotv_eq] at h1 h2
    exact WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn', h1, h2], ⟨VG.Proof.AesGcm.X86.ta_keep h (by regs []) (by regs [])
      (by regs []) (by mems []) (by mems []) (by mems []), by mems []; exact hm⟩, by mems []⟩
  -- The padding of the additional data, before the first text.
  refine Pc.seq (Q := VG.Proof.AesGcm.X86.TaMid Ctx St W SP K D n al ah xl xh) ?_ ?_
  · refine Pc.ite (xl ||| xh == 0) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
    · refine Pc.seq (Q := fun m₀ s => VG.Proof.AesGcm.X86.TaIn Ctx St W SP K D n al xl xh s ∧
          slotv s.mem W bO = BitVec.ofNat 32 (al.toNat % 16) ∧ Frame [⟨w64 W + BitVec.ofNat 64 bO, 4⟩] m₀ s.mem)
        (Pc.taint [.ebp] (fun m₀ s ⟨⟨h, hm⟩, _⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.env.ebp, h₂.1.1.env.ebp]) (by taint_decide)) ?_
      · have he := h.env
        have h1 := h.sl.al
        rw [slotv_eq] at h1
        have hand := and15 al
        refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn, he.wIn', h1], ?_⟩
        have fb : Frame [⟨w64 W + BitVec.ofNat 64 bO, 4⟩] s.mem
            (s.mem.writeW (w64 W + BitVec.ofNat 64 bO) (al &&& BitVec.ofNat 32 15)) :=
          (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
        have dK : ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 bO, 4⟩ : Region)], (keptR W).Disjoint r := fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        refine ⟨⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by
            simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact slot_frame fb fun r hr =>
              (dK r hr).sub_left (Offset.sub _ (by decide) (by decide))),
          by simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact h.sl.frame fb dK, h.nlt,
          h.data.of_eq (by mems []) (by mems [])⟩, ?_, ?_⟩
        · simp only [mem_setMem, mem_setReg, mem_arithFlags, slotv_eq, Mem.readW_writeW_self32]; exact hand
        · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [← hm]; exact fb
      refine Pc.mono (Pc.lift (flush_pc L (yo := 16) (.inr rfl) (b := al.toNat % 16) (Nat.mod_lt _ (by decide)))
        (fun _ s => s.mem) fun m₀ s h => ⟨⟨h.1.env, h.2.1⟩, rfl⟩) (fun _ _ h => h)
        fun m₀ s' ⟨s, ⟨h, _, fb⟩, fo, rd, wr⟩ => ?_
      have dS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 bO, 4⟩ : Region)],
          (⟨w64 St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
      have kT : ∀ r ∈ tFrame St W SP K 16, (keptR W).Disjoint r := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w (by decide)).symm
      have hHs : Hk s.mem Ctx = Hk m₀ Ctx := blockAt_frame fb fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
      have hH' : Hk s'.mem Ctx = Hk s.mem Ctx := blockAt_frame fo.frame (ctx_tFrame L (.inr rfl))
      have dT : ∀ r ∈ tFrame St W SP K 16, (⟨w64 D, n⟩ : Region).Disjoint r := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact h.data.st.sub_right (Lay.stSub (by decide))
        · exact h.data.w.sub_right (Lay.wSub (by decide))
        · exact h.data.w.sub_right (Lay.wSub (by decide))
        · exact h.data.stk.symm
      have hfit := h.data.fit
      refine ⟨⟨fo.env, h.sl.frame fo.frame kT, h.nlt, h.data.of_eq rd wr⟩, by rw [hH', hHs], ?_, ?_,
        fun a c ⟨hl, hx⟩ ha => ?_⟩
      · rw [bytesAt_frame fo.frame dT (by omega), bytesAt_frame fb (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.data.w.sub_right (Lay.wSub (by decide))) (by omega)]
      · exact (fb.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩).trans (VG.Proof.AesGcm.X86.t_taFrame fo.frame)
      · have hc : c = [] := by
          have := VG.Proof.AesGcm.X86.nil_of_len hx; rw [ht] at this; simpa using this.symm
        subst hc
        simp only [↓reduceIte]
        rw [Proof.Gcm.ghashInput_nil] at ha
        have ha₁ : Absorbed s.mem (w64 St + BitVec.ofNat 64 16) (w64 St + BitVec.ofNat 64 32) (Hk s.mem Ctx) a := by
          rw [hHs]
          exact ha.congr (blockAt_frame fb (dS (by decide))) (bytesAt_frame fb (dS (d := 32) (k := a.length % 16)
            (by omega)) (by omega))
        have := fo.abs a (VG.Proof.AesGcm.X86.lo_mod16 hl).symm ha₁
        rwa [hHs] at this
    · refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨h, by rw [hm], by rw [hm],
        by rw [hm]; exact Frame.refl _ _, fun a c ⟨_, hx⟩ ha => ?_⟩
      have hc : c ≠ [] := by
        have := VG.Proof.AesGcm.X86.nil_of_len hx; rw [hf] at this; simpa using this.symm
      simp only [hc, ↓reduceIte]; rw [hm]; exact ha
  -- The text, as the piece `absorb` takes it.
  refine Pc.seq (Q := fun m₀ s => ∃ s₃, VG.Proof.AesGcm.X86.TaMid Ctx St W SP K D n al ah xl xh m₀ s₃ ∧
      AbsIn Ctx St W SP K D n (xl.toNat % 16) s ∧ Frame [pslotR W] s₃.mem s.mem ∧ s.rd = s₃.rd ∧ s.wr = s₃.wr)
    (Pc.taint [.ebp] (fun m₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ta.env.ebp, h₂.ta.env.ebp]) (by taint_decide)) ?_
  · have he := h.ta.env
    have h1 := h.ta.sl.data; have h2 := h.ta.sl.len; have h3 := h.ta.sl.xl
    rw [slotv_eq] at h1 h2 h3
    simp only [dataO, lenO, xlO] at h1 h2 h3
    have hand := and15 xl
    refine WP.of_runBlock ⟨_, by xrun [setText, he.ebp, L.aW, he.wIn, he.wIn', h1, h2, h3], s, h, ?_⟩
    refine ⟨⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems []), ?_, ?_, ?_,
        Nat.mod_lt _ (by decide), h.ta.nlt, h.ta.data.of_eq (by mems []) (by mems [])⟩, ?_, by mems [], by mems []⟩
    rotate_left 3
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]
      exact pslot_write (pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide)
        (by decide) _) (by decide) (by decide) _
    · mems [slotv_eq]
    · mems [slotv_eq, h2]
    · mems [slotv_eq, h3]; rw [hand]
  refine Pc.mono (Pc.lift (absorb_pc L (yo := 16) (.inr rfl) (b := xl.toNat % 16) (Nat.mod_lt _ (by decide)) hnlt)
    (fun _ s => s.mem) fun m₀ s ⟨_, _, h, _⟩ => ⟨h, rfl⟩) (fun _ _ h => h)
    fun m₀ s' ⟨s, ⟨s₃, h₃, _, fr, _, _⟩, ao, _, _⟩ => ?_
  have hd := h₃.ta.data
  have hfit := hd.fit
  have hD : bytesAt s.mem (w64 D) n = bytesAt m₀ (w64 D) n := by
    rw [bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd.w.sub_right (Lay.wSub (by decide))) (by omega),
      h₃.bytes]
  have hHs : Hk s.mem Ctx = Hk m₀ Ctx := by
    rw [← h₃.hk]; exact blockAt_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  refine ⟨ao.env, (h₃.frame.trans (VG.Proof.AesGcm.X86.pslot_taFrame fr)).trans (VG.Proof.AesGcm.X86.abs_taFrame ao.frame), fun a c ⟨hl, hx⟩ ha => ?_⟩
  have hx' : (if c = [] then a ++ zeros (padLen a.length) else ghashInput a c).length % 16 = xl.toNat % 16 := by
    have e := VG.Proof.AesGcm.X86.append_toNat32 xh xl
    split
    · next hc =>
      subst hc
      simp only [List.length_nil] at hx
      rw [List.length_append, Proof.Gcm.length_zeros, Proof.Gcm.length_pad_mod]
      omega
    · next hc =>
      rw [Proof.Gcm.ghashInput_of_ne hc]
      simp only [List.length_append, Proof.Gcm.length_zeros]
      have := Proof.Gcm.length_pad_mod a.length
      omega
  have := ao.abs _ hx' (by rw [hHs]; exact absorbed_pslot fr (h₃.abs a c ⟨hl, hx⟩ ha) L (.inr rfl))
  rw [hHs, hD, ← Proof.Gcm.ghashInput_append a c _ (by
    intro h0; have := congrArg List.length h0; rw [length_bytesAt] at this; exact hn0 this)] at this
  exact this

end

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.StreamCrypt`. -/
section

/-!
# AES-GCM on x86: the entry of `stream_encrypt` and `stream_decrypt`

Untrusted: everything here is checked by Lean. What the precondition
gives (`CrPure`), the entry (`crEntry_pc`), the text as `crypt` takes it
(`setText_ok`) and as `textAbsorb` takes it.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph)

abbrev crKeeps : List (Nat × Nat) :=
  [(0, ctxO), (1, roundsO), (3, alO), (4, ahO), (5, xlO), (6, xhO), (7, dataO), (8, lenO)]

/-- The facts of the precondition about the public data `p` alone. -/
structure CrPure (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  lay : Lay (p.2 0) (p.2 2) (p.2 9) p.1 28
  fd : (p.2 7).toNat + (p.2 8).toNat ≤ 2 ^ 32
  dctx : (⟨w64 (p.2 0), 256⟩ : Region).Disjoint ⟨w64 (p.2 7), (p.2 8).toNat⟩
  dst : (⟨w64 (p.2 7), (p.2 8).toNat⟩ : Region).Disjoint ⟨w64 (p.2 2), 80⟩
  dw : (⟨w64 (p.2 7), (p.2 8).toNat⟩ : Region).Disjoint ⟨w64 (p.2 9), 2560⟩
  dstk : (below p.1 28).Disjoint ⟨w64 (p.2 7), (p.2 8).toNat⟩
  r_s : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 2), 80⟩
  r_d : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 7), (p.2 8).toNat⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 9), 2560⟩
  sp : 28 ≤ p.1.toNat
  rounds : (p.2 1).toNat = 10 ∨ (p.2 1).toNat = 12 ∨ (p.2 1).toNat = 14

theorem crPure_of {p : BitVec 32 × (Nat → BitVec 32)} {s : State} (h : VG.Proof.AesGcm.X86.streamCryptPre s) (hp : VG.Proof.AesGcm.X86.pubOf 10 s = p) :
    VG.Proof.AesGcm.X86.CrPure p := by
  simp only [VG.Proof.AesGcm.X86.streamCryptPre] at h
  obtain ⟨-, -, d_cs, d_cd, d_cw, -, d_sd, d_sw, -, d_dw, -, -, -, r_s, r_d, r_w, -, k_c, k_s, k_d, k_w, -,
    fc, fs, fd, fw, sp, -, hR⟩ := h
  rw [VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.below_eq sp] at k_c k_s k_d k_w
  have a0 := VG.Proof.AesGcm.X86.pubOf_arg hp (i := 0) (by decide); have a1 := VG.Proof.AesGcm.X86.pubOf_arg hp (i := 1) (by decide)
  have a2 := VG.Proof.AesGcm.X86.pubOf_arg hp (i := 2) (by decide); have a7 := VG.Proof.AesGcm.X86.pubOf_arg hp (i := 7) (by decide)
  have a8 := VG.Proof.AesGcm.X86.pubOf_arg hp (i := 8) (by decide); have a9 := VG.Proof.AesGcm.X86.pubOf_arg hp (i := 9) (by decide)
  have e := VG.Proof.AesGcm.X86.pubOf_esp hp
  simp only [VG.Proof.AesGcm.X86.roundsOk] at hR
  simp only [a0, a1, a2, a7, a8, a9, e] at d_cs d_cd d_cw d_sd d_sw d_dw r_s r_d r_w k_c k_s k_d k_w fc fs fd fw sp hR
  exact ⟨⟨fc, fs, fw, by decide, Nat.le_refl _, sp, d_cs, d_cw, d_sw.sub_right (Region.sub_prefix (by decide)),
    d_sw.sub_right (Lay.wSub (by decide)), k_c, k_s, k_w⟩, fd, d_cd, d_sd.symm, d_dw, k_d, r_s, r_d, r_w, sp, hR⟩

/-- After the entry of `stream_encrypt` or `stream_decrypt`. -/
structure CEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : VG.Proof.AesGcm.X86.streamCryptPre s₀
  pub : VG.Proof.AesGcm.X86.pubOf 10 s₀ = p
  env : Env (p.2 0) (p.2 2) (p.2 9) p.1 s
  rounds : RoundsAt s.mem (p.2 9) (p.2 1).toNat
  ta : VG.Proof.AesGcm.X86.TaSl (p.2 9) (p.2 7) (p.2 8).toNat (p.2 3) (p.2 5) (p.2 6) s.mem
  ah : slotv s.mem (p.2 9) ahO = p.2 4
  saved : SavedAt s.mem (p.2 9) s₀
  frame : Frame [⟨w64 (p.2 9) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem crEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => VG.Proof.AesGcm.X86.streamCryptPre s₀ ∧ VG.Proof.AesGcm.X86.pubOf 10 s₀ = p ∧ s = s₀)
      (entry 9 (([.mov .esi (argOp 2)] : List Instr) ++ (crKeeps.flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ []))) (VG.Proof.AesGcm.X86.CEnt p) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have hp := hpre
    simp only [VG.Proof.AesGcm.X86.streamCryptPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, d_wa, -, -, -, -, -, -, -, -, -, -, -, -, -, fw, -, fa, hR⟩ := hp
    have a : ∀ i, i < 10 → arg s₀ i = p.2 i := fun i hi => VG.Proof.AesGcm.X86.pubOf_arg hpub hi
    have esp := VG.Proof.AesGcm.X86.pubOf_esp hpub
    have wW : Covers [⟨w64 (arg s₀ 9), 2560⟩] s₀.wr := by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 10] (s₀.rd ++ s₀.wr) := by
      rw [VG.Proof.AesGcm.X86.argsR_eq, hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 10).Disjoint ⟨w64 (arg s₀ 9), 2560⟩ := by rw [VG.Proof.AesGcm.X86.argsR_eq]; exact d_wa.symm
    refine entry_ok VG.Proof.AesGcm.X86.crKeeps [] (by decide) (by decide) (by decide) (by decide) rfl rfl wW rA aw (by omega) fw
      fun s₂ e => ?_
    have he : Env (arg s₀ 0) (arg s₀ 2) (arg s₀ 9) (s₀.gpr .esp) s₂ :=
      ⟨e.ebp, e.esi, e.esp, by rw [e.rd, e.wr, hrd]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp),
        by rw [e.wr, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), by rw [e.wr]; exact wW,
        e.slots (0, ctxO) (by simp)⟩
    refine ⟨s₂, rfl, hpre, hpub, ?_, ?_, ?_, ?_, ?_, ?_, e.rd, e.wr⟩
    · rw [← a 0 (by decide), ← a 2 (by decide), ← a 9 (by decide), ← esp]; exact he
    · rw [← a 1 (by decide), ← a 9 (by decide)]
      exact ⟨by rw [e.slots (1, roundsO) (by simp), VG.Proof.AesGcm.X86.ofNat_toNat32], hR⟩
    · rw [← a 3 (by decide), ← a 5 (by decide), ← a 6 (by decide), ← a 7 (by decide), ← a 8 (by decide),
        ← a 9 (by decide)]
      exact ⟨e.slots (7, dataO) (by simp), by rw [e.slots (8, lenO) (by simp), VG.Proof.AesGcm.X86.ofNat_toNat32],
        e.slots (3, alO) (by simp), e.slots (5, xlO) (by simp), e.slots (6, xhO) (by simp)⟩
    · rw [← a 4 (by decide), ← a 9 (by decide)]; exact e.slots (4, ahO) (by simp)
    · rw [← a 9 (by decide)]; exact e.saved
    · rw [← a 9 (by decide)]; exact e.frame
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 9 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [VG.Proof.AesGcm.X86.pubOf_esp h₁, VG.Proof.AesGcm.X86.pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    subst s
    have hp := hpre
    simp only [VG.Proof.AesGcm.X86.streamCryptPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fa, -⟩ := hp
    have rA : Covers [argsR (s₀.gpr .esp) 10] (s₀.rd ++ s₀.wr) := by
      rw [VG.Proof.AesGcm.X86.argsR_eq, hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
    exact WP.mono (VG.Proof.AesGcm.X86.arg0_ok (VG.Proof.AesGcm.X86.argIn_of rA (by omega) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact VG.Proof.AesGcm.X86.pubOf_arg hpub (by decide), by rw [sp]; exact VG.Proof.AesGcm.X86.pubOf_esp hpub⟩

/-- `setText`: the text as the pieces take it. -/
theorem setText_ok {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K) {D : BitVec 32} {n : Nat}
    {al xl xh : BitVec 32} {s : State} (he : Env Ctx St W SP s) (hs : VG.Proof.AesGcm.X86.TaSl W D n al xl xh s.mem) :
    ∃ s', runBlock isa setText s = some s' ∧ slotv s'.mem W dO = D ∧ slotv s'.mem W nO = BitVec.ofNat 32 n ∧
      slotv s'.mem W bO = BitVec.ofNat 32 (xl.toNat % 16) ∧ Frame [pslotR W] s.mem s'.mem ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h1 := hs.data; have h2 := hs.len; have h3 := hs.xl
  rw [slotv_eq] at h1 h2 h3
  simp only [dataO, lenO, xlO] at h1 h2 h3
  have hand := and15 xl
  refine ⟨_, by xrun [setText, he.ebp, L.aW, he.wIn, he.wIn', h1, h2, h3], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems [slotv_eq]
  · mems [slotv_eq, h2]
  · mems [slotv_eq, h3]; rw [hand]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    exact pslot_write (pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide)
      (by decide) _) (by decide) (by decide) _
  · regs []
  · regs []
  · regs []
  all_goals rfl

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.StreamFinish`. -/
section

/-!
# AES-GCM on x86: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. The entry, the tag
(`finTag 0`), its copy to `tag` (`tagOut 0`) and the exit, as one `Pc`
(`streamFinish_pc`): correct (`streamFinish_correct`) and constant time
(`streamFinish_ct`). The entry is shared with `vg_aes_gcm_stream_verify`
(`finEntry_pc`), whose `W` is its last argument too: the pieces find it at 7
in the public data (`pubSw`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph)

abbrev finKeeps : List (Nat × Nat) := [(0, ctxO), (1, roundsO), (3, alO), (4, ahO), (5, xlO), (6, xhO)]

theorem streamFinish_eq : (streamFinish vg.callees) = .seq (entry 8 (([.mov .esi (argOp 2)] : List Instr) ++
    ((VG.Proof.AesGcm.X86.finKeeps ++ [(7, tpO)]).flatMap (fun (p : Nat × Nat) => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ [])))
    (.seq (finTag vg.callees 0) (.seq (tagOut 0) (.block restore))) := rfl

/-- What the precondition of `finish` and `verify` (with `nA` arguments, `W`
the last, `w`) gives. -/
structure FinPre (nA w : Nat) (s : State) : Prop where
  cR : Covers [⟨w64 (arg s 0), 256⟩] (s.rd ++ s.wr)
  sW : Covers [⟨w64 (arg s 2), 80⟩] s.wr
  wW : Covers [⟨w64 (arg s w), 2560⟩] s.wr
  aR : Covers [⟨argAddr s 0, 4 * nA⟩] (s.rd ++ s.wr)
  cs : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s 2), 80⟩
  cw : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  sw : (⟨w64 (arg s 2), 80⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  wa : (⟨w64 (arg s w), 2560⟩ : Region).Disjoint ⟨argAddr s 0, 4 * nA⟩
  r_s : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 2), 80⟩
  r_w : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  k_c : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 0), 256⟩
  k_s : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 2), 80⟩
  k_w : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s w), 2560⟩
  fc : (arg s 0).toNat + 256 ≤ 2 ^ 32
  fs : (arg s 2).toNat + 80 ≤ 2 ^ 32
  fw : (arg s w).toNat + 2560 ≤ 2 ^ 32
  sp : 28 ≤ (s.gpr .esp).toNat
  fa : (s.gpr .esp).toNat + 4 + 4 * nA ≤ 2 ^ 32
  rounds : VG.Proof.AesGcm.X86.roundsOk s 1

theorem finPre_of {s : State} (h : VG.Proof.AesGcm.X86.finPre s) : VG.Proof.AesGcm.X86.FinPre 9 8 s := by
  simp only [VG.Proof.AesGcm.X86.finPre] at h
  obtain ⟨hrd, hwr, d_cs, -, d_cw, -, -, d_sw, -, -, -, d_wa, -, r_s, -, r_w, -, k_c, k_s, -, k_w, -, fc, fs, -, fw,
    sp, fa, hR⟩ := h
  rw [VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.below_eq sp] at k_c k_s k_w
  exact ⟨by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp),
    by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), d_cs, d_cw, d_sw,
    d_wa, r_s, r_w, k_c, k_s, k_w, fc, fs, fw, sp, by omega, hR⟩

/-- The tag `finish` writes. -/
theorem finPre_tag {s : State} (h : VG.Proof.AesGcm.X86.finPre s) : Covers [⟨w64 (arg s 7), 16⟩] s.wr ∧
    (arg s 7).toNat + 16 ≤ 2 ^ 32 ∧ (⟨w64 (arg s 7), 16⟩ : Region).Disjoint ⟨w64 (arg s 8), 2560⟩ ∧
    (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 7), 16⟩ := by
  simp only [VG.Proof.AesGcm.X86.finPre] at h
  obtain ⟨-, hwr, -, -, -, -, -, -, -, d_tw, -, -, -, -, r_t, -, -, -, -, -, -, -, -, -, ft, -, -, -, -⟩ := h
  exact ⟨by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), ft, d_tw, r_t⟩

theorem verifyPre_of {s : State} (h : VG.Proof.AesGcm.X86.verifyPre s) : VG.Proof.AesGcm.X86.FinPre 10 9 s := by
  simp only [VG.Proof.AesGcm.X86.verifyPre] at h
  obtain ⟨hrd, hwr, d_cs, d_cw, -, -, -, -, d_sw, -, d_wa, -, r_s, -, r_w, -, k_c, k_s, -, k_w, -, fc, fs, -, fw,
    sp, fa, hR⟩ := h
  rw [VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.below_eq sp] at k_c k_s k_w
  exact ⟨by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp),
    by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), d_cs, d_cw, d_sw,
    d_wa, r_s, r_w, k_c, k_s, k_w, fc, fs, fw, sp, by omega, hR⟩

/-- The tag `verify` reads. -/
theorem verifyPre_tag {s : State} (h : VG.Proof.AesGcm.X86.verifyPre s) :
    Covers [⟨w64 (arg s 7), (arg s 8).toNat⟩] (s.rd ++ s.wr) ∧ (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32 ∧
      (⟨w64 (arg s 7), (arg s 8).toNat⟩ : Region).Disjoint ⟨w64 (arg s 9), 2560⟩ := by
  simp only [VG.Proof.AesGcm.X86.verifyPre] at h
  obtain ⟨hrd, hwr, -, -, -, -, d_tw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ft, -, -, -, -⟩ := h
  exact ⟨by rw [hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), ft, d_tw⟩

theorem FinPre.lay {nA w : Nat} {s : State} (h : VG.Proof.AesGcm.X86.FinPre nA w s) :
    Lay (arg s 0) (arg s 2) (arg s w) (s.gpr .esp) 28 :=
  ⟨h.fc, h.fs, h.fw, by decide, Nat.le_refl _, h.sp, h.cs, h.cw, h.sw.sub_right (Region.sub_prefix (by decide)),
    h.sw.sub_right (Lay.wSub (by decide)), h.k_c, h.k_s, h.k_w⟩

/-- The layout of `finish` and `verify`, for the public data `p` (`W` at 7). -/
structure FinL (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  L : Lay (p.2 0) (p.2 2) (p.2 7) p.1 28
  r_s : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 2), 80⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 7), 2560⟩
  rounds : (p.2 1).toNat = 10 ∨ (p.2 1).toNat = 12 ∨ (p.2 1).toNat = 14

theorem FinPre.fl {nA w : Nat} {s : State} (h : VG.Proof.AesGcm.X86.FinPre nA w s) (hw : nA = w + 1) (h8 : 8 ≤ w)
    {p : BitVec 32 × (Nat → BitVec 32)} (hp : VG.Proof.AesGcm.X86.pubSw nA 7 s = p) : VG.Proof.AesGcm.X86.FinL p := by
  have a : ∀ i, i < 7 → arg s i = p.2 i := fun i hi => VG.Proof.AesGcm.X86.pubSw_arg hp (by omega) (by omega) (by omega)
  have aW : arg s w = p.2 7 := VG.Proof.AesGcm.X86.pubSw_W hp (by omega) hw
  have esp := VG.Proof.AesGcm.X86.pubSw_esp hp
  have L := h.lay
  have r_s := h.r_s
  have r_w := h.r_w
  have hR := h.rounds
  rw [a 0 (by decide), a 2 (by decide), aW, esp] at L
  rw [esp, a 2 (by decide)] at r_s
  rw [esp, aW] at r_w
  rw [VG.Proof.AesGcm.X86.roundsOk, a 1 (by decide)] at hR
  exact ⟨L, r_s, r_w, hR⟩

/-- After the entry of `finish` or `verify`. -/
structure FinEnt (nA w : Nat) (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : VG.Proof.AesGcm.X86.FinPre nA w s₀
  pub : VG.Proof.AesGcm.X86.pubSw nA 7 s₀ = p
  fin : VG.Proof.AesGcm.X86.FinIn (p.2 0) (p.2 2) (p.2 7) p.1 (p.2 1).toNat (p.2 3) (p.2 4) (p.2 5) (p.2 6) s
  saved : SavedAt s.mem (p.2 7) s₀
  frame : Frame [⟨w64 (p.2 7) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The entry of `finish` and `verify`, copying also the arguments `ex`. -/
theorem finEntry_pc (nA w : Nat) (hw : nA = w + 1) (h8 : 8 ≤ w) (ex : List (Nat × Nat))
    (hex : ∀ q ∈ VG.Proof.AesGcm.X86.finKeeps ++ ex, q.1 < nA ∧ 144 ≤ q.2 ∧ q.2 + 4 ≤ 2560 ∧ q.2 % 4 = 0)
    (hnd : ((VG.Proof.AesGcm.X86.finKeeps ++ ex).map (·.2)).Nodup) (Pre : State → Prop) (hPre : ∀ s, Pre s → VG.Proof.AesGcm.X86.FinPre nA w s)
    (p : BitVec 32 × (Nat → BitVec 32)) {hh₀ hh : Taint.Hint VG.X86.taint.T}
    (ht₀ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .eax (argOp w)]) hh₀).isSome = true)
    (ht : (VG.X86.taint.check (τr [.eax, .esp]) (.block (saveAt ++ (([.mov .esi (argOp 2)] : List Instr) ++
      ((VG.Proof.AesGcm.X86.finKeeps ++ ex).flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ [])))) hh).isSome = true) :
    Pc (fun (s₀ : State) s => Pre s₀ ∧ VG.Proof.AesGcm.X86.pubSw nA 7 s₀ = p ∧ s = s₀)
      (entry w (([.mov .esi (argOp 2)] : List Instr) ++ ((VG.Proof.AesGcm.X86.finKeeps ++ ex).flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ [])))
      (fun s₀ s => VG.Proof.AesGcm.X86.FinEnt nA w p s₀ s ∧ (∀ q ∈ ex, slotv s.mem (p.2 7) q.2 = arg s₀ q.1) ∧ Pre s₀) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have h := hPre _ hpre
    have L := h.lay
    have a : ∀ i, i < 7 → arg s₀ i = p.2 i := fun i hi => VG.Proof.AesGcm.X86.pubSw_arg hpub (by omega) (by omega) (by omega)
    have aW : arg s₀ w = p.2 7 := VG.Proof.AesGcm.X86.pubSw_W hpub (by omega) hw
    have esp := VG.Proof.AesGcm.X86.pubSw_esp hpub
    have rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by rw [VG.Proof.AesGcm.X86.argsR_eq]; exact h.aR
    have aw : (argsR (s₀.gpr .esp) nA).Disjoint ⟨w64 (arg s₀ w), 2560⟩ := by rw [VG.Proof.AesGcm.X86.argsR_eq]; exact h.wa.symm
    refine entry_ok (VG.Proof.AesGcm.X86.finKeeps ++ ex) [] (by omega) (by omega) hex hnd rfl rfl h.wW rA aw h.fa h.fw fun s₂ e => ?_
    have he : Env (arg s₀ 0) (arg s₀ 2) (arg s₀ w) (s₀.gpr .esp) s₂ :=
      ⟨e.ebp, e.esi, e.esp, by rw [e.rd, e.wr]; exact h.cR, by rw [e.wr]; exact h.sW, by rw [e.wr]; exact h.wW,
        e.slots (0, ctxO) (by simp)⟩
    refine ⟨s₂, rfl, ⟨h, hpub, ?_, ?_, ?_, e.rd, e.wr⟩, fun q hq => by rw [← aW]; exact e.slots q (by simp [hq]),
      hpre⟩
    · rw [← a 0 (by omega), ← a 1 (by omega), ← a 2 (by omega), ← a 3 (by omega), ← a 4 (by omega),
        ← a 5 (by omega), ← a 6 (by omega), ← aW, ← esp]
      exact ⟨he, e.slots (3, alO) (by simp), e.slots (4, ahO) (by simp), e.slots (5, xlO) (by simp),
        e.slots (6, xhO) (by simp), by rw [e.slots (1, roundsO) (by simp), VG.Proof.AesGcm.X86.ofNat_toNat32], h.rounds⟩
    · rw [← aW]; exact e.saved
    · rw [← aW]; exact e.frame
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 7 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [VG.Proof.AesGcm.X86.pubSw_esp h₁, VG.Proof.AesGcm.X86.pubSw_esp h₂]) ht₀) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) ht)
    subst s
    have h := hPre _ hpre
    have rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by rw [VG.Proof.AesGcm.X86.argsR_eq]; exact h.aR
    exact WP.mono (VG.Proof.AesGcm.X86.arg0_ok (VG.Proof.AesGcm.X86.argIn_of rA h.fa (by omega))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact VG.Proof.AesGcm.X86.pubSw_W hpub (by omega) hw, by rw [sp]; exact VG.Proof.AesGcm.X86.pubSw_esp hpub⟩

/-- Our caller's registers, outside the regions the tag is computed in. -/
theorem saved_tagFrame {Ctx St W SP : BitVec 32} (L : Lay Ctx St W SP 28) :
    ∀ r ∈ VG.Proof.AesGcm.X86.tagFrame St W SP 0, (savedR W).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- The return address, outside the regions the tag is computed in. -/
theorem ret_tagFrame {p : BitVec 32 × (Nat → BitVec 32)} (FL : VG.Proof.AesGcm.X86.FinL p) :
    ∀ r ∈ VG.Proof.AesGcm.X86.tagFrame (p.2 2) (p.2 7) p.1 0, (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact FL.r_s.sub_right (Region.sub_prefix (by decide))
  · exact FL.r_w.sub_right (Lay.wSub (by decide))
  · exact FL.r_w.sub_right (Lay.wSub (by decide))
  · exact FL.r_w.sub_right (Lay.wSub (by decide))
  · exact VG.Proof.AesGcm.X86.ret_below FL.L.sp

/-- The exit of `finish` and `verify`, after the pieces wrote within `rs`,
apart from our caller's registers and the return address. -/
theorem fin_exit {nA w : Nat} {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ s : State} (h₁ : VG.Proof.AesGcm.X86.FinEnt nA w p s₀ s₁)
    (FL : VG.Proof.AesGcm.X86.FinL p) (he : Env (p.2 0) (p.2 2) (p.2 7) p.1 s) {rs : List Region} (hf : Frame rs s₁.mem s.mem)
    (hS : ∀ r ∈ rs, (savedR (p.2 7)).Disjoint r) (hR : ∀ r ∈ rs, (⟨w64 p.1, 4⟩ : Region).Disjoint r) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .eax = s.gpr .eax := by
  have esp := VG.Proof.AesGcm.X86.pubSw_esp h₁.pub
  have hsv : SavedAt s.mem (p.2 7) s₀ := h₁.saved.frame hf hS
  have rE : ∀ r ∈ [(⟨w64 (p.2 7) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact FL.r_w.sub_right (Lay.wSub (by decide))
  have hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [esp, VG.Proof.AesGcm.X86.ret_kept hf hR, VG.Proof.AesGcm.X86.ret_kept h₁.frame rE]
  exact WP.mono (exit_ok he.ebp (by rw [he.esp, esp]) (covers_left he.wW) FL.L.fw hsv hret)
    fun s' ⟨abi, m', ax, _, _⟩ => ⟨abi, m', ax⟩

/-- The streaming state and the key context, as the pieces see them after the entry. -/
theorem fin_repr {nA w : Nat} {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ : State} (h₁ : VG.Proof.AesGcm.X86.FinEnt nA w p s₀ s₁)
    (L : Lay (p.2 0) (p.2 2) (p.2 7) p.1 28) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {iv a c : List Byte}
    (hr : StreamRepr s₀.mem (w64 (p.2 2)) (ctxCiph s₀.mem (w64 (p.2 0)) R) (ctxH s₀.mem (w64 (p.2 0))) iv a c) :
    StreamRepr s₁.mem (w64 (p.2 2)) (ciphOf s₁.mem (p.2 0) R) (Hk s₁.mem (p.2 0)) iv a c ∧
      ciphOf s₁.mem (p.2 0) R = ctxCiph s₀.mem (w64 (p.2 0)) R ∧ Hk s₁.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0)) := by
  have hC : ciphOf s₁.mem (p.2 0) R = ctxCiph s₀.mem (w64 (p.2 0)) R :=
    ciph_frame h₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide))) hR
  have hH : Hk s₁.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0)) := by
    rw [VG.Proof.AesGcm.X86.ctxH_eq]
    exact blockAt_frame h₁.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  refine ⟨?_, hC, hH⟩
  rw [hC, hH]
  exact VG.Proof.AesGcm.X86.streamRepr_frame h₁.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    simpa using L.st_w (a := 0) (n := 80) (d := 128) (k := 2432) (by decide) (.inr ⟨by decide, by decide⟩)) hr

/-- A word of `W` outside the regions the tag is computed in. -/
theorem slot_tagFrame {Ctx St W SP : BitVec 32} (L : Lay Ctx St W SP 28) {m m' : Mem}
    (hf : Frame (VG.Proof.AesGcm.X86.tagFrame St W SP 0) m m') {o : Nat} (h₁ : 128 ≤ o) (h₂ : o + 4 ≤ 240) :
    slotv m' W o = slotv m W o := by
  rw [slotv_eq, slotv_eq]
  refine slot_frame hf fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · have := (L.st_w (a := 0) (n := 32) (d := o) (k := 4) (by decide) (.inr ⟨by omega, by omega⟩)).symm
    rwa [BitVec.add_zero] at this
  · exact Lay.w_w (d := 96) (k := 16) (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (d := 0) (k := 16) (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (d := 240) (k := 2320) (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem streamFinish_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => VG.Proof.AesGcm.X86.finPre s₀ ∧ VG.Proof.AesGcm.X86.pubSw 9 7 s₀ = p ∧ s = s₀) (streamFinish vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamFinishX86.post s₀ s') := by
  by_cases hex : ∃ s₀, VG.Proof.AesGcm.X86.finPre s₀ ∧ VG.Proof.AesGcm.X86.pubSw 9 7 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have FL : VG.Proof.AesGcm.X86.FinL p := (VG.Proof.AesGcm.X86.finPre_of hz).fl rfl (by decide) hzp
  have L := FL.L
  have hR := FL.rounds
  obtain ⟨-, fT, tw, rt⟩ := VG.Proof.AesGcm.X86.finPre_tag hz
  rw [VG.Proof.AesGcm.X86.pubSw_last hzp (m := 8) (by decide) rfl] at fT
  rw [VG.Proof.AesGcm.X86.pubSw_last hzp (m := 8) (by decide) rfl, VG.Proof.AesGcm.X86.pubSw_W hzp (m := 8) (by decide) rfl] at tw
  rw [VG.Proof.AesGcm.X86.pubSw_last hzp (m := 8) (by decide) rfl, VG.Proof.AesGcm.X86.pubSw_esp hzp] at rt
  rw [VG.Proof.AesGcm.X86.streamFinish_eq]
  refine Pc.seq (VG.Proof.AesGcm.X86.finEntry_pc 9 8 rfl (by decide) [(7, tpO)] (by decide) (by decide) VG.Proof.AesGcm.X86.finPre (fun _ h => VG.Proof.AesGcm.X86.finPre_of h) p
    (by taint_decide) (by taint_decide)) (Pc.seq (Pc.lift (VG.Proof.AesGcm.X86.finTag_pc L (o := 0) (.inl rfl)) (fun _ s => s.mem)
      fun s₀ s h => ⟨h.1.fin, rfl⟩) ?_)
  -- The tag copied to `tag`.
  refine Pc.seq (Pc.of (I := fun s => VG.Proof.AesGcm.X86.WEnv (p.2 7) s ∧ slotv s.mem (p.2 7) tpO = p.2 8 ∧
      Covers [⟨w64 (p.2 8), 16⟩] s.wr)
    (R := fun s s' => bytesAt s'.mem (w64 (p.2 8)) 16 = bytesAt s.mem (w64 (p.2 7) + BitVec.ofNat 64 0) 16 ∧
      Frame [⟨w64 (p.2 8), 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (fun s hs => VG.Proof.AesGcm.X86.tagOut_ok hs.1 (by decide) hs.2.1 hs.2.2 fT) (VG.Proof.AesGcm.X86.tagOut_ct rfl fun s hs => ⟨hs.1, hs.2.1⟩) _
    (fun s₀ s' ⟨s, ⟨h₁, hv, hpre⟩, fo, rd, wr⟩ => ⟨⟨fo.env.ebp, fo.env.wW, L.fw⟩, by
      rw [VG.Proof.AesGcm.X86.slot_tagFrame L fo.frame (by decide) (by decide), hv (7, tpO) (by simp),
        VG.Proof.AesGcm.X86.pubSw_last h₁.pub (m := 8) (by decide) rfl], by
      rw [wr, h₁.wr, ← VG.Proof.AesGcm.X86.pubSw_last h₁.pub (m := 8) (by decide) rfl]; exact (VG.Proof.AesGcm.X86.finPre_tag hpre).1⟩)) ?_
  -- The exit.
  refine Pc.taint [.ebp] (fun s₀ s'' ⟨s', ⟨s, ⟨h₁, _, _⟩, fo, _, _⟩, b, f, bp, si, sp, rd, wr⟩ => ?_)
    (fun _ _ s₁ s₂ ⟨_, ⟨_, _, h₁, _⟩, _, _, e₁, _⟩ ⟨_, ⟨_, _, h₂, _⟩, _, _, e₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e₁, e₂, h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  have tS : ∀ r ∈ [(⟨w64 (p.2 8), 16⟩ : Region)], (⟨w64 (p.2 7) + BitVec.ofNat 64 ctxO, 4⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (tw.sub_right (Lay.wSub (by decide))).symm
  have he : Env (p.2 0) (p.2 2) (p.2 7) p.1 s'' := fo.env.keep bp si sp rd wr (slot_frame f tS)
  have hf : Frame (VG.Proof.AesGcm.X86.tagFrame (p.2 2) (p.2 7) p.1 0 ++ [⟨w64 (p.2 8), 16⟩]) s.mem s''.mem :=
    (fo.frame.mono fun r hr => List.mem_append_left _ hr).trans (f.mono fun r hr => List.mem_append_right _ hr)
  refine WP.mono (VG.Proof.AesGcm.X86.fin_exit h₁ FL he hf (fun r hr => ?_) (fun r hr => ?_)) fun s₃ ⟨abi, m', _⟩ =>
    ⟨abi, fun iv a c hr hl ht => ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact VG.Proof.AesGcm.X86.saved_tagFrame L r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact (tw.sub_right (Lay.wSub (by decide))).symm
  · rcases List.mem_append.mp hr with hr | hr
    · exact VG.Proof.AesGcm.X86.ret_tagFrame FL r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact rt
  have hA : ∀ i, i < 7 → arg s₀ i = p.2 i := fun i hi => VG.Proof.AesGcm.X86.pubSw_arg h₁.pub (by omega) (by omega) (by omega)
  rw [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide)] at hr
  rw [hA 3 (by decide), hA 4 (by decide)] at hl
  rw [hA 5 (by decide), hA 6 (by decide)] at ht
  rw [hA 0 (by decide), hA 1 (by decide), VG.Proof.AesGcm.X86.pubSw_last h₁.pub (m := 8) (by decide) rfl, m', b]
  obtain ⟨hr₁, hC, hH⟩ := VG.Proof.AesGcm.X86.fin_repr h₁ L hR hr
  have := fo.tag iv a c hr₁ hl ht
  rw [hC, hH] at this
  exact this

theorem streamFinish_correct (s : State) (hs : streamFinishX86.pre s) :
    ∃ t s', Exec isa (streamFinish vg.callees) s t s' ∧ abiPreserved s s' ∧ streamFinishX86.post s s' :=
  (VG.Proof.AesGcm.X86.streamFinish_pc (VG.Proof.AesGcm.X86.pubSw 9 7 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamFinish_ct : ConstantTime isa streamFinishX86.pre streamFinishX86.pub (streamFinish vg.callees) :=
  Pc.constantTime (VG.Proof.AesGcm.X86.pubSw 9 7) (fun _ _ _ _ h => VG.Proof.AesGcm.X86.pubSw_eq (by decide) h) VG.Proof.AesGcm.X86.streamFinish_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.StreamInit`. -/
section

/-!
# AES-GCM on x86: `vg_aes_gcm_stream_init`

Untrusted: everything here is checked by Lean. The entry, `J₀` and the
first counter block (`j0`) and the exit, as one `Pc` (`streamInit_pc`):
correct (`streamInit_correct`) and constant time (`streamInit_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)
open VG.Proof.Gcm (Absorbed Ctr)

abbrev siTail : List Instr := [.mov .eax (imm 0), .store (at_ .ebp zO) .eax]
abbrev siKeeps : List (Nat × Nat) := [(0, ctxO), (1, dO), (2, nO), (2, nlO)]

theorem streamInit_eq : (streamInit vg.callees) = .seq (entry 4 (([.mov .esi (argOp 3)] : List Instr) ++
    (siKeeps.flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ VG.Proof.AesGcm.X86.siTail))) (.seq (j0 vg.callees) (.block restore)) := rfl

theorem streamInit_lay {s : State} (h : VG.Proof.AesGcm.X86.streamInitPre s) :
    Lay (arg s 0) (arg s 3) (arg s 4) (s.gpr .esp) 24 := by
  simp only [VG.Proof.AesGcm.X86.streamInitPre] at h
  obtain ⟨-, -, d_cs, d_cw, -, -, -, -, d_sw, -, -, -, -, -, -, -, k_c, -, k_s, k_w, -, fc, -, fs, fw, sp, -⟩ := h
  rw [VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.below_eq sp] at k_c k_s k_w
  exact ⟨fc, fs, fw, Nat.le_refl _, by decide, sp, d_cs, d_cw, d_sw.sub_right (Region.sub_prefix (by decide)),
    d_sw.sub_right (Lay.wSub (by decide)), k_c, k_s, k_w⟩

/-- After the entry: the nonce ready for `j0`. -/
structure SiIn (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : VG.Proof.AesGcm.X86.streamInitPre s₀
  pub : VG.Proof.AesGcm.X86.pubOf 5 s₀ = p
  j : VG.Proof.AesGcm.X86.J0In (p.2 0) (p.2 3) (p.2 4) p.1 24 (p.2 1) (p.2 2).toNat s
  saved : SavedAt s.mem (p.2 4) s₀
  frame : Frame [⟨w64 (p.2 4) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem siEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => VG.Proof.AesGcm.X86.streamInitPre s₀ ∧ VG.Proof.AesGcm.X86.pubOf 5 s₀ = p ∧ s = s₀)
      (entry 4 (([.mov .esi (argOp 3)] : List Instr) ++ (siKeeps.flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ VG.Proof.AesGcm.X86.siTail)))
      (VG.Proof.AesGcm.X86.SiIn p) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have L := VG.Proof.AesGcm.X86.streamInit_lay hpre
    have hp := hpre
    simp only [VG.Proof.AesGcm.X86.streamInitPre] at hp
    obtain ⟨hrd, hwr, -, -, -, d_ns, d_nw, -, -, -, d_wa, -, -, -, -, -, -, k_n, -, -, -,
      -, fn, -, fw, sp, fa⟩ := hp
    have a : ∀ i, i < 5 → arg s₀ i = p.2 i := fun i hi => VG.Proof.AesGcm.X86.pubOf_arg hpub hi
    have esp := VG.Proof.AesGcm.X86.pubOf_esp hpub
    rw [VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.below_eq sp] at k_n
    have wW : Covers [⟨w64 (arg s₀ 4), 2560⟩] s₀.wr := by rw [hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 5] (s₀.rd ++ s₀.wr) := by
      rw [VG.Proof.AesGcm.X86.argsR_eq, hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 5).Disjoint ⟨w64 (arg s₀ 4), 2560⟩ := by rw [VG.Proof.AesGcm.X86.argsR_eq]; exact d_wa.symm
    refine entry_ok VG.Proof.AesGcm.X86.siKeeps VG.Proof.AesGcm.X86.siTail (by decide) (by decide) (by decide) (by decide) rfl rfl wW rA aw
      (by omega) fw fun s₂ e => ?_
    have he : Env (arg s₀ 0) (arg s₀ 3) (arg s₀ 4) (s₀.gpr .esp) s₂ :=
      ⟨e.ebp, e.esi, e.esp, by rw [e.rd, e.wr, hrd]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp),
        by rw [e.wr, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp), by rw [e.wr]; exact wW,
        e.slots (0, ctxO) (by simp)⟩
    refine ⟨_, by xrun [he.ebp, L.aW, he.wIn], ?_⟩
    have hf : Frame [⟨w64 (arg s₀ 4) + BitVec.ofNat 64 zO, 4⟩] s₂.mem
        (s₂.mem.writeW (w64 (arg s₀ 4) + BitVec.ofNat 64 zO) (BitVec.ofNat 32 0)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have sl : ∀ {o}, 128 ≤ o → o + 4 ≤ 2560 → (o + 4 ≤ zO ∨ zO + 4 ≤ o) → slotv (s₂.mem.writeW
        (w64 (arg s₀ 4) + BitVec.ofNat 64 zO) (BitVec.ofNat 32 0)) (arg s₀ 4) o = slotv s₂.mem (arg s₀ 4) o :=
      fun h₁ h₂ h₃ => slot_frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w h₃ (by omega) (by decide)
    refine ⟨hpre, hpub, ?_, ?_, ?_, by mems [e.rd], by mems [e.wr]⟩
    rotate_left
    · rw [← a 4 (by decide)]
      simp only [mem_setMem, mem_setReg, mem_arithFlags]
      exact e.saved.frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [← a 4 (by decide)]
      simp only [mem_setMem, mem_setReg, mem_arithFlags]
      exact e.frame.trans (hf.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)
    rw [← a 0 (by decide), ← a 1 (by decide), ← a 2 (by decide), ← a 3 (by decide), ← a 4 (by decide), ← esp]
    refine ⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) ?_, ?_, ?_, ?_, ?_,
      ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact sl (by decide) (by decide) (by decide)
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sl (by decide) (by decide) (by decide)]
      exact e.slots (1, dO) (by simp)
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sl (by decide) (by decide) (by decide)]
      rw [e.slots (2, nO) (by simp), VG.Proof.AesGcm.X86.ofNat_toNat32]
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sl (by decide) (by decide) (by decide)]
      rw [e.slots (2, nlO) (by simp), VG.Proof.AesGcm.X86.ofNat_toNat32]
    · simp only [mem_setMem, mem_setReg, mem_arithFlags, slotv_eq, Mem.readW_writeW_self32]; rfl
    · exact (arg s₀ 2).isLt
    · mems [e.rd, e.wr, hrd]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
    · exact fn
    · exact d_ns
    · exact d_nw
    · exact k_n
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 4 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [VG.Proof.AesGcm.X86.pubOf_esp h₁, VG.Proof.AesGcm.X86.pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    subst s
    have hp := hpre
    simp only [VG.Proof.AesGcm.X86.streamInitPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fa⟩ := hp
    have rA : Covers [argsR (s₀.gpr .esp) 5] (s₀.rd ++ s₀.wr) := by
      rw [VG.Proof.AesGcm.X86.argsR_eq, hrd, hwr]; exact VG.Proof.AesGcm.X86.covers_of_mem (by simp)
    exact WP.mono (VG.Proof.AesGcm.X86.arg0_ok (VG.Proof.AesGcm.X86.argIn_of rA (by omega) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact VG.Proof.AesGcm.X86.pubOf_arg hpub (by decide), by rw [sp]; exact VG.Proof.AesGcm.X86.pubOf_esp hpub⟩

theorem si_ret {p : BitVec 32 × (Nat → BitVec 32)} {s₀ : State} (h : VG.Proof.AesGcm.X86.streamInitPre s₀) (hp : VG.Proof.AesGcm.X86.pubOf 5 s₀ = p) :
    (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 3), 80⟩ ∧ (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 4), 2560⟩ ∧
      24 ≤ p.1.toNat := by
  simp only [VG.Proof.AesGcm.X86.streamInitPre] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, r_s, r_w, -, -, -, -, -, -, -, -, -, -, sp, -⟩ := h
  rw [VG.Proof.AesGcm.X86.pubOf_arg hp (i := 3) (by decide), VG.Proof.AesGcm.X86.pubOf_arg hp (i := 4) (by decide), VG.Proof.AesGcm.X86.pubOf_esp hp] at *
  exact ⟨r_s, r_w, sp⟩

theorem streamInit_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => VG.Proof.AesGcm.X86.streamInitPre s₀ ∧ VG.Proof.AesGcm.X86.pubOf 5 s₀ = p ∧ s = s₀) (streamInit vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamInitX86.post s₀ s') := by
  by_cases hex : ∃ s₀, VG.Proof.AesGcm.X86.streamInitPre s₀ ∧ VG.Proof.AesGcm.X86.pubOf 5 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : Lay (p.2 0) (p.2 3) (p.2 4) p.1 24 := by
    have := VG.Proof.AesGcm.X86.streamInit_lay hz
    rwa [VG.Proof.AesGcm.X86.pubOf_arg hzp (i := 0) (by decide), VG.Proof.AesGcm.X86.pubOf_arg hzp (i := 3) (by decide),
      VG.Proof.AesGcm.X86.pubOf_arg hzp (i := 4) (by decide), VG.Proof.AesGcm.X86.pubOf_esp hzp] at this
  obtain ⟨r_s, r_w, sp⟩ := VG.Proof.AesGcm.X86.si_ret hz hzp
  rw [VG.Proof.AesGcm.X86.streamInit_eq]
  refine Pc.seq (VG.Proof.AesGcm.X86.siEntry_pc p) (Pc.seq (Pc.lift (VG.Proof.AesGcm.X86.j0_pc L) (fun _ s => s.mem) fun s₀ s h => ⟨h.j, rfl⟩) ?_)
  refine Pc.taint [.ebp] (fun s₀ s ⟨s₁, h₁, ho, rd, wr⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  have he := ho.env
  have esp := VG.Proof.AesGcm.X86.pubOf_esp h₁.pub
  have a : ∀ i, i < 5 → arg s₀ i = p.2 i := fun i hi => VG.Proof.AesGcm.X86.pubOf_arg h₁.pub hi
  have fE := h₁.frame
  have fJ := ho.frame
  have hsv : SavedAt s.mem (p.2 4) s₀ := h₁.saved.frameK fJ (VG.Proof.AesGcm.X86.kept_j0Frame L)
  have rJ : ∀ r ∈ VG.Proof.AesGcm.X86.j0Frame (p.2 3) (p.2 4) p.1 24, (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact r_s
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact VG.Proof.AesGcm.X86.ret_below sp
  have rE : ∀ r ∈ [(⟨w64 (p.2 4) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact r_w.sub_right (Lay.wSub (by decide))
  have hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [esp, VG.Proof.AesGcm.X86.ret_kept fJ rJ, VG.Proof.AesGcm.X86.ret_kept fE rE]
  refine WP.mono (exit_ok he.ebp (by rw [he.esp, esp]) (covers_left he.wW) L.fw hsv hret)
    fun s' ⟨abi, m', _, _, _⟩ => ⟨abi, fun ciph => ?_⟩
  have hp := h₁.pre
  simp only [VG.Proof.AesGcm.X86.streamInitPre] at hp
  obtain ⟨-, -, -, -, -, -, d_nw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fn, -, -, -, -⟩ := hp
  rw [a 1 (by decide), a 2 (by decide), a 4 (by decide)] at d_nw
  rw [a 1 (by decide), a 2 (by decide)] at fn
  rw [a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide)]
  have hH : Hk s₁.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0)) := by
    rw [VG.Proof.AesGcm.X86.ctxH_eq]
    exact blockAt_frame fE fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hD : bytesAt s₁.mem (w64 (p.2 1)) (p.2 2).toNat = bytesAt s₀.mem (w64 (p.2 1)) (p.2 2).toNat :=
    bytesAt_frame (p := w64 (p.2 1)) (n := (p.2 2).toNat) fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact d_nw.sub_right (Lay.wSub (d := 128) (n := 2432) (by decide))) (by omega)
  rw [Proof.Gcm.streamRepr_iff, VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.ofNat_lit, VG.Proof.AesGcm.X86.ofNat_lit, m', Proof.Gcm.ghashInput_nil]
  refine ⟨by rw [ho.j0, hH, hD], Proof.Gcm.absorbed_nil _ ho.y, Proof.Gcm.ctr_zero _ _ _ _ ?_⟩
  rw [ho.cb, hH, hD]

theorem streamInit_correct (s : State) (hs : streamInitX86.pre s) :
    ∃ t s', Exec isa (streamInit vg.callees) s t s' ∧ abiPreserved s s' ∧ streamInitX86.post s s' :=
  (VG.Proof.AesGcm.X86.streamInit_pc (VG.Proof.AesGcm.X86.pubOf 5 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamInit_ct : ConstantTime isa streamInitX86.pre streamInitX86.pub (streamInit vg.callees) :=
  Pc.constantTime (VG.Proof.AesGcm.X86.pubOf 5) (fun _ _ _ _ h => VG.Proof.AesGcm.X86.pubOf_eq h) VG.Proof.AesGcm.X86.streamInit_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86.StreamVerify`. -/
section

/-!
# AES-GCM on x86: `vg_aes_gcm_stream_verify`

Untrusted: everything here is checked by Lean. The entry (`finEntry_pc`,
keeping `tag` and `tag_len` too), the tag length checked (`tagLenOk_pc`),
and then either 0, or the received tag copied from `tag` (`recv_ok`), the
tag computed (`finTag_pc`) and compared (`cmp_ok`), as one `Pc`
(`streamVerify_pc`): correct (`streamVerify_correct`) and constant time
(`streamVerify_ct`). Only the lengths, the pointers and `rounds` affect the
branches: the comparison has none.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph fullTag zeros)

theorem streamVerify_eq : (streamVerify vg.callees) = .seq (entry 9 (([.mov .esi (argOp 2)] : List Instr) ++
    ((VG.Proof.AesGcm.X86.finKeeps ++ [(7, tpO), (8, tglO)]).flatMap (fun (p : Nat × Nat) => VG.Impl.AesGcm.X86.keep p.1 p.2) ++ [])))
    (.seq tagLenOk (.seq (.ite .e (.block [.mov .eax (imm 0)])
      (.seq recv (.seq (finTag vg.callees 0) (cmp 0)))) (.block restore))) := rfl

/-- Where the received tag is copied. -/
abbrev rR (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 rO, 16⟩

/-- The kept values, after the received tag is copied. -/
theorem FinIn.frameR {Ctx St W SP : BitVec 32} {R : Nat} {al ah xl xh : BitVec 32} {s s' : State}
    (h : VG.Proof.AesGcm.X86.FinIn Ctx St W SP R al ah xl xh s) (hf : Frame [VG.Proof.AesGcm.X86.rR W] s.mem s'.mem) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesGcm.X86.FinIn Ctx St W SP R al ah xl xh s' := by
  have sl : ∀ o, o + 4 ≤ rO → slotv s'.mem W o = slotv s.mem W o := fun o ho => by
    have ho' : o + 4 ≤ 196 := ho
    rw [slotv_eq, slotv_eq]
    exact slot_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl ho') (by omega) (by decide)
  have hc := sl ctxO (by decide)
  rw [slotv_eq, slotv_eq] at hc
  exact ⟨h.env.keep hbp hsi hsp hrd hwr hc, by rw [sl _ (by decide)]; exact h.al, by rw [sl _ (by decide)]; exact h.ah,
    by rw [sl _ (by decide)]; exact h.xl, by rw [sl _ (by decide)]; exact h.xh,
    ⟨by rw [sl _ (by decide)]; exact h.rounds.1, h.rounds.2⟩⟩

/-- The received tag, outside the regions the tag is computed in. -/
theorem rR_tagFrame {Ctx St W SP : BitVec 32} (L : Lay Ctx St W SP 28) :
    ∀ r ∈ VG.Proof.AesGcm.X86.tagFrame St W SP 0, (VG.Proof.AesGcm.X86.rR W).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · have := (L.st_w (a := 0) (n := 32) (d := 196) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    rwa [BitVec.add_zero] at this
  · exact Lay.w_w (d := 96) (k := 16) (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (d := 240) (k := 2320) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- After the entry and the tag length checked. -/
structure VT (p : BitVec 32 × (Nat → BitVec 32)) (ok : Bool) (s₀ s₁ s : State) : Prop where
  ent : VG.Proof.AesGcm.X86.FinEnt 10 9 p s₀ s₁
  vp : VG.Proof.AesGcm.X86.verifyPre s₀
  fin : VG.Proof.AesGcm.X86.FinIn (p.2 0) (p.2 2) (p.2 7) p.1 (p.2 1).toNat (p.2 3) (p.2 4) (p.2 5) (p.2 6) s
  mem : s.mem = s₁.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  tgl : slotv s.mem (p.2 7) tglO = BitVec.ofNat 32 (p.2 8).toNat
  tp : slotv s.mem (p.2 7) tpO = p.2 9
  zf : s.zf = some (!ok)

/-- What `verify` ends with, before restoring our caller's registers. -/
def VOut (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop :=
  ∃ s₁, VG.Proof.AesGcm.X86.FinEnt 10 9 p s₀ s₁ ∧ Env (p.2 0) (p.2 2) (p.2 7) p.1 s ∧
    Frame (VG.Proof.AesGcm.X86.rR (p.2 7) :: VG.Proof.AesGcm.X86.tagFrame (p.2 2) (p.2 7) p.1 0) s₁.mem s.mem ∧ streamVerifyX86.post s₀ s

theorem streamVerify_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => VG.Proof.AesGcm.X86.verifyPre s₀ ∧ VG.Proof.AesGcm.X86.pubSw 10 7 s₀ = p ∧ s = s₀) (streamVerify vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamVerifyX86.post s₀ s') := by
  by_cases hex : ∃ s₀, VG.Proof.AesGcm.X86.verifyPre s₀ ∧ VG.Proof.AesGcm.X86.pubSw 10 7 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have FL : VG.Proof.AesGcm.X86.FinL p := (VG.Proof.AesGcm.X86.verifyPre_of hz).fl rfl (by decide) hzp
  have L := FL.L
  have hR := FL.rounds
  have a8 : ∀ {s₀ : State}, VG.Proof.AesGcm.X86.pubSw 10 7 s₀ = p → arg s₀ 8 = p.2 8 := fun h =>
    VG.Proof.AesGcm.X86.pubSw_arg h (by decide) (by decide) (by decide)
  have a7 : ∀ {s₀ : State}, VG.Proof.AesGcm.X86.pubSw 10 7 s₀ = p → arg s₀ 7 = p.2 9 := fun h => VG.Proof.AesGcm.X86.pubSw_last h (by decide) rfl
  obtain ⟨-, fT, tw⟩ := VG.Proof.AesGcm.X86.verifyPre_tag hz
  rw [a7 hzp, a8 hzp] at fT
  rw [a7 hzp, a8 hzp, VG.Proof.AesGcm.X86.pubSw_W hzp (m := 9) (by decide) rfl] at tw
  generalize hok : Spec.Gcm.tagLenOk (p.2 8).toNat = ok
  have ht32 : (p.2 8).toNat < 2 ^ 32 := (p.2 8).isLt
  rw [VG.Proof.AesGcm.X86.streamVerify_eq]
  -- The entry, then the tag length.
  refine Pc.seq (VG.Proof.AesGcm.X86.finEntry_pc 10 9 rfl (by decide) [(7, tpO), (8, tglO)] (by decide) (by decide) VG.Proof.AesGcm.X86.verifyPre
    (fun _ h => VG.Proof.AesGcm.X86.verifyPre_of h) p (by taint_decide) (by taint_decide)) ?_
  refine Pc.seq (Q := fun s₀ s => ∃ s₁, VG.Proof.AesGcm.X86.VT p ok s₀ s₁ s) (Pc.mono (Pc.lift (VG.Proof.AesGcm.X86.tagLenOk_pc (W := p.2 7) ht32)
    (fun _ s => s) fun s₀ s ⟨h, hv, _⟩ => ⟨rfl, h.fin.env.ebp, L.aW (by decide), h.fin.env.wIn' (by decide), by
      rw [hv (8, tglO) (by simp), a8 h.pub, VG.Proof.AesGcm.X86.ofNat_toNat32]⟩) (fun _ _ h => h)
    fun s₀ s ⟨s₁, ⟨h₁, hv, hpre⟩, ⟨tl, hz⟩, _, _⟩ => ⟨s₁, h₁, hpre, h₁.fin.keep
      (by rw [tl.other _ (by decide) (by decide)]) (by rw [tl.other _ (by decide) (by decide)])
      (by rw [tl.other _ (by decide) (by decide)]) tl.mem tl.rd tl.wr,
      tl.mem, by rw [tl.rd, h₁.rd], by rw [tl.wr, h₁.wr], by rw [tl.mem, hv (8, tglO) (by simp), a8 h₁.pub, VG.Proof.AesGcm.X86.ofNat_toNat32],
      by rw [tl.mem, hv (7, tpO) (by simp), a7 h₁.pub], by rw [hz, hok]⟩) ?_
  refine Pc.seq (Q := VG.Proof.AesGcm.X86.VOut p) (Pc.ite (!ok) (fun _ _ ⟨_, h⟩ => h.zf) (fun hb => ?_) (fun hb => ?_)) ?_
  -- A tag length §5.2.1.2 does not allow.
  · have hf : ok = false := by simpa using hb
    refine Pc.taint [] (fun s₀ s ⟨s₁, h⟩ => ?_) (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    have he := h.fin.env
    refine WP.of_runBlock ⟨_, by xrun [], ?_⟩
    refine ⟨s₁, h.ent, he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems []), ?_, ?_⟩
    · mems []; rw [h.mem]; exact Frame.refl _ _
    · simp only [VG.Proof.AesGcm.X86.streamVerifyX86, VG.Proof.AesGcm.X86.ret32_eq]
      intro iv a c _ _ _
      have e : Spec.Gcm.tagLenOk (arg s₀ 8).toNat = false := by rw [a8 h.ent.pub, hok, hf]
      simp only [e, Bool.false_eq_true, false_and, ↓reduceIte]
      regs []; rfl
  -- An allowed one: the tags compared.
  · have hT : ok = true := by simpa using hb
    have ht := hok
    rw [hT] at ht
    have ht' : 1 ≤ (p.2 8).toNat ∧ (p.2 8).toNat ≤ 16 := by
      simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at ht
      omega
    obtain ⟨t1, t16⟩ := ht'
    -- The received tag copied.
    refine Pc.seq (Pc.of (I := fun s => VG.Proof.AesGcm.X86.WEnv (p.2 7) s ∧ slotv s.mem (p.2 7) tglO = BitVec.ofNat 32 (p.2 8).toNat ∧
        slotv s.mem (p.2 7) tpO = p.2 9 ∧ Covers [⟨w64 (p.2 9), (p.2 8).toNat⟩] (s.rd ++ s.wr))
      (R := fun s s' => bytesAt s'.mem (w64 (p.2 7) + BitVec.ofNat 64 rO) 16 =
          bytesAt s.mem (w64 (p.2 9)) (p.2 8).toNat ++ zeros (16 - (p.2 8).toNat) ∧
        Frame [⟨w64 (p.2 7) + BitVec.ofNat 64 rO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧
        s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
      (fun s hs => VG.Proof.AesGcm.X86.recv_ok hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 fT tw t1 t16)
      (VG.Proof.AesGcm.X86.recv_ct fun s hs => ⟨hs.1, hs.2.1, hs.2.2.1⟩) _
      (fun s₀ s ⟨s₁, h⟩ => ⟨⟨h.fin.env.ebp, h.fin.env.wW, L.fw⟩, h.tgl, h.tp, by
        rw [h.rd, h.wr, ← a7 h.ent.pub, ← a8 h.ent.pub]; exact (VG.Proof.AesGcm.X86.verifyPre_tag h.vp).1⟩)) ?_
    -- The tag computed.
    refine Pc.seq (Pc.lift (VG.Proof.AesGcm.X86.finTag_pc L (R := (p.2 1).toNat) (o := 0) (.inl rfl) (al := p.2 3) (ah := p.2 4)
      (xl := p.2 5) (xh := p.2 6)) (fun _ s => s.mem)
      fun s₀ s' ⟨s, ⟨s₁, h⟩, _, f, g1, g2, g3, rd, wr⟩ => ⟨h.fin.frameR f g1 g2 g3 rd wr, rfl⟩) ?_
    -- Compared.
    refine Pc.mono (Pc.of (I := fun s => VG.Proof.AesGcm.X86.WEnv (p.2 7) s ∧ slotv s.mem (p.2 7) tglO = BitVec.ofNat 32 (p.2 8).toNat)
      (R := fun s s' => s'.gpr .eax = BitVec.ofNat 32
          (if bytesAt s.mem (w64 (p.2 7) + BitVec.ofNat 64 0) (p.2 8).toNat ++ zeros (16 - (p.2 8).toNat) =
              bytesAt s.mem (w64 (p.2 7) + BitVec.ofNat 64 rO) 16 then 1 else 0) ∧
        Frame [⟨w64 (p.2 7) + BitVec.ofNat 64 vO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧
        s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
      (fun s hs => VG.Proof.AesGcm.X86.cmp_ok hs.1 hs.2 t1 t16 (by decide)) (VG.Proof.AesGcm.X86.cmp_ct (.inl rfl) fun s hs => hs) _
      (fun s₀ s'' ⟨s', ⟨s, ⟨s₁, h⟩, _, f, _⟩, fo, _, _⟩ => ⟨⟨fo.env.ebp, fo.env.wW, L.fw⟩, by
        rw [VG.Proof.AesGcm.X86.slot_tagFrame L fo.frame (by decide) (by decide), slotv_eq,
          slot_frame f fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Lay.w_w (a := 180) (n := 4) (d := 196) (k := 16) (.inl (by decide)) (by decide) (by decide),
          ← slotv_eq]
        exact h.tgl⟩)) (fun _ _ h => h) ?_
    intro s₀ s₃ ⟨s₂, ⟨s', ⟨s, ⟨s₁, h⟩, b, f, g1, g2, g3, rd, wr⟩, fo, rd₂, wr₂⟩, a₃, f₃, e1, e2, e3, rd₃, wr₃⟩
    have f₁ : Frame [VG.Proof.AesGcm.X86.rR (p.2 7)] s₁.mem s'.mem := by rw [← h.mem]; exact f
    refine ⟨s₁, h.ent, fo.env.keep e1 e2 e3 rd₃ wr₃ ?_, ?_, ?_⟩
    · exact slot_frame f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (a := 144) (n := 4) (d := 240) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · refine f₁.mono (fun r hr => by simp at hr; subst hr; simp) |>.trans
        (fo.frame.mono (fun r hr => List.mem_cons_of_mem _ hr) |>.trans
        (f₃.sub (fun r hr => ⟨wsR (p.2 7), by simp, by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩)))
    · have hA : ∀ i, i < 7 → arg s₀ i = p.2 i := fun i hi => VG.Proof.AesGcm.X86.pubSw_arg h.ent.pub (by omega) (by omega) (by omega)
      simp only [VG.Proof.AesGcm.X86.streamVerifyX86, VG.Proof.AesGcm.X86.ret32_eq]
      intro iv a c hr hl hc
      rw [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide)] at hr
      rw [hA 3 (by decide), hA 4 (by decide)] at hl
      rw [hA 5 (by decide), hA 6 (by decide)] at hc
      rw [hA 0 (by decide), hA 1 (by decide), a7 h.ent.pub, a8 h.ent.pub]
      obtain ⟨hr₁, hC, hH⟩ := VG.Proof.AesGcm.X86.fin_repr h.ent L hR hr
      have hC' : ciphOf s'.mem (p.2 0) (p.2 1).toNat = ciphOf s₁.mem (p.2 0) (p.2 1).toNat :=
        ciph_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide))) hR
      have hH' : Hk s'.mem (p.2 0) = Hk s₁.mem (p.2 0) :=
        blockAt_frame f₁ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
      have hr₂ : StreamRepr s'.mem (w64 (p.2 2)) (ciphOf s'.mem (p.2 0) (p.2 1).toNat) (Hk s'.mem (p.2 0)) iv a c := by
        rw [hC', hH']
        exact VG.Proof.AesGcm.X86.streamRepr_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          simpa using L.st_w (a := 0) (n := 80) (d := 196) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)) hr₁
      have tag := fo.tag iv a c hr₂ hl hc
      rw [hC', hH', hC, hH] at tag
      generalize fullTag (ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat) (ctxH s₀.mem (w64 (p.2 0))) iv a c = T at tag ⊢
      have bW : bytesAt s₂.mem (w64 (p.2 7) + BitVec.ofNat 64 0) (p.2 8).toNat = T.take (p.2 8).toNat := by
        rw [← tag, bytesAt_take _ _ t16]
      have bR : bytesAt s₂.mem (w64 (p.2 7) + BitVec.ofNat 64 rO) 16 =
          bytesAt s₀.mem (w64 (p.2 9)) (p.2 8).toNat ++ zeros (16 - (p.2 8).toNat) := by
        rw [bytesAt_frame fo.frame (VG.Proof.AesGcm.X86.rR_tagFrame L) (by decide), b, h.mem,
          bytesAt_frame h.ent.frame (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact tw.sub_right (Lay.wSub (by decide))) (by omega)]
      simp only [bW, bR, List.append_left_inj] at a₃
      simp only [hok, hT, true_and]
      by_cases hX : T.take (p.2 8).toNat = bytesAt s₀.mem (w64 (p.2 9)) (p.2 8).toNat
      · simp only [hX, ↓reduceIte] at a₃ ⊢
        rw [a₃]; rfl
      · simp only [hX, ↓reduceIte] at a₃ ⊢
        rw [a₃]; rfl
  -- The exit.
  refine Pc.taint [.ebp] (fun s₀ s ⟨s₁, h₁, he, hf, hpost⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ebp, h₂.ebp]) (by taint_decide)
  refine WP.mono (VG.Proof.AesGcm.X86.fin_exit h₁ FL he hf (fun r hr => ?_) (fun r hr => ?_)) fun s' ⟨abi, _, ax⟩ => ⟨abi, ?_⟩
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact VG.Proof.AesGcm.X86.saved_tagFrame L r hr
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact FL.r_w.sub_right (Lay.wSub (by decide))
    · exact VG.Proof.AesGcm.X86.ret_tagFrame FL r hr
  simp only [VG.Proof.AesGcm.X86.streamVerifyX86, VG.Proof.AesGcm.X86.ret32_eq] at hpost ⊢
  rw [ax]
  exact hpost

theorem streamVerify_correct (s : State) (hs : streamVerifyX86.pre s) :
    ∃ t s', Exec isa (streamVerify vg.callees) s t s' ∧ abiPreserved s s' ∧ streamVerifyX86.post s s' :=
  (VG.Proof.AesGcm.X86.streamVerify_pc (VG.Proof.AesGcm.X86.pubSw 10 7 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamVerify_ct : ConstantTime isa streamVerifyX86.pre streamVerifyX86.pub (streamVerify vg.callees) :=
  Pc.constantTime (VG.Proof.AesGcm.X86.pubSw 10 7) (fun _ _ _ _ h => VG.Proof.AesGcm.X86.pubSw_eq (by decide) h) VG.Proof.AesGcm.X86.streamVerify_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86

end
