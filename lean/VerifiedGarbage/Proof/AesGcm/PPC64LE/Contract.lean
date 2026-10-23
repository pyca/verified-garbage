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
open VG.Spec.Gcm (StreamRepr KeyRepr ctxCiph ctxH gctr inc32 j0)

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

end VG.Proof.AesGcm.PPC64LE
