module

public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Taint

/-!
# SM4-GCM on ARMv7: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Sm4/Gcm/Contract.lean`, which imply these
(`Verified.lean`). Every function calls others that use the 1520 bytes below
the stack pointer (`bel`), which no buffer overlaps.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr gctr inc32 j0 fullTag tagLenOk zeros encryptWith openResult)
open VG.Spec.Sm4.Gcm (KeyRepr ctxCiph)
open VG.Spec.Gcm (ctxH)

/-- The 1520 bytes below the stack pointer. -/
abbrev bel (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 1520, 1520⟩

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 32 := stackArg s i

/-- The arguments on the stack, `n` words of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 4 * n⟩

/-- A 64-bit argument on the stack, from word `i`. -/
abbrev arg64 (s : State) (i : Nat) : BitVec 64 := stackArg s (i + 1) ++ stackArg s i

/-- `vg_sm4_gcm_init(key = r0, ctx = r1, scratch = r2)`. -/
def initArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 16⟩
    let ctx : Region := ⟨State.addr (s.gpr .r1), 256⟩
    let scr : Region := ⟨State.addr (s.gpr .r2), 768⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (bel s).Disjoint key ∧ (bel s).Disjoint ctx ∧ (bel s).Disjoint scr ∧
      (s.gpr .r0).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 256 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 768 ≤ 2 ^ 32 ∧ 1520 ≤ s.sp.toNat
  post s s' := KeyRepr s'.mem (State.addr (s.gpr .r1)) (bytesAt s.mem (State.addr (s.gpr .r0)) 16)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

/-- `vg_sm4_gcm_stream_init(ctx = r0, nonce = r1, nonce_len = r2, state = r3, scratch = [sp])`. -/
def streamInitArm : Contract isa where
  pre s :=
    let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
    let nonce : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let st : Region := ⟨State.addr (s.gpr .r3), 80⟩
    let scr : Region := ⟨State.addr (arg s 0), 768⟩
    s.rd = [ctx, nonce, args s 1] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧ st.Disjoint scr ∧
      st.Disjoint (args s 1) ∧ scr.Disjoint (args s 1) ∧
      (bel s).Disjoint ctx ∧ (bel s).Disjoint nonce ∧ (bel s).Disjoint st ∧ (bel s).Disjoint scr ∧
      (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 80 ≤ 2 ^ 32 ∧ (arg s 0).toNat + 768 ≤ 2 ^ 32 ∧ 1520 ≤ s.sp.toNat ∧
      s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' := ∀ ciph, StreamRepr s'.mem (State.addr (s.gpr .r3)) ciph (ctxH s.mem (State.addr (s.gpr .r0)))
    (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat) [] []
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ arg s₁ 0 = arg s₂ 0

/-- `vg_sm4_gcm_stream_aad(ctx = r0, state = r1, aad_len = r3:r2, data = [sp], len = [sp + 4],
scratch = [sp + 8])`. -/
def streamAadArm : Contract isa where
  pre s :=
    let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
    let st : Region := ⟨State.addr (s.gpr .r1), 80⟩
    let data : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
    let scr : Region := ⟨State.addr (arg s 2), 768⟩
    s.rd = [ctx, data, args s 3] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ data.Disjoint st ∧ data.Disjoint scr ∧ st.Disjoint scr ∧
      st.Disjoint (args s 3) ∧ scr.Disjoint (args s 3) ∧
      (bel s).Disjoint ctx ∧ (bel s).Disjoint data ∧ (bel s).Disjoint st ∧ (bel s).Disjoint scr ∧
      (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 80 ≤ 2 ^ 32 ∧
      (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + 768 ≤ 2 ^ 32 ∧ 1520 ≤ s.sp.toNat ∧
      s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ ciph iv a, StreamRepr s.mem (State.addr (s.gpr .r1)) ciph (ctxH s.mem (State.addr (s.gpr .r0))) iv a [] →
    (s.gpr .r3 ++ s.gpr .r2) = BitVec.ofNat 64 a.length →
    StreamRepr s'.mem (State.addr (s.gpr .r1)) ciph (ctxH s.mem (State.addr (s.gpr .r0))) iv
      (a ++ bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat) []
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2

/-- What `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt` need:
`(ctx = r0, state = r1, aad_len = r3:r2, text_len = [sp + 4]:[sp], data = [sp + 8], len = [sp + 12],
scratch = [sp + 16])`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let st : Region := ⟨State.addr (s.gpr .r1), 80⟩
  let data : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let scr : Region := ⟨State.addr (arg s 4), 768⟩
  s.rd = [ctx, args s 5] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ st.Disjoint (args s 5) ∧ data.Disjoint scr ∧
    data.Disjoint (args s 5) ∧ scr.Disjoint (args s 5) ∧
    (bel s).Disjoint ctx ∧ (bel s).Disjoint st ∧ (bel s).Disjoint data ∧ (bel s).Disjoint scr ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 80 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 768 ≤ 2 ^ 32 ∧ 1520 ≤ s.sp.toNat ∧
    s.sp.toNat + 20 ≤ 2 ^ 32

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncryptArm : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (State.addr (s.gpr .r0))
    let h := ctxH s.mem (State.addr (s.gpr .r0))
    ∀ iv a p, StreamRepr s.mem (State.addr (s.gpr .r1)) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      (s.gpr .r3 ++ s.gpr .r2) = BitVec.ofNat 64 a.length → (arg64 s 0).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat)
      StreamRepr s'.mem (State.addr (s.gpr .r1)) ciph h iv a c ∧
        bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat = c.drop p.length
  pub := streamCryptPub

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecryptArm : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (State.addr (s.gpr .r0))
    let h := ctxH s.mem (State.addr (s.gpr .r0))
    ∀ iv a c, StreamRepr s.mem (State.addr (s.gpr .r1)) ciph h iv a c →
      (s.gpr .r3 ++ s.gpr .r2) = BitVec.ofNat 64 a.length → (arg64 s 0).toNat = c.length →
      let c' := c ++ bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat
      StreamRepr s'.mem (State.addr (s.gpr .r1)) ciph h iv a c' ∧
        bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := streamCryptPub

/-- What `vg_sm4_gcm_stream_finish` and `vg_sm4_gcm_stream_verify` both need:
`(ctx = r0, state = r1, aad_len = r3:r2, text_len = [sp + 4]:[sp], …)`, with `n` words of stack
arguments and `work` the `wi`-th (`streamFinishPreArm.fin`, `streamVerifyPreArm.fin`). -/
def finPre (n wi : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let st : Region := ⟨State.addr (s.gpr .r1), 80⟩
  let work : Region := ⟨State.addr (arg s wi), 768⟩
  (ctx ∈ s.rd ∧ args s n ∈ s.rd) ∧ (st ∈ s.wr ∧ work ∈ s.wr ∧ ∀ r ∈ s.wr, (args s n).Disjoint r) ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint work ∧ st.Disjoint (args s n) ∧
    work.Disjoint (args s n) ∧
    (bel s).Disjoint ctx ∧ (bel s).Disjoint st ∧ (bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 80 ≤ 2 ^ 32 ∧ (arg s wi).toNat + 768 ≤ 2 ^ 32 ∧
    1520 ≤ s.sp.toNat ∧ s.sp.toNat + 4 * n ≤ 2 ^ 32

def finPub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < n, arg s₁ i = arg s₂ i

/-- What `vg_sm4_gcm_stream_finish` needs: `(ctx = r0, state = r1, aad_len = r3:r2,
text_len = [sp + 4]:[sp], tag = [sp + 8], work = [sp + 12])`. -/
def streamFinishPreArm (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let st : Region := ⟨State.addr (s.gpr .r1), 80⟩
  let tag : Region := ⟨State.addr (arg s 2), 16⟩
  let work : Region := ⟨State.addr (arg s 3), 768⟩
  s.rd = [ctx, args s 4] ∧ s.wr = [st, tag, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint work ∧ st.Disjoint tag ∧ st.Disjoint work ∧
    st.Disjoint (args s 4) ∧ tag.Disjoint work ∧ tag.Disjoint (args s 4) ∧ work.Disjoint (args s 4) ∧
    (bel s).Disjoint ctx ∧ (bel s).Disjoint st ∧ (bel s).Disjoint tag ∧ (bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 80 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 768 ≤ 2 ^ 32 ∧ 1520 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 32

/-- `vg_sm4_gcm_stream_finish`. -/
def streamFinishArm : Contract isa where
  pre := streamFinishPreArm
  post s s' :=
    let ciph := ctxCiph s.mem (State.addr (s.gpr .r0))
    let h := ctxH s.mem (State.addr (s.gpr .r0))
    ∀ iv a c, StreamRepr s.mem (State.addr (s.gpr .r1)) ciph h iv a c →
      (s.gpr .r3 ++ s.gpr .r2) = BitVec.ofNat 64 a.length → (arg64 s 0).toNat = c.length →
      bytesAt s'.mem (State.addr (arg s 2)) 16 = fullTag ciph h iv a c
  pub := finPub 4

/-- What `vg_sm4_gcm_stream_verify` needs: `(ctx = r0, state = r1, aad_len = r3:r2,
text_len = [sp + 4]:[sp], tag = [sp + 8], tag_len = [sp + 12], work = [sp + 16])`. -/
def streamVerifyPreArm (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let st : Region := ⟨State.addr (s.gpr .r1), 80⟩
  let tag : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let work : Region := ⟨State.addr (arg s 4), 768⟩
  s.rd = [ctx, tag, args s 5] ∧ s.wr = [st, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint tag ∧ st.Disjoint work ∧ st.Disjoint (args s 5) ∧
    tag.Disjoint work ∧ work.Disjoint (args s 5) ∧
    (bel s).Disjoint ctx ∧ (bel s).Disjoint st ∧ (bel s).Disjoint tag ∧ (bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 80 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 768 ≤ 2 ^ 32 ∧ 1520 ≤ s.sp.toNat ∧
    s.sp.toNat + 20 ≤ 2 ^ 32

/-- `vg_sm4_gcm_stream_verify`. -/
def streamVerifyArm : Contract isa where
  pre := streamVerifyPreArm
  post s s' :=
    let ciph := ctxCiph s.mem (State.addr (s.gpr .r0))
    let h := ctxH s.mem (State.addr (s.gpr .r0))
    let tl := (arg s 3).toNat
    ∀ iv a c, StreamRepr s.mem (State.addr (s.gpr .r1)) ciph h iv a c →
      (s.gpr .r3 ++ s.gpr .r2) = BitVec.ofNat 64 a.length → (arg64 s 0).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (State.addr (arg s 2)) tl then s'.gpr .r0 = 1
      else s'.gpr .r0 = 0
  pub := finPub 5

/-- What `vg_sm4_gcm_seal` and `vg_sm4_gcm_open` both need: `(ctx = r0, nonce = r1, nonce_len = r2,
aad = r3, aad_len = [sp], data = [sp + 4], len = [sp + 8], …)`, with `n` words of stack arguments and
`work` the `wi`-th (`sealPreArm.one`, `openPreArm.one`). -/
def onePre (n wi : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
  let aad : Region := ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩
  let data : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
  let work : Region := ⟨State.addr (arg s wi), 768⟩
  (ctx ∈ s.rd ∧ nonce ∈ s.rd ∧ aad ∈ s.rd ∧ args s n ∈ s.rd) ∧
    (data ∈ s.wr ∧ work ∈ s.wr ∧ ∀ r ∈ s.wr, (args s n).Disjoint r) ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s n) ∧ work.Disjoint (args s n) ∧
    (bel s).Disjoint ctx ∧ (bel s).Disjoint nonce ∧ (bel s).Disjoint aad ∧ (bel s).Disjoint data ∧
    (bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + (arg s 0).toNat ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s wi).toNat + 768 ≤ 2 ^ 32 ∧ 1520 ≤ s.sp.toNat ∧ s.sp.toNat + 4 * n ≤ 2 ^ 32

def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < n, arg s₁ i = arg s₂ i

/-- What `vg_sm4_gcm_seal` needs: `(ctx = r0, nonce = r1, nonce_len = r2, aad = r3, aad_len = [sp],
data = [sp + 4], len = [sp + 8], tag = [sp + 12], work = [sp + 16])`. -/
def sealPreArm (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
  let aad : Region := ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩
  let data : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
  let tag : Region := ⟨State.addr (arg s 3), 16⟩
  let work : Region := ⟨State.addr (arg s 4), 768⟩
  s.rd = [ctx, nonce, aad, args s 5] ∧ s.wr = [data, tag, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    nonce.Disjoint work ∧ aad.Disjoint data ∧ aad.Disjoint tag ∧ aad.Disjoint work ∧
    data.Disjoint tag ∧ data.Disjoint work ∧ data.Disjoint (args s 5) ∧ tag.Disjoint work ∧
    tag.Disjoint (args s 5) ∧ work.Disjoint (args s 5) ∧
    (bel s).Disjoint ctx ∧ (bel s).Disjoint nonce ∧ (bel s).Disjoint aad ∧ (bel s).Disjoint data ∧
    (bel s).Disjoint tag ∧ (bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + (arg s 0).toNat ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 768 ≤ 2 ^ 32 ∧ 1520 ≤ s.sp.toNat ∧
    s.sp.toNat + 20 ≤ 2 ^ 32

/-- `vg_sm4_gcm_seal`. -/
def sealArm : Contract isa where
  pre := sealPreArm
  post s s' :=
    encryptWith (ctxCiph s.mem (State.addr (s.gpr .r0))) (ctxH s.mem (State.addr (s.gpr .r0))) 16
        (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat) (bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)
        (bytesAt s.mem (State.addr (s.gpr .r3)) (arg s 0).toNat) =
      (bytesAt s'.mem (State.addr (arg s 1)) (arg s 2).toNat, bytesAt s'.mem (State.addr (arg s 3)) 16)
  pub := onePub 5

/-- What `vg_sm4_gcm_open` needs: `(ctx = r0, nonce = r1, nonce_len = r2, aad = r3, aad_len = [sp],
data = [sp + 4], len = [sp + 8], tag = [sp + 12], tag_len = [sp + 16], work = [sp + 20])`. -/
def openPreArm (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
  let aad : Region := ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩
  let data : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
  let tag : Region := ⟨State.addr (arg s 3), (arg s 4).toNat⟩
  let work : Region := ⟨State.addr (arg s 5), 768⟩
  s.rd = [ctx, nonce, aad, tag, args s 6] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ data.Disjoint tag ∧ data.Disjoint work ∧
    data.Disjoint (args s 6) ∧ tag.Disjoint work ∧ work.Disjoint (args s 6) ∧
    (bel s).Disjoint ctx ∧ (bel s).Disjoint nonce ∧ (bel s).Disjoint aad ∧ (bel s).Disjoint data ∧
    (bel s).Disjoint tag ∧ (bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + (arg s 0).toNat ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 768 ≤ 2 ^ 32 ∧ 1520 ≤ s.sp.toNat ∧
    s.sp.toNat + 24 ≤ 2 ^ 32

/-- What `vg_sm4_gcm_open` computes, in a state. -/
abbrev openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (State.addr (s.gpr .r0))) (ctxH s.mem (State.addr (s.gpr .r0)))
    (arg s 4).toNat (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
    (bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat) (bytesAt s.mem (State.addr (s.gpr .r3)) (arg s 0).toNat)
    (bytesAt s.mem (State.addr (arg s 3)) (arg s 4).toNat)

/-- `vg_sm4_gcm_open`. -/
def openArm : Contract isa where
  pre := openPreArm
  post s s' :=
    match openRes s with
    | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (arg s 1)) (arg s 2).toNat = pt
    | none => s'.gpr .r0 = 0 ∧
        bytesAt s'.mem (State.addr (arg s 1)) (arg s 2).toNat = bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat
  pub s₁ s₂ := onePub 6 s₁ s₂ ∧ (openRes s₁).isSome = (openRes s₂).isSome

/-! ## The shared preconditions, from each function's -/

theorem streamFinishPreArm.fin {s : State} (h : streamFinishPreArm s) : finPre 4 3 s := by
  obtain ⟨hrd, hwr, cs, -, cw, -, sw, sa, -, ta, wa, bc, bs, -, bw, fc, fs, -, fw, sp8, spf⟩ := h
  refine ⟨⟨by rw [hrd]; simp, by rw [hrd]; simp⟩, ⟨by rw [hwr]; simp, by rw [hwr]; simp, fun r hr => ?_⟩,
    cs, cw, sw, sa, wa, bc, bs, bw, fc, fs, fw, sp8, spf⟩
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sa.symm
  · exact ta.symm
  · exact wa.symm

theorem streamVerifyPreArm.fin {s : State} (h : streamVerifyPreArm s) : finPre 5 4 s := by
  obtain ⟨hrd, hwr, cs, cw, -, sw, sa, -, wa, bc, bs, -, bw, fc, fs, -, fw, sp8, spf⟩ := h
  refine ⟨⟨by rw [hrd]; simp, by rw [hrd]; simp⟩, ⟨by rw [hwr]; simp, by rw [hwr]; simp, fun r hr => ?_⟩,
    cs, cw, sw, sa, wa, bc, bs, bw, fc, fs, fw, sp8, spf⟩
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sa.symm
  · exact wa.symm

theorem sealPreArm.one {s : State} (h : sealPreArm s) : onePre 5 4 s := by
  obtain ⟨hrd, hwr, cd, -, cw, nd, -, nw, ad, -, aw, -, dw, da, -, ta, wa, bc, bn, ba, bd, -, bw,
    fc, fn, fa, fd, -, fw, sp8, spf⟩ := h
  refine ⟨⟨by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp⟩,
    ⟨by rw [hwr]; simp, by rw [hwr]; simp, fun r hr => ?_⟩,
    cd, cw, nd, nw, ad, aw, dw, da, wa, bc, bn, ba, bd, bw, fc, fn, fa, fd, fw, sp8, spf⟩
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact da.symm
  · exact ta.symm
  · exact wa.symm

theorem openPreArm.one {s : State} (h : openPreArm s) : onePre 6 5 s := by
  obtain ⟨hrd, hwr, cd, cw, nd, nw, ad, aw, -, dw, da, -, wa, bc, bn, ba, bd, -, bw, fc, fn, fa, fd, -, fw,
    sp8, spf⟩ := h
  refine ⟨⟨by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp⟩,
    ⟨by rw [hwr]; simp, by rw [hwr]; simp, fun r hr => ?_⟩,
    cd, cw, nd, nw, ad, aw, dw, da, wa, bc, bn, ba, bd, bw, fc, fn, fa, fd, fw, sp8, spf⟩
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact da.symm
  · exact wa.symm

end VG.Proof.Sm4Gcm.Arm
