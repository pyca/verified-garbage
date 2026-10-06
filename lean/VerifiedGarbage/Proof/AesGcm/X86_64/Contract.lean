import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES-GCM on x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Gcm/Contract.lean`, which imply these
(`Verified.lean`). Every function calls others, whose return addresses are
in the 8 bytes below the stack pointer (`stk`), which no buffer overlaps,
nor the return address (`ret`).
-/

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr KeyRepr ctxCiph ctxH gctr inc32 j0 fullTag tagLenOk encryptWith openResult)

/-- The return address. -/
abbrev ret (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- The stack the calls use. -/
abbrev stk (s : State) : Region := below (s.gpr .rsp) 8

/-- The stack `seal` and `open` use: a frame of one argument, and the return
addresses of a call and of its own calls. -/
abbrev stk24 (s : State) : Region := below (s.gpr .rsp) 24

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 64 := stackArg s i

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (s : State) : Prop :=
  (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14

/-- `vg_aes_gcm_init(key = rdi, key_len = rsi, ctx = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ctx : Region := ⟨s.gpr .rdx, 256⟩
    let scr : Region := ⟨s.gpr .rcx, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧ (ret s).Disjoint ctx ∧ (ret s).Disjoint scr ∧
      (stk s).Disjoint key ∧ (stk s).Disjoint ctx ∧ (stk s).Disjoint scr ∧
      (s.gpr .rdx).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32)
  post s s' := KeyRepr s'.mem (s.gpr .rdx) (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_aes_gcm_stream_init(ctx = rdi, nonce = rsi, nonce_len = rdx, state = rcx, scratch = r8)`. -/
def streamInitX86_64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 256⟩
    let nonce : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let st : Region := ⟨s.gpr .rcx, 80⟩
    let scr : Region := ⟨s.gpr .r8, 2560⟩
    s.rd = [ctx, nonce] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧ st.Disjoint scr ∧
      (ret s).Disjoint st ∧ (ret s).Disjoint scr ∧
      (stk s).Disjoint ctx ∧ (stk s).Disjoint nonce ∧ (stk s).Disjoint st ∧ (stk s).Disjoint scr ∧
      (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 2560 ≤ 2 ^ 64
  post s s' := ∀ ciph, StreamRepr s'.mem (s.gpr .rcx) ciph (ctxH s.mem (s.gpr .rdi))
    (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) [] []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_aes_gcm_stream_aad(ctx = rdi, state = rsi, aad_len = rdx, data = rcx, len = r8, scratch = r9)`. -/
def streamAadX86_64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 256⟩
    let st : Region := ⟨s.gpr .rsi, 80⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2560⟩
    s.rd = [ctx, data] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ data.Disjoint st ∧ data.Disjoint scr ∧ st.Disjoint scr ∧
      (ret s).Disjoint st ∧ (ret s).Disjoint scr ∧
      (stk s).Disjoint ctx ∧ (stk s).Disjoint data ∧ (stk s).Disjoint st ∧ (stk s).Disjoint scr ∧
      (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rsi).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 2560 ≤ 2 ^ 64
  post s s' := ∀ ciph iv a, StreamRepr s.mem (s.gpr .rsi) ciph (ctxH s.mem (s.gpr .rdi)) iv a [] →
    s.gpr .rdx = BitVec.ofNat 64 a.length →
    StreamRepr s'.mem (s.gpr .rsi) ciph (ctxH s.mem (s.gpr .rdi)) iv
      (a ++ bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- What `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` need:
`(ctx = rdi, rounds = rsi, state = rdx, aad_len = rcx, text_len = r8, data = r9, len = [rsp + 8],
scratch = [rsp + 16])`, for a key context of `cl` bytes. -/
def streamCryptPre (cl : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, cl⟩
  let st : Region := ⟨s.gpr .rdx, 80⟩
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let scr : Region := ⟨arg s 1, 2560⟩
  s.rd = [ctx, args s 2] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ st.Disjoint (args s 2) ∧ data.Disjoint scr ∧
    data.Disjoint (args s 2) ∧ scr.Disjoint (args s 2) ∧
    (ret s).Disjoint st ∧ (ret s).Disjoint data ∧ (ret s).Disjoint scr ∧
    (stk24 s).Disjoint ctx ∧ (stk24 s).Disjoint st ∧ (stk24 s).Disjoint data ∧ (stk24 s).Disjoint scr ∧
    (s.gpr .rdi).toNat + cl ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (arg s 0).toNat ≤ 2 ^ 64 ∧ (arg s 1).toNat + 2560 ≤ 2 ^ 64 ∧
    24 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64 ∧ rounds s

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncryptX86_64 : Contract isa where
  pre := streamCryptPre 256
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let h := ctxH s.mem (s.gpr .rdi)
    ∀ iv a p, StreamRepr s.mem (s.gpr .rdx) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r9) (arg s 0).toNat)
      StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c ∧ bytesAt s'.mem (s.gpr .r9) (arg s 0).toNat = c.drop p.length
  pub := streamCryptPub

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecryptX86_64 : Contract isa where
  pre := streamCryptPre 256
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let h := ctxH s.mem (s.gpr .rdi)
    ∀ iv a c, StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
      s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = c.length →
      let c' := c ++ bytesAt s.mem (s.gpr .r9) (arg s 0).toNat
      StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c' ∧
        bytesAt s'.mem (s.gpr .r9) (arg s 0).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := streamCryptPub

/-- What `vg_aes_gcm_stream_finish` needs: `(ctx = rdi, rounds = rsi, state = rdx, aad_len = rcx,
text_len = r8, tag = r9, work = [rsp + 8])`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let st : Region := ⟨s.gpr .rdx, 80⟩
  let tag : Region := ⟨s.gpr .r9, 16⟩
  let work : Region := ⟨arg s 0, 2560⟩
  s.rd = [ctx, args s 1] ∧ s.wr = [st, tag, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint work ∧ tag.Disjoint st ∧ tag.Disjoint work ∧
    (ret s).Disjoint st ∧ (ret s).Disjoint tag ∧ (ret s).Disjoint work ∧
    (stk s).Disjoint ctx ∧ (stk s).Disjoint st ∧ (stk s).Disjoint tag ∧ (stk s).Disjoint work ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 16 ≤ 2 ^ 64 ∧
    (arg s 0).toNat + 2560 ≤ 2 ^ 64 ∧ rounds s

/-- What `vg_aes_gcm_stream_verify` needs: `(ctx = rdi, rounds = rsi, state = rdx, aad_len = rcx,
text_len = r8, tag = r9, tag_len = [rsp + 8], work = [rsp + 16])`. -/
def verifyPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let st : Region := ⟨s.gpr .rdx, 80⟩
  let tag : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let work : Region := ⟨arg s 1, 2560⟩
  s.rd = [ctx, tag, args s 2] ∧ s.wr = [st, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint work ∧ tag.Disjoint work ∧ work.Disjoint (args s 2) ∧
    (ret s).Disjoint st ∧ (ret s).Disjoint work ∧
    (stk s).Disjoint ctx ∧ (stk s).Disjoint st ∧ (stk s).Disjoint work ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (arg s 0).toNat ≤ 2 ^ 64 ∧ (arg s 1).toNat + 2560 ≤ 2 ^ 64 ∧
    (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64 ∧ rounds s

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinishX86_64 : Contract isa where
  pre := finPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let h := ctxH s.mem (s.gpr .rdi)
    ∀ iv a c, StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
      s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = c.length →
      bytesAt s'.mem (s.gpr .r9) 16 = fullTag ciph h iv a c
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    arg s₁ 0 = arg s₂ 0

/-- `vg_aes_gcm_stream_verify`. -/
def streamVerifyX86_64 : Contract isa where
  pre := verifyPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let h := ctxH s.mem (s.gpr .rdi)
    let tl := (arg s 0).toNat
    ∀ iv a c, StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
      s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (s.gpr .r9) tl then (s'.gpr .rax).setWidth 32 = 1
      else (s'.gpr .rax).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

/-- What `vg_aes_gcm_seal` and `vg_aes_gcm_open` both need, but for `tag` and
the permissions: `(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx,
aad = r8, aad_len = r9, data = [rsp + 8], len = [rsp + 16], tag = [rsp + 24])`,
`work` the `w`-th argument on the stack, and `n` arguments there, for a key
context of `cl` bytes. -/
def oneLay (cl w n : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, cl⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let work : Region := ⟨arg s w, 2560⟩
  ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s n) ∧ work.Disjoint (args s n) ∧
    (ret s).Disjoint data ∧ (ret s).Disjoint work ∧
    (stk24 s).Disjoint ctx ∧ (stk24 s).Disjoint nonce ∧ (stk24 s).Disjoint aad ∧ (stk24 s).Disjoint data ∧
    (stk24 s).Disjoint work ∧
    (s.gpr .rdi).toNat + cl ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧
    (arg s w).toNat + 2560 ≤ 2 ^ 64 ∧ 24 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 8 * (n + 1) ≤ 2 ^ 64 ∧
    rounds s

/-- What `vg_aes_gcm_seal` needs: `oneLay`, with `tag` a 16-byte buffer to
write and `work = [rsp + 32]`, for a key context of `cl` bytes. -/
def sealPre (cl : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, cl⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let tag : Region := ⟨arg s 2, 16⟩
  let work : Region := ⟨arg s 3, 2560⟩
  s.rd = [ctx, nonce, aad, args s 4] ∧ s.wr = [data, tag, work] ∧ oneLay cl 3 4 s ∧
    tag.Disjoint data ∧ tag.Disjoint work ∧ (ret s).Disjoint tag ∧ (arg s 2).toNat + 16 ≤ 2 ^ 64

/-- What `vg_aes_gcm_open` needs: `oneLay`, with the received tag the
`tag_len = [rsp + 32]` bytes at `tag`, to read, and `work = [rsp + 40]`, for
a key context of `cl` bytes. -/
def openPre (cl : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, cl⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let tag : Region := ⟨arg s 2, (arg s 3).toNat⟩
  let work : Region := ⟨arg s 4, 2560⟩
  s.rd = [ctx, nonce, aad, tag, args s 5] ∧ s.wr = [data, work] ∧ oneLay cl 4 5 s ∧
    tag.Disjoint data ∧ tag.Disjoint work ∧ (stk24 s).Disjoint tag ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 64

def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < n, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_seal`. -/
def sealX86_64 : Contract isa where
  pre := sealPre 256
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) 16
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (arg s 0) (arg s 1).toNat)
        (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      (bytesAt s'.mem (arg s 0) (arg s 1).toNat, bytesAt s'.mem (arg s 2) 16)
  pub := onePub 4

/-- What `vg_aes_gcm_open` may leak (`Spec.Gcm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬rounds s then [] else
  [if (openResult (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) (arg s 3).toNat
      (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (arg s 0) (arg s 1).toNat)
      (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (arg s 2) (arg s 3).toNat)).isSome
    then 1 else 0]

/-- `vg_aes_gcm_open`. -/
def openX86_64 : Contract isa where
  pre := openPre 256
  post s s' :=
    match openResult (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) (arg s 3).toNat
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (arg s 0) (arg s 1).toNat)
        (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (arg s 2) (arg s 3).toNat) with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (arg s 0) (arg s 1).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        bytesAt s'.mem (arg s 0) (arg s 1).toNat = bytesAt s.mem (arg s 0) (arg s 1).toNat
  pub s₁ s₂ := onePub 5 s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesGcm
