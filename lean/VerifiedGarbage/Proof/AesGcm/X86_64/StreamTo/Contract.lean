import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Contract
import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-!
# AES-GCM streaming encryption out of place, x86-64: the contracts

Untrusted: everything here is checked by Lean. `vg_aes_gcm_stream_encrypt_to`
keeps its working space in a frame of its own (`Verified.stackArgScratch`),
around code proved with the working space as its last argument:
`streamEncryptToScratchContract` is the shared contract with a 2192-byte
`scratch` buffer appended, whatever it holds, which the contract the proof
is written against, `streamEncryptToX86_64M`, implies
(`StreamTo/Verified.lean`): `(ctx = rdi, rounds = rsi, state = rdx,
aad_len = rcx, text_len = r8, src = r9, len = [rsp + 8], dst = [rsp + 16],
dst_len = [rsp + 24], work = [rsp + 32])`, for a key context of kind `M`
(`Stitch.CtxMode`). The code calls `vg_aes_gcm_stream_encrypt`, which uses
2608 bytes of stack, with one argument on the stack, so it uses the 2624
bytes below the stack pointer (`stkS`).
-/

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr ctxCiph ctxH gctr inc32 j0)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- `vg_aes_gcm_stream_encrypt_to` with `scratch: *mut [u64; 274]`. -/
def streamEncryptToScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len"), ("scratch", .array true .u64 274)]

/-- `streamEncryptToContract`, whatever `scratch` is. -/
def streamEncryptToScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamEncryptToScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen src len dst dstLen _scratch =>
      Spec.Gcm.streamEncryptToPre A.ptrBits ctx rounds state aadLen textLen src len dst dstLen)
    (post := fun ctx rounds state aadLen textLen src len dst dstLen _scratch =>
      Spec.Gcm.streamEncryptToPost A.ptrBits ctx rounds state aadLen textLen src len dst dstLen)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_encrypt_to_precomputed` with `scratch: *mut [u64; 274]`. -/
def streamEncryptToPrecomputedScratchSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len"), ("scratch", .array true .u64 274)]

/-- `streamEncryptToPrecomputedContract`, whatever `scratch` is. -/
def streamEncryptToPrecomputedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamEncryptToPrecomputedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen src len dst dstLen _scratch =>
      Spec.Gcm.streamEncryptToPrecomputedPre A.ptrBits ctx rounds state aadLen textLen src len dst dstLen)
    (post := fun ctx rounds state aadLen textLen src len dst dstLen _scratch =>
      Spec.Gcm.streamEncryptToPost A.ptrBits ctx rounds state aadLen textLen src len dst dstLen)
    (writeArgs := true) (stack := stack)

/-- The stack the code uses: the frame of the argument of
`vg_aes_gcm_stream_encrypt`, its return address and its 2608 bytes. -/
abbrev stkS (s : State) : Region := below (s.gpr .rsp) 2624

/-- What the code of `vg_aes_gcm_stream_encrypt_to` needs, for a key context
of kind `M`. -/
def streamToPreM (M : CtxMode) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, M.len⟩
  let st : Region := ⟨s.gpr .rdx, 80⟩
  let src : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let dst : Region := ⟨arg s 1, (arg s 2).toNat⟩
  let scr : Region := ⟨arg s 3, 2192⟩
  s.rd = [ctx, src, args s 4] ∧ s.wr = [st, dst, scr] ∧ arg s 2 = arg s 0 ∧
    ctx.Disjoint st ∧ ctx.Disjoint dst ∧ ctx.Disjoint scr ∧
    st.Disjoint src ∧ st.Disjoint dst ∧ st.Disjoint scr ∧ st.Disjoint (args s 4) ∧
    src.Disjoint dst ∧ src.Disjoint scr ∧
    dst.Disjoint scr ∧ dst.Disjoint (args s 4) ∧ scr.Disjoint (args s 4) ∧
    (ret s).Disjoint st ∧ (ret s).Disjoint dst ∧ (ret s).Disjoint scr ∧
    (stkS s).Disjoint ctx ∧ (stkS s).Disjoint st ∧ (stkS s).Disjoint src ∧ (stkS s).Disjoint dst ∧
    (stkS s).Disjoint scr ∧
    (s.gpr .rdi).toNat + M.len ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (arg s 0).toNat ≤ 2 ^ 64 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 64 ∧
    (arg s 3).toNat + 2192 ≤ 2 ^ 64 ∧
    2624 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧ rounds s ∧ M.ok s.mem (s.gpr .rdi)

def streamToPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧
    arg s₁ 3 = arg s₂ 3

/-- What `vg_aes_gcm_stream_encrypt_to` leaves: `streamEncryptToPost`. -/
def streamToPost (s s' : State) : Prop :=
  let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
  let h := ctxH s.mem (s.gpr .rdi)
  ∀ iv a p, StreamRepr s.mem (s.gpr .rdx) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
    s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = p.length →
    let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r9) (arg s 0).toNat)
    StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c ∧ bytesAt s'.mem (arg s 1) (arg s 0).toNat = c.drop p.length

/-- `vg_aes_gcm_stream_encrypt_to`, for a key context of kind `M`. -/
def streamEncryptToX86_64M (M : CtxMode) : Contract isa where
  pre := streamToPreM M
  post := streamToPost
  pub := streamToPub

end VG.Proof.AesGcm
