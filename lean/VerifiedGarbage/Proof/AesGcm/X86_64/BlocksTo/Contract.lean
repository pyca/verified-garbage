import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksContract

/-!
# AES-GCM on whole blocks out of place, x86-64: the contract the proof is written against

Untrusted: everything here is checked by Lean. `vg_aes_gcm_encrypt_blocks_to`
`(ctx = rdi, rounds = rsi, counter = rdx, y = rcx, src = r8, n = r9,
dst = [rsp + 8], dst_n = [rsp + 16], scratch = [rsp + 24])`; the shared
contract of `Spec/Gcm/OutOfPlace.lean` implies this one
(`BlocksTo/Verified.lean`). `blocksToPreM M` is for a key context of kind `M`
(`Stitch.CtxMode`), as `blocksPreM` is. The function calls
`vg_aes_gcm_encrypt_blocks` with one argument on the stack, and that makes
calls, so it uses the 24 bytes below the stack pointer (`stk24`).
-/

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- What `vg_aes_gcm_encrypt_blocks_to` needs, for a key context of kind `M`. -/
def blocksToPreM (M : CtxMode) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, M.len⟩
  let ctr : Region := ⟨s.gpr .rdx, 16⟩
  let y : Region := ⟨s.gpr .rcx, 16⟩
  let src : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 16⟩
  let dst : Region := ⟨arg s 0, (arg s 1).toNat * 16⟩
  let scr : Region := ⟨arg s 2, 2112⟩
  s.rd = [ctx, src, args s 3] ∧ s.wr = [ctr, y, dst, scr] ∧ arg s 1 = s.gpr .r9 ∧
    ctx.Disjoint ctr ∧ ctx.Disjoint y ∧ ctx.Disjoint dst ∧ ctx.Disjoint scr ∧
    ctr.Disjoint y ∧ ctr.Disjoint src ∧ ctr.Disjoint dst ∧ ctr.Disjoint scr ∧ ctr.Disjoint (args s 3) ∧
    y.Disjoint src ∧ y.Disjoint dst ∧ y.Disjoint scr ∧ y.Disjoint (args s 3) ∧
    src.Disjoint dst ∧ src.Disjoint scr ∧
    dst.Disjoint scr ∧ dst.Disjoint (args s 3) ∧ scr.Disjoint (args s 3) ∧
    (ret s).Disjoint ctr ∧ (ret s).Disjoint y ∧ (ret s).Disjoint dst ∧ (ret s).Disjoint scr ∧
    (stk24 s).Disjoint ctx ∧ (stk24 s).Disjoint ctr ∧ (stk24 s).Disjoint y ∧ (stk24 s).Disjoint src ∧
    (stk24 s).Disjoint dst ∧ (stk24 s).Disjoint scr ∧
    (s.gpr .rdi).toNat + M.len ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + (s.gpr .r9).toNat * 16 ≤ 2 ^ 64 ∧
    (arg s 0).toNat + (arg s 1).toNat * 16 ≤ 2 ^ 64 ∧ (arg s 2).toNat + 2112 ≤ 2 ^ 64 ∧
    24 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧ rounds s ∧ M.ok s.mem (s.gpr .rdi)

def blocksToPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2

/-- What `vg_aes_gcm_encrypt_blocks_to` leaves: the encryption of the plaintext
in the output, the counter advanced, and `Y` continued over the ciphertext. -/
def blocksToPost (s s' : State) : Prop :=
  let n := (s.gpr .r9).toNat
  let c := ctr32 (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (blockAt s.mem (s.gpr .rdx))
    (blocksAt s.mem (s.gpr .r8) n)
  blocksAt s'.mem (arg s 0) n = c ∧
    blockAt s'.mem (s.gpr .rdx) = Nat.repeat inc32 n (blockAt s.mem (s.gpr .rdx)) ∧
    blockAt s'.mem (s.gpr .rcx) = ghashFrom (ctxH s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rcx)) c

/-- `vg_aes_gcm_encrypt_blocks_to`, for a key context of kind `M`. -/
def encryptBlocksToX86_64M (M : CtxMode) : Contract isa where
  pre := blocksToPreM M
  post := blocksToPost
  pub := blocksToPub

end VG.Proof.AesGcm
