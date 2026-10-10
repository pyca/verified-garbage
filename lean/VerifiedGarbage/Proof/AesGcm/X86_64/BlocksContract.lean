import VerifiedGarbage.Proof.AesGcm.X86_64.Contract
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecP

/-!
# AES-GCM on whole blocks, x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. `vg_aes_gcm_encrypt_blocks`
and `vg_aes_gcm_decrypt_blocks` `(ctx = rdi, rounds = rsi, counter = rdx,
y = rcx, data = r8, n = r9, scratch = [rsp + 8])`; the shared contracts of
`Spec/Gcm/Contract.lean` imply these (`BlocksVerified.lean`). `blocksPreM M`
is `blocksPre` for a key context of kind `M` (`Stitch.CtxMode`): its length,
and what it holds beyond the key schedule and the hash subkey, as the
`_precomputed` functions' (`Spec/Gcm/Precomputed.lean`).
-/

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- What both need. -/
def blocksPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let ctr : Region := ⟨s.gpr .rdx, 16⟩
  let y : Region := ⟨s.gpr .rcx, 16⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 16⟩
  let scr : Region := ⟨arg s 0, 2112⟩
  s.rd = [ctx, args s 1] ∧ s.wr = [ctr, y, data, scr] ∧
    ctx.Disjoint ctr ∧ ctx.Disjoint y ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    ctr.Disjoint y ∧ ctr.Disjoint data ∧ ctr.Disjoint scr ∧ ctr.Disjoint (args s 1) ∧
    y.Disjoint data ∧ y.Disjoint scr ∧ y.Disjoint (args s 1) ∧
    data.Disjoint scr ∧ data.Disjoint (args s 1) ∧ scr.Disjoint (args s 1) ∧
    (ret s).Disjoint ctr ∧ (ret s).Disjoint y ∧ (ret s).Disjoint data ∧ (ret s).Disjoint scr ∧
    (stk s).Disjoint ctx ∧ (stk s).Disjoint ctr ∧ (stk s).Disjoint y ∧ (stk s).Disjoint data ∧
    (stk s).Disjoint scr ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat * 16 ≤ 2 ^ 64 ∧ (arg s 0).toNat + 2112 ≤ 2 ^ 64 ∧
    (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧ rounds s

open VG.Proof.Gcm.X86_64.Stitch (CtxMode) in
/-- What both need, for a key context of kind `M`. -/
def blocksPreM (M : CtxMode) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, M.len⟩
  let ctr : Region := ⟨s.gpr .rdx, 16⟩
  let y : Region := ⟨s.gpr .rcx, 16⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 16⟩
  let scr : Region := ⟨arg s 0, 2112⟩
  s.rd = [ctx, args s 1] ∧ s.wr = [ctr, y, data, scr] ∧
    ctx.Disjoint ctr ∧ ctx.Disjoint y ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    ctr.Disjoint y ∧ ctr.Disjoint data ∧ ctr.Disjoint scr ∧ ctr.Disjoint (args s 1) ∧
    y.Disjoint data ∧ y.Disjoint scr ∧ y.Disjoint (args s 1) ∧
    data.Disjoint scr ∧ data.Disjoint (args s 1) ∧ scr.Disjoint (args s 1) ∧
    (ret s).Disjoint ctr ∧ (ret s).Disjoint y ∧ (ret s).Disjoint data ∧ (ret s).Disjoint scr ∧
    (stk s).Disjoint ctx ∧ (stk s).Disjoint ctr ∧ (stk s).Disjoint y ∧ (stk s).Disjoint data ∧
    (stk s).Disjoint scr ∧
    (s.gpr .rdi).toNat + M.len ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat * 16 ≤ 2 ^ 64 ∧ (arg s 0).toNat + 2112 ≤ 2 ^ 64 ∧
    (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧ rounds s ∧ M.ok s.mem (s.gpr .rdi)

theorem blocksPreM_base {s : State} (h : blocksPre s) : blocksPreM Gcm.X86_64.Stitch.CtxMode.base s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
    a₂₈ a₂₉ a₃₀ a₃₁
  have a₃₂ := h
  clear h
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂, a₂₃,
    a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, trivial⟩

def blocksPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0

/-- `vg_aes_gcm_encrypt_blocks`. -/
def encryptBlocksX86_64 : Contract isa where
  pre := blocksPre
  post s s' :=
    let n := (s.gpr .r9).toNat
    let c := ctr32 (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (blockAt s.mem (s.gpr .rdx))
      (blocksAt s.mem (s.gpr .r8) n)
    blocksAt s'.mem (s.gpr .r8) n = c ∧ blockAt s'.mem (s.gpr .rdx) = Nat.repeat inc32 n (blockAt s.mem (s.gpr .rdx)) ∧
      blockAt s'.mem (s.gpr .rcx) = ghashFrom (ctxH s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rcx)) c
  pub := blocksPub

/-- `vg_aes_gcm_decrypt_blocks`. -/
def decryptBlocksX86_64 : Contract isa where
  pre := blocksPre
  post s s' :=
    let n := (s.gpr .r9).toNat
    let c := blocksAt s.mem (s.gpr .r8) n
    blocksAt s'.mem (s.gpr .r8) n =
        ctr32 (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (blockAt s.mem (s.gpr .rdx)) c ∧
      blockAt s'.mem (s.gpr .rdx) = Nat.repeat inc32 n (blockAt s.mem (s.gpr .rdx)) ∧
      blockAt s'.mem (s.gpr .rcx) = ghashFrom (ctxH s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rcx)) c
  pub := blocksPub

open VG.Proof.Gcm.X86_64.Stitch (CtxMode) in
/-- `vg_aes_gcm_encrypt_blocks`, for a key context of kind `M`. -/
def encryptBlocksX86_64M (M : CtxMode) : Contract isa where
  pre := blocksPreM M
  post := encryptBlocksX86_64.post
  pub := blocksPub

open VG.Proof.Gcm.X86_64.Stitch (CtxMode) in
/-- `vg_aes_gcm_decrypt_blocks`, for a key context of kind `M`. -/
def decryptBlocksX86_64M (M : CtxMode) : Contract isa where
  pre := blocksPreM M
  post := decryptBlocksX86_64.post
  pub := blocksPub

/-! ### For a key context of kind `M`

The contracts of the `_precomputed` functions (`Spec/Gcm/Precomputed.lean`):
those above, with the key context `M.len` bytes long and holding what `M`
says. -/

section
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- `vg_aes_gcm_init_precomputed(key = rdi, key_len = rsi, ctx = rdx, scratch = rcx)`. -/
def initPrecomputedX86_64 : Contract isa where
  pre := initPreL 1024
  post s s' := Spec.Gcm.KeyRepr s'.mem (s.gpr .rdx) (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) ∧
    Spec.Gcm.PowersRepr s'.mem (s.gpr .rdx)
  pub := initX86_64.pub

/-- `vg_aes_gcm_seal`, for a key context of kind `M`. -/
def sealX86_64M (M : CtxMode) : Contract isa where
  pre s := sealPre M.len s ∧ M.ok s.mem (s.gpr .rdi)
  post := sealX86_64.post
  pub := sealX86_64.pub

/-- `vg_aes_gcm_open`, for a key context of kind `M`. -/
def openX86_64M (M : CtxMode) : Contract isa where
  pre s := openPre M.len s ∧ M.ok s.mem (s.gpr .rdi)
  post := openX86_64.post
  pub := openX86_64.pub

/-- `vg_aes_gcm_stream_encrypt`, for a key context of kind `M`. -/
def streamEncryptX86_64M (M : CtxMode) : Contract isa where
  pre s := streamCryptPre M.len s ∧ M.ok s.mem (s.gpr .rdi)
  post := streamEncryptX86_64.post
  pub := streamCryptPub

/-- `vg_aes_gcm_stream_decrypt`, for a key context of kind `M`. -/
def streamDecryptX86_64M (M : CtxMode) : Contract isa where
  pre s := streamCryptPre M.len s ∧ M.ok s.mem (s.gpr .rdi)
  post := streamDecryptX86_64.post
  pub := streamCryptPub

end

end VG.Proof.AesGcm
