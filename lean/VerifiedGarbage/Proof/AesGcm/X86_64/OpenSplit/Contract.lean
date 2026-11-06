module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Contract
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecP
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM `open_split` on x86-64: the contract

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_split`
`(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8,
aad_len = r9, dst = [rsp + 8], len = [rsp + 16], tag = [rsp + 24],
tag_len = [rsp + 32], src = [rsp + 40], src_len = [rsp + 48], work = [rsp + 56])`, for a key
context of kind `M`: `open`'s contract (`openPre`, `openX86_64`), with the
ciphertext read from the `len` bytes at `src` and the plaintext written to
`dst`, which it leaves unspecified when the tag is wrong (its callers zero
it). Only verified code calls it, so its contract is here, with no `Api`.
Its calls take the 56 bytes below the stack pointer, as `seal_split`'s do
(`stk56`).
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- What `vg_aes_gcm_open_split` needs, for a key context of `cl` bytes:
`openPre`'s layout (`oneLay`), with `src`, `src_len` and `work` the fifth to
seventh arguments on the stack, `src` the `len` bytes to read (`src_len`
is `len`), and the 56 bytes
below the stack pointer apart from the buffers. -/
def openSplitPre (cl : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, cl⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let tag : Region := ⟨arg s 2, (arg s 3).toNat⟩
  let src : Region := ⟨arg s 4, (arg s 1).toNat⟩
  let work : Region := ⟨arg s 6, 2560⟩
  s.rd = [ctx, nonce, aad, tag, src, args s 7] ∧ s.wr = [data, work] ∧ oneLay cl 6 7 s ∧
    tag.Disjoint data ∧ tag.Disjoint work ∧ (stk56 s).Disjoint tag ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 64 ∧
    src.Disjoint data ∧ src.Disjoint work ∧ (stk56 s).Disjoint ctx ∧ (stk56 s).Disjoint nonce ∧
    (stk56 s).Disjoint aad ∧ (stk56 s).Disjoint src ∧ (stk56 s).Disjoint data ∧ (stk56 s).Disjoint work ∧
    (arg s 4).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧ 56 ≤ (s.gpr .rsp).toNat ∧ arg s 5 = arg s 1

/-- The result of `open` of the ciphertext at `src`. -/
abbrev openSplitResult (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) (arg s 3).toNat
    (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (arg s 4) (arg s 1).toNat)
    (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (arg s 2) (arg s 3).toNat)

/-- What `vg_aes_gcm_open_split` may leak: whether it succeeds. -/
def openSplitLeak (s : State) : List Nat :=
  if ¬rounds s then [] else [if (openSplitResult s).isSome then 1 else 0]

/-- `vg_aes_gcm_open_split`, for a key context of kind `M`. -/
def openSplitX86_64M (M : CtxMode) : Contract isa where
  pre s := openSplitPre M.len s ∧ M.ok s.mem (s.gpr .rdi)
  post s s' :=
    match openSplitResult s with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (arg s 0) (arg s 1).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0
  pub s₁ s₂ := onePub 7 s₁ s₂ ∧ openSplitLeak s₁ = openSplitLeak s₂

end VG.Proof.AesGcm
