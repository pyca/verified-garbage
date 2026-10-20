module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Contract
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecP


/-!
# AES-GCM `seal_split` on x86-64: the contract the proof is written against

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_split`
`(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8,
aad_len = r9, src = [rsp + 8], src_len = [rsp + 16], dst = [rsp + 24],
len = [rsp + 32], tag = [rsp + 40], work = [rsp + 48])`, for a key context
of kind `M`; the shared contracts of `Spec/Gcm/OutOfPlace.lean` and
`Spec/Gcm/Prepared.lean` imply it. Its calls take the 56 bytes below the
stack pointer: the call of `vg_aes_gcm_encrypt_blocks_to`, its three
arguments on the stack, its return address and the 24 bytes its stack may
take (`BlkToFn.xd`).
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- The stack `seal_split` uses: three arguments, the return address and
the stack of a call. -/
abbrev stk56 (s : State) : Region := below (s.gpr .rsp) 56

/-- What `vg_aes_gcm_seal_split` needs, for a key context of `cl` bytes. -/
def splitPre (cl : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, cl⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let src : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let data : Region := ⟨arg s 2, (arg s 3).toNat⟩
  let tag : Region := ⟨arg s 4, 16⟩
  let work : Region := ⟨arg s 5, 2560⟩
  s.rd = [ctx, nonce, aad, src, args s 6] ∧ s.wr = [data, tag, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ src.Disjoint data ∧ src.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s 6) ∧ work.Disjoint (args s 6) ∧
    tag.Disjoint data ∧ tag.Disjoint work ∧
    (ret s).Disjoint data ∧ (ret s).Disjoint work ∧ (ret s).Disjoint tag ∧
    (stk56 s).Disjoint ctx ∧ (stk56 s).Disjoint nonce ∧ (stk56 s).Disjoint aad ∧ (stk56 s).Disjoint src ∧
    (stk56 s).Disjoint data ∧ (stk56 s).Disjoint work ∧
    (s.gpr .rdi).toNat + cl ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 64 ∧ (arg s 4).toNat + 16 ≤ 2 ^ 64 ∧
    (arg s 5).toNat + 2560 ≤ 2 ^ 64 ∧ 56 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 56 ≤ 2 ^ 64 ∧
    (arg s 1).toNat ≤ (arg s 3).toNat ∧ rounds s

/-- `vg_aes_gcm_seal_split`, for a key context of kind `M`. -/
def sealSplitX86_64M (M : CtxMode) : Contract isa where
  pre s := splitPre M.len s ∧ M.ok s.mem (s.gpr .rdi)
  post s s' :=
    (arg s 1).toNat ≤ (arg s 3).toNat →
    encryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) 16
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (bytesAt s.mem (arg s 0) (arg s 1).toNat ++ (bytesAt s.mem (arg s 2) (arg s 3).toNat).drop (arg s 1).toNat)
        (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      (bytesAt s'.mem (arg s 2) (arg s 3).toNat, bytesAt s'.mem (arg s 4) 16)
  pub := onePub 6

end VG.Proof.AesGcm
