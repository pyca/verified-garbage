import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# AES-CCM on x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ccm/Contract.lean`, which imply these
(`Verified.lean`), with a 2560-byte `work` buffer appended
(`Proof/AesCcm/Scratch.lean`). `seal` and `open` call `vg_cmac_aes_update`, which calls
`vg_aes_ctr32`, and `vg_aes_ctr32` directly: the return addresses are in the
16 bytes below the stack pointer (`stk16`), which no buffer overlaps, nor
the return address (`ret`).
-/

namespace VG.Proof.AesCcm

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- The return address. -/
abbrev ret (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- The stack the calls use. -/
abbrev stk16 (s : State) : Region := below (s.gpr .rsp) 16

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 64 := stackArg s i

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (s : State) : Prop :=
  (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14

/-- What `vg_aes_ccm_seal` and `vg_aes_ccm_open` both need, but for the
permissions: `(schedule = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx,
aad = r8, aad_len = r9, data = [rsp + 8], len = [rsp + 16], tag = [rsp + 24],
tag_len = [rsp + 32], work = [rsp + 40])`. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let tag : Region := ⟨arg s 2, (arg s 3).toNat⟩
  let work : Region := ⟨arg s 4, 2560⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s 5) ∧ work.Disjoint (args s 5) ∧
    (ret s).Disjoint data ∧ (ret s).Disjoint work ∧
    (stk16 s).Disjoint sch ∧ (stk16 s).Disjoint nonce ∧ (stk16 s).Disjoint aad ∧ (stk16 s).Disjoint data ∧
    (stk16 s).Disjoint tag ∧ (stk16 s).Disjoint work ∧
    (s.gpr .rdi).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 64 ∧
    (arg s 4).toNat + 2560 ≤ 2 ^ 64 ∧ 16 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧
    rounds s ∧ valid (arg s 3).toNat (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat = true

/-- What `vg_aes_ccm_seal` needs: `oneLay`, with `tag` the `tag_len` bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let tag : Region := ⟨arg s 2, (arg s 3).toNat⟩
  let work : Region := ⟨arg s 4, 2560⟩
  s.rd = [sch, nonce, aad, args s 5] ∧ s.wr = [data, tag, work] ∧ oneLay s ∧ (ret s).Disjoint tag

/-- What `vg_aes_ccm_open` needs: `oneLay`, with the received tag the
`tag_len` bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let tag : Region := ⟨arg s 2, (arg s 3).toNat⟩
  let work : Region := ⟨arg s 4, 2560⟩
  s.rd = [sch, nonce, aad, tag, args s 5] ∧ s.wr = [data, work] ∧ oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `vg_aes_ccm_seal`. -/
def sealX86_64 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (arg s 3).toNat
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (arg s 0) (arg s 1).toNat)
        (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      (bytesAt s'.mem (arg s 0) (arg s 1).toNat, bytesAt s'.mem (arg s 2) (arg s 3).toNat)
  pub := onePub

/-- What `vg_aes_ccm_open` may leak (`Spec.Ccm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬rounds s then [] else
  [if (decryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (arg s 3).toNat
      (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (arg s 0) (arg s 1).toNat)
      (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (arg s 2) (arg s 3).toNat)).isSome
    then 1 else 0]

/-- `vg_aes_ccm_open`. -/
def openX86_64 : Contract isa where
  pre := openPre
  post s s' :=
    match decryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (arg s 3).toNat
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (arg s 0) (arg s 1).toNat)
        (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (arg s 2) (arg s 3).toNat) with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (arg s 0) (arg s 1).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (arg s 0) (arg s 1).toNat = zeros (arg s 1).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesCcm
