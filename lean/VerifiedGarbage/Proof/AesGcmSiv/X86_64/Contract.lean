import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# AES-GCM-SIV on x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The shared contracts of
`Spec/GcmSiv/Contract.lean`, with the working space as a last argument
(`Proof/AesGcmSiv/Scratch.lean`), imply these (`Verified.lean`). `seal` and `open` call `vg_aes_ctr32`,
`vg_aes_expand_key` and `vg_ghash`, which make no calls: the return address
is in the 8 bytes below the stack pointer (`stk8`), which no buffer
overlaps, nor the return address (`ret`).
-/

namespace VG.Proof.AesGcmSiv

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.GcmSiv (ctxCiph keyLen encryptWith decryptWith zeros)

/-- The return address. -/
abbrev ret (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- The stack the calls use. -/
abbrev stk8 (s : State) : Region := below (s.gpr .rsp) 8

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 64 := stackArg s i

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (s : State) : Prop := (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 14

/-- What `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` both need, but for
the permissions: `(schedule = rdi, rounds = rsi, nonce = rdx, aad = rcx,
aad_len = r8, data = r9, len = [rsp + 8], tag = [rsp + 16],
work = [rsp + 24])`. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, 12⟩
  let aad : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let tag : Region := ⟨arg s 1, 16⟩
  let work : Region := ⟨arg s 2, 3816⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s 3) ∧ work.Disjoint (args s 3) ∧
    (ret s).Disjoint data ∧ (ret s).Disjoint work ∧
    (stk8 s).Disjoint sch ∧ (stk8 s).Disjoint nonce ∧ (stk8 s).Disjoint aad ∧ (stk8 s).Disjoint data ∧
    (stk8 s).Disjoint tag ∧ (stk8 s).Disjoint work ∧
    (s.gpr .rdi).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (arg s 0).toNat ≤ 2 ^ 64 ∧
    (arg s 1).toNat + 16 ≤ 2 ^ 64 ∧ (arg s 2).toNat + 3816 ≤ 2 ^ 64 ∧ 8 ≤ (s.gpr .rsp).toNat ∧
    (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧ rounds s

/-- What `vg_aes_gcm_siv_seal` needs: `oneLay`, with `tag` the 16 bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, 12⟩
  let aad : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let tag : Region := ⟨arg s 1, 16⟩
  let work : Region := ⟨arg s 2, 3816⟩
  s.rd = [sch, nonce, aad, args s 3] ∧ s.wr = [data, tag, work] ∧ oneLay s ∧ (ret s).Disjoint tag

/-- What `vg_aes_gcm_siv_open` needs: `oneLay`, with the received tag the 16
bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, 12⟩
  let aad : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let tag : Region := ⟨arg s 1, 16⟩
  let work : Region := ⟨arg s 2, 3816⟩
  s.rd = [sch, nonce, aad, tag, args s 3] ∧ s.wr = [data, work] ∧ oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_siv_seal`. -/
def sealX86_64 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (keyLen (s.gpr .rsi).toNat)
        (bytesAt s.mem (s.gpr .rdx) 12) (bytesAt s.mem (s.gpr .r9) (arg s 0).toNat)
        (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) =
      (bytesAt s'.mem (s.gpr .r9) (arg s 0).toNat, bytesAt s'.mem (arg s 1) 16)
  pub := onePub

/-- What `vg_aes_gcm_siv_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (keyLen (s.gpr .rsi).toNat)
    (bytesAt s.mem (s.gpr .rdx) 12) (bytesAt s.mem (s.gpr .r9) (arg s 0).toNat)
    (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (bytesAt s.mem (arg s 1) 16)

/-- What `vg_aes_gcm_siv_open` leaves in `rax` and in the `n` bytes of data
at `D`, for the result `r`. Irreducible, so that checking a state against
it never evaluates `r`. -/
@[irreducible] def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
  | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : (s'.gpr .rax).setWidth 32 = 1) (hd : bytesAt s'.mem D n = pt) : openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : (s'.gpr .rax).setWidth 32 = 0) (hd : bytesAt s'.mem D n = zeros n) : openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

/-- What `vg_aes_gcm_siv_open` may leak (`Spec.GcmSiv.openLeak`): whether it
succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬rounds s then [] else [if (openResult s).isSome then 1 else 0]

/-- `vg_aes_gcm_siv_open`. -/
def openX86_64 : Contract isa where
  pre := openPre
  post s s' := openPost (openResult s) s' (s.gpr .r9) (arg s 0).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesGcmSiv
