import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-GCM-SIV on AArch64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/GcmSiv/Contract.lean`, which imply these
(`Verified.lean`). Every argument is in a register, and a call (`bl`)
stores nothing in memory, so no stack is used.
-/

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.GcmSiv (ctxCiph keyLen encryptWith decryptWith zeros)

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 14

/-- What `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` need: `(schedule = x0,
rounds = x1, nonce = x2, aad = x3, aad_len = x4, data = x5, len = x6, work = x7)`. -/
def onePre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .x0, 240⟩
  let nonce : Region := ⟨s.gpr .x2, 12⟩
  let aad : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let work : Region := ⟨s.gpr .x7, 4096⟩
  s.rd = [sch, nonce, aad] ∧ s.wr = [data, work] ∧
    sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ data.Disjoint work ∧
    (s.gpr .x0).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x7).toNat + 4096 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1)

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp

/-- `vg_aes_gcm_siv_seal`. -/
def sealAArch64 : Contract isa where
  pre := onePre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (keyLen (s.gpr .x1).toNat)
        (bytesAt s.mem (s.gpr .x2) 12) (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
        (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) =
      (bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat, bytesAt s'.mem (s.gpr .x7) 16)
  pub := onePub

/-- What `vg_aes_gcm_siv_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (keyLen (s.gpr .x1).toNat)
    (bytesAt s.mem (s.gpr .x2) 12) (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
    (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (bytesAt s.mem (s.gpr .x7) 16)

/-- What `vg_aes_gcm_siv_open` leaves in `x0` and in the `n` bytes of data
at `D`, for the result `r`. Irreducible, so that checking a state against
it never evaluates `r`. -/
@[irreducible] def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
  | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : (s'.gpr .x0).setWidth 32 = 1) (hd : bytesAt s'.mem D n = pt) :
    openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : (s'.gpr .x0).setWidth 32 = 0) (hd : bytesAt s'.mem D n = zeros n) :
    openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

/-- `vg_aes_gcm_siv_open`. It does not branch on whether the tag is right,
so its runs are related without the leak the shared contract allows. -/
def openAArch64 : Contract isa where
  pre := onePre
  post s s' := openPost (openResult s) s' (s.gpr .x5) (s.gpr .x6).toNat
  pub := onePub

end VG.Proof.AesGcmSiv.AArch64
