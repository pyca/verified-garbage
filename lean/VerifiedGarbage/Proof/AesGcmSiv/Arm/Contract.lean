import VerifiedGarbage.Proof.AesGcm.Arm.Contract
import VerifiedGarbage.Spec.GcmSiv.Contract

/-!
# AES-GCM-SIV on ARMv7: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The shared contracts of
`Spec/GcmSiv/Contract.lean`, with the working space as a last argument
(`Proof/AesGcmSiv/Scratch.lean`), imply these (`Verified.lean`). The
functions take `aad_len`, `data`, `len`, `tag` and `work` on the stack, and
call others in frames that push their stack arguments in the 8 bytes below
the stack pointer (`bel`), which no buffer overlaps.
-/

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.GcmSiv (ctxCiph keyLen encryptWith decryptWith zeros)
open VG.Proof.AesGcm.Arm (bel arg args)

abbrev rounds (r : BitVec 32) : Prop := r.toNat = 10 ∨ r.toNat = 14

/-- What `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` both need, but for
the permissions: `(schedule = r0, rounds = r1, nonce = r2, aad = r3,
aad_len = [sp], data = [sp + 4], len = [sp + 8], tag = [sp + 12],
work = [sp + 16])`. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨State.addr (s.gpr .r0), 240⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), 12⟩
  let aad : Region := ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩
  let data : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
  let tag : Region := ⟨State.addr (arg s 3), 16⟩
  let work : Region := ⟨State.addr (arg s 4), 3760⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧ data.Disjoint work ∧
    data.Disjoint (args s 5) ∧ work.Disjoint (args s 5) ∧
    (bel s).Disjoint sch ∧ (bel s).Disjoint nonce ∧ (bel s).Disjoint aad ∧ (bel s).Disjoint data ∧
    (bel s).Disjoint tag ∧ (bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 12 ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + (arg s 0).toNat ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 3760 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
    s.sp.toNat + 20 ≤ 2 ^ 32 ∧ rounds (s.gpr .r1)

/-- What `vg_aes_gcm_siv_seal` needs: `oneLay`, with `tag` the 16 bytes to
write, apart from the stack arguments. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨State.addr (s.gpr .r0), 240⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), 12⟩
  let aad : Region := ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩
  let data : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
  let tag : Region := ⟨State.addr (arg s 3), 16⟩
  let work : Region := ⟨State.addr (arg s 4), 3760⟩
  s.rd = [sch, nonce, aad, args s 5] ∧ s.wr = [data, tag, work] ∧ tag.Disjoint (args s 5) ∧ oneLay s

/-- What `vg_aes_gcm_siv_open` needs: `oneLay`, with the received tag the 16
bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨State.addr (s.gpr .r0), 240⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), 12⟩
  let aad : Region := ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩
  let data : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
  let tag : Region := ⟨State.addr (arg s 3), 16⟩
  let work : Region := ⟨State.addr (arg s 4), 3760⟩
  s.rd = [sch, nonce, aad, tag, args s 5] ∧ s.wr = [data, work] ∧ oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_siv_seal`. -/
def sealArm : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (keyLen (s.gpr .r1).toNat)
        (bytesAt s.mem (State.addr (s.gpr .r2)) 12) (bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)
        (bytesAt s.mem (State.addr (s.gpr .r3)) (arg s 0).toNat) =
      (bytesAt s'.mem (State.addr (arg s 1)) (arg s 2).toNat, bytesAt s'.mem (State.addr (arg s 3)) 16)
  pub := onePub

/-- What `vg_aes_gcm_siv_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (keyLen (s.gpr .r1).toNat)
    (bytesAt s.mem (State.addr (s.gpr .r2)) 12) (bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)
    (bytesAt s.mem (State.addr (s.gpr .r3)) (arg s 0).toNat) (bytesAt s.mem (State.addr (arg s 3)) 16)

/-- What `vg_aes_gcm_siv_open` leaves in `r0` and in the `n` bytes of data
at `D`, for the result `r`. Irreducible, so that checking a state against
it never evaluates `r`. -/
@[irreducible] def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem D n = pt
  | none => s'.gpr .r0 = 0 ∧ bytesAt s'.mem D n = zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : s'.gpr .r0 = 1) (hd : bytesAt s'.mem D n = pt) : openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : s'.gpr .r0 = 0) (hd : bytesAt s'.mem D n = zeros n) : openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

/-- `vg_aes_gcm_siv_open`. It does not branch on whether the tag is right,
so its runs are related without the leak the shared contract allows. -/
def openArm : Contract isa where
  pre := openPre
  post s s' := openPost (openResult s) s' (State.addr (arg s 1)) (arg s 2).toNat
  pub := onePub

end VG.Proof.AesGcmSiv.Arm
