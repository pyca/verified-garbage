import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-GCM-SIV on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/GcmSiv/Contract.lean`, which imply these
(`Verified.lean`). The arguments are on the stack, from `[esp + 4]` (cdecl),
and may be overwritten (`writeArgs`); the calls of `vg_aes_ctr32`,
`vg_aes_expand_key` and `vg_ghash`, which make no calls, push their
arguments and return addresses in the 28 bytes below `esp`, which no buffer
overlaps, nor the return address.
-/

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.GcmSiv (ctxCiph keyLen encryptWith decryptWith zeros)

/-- The buffers of `vg_aes_gcm_siv_seal(schedule, rounds, nonce, aad, aad_len, data, len, work)`
and `vg_aes_gcm_siv_open`, with the same arguments. -/
abbrev schR (s : State) : Region := ⟨(arg s 0).setWidth 64, 240⟩
abbrev nonceR (s : State) : Region := ⟨(arg s 2).setWidth 64, 12⟩
abbrev aadR (s : State) : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
abbrev dataR (s : State) : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩
abbrev workR (s : State) : Region := ⟨(arg s 7).setWidth 64, 4096⟩
abbrev argsR' (s : State) : Region := ⟨argAddr s 0, 32⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev stackR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 28, 28⟩

/-- What both functions' preconditions say. -/
def onePre (s : State) : Prop :=
  s.rd = [schR s, nonceR s, aadR s] ∧ s.wr = [dataR s, workR s, argsR' s] ∧
  (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (workR s) ∧ (schR s).Disjoint (argsR' s) ∧
  (nonceR s).Disjoint (dataR s) ∧ (nonceR s).Disjoint (workR s) ∧ (nonceR s).Disjoint (argsR' s) ∧
  (aadR s).Disjoint (dataR s) ∧ (aadR s).Disjoint (workR s) ∧ (aadR s).Disjoint (argsR' s) ∧
  (dataR s).Disjoint (workR s) ∧ (dataR s).Disjoint (argsR' s) ∧ (workR s).Disjoint (argsR' s) ∧
  (retR s).Disjoint (schR s) ∧ (retR s).Disjoint (nonceR s) ∧ (retR s).Disjoint (aadR s) ∧
  (retR s).Disjoint (dataR s) ∧ (retR s).Disjoint (workR s) ∧ (retR s).Disjoint (argsR' s) ∧
  (stackR s).Disjoint (schR s) ∧ (stackR s).Disjoint (nonceR s) ∧ (stackR s).Disjoint (aadR s) ∧
  (stackR s).Disjoint (dataR s) ∧ (stackR s).Disjoint (workR s) ∧ (stackR s).Disjoint (argsR' s) ∧
  (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 12 ≤ 2 ^ 32 ∧
  (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32 ∧
  (arg s 7).toNat + 4096 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 36 ≤ 2 ^ 32 ∧
  ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 14)

/-- All eight stack arguments are public, and the stack pointer. -/
def onePub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 8, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_siv_seal`. -/
def sealX86 : Contract isa where
  pre := onePre
  post s s' :=
    encryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (keyLen (arg s 1).toNat)
        (bytesAt s.mem ((arg s 2).setWidth 64) 12) (bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat)
        (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) =
      (bytesAt s'.mem ((arg s 5).setWidth 64) (arg s 6).toNat, bytesAt s'.mem ((arg s 7).setWidth 64) 16)
  pub := onePub

/-- What `vg_aes_gcm_siv_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (keyLen (arg s 1).toNat)
    (bytesAt s.mem ((arg s 2).setWidth 64) 12) (bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat)
    (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) (bytesAt s.mem ((arg s 7).setWidth 64) 16)

/-- What `vg_aes_gcm_siv_open` leaves in `eax` and in the `n` bytes of data
at `D`, for the result `r`. Irreducible, so that checking a state against
it never evaluates `r`. -/
@[irreducible] def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => s'.gpr .eax = 1 ∧ bytesAt s'.mem D n = pt
  | none => s'.gpr .eax = 0 ∧ bytesAt s'.mem D n = zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : s'.gpr .eax = 1) (hd : bytesAt s'.mem D n = pt) : openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : s'.gpr .eax = 0) (hd : bytesAt s'.mem D n = zeros n) : openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

/-- `vg_aes_gcm_siv_open`. It does not branch on whether the tag is right,
so its runs are related without the leak the shared contract allows. -/
def openX86 : Contract isa where
  pre := onePre
  post s s' := openPost (openResult s) s' ((arg s 5).setWidth 64) (arg s 6).toNat
  pub := onePub

end VG.Proof.AesGcmSiv.X86
