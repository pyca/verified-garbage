import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-CCM on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The code is proved with its
working space as an eleventh argument, `work`, against the shared contracts
with it appended (`Proof/AesCcm/Scratch.lean`), which imply these
(`Verified.lean`); a frame allocates it (`Frame.lean`). The arguments are on the stack, from `[esp + 4]`
(cdecl), and may be overwritten (`writeArgs`); the calls push their
arguments and return addresses below `esp`: 56 bytes for a call of
`vg_cmac_aes_update` (its own 28 and those of its calls of `vg_aes_ctr32`),
which no buffer overlaps, nor the return address.
-/

namespace VG.Proof.AesCcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- The buffers of `vg_aes_ccm_seal(schedule, rounds, nonce, nonce_len, aad, aad_len, data, len, tag, tag_len, work)`
and `vg_aes_ccm_open`, with the same arguments. -/
abbrev schR (s : State) : Region := ⟨(arg s 0).setWidth 64, 240⟩
abbrev nonceR (s : State) : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
abbrev aadR (s : State) : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
abbrev dataR (s : State) : Region := ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩
abbrev tagR (s : State) : Region := ⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩
abbrev workR (s : State) : Region := ⟨(arg s 10).setWidth 64, 2560⟩
abbrev argsR' (s : State) : Region := ⟨argAddr s 0, 44⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev stackR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 56, 56⟩

/-- What both functions' preconditions say of the buffers and the
arguments, but for which may be written. -/
def oneLay (s : State) : Prop :=
  (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (workR s) ∧ (schR s).Disjoint (argsR' s) ∧
  (nonceR s).Disjoint (dataR s) ∧ (nonceR s).Disjoint (workR s) ∧ (nonceR s).Disjoint (argsR' s) ∧
  (aadR s).Disjoint (dataR s) ∧ (aadR s).Disjoint (workR s) ∧ (aadR s).Disjoint (argsR' s) ∧
  (dataR s).Disjoint (tagR s) ∧ (dataR s).Disjoint (workR s) ∧ (dataR s).Disjoint (argsR' s) ∧
  (tagR s).Disjoint (workR s) ∧ (tagR s).Disjoint (argsR' s) ∧ (workR s).Disjoint (argsR' s) ∧
  (retR s).Disjoint (schR s) ∧ (retR s).Disjoint (nonceR s) ∧ (retR s).Disjoint (aadR s) ∧
  (retR s).Disjoint (dataR s) ∧ (retR s).Disjoint (tagR s) ∧ (retR s).Disjoint (workR s) ∧
  (retR s).Disjoint (argsR' s) ∧
  (stackR s).Disjoint (schR s) ∧ (stackR s).Disjoint (nonceR s) ∧ (stackR s).Disjoint (aadR s) ∧
  (stackR s).Disjoint (dataR s) ∧ (stackR s).Disjoint (tagR s) ∧ (stackR s).Disjoint (workR s) ∧
  (stackR s).Disjoint (argsR' s) ∧
  (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
  (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
  (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32 ∧
  (arg s 10).toNat + 2560 ≤ 2 ^ 32 ∧ 56 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 48 ≤ 2 ^ 32 ∧
  ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) ∧
  valid (arg s 9).toNat (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat = true

/-- `seal` writes the tag. -/
def sealPre (s : State) : Prop :=
  s.rd = [schR s, nonceR s, aadR s] ∧ s.wr = [dataR s, tagR s, workR s, argsR' s] ∧ oneLay s

/-- `open` reads it. -/
def openPre (s : State) : Prop :=
  s.rd = [schR s, nonceR s, aadR s, tagR s] ∧ s.wr = [dataR s, workR s, argsR' s] ∧ oneLay s

/-- All eleven stack arguments are public, and the stack pointer. -/
def onePub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 11, arg s₁ i = arg s₂ i

/-- What `open` computes. -/
abbrev openRes (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (arg s 9).toNat
    (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
    (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) (bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat)

/-- `vg_aes_ccm_seal`. -/
def sealX86 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (arg s 9).toNat
        (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
        (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) =
      (bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat, bytesAt s'.mem ((arg s 8).setWidth 64) (arg s 9).toNat)
  pub := onePub

/-- What `vg_aes_ccm_open` may leak (`Spec.Ccm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) then [] else
  [if (openRes s).isSome then 1 else 0]

/-- `vg_aes_ccm_open`. -/
def openX86 : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧ bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = pt
    | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧
      bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = zeros (arg s 7).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesCcm.X86
