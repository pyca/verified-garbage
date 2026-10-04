import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-CCM on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ccm/Contract.lean`, which imply these
(`Verified.lean`). The arguments are on the stack, from `[esp + 4]`
(cdecl), and may be overwritten (`writeArgs`); the calls push their
arguments and return addresses below `esp`: 56 bytes for a call of
`vg_cmac_aes_update` (its own 28 and those of its calls of `vg_aes_ctr32`),
which no buffer overlaps, nor the return address.
-/

namespace VG.Proof.AesCcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- `vg_aes_ccm_seal(schedule, rounds, nonce, nonce_len, aad, aad_len, data, len, work, tag_len)`
and `vg_aes_ccm_open`, with the same arguments. -/
def onePre (s : State) : Prop :=
  let sch : Region := ⟨(arg s 0).setWidth 64, 240⟩
  let nonce : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  let aad : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
  let data : Region := ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩
  let work : Region := ⟨(arg s 8).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 40⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 56, 56⟩
  s.rd = [sch, nonce, aad] ∧ s.wr = [data, work, args] ∧
  sch.Disjoint data ∧ sch.Disjoint work ∧ sch.Disjoint args ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
  nonce.Disjoint args ∧ aad.Disjoint data ∧ aad.Disjoint work ∧ aad.Disjoint args ∧
  data.Disjoint work ∧ data.Disjoint args ∧ work.Disjoint args ∧
  ret.Disjoint sch ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧ ret.Disjoint work ∧
  ret.Disjoint args ∧
  stack.Disjoint sch ∧ stack.Disjoint nonce ∧ stack.Disjoint aad ∧ stack.Disjoint data ∧
  stack.Disjoint work ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
  (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
  (arg s 8).toNat + 2560 ≤ 2 ^ 32 ∧ 56 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 44 ≤ 2 ^ 32 ∧
  ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) ∧
  valid (arg s 9).toNat (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat = true

/-- All ten stack arguments are public, and the stack pointer. -/
def onePub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 10, arg s₁ i = arg s₂ i

/-- What `open` computes. -/
abbrev openRes (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (arg s 9).toNat
    (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
    (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) (bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat)

/-- `vg_aes_ccm_seal`. -/
def sealX86 : Contract isa where
  pre := onePre
  post s s' :=
    encryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (arg s 9).toNat
        (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
        (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) =
      (bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat, bytesAt s'.mem ((arg s 8).setWidth 64) (arg s 9).toNat)
  pub := onePub

/-- `vg_aes_ccm_open`. -/
def openX86 : Contract isa where
  pre := onePre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧ bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = pt
    | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧
      bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = zeros (arg s 7).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ (openRes s₁).isSome = (openRes s₂).isSome

end VG.Proof.AesCcm.X86
