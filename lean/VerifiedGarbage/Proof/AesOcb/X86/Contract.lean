import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-OCB on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The code is proved with its
working space as a last argument, `work` (`scratch` for `init`), against the
shared contracts with it appended (`Proof/AesOcb/Scratch.lean`), which imply
these (`Verified.lean`); a frame allocates it (`Frame.lean`). The arguments
are on the stack, from `[esp + 4]` (cdecl), and may be overwritten
(`writeArgs`); the calls of `vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks`
and `vg_aes_expand_key`, which make no calls, push their arguments and
return addresses in the 24 bytes below `esp`, which no buffer overlaps, nor
the return address.
-/

namespace VG.Proof.AesOcb.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (ctxCiph ctxInv ctxLstar encryptWith decryptWith lengthsOk zeros KeyRepr)

/-! ## `seal` and `open` -/

/-- The buffers of `vg_aes_ocb_seal(ctx, rounds, nonce, nonce_len, aad, aad_len, data, len, tag, tag_len, work)`
and `vg_aes_ocb_open`, with the same arguments. -/
abbrev ctxR (s : State) : Region := ⟨(arg s 0).setWidth 64, 256⟩
abbrev nonceR (s : State) : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
abbrev aadR (s : State) : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
abbrev dataR (s : State) : Region := ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩
abbrev tagR (s : State) : Region := ⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩
abbrev workR (s : State) : Region := ⟨(arg s 10).setWidth 64, 2560⟩
abbrev argsR' (s : State) : Region := ⟨argAddr s 0, 44⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev stackR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 24, 24⟩

/-- What both functions' preconditions say of the buffers and the
arguments, but for which may be written. -/
def oneLay (s : State) : Prop :=
  (ctxR s).Disjoint (dataR s) ∧ (ctxR s).Disjoint (workR s) ∧ (ctxR s).Disjoint (argsR' s) ∧
  (nonceR s).Disjoint (dataR s) ∧ (nonceR s).Disjoint (workR s) ∧ (nonceR s).Disjoint (argsR' s) ∧
  (aadR s).Disjoint (dataR s) ∧ (aadR s).Disjoint (workR s) ∧ (aadR s).Disjoint (argsR' s) ∧
  (dataR s).Disjoint (tagR s) ∧ (dataR s).Disjoint (workR s) ∧ (dataR s).Disjoint (argsR' s) ∧
  (tagR s).Disjoint (workR s) ∧ (tagR s).Disjoint (argsR' s) ∧ (workR s).Disjoint (argsR' s) ∧
  (retR s).Disjoint (ctxR s) ∧ (retR s).Disjoint (nonceR s) ∧ (retR s).Disjoint (aadR s) ∧
  (retR s).Disjoint (dataR s) ∧ (retR s).Disjoint (tagR s) ∧ (retR s).Disjoint (workR s) ∧
  (retR s).Disjoint (argsR' s) ∧
  (stackR s).Disjoint (ctxR s) ∧ (stackR s).Disjoint (nonceR s) ∧ (stackR s).Disjoint (aadR s) ∧
  (stackR s).Disjoint (dataR s) ∧ (stackR s).Disjoint (tagR s) ∧ (stackR s).Disjoint (workR s) ∧
  (stackR s).Disjoint (argsR' s) ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
  (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
  (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32 ∧
  (arg s 10).toNat + 2560 ≤ 2 ^ 32 ∧ 24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 48 ≤ 2 ^ 32 ∧
  ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) ∧
  lengthsOk (arg s 9).toNat (arg s 3).toNat = true

/-- `seal` writes the tag. -/
def sealPre (s : State) : Prop :=
  s.rd = [ctxR s, nonceR s, aadR s] ∧ s.wr = [dataR s, tagR s, workR s, argsR' s] ∧
    (ctxR s).Disjoint (tagR s) ∧ (nonceR s).Disjoint (tagR s) ∧ (aadR s).Disjoint (tagR s) ∧ oneLay s

/-- `open` reads it. -/
def openPre (s : State) : Prop :=
  s.rd = [ctxR s, nonceR s, aadR s, tagR s] ∧ s.wr = [dataR s, workR s, argsR' s] ∧ oneLay s

/-- All eleven stack arguments are public, and the stack pointer. -/
def onePub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 11, arg s₁ i = arg s₂ i

/-- `vg_aes_ocb_seal`. -/
def sealX86 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (ctxLstar s.mem ((arg s 0).setWidth 64))
        (arg s 9).toNat (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
        (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat) =
      (bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat, bytesAt s'.mem ((arg s 8).setWidth 64) (arg s 9).toNat)
  pub := onePub

/-- What `vg_aes_ocb_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
    (ctxInv s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (ctxLstar s.mem ((arg s 0).setWidth 64))
    (arg s 9).toNat (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
    (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
    (bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat)

/-- The return value: the low word of `edx:eax`. -/
theorem setWidth_ret (a b : BitVec 32) : (a ++ b).setWidth 32 = b := BitVec.setWidth_append_eq_right

/-- What `vg_aes_ocb_open` leaves in `edx:eax` and in the `n` bytes of data
at `D`, for the result `r`. -/
def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
  | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : s'.gpr .eax = 1) (hd : bytesAt s'.mem D n = pt) : openPost r s' D n := by
  subst hr; exact ⟨by rw [setWidth_ret, hax], hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : s'.gpr .eax = 0) (hd : bytesAt s'.mem D n = zeros n) : openPost r s' D n := by
  subst hr; exact ⟨by rw [setWidth_ret, hax], hd⟩

/-- `vg_aes_ocb_open`. It does not branch on whether the tag is right, so
its runs are related without the leak the shared contract allows. -/
def openX86 : Contract isa where
  pre := openPre
  post s s' := openPost (openResult s) s' ((arg s 6).setWidth 64) (arg s 7).toNat
  pub := onePub

/-! ## `init` -/

/-- The buffers of `vg_aes_ocb_init(key, key_len, ctx, scratch)`. -/
abbrev keyR (s : State) : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
abbrev ictxR (s : State) : Region := ⟨(arg s 2).setWidth 64, 256⟩
abbrev scrR (s : State) : Region := ⟨(arg s 3).setWidth 64, 2560⟩
abbrev iargsR (s : State) : Region := ⟨argAddr s 0, 16⟩

/-- What `init` needs. -/
def initPre (s : State) : Prop :=
  s.rd = [keyR s] ∧ s.wr = [ictxR s, scrR s, iargsR s] ∧
  (keyR s).Disjoint (ictxR s) ∧ (keyR s).Disjoint (scrR s) ∧ (keyR s).Disjoint (iargsR s) ∧
  (ictxR s).Disjoint (scrR s) ∧ (ictxR s).Disjoint (iargsR s) ∧ (scrR s).Disjoint (iargsR s) ∧
  (retR s).Disjoint (keyR s) ∧ (retR s).Disjoint (ictxR s) ∧ (retR s).Disjoint (scrR s) ∧
  (retR s).Disjoint (iargsR s) ∧
  (stackR s).Disjoint (keyR s) ∧ (stackR s).Disjoint (ictxR s) ∧ (stackR s).Disjoint (scrR s) ∧
  (stackR s).Disjoint (iargsR s) ∧
  (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + 256 ≤ 2 ^ 32 ∧
  (arg s 3).toNat + 2560 ≤ 2 ^ 32 ∧ 24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
  ((arg s 1).toNat = 16 ∨ (arg s 1).toNat = 24 ∨ (arg s 1).toNat = 32)

/-- `vg_aes_ocb_init`. -/
def initX86 : Contract isa where
  pre := initPre
  post s s' := KeyRepr s'.mem ((arg s 2).setWidth 64) (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

end VG.Proof.AesOcb.X86
