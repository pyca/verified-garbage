import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.AesGcm.X86.Fn
import VerifiedGarbage.Proof.AesGcm.X86.StreamCrypt
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.AesOcb.X86
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
import VerifiedGarbage.Proof.AesGcm.X86.Callee
import VerifiedGarbage.Proof.Ocb.Stretch32
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.AesCcm.Bytes
import VerifiedGarbage.Proof.Ocb.Stretch32
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesOcb.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Contract`. -/
section

/-!
# AES-OCB on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The code is proved with its
working space as a last argument, `work` (`scratch` for `init`), against the
shared contracts with it appended (`Proof/AesOcb/Scratch.lean`), which imply
these (`Verified.lean`); a frame allocates it (`Frame.lean`). The arguments
are on the stack, from `[esp + 4]` (cdecl), and may be overwritten
(`writeArgs`); the calls of `vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks`
and `vg_aes_expand_key_scratch`, which make no calls, push their arguments and
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
abbrev ctxR (s : State) : Region := ⟨(VG.X86.arg s 0).setWidth 64, 256⟩
abbrev nonceR (s : State) : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
abbrev aadR (s : State) : Region := ⟨(VG.X86.arg s 4).setWidth 64, (VG.X86.arg s 5).toNat⟩
abbrev dataR (s : State) : Region := ⟨(VG.X86.arg s 6).setWidth 64, (VG.X86.arg s 7).toNat⟩
abbrev tagR (s : State) : Region := ⟨(VG.X86.arg s 8).setWidth 64, (VG.X86.arg s 9).toNat⟩
abbrev workR (s : State) : Region := ⟨(VG.X86.arg s 10).setWidth 64, 2560⟩
abbrev argsR' (s : State) : Region := ⟨argAddr s 0, 44⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev stackR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 24, 24⟩

/-- What both functions' preconditions say of the buffers and the
arguments, but for which may be written. -/
def oneLay (s : State) : Prop :=
  (VG.Proof.AesOcb.X86.ctxR s).Disjoint (VG.Proof.AesOcb.X86.dataR s) ∧ (VG.Proof.AesOcb.X86.ctxR s).Disjoint (VG.Proof.AesOcb.X86.workR s) ∧ (VG.Proof.AesOcb.X86.ctxR s).Disjoint (VG.Proof.AesOcb.X86.argsR' s) ∧
  (VG.Proof.AesOcb.X86.nonceR s).Disjoint (VG.Proof.AesOcb.X86.dataR s) ∧ (VG.Proof.AesOcb.X86.nonceR s).Disjoint (VG.Proof.AesOcb.X86.workR s) ∧ (VG.Proof.AesOcb.X86.nonceR s).Disjoint (VG.Proof.AesOcb.X86.argsR' s) ∧
  (VG.Proof.AesOcb.X86.aadR s).Disjoint (VG.Proof.AesOcb.X86.dataR s) ∧ (VG.Proof.AesOcb.X86.aadR s).Disjoint (VG.Proof.AesOcb.X86.workR s) ∧ (VG.Proof.AesOcb.X86.aadR s).Disjoint (VG.Proof.AesOcb.X86.argsR' s) ∧
  (VG.Proof.AesOcb.X86.dataR s).Disjoint (VG.Proof.AesOcb.X86.tagR s) ∧ (VG.Proof.AesOcb.X86.dataR s).Disjoint (VG.Proof.AesOcb.X86.workR s) ∧ (VG.Proof.AesOcb.X86.dataR s).Disjoint (VG.Proof.AesOcb.X86.argsR' s) ∧
  (VG.Proof.AesOcb.X86.tagR s).Disjoint (VG.Proof.AesOcb.X86.workR s) ∧ (VG.Proof.AesOcb.X86.tagR s).Disjoint (VG.Proof.AesOcb.X86.argsR' s) ∧ (VG.Proof.AesOcb.X86.workR s).Disjoint (VG.Proof.AesOcb.X86.argsR' s) ∧
  (VG.Proof.AesOcb.X86.retR s).Disjoint (VG.Proof.AesOcb.X86.ctxR s) ∧ (VG.Proof.AesOcb.X86.retR s).Disjoint (VG.Proof.AesOcb.X86.nonceR s) ∧ (VG.Proof.AesOcb.X86.retR s).Disjoint (VG.Proof.AesOcb.X86.aadR s) ∧
  (VG.Proof.AesOcb.X86.retR s).Disjoint (VG.Proof.AesOcb.X86.dataR s) ∧ (VG.Proof.AesOcb.X86.retR s).Disjoint (VG.Proof.AesOcb.X86.tagR s) ∧ (VG.Proof.AesOcb.X86.retR s).Disjoint (VG.Proof.AesOcb.X86.workR s) ∧
  (VG.Proof.AesOcb.X86.retR s).Disjoint (VG.Proof.AesOcb.X86.argsR' s) ∧
  (VG.Proof.AesOcb.X86.stackR s).Disjoint (VG.Proof.AesOcb.X86.ctxR s) ∧ (VG.Proof.AesOcb.X86.stackR s).Disjoint (VG.Proof.AesOcb.X86.nonceR s) ∧ (VG.Proof.AesOcb.X86.stackR s).Disjoint (VG.Proof.AesOcb.X86.aadR s) ∧
  (VG.Proof.AesOcb.X86.stackR s).Disjoint (VG.Proof.AesOcb.X86.dataR s) ∧ (VG.Proof.AesOcb.X86.stackR s).Disjoint (VG.Proof.AesOcb.X86.tagR s) ∧ (VG.Proof.AesOcb.X86.stackR s).Disjoint (VG.Proof.AesOcb.X86.workR s) ∧
  (VG.Proof.AesOcb.X86.stackR s).Disjoint (VG.Proof.AesOcb.X86.argsR' s) ∧
  (VG.X86.arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧
  (VG.X86.arg s 4).toNat + (VG.X86.arg s 5).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 6).toNat + (VG.X86.arg s 7).toNat ≤ 2 ^ 32 ∧
  (VG.X86.arg s 8).toNat + (VG.X86.arg s 9).toNat ≤ 2 ^ 32 ∧
  (VG.X86.arg s 10).toNat + 2560 ≤ 2 ^ 32 ∧ 24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 48 ≤ 2 ^ 32 ∧
  ((VG.X86.arg s 1).toNat = 10 ∨ (VG.X86.arg s 1).toNat = 12 ∨ (VG.X86.arg s 1).toNat = 14) ∧
  lengthsOk (VG.X86.arg s 9).toNat (VG.X86.arg s 3).toNat = true

/-- `seal` writes the tag. -/
def sealPre (s : State) : Prop :=
  s.rd = [VG.Proof.AesOcb.X86.ctxR s, VG.Proof.AesOcb.X86.nonceR s, VG.Proof.AesOcb.X86.aadR s] ∧ s.wr = [VG.Proof.AesOcb.X86.dataR s, VG.Proof.AesOcb.X86.tagR s, VG.Proof.AesOcb.X86.workR s, VG.Proof.AesOcb.X86.argsR' s] ∧
    (VG.Proof.AesOcb.X86.ctxR s).Disjoint (VG.Proof.AesOcb.X86.tagR s) ∧ (VG.Proof.AesOcb.X86.nonceR s).Disjoint (VG.Proof.AesOcb.X86.tagR s) ∧ (VG.Proof.AesOcb.X86.aadR s).Disjoint (VG.Proof.AesOcb.X86.tagR s) ∧ VG.Proof.AesOcb.X86.oneLay s

/-- `open` reads it. -/
def openPre (s : State) : Prop :=
  s.rd = [VG.Proof.AesOcb.X86.ctxR s, VG.Proof.AesOcb.X86.nonceR s, VG.Proof.AesOcb.X86.aadR s, VG.Proof.AesOcb.X86.tagR s] ∧ s.wr = [VG.Proof.AesOcb.X86.dataR s, VG.Proof.AesOcb.X86.workR s, VG.Proof.AesOcb.X86.argsR' s] ∧ VG.Proof.AesOcb.X86.oneLay s

/-- All eleven stack arguments are public, and the stack pointer. -/
def onePub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 11, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `vg_aes_ocb_seal`. -/
def sealX86 : Contract isa where
  pre := VG.Proof.AesOcb.X86.sealPre
  post s s' :=
    VG.Spec.Ocb.encryptWith (VG.Spec.Ocb.ctxCiph s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat) (ctxLstar s.mem ((VG.X86.arg s 0).setWidth 64))
        (VG.X86.arg s 9).toNat (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat)
        (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 4).setWidth 64) (VG.X86.arg s 5).toNat) (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat) =
      (VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat, VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 8).setWidth 64) (VG.X86.arg s 9).toNat)
  pub := VG.Proof.AesOcb.X86.onePub

/-- What `vg_aes_ocb_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  VG.Spec.Ocb.decryptWith (VG.Spec.Ocb.ctxCiph s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat)
    (ctxInv s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat) (ctxLstar s.mem ((VG.X86.arg s 0).setWidth 64))
    (VG.X86.arg s 9).toNat (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat)
    (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 4).setWidth 64) (VG.X86.arg s 5).toNat) (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat)
    (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 8).setWidth 64) (VG.X86.arg s 9).toNat)

/-- The return value: the low word of `edx:eax`. -/
theorem setWidth_ret (a b : BitVec 32) : (a ++ b).setWidth 32 = b := BitVec.setWidth_append_eq_right

/-- What `vg_aes_ocb_open` leaves in `edx:eax` and in the `n` bytes of data
at `D`, for the result `r`. -/
def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧ VG.Spec.Aes.bytesAt s'.mem D n = pt
  | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧ VG.Spec.Aes.bytesAt s'.mem D n = VG.Spec.Ocb.zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : s'.gpr .eax = 1) (hd : VG.Spec.Aes.bytesAt s'.mem D n = pt) : VG.Proof.AesOcb.X86.openPost r s' D n := by
  subst hr; exact ⟨by rw [VG.Proof.AesOcb.X86.setWidth_ret, hax], hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : s'.gpr .eax = 0) (hd : VG.Spec.Aes.bytesAt s'.mem D n = VG.Spec.Ocb.zeros n) : VG.Proof.AesOcb.X86.openPost r s' D n := by
  subst hr; exact ⟨by rw [VG.Proof.AesOcb.X86.setWidth_ret, hax], hd⟩

/-- `vg_aes_ocb_open`. It does not branch on whether the tag is right, so
its runs are related without the leak the shared contract allows. -/
def openX86 : Contract isa where
  pre := VG.Proof.AesOcb.X86.openPre
  post s s' := VG.Proof.AesOcb.X86.openPost (VG.Proof.AesOcb.X86.openResult s) s' ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat
  pub := VG.Proof.AesOcb.X86.onePub

/-! ## `init` -/

/-- The buffers of `vg_aes_ocb_init(key, key_len, ctx, scratch)`. -/
abbrev keyR (s : State) : Region := ⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩
abbrev ictxR (s : State) : Region := ⟨(VG.X86.arg s 2).setWidth 64, 256⟩
abbrev scrR (s : State) : Region := ⟨(VG.X86.arg s 3).setWidth 64, 2560⟩
abbrev iargsR (s : State) : Region := ⟨argAddr s 0, 16⟩

/-- What `init` needs. -/
def initPre (s : State) : Prop :=
  s.rd = [VG.Proof.AesOcb.X86.keyR s] ∧ s.wr = [VG.Proof.AesOcb.X86.ictxR s, VG.Proof.AesOcb.X86.scrR s, VG.Proof.AesOcb.X86.iargsR s] ∧
  (VG.Proof.AesOcb.X86.keyR s).Disjoint (VG.Proof.AesOcb.X86.ictxR s) ∧ (VG.Proof.AesOcb.X86.keyR s).Disjoint (VG.Proof.AesOcb.X86.scrR s) ∧ (VG.Proof.AesOcb.X86.keyR s).Disjoint (VG.Proof.AesOcb.X86.iargsR s) ∧
  (VG.Proof.AesOcb.X86.ictxR s).Disjoint (VG.Proof.AesOcb.X86.scrR s) ∧ (VG.Proof.AesOcb.X86.ictxR s).Disjoint (VG.Proof.AesOcb.X86.iargsR s) ∧ (VG.Proof.AesOcb.X86.scrR s).Disjoint (VG.Proof.AesOcb.X86.iargsR s) ∧
  (VG.Proof.AesOcb.X86.retR s).Disjoint (VG.Proof.AesOcb.X86.keyR s) ∧ (VG.Proof.AesOcb.X86.retR s).Disjoint (VG.Proof.AesOcb.X86.ictxR s) ∧ (VG.Proof.AesOcb.X86.retR s).Disjoint (VG.Proof.AesOcb.X86.scrR s) ∧
  (VG.Proof.AesOcb.X86.retR s).Disjoint (VG.Proof.AesOcb.X86.iargsR s) ∧
  (VG.Proof.AesOcb.X86.stackR s).Disjoint (VG.Proof.AesOcb.X86.keyR s) ∧ (VG.Proof.AesOcb.X86.stackR s).Disjoint (VG.Proof.AesOcb.X86.ictxR s) ∧ (VG.Proof.AesOcb.X86.stackR s).Disjoint (VG.Proof.AesOcb.X86.scrR s) ∧
  (VG.Proof.AesOcb.X86.stackR s).Disjoint (VG.Proof.AesOcb.X86.iargsR s) ∧
  (VG.X86.arg s 0).toNat + (VG.X86.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + 256 ≤ 2 ^ 32 ∧
  (VG.X86.arg s 3).toNat + 2560 ≤ 2 ^ 32 ∧ 24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
  ((VG.X86.arg s 1).toNat = 16 ∨ (VG.X86.arg s 1).toNat = 24 ∨ (VG.X86.arg s 1).toNat = 32)

/-- `vg_aes_ocb_init`. -/
def initX86 : Contract isa where
  pre := VG.Proof.AesOcb.X86.initPre
  post s s' := VG.Spec.Ocb.KeyRepr s'.mem ((VG.X86.arg s 2).setWidth 64) (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, VG.X86.arg s₁ i = VG.X86.arg s₂ i

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Env`. -/
section

/-!
# AES-OCB on x86: where everything is

Untrusted: everything here is checked by Lean. The public arguments
(`Prm`): the key context (256 bytes at `K`), the working space (2560 bytes
at `W`), the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`), the stack
pointer and the number of rounds, all 32-bit; how their regions lie, apart
from each other and from the 24 bytes below `SP` that the calls use
(`Lay`); what a state may access (`Perm`); and `W` in `ebp`, the stack
pointer, and the arguments the entry keeps in `W` (`Env`). The pieces write
only the parts of `W` in `mutR` (and the data, and the stack below `SP`), so
they keep the slots and our caller's registers saved in `W`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_off in_off in_left covers_left
  covers_cons covers_nil slotv)

/-! ## Covering -/

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := fun a m ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

/-! ## The public arguments and their regions -/

/-- The public arguments. -/
structure Prm where
  /-- The key context. -/
  K : BitVec 32
  /-- The working space. -/
  W : BitVec 32
  /-- The nonce. -/
  N : BitVec 32
  /-- The associated data. -/
  A : BitVec 32
  /-- The data. -/
  D : BitVec 32
  /-- The tag. -/
  T : BitVec 32
  /-- The stack pointer. -/
  SP : BitVec 32
  /-- The number of rounds. -/
  R : Nat
  /-- The length of the nonce. -/
  nl : Nat
  /-- The length of the associated data. -/
  al : Nat
  /-- The length of the data. -/
  n : Nat
  /-- The length of the tag. -/
  tl : Nat

/-- The stack the calls use. -/
abbrev stk (p : VG.Proof.AesOcb.X86.Prm) : Region := below p.SP 24

/-- How the regions lie. -/
structure Lay (p : VG.Proof.AesOcb.X86.Prm) : Prop where
  kw : p.K.toNat + 256 ≤ 2 ^ 32
  ww : p.W.toNat + 2560 ≤ 2 ^ 32
  nw : p.N.toNat + p.nl ≤ 2 ^ 32
  aw : p.A.toNat + p.al ≤ 2 ^ 32
  dw : p.D.toNat + p.n ≤ 2 ^ 32
  tw : p.T.toNat + p.tl ≤ 2 ^ 32
  sp : 24 ≤ p.SP.toNat
  k_w : (⟨w64 p.K, 256⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  k_d : (⟨w64 p.K, 256⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  n_w : (⟨w64 p.N, p.nl⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  n_d : (⟨w64 p.N, p.nl⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  a_w : (⟨w64 p.A, p.al⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  a_d : (⟨w64 p.A, p.al⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  d_w : (⟨w64 p.D, p.n⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  t_w : (⟨w64 p.T, p.tl⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  t_d : (⟨w64 p.T, p.tl⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  bk : (VG.Proof.AesOcb.X86.stk p).Disjoint ⟨w64 p.K, 256⟩
  bn : (VG.Proof.AesOcb.X86.stk p).Disjoint ⟨w64 p.N, p.nl⟩
  ba : (VG.Proof.AesOcb.X86.stk p).Disjoint ⟨w64 p.A, p.al⟩
  bd : (VG.Proof.AesOcb.X86.stk p).Disjoint ⟨w64 p.D, p.n⟩
  bw : (VG.Proof.AesOcb.X86.stk p).Disjoint ⟨w64 p.W, 2560⟩
  bt : (VG.Proof.AesOcb.X86.stk p).Disjoint ⟨w64 p.T, p.tl⟩
  rounds : p.R = 10 ∨ p.R = 12 ∨ p.R = 14
  nl1 : 1 ≤ p.nl
  nl15 : p.nl ≤ 15
  tl1 : 1 ≤ p.tl
  tl16 : p.tl ≤ 16
  al32 : p.al < 2 ^ 32
  n32 : p.n < 2 ^ 32
  retW : (⟨w64 p.SP, 4⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  retD : (⟨w64 p.SP, 4⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  retT : (⟨w64 p.SP, 4⟩ : Region).Disjoint ⟨w64 p.T, p.tl⟩

/-- What a state may access. -/
structure Perm (p : VG.Proof.AesOcb.X86.Prm) (s : State) : Prop where
  k : Covers [⟨w64 p.K, 256⟩] (s.rd ++ s.wr)
  non : Covers [⟨w64 p.N, p.nl⟩] (s.rd ++ s.wr)
  aad : Covers [⟨w64 p.A, p.al⟩] (s.rd ++ s.wr)
  d : Covers [⟨w64 p.D, p.n⟩] s.wr
  w : Covers [⟨w64 p.W, 2560⟩] s.wr
  t : Covers [⟨w64 p.T, p.tl⟩] (s.rd ++ s.wr)

theorem Perm.of_eq {p : VG.Proof.AesOcb.X86.Prm} {s s' : State} (h : VG.Proof.AesOcb.X86.Perm p s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesOcb.X86.Perm p s' := by
  obtain ⟨a, b, c, d, e, f⟩ := h
  exact ⟨by rw [hrd, hwr]; exact a, by rw [hrd, hwr]; exact b, by rw [hrd, hwr]; exact c, by rw [hwr]; exact d,
    by rw [hwr]; exact e, by rw [hrd, hwr]; exact f⟩

/-- The public values the entry keeps in `W`: all the arguments but `work`. -/
structure Slots (p : VG.Proof.AesOcb.X86.Prm) (m : Mem) : Prop where
  ctx : slotv m p.W Impl.AesOcb.X86.ctxO = p.K
  rounds : slotv m p.W Impl.AesOcb.X86.rndO = BitVec.ofNat 32 p.R
  nonce : slotv m p.W Impl.AesOcb.X86.nO = p.N
  nlen : slotv m p.W Impl.AesOcb.X86.nlO = BitVec.ofNat 32 p.nl
  aad : slotv m p.W Impl.AesOcb.X86.aadO = p.A
  alen : slotv m p.W Impl.AesOcb.X86.alenO = BitVec.ofNat 32 p.al
  data : slotv m p.W Impl.AesOcb.X86.dataO = p.D
  len : slotv m p.W Impl.AesOcb.X86.lenO = BitVec.ofNat 32 p.n
  tg : slotv m p.W Impl.AesOcb.X86.tgO = p.T
  tlen : slotv m p.W Impl.AesOcb.X86.tlO = BitVec.ofNat 32 p.tl

/-- `W` in `ebp`, the stack pointer, what the state may access, and the
slots. -/
structure Env (p : VG.Proof.AesOcb.X86.Prm) (s : State) : Prop where
  ebp : s.gpr .ebp = p.W
  esp : s.gpr .esp = p.SP
  perm : VG.Proof.AesOcb.X86.Perm p s
  slots : VG.Proof.AesOcb.X86.Slots p s.mem

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

/-- Parts of `W` are disjoint. -/
theorem w_w {W : BitVec 32} {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

variable {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p)
include L

/-- An offset into `W`, as a 64-bit address. -/
theorem aW {o : Nat} (ho : o < 2560) : w64 (p.W + BitVec.ofNat 32 o) = w64 p.W + BitVec.ofNat 64 o :=
  w64_add (by have := L.ww; omega)

theorem nW {o : Nat} (ho : o < 2560) : (p.W + BitVec.ofNat 32 o).toNat = p.W.toNat + o :=
  toNat_add32 (by have := L.ww; omega)

/-- An offset into the key context. -/
theorem aK {o : Nat} (ho : o < 256) : w64 (p.K + BitVec.ofNat 32 o) = w64 p.K + BitVec.ofNat 64 o :=
  w64_add (by have := L.kw; omega)

theorem k_w' {d k : Nat} (hd : d + k ≤ 2560) : (⟨w64 p.K, 256⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (VG.Proof.AesOcb.X86.Lay.wSub hd)

theorem n_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨w64 p.N, p.nl⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.n_w.sub_right (VG.Proof.AesOcb.X86.Lay.wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨w64 p.A, p.al⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (VG.Proof.AesOcb.X86.Lay.wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨w64 p.D, p.n⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (VG.Proof.AesOcb.X86.Lay.wSub hd)

theorem t_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨w64 p.T, p.tl⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.t_w.sub_right (VG.Proof.AesOcb.X86.Lay.wSub hd)

theorem bw' {d k : Nat} (hd : d + k ≤ 2560) : (VG.Proof.AesOcb.X86.stk p).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.bw.sub_right (VG.Proof.AesOcb.X86.Lay.wSub hd)

/-- The stack below `SP` that a call uses, within the 24 bytes. -/
theorem stkSub {k : Nat} (hk : k ≤ 24) : Region.Sub (below p.SP k) (VG.Proof.AesOcb.X86.stk p) := VG.X86.below_sub hk L.sp

theorem rounds_le : 16 * (p.R + 1) ≤ 240 := by rcases L.rounds with h | h | h <;> rw [h] <;> decide

theorem toNat_R : (BitVec.ofNat 32 p.R).toNat = p.R := by
  rcases L.rounds with h | h | h <;> rw [h] <;> rfl

theorem R_lt : p.R < 2 ^ 32 := by rcases L.rounds with h | h | h <;> rw [h] <;> decide

end Lay

namespace Perm

variable {p : VG.Proof.AesOcb.X86.Prm} {s : State} (P : VG.Proof.AesOcb.X86.Perm p s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (w64 p.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (w64 p.W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨w64 p.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨w64 p.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_left (P.wC h)

/-- The first 2560 bytes of `W`, where AES-GCM's save area is. -/
theorem w2560 : Covers [⟨w64 p.W, 2560⟩] s.wr := P.w

theorem kR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (w64 p.K + BitVec.ofNat 64 d) n :=
  in_off P.k h (by decide)

end Perm

/-! ## What the pieces write -/

/-- The parts of `W` the pieces write: the blocks at `[0, 128)`, at
`[144, 176)`, the variables and blocks at `[216, 384)`, and from `384` on. -/
abbrev wA (W : BitVec 32) : Region := ⟨w64 W, 128⟩
abbrev wB (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 144, 32⟩
abbrev wV (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 216, 168⟩
abbrev wC (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 384, 2176⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (p : VG.Proof.AesOcb.X86.Prm) : List Region := [VG.Proof.AesOcb.X86.wA p.W, VG.Proof.AesOcb.X86.wB p.W, VG.Proof.AesOcb.X86.wV p.W, VG.Proof.AesOcb.X86.wC p.W, VG.Proof.AesOcb.X86.stk p, ⟨w64 p.D, p.n⟩]

/-- The regions `rs` are within `mutR`. -/
abbrev InMut (p : VG.Proof.AesOcb.X86.Prm) (rs : List Region) : Prop := ∀ r ∈ rs, ∃ r' ∈ VG.Proof.AesOcb.X86.mutR p, Region.Sub r r'

theorem frame_toMut {p : VG.Proof.AesOcb.X86.Prm} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (h : VG.Proof.AesOcb.X86.InMut p rs) :
    Frame (VG.Proof.AesOcb.X86.mutR p) m m' := hf.sub h

/-- A part of `W` in `wA`, `wB`, `wV` or `wC`. -/
theorem inMut_w (p : VG.Proof.AesOcb.X86.Prm) {d k : Nat}
    (h : d + k ≤ 128 ∨ 144 ≤ d ∧ d + k ≤ 176 ∨ 216 ≤ d ∧ d + k ≤ 384 ∨ 384 ≤ d ∧ d + k ≤ 2560) :
    ∃ r' ∈ VG.Proof.AesOcb.X86.mutR p, Region.Sub ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with h | h | h | h
  · exact ⟨VG.Proof.AesOcb.X86.wA p.W, by simp, Offset.sub_base _ h⟩
  · exact ⟨VG.Proof.AesOcb.X86.wB p.W, by simp, Offset.sub _ (by omega) (by omega)⟩
  · exact ⟨VG.Proof.AesOcb.X86.wV p.W, by simp, Offset.sub _ (by omega) (by omega)⟩
  · exact ⟨VG.Proof.AesOcb.X86.wC p.W, by simp, Offset.sub _ (by omega) (by omega)⟩

theorem inMut_stk (p : VG.Proof.AesOcb.X86.Prm) : ∃ r' ∈ VG.Proof.AesOcb.X86.mutR p, Region.Sub (VG.Proof.AesOcb.X86.stk p) r' := ⟨VG.Proof.AesOcb.X86.stk p, by simp, fun _ h => h⟩

theorem inMut_d (p : VG.Proof.AesOcb.X86.Prm) : ∃ r' ∈ VG.Proof.AesOcb.X86.mutR p, Region.Sub ⟨w64 p.D, p.n⟩ r' := ⟨_, by simp, fun _ h => h⟩

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {d k : Nat} (hd : 128 ≤ d ∧ d + k ≤ 144 ∨ 176 ≤ d ∧ d + k ≤ 216) :
    ∀ r ∈ VG.Proof.AesOcb.X86.mutR p, (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Lay.w_w (W := p.W) (a := d) (n := k) (d := 0) (k := 128) (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (by omega) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.bw' (by omega)).symm
  · exact (L.d_w' (by omega)).symm

/-- The slots, after code that changes only `mutR`. -/
theorem Slots.mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesOcb.X86.mutR p) m m') (S : VG.Proof.AesOcb.X86.Slots p m) : VG.Proof.AesOcb.X86.Slots p m' := by
  have k : ∀ o, 176 ≤ o ∧ o + 4 ≤ 216 → slotv m' p.W o = slotv m p.W o := fun o ho =>
    hf.readW (r := ⟨w64 p.W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (VG.Proof.AesOcb.X86.kept_mut L (.inr ho)) (by decide)
  exact ⟨by rw [k _ (by decide)]; exact S.ctx, by rw [k _ (by decide)]; exact S.rounds,
    by rw [k _ (by decide)]; exact S.nonce, by rw [k _ (by decide)]; exact S.nlen,
    by rw [k _ (by decide)]; exact S.aad, by rw [k _ (by decide)]; exact S.alen,
    by rw [k _ (by decide)]; exact S.data, by rw [k _ (by decide)]; exact S.len,
    by rw [k _ (by decide)]; exact S.tg, by rw [k _ (by decide)]; exact S.tlen⟩

/-- Our caller's registers saved at `W + 128`, after code that changes only
`mutR`. -/
theorem SavedAt.mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesOcb.X86.mutR p) m m') {s₀ : State}
    (h : Proof.AesGcm.X86.SavedAt m p.W s₀) : Proof.AesGcm.X86.SavedAt m' p.W s₀ :=
  h.frame hf (VG.Proof.AesOcb.X86.kept_mut L (.inl (by decide)))

/-- An environment, after code that keeps `ebp`, `esp` and the permissions,
and changes only `mutR`. -/
theorem Env.mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s s' : State} (h : VG.Proof.AesOcb.X86.Env p s) (hbp : s'.gpr .ebp = p.W)
    (hsp : s'.gpr .esp = p.SP) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame (VG.Proof.AesOcb.X86.mutR p) s.mem s'.mem) :
    VG.Proof.AesOcb.X86.Env p s' :=
  ⟨hbp, hsp, h.perm.of_eq hrd hwr, h.slots.mut L hf⟩

/-- An environment, after code that keeps `ebp`, `esp`, the permissions and
the memory. -/
theorem Env.keep {p : VG.Proof.AesOcb.X86.Prm} {s s' : State} (h : VG.Proof.AesOcb.X86.Env p s) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hm : s'.mem = s.mem) : VG.Proof.AesOcb.X86.Env p s' :=
  ⟨by rw [hbp, h.ebp], by rw [hsp, h.esp], h.perm.of_eq hrd hwr, by rw [hm]; exact h.slots⟩

/-- The return address, after code that changes only `mutR`. -/
theorem ret_mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesOcb.X86.mutR p) m m') :
    m'.readW (w64 p.SP) 32 = m.readW (w64 p.SP) 32 :=
  Proof.AesGcm.X86.ret_kept hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact L.retW.sub_right (Region.sub_prefix (by decide))
    · exact L.retW.sub_right (Lay.wSub (by decide))
    · exact L.retW.sub_right (Lay.wSub (by decide))
    · exact L.retW.sub_right (Lay.wSub (by decide))
    · exact Proof.AesGcm.X86.ret_below L.sp
    · exact L.retD)

/-! ## Buffers apart from `W` and the stack -/

/-- The bytes of a buffer apart from `mutR` but the data. -/
theorem bytes_mut {p : VG.Proof.AesOcb.X86.Prm} {P : BitVec 32} {len : Nat}
    (hw : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) (hb : (VG.Proof.AesOcb.X86.stk p).Disjoint ⟨w64 P, len⟩)
    (hd : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩) (hl : len ≤ 2 ^ 64) {m m' : Mem}
    (hf : Frame (VG.Proof.AesOcb.X86.mutR p) m m') : bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hw.sub_right (Region.sub_prefix (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hb.symm
    · exact hd) hl

theorem ctx_mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesOcb.X86.mutR p) m m') :
    bytesAt m' (w64 p.K) 256 = bytesAt m (w64 p.K) 256 := VG.Proof.AesOcb.X86.bytes_mut L.k_w L.bk L.k_d (by decide) hf

theorem nonce_mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesOcb.X86.mutR p) m m') :
    bytesAt m' (w64 p.N) p.nl = bytesAt m (w64 p.N) p.nl :=
  VG.Proof.AesOcb.X86.bytes_mut L.n_w L.bn L.n_d (by have := L.nl15; omega) hf

theorem aad_mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesOcb.X86.mutR p) m m') :
    bytesAt m' (w64 p.A) p.al = bytesAt m (w64 p.A) p.al :=
  VG.Proof.AesOcb.X86.bytes_mut L.a_w L.ba L.a_d (by have := L.aw; omega) hf

theorem tag_mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesOcb.X86.mutR p) m m') :
    bytesAt m' (w64 p.T) p.tl = bytesAt m (w64 p.T) p.tl :=
  VG.Proof.AesOcb.X86.bytes_mut L.t_w L.bt L.t_d (by have := L.tl16; omega) hf

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Run`. -/
section

/-!
# AES-OCB on x86: running straight-line blocks

Untrusted: everything here is checked by Lean. `grun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`,
keeping the registers folded), as AES-GCM's `xrun` does, with the offsets
of the AES-OCB code; `gregs` and `gmems` read registers, memory, flags
and permissions through the writes of a block.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp)
open VG.Proof.AesGcm.X86 (store32_eq store8_eq gpr_setMem mem_setMem rd_setMem wr_setMem cf_setMem zf_setMem
  readW_writeW_off CT)

/-- A word at `p + a`, after a byte written at `p + b` elsewhere. -/
theorem readW_writeB_off (m : Mem) (p : Addr) (v : BitVec 8) {a b : Nat} (h : a + 4 ≤ b ∨ b + 1 ≤ a)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (m.writeW (p + BitVec.ofNat 64 b) v).readW (p + BitVec.ofNat 64 a) 32 = m.readW (p + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Runs a block of the instructions the AES-OCB code uses. The facts
given rewrite the addresses and discharge the permissions. -/
macro "grun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, execAlu, execShift, State.load32, store32_eq, State.load8, store8_eq,
    State.ea, at_, imm, slot, argOp, tagO, ofsO, ckO, sumO, ldO, l0O, lO, tmpO, t2O, ohO, ctxO, rndO, nO, nlO,
    aadO, alenO, dataO, lenO, tgO, tlO, botO, kO, o0O, stO, hlO, fpO, cntO, restO, nbO, okO, bufO, scrO, List.cons_append, List.nil_append, List.append_assoc,
    Option.bind_some, Option.map_some, readW_writeW_off, readW_writeB_off, gpr_setReg_self, gpr_setReg_of_ne,
    gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags,
    wr_setReg, wr_arithFlags, wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags, gpr_setMem,
    mem_setMem, rd_setMem, wr_setMem, cf_setMem, zf_setMem, ite_true, ite_false, reduceCtorEq, Nat.reduceAdd,
    ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceMul, and_self,
    and_true, true_and, eq_self_iff_true, Reg8.reg, $ts,*]) <;>
  try rfl)

/-- Reads registers through the writes of a block. -/
macro "gregs" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | with_reducible assumption) only [gpr_setMem, gpr_setReg_self, gpr_setReg_of_ne,
    gpr_arithFlags, gpr_setFlags, $ts,*]))

/-- Reads the memory, flags and permissions through the writes of a block. -/
macro "gmems" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [mem_setMem, mem_setReg, mem_arithFlags, mem_setFlags,
    rd_setMem, rd_setReg, rd_arithFlags, rd_setFlags, wr_setMem, wr_setReg, wr_arithFlags, wr_setFlags,
    zf_setMem, zf_setReg, zf_arithFlags, cf_setMem, cf_setReg, cf_arithFlags, gpr_setMem, gpr_setReg_self,
    gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, Mem.readW_writeW_self32, readW_writeW_off, readW_writeB_off,
    tagO, ofsO, ckO, sumO, ldO, l0O, lO, tmpO, t2O, ohO, ctxO, rndO, nO, nlO,
    aadO, alenO, dataO, lenO, tgO, tlO, botO, kO, o0O, stO, hlO, fpO, cntO, restO, nbO, okO, bufO, scrO, Nat.reduceAdd, Reg8.reg, eq_self_iff_true, and_self, $ts,*]))

theorem eval_e {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .e s = some b := h

theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some !b := by
  show s.zf.map _ = _; rw [h]; rfl

theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := h

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

/-- A block, then code: the block constant time by the taint analysis from
the registers `rs`, which `I` pins, and the code from what the block leaves
(`F`, from the state it started in). -/
theorem CT.block_seq {I : State → Prop} {is : List Instr} {c : Prog isa} {F : State → State → Prop}
    (rs : List Reg) (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {hc : Taint.Hint VG.X86.taint.T}
    (h : (VG.X86.taint.check (τr rs) (.block is) hc).isSome = true)
    (blk : ∀ s, I s → ∃ s', runBlock isa is s = some s' ∧ F s s') (h₂ : CT (fun s' => ∃ s, I s ∧ F s s') c) :
    CT I (.seq (.block is) c) :=
  CT.seq (CT.taint rs hr h) (fun s hs => let ⟨s', r, f⟩ := blk s hs; WP.of_runBlock ⟨s', r, s, hs, f⟩) h₂

/-- `ebp` pinned. -/
theorem pin_ebp {I : State → Prop} {W : BitVec 32} (h : ∀ s, I s → s.gpr .ebp = W) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h _ h₁, h _ h₂]

/-- Two registers pinned. -/
theorem pin2 {I : State → Prop} {a b : Reg} {x y : BitVec 32} (h : ∀ s, I s → s.gpr a = x ∧ s.gpr b = y) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a, b], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [(h _ h₁).1, (h _ h₂).1]
  · rw [(h _ h₁).2, (h _ h₂).2]

/-- Three registers pinned. -/
theorem pin3 {I : State → Prop} {a b c : Reg} {x y z : BitVec 32}
    (h : ∀ s, I s → s.gpr a = x ∧ s.gpr b = y ∧ s.gpr c = z) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a, b, c], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [(h _ h₁).1, (h _ h₂).1]
  · rw [(h _ h₁).2.1, (h _ h₂).2.1]
  · rw [(h _ h₁).2.2, (h _ h₂).2.2]

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Entry`. -/
section

/-!
# AES-OCB on x86: the arguments and the entry

Untrusted: everything here is checked by Lean. The precondition `onePre`
gives the public arguments (`prmOf`), how they lie (`lay_of`) and what the
state may access (`perm_of`). The entry saves our caller's registers in `W`
(AES-GCM's `save_ok`) and copies the stack arguments into their slots
(`keeps_ok`): after it, `Env` holds (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt)
open VG.Proof.AesGcm.X86 (w64 slotv argA argsR argsR_eq argA_contains argA_sub SavedAt save_ok KeepEnv keeps_ok
  keepR runBlock_app_of in_off below_eq covers_left)

/-- What both preconditions say: the layout, and that the buffers may be
read (the key context, the nonce, the associated data and the tag) or
written (the data, `work` and the arguments). -/
structure onePre (s : State) : Prop where
  lay : VG.Proof.AesOcb.X86.oneLay s
  rd : ∀ r ∈ [VG.Proof.AesOcb.X86.ctxR s, VG.Proof.AesOcb.X86.nonceR s, VG.Proof.AesOcb.X86.aadR s, VG.Proof.AesOcb.X86.tagR s], Covers [r] (s.rd ++ s.wr)
  wr : ∀ r ∈ [VG.Proof.AesOcb.X86.dataR s, VG.Proof.AesOcb.X86.workR s, VG.Proof.AesOcb.X86.argsR' s], Covers [r] s.wr

theorem onePre_seal {s : State} (h : VG.Proof.AesOcb.X86.sealPre s) : VG.Proof.AesOcb.X86.onePre s := by
  obtain ⟨hrd, hwr, -, -, -, hl⟩ := h
  refine ⟨hl, fun r hr => ?_, fun r hr => ?_⟩
  swap
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact VG.Proof.AesOcb.X86.covers_of_mem (by rw [hwr]; simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesOcb.X86.covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · exact VG.Proof.AesOcb.X86.covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · exact VG.Proof.AesOcb.X86.covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · exact VG.Proof.AesOcb.X86.covers_of_mem (List.mem_append_right _ (by rw [hwr]; simp))

theorem onePre_open {s : State} (h : VG.Proof.AesOcb.X86.openPre s) : VG.Proof.AesOcb.X86.onePre s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  refine ⟨hl, fun r hr => VG.Proof.AesOcb.X86.covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr)),
    fun r hr => VG.Proof.AesOcb.X86.covers_of_mem (by rw [hwr]; exact hr)⟩

/-- The public arguments of a state. -/
def prmOf (s : State) : VG.Proof.AesOcb.X86.Prm where
  K := arg s 0
  W := arg s 10
  N := arg s 2
  A := arg s 4
  D := arg s 6
  T := arg s 8
  SP := s.gpr .esp
  R := (arg s 1).toNat
  nl := (arg s 3).toNat
  al := (arg s 5).toNat
  n := (arg s 7).toNat
  tl := (arg s 9).toNat

/-- What the precondition says of the stack arguments. -/
structure ArgsOk (s : State) : Prop where
  rA : Covers [argsR (s.gpr .esp) 11] (s.rd ++ s.wr)
  aw : (argsR (s.gpr .esp) 11).Disjoint ⟨w64 (arg s 10), 2560⟩
  fa : (s.gpr .esp).toNat + 4 + 4 * 11 ≤ 2 ^ 32

theorem lay_of {s : State} (h : VG.Proof.AesOcb.X86.onePre s) : VG.Proof.AesOcb.X86.Lay (VG.Proof.AesOcb.X86.prmOf s) := by
  obtain ⟨kd, kw, _, nd, nw, _, ad, aw, _, dt, dw, _, tw, _, _, rk, _, _, rd, rt, rw, _, bk, bn, ba, bd, bt, bw,
    _, fK, fN, fA, fD, fT, fW, sp24, _, hR, hl⟩ := h.lay
  simp only [VG.Proof.AesOcb.X86.stackR] at bk bn ba bd bt bw
  rw [show (24 : Addr) = BitVec.ofNat 64 24 from rfl, below_eq sp24] at bk bn ba bd bt bw
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨t1, t16⟩, n1⟩, n15⟩ := hl
  exact ⟨fK, fW, fN, fA, fD, fT, sp24, kw, kd, nw, nd, aw, ad, dw, tw, dt.symm, bk, bn, ba, bd, bw, bt, hR,
    n1, n15, t1, t16, BitVec.isLt _, BitVec.isLt _, rw, rd, rt⟩

theorem perm_of {s : State} (h : VG.Proof.AesOcb.X86.onePre s) : VG.Proof.AesOcb.X86.Perm (VG.Proof.AesOcb.X86.prmOf s) s :=
  ⟨h.rd (VG.Proof.AesOcb.X86.ctxR s) (by simp), h.rd (VG.Proof.AesOcb.X86.nonceR s) (by simp), h.rd (VG.Proof.AesOcb.X86.aadR s) (by simp), h.wr (VG.Proof.AesOcb.X86.dataR s) (by simp),
    h.wr (VG.Proof.AesOcb.X86.workR s) (by simp), h.rd (VG.Proof.AesOcb.X86.tagR s) (by simp)⟩

theorem argsOk_of {s : State} (h : VG.Proof.AesOcb.X86.onePre s) : VG.Proof.AesOcb.X86.ArgsOk s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, wa, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, spf, -, -⟩ := h.lay
  refine ⟨?_, ?_, by omega⟩
  · rw [argsR_eq]; exact covers_left (h.wr (VG.Proof.AesOcb.X86.argsR' s) (by simp))
  · rw [argsR_eq]; exact wa.symm

/-- The arguments the entry copies, and where. -/
abbrev entryPs : List (Nat × Nat) :=
  [(0, ctxO), (1, rndO), (2, nO), (3, nlO), (4, aadO), (5, alenO), (6, dataO), (7, lenO), (8, tgO), (9, tlO)]

theorem ocbEntry_eq : ocbEntry = entry 10 (entryPs.flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2)) := rfl

/-- What the entry leaves. -/
structure Entered (s : State) (p : VG.Proof.AesOcb.X86.Prm) (s' : State) : Prop where
  env : VG.Proof.AesOcb.X86.Env p s'
  saved : SavedAt s'.mem p.W s
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 128, 88⟩] s.mem s'.mem

/-- The entry. -/
theorem entry_ok {s : State} (h : VG.Proof.AesOcb.X86.onePre s) : WP isa ocbEntry s (VG.Proof.AesOcb.X86.Entered s (VG.Proof.AesOcb.X86.prmOf s)) := by
  have L := VG.Proof.AesOcb.X86.lay_of h
  have P := VG.Proof.AesOcb.X86.perm_of h
  have Ao := VG.Proof.AesOcb.X86.argsOk_of h
  rw [VG.Proof.AesOcb.X86.ocbEntry_eq]
  generalize hSP : s.gpr .esp = SP at Ao
  have rA := Ao.rA
  have aw := Ao.aw
  have fa := Ao.fa
  rw [hSP] at rA aw fa
  have fw : (arg s 10).toNat + 2560 ≤ 2 ^ 32 := by have := L.ww; simp only [VG.Proof.AesOcb.X86.prmOf] at this; omega
  have wW : Covers [⟨w64 (arg s 10), 2560⟩] s.wr := P.w2560
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 10) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.seq (WP.of_runBlock ⟨_, by grun [hSP, i₀], ?_⟩)
  have hax : (s.setReg .eax (s.mem.readW (argA SP 10) 32)).gpr .eax = arg s 10 := by
    rw [gpr_setReg_self, ← hSP]; rfl
  set s₀ := s.setReg .eax (s.mem.readW (argA SP 10) 32) with hs₀
  obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := save_ok s₀ hax (by rw [hs₀]; exact wW) fw
  have sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide), hSP]
  have argW : ∀ {i}, i < 11 → ∀ {d k : Nat}, d + k ≤ 2560 →
      ∀ r ∈ [(⟨w64 (arg s 10) + BitVec.ofNat 64 d, k⟩ : Region)], (⟨argA SP i, 4⟩ : Region).Disjoint r :=
    fun hi _ _ hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (aw.sub_left (argA_sub hi fa)).sub_right (Lay.wSub hk)
  have hA₁ : ∀ i < 11, s₁.mem.readW (argA SP i) 32 = arg s i := fun i hi => by
    rw [f₁.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (argW hi (by decide)) (by decide)]
    rw [arg, argAddr, hSP]
    exact rfl
  have aw' : (argsR SP 11).Disjoint ⟨w64 (arg s 10), 2560⟩ := aw.sub_right (Region.sub_prefix (by decide))
  have ke : KeepEnv (arg s 10) SP 11 s₁ := ⟨bp₁, sp₁, by rw [wr₁]; exact wW, by rw [rd₁, wr₁]; exact rA, aw', fa, fw⟩
  obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := keeps_ok VG.Proof.AesOcb.X86.entryPs (fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) ke
  have bp₃ : s₃.gpr .ebp = arg s 10 := by rw [g₃ _ (by decide), bp₁]
  have sp₃ : s₃.gpr .esp = SP := by rw [g₃ _ (by decide), sp₁]
  refine WP.of_runBlock ⟨_, runBlock_app_of run₁ run₃, ?_⟩
  -- What the entry wrote.
  have f₃' : Frame [⟨w64 (arg s 10) + BitVec.ofNat 64 128, 88⟩] s.mem s₃.mem := by
    refine (f₁.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hsv : SavedAt s₃.mem (arg s 10) s := by
    have := sv₁.frame f₃ fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    obtain ⟨a, b, c, d⟩ := this
    refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_⟩ <;>
      simp only [hs₀, gpr_setReg_of_ne _ _ (by decide : Reg.ebx ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.esi ≠ .eax),
        gpr_setReg_of_ne _ _ (by decide : Reg.edi ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.ebp ≠ .eax)]
  have sl : ∀ q ∈ VG.Proof.AesOcb.X86.entryPs, slotv s₃.mem (arg s 10) q.2 = arg s q.1 := fun q hq => by
    have e := sl₃ q hq
    have hq1 : q.1 < 11 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hA₁ q.1 hq1] at e
    exact e
  have ofN : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => BitVec.eq_of_toNat_eq (by simp)
  refine ⟨⟨bp₃, by rw [sp₃, ← hSP]; rfl, P.of_eq (by rw [rd₃, rd₁]; rfl) (by rw [wr₃, wr₁]; rfl),
    ⟨sl (0, ctxO) (by simp), by simp only [VG.Proof.AesOcb.X86.prmOf]; rw [sl (1, rndO) (by simp)]; exact (ofN _).symm,
      sl (2, nO) (by simp), by simp only [VG.Proof.AesOcb.X86.prmOf]; rw [sl (3, nlO) (by simp)]; exact (ofN _).symm,
      sl (4, aadO) (by simp), by simp only [VG.Proof.AesOcb.X86.prmOf]; rw [sl (5, alenO) (by simp)]; exact (ofN _).symm,
      sl (6, dataO) (by simp), by simp only [VG.Proof.AesOcb.X86.prmOf]; rw [sl (7, lenO) (by simp)]; exact (ofN _).symm,
      sl (8, tgO) (by simp), by simp only [VG.Proof.AesOcb.X86.prmOf]; rw [sl (9, tlO) (by simp)]; exact (ofN _).symm⟩⟩, hsv, by rw [rd₃, rd₁]; rfl, by rw [wr₃, wr₁]; rfl, f₃'⟩

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Callee`. -/
section

/-!
# AES-OCB on x86: the calls

Untrusted: everything here is checked by Lean. Each call of
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` (of any implementation
`v`), and of `vg_aes_expand_key_scratch`, in a frame of its arguments, from the
callee's contract (`WP.callWith`): what it needs of the registers it pushes
and of the regions it is given (`BCall`, AES-GCM's `KeyCall`), and what it leaves
(`BPost`, `KeyPost`), in terms of the memory before the call; and that it is
constant time (`blk_ct`, `key_ct`) by the callee's own proof, when the
arguments are the same in both runs.
-/

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 bytesAt_frame one_disj toNat_rounds CT)

/-- The implementations `v` call. -/
def callees (v : BlocksImpl) : Callees :=
  ⟨⟨v.enc.name, v.enc.code⟩, ⟨v.dec.name, v.dec.code⟩, ⟨v.expand.name, v.expand.code⟩⟩

/-- The `n` blocks at `p`, as states, over code that writes only elsewhere. -/
theorem statesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Aes.statesAt m' p n = Spec.Aes.statesAt m p n := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  simp only [Spec.Aes.stateAt]
  congr 1
  funext j
  rw [VG.Proof.AesOcb.X86.add_ofNat_assoc]
  exact hf.bytes (R := ⟨p, 16 * n⟩) hd hn (show 16 * i + j.1 < 16 * n by have := j.2; omega)

/-! ## `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` -/

abbrev blkRegs : List Reg := [.ebp, .ebx, .edx, .ecx, .eax]

theorem blkRegs_esp : Reg.esp ∉ VG.Proof.AesOcb.X86.blkRegs := by decide

/-- What a call of `vg_aes_*_blocks` needs: the key schedule at `K` for `R`
rounds, `n` blocks at `D` and working space at `S`. -/
structure BCall (s : State) (K D S : BitVec 32) (R n : Nat) : Prop where
  eax : s.gpr .eax = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = D
  ebx : s.gpr .ebx = BitVec.ofNat 32 n
  ebp : s.gpr .ebp = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  esp : 24 ≤ (s.gpr .esp).toNat
  kd : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, 16 * n⟩
  ks : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 S, 2048⟩
  ds : (⟨w64 D, 16 * n⟩ : Region).Disjoint ⟨w64 S, 2048⟩
  bk : (below (s.gpr .esp) 24).Disjoint ⟨w64 K, 240⟩
  bd : (below (s.gpr .esp) 24).Disjoint ⟨w64 D, 16 * n⟩
  bs : (below (s.gpr .esp) 24).Disjoint ⟨w64 S, 2048⟩
  fK : K.toNat + 240 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 2048 ≤ 2 ^ 32
  reads : Covers [⟨w64 K, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨w64 D, 16 * n⟩, ⟨w64 S, 2048⟩] s.wr

/-- What a call of a function with the contract `blocksX86 f` leaves. -/
structure BPost (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (K D S : BitVec 32) (R n : Nat)
    (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨w64 D, 16 * n⟩, ⟨w64 S, 2048⟩, below (s.gpr .esp) 24] s.mem s'.mem
  out : Spec.Aes.statesAt s'.mem (w64 D) n =
    (Spec.Aes.statesAt s.mem (w64 D) n).map (f R (bytesAt s.mem (w64 K) (16 * (R + 1))))

abbrev blkRd (E K : BitVec 32) : List Region := [⟨w64 K, 240⟩, below E 20]
abbrev blkWr (D S : BitVec 32) (n : Nat) : List Region := [⟨w64 D, 16 * n⟩, ⟨w64 S, 2048⟩]

namespace BCall
variable {s : State} {K D S : BitVec 32} {R n : Nat} (h : VG.Proof.AesOcb.X86.BCall s K D S R n)
include h

theorem fit : 4 * blkRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem n_lt : n < 2 ^ 32 := by have := h.fD; omega

theorem args : arg (pushed VG.Proof.AesOcb.X86.blkRegs s).callEntry 0 = K ∧ arg (pushed VG.Proof.AesOcb.X86.blkRegs s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed VG.Proof.AesOcb.X86.blkRegs s).callEntry 2 = D ∧ arg (pushed VG.Proof.AesOcb.X86.blkRegs s).callEntry 3 = BitVec.ofNat 32 n ∧
    arg (pushed VG.Proof.AesOcb.X86.blkRegs s).callEntry 4 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit VG.Proof.AesOcb.X86.blkRegs_esp (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.ebp]

theorem sub20 : Region.Sub (below (s.gpr .esp) 20) (below (s.gpr .esp) 24) := below_sub (by omega) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below (s.gpr .esp) 24) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 24) (k := 20) (by omega) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 24 = s.gpr .esp - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem callPre (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) :
    CallPre (Proof.Aes.blocksX86 f) VG.Proof.AesOcb.X86.blkRegs (VG.Proof.AesOcb.X86.blkRd (s.gpr .esp) K) (VG.Proof.AesOcb.X86.blkWr D S n) s := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h.args
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat32 h.n_lt
  have eA : argAddr (pushed VG.Proof.AesOcb.X86.blkRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed VG.Proof.AesOcb.X86.blkRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Aes.blocksX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, hR, hn]
    refine ⟨trivial, trivial, h.kd, h.ks, h.ds, h.bd.sub_left h.sub20, h.bs.sub_left h.sub20,
      h.bd.sub_left h.sub4, h.bs.sub_left h.sub4, h.fK, h.fD, h.fS, ?_, h.rounds⟩
    rw [sub_toNat (by have := h.esp; omega)]; have := (s.gpr .esp).isLt; omega
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a m hi
    obtain ⟨r', hr', hc'⟩ := h.writes a m hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end BCall

/-- A call of `vg_aes_*_blocks` with the contract `blocksX86 f`. -/
theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0)
    {s : State} {K D S : BitVec 32} {R n : Nat} (h : VG.Proof.AesOcb.X86.BCall s K D S R n) :
    WP isa (blocksFrame fn) s (VG.Proof.AesOcb.X86.BPost f s K D S R n) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat32 h.n_lt
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  unfold blocksFrame
  refine WP.callWith (rs := VG.Proof.AesOcb.X86.blkRegs) (k := Proof.Aes.blocksX86 f) ok nosp (by simp)
    VG.Proof.AesOcb.X86.blkRegs_esp (by rw [stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega)
    (h.callPre f) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, -⟩ := h.args
  rw [stack] at f'
  have fE := callEntry_frame h.fit VG.Proof.AesOcb.X86.blkRegs_esp
  rw [show 4 * blkRegs.length + 4 = 24 from rfl] at fE
  simp only [Proof.Aes.blocksX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, hR, hn, m₂] at post
  have eK := bytesAt_frame fE (p := w64 K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bk.sub_right (Region.sub_prefix hR')).symm) (by omega)
  rw [VG.Proof.AesOcb.X86.statesAt_frame fE (one_disj h.bd) (by have := h.fD; omega), eK] at post
  refine ⟨rd', wr', cs', ?_, post⟩
  exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr

/-- Calls of `vg_aes_*_blocks` with the same arguments and stack pointer in
both runs are constant time. -/
theorem blk_ct {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub fn.code)
    {I : State → Prop} {K D S E : BitVec 32} {R n : Nat}
    (h : ∀ s, I s → VG.Proof.AesOcb.X86.BCall s K D S R n ∧ s.gpr .esp = E) : CT I (blocksFrame fn) := by
  refine CT.callWith ok ct (VG.Proof.AesOcb.X86.blkRd E K) (VG.Proof.AesOcb.X86.blkWr D S n) fun s₁ s₂ i₁ i₂ => ?_
  obtain ⟨h₁, e₁⟩ := h s₁ i₁
  obtain ⟨h₂, e₂⟩ := h s₂ i₂
  have p₁ := h₁.callPre f
  have p₂ := h₂.callPre f
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4⟩ := h₂.args
  simp only [Proof.Aes.blocksX86]
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]

/-! ## `vg_aes_expand_key_scratch` -/

open VG.Proof.AesGcm.X86 (KeyCall KeyPost keyRegs keyRegs_esp keyRd keyWr) in
/-- A call of `vg_aes_expand_key_scratch`. -/
theorem key_ok (v : BlocksImpl) {s : State} {K C S : BitVec 32} {L : Nat} (h : KeyCall s K C S L) :
    WP isa (keyFrame (VG.Proof.AesOcb.X86.callees v)) s (KeyPost s K C S L) := by
  have hL := toNat_ofNat32 h.L_lt
  unfold keyFrame
  refine WP.callWith (rs := keyRegs) (k := Proof.Aes.expandKeyX86) v.expandOk v.expandNosp
    (by simp) keyRegs_esp (by rw [v.expandStack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, -⟩ := h.args
  rw [v.expandStack] at f'
  have fE := callEntry_frame h.fit keyRegs_esp
  rw [show 4 * keyRegs.length + 4 = 20 from rfl] at fE
  simp only [Proof.Aes.expandKeyX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, hL, m₂] at post
  refine ⟨rd', wr', cs', ?_, ?_⟩
  · exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr
  · rw [post, bytesAt_frame fE (one_disj h.bk) (by rcases h.len with rfl | rfl | rfl <;> decide)]

open VG.Proof.AesGcm.X86 (KeyCall keyRd keyWr) in
/-- Calls of `vg_aes_expand_key_scratch` with the same arguments and stack pointer
in both runs are constant time. -/
theorem key_ct (v : BlocksImpl) {I : State → Prop} {K C S E : BitVec 32} {L : Nat}
    (h : ∀ s, I s → KeyCall s K C S L ∧ s.gpr .esp = E) : CT I (keyFrame (VG.Proof.AesOcb.X86.callees v)) := by
  refine CT.callWith v.expandOk v.expandCt (keyRd E K L) (keyWr C S) fun s₁ s₂ i₁ i₂ => ?_
  obtain ⟨h₁, e₁⟩ := h s₁ i₁
  obtain ⟨h₂, e₂⟩ := h s₂ i₂
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Dbl`. -/
section

/-!
# AES-OCB on x86: doubling a block

Untrusted: everything here is checked by Lean. `dbl b s d` doubles the
block at `b + s` into `W + d` (`dblMem`): its words are byte-reversed into
numbers, doubled a word at a time as x86's CMAC does (`Proof.Cmac.dblW0`,
`dblW3`), and byte-reversed back, so that the block written is `double` of
the block read (`dblMem_block`). The run (`dblW_ok`, `dblK_ok`) reads each
word of the source before the word of the destination before it is
written, so the source may be the destination.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq w64_add in_off in_left)

theorem bswap_eq (a : BitVec 32) : bswap a = byteRev32 a := rfl

theorem add_self_shl (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  congr 1; omega

/-- The memory `dbl` leaves: the block at `A + s` doubled into `B + d`. -/
def dblMem (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) : Mem :=
  let b₀ := byteRev32 (m.readW (A + BitVec.ofNat 64 s) 32)
  let b₁ := byteRev32 (m.readW (A + BitVec.ofNat 64 (s + 4)) 32)
  let b₂ := byteRev32 (m.readW (A + BitVec.ofNat 64 (s + 8)) 32)
  let b₃ := byteRev32 (m.readW (A + BitVec.ofNat 64 (s + 12)) 32)
  Proof.Cmac.store4 m (B + BitVec.ofNat 64 d) (byteRev32 (Proof.Cmac.dblW0 b₀ b₁))
    (byteRev32 (Proof.Cmac.dblW0 b₁ b₂)) (byteRev32 (Proof.Cmac.dblW0 b₂ b₃)) (byteRev32 (Proof.Cmac.dblW3 b₀ b₃))

theorem dblMem_frame (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    Frame [⟨B + BitVec.ofNat 64 d, 16⟩] m (VG.Proof.AesOcb.X86.dblMem m A s B d) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem dblMem_bytes (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    bytesAt (VG.Proof.AesOcb.X86.dblMem m A s B d) (B + BitVec.ofNat 64 d) 16 = Spec.Cmac.dbl 16 (bytesAt m (A + BitVec.ofNat 64 s) 16) := by
  simp only [VG.Proof.AesOcb.X86.dblMem]
  rw [Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_rev4, Proof.Cmac.dbl_words4,
    Proof.Cmac.dbl_eq (Proof.Cmac.bytesAt_length _ _ _), Proof.Cmac.ofBytes_rev4, VG.Proof.AesOcb.X86.add_ofNat_assoc,
    VG.Proof.AesOcb.X86.add_ofNat_assoc, VG.Proof.AesOcb.X86.add_ofNat_assoc]

/-- The block `dbl` writes is `double` of the block it reads. -/
theorem dblMem_block (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    Spec.Ocb.blockAtMem (VG.Proof.AesOcb.X86.dblMem m A s B d) (B + BitVec.ofNat 64 d) =
      Spec.Ocb.double (Spec.Ocb.blockAtMem m (A + BitVec.ofNat 64 s)) := by
  rw [Spec.Ocb.blockAtMem, VG.Proof.AesOcb.X86.dblMem_bytes, Proof.Cmac.dbl_eq (Proof.Cmac.bytesAt_length _ _ _),
    Proof.Ocb.double_eq, Spec.Ocb.blockAtMem, Proof.Ocb.ofBytes_eq, Proof.Cmac.ofBytes_toBytes]

/-- `dbl` within `W` (`ebp`), from `W + s` to `W + d`, the same block or
apart. -/
theorem dblW_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {s d : Nat} (hs : s + 16 ≤ 2560)
    (hd : d + 16 ≤ 2560) (hsd : s = d ∨ s + 16 ≤ d ∨ d + 16 ≤ s) :
    ∃ t', runBlock isa (dbl .ebp s d) t = some t' ∧ t'.mem = VG.Proof.AesOcb.X86.dblMem t.mem (w64 p.W) s (w64 p.W) d ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [dbl, Impl.AesOcb.X86.dblW, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_, fun r h₁ h₂ h₃ => by
    gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [VG.Proof.AesOcb.X86.bswap_eq, VG.Proof.AesOcb.X86.add_self_shl]
  rw [Proof.AesGcm.X86.store4_eq]
  simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
  rfl

/-- A word of the key context, after a word of `W` written. -/
theorem readW_KW {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) (m : Mem) (v : BitVec 32) {a b : Nat} (ha : a + 4 ≤ 256)
    (hb : b + 4 ≤ 2560) :
    (m.writeW (w64 p.W + BitVec.ofNat 64 b) v).readW (w64 p.K + BitVec.ofNat 64 a) 32 =
      m.readW (w64 p.K + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (L.k_w.sep (Offset.contains_base _ ha (by have := L.kw; omega))
    (Offset.contains_base _ hb (by have := L.ww; omega))) (by decide)

/-- `dbl` from the key context (`ebx`) at `K + s` to `W + d`. -/
theorem dblK_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) (hb : t.gpr .ebx = p.K) {s d : Nat}
    (hs : s + 16 ≤ 256) (hd : d + 16 ≤ 2560) :
    ∃ t', runBlock isa (dbl .ebx s d) t = some t' ∧ t'.mem = VG.Proof.AesOcb.X86.dblMem t.mem (w64 p.K) s (w64 p.W) d ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [dbl, Impl.AesOcb.X86.dblW, E.ebp, hb, L.aW, L.aK, E.perm.wR, E.perm.wW, E.perm.kR,
    (VG.Proof.AesOcb.X86.readW_KW L)], ?_, fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [VG.Proof.AesOcb.X86.bswap_eq, VG.Proof.AesOcb.X86.add_self_shl, (VG.Proof.AesOcb.X86.readW_KW L)]
  rw [Proof.AesGcm.X86.store4_eq]
  simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
  rfl

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Blk`. -/
section

/-!
# AES-OCB on x86: blocks copied and XORed a word at a time

Untrusted: everything here is checked by Lean. `copy16 s d` copies the
block at `W + s` to `W + d` (`copyMem16`), and `xor16 b s d` XORs the block
at `b + s` into `W + d` (`xorMem16`), a word at a time; as blocks, the
block written is the one read (`copyMem16_block`), or the XOR of the two
(`xorMem16_block`). The runs are within `W` (`copy16_ok`, `xor16W_ok`) or
read another buffer, apart from `W` (`xor16R_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq w64_add in_off in_left)

/-! ## Memory -/

/-- The memory after the block at `A + s` is copied to `B + d`. -/
def copyMem16 (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) : Mem :=
  Proof.Cmac.store4 m (B + BitVec.ofNat 64 d) (m.readW (A + BitVec.ofNat 64 s) 32)
    (m.readW (A + BitVec.ofNat 64 (s + 4)) 32) (m.readW (A + BitVec.ofNat 64 (s + 8)) 32)
    (m.readW (A + BitVec.ofNat 64 (s + 12)) 32)

/-- The memory after the block at `A + s` is XORed into `B + d`. -/
def xorMem16 (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) : Mem :=
  Proof.Cmac.store4 m (B + BitVec.ofNat 64 d)
    (m.readW (B + BitVec.ofNat 64 d) 32 ^^^ m.readW (A + BitVec.ofNat 64 s) 32)
    (m.readW (B + BitVec.ofNat 64 (d + 4)) 32 ^^^ m.readW (A + BitVec.ofNat 64 (s + 4)) 32)
    (m.readW (B + BitVec.ofNat 64 (d + 8)) 32 ^^^ m.readW (A + BitVec.ofNat 64 (s + 8)) 32)
    (m.readW (B + BitVec.ofNat 64 (d + 12)) 32 ^^^ m.readW (A + BitVec.ofNat 64 (s + 12)) 32)

theorem copyMem16_frame (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    Frame [⟨B + BitVec.ofNat 64 d, 16⟩] m (VG.Proof.AesOcb.X86.copyMem16 m A s B d) := Proof.Cmac.frame_store4 _ _ _ _ _

theorem xorMem16_frame (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    Frame [⟨B + BitVec.ofNat 64 d, 16⟩] m (VG.Proof.AesOcb.X86.xorMem16 m A s B d) := Proof.Cmac.frame_store4 _ _ _ _ _

theorem copyMem16_bytes (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    bytesAt (VG.Proof.AesOcb.X86.copyMem16 m A s B d) (B + BitVec.ofNat 64 d) 16 = bytesAt m (A + BitVec.ofNat 64 s) 16 := by
  rw [VG.Proof.AesOcb.X86.copyMem16, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.bytesAt_split4, VG.Proof.AesOcb.X86.add_ofNat_assoc, VG.Proof.AesOcb.X86.add_ofNat_assoc, VG.Proof.AesOcb.X86.add_ofNat_assoc]

theorem copyMem16_block (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    blockAtMem (VG.Proof.AesOcb.X86.copyMem16 m A s B d) (B + BitVec.ofNat 64 d) = blockAtMem m (A + BitVec.ofNat 64 s) := by
  rw [blockAtMem, VG.Proof.AesOcb.X86.copyMem16_bytes, ← blockAtMem]

theorem xorMem16_bytes (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    bytesAt (VG.Proof.AesOcb.X86.xorMem16 m A s B d) (B + BitVec.ofNat 64 d) 16 =
      Spec.Cmac.xor (bytesAt m (B + BitVec.ofNat 64 d) 16) (bytesAt m (A + BitVec.ofNat 64 s) 16) := by
  rw [VG.Proof.AesOcb.X86.xorMem16, Proof.Cmac.bytesAt_store4, ← VG.Proof.AesOcb.X86.add_ofNat_assoc _ d 4, ← VG.Proof.AesOcb.X86.add_ofNat_assoc _ d 8,
    ← VG.Proof.AesOcb.X86.add_ofNat_assoc _ d 12, ← VG.Proof.AesOcb.X86.add_ofNat_assoc _ s 4, ← VG.Proof.AesOcb.X86.add_ofNat_assoc _ s 8, ← VG.Proof.AesOcb.X86.add_ofNat_assoc _ s 12,
    Proof.Cmac.xor_words4]

theorem xorMem16_block (m : Mem) (A : Addr) (s : Nat) (B : Addr) (d : Nat) :
    blockAtMem (VG.Proof.AesOcb.X86.xorMem16 m A s B d) (B + BitVec.ofNat 64 d) =
      blockAtMem m (B + BitVec.ofNat 64 d) ^^^ blockAtMem m (A + BitVec.ofNat 64 s) := by
  rw [blockAtMem, VG.Proof.AesOcb.X86.xorMem16_bytes, ← Proof.Ocb.xor_eq, Proof.Ocb.ofBytes_xor (Proof.Cmac.bytesAt_length _ _ _)
    (Proof.Cmac.bytesAt_length _ _ _)]
  rfl

/-! ## Runs -/

/-- `copy16 s d` within `W`, the blocks apart. -/
theorem copy16_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {s d : Nat} (hs : s + 16 ≤ 2560)
    (hd : d + 16 ≤ 2560) (hsd : s + 16 ≤ d ∨ d + 16 ≤ s) :
    ∃ t', runBlock isa (copy16 s d) t = some t' ∧ t'.mem = VG.Proof.AesOcb.X86.copyMem16 t.mem (w64 p.W) s (w64 p.W) d ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [copy16, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_, fun r h₁ => by gregs [h₁], by gmems [],
    by gmems []⟩
  gmems []
  rw [Proof.AesGcm.X86.store4_eq]
  rfl

/-- `xor16 .ebp s d` within `W`, the blocks apart. -/
theorem xor16W_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {s d : Nat} (hs : s + 16 ≤ 2560)
    (hd : d + 16 ≤ 2560) (hsd : s + 16 ≤ d ∨ d + 16 ≤ s) :
    ∃ t', runBlock isa (xor16 .ebp s d) t = some t' ∧ t'.mem = VG.Proof.AesOcb.X86.xorMem16 t.mem (w64 p.W) s (w64 p.W) d ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [xor16, xorW, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_, fun r h₁ => by gregs [h₁],
    by gmems [], by gmems []⟩
  gmems []
  rw [Proof.AesGcm.X86.store4_eq]
  simp only [Nat.add_zero]
  rfl

/-- A word of a buffer `⟨B, k⟩` apart from `W`, after a word of `W` written. -/
theorem readW_XW {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {B : Addr} {k : Nat} (hB : B.toNat + k ≤ 2 ^ 32)
    (hd : (⟨B, k⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) (m : Mem) (v : BitVec 32) {a b : Nat} (ha : a + 4 ≤ k)
    (hb : b + 4 ≤ 2560) :
    (m.writeW (w64 p.W + BitVec.ofNat 64 b) v).readW (B + BitVec.ofNat 64 a) 32 = m.readW (B + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (hd.sep (Offset.contains_base _ ha (by omega))
    (Offset.contains_base _ hb (by have := L.ww; omega))) (by decide)

/-- `xor16 b s d`, reading the block at `b + s` of a buffer `⟨w64 X, k⟩`
apart from `W`. -/
theorem xor16R_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {b : Reg} (hb : b ≠ .eax) {X : BitVec 32}
    (hX : t.gpr b = X) {k : Nat} (hk : X.toNat + k ≤ 2 ^ 32)
    (hdis : (⟨w64 X, k⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) (hR : Covers [⟨w64 X, k⟩] (t.rd ++ t.wr)) {s d : Nat}
    (hs : s + 16 ≤ k) (hd : d + 16 ≤ 2560) :
    ∃ t', runBlock isa (xor16 b s d) t = some t' ∧ t'.mem = VG.Proof.AesOcb.X86.xorMem16 t.mem (w64 X) s (w64 p.W) d ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have aX : ∀ {o : Nat}, o < k → w64 (X + BitVec.ofNat 32 o) = w64 X + BitVec.ofNat 64 o := fun ho =>
    w64_add (by omega)
  have rX : ∀ {o : Nat}, o + 4 ≤ k → InRegions (t.rd ++ t.wr) (w64 X + BitVec.ofNat 64 o) 4 := fun ho =>
    in_off hR ho (by omega)
  have hXk : (w64 X).toNat + k ≤ 2 ^ 32 := by rw [Proof.AesGcm.X86.toNat_w64]; exact hk
  refine ⟨_, by grun [xor16, xorW, E.ebp, hX, L.aW, aX, rX, E.perm.wR, E.perm.wW, (VG.Proof.AesOcb.X86.readW_XW L hXk hdis)],
    ?_, fun r h₁ => by gregs [h₁], by gmems [], by gmems []⟩
  gmems [(VG.Proof.AesOcb.X86.readW_XW L hXk hdis)]
  rw [Proof.AesGcm.X86.store4_eq]
  simp only [Nat.add_zero]
  rfl

/-- `xor16 b 0 d`, `b` pointing at `W + e`, the blocks apart. -/
theorem xor16P_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {b : Reg} (hb : b ≠ .eax) {e d : Nat}
    (hbv : t.gpr b = p.W + BitVec.ofNat 32 e) (he : e + 16 ≤ 2560) (hd : d + 16 ≤ 2560)
    (hed : e + 16 ≤ d ∨ d + 16 ≤ e) :
    ∃ t', runBlock isa (xor16 b 0 d) t = some t' ∧ t'.mem = VG.Proof.AesOcb.X86.xorMem16 t.mem (w64 p.W) e (w64 p.W) d ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have aE : ∀ {k : Nat}, k < 16 → w64 (p.W + BitVec.ofNat 32 e + BitVec.ofNat 32 k) = w64 p.W + BitVec.ofNat 64 (e + k) :=
    fun hk => by rw [Proof.AesGcm.X86.add_ofNat_assoc32]; exact L.aW (by omega)
  refine ⟨_, by grun [xor16, xorW, E.ebp, hbv, aE, L.aW, E.perm.wR, E.perm.wW], ?_, fun r h₁ => by gregs [h₁],
    by gmems [], by gmems []⟩
  gmems []
  rw [Proof.AesGcm.X86.store4_eq]
  simp only [Nat.add_zero, Nat.zero_add]
  rfl

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.LNtz`. -/
section

/-!
# AES-OCB on x86: `L_{ntz(i)}` (`lNtz`)

Untrusted: everything here is checked by Lean. `lNtz` copies `L_0` to
`W + lO` and doubles it while the block index `i` (in `edi`), shifted right
once more each time (at `W + kO`), is even: `ntz(i)` times (`lNtz_ok`). The
invariant: after `j` doublings, `W + lO` holds `L_j`, `W + kO` holds
`i / 2^j`, which is positive, and `ntz(i) = j + ntz(i / 2^j)`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq toNat_ofNat32 runBlock_app_of)

theorem even_zf32 {v : Nat} (hv : v < 2 ^ 32) :
    (BitVec.ofNat 32 v &&& 1#32 == 0) = decide (v % 2 = 0) := by
  have : BitVec.ofNat 32 v &&& 1#32 = BitVec.ofNat 32 (v % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, toNat_ofNat32 hv, toNat_ofNat32 (by decide), Nat.and_one_is_mod,
      toNat_ofNat32 (by omega)]
  rw [this]
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> rw [h] <;> decide

theorem shr1_32 {v : Nat} (hv : v < 2 ^ 32) : BitVec.ofNat 32 v >>> 1 = BitVec.ofNat 32 (v / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat32 hv, toNat_ofNat32 (by omega), Nat.shiftRight_eq_div_pow]

/-- The regions `lNtz` writes. -/
abbrev lNtzR (p : VG.Proof.AesOcb.X86.Prm) : List Region := [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩]

theorem inMut_lNtzR (p : VG.Proof.AesOcb.X86.Prm) : VG.Proof.AesOcb.X86.InMut p (VG.Proof.AesOcb.X86.lNtzR p) := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))

/-- What `lNtz` leaves. -/
structure LNtzPost (p : VG.Proof.AesOcb.X86.Prm) (l : Block) (i : Nat) (s s' : State) : Prop where
  frame : Frame (VG.Proof.AesOcb.X86.lNtzR p) s.mem s'.mem
  val : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 lO) = lAt l (ntz i)
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem LNtzPost.env {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {l : Block} {i : Nat} {s s' : State} (E : VG.Proof.AesOcb.X86.Env p s)
    (h : VG.Proof.AesOcb.X86.LNtzPost p l i s s') : VG.Proof.AesOcb.X86.Env p s' :=
  E.mut L (by rw [h.gpr _ (by decide) (by decide) (by decide), E.ebp])
    (by rw [h.gpr _ (by decide) (by decide) (by decide), E.esp]) h.rd h.wr (VG.Proof.AesOcb.X86.frame_toMut h.frame (VG.Proof.AesOcb.X86.inMut_lNtzR p))

/-- What a step leaves: `W + lO` written as `h` says, then `W + kO`. -/
theorem lNtz_frame {p : VG.Proof.AesOcb.X86.Prm} {m m' : Mem} (h : Frame [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩] m m')
    (v : BitVec 32) : Frame (VG.Proof.AesOcb.X86.lNtzR p) m (m'.writeW (w64 p.W + BitVec.ofNat 64 kO) v) :=
  (h.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).writeW (r := ⟨_, 4⟩)
    (by simp) v (Region.contains_self _ _)

theorem lO_kO (p : VG.Proof.AesOcb.X86.Prm) : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩ : Region)],
    (⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩ : Region).Disjoint r := by
  simp only [List.mem_singleton, forall_eq]
  exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem block_writeK (p : VG.Proof.AesOcb.X86.Prm) (m : Mem) (v : BitVec 32) :
    blockAtMem (m.writeW (w64 p.W + BitVec.ofNat 64 kO) v) (w64 p.W + BitVec.ofNat 64 lO) =
      blockAtMem m (w64 p.W + BitVec.ofNat 64 lO) :=
  Proof.Ocb.blockAtMem_frame ((Frame.refl _ m).writeW (List.mem_singleton_self _) v (Region.contains_self _ _))
    (VG.Proof.AesOcb.X86.lO_kO p)

theorem readK_dbl (p : VG.Proof.AesOcb.X86.Prm) (m : Mem) :
    (VG.Proof.AesOcb.X86.dblMem m (w64 p.W) lO (w64 p.W) lO).readW (w64 p.W + BitVec.ofNat 64 kO) 32 =
      m.readW (w64 p.W + BitVec.ofNat 64 kO) 32 :=
  (VG.Proof.AesOcb.X86.dblMem_frame m _ lO _ lO).readW (Region.contains_self _ _) (by
    simp only [List.mem_singleton, forall_eq]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by decide)

/-- One step of `lNtz`'s loop: `W + lO` doubled, `W + kO` halved, and ZF set
if what is left is even. -/
theorem lNtzStep_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (Et : VG.Proof.AesOcb.X86.Env p t) {k : Nat} (hk : k < 2 ^ 32)
    (kt : slotv t.mem p.W kO = BitVec.ofNat 32 k) :
    ∃ t₂, runBlock isa (dbl .ebp lO lO ++ ([.mov .eax (slot kO), .shift .shr .eax 1, .store (at_ .ebp kO) .eax,
        .alu .test .eax (imm 1)] : List Instr)) t = some t₂ ∧
      Frame (VG.Proof.AesOcb.X86.lNtzR p) t.mem t₂.mem ∧
      blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 lO) = double (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 lO)) ∧
      slotv t₂.mem p.W kO = BitVec.ofNat 32 (k / 2) ∧ t₂.zf = some (decide (k / 2 % 2 = 0)) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₂.gpr r = t.gpr r) ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr := by
  obtain ⟨t₁, runt₁, m₁', g₁', rd₁', wr₁'⟩ := VG.Proof.AesOcb.X86.dblW_ok L Et (s := lO) (d := lO) (by decide) (by decide) (.inl rfl)
  have Et₁ : VG.Proof.AesOcb.X86.Env p t₁ := Et.mut L (by rw [g₁' _ (by decide) (by decide) (by decide), Et.ebp])
    (by rw [g₁' _ (by decide) (by decide) (by decide), Et.esp]) rd₁' wr₁'
    (VG.Proof.AesOcb.X86.frame_toMut (by rw [m₁']; exact VG.Proof.AesOcb.X86.dblMem_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  have kt₁ : t₁.mem.readW (w64 p.W + BitVec.ofNat 64 kO) 32 = BitVec.ofNat 32 k := by
    rw [m₁', VG.Proof.AesOcb.X86.readK_dbl, ← slotv_eq, kt]
  obtain ⟨t₂, runt₂, m₂', zf₂', g₂'', rd₂', wr₂'⟩ : ∃ t₂,
      runBlock isa [.mov .eax (slot kO), .shift .shr .eax 1, .store (at_ .ebp kO) .eax,
        .alu .test .eax (imm 1)] t₁ = some t₂ ∧
      t₂.mem = t₁.mem.writeW (w64 p.W + BitVec.ofNat 64 kO) (BitVec.ofNat 32 (k / 2)) ∧
      t₂.zf = some (decide (k / 2 % 2 = 0)) ∧
      (∀ r, r ≠ .eax → t₂.gpr r = t₁.gpr r) ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    refine ⟨_, by grun [Et₁.ebp, kt₁, L.aW, Et₁.perm.wR, Et₁.perm.wW], by gmems [kt₁, VG.Proof.AesOcb.X86.shr1_32 hk], ?_,
      fun r h => by gregs [h], by gmems [], by gmems []⟩
    gmems [kt₁, VG.Proof.AesOcb.X86.shr1_32 hk, VG.Proof.AesOcb.X86.even_zf32 (show k / 2 < 2 ^ 32 by omega)]
  refine ⟨t₂, runBlock_app_of runt₁ runt₂, ?_, ?_, ?_, zf₂', fun r h1 h2 h3 => by rw [g₂'' r h1, g₁' r h1 h2 h3],
    by rw [rd₂', rd₁'], by rw [wr₂', wr₁']⟩
  · rw [m₂', m₁']; exact VG.Proof.AesOcb.X86.lNtz_frame (VG.Proof.AesOcb.X86.dblMem_frame _ _ _ _ _) _
  · rw [m₂', VG.Proof.AesOcb.X86.block_writeK, m₁', VG.Proof.AesOcb.X86.dblMem_block]
  · rw [m₂']; simp only [slotv_eq]; gmems []

/-- The head of `lNtz`: `L_0` copied to `W + lO`, `i` to `W + kO`, and ZF
set if `i` is even. -/
theorem lNtzHead_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {i : Nat} (hi' : i < 2 ^ 32)
    (hdi : s.gpr .edi = BitVec.ofNat 32 i) :
    ∃ s₂, runBlock isa (copy16 l0O lO ++ ([.mov .eax (.reg .edi), .store (at_ .ebp kO) .eax, .alu .test .eax (imm 1)] : List Instr))
        s = some s₂ ∧
      Frame (VG.Proof.AesOcb.X86.lNtzR p) s.mem s₂.mem ∧
      blockAtMem s₂.mem (w64 p.W + BitVec.ofNat 64 lO) = blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) ∧
      slotv s₂.mem p.W kO = BitVec.ofNat 32 i ∧ s₂.zf = some (decide (i % 2 = 0)) ∧
      (∀ r, r ≠ .eax → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.copy16_ok L E (s := l0O) (d := lO) (by decide) (by decide) (by decide)
  have E₁ : VG.Proof.AesOcb.X86.Env p s₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (VG.Proof.AesOcb.X86.frame_toMut (by rw [m₁]; exact VG.Proof.AesOcb.X86.copyMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  have hdi₁ : s₁.gpr .edi = BitVec.ofNat 32 i := by rw [g₁ _ (by decide), hdi]
  obtain ⟨s₂, run₂, m₂, k₂, zf₂, g₂, rd₂, wr₂⟩ : ∃ s₂,
      runBlock isa [.mov .eax (.reg .edi), .store (at_ .ebp kO) .eax, .alu .test .eax (imm 1)] s₁ = some s₂ ∧
      s₂.mem = s₁.mem.writeW (w64 p.W + BitVec.ofNat 64 kO) (BitVec.ofNat 32 i) ∧
      slotv s₂.mem p.W kO = BitVec.ofNat 32 i ∧ s₂.zf = some (decide (i % 2 = 0)) ∧
      (∀ r, r ≠ .eax → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by grun [E₁.ebp, hdi₁, L.aW, E₁.perm.wW], by gmems [hdi₁], ?_, ?_, fun r h => by gregs [h],
      by gmems [], by gmems []⟩
    · simp only [slotv_eq]; gmems [hdi₁]
    · gmems [hdi₁, VG.Proof.AesOcb.X86.even_zf32 hi']
  refine ⟨s₂, runBlock_app_of run₁ run₂, ?_, ?_, k₂, zf₂, fun r h => by rw [g₂ r h, g₁ r h], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  · rw [m₂, m₁]; exact VG.Proof.AesOcb.X86.lNtz_frame (VG.Proof.AesOcb.X86.copyMem16_frame _ _ _ _ _) _
  · rw [m₂, VG.Proof.AesOcb.X86.block_writeK, m₁, VG.Proof.AesOcb.X86.copyMem16_block]

theorem lNtz_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {l : Block} {i : Nat} (hi : 0 < i)
    (hi' : i < 2 ^ 32) (hdi : s.gpr .edi = BitVec.ofNat 32 i)
    (hl0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa lNtz s (VG.Proof.AesOcb.X86.LNtzPost p l i s) := by
  obtain ⟨s₂, run₂, fr₂, v₂, k₂, zf₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.lNtzHead_ok L E hi' hdi
  have g₂' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₂.gpr r = s.gpr r := fun r h _ _ => g₂ r h
  rw [hl0] at v₂
  have post_of : ∀ t : State, Frame (VG.Proof.AesOcb.X86.lNtzR p) s.mem t.mem →
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 lO) = lAt l (ntz i) →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) →
      t.rd = s.rd → t.wr = s.wr → VG.Proof.AesOcb.X86.LNtzPost p l i s t := fun t fr v g rd wr => ⟨fr, v, g, rd, wr⟩
  unfold lNtz
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.ite (decide (i % 2 = 0)) (VG.Proof.AesOcb.X86.eval_e zf₂) (fun hb => ?_)
    (fun hb => WP.block_nil (post_of s₂ fr₂ ?_ g₂' rd₂ wr₂))
  rotate_left
  · rw [v₂, Proof.Ocb.ntz_odd (by simpa using hb)]
  have he : i % 2 = 0 := of_decide_eq_true hb
  refine WP.loop (M := isa) (c := .e)
    (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
      ntz i = j + ntz (i / 2 ^ j) ∧ slotv t.mem p.W kO = BitVec.ofNat 32 (i / 2 ^ j) ∧
      Frame (VG.Proof.AesOcb.X86.lNtzR p) s.mem t.mem ∧ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 lO) = lAt l j ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr) ?_ (i / 2 ^ 0) _
    ⟨0, rfl, by simpa using hi, by simpa using he, by simp, by simpa using k₂, fr₂, v₂,
      g₂', rd₂, wr₂⟩
  rintro k t ⟨j, rfl, hpos, hev, hntz, kt, fr, v, g, rd, wr⟩
  have hv : i / 2 ^ j < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
  have Et : VG.Proof.AesOcb.X86.Env p t := E.mut L (by rw [g _ (by decide) (by decide) (by decide), E.ebp])
    (by rw [g _ (by decide) (by decide) (by decide), E.esp]) rd wr (VG.Proof.AesOcb.X86.frame_toMut fr (VG.Proof.AesOcb.X86.inMut_lNtzR p))
  have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  obtain ⟨t₂, runt, frt, vt, kt', zf₂', g₂'', rd₂', wr₂'⟩ := VG.Proof.AesOcb.X86.lNtzStep_ok L Et hv kt
  rw [← e] at kt' zf₂'
  refine WP.of_runBlock ⟨t₂, runt, ?_⟩
  have fr' : Frame (VG.Proof.AesOcb.X86.lNtzR p) s.mem t₂.mem := fr.trans frt
  have v' : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 lO) = lAt l (j + 1) := by
    rw [vt, v]; rfl
  have g' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 => by rw [g₂'' r h1 h2 h3, g r h1 h2 h3]
  have hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
    rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega
  by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
  · right
    refine ⟨(VG.Proof.AesOcb.X86.eval_e zf₂').trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega, j + 1, rfl,
      by rw [e]; omega, hodd, hntz', kt', fr', v', g', by rw [rd₂', rd], by rw [wr₂', wr]⟩
  · left
    refine ⟨(VG.Proof.AesOcb.X86.eval_e zf₂').trans (by simp [hodd]), post_of t₂ fr' ?_ g' (by rw [rd₂', rd])
      (by rw [wr₂', wr])⟩
    rw [v', hntz', Proof.Ocb.ntz_odd (by omega)]

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Setup`. -/
section

/-!
# AES-OCB on x86: `L_$`, `L_0` and the checksum (`setup`)

Untrusted: everything here is checked by Lean. `setup` doubles `L_*` (bytes
240–255 of the key context) to `L_$` at `W + ldO`, doubles that to `L_0` at
`W + l0O`, and zeroes the checksum at `W + ckO` (`setup_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem double lAt lDollar ctxLstar)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq runBlock_app_of)

theorem zero4_fold (m : Mem) (W : BitVec 32) (d : Nat) :
    (((m.writeW (w64 W + BitVec.ofNat 64 d) (BitVec.ofNat 32 0)).writeW (w64 W + BitVec.ofNat 64 (d + 4))
      (BitVec.ofNat 32 0)).writeW (w64 W + BitVec.ofNat 64 (d + 8)) (BitVec.ofNat 32 0)).writeW
      (w64 W + BitVec.ofNat 64 (d + 12)) (BitVec.ofNat 32 0) = Proof.Cmac.zero4 m (w64 W + BitVec.ofNat 64 d) := by
  simp only [Proof.Cmac.zero4, Proof.Cmac.store4, Proof.AesGcm.X86.add_ofNat_assoc]; rfl

/-- A block of `W` below 128, within `wA`. -/
theorem frame_wA {p : VG.Proof.AesOcb.X86.Prm} {d : Nat} (h : d + 16 ≤ 128) {m m' : Mem}
    (hf : Frame [⟨w64 p.W + BitVec.ofNat 64 d, 16⟩] m m') : Frame [VG.Proof.AesOcb.X86.wA p.W] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ h⟩

/-- A zeroed block is zero. -/
theorem blockAtMem_zero4 (m : Mem) (c : Addr) : blockAtMem (Proof.Cmac.zero4 m c) c = 0 := by
  rw [blockAtMem, Proof.Cmac.zero4_bytes]; decide

/-- What `setup` leaves. -/
structure SetupPost (p : VG.Proof.AesOcb.X86.Prm) (s s' : State) : Prop where
  frame : Frame [VG.Proof.AesOcb.X86.wA p.W] s.mem s'.mem
  ld : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K))
  l0 : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (w64 p.K)) 0
  ck : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem setup_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) :
    ∃ s', runBlock isa setup s = some s' ∧ VG.Proof.AesOcb.X86.SetupPost p s s' := by
  obtain ⟨s₁, run₁, m₁, b₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .ebx (slot ctxO)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .ebx = p.K ∧ (∀ r, r ≠ .ebx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    have hc := E.slots.ctx
    simp only [slotv_eq] at hc
    exact ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hc], by gmems [], by gregs [hc], fun r h => by gregs [h],
      by gmems [], by gmems []⟩
  have E₁ : VG.Proof.AesOcb.X86.Env p s₁ := E.keep (by rw [g₁ _ (by decide)]) (by rw [g₁ _ (by decide)]) rd₁ wr₁ m₁
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.dblK_ok L E₁ b₁ (s := 240) (d := ldO) (by decide) (by decide)
  have E₂ : VG.Proof.AesOcb.X86.Env p s₂ := E₁.mut L (by rw [g₂ _ (by decide) (by decide) (by decide), E₁.ebp])
    (by rw [g₂ _ (by decide) (by decide) (by decide), E₁.esp]) rd₂ wr₂
    (VG.Proof.AesOcb.X86.frame_toMut (by rw [m₂]; exact VG.Proof.AesOcb.X86.dblMem_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := VG.Proof.AesOcb.X86.dblW_ok L E₂ (s := ldO) (d := l0O) (by decide) (by decide)
    (.inr (.inl (by decide)))
  have E₃ : VG.Proof.AesOcb.X86.Env p s₃ := E₂.mut L (by rw [g₃ _ (by decide) (by decide) (by decide), E₂.ebp])
    (by rw [g₃ _ (by decide) (by decide) (by decide), E₂.esp]) rd₃ wr₃
    (VG.Proof.AesOcb.X86.frame_toMut (by rw [m₃]; exact VG.Proof.AesOcb.X86.dblMem_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa (zero4 ckO) s₃ = some s₄ ∧
      s₄.mem = Proof.Cmac.zero4 s₃.mem (w64 p.W + BitVec.ofNat 64 ckO) ∧
      (∀ r, r ≠ .eax → s₄.gpr r = s₃.gpr r) ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr :=
    ⟨_, by grun [zero4, E₃.ebp, L.aW, E₃.perm.wW], by gmems []; exact VG.Proof.AesOcb.X86.zero4_fold _ _ _, fun r h => by gregs [h],
      by gmems [], by gmems []⟩
  refine ⟨s₄, runBlock_app_of (runBlock_app_of (runBlock_app_of run₁ run₂) run₃) run₄, ?_⟩
  have f₄ : Frame [VG.Proof.AesOcb.X86.wA p.W] s₃.mem s₄.mem := by rw [m₄]; exact VG.Proof.AesOcb.X86.frame_wA (by decide) (Proof.Cmac.frame_store4 _ _ _ _ _)
  have hd : ∀ {d : Nat}, d + 16 ≤ ckO ∨ ckO + 16 ≤ d → d + 16 ≤ 2560 →
      blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun h h' => by
      rw [m₄]
      exact Proof.Ocb.blockAtMem_frame (Proof.Cmac.frame_store4 _ _ _ _ _) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w h h' (by decide)
  have hld₂ : blockAtMem s₂.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K)) := by
    rw [m₂, VG.Proof.AesOcb.X86.dblMem_block, m₁]; rfl
  have hl0 : blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K)) := by
    rw [m₃, Proof.Ocb.blockAtMem_frame (VG.Proof.AesOcb.X86.dblMem_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (by decide) (by decide) (by decide), hld₂]
  refine ⟨?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · have f₂ : Frame [VG.Proof.AesOcb.X86.wA p.W] s.mem s₂.mem := by
      rw [m₂, m₁]; exact VG.Proof.AesOcb.X86.frame_wA (by decide) (VG.Proof.AesOcb.X86.dblMem_frame _ _ _ _ _)
    have f₃ : Frame [VG.Proof.AesOcb.X86.wA p.W] s₂.mem s₃.mem := by rw [m₃]; exact VG.Proof.AesOcb.X86.frame_wA (by decide) (VG.Proof.AesOcb.X86.dblMem_frame _ _ _ _ _)
    exact (f₂.trans f₃).trans f₄
  · rw [hd (by decide) (by decide), hl0]
  · rw [hd (by decide) (by decide), m₃, VG.Proof.AesOcb.X86.dblMem_block, hld₂]; rfl
  · rw [m₄]; exact VG.Proof.AesOcb.X86.blockAtMem_zero4 _ _
  · rw [g₄ r h₁, g₃ r h₁ h₂ h₃, g₂ r h₁ h₂ h₃, g₁ r h₄]

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.NonceBlock`. -/
section

/-!
# AES-OCB on x86: the block `Nonce` (`nonceBlock`)

Untrusted: everything here is checked by Lean. `nonceBlock` writes `Nonce`
(§4.2) with its last 6 bits cleared to `W + tmpO`, and `bottom` to
`W + botO` (`nonceBlock_ok`): zeros, the nonce copied to the end
(`copyLoop`), the 1 before it, `TAGLEN mod 128` ORed into the first byte,
and the last byte split into `bottom` and the rest. The 16 bytes are
followed as a list through the writes, and compared with `nb`
(`Proof.Ocb.nonceN_masked_byte`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (nonceN nb nbase)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq runBlock_app_of toNat_ofNat32 LoopPre CopyPost copyLoop_ok
  length_bytesAt)
open VG.Proof.AesCcm (bytesAt_writeBytes_at bytesAt_writeW8_at bytesAt_writeW8_base)

theorem or_byte32 (b : Byte) {v : Nat} (hv : v < 256) :
    ((b.setWidth 32 ||| BitVec.ofNat 32 v).setWidth 8 : Byte) = b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := v) (by omega), Nat.mod_eq_of_lt (a := v) (by omega),
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow b.isLt (by omega))

theorem and_byte32 (b : Byte) {v : Nat} (hv : v < 256) :
    ((b.setWidth 32 &&& BitVec.ofNat 32 v).setWidth 8 : Byte) = b &&& BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := v) (by omega), Nat.mod_eq_of_lt (a := v) (by omega),
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left b.isLt)

theorem and63_32 (b : Byte) : b.setWidth 32 &&& BitVec.ofNat 32 63 = BitVec.ofNat 32 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (63 : Nat) % 2 ^ 32 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem and15_32 {t : Nat} (ht : t < 2 ^ 32) : BitVec.ofNat 32 t &&& BitVec.ofNat 32 15 = BitVec.ofNat 32 (t % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat32 ht, toNat_ofNat32 (by decide),
    show (15 : Nat) = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod, toNat_ofNat32 (by omega)]

theorem sub32 (W : BitVec 32) {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    W + BitVec.ofNat 32 a - BitVec.ofNat 32 b = W + BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, toNat_ofNat32 ha, toNat_ofNat32 (by omega),
    toNat_ofNat32 (by omega)]
  have := W.isLt
  omega

theorem contains_pre (p : Addr) {j n : Nat} (h : j ≤ n) : (⟨p, n⟩ : Region).Contains p j := by
  simpa using Offset.contains_base p (d := 0) (n := j) (k := n) (by omega) (by decide)

/-- What `nonceBlock` leaves. -/
structure NoncePost (p : VG.Proof.AesOcb.X86.Prm) (nonce : List Byte) (s s' : State) : Prop where
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 botO, 4⟩] s.mem s'.mem
  blk : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 tmpO) = nonceN p.tl nonce &&& ~~~(63 : Block)
  bot : slotv s'.mem p.W botO = BitVec.ofNat 32 ((nonceN p.tl nonce).extractLsb' 0 6).toNat
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- A copy of `n` bytes into `W + d`, within the first 128 bytes of `W`:
the environment is kept. -/
theorem copyW_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {S : BitVec 32} {d n : Nat} (hd : d + n ≤ 128)
    (lp : LoopPre s S (p.W + BitVec.ofNat 32 d) n) :
    WP isa copyLoop s fun s' => VG.Proof.AesOcb.X86.Env p s' ∧ CopyPost s S (p.W + BitVec.ofNat 32 d) n s' :=
  WP.mono (copyLoop_ok s lp) fun s' P => ⟨E.mut L
    (by rw [P.other _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (by rw [P.other _ (by decide) (by decide) (by decide) (by decide), E.esp]) P.rd P.wr
    (VG.Proof.AesOcb.X86.frame_toMut (rs := [⟨w64 p.W + BitVec.ofNat 64 d, n⟩]) (by
      rw [P.mem, L.aW (by omega)]
      exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _))
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl hd)), P⟩

/-- The head of `nonceBlock`: `W + tmpO` zeroed, the copy's arguments. -/
theorem nonceHead_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) :
    ∃ s₂, runBlock isa (zero4 tmpO ++
      ([.mov .edi (slot nO), .mov .ecx (slot nlO), .mov .edx (.reg .ebp), .alu .add .edx (imm (tmpO + 16)),
        .alu .sub .edx (.reg .ecx)] : List Instr)) s = some s₂ ∧
      VG.Proof.AesOcb.X86.Env p s₂ ∧ LoopPre s₂ p.N (p.W + BitVec.ofNat 32 (128 - p.nl)) p.nl ∧
      s₂.mem = Proof.Cmac.zero4 s.mem (w64 p.W + BitVec.ofNat 64 tmpO) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  have h1 := L.nl1
  have h15 := L.nl15
  have hN := E.slots.nonce
  have hnl := E.slots.nlen
  simp only [slotv_eq] at hN hnl
  have hz := VG.Proof.AesOcb.X86.zero4_fold s.mem p.W tmpO
  obtain ⟨s₂, run₂, m₂, di₂, dx₂, cx₂, g₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa (zero4 tmpO ++
      ([.mov .edi (slot nO), .mov .ecx (slot nlO), .mov .edx (.reg .ebp), .alu .add .edx (imm (tmpO + 16)),
        .alu .sub .edx (.reg .ecx)] : List Instr)) s = some s₂ ∧
      s₂.mem = Proof.Cmac.zero4 s.mem (w64 p.W + BitVec.ofNat 64 tmpO) ∧ s₂.gpr .edi = p.N ∧
      s₂.gpr .edx = p.W + BitVec.ofNat 32 (128 - p.nl) ∧ s₂.gpr .ecx = BitVec.ofNat 32 p.nl ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by grun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hN, hnl], by gmems [hz], by gregs [hN],
      ?_, by gregs [hnl], fun r h₁ h₂ h₃ h₄ => by gregs [h₁, h₂, h₃, h₄], by gmems [], by gmems []⟩
    gregs [hnl, E.ebp]
    exact VG.Proof.AesOcb.X86.sub32 _ (by omega) (by decide)
  have a128 : w64 (p.W + BitVec.ofNat 32 (128 - p.nl)) = w64 p.W + BitVec.ofNat 64 (128 - p.nl) := L.aW (by omega)
  have fr₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] s.mem s₂.mem := by
    rw [m₂]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine ⟨s₂, run₂, E.mut L (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd₂ wr₂
    (VG.Proof.AesOcb.X86.frame_toMut fr₂ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))),
    ⟨di₂, dx₂, cx₂, h1, by omega, L.nw, by rw [L.nW (by omega)]; have := L.ww; omega,
      by rw [rd₂, wr₂]; exact E.perm.non, by rw [a128, wr₂]; exact E.perm.wC (by omega),
      by rw [a128]; exact L.n_w' (by omega)⟩, m₂, g₂, rd₂, wr₂⟩

theorem nonceBlock_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) :
    WP isa nonceBlock s (VG.Proof.AesOcb.X86.NoncePost p (bytesAt s.mem (w64 p.N) p.nl) s) := by
  have h1 := L.nl1
  have h15 := L.nl15
  obtain ⟨s₂, run₂, -, lp, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.nonceHead_ok L E
  have a128 : w64 (p.W + BitVec.ofNat 32 (128 - p.nl)) = w64 p.W + BitVec.ofNat 64 (128 - p.nl) := L.aW (by omega)
  have fr₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] s.mem s₂.mem := by
    rw [m₂]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have eN : bytesAt s₂.mem (w64 p.N) p.nl = bytesAt s.mem (w64 p.N) p.nl :=
    Proof.AesGcm.X86.bytesAt_frame fr₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.n_w' (by decide)) (by omega)
  unfold nonceBlock
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ P₃ => ?_)
  have m₃ := P₃.mem
  rw [eN, a128] at m₃
  have E₃ : VG.Proof.AesOcb.X86.Env p s₃ := E.mut L (by rw [P₃.other _ (by decide) (by decide) (by decide) (by decide),
                          g₂ _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (by rw [P₃.other _ (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide) (by decide) (by decide), E.esp]) (by rw [P₃.rd, rd₂]) (by rw [P₃.wr, wr₂])
    (VG.Proof.AesOcb.X86.frame_toMut (rs := [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩]) (by
      refine fr₂.trans ?_
      rw [m₃]
      exact writeBytes_frame _ _ _ (by
        rw [length_bytesAt]
        exact Offset.contains (w64 p.W) (d := 128 - p.nl) (n := p.nl) (e := 112) (k := 16) (by omega) (by omega)
          (by decide)))
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  have hnl₃ := E₃.slots.nlen
  have htl₃ := E₃.slots.tlen
  simp only [slotv_eq] at hnl₃ htl₃
  have hsub : p.W + BitVec.ofNat 32 127 - BitVec.ofNat 32 p.nl = p.W + BitVec.ofNat 32 (127 - p.nl) :=
    VG.Proof.AesOcb.X86.sub32 _ (by omega) (by decide)
  have a127 : w64 (p.W + BitVec.ofNat 32 (127 - p.nl) + BitVec.ofNat 32 0) = w64 p.W + BitVec.ofNat 64 (127 - p.nl) := by
    rw [show p.W + BitVec.ofNat 32 (127 - p.nl) + BitVec.ofNat 32 0 = p.W + BitVec.ofNat 32 (127 - p.nl) from
      BitVec.add_zero _]
    exact L.aW (by omega)
  have w127 : InRegions s₃.wr (w64 p.W + BitVec.ofNat 64 (127 - p.nl)) 1 := E₃.perm.wW (by omega)
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa [.mov .ecx (slot nlO), .mov .edx (.reg .ebp),
      .alu .add .edx (imm (tmpO + 15)), .alu .sub .edx (.reg .ecx), .mov .eax (imm 1), .store8 (at_ .edx 0) .al] s₃ =
        some s₄ ∧
      s₄.mem = s₃.mem.writeW (w64 p.W + BitVec.ofNat 64 (127 - p.nl)) (1 : Byte) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₄.gpr r = s₃.gpr r) ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by grun [E₃.ebp, L.aW, E₃.perm.wR, hnl₃, hsub, a127, w127], ?_,
      fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
    gmems [E₃.ebp, hnl₃, hsub, a127]; rfl
  have E₄ : VG.Proof.AesOcb.X86.Env p s₄ := E₃.mut L (by rw [g₄ _ (by decide) (by decide) (by decide), E₃.ebp])
    (by rw [g₄ _ (by decide) (by decide) (by decide), E₃.esp]) rd₄ wr₄
    (VG.Proof.AesOcb.X86.frame_toMut (rs := [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩]) (by
      rw [m₄]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains (w64 p.W) (d := 127 - p.nl) (n := 1) (e := 112) (k := 16) (by omega) (by omega)
          (by decide)))
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  have htl₄ := E₄.slots.tlen
  simp only [slotv_eq] at htl₄
  have ht : p.tl < 2 ^ 32 := by have := L.tl16; omega
  have d2 : ∀ a : Nat, BitVec.ofNat 32 a + BitVec.ofNat 32 a = BitVec.ofNat 32 (2 * a) := fun a => by
    rw [← BitVec.ofNat_add, Nat.two_mul]
  obtain ⟨s₅, run₅, ax₅, g₅, m₅, rd₅, wr₅⟩ : ∃ s₅, runBlock isa [.mov .eax (slot tlO), .alu .and .eax (imm 15),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .eax)] s₄ = some s₅ ∧ s₅.gpr .eax = BitVec.ofNat 32 (16 * (p.tl % 16)) ∧
      (∀ r, r ≠ .eax → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by grun [E₄.ebp, L.aW, E₄.perm.wR, htl₄], ?_, fun r h => by gregs [h], by gmems [], by gmems [],
      by gmems []⟩
    gregs [htl₄, VG.Proof.AesOcb.X86.and15_32 ht, d2]
    congr 1; omega
  have E₅ : VG.Proof.AesOcb.X86.Env p s₅ := E₄.keep (by rw [g₅ _ (by decide)]) (by rw [g₅ _ (by decide)]) rd₅ wr₅ m₅
  obtain ⟨s₆, run₆, m₆, g₆, rd₆, wr₆⟩ : ∃ s₆, runBlock isa [.movzx8 .ecx (at_ .ebp tmpO), .alu .or .ecx (.reg .eax),
      .store8 (at_ .ebp tmpO) .cl] s₅ = some s₆ ∧
      s₆.mem = s₅.mem.writeW (w64 p.W + BitVec.ofNat 64 112)
        (s₅.mem (w64 p.W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (p.tl % 16))) ∧
      (∀ r, r ≠ .ecx → s₆.gpr r = s₅.gpr r) ∧ s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr := by
    refine ⟨_, by grun [E₅.ebp, L.aW, E₅.perm.wR, E₅.perm.wW], ?_, fun r h => by gregs [h], by gmems [],
      by gmems []⟩
    gmems [ax₅, VG.Proof.AesOcb.X86.or_byte32 _ (show 16 * (p.tl % 16) < 256 by omega)]
  have E₆ : VG.Proof.AesOcb.X86.Env p s₆ := E₅.mut L (by rw [g₆ _ (by decide), E₅.ebp]) (by rw [g₆ _ (by decide), E₅.esp]) rd₆ wr₆
    (VG.Proof.AesOcb.X86.frame_toMut (rs := [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩]) (by
      rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.AesOcb.X86.contains_pre _ (by decide)))
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  obtain ⟨s₇, run₇, m₇, g₇, rd₇, wr₇⟩ : ∃ s₇, runBlock isa [.movzx8 .eax (at_ .ebp (tmpO + 15)),
      .mov .ecx (.reg .eax), .alu .and .ecx (imm 63), .store (at_ .ebp botO) .ecx, .alu .and .eax (imm 0xc0),
      .store8 (at_ .ebp (tmpO + 15)) .al] s₆ = some s₇ ∧
      s₇.mem = (s₆.mem.writeW (w64 p.W + BitVec.ofNat 64 botO)
          (BitVec.ofNat 32 ((s₆.mem (w64 p.W + BitVec.ofNat 64 127)).toNat % 64))).writeW
            (w64 p.W + BitVec.ofNat 64 127) (s₆.mem (w64 p.W + BitVec.ofNat 64 127) &&& BitVec.ofNat 8 192) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s₇.gpr r = s₆.gpr r) ∧ s₇.rd = s₆.rd ∧ s₇.wr = s₆.wr := by
    refine ⟨_, by grun [E₆.ebp, L.aW, E₆.perm.wR, E₆.perm.wW], ?_, fun r h₁ h₂ => by gregs [h₁, h₂], by gmems [],
      by gmems []⟩
    gmems [VG.Proof.AesOcb.X86.and63_32, VG.Proof.AesOcb.X86.and_byte32 _ (show 192 < 256 by decide)]
  -- the bytes at `W + tmpO`, step by step
  have hlen : (bytesAt s.mem (w64 p.N) p.nl).length = p.nl := length_bytesAt _ _ _
  have L₂ : bytesAt s₂.mem (w64 p.W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros 16 := by
    rw [m₂, Proof.Cmac.zero4_bytes]; rfl
  have e128 : w64 p.W + BitVec.ofNat 64 (128 - p.nl) =
      w64 p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (16 - p.nl) := by
    rw [Offset.add_add, show 112 + (16 - p.nl) = 128 - p.nl by omega]
  have e127 : w64 p.W + BitVec.ofNat 64 (127 - p.nl) =
      w64 p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - p.nl) := by
    rw [Offset.add_add, show 112 + (15 - p.nl) = 127 - p.nl by omega]
  have L₃ : bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 112) 16 =
      Spec.Ocb.zeros (16 - p.nl) ++ bytesAt s.mem (w64 p.N) p.nl := by
    rw [m₃, e128, bytesAt_writeBytes_at _ _ _ (by rw [hlen]; omega) (by decide), L₂, hlen]
    rw [show 16 - p.nl + p.nl = 16 by omega]
    simp only [Spec.Ocb.zeros, List.take_replicate, List.drop_replicate,
      show min (16 - p.nl) 16 = 16 - p.nl by omega, Nat.sub_self, List.replicate_zero, List.append_nil]
  have L₄ : bytesAt s₄.mem (w64 p.W + BitVec.ofNat 64 112) 16 =
      Spec.Ocb.zeros (15 - p.nl) ++ [1] ++ bytesAt s.mem (w64 p.N) p.nl := by
    rw [m₄, e127, bytesAt_writeW8_at _ _ _ (by omega) (by decide), L₃]
    simp only [Spec.Ocb.zeros, List.take_append, List.take_replicate, List.drop_append, List.drop_replicate,
      List.length_replicate, show min (15 - p.nl) (16 - p.nl) = 15 - p.nl by omega,
      show 15 - p.nl - (16 - p.nl) = 0 by omega, show 16 - p.nl - (15 - p.nl + 1) = 0 by omega,
      show 15 - p.nl + 1 - (16 - p.nl) = 0 by omega, List.take_zero, List.drop_zero, List.replicate_zero,
      List.nil_append, List.append_nil, List.append_assoc]
  have L₄d : ∀ k < 16, (bytesAt s₄.mem (w64 p.W + BitVec.ofNat 64 112) 16).getD k 0 =
      nbase (bytesAt s.mem (w64 p.N) p.nl) k := fun k hk => by
    have := Proof.Ocb.nbase_list (bytesAt s.mem (w64 p.N) p.nl) (by rw [hlen]; omega) (by rw [hlen]; omega) hk
    rw [hlen] at this; rw [L₄]; exact this
  have e127' : w64 p.W + BitVec.ofNat 64 127 = w64 p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 15 :=
    (Offset.add_add _ 112 15).symm
  have h0 : w64 p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 0 = w64 p.W + BitVec.ofNat 64 112 := BitVec.add_zero _
  have b0e : s₅.mem (w64 p.W + BitVec.ofNat 64 112) = nbase (bytesAt s.mem (w64 p.N) p.nl) 0 := by
    have := Proof.Ocb.getD_bytesAt_eq s₄.mem (w64 p.W + BitVec.ofNat 64 112) (k := 0) (n := 16) (by decide)
    rw [h0] at this
    rw [m₅, this, L₄d 0 (by decide)]
  have L₆d : ∀ k < 16, (bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 112) 16).getD k 0 =
      nb p.tl (bytesAt s.mem (w64 p.N) p.nl) k := by
    intro k hk
    rw [m₆, bytesAt_writeW8_base _ _ _ (by decide) (by decide), b0e, m₅]
    unfold nb
    rcases k with _ | k
    · rfl
    · simp only [List.getD_cons_succ, show k + 1 ≠ 0 by omega, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
        show 1 + k = k + 1 by omega]
      exact L₄d (k + 1) hk
  have b15e : s₆.mem (w64 p.W + BitVec.ofNat 64 127) = nb p.tl (bytesAt s.mem (w64 p.N) p.nl) 15 := by
    rw [e127', Proof.Ocb.getD_bytesAt_eq s₆.mem (w64 p.W + BitVec.ofNat 64 112) (k := 15) (n := 16) (by decide),
      L₆d 15 (by decide)]
  have frb : ∀ v : BitVec 32,
      Frame [⟨w64 p.W + BitVec.ofNat 64 botO, 4⟩] s₆.mem (s₆.mem.writeW (w64 p.W + BitVec.ofNat 64 botO) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have L₇d : ∀ k < 16, (bytesAt s₇.mem (w64 p.W + BitVec.ofNat 64 112) 16).getD k 0 =
      if k = 15 then nb p.tl (bytesAt s.mem (w64 p.N) p.nl) 15 &&& 0xc0
      else nb p.tl (bytesAt s.mem (w64 p.N) p.nl) k := by
    intro k hk
    generalize hb : s₆.mem (w64 p.W + BitVec.ofNat 64 127) = b at m₇ b15e
    rw [m₇, e127', bytesAt_writeW8_at _ _ (o := 15) (n := 16) _ (by decide) (by decide),
      Proof.AesGcm.X86.bytesAt_frame (frb _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (a := 112) (n := 16) (d := botO) (k := 4) (.inl (by decide)) (by decide) (by decide))
        (by decide),
      Proof.Ocb.getD_set16 _ (length_bytesAt _ _ _) (by decide) _ hk, b15e]
    split
    · rfl
    · exact L₆d k hk
  have hlen16 := length_bytesAt s₇.mem (w64 p.W + BitVec.ofNat 64 112) 16
  refine WP.of_runBlock ⟨s₇, runBlock_app_of run₄ (runBlock_app_of run₅ (runBlock_app_of run₆ run₇)), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- the frame
    have F₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 botO, 4⟩] s.mem s₃.mem :=
      (fr₂.mono (fun r hr => by simp at hr; simp [hr])).trans (by
        rw [m₃]
        refine (writeBytes_frame _ _ _ (R := ⟨w64 p.W + BitVec.ofNat 64 112, 16⟩) ?_).mono
          (fun r hr => by simp at hr; simp [hr])
        rw [length_bytesAt, e128]; exact Offset.contains_base _ (by omega) (by omega))
    rw [m₇, m₆, m₅, m₄]
    refine (((F₃.writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_self ..) _ ?_).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ ?_).writeW (List.mem_cons_self ..) _ ?_
    · rw [e127]; exact Offset.contains_base _ (by omega) (by omega)
    · exact VG.Proof.AesOcb.X86.contains_pre _ (by decide)
    · exact Region.contains_self _ _
    · rw [e127']; exact Offset.contains_base _ (by decide) (by decide)
  · -- the block
    show blockAtMem s₇.mem (w64 p.W + BitVec.ofNat 64 112) = _
    rw [blockAtMem]
    apply Proof.Ocb.toBytes_inj
    rw [Proof.Ocb.toBytes_ofBytes hlen16]
    refine Proof.Cmac.ext16 hlen16 (Proof.Ocb.toBytes_length _) fun k hk => ?_
    rw [L₇d k hk, Proof.Ocb.nonceN_masked_byte _ _ (by omega) (by omega) hk]
  · -- `bottom`
    rw [slotv_eq, m₇, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, b15e, Proof.Ocb.nonceN_bottom _ _ (by omega) (by omega)]
  · intro r h1 h2 h3 h4
    rw [g₇ r h1 h2, g₆ r h2, g₅ r h1, g₄ r h1 h2 h3, P₃.other r h1 h4 h3 h2, g₂ r h1 h2 h3 h4]
  · rw [rd₇, rd₆, rd₅, rd₄, P₃.rd, rd₂]
  · rw [wr₇, wr₆, wr₅, wr₄, P₃.wr, wr₂]

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Offset0`. -/
section

/-!
# AES-OCB on x86: `Offset_0` (`offset0`)

Untrusted: everything here is checked by Lean. `offset0` stores `Ktop` as
four byte-reversed words at `W + stO`, and the two words of `Stretch`'s
tail after them (`stretch_ok`, `Proof.Ocb.stretch_words32`): `Stretch` as
six words (`stv`). Six masked stages shift them left by `bottom`
(`stage_ok`, `stage32_ok`, `Proof.Ocb.shl_stages`), and the top four,
byte-reversed, are stored to `W + ofsO` and `W + o0O` (`offset0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (shlIf cat6 shlW shl6 shl6_32 ror_mask32 sel_mask32 bit_bottom32 stretch_words32)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq runBlock_app_of readW_writeW_off)

/-- The six words at `W + stO`, the most significant first. -/
def stv (m : Mem) (W : BitVec 32) : BitVec 192 :=
  cat6 (slotv m W 240) (slotv m W 244) (slotv m W 248) (slotv m W 252) (slotv m W 256) (slotv m W 260)

/-- Six words stored at `W + stO`. -/
def put6 (m : Mem) (W : BitVec 32) (y0 y1 y2 y3 y4 y5 : BitVec 32) : Mem :=
  (((((m.writeW (w64 W + BitVec.ofNat 64 240) y0).writeW (w64 W + BitVec.ofNat 64 244) y1).writeW
    (w64 W + BitVec.ofNat 64 248) y2).writeW (w64 W + BitVec.ofNat 64 252) y3).writeW
    (w64 W + BitVec.ofNat 64 256) y4).writeW (w64 W + BitVec.ofNat 64 260) y5

theorem stv_put6 (m : Mem) (W : BitVec 32) (y0 y1 y2 y3 y4 y5 : BitVec 32) :
    VG.Proof.AesOcb.X86.stv (VG.Proof.AesOcb.X86.put6 m W y0 y1 y2 y3 y4 y5) W = cat6 y0 y1 y2 y3 y4 y5 := by
  simp (disch := first | decide | omega) only [VG.Proof.AesOcb.X86.stv, VG.Proof.AesOcb.X86.put6, slotv_eq, Mem.readW_writeW_self32, readW_writeW_off]

theorem frame_put6 (m : Mem) (W : BitVec 32) (y0 y1 y2 y3 y4 y5 : BitVec 32) :
    Frame [⟨w64 W + BitVec.ofNat 64 stO, 24⟩] m (VG.Proof.AesOcb.X86.put6 m W y0 y1 y2 y3 y4 y5) := by
  have c : ∀ d, 240 ≤ d → d + 4 ≤ 264 →
      (⟨w64 W + BitVec.ofNat 64 stO, 24⟩ : Region).Contains (w64 W + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ =>
    Offset.contains (w64 W) (e := 240) (k := 24) (d := d) (n := 4) (by omega) (by omega) (by decide)
  have hm := List.mem_singleton_self (⟨w64 W + BitVec.ofNat 64 stO, 24⟩ : Region)
  exact (((((((Frame.refl _ m).writeW hm _ (c 240 (by decide) (by decide))).writeW hm _ (c 244 (by decide)
    (by decide))).writeW hm _ (c 248 (by decide) (by decide))).writeW hm _ (c 252 (by decide)
    (by decide))).writeW hm _ (c 256 (by decide) (by decide))).writeW hm _ (c 260 (by decide) (by decide)))

/-- The mask of a stage: all ones if bit `k` of `bottom` is set. -/
theorem stageMask_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {k v : Nat} (hk : k < 6) (hv : v < 64)
    (hb : slotv s.mem p.W botO = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa (stageMask k) s = some s' ∧
      s'.gpr .ebx = (0 : BitVec 32) - (if v.testBit k then 1 else 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [slotv_eq] at hb
  by_cases hk0 : k = 0
  · subst hk0
    have := bit_bottom32 hv 0
    rw [BitVec.ushiftRight_zero] at this
    refine ⟨_, by grun [stageMask, E.ebp, L.aW, E.perm.wR, hb], ?_, fun r h₁ h₂ => by gregs [h₁, h₂], by gmems [],
      by gmems [], by gmems []⟩
    gregs [hb]
    rw [← this]; rfl
  · have := bit_bottom32 hv k
    have ck : 1 ≤ k ∧ k ≤ 31 := ⟨by omega, by omega⟩
    refine ⟨_, by grun [stageMask, hk0, ck, E.ebp, L.aW, E.perm.wR, hb], ?_, fun r h₁ h₂ => by gregs [h₁, h₂],
      by gmems [], by gmems [], by gmems []⟩
    gregs [hb]
    rw [← this]; rfl

/-- Word `j` of a stage: shifted if `b`. -/
abbrev selW' (b : Bool) (x x' : BitVec 32) : BitVec 32 := if b then x' else x

/-- Word `j < 5` of a stage, with the mask in `ebx`. -/
theorem stageW_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {a j : Nat} {b : Bool} (ha : 0 < a)
    (ha' : a < 32) (hj : j < 5) (hbx : t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0)) :
    ∃ t', runBlock isa (stageW a j) t = some t' ∧
      t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 (240 + 4 * j))
        (VG.Proof.AesOcb.X86.selW' b (slotv t.mem p.W (240 + 4 * j)) (shlW a (slotv t.mem p.W (240 + 4 * j))
          (slotv t.mem p.W (240 + 4 * j + 4)))) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have c1 : 1 ≤ 32 - a ∧ 32 - a ≤ 31 := ⟨by omega, by omega⟩
  refine ⟨_, by grun [stageW, shlEcx, selW, c1, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_,
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [hbx, ror_mask32 _ ha ha', sel_mask32, slotv_eq]

/-- The last word of a stage: `x5 << a`. -/
theorem stageL_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {a : Nat} {b : Bool} (ha : 0 < a)
    (ha' : a < 32) (hbx : t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0)) :
    ∃ t', runBlock isa (([.mov .eax (slot (stO + 20)), .mov .ecx (.reg .eax)] : List Instr) ++ shlEcx a ++ selW 5) t = some t' ∧
      t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 260)
        (VG.Proof.AesOcb.X86.selW' b (slotv t.mem p.W 260) (slotv t.mem p.W 260 <<< a)) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have c1 : 1 ≤ 32 - a ∧ 32 - a ≤ 31 := ⟨by omega, by omega⟩
  refine ⟨_, by grun [shlEcx, selW, c1, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_,
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [hbx, ror_mask32 _ ha ha', sel_mask32, slotv_eq]

/-- Word `j < 5` of the last stage: the next word. -/
theorem stage32W_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {j : Nat} {b : Bool} (hj : j < 5)
    (hbx : t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0)) :
    ∃ t', runBlock isa (stage32W j) t = some t' ∧
      t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 (240 + 4 * j))
        (VG.Proof.AesOcb.X86.selW' b (slotv t.mem p.W (240 + 4 * j)) (slotv t.mem p.W (240 + 4 * j + 4))) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [stage32W, selW, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_,
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [hbx, sel_mask32, slotv_eq]

/-- The last word of the last stage: zero. -/
theorem stage32L_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {b : Bool}
    (hbx : t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0)) :
    ∃ t', runBlock isa (([.mov .eax (slot (stO + 20)), .mov .ecx (imm 0)] : List Instr) ++ selW 5) t = some t' ∧
      t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 260) (VG.Proof.AesOcb.X86.selW' b (slotv t.mem p.W 260) 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [selW, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_,
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [hbx, sel_mask32, slotv_eq]; rfl

/-- A word of `W + stO` written. -/
theorem frame_st {p : VG.Proof.AesOcb.X86.Prm} {m m' : Mem} (hf : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] m m') {d : Nat}
    (h₁ : 240 ≤ d) (h₂ : d + 4 ≤ 264) (v : BitVec 32) :
    Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] m (m'.writeW (w64 p.W + BitVec.ofNat 64 d) v) :=
  hf.writeW (List.mem_singleton_self _) v
    (Offset.contains (w64 p.W) (e := 240) (k := 24) (d := d) (n := 4) (by omega) (by omega) (by decide))

/-- A word of `W` after a word written: the value written, or the word before. -/
theorem slot_upd {m m' : Mem} {W : BitVec 32} {d : Nat} {v : BitVec 32}
    (h : m' = m.writeW (w64 W + BitVec.ofNat 64 d) v) (o : Nat) (hs : o = d ∨ o + 4 ≤ d ∨ d + 4 ≤ o)
    (ho : o < 2 ^ 32) (hd : d < 2 ^ 32) : slotv m' W o = if o = d then v else slotv m W o := by
  subst h
  rw [slotv_eq, slotv_eq]
  rcases hs with rfl | hs
  · simp only [↓reduceIte, Mem.readW_writeW_self32]
  · rw [ite_eq_right_of_eq_false _ _ (by simp only [eq_iff_iff, iff_false]; omega)]; exact readW_writeW_off _ _ _ hs ho hd

/-- What a stage leaves. -/
structure StagePost (p : VG.Proof.AesOcb.X86.Prm) (b : Bool) (f : BitVec 192 → BitVec 192) (s s' : State) : Prop where
  val : VG.Proof.AesOcb.X86.stv s'.mem p.W = (if b then f (VG.Proof.AesOcb.X86.stv s.mem p.W) else VG.Proof.AesOcb.X86.stv s.mem p.W)
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem s'.mem
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The words of a stage, run one after another from the mask. -/
theorem stage_words {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {b : Bool}
    (hbx : s.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0)) (w : Nat → List Instr) (last : List Instr)
    (f : BitVec 32 → BitVec 32 → BitVec 32) (fl : BitVec 32 → BitVec 32)
    (hw : ∀ {t : State} {j : Nat}, VG.Proof.AesOcb.X86.Env p t → j < 5 → t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0) →
      ∃ t', runBlock isa (w j) t = some t' ∧
        t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 (240 + 4 * j))
          (VG.Proof.AesOcb.X86.selW' b (slotv t.mem p.W (240 + 4 * j)) (f (slotv t.mem p.W (240 + 4 * j))
            (slotv t.mem p.W (240 + 4 * j + 4)))) ∧
        (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr)
    (hl : ∀ {t : State}, VG.Proof.AesOcb.X86.Env p t → t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0) →
      ∃ t', runBlock isa last t = some t' ∧
        t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 260) (VG.Proof.AesOcb.X86.selW' b (slotv t.mem p.W 260) (fl (slotv t.mem p.W 260))) ∧
        (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr) :
    ∃ s', runBlock isa (w 0 ++ w 1 ++ w 2 ++ w 3 ++ w 4 ++ last) s = some s' ∧
      VG.Proof.AesOcb.X86.stv s'.mem p.W = (if b then
        cat6 (f (slotv s.mem p.W 240) (slotv s.mem p.W 244)) (f (slotv s.mem p.W 244) (slotv s.mem p.W 248))
          (f (slotv s.mem p.W 248) (slotv s.mem p.W 252)) (f (slotv s.mem p.W 252) (slotv s.mem p.W 256))
          (f (slotv s.mem p.W 256) (slotv s.mem p.W 260)) (fl (slotv s.mem p.W 260))
        else VG.Proof.AesOcb.X86.stv s.mem p.W) ∧
      Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have step : ∀ {t t' : State}, VG.Proof.AesOcb.X86.Env p t → (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) →
      t'.rd = t.rd → t'.wr = t.wr → (∃ d, 240 ≤ d ∧ d + 4 ≤ 264 ∧ ∃ v : BitVec 32,
        t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 d) v) → VG.Proof.AesOcb.X86.Env p t' := fun Et g rd wr ⟨d, h₁, h₂, v, hm⟩ =>
    Et.mut L (by rw [g _ (by decide) (by decide) (by decide), Et.ebp])
      (by rw [g _ (by decide) (by decide) (by decide), Et.esp]) rd wr
      (VG.Proof.AesOcb.X86.frame_toMut (rs := [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩]) (by rw [hm]; exact VG.Proof.AesOcb.X86.frame_st (Frame.refl _ _) h₁ h₂ v)
        fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have bx : ∀ {t t' : State}, (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) →
      t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0) → t'.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0) :=
    fun g h => by rw [g _ (by decide) (by decide) (by decide), h]
  obtain ⟨t₁, r₁, m₁, g₁, rd₁, wr₁⟩ := hw E (j := 0) (by decide) hbx
  have E₁ := step E g₁ rd₁ wr₁ ⟨_, by decide, by decide, _, m₁⟩
  obtain ⟨t₂, r₂, m₂, g₂, rd₂, wr₂⟩ := hw E₁ (j := 1) (by decide) (bx g₁ hbx)
  have E₂ := step E₁ g₂ rd₂ wr₂ ⟨_, by decide, by decide, _, m₂⟩
  obtain ⟨t₃, r₃, m₃, g₃, rd₃, wr₃⟩ := hw E₂ (j := 2) (by decide) (bx g₂ (bx g₁ hbx))
  have E₃ := step E₂ g₃ rd₃ wr₃ ⟨_, by decide, by decide, _, m₃⟩
  obtain ⟨t₄, r₄, m₄, g₄, rd₄, wr₄⟩ := hw E₃ (j := 3) (by decide) (bx g₃ (bx g₂ (bx g₁ hbx)))
  have E₄ := step E₃ g₄ rd₄ wr₄ ⟨_, by decide, by decide, _, m₄⟩
  obtain ⟨t₅, r₅, m₅, g₅, rd₅, wr₅⟩ := hw E₄ (j := 4) (by decide) (bx g₄ (bx g₃ (bx g₂ (bx g₁ hbx))))
  have E₅ := step E₄ g₅ rd₅ wr₅ ⟨_, by decide, by decide, _, m₅⟩
  obtain ⟨t₆, r₆, m₆, g₆, rd₆, wr₆⟩ := hl E₅ (bx g₅ (bx g₄ (bx g₃ (bx g₂ (bx g₁ hbx)))))
  refine ⟨t₆, runBlock_app_of (runBlock_app_of (runBlock_app_of (runBlock_app_of (runBlock_app_of r₁ r₂) r₃) r₄) r₅) r₆,
    ?_, ?_, fun r h₁ h₂ h₃ => by rw [g₆ r h₁ h₂ h₃, g₅ r h₁ h₂ h₃, g₄ r h₁ h₂ h₃, g₃ r h₁ h₂ h₃, g₂ r h₁ h₂ h₃,
      g₁ r h₁ h₂ h₃], by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · simp only [Nat.reduceMul, Nat.reduceAdd] at m₁ m₂ m₃ m₄ m₅
    rw [VG.Proof.AesOcb.X86.stv]
    simp (disch := decide) only [VG.Proof.AesOcb.X86.slot_upd m₆, VG.Proof.AesOcb.X86.slot_upd m₅, VG.Proof.AesOcb.X86.slot_upd m₄, VG.Proof.AesOcb.X86.slot_upd m₃, VG.Proof.AesOcb.X86.slot_upd m₂,
      VG.Proof.AesOcb.X86.slot_upd m₁, Nat.reduceEqDiff, ↓reduceIte]
    cases b <;> rfl
  · simp only [Nat.reduceMul, Nat.reduceAdd] at m₁ m₂ m₃ m₄ m₅
    have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem t₁.mem := by
      rw [m₁]; exact VG.Proof.AesOcb.X86.frame_st (Frame.refl _ _) (by decide) (by decide) _
    have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem t₂.mem := by
      rw [m₂]; exact VG.Proof.AesOcb.X86.frame_st f₁ (by decide) (by decide) _
    have f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem t₃.mem := by
      rw [m₃]; exact VG.Proof.AesOcb.X86.frame_st f₂ (by decide) (by decide) _
    have f₄ : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem t₄.mem := by
      rw [m₄]; exact VG.Proof.AesOcb.X86.frame_st f₃ (by decide) (by decide) _
    have f₅ : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem t₅.mem := by
      rw [m₅]; exact VG.Proof.AesOcb.X86.frame_st f₄ (by decide) (by decide) _
    rw [m₆]; exact VG.Proof.AesOcb.X86.frame_st f₅ (by decide) (by decide) _

/-- One stage: the six words shifted left by `a` if bit `k` of `bottom` is set. -/
theorem stage_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {k a v : Nat} (hk : k < 6) (ha : 0 < a)
    (ha' : a < 32) (hv : v < 64) (hb : slotv s.mem p.W botO = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa (stage k a) s = some s' ∧ VG.Proof.AesOcb.X86.StagePost p (v.testBit k) (· <<< a) s s' := by
  obtain ⟨s₁, run₁, bx₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.stageMask_ok L E hk hv hb
  have E₁ : VG.Proof.AesOcb.X86.Env p s₁ := E.keep (by rw [g₁ _ (by decide) (by decide)]) (by rw [g₁ _ (by decide) (by decide)]) rd₁ wr₁ m₁
  obtain ⟨s', run', v', f', g', rd', wr'⟩ := VG.Proof.AesOcb.X86.stage_words L E₁ bx₁ (stageW a)
    (([.mov .eax (slot (stO + 20)), .mov .ecx (.reg .eax)] : List Instr) ++ shlEcx a ++ selW 5) (shlW a) (· <<< a)
    (fun Et hj hbx => VG.Proof.AesOcb.X86.stageW_ok L Et ha ha' hj hbx) (fun Et hbx => VG.Proof.AesOcb.X86.stageL_ok L Et ha ha' hbx)
  refine ⟨s', ?_, ⟨?_, by rw [← m₁]; exact f', fun r h₁ h₂ h₃ h₄ => by rw [g' r h₁ h₃ h₄, g₁ r h₁ h₂],
    by rw [rd', rd₁], by rw [wr', wr₁]⟩⟩
  · rw [show stage k a = stageMask k ++ (stageW a 0 ++ stageW a 1 ++ stageW a 2 ++ stageW a 3 ++ stageW a 4 ++
      (([.mov .eax (slot (stO + 20)), .mov .ecx (.reg .eax)] : List Instr) ++ shlEcx a ++ selW 5)) by simp [stage]]
    exact runBlock_app_of run₁ run'
  · rw [v', m₁]
    split
    · exact shl6 _ _ _ _ _ _ ha ha'
    · rfl

/-- The last stage: the six words shifted left by 32 if bit 5 of `bottom` is set. -/
theorem stage32_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {v : Nat} (hv : v < 64)
    (hb : slotv s.mem p.W botO = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa stage32 s = some s' ∧ VG.Proof.AesOcb.X86.StagePost p (v.testBit 5) (· <<< 32) s s' := by
  obtain ⟨s₁, run₁, bx₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.stageMask_ok L E (k := 5) (by decide) hv hb
  have E₁ : VG.Proof.AesOcb.X86.Env p s₁ := E.keep (by rw [g₁ _ (by decide) (by decide)]) (by rw [g₁ _ (by decide) (by decide)]) rd₁ wr₁ m₁
  obtain ⟨s', run', v', f', g', rd', wr'⟩ := VG.Proof.AesOcb.X86.stage_words L E₁ bx₁ stage32W
    (([.mov .eax (slot (stO + 20)), .mov .ecx (imm 0)] : List Instr) ++ selW 5) (fun _ y => y) (fun _ => 0)
    (fun Et hj hbx => VG.Proof.AesOcb.X86.stage32W_ok L Et hj hbx) (fun Et hbx => VG.Proof.AesOcb.X86.stage32L_ok L Et hbx)
  refine ⟨s', ?_, ⟨?_, by rw [← m₁]; exact f', fun r h₁ h₂ h₃ h₄ => by rw [g' r h₁ h₃ h₄, g₁ r h₁ h₂],
    by rw [rd', rd₁], by rw [wr', wr₁]⟩⟩
  · rw [show stage32 = stageMask 5 ++ (stage32W 0 ++ stage32W 1 ++ stage32W 2 ++ stage32W 3 ++ stage32W 4 ++
      (([.mov .eax (slot (stO + 20)), .mov .ecx (imm 0)] : List Instr) ++ selW 5)) by simp [stage32]]
    exact runBlock_app_of run₁ run'
  · rw [v', m₁]
    split
    · exact shl6_32 _ _ _ _ _ _
    · rfl

/-- `Stretch = Ktop ‖ (Ktop[1..64] ⊕ Ktop[9..72])`. -/
def stretchV (ktop : Block) : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)

/-- The block at `W + d` as its four byte-reversed words. -/
theorem blockAtMem_words (m : Mem) (W : BitVec 32) (d : Nat) :
    blockAtMem m (w64 W + BitVec.ofNat 64 d) = byteRev32 (slotv m W d) ++ byteRev32 (slotv m W (d + 4)) ++
      byteRev32 (slotv m W (d + 8)) ++ byteRev32 (slotv m W (d + 12)) := by
  rw [blockAtMem, Proof.Ocb.ofBytes_eq, Proof.Cmac.ofBytes_rev4, slotv_eq, slotv_eq, slotv_eq, slotv_eq,
    VG.Proof.AesOcb.X86.add_ofNat_assoc, VG.Proof.AesOcb.X86.add_ofNat_assoc, VG.Proof.AesOcb.X86.add_ofNat_assoc]

/-- Word `j < 2` of `Stretch`'s tail. -/
theorem tailW_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {j : Nat} (hj : j < 2) :
    ∃ t', runBlock isa (tailW j) t = some t' ∧
      t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 (256 + 4 * j))
        ((slotv t.mem p.W (240 + 4 * j) <<< 8 ||| slotv t.mem p.W (240 + 4 * j + 4) >>> 24) ^^^
          slotv t.mem p.W (240 + 4 * j)) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [tailW, shlEcx, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_,
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [ror_mask32 _ (show 0 < 8 by decide) (show 8 < 32 by decide), slotv_eq]

/-- `Stretch` to `W + stO`, from `Ktop` at `W + tmpO`. -/
theorem stretch_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) :
    ∃ s', runBlock isa Impl.AesOcb.X86.stretch s = some s' ∧ VG.Proof.AesOcb.X86.stv s'.mem p.W = VG.Proof.AesOcb.X86.stretchV (blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 tmpO)) ∧
      Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa ([0, 1, 2, 3].flatMap (fun j =>
      [.mov .eax (slot (tmpO + 4 * j)), .bswap .eax, .store (at_ .ebp (stO + 4 * j)) .eax])) s = some s₁ ∧
      s₁.mem = (((s.mem.writeW (w64 p.W + BitVec.ofNat 64 240) (byteRev32 (slotv s.mem p.W 112))).writeW
        (w64 p.W + BitVec.ofNat 64 244) (byteRev32 (slotv s.mem p.W 116))).writeW
        (w64 p.W + BitVec.ofNat 64 248) (byteRev32 (slotv s.mem p.W 120))).writeW
        (w64 p.W + BitVec.ofNat 64 252) (byteRev32 (slotv s.mem p.W 124)) ∧
      (∀ r, r ≠ .eax → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by grun [List.flatMap_cons, List.flatMap_nil, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_,
      fun r h₁ => by gregs [h₁], by gmems [], by gmems []⟩
    gmems [VG.Proof.AesOcb.X86.bswap_eq, slotv_eq]
  have E₁ : VG.Proof.AesOcb.X86.Env p s₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (VG.Proof.AesOcb.X86.frame_toMut (rs := [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩]) (by
      rw [m₁]
      exact VG.Proof.AesOcb.X86.frame_st (VG.Proof.AesOcb.X86.frame_st (VG.Proof.AesOcb.X86.frame_st (VG.Proof.AesOcb.X86.frame_st (Frame.refl _ _) (by decide) (by decide) _) (by decide) (by decide) _)
        (by decide) (by decide) _) (by decide) (by decide) _)
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.tailW_ok L E₁ (j := 0) (by decide)
  have E₂ : VG.Proof.AesOcb.X86.Env p s₂ := E₁.mut L (by rw [g₂ _ (by decide) (by decide) (by decide), E₁.ebp])
    (by rw [g₂ _ (by decide) (by decide) (by decide), E₁.esp]) rd₂ wr₂
    (VG.Proof.AesOcb.X86.frame_toMut (rs := [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩]) (by
      rw [m₂]; exact VG.Proof.AesOcb.X86.frame_st (Frame.refl _ _) (by decide) (by decide) _)
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := VG.Proof.AesOcb.X86.tailW_ok L E₂ (j := 1) (by decide)
  refine ⟨s₃, runBlock_app_of (runBlock_app_of run₁ run₂) run₃, ?_, ?_,
    fun r h₁ h₂ h₃ => by rw [g₃ r h₁ h₂ h₃, g₂ r h₁ h₂ h₃, g₁ r h₁], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  · simp only [Nat.reduceMul, Nat.reduceAdd] at m₂ m₃
    have m₁' := m₁
    rw [VG.Proof.AesOcb.X86.stv]
    simp (disch := decide) only [VG.Proof.AesOcb.X86.slot_upd m₃, VG.Proof.AesOcb.X86.slot_upd m₂, Nat.reduceEqDiff, ↓reduceIte]
    rw [VG.Proof.AesOcb.X86.stretchV, VG.Proof.AesOcb.X86.blockAtMem_words, stretch_words32]
    simp (disch := first | decide | omega) only [slotv_eq, m₁, Mem.readW_writeW_self32, readW_writeW_off,
      Nat.reduceAdd]
  · simp only [Nat.reduceMul, Nat.reduceAdd] at m₂ m₃
    rw [m₃, m₂, m₁]
    exact VG.Proof.AesOcb.X86.frame_st (VG.Proof.AesOcb.X86.frame_st (VG.Proof.AesOcb.X86.frame_st (VG.Proof.AesOcb.X86.frame_st (VG.Proof.AesOcb.X86.frame_st (VG.Proof.AesOcb.X86.frame_st (Frame.refl _ _) (by decide) (by decide) _)
      (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _)
      (by decide) (by decide) _

/-- The top four of six words. -/
theorem top4 (a b c d e f : BitVec 32) : (cat6 a b c d e f).extractLsb' 64 128 = a ++ b ++ c ++ d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Proof.Ocb.getLsbD_cat6,
    BitVec.getLsbD_append]
  simp only [Nat.sub_sub, Nat.reduceAdd]
  split_ifs <;> first | omega | exact congrArg _ (by omega)

/-- What `offset0` leaves. -/
structure Off0Post (p : VG.Proof.AesOcb.X86.Prm) (o : Block) (s s' : State) : Prop where
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o0O, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem s'.mem
  ofs : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 o0O) = o
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- A stage keeps the environment and `bottom`. -/
theorem StagePost.env {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {b : Bool} {f : BitVec 192 → BitVec 192} {s s' : State}
    (P : VG.Proof.AesOcb.X86.StagePost p b f s s') (E : VG.Proof.AesOcb.X86.Env p s) : VG.Proof.AesOcb.X86.Env p s' :=
  E.mut L (by rw [P.gpr _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (by rw [P.gpr _ (by decide) (by decide) (by decide) (by decide), E.esp]) P.rd P.wr
    (VG.Proof.AesOcb.X86.frame_toMut P.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))

theorem StagePost.bot {p : VG.Proof.AesOcb.X86.Prm} {b : Bool} {f : BitVec 192 → BitVec 192} {s s' : State}
    (P : VG.Proof.AesOcb.X86.StagePost p b f s s') : slotv s'.mem p.W botO = slotv s.mem p.W botO :=
  P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 botO, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
    (by decide)

theorem offset0_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {v : Nat} (hv : v < 64)
    (hbot : slotv s.mem p.W botO = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa offset0 s = some s' ∧
      VG.Proof.AesOcb.X86.Off0Post p ((VG.Proof.AesOcb.X86.stretchV (blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128) s s' := by
  obtain ⟨s₁, run₁, v₁, f₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.stretch_ok L E
  have E₁ : VG.Proof.AesOcb.X86.Env p s₁ := E.mut L (by rw [g₁ _ (by decide) (by decide) (by decide), E.ebp])
    (by rw [g₁ _ (by decide) (by decide) (by decide), E.esp]) rd₁ wr₁
    (VG.Proof.AesOcb.X86.frame_toMut f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have b₁ : slotv s₁.mem p.W botO = BitVec.ofNat 32 v := by
    rw [← hbot]
    exact f₁.readW (r := ⟨w64 p.W + BitVec.ofNat 64 botO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)
  obtain ⟨s₂, run₂, P₂⟩ := VG.Proof.AesOcb.X86.stage_ok L E₁ (k := 0) (a := 1) (by decide) (by decide) (by decide) hv b₁
  obtain ⟨s₃, run₃, P₃⟩ := VG.Proof.AesOcb.X86.stage_ok L (P₂.env L E₁) (k := 1) (a := 2) (by decide) (by decide) (by decide) hv
    (P₂.bot.trans b₁)
  obtain ⟨s₄, run₄, P₄⟩ := VG.Proof.AesOcb.X86.stage_ok L (P₃.env L (P₂.env L E₁)) (k := 2) (a := 4) (by decide) (by decide) (by decide) hv
    (P₃.bot.trans (P₂.bot.trans b₁))
  obtain ⟨s₅, run₅, P₅⟩ := VG.Proof.AesOcb.X86.stage_ok L (P₄.env L (P₃.env L (P₂.env L E₁))) (k := 3) (a := 8) (by decide) (by decide)
    (by decide) hv (P₄.bot.trans (P₃.bot.trans (P₂.bot.trans b₁)))
  obtain ⟨s₆, run₆, P₆⟩ := VG.Proof.AesOcb.X86.stage_ok L (P₅.env L (P₄.env L (P₃.env L (P₂.env L E₁)))) (k := 4) (a := 16) (by decide)
    (by decide) (by decide) hv (P₅.bot.trans (P₄.bot.trans (P₃.bot.trans (P₂.bot.trans b₁))))
  have E₆ := P₆.env L (P₅.env L (P₄.env L (P₃.env L (P₂.env L E₁))))
  obtain ⟨s₇, run₇, P₇⟩ := VG.Proof.AesOcb.X86.stage32_ok L E₆ hv
    (P₆.bot.trans (P₅.bot.trans (P₄.bot.trans (P₃.bot.trans (P₂.bot.trans b₁)))))
  have E₇ := P₇.env L E₆
  have hw : VG.Proof.AesOcb.X86.stv s₇.mem p.W = VG.Proof.AesOcb.X86.stretchV (blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 tmpO)) <<< v := by
    rw [P₇.val, P₆.val, P₅.val, P₄.val, P₃.val, P₂.val, v₁, ← Proof.Ocb.shl_stages _ hv]; rfl
  have hO : (VG.Proof.AesOcb.X86.stv s₇.mem p.W).extractLsb' 64 128 =
      (VG.Proof.AesOcb.X86.stretchV (blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [hw, Proof.Ocb.offset_shl _ (by omega)]
  obtain ⟨s₈, run₈, m₈, g₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa ([0, 1, 2, 3].flatMap (fun j =>
      [.mov .eax (slot (stO + 4 * j)), .bswap .eax, .store (at_ .ebp (ofsO + 4 * j)) .eax,
        .store (at_ .ebp (o0O + 4 * j)) .eax])) s₇ = some s₈ ∧
      s₈.mem = (((((((s₇.mem.writeW (w64 p.W + BitVec.ofNat 64 16) (byteRev32 (slotv s₇.mem p.W 240))).writeW
        (w64 p.W + BitVec.ofNat 64 224) (byteRev32 (slotv s₇.mem p.W 240))).writeW
        (w64 p.W + BitVec.ofNat 64 20) (byteRev32 (slotv s₇.mem p.W 244))).writeW
        (w64 p.W + BitVec.ofNat 64 228) (byteRev32 (slotv s₇.mem p.W 244))).writeW
        (w64 p.W + BitVec.ofNat 64 24) (byteRev32 (slotv s₇.mem p.W 248))).writeW
        (w64 p.W + BitVec.ofNat 64 232) (byteRev32 (slotv s₇.mem p.W 248))).writeW
        (w64 p.W + BitVec.ofNat 64 28) (byteRev32 (slotv s₇.mem p.W 252))).writeW
        (w64 p.W + BitVec.ofNat 64 236) (byteRev32 (slotv s₇.mem p.W 252)) ∧
      (∀ r, r ≠ .eax → s₈.gpr r = s₇.gpr r) ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by grun [List.flatMap_cons, List.flatMap_nil, E₇.ebp, L.aW, E₇.perm.wR, E₇.perm.wW], ?_,
      fun r h₁ => by gregs [h₁], by gmems [], by gmems []⟩
    gmems [VG.Proof.AesOcb.X86.bswap_eq, slotv_eq]
  have blk : ∀ d, d = 16 ∨ d = 224 → blockAtMem s₈.mem (w64 p.W + BitVec.ofNat 64 d) =
      (VG.Proof.AesOcb.X86.stretchV (blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    intro d hd
    rw [← hO, VG.Proof.AesOcb.X86.stv, VG.Proof.AesOcb.X86.top4, VG.Proof.AesOcb.X86.blockAtMem_words]
    rcases hd with rfl | rfl <;>
      simp (disch := first | decide | omega) only [slotv_eq, m₈, Mem.readW_writeW_self32, readW_writeW_off,
        Nat.reduceAdd, Proof.Cmac.byteRev32_byteRev32]
  have fs : ∀ {t t' : State} {b : Bool} {f : BitVec 192 → BitVec 192}, VG.Proof.AesOcb.X86.StagePost p b f t t' →
      Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o0O, 16⟩,
        ⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] t.mem t'.mem := fun P =>
    P.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]
  have F₇ : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o0O, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem s₇.mem :=
    ((((((f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans (fs P₂)).trans (fs P₃)).trans
      (fs P₄)).trans (fs P₅)).trans (fs P₆)).trans (fs P₇)
  refine ⟨s₈, ?_, ⟨?_, blk 16 (.inl rfl), blk 224 (.inr rfl), fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_⟩⟩
  · unfold offset0
    exact runBlock_app_of (runBlock_app_of (runBlock_app_of (runBlock_app_of (runBlock_app_of (runBlock_app_of
      (runBlock_app_of run₁ run₂) run₃) run₄) run₅) run₆) run₇) run₈
  · rw [m₈]
    have c : ∀ e d, (e = 16 ∨ e = 224) → e ≤ d → d + 4 ≤ e + 16 →
        (⟨w64 p.W + BitVec.ofNat 64 e, 16⟩ : Region).Contains (w64 p.W + BitVec.ofNat 64 d) (32 / 8) :=
      fun e d he h₁ h₂ => Offset.contains (w64 p.W) (by omega) (by rcases he with rfl | rfl <;> omega) (by omega)
    have m0 : (⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region) ∈ [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩,
        ⟨w64 p.W + BitVec.ofNat 64 o0O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] := by simp
    have m1 : (⟨w64 p.W + BitVec.ofNat 64 o0O, 16⟩ : Region) ∈ [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩,
        ⟨w64 p.W + BitVec.ofNat 64 o0O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] := by simp
    exact (((((((F₇.writeW m0 _ (c 16 16 (.inl rfl) (by decide) (by decide))).writeW m1 _
      (c 224 224 (.inr rfl) (by decide) (by decide))).writeW m0 _ (c 16 20 (.inl rfl) (by decide) (by decide))).writeW
      m1 _ (c 224 228 (.inr rfl) (by decide) (by decide))).writeW m0 _ (c 16 24 (.inl rfl) (by decide) (by decide))).writeW
      m1 _ (c 224 232 (.inr rfl) (by decide) (by decide))).writeW m0 _ (c 16 28 (.inl rfl) (by decide) (by decide))).writeW
      m1 _ (c 224 236 (.inr rfl) (by decide) (by decide))
  · rw [g₈ r h₁, P₇.gpr r h₁ h₂ h₃ h₄, P₆.gpr r h₁ h₂ h₃ h₄, P₅.gpr r h₁ h₂ h₃ h₄, P₄.gpr r h₁ h₂ h₃ h₄,
      P₃.gpr r h₁ h₂ h₃ h₄, P₂.gpr r h₁ h₂ h₃ h₄, g₁ r h₁ h₃ h₄]
  · rw [rd₈, P₇.rd, P₆.rd, P₅.rd, P₄.rd, P₃.rd, P₂.rd, rd₁]
  · rw [wr₈, P₇.wr, P₆.wr, P₅.wr, P₄.wr, P₃.wr, P₂.wr, wr₁]

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Calls`. -/
section

/-!
# AES-OCB on x86: enciphering blocks (`callBlocks`)

Untrusted: everything here is checked by Lean. `callBlocks f args` sets up
the arguments of `vg_aes_*_blocks` (`args` puts the blocks' address in `edx`
and their number in `ebx`) and calls it with the key context and the working
space at `W + scrO` (`callBlocks_ok`): the blocks at `D` (`DReg`, in `W` or
the data) go through `f` with the key schedule.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq runBlock_app_of toNat_rounds)

/-- `n` blocks at `D` that a call may encipher in place: in `W` before
`scrO`, or in the data. -/
structure DReg (p : VG.Proof.AesOcb.X86.Prm) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  kd : (⟨w64 p.K, 240⟩ : Region).Disjoint ⟨w64 D, 16 * n⟩
  ds : (⟨w64 D, 16 * n⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩
  bd : (VG.Proof.AesOcb.X86.stk p).Disjoint ⟨w64 D, 16 * n⟩
  wr : Covers [⟨w64 D, 16 * n⟩] s.wr
  inm : VG.Proof.AesOcb.X86.InMut p [⟨w64 D, 16 * n⟩]

theorem DReg.of_eq {p : VG.Proof.AesOcb.X86.Prm} {s s' : State} {D : BitVec 32} {n : Nat} (h : VG.Proof.AesOcb.X86.DReg p s D n) (hwr : s'.wr = s.wr) :
    VG.Proof.AesOcb.X86.DReg p s' D n := ⟨h.fD, h.kd, h.ds, h.bd, by rw [hwr]; exact h.wr, h.inm⟩

/-- Blocks of `W` before `scrO`. -/
theorem DReg.w {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {d n : Nat} (h : d + 16 * n ≤ scrO)
    (hm : d + 16 * n ≤ 128 ∨ 144 ≤ d ∧ d + 16 * n ≤ 176 ∨ 216 ≤ d ∧ d + 16 * n ≤ 384 ∨ 384 ≤ d) :
    VG.Proof.AesOcb.X86.DReg p s (p.W + BitVec.ofNat 32 d) n := by
  simp only [scrO] at h
  have a := L.aW (o := d) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [L.nW (by omega)]; have := L.ww; omega
  · rw [a]; exact (L.k_w' (by omega)).sub_left (Region.sub_prefix (by decide))
  · rw [a]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · rw [a]; exact L.bw' (by omega)
  · rw [a]; exact E.perm.wC (by omega)
  simp only [List.mem_singleton] at hr; subst hr; rw [a]
  rcases hm with hm | hm | hm | hm
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inl hm)
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inl hm))
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inl hm)))
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inr ⟨hm, by omega⟩)))

/-- What `callBlocks` leaves: the blocks through `f`. -/
structure CallPost (p : VG.Proof.AesOcb.X86.Prm) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (D : BitVec 32) (n : Nat)
    (s s' : State) : Prop where
  env : VG.Proof.AesOcb.X86.Env p s'
  frame : Frame [⟨w64 D, 16 * n⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, VG.Proof.AesOcb.X86.stk p] s.mem s'.mem
  out : Spec.Aes.statesAt s'.mem (w64 D) n =
    (Spec.Aes.statesAt s.mem (w64 D) n).map (f p.R (bytesAt s.mem (w64 p.K) (16 * (p.R + 1))))
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The arguments of `vg_aes_*_blocks` but the blocks: the key context, its
rounds, and the working space at `W + scrO`. -/
theorem callArgs_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {D : BitVec 32} {n : Nat}
    (hdx : s.gpr .edx = D) (hbx : s.gpr .ebx = BitVec.ofNat 32 n) (hD : VG.Proof.AesOcb.X86.DReg p s D n) :
    ∃ s₁, runBlock isa [.mov .eax (slot ctxO), .mov .ecx (slot rndO), .alu .add .ebp (imm scrO)] s = some s₁ ∧
      VG.Proof.AesOcb.X86.BCall s₁ p.K D (p.W + BitVec.ofNat 32 scrO) p.R n ∧ s₁.gpr .esp = p.SP ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebp → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  have hc := E.slots.ctx
  have hr := E.slots.rounds
  simp only [slotv_eq] at hc hr
  obtain ⟨s₁, run₁, ax₁, cx₁, bp₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .eax (slot ctxO),
      .mov .ecx (slot rndO), .alu .add .ebp (imm scrO)] s = some s₁ ∧ s₁.gpr .eax = p.K ∧
      s₁.gpr .ecx = BitVec.ofNat 32 p.R ∧ s₁.gpr .ebp = p.W + BitVec.ofNat 32 scrO ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebp → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hc, hr], by gregs [hc], by gregs [hr], by gregs [E.ebp],
      fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [], by gmems []⟩
  have aS : w64 (p.W + BitVec.ofNat 32 scrO) = w64 p.W + BitVec.ofNat 64 scrO := L.aW (by decide)
  have hsp₁ : s₁.gpr .esp = p.SP := by rw [g₁ _ (by decide) (by decide) (by decide), E.esp]
  refine ⟨s₁, run₁, {
    eax := ax₁, ecx := cx₁, edx := by rw [g₁ _ (by decide) (by decide) (by decide), hdx],
    ebx := by rw [g₁ _ (by decide) (by decide) (by decide), hbx], ebp := bp₁, rounds := L.rounds,
    esp := by rw [hsp₁]; exact L.sp, kd := hD.kd,
    ks := by rw [aS]; exact (L.k_w' (by decide)).sub_left (Region.sub_prefix (by decide)),
    ds := by rw [aS]; exact hD.ds, bk := by rw [hsp₁]; exact L.bk.sub_right (Region.sub_prefix (by decide)),
    bd := by rw [hsp₁]; exact hD.bd, bs := by rw [hsp₁, aS]; exact L.bw' (by decide),
    fK := by have := L.kw; omega, fD := hD.fD, fS := by rw [L.nW (by decide)]; have := L.ww; omega,
    reads := by rw [rd₁, wr₁]; exact VG.Proof.AesOcb.X86.covers_prefix E.perm.k (by decide),
    writes := by
      rw [wr₁, aS]
      intro a k ⟨r, hr, hc⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hD.wr a k ⟨_, List.mem_singleton_self _, hc⟩
      · exact E.perm.wC (show scrO + 2048 ≤ 2560 by decide) a k ⟨_, List.mem_singleton_self _, hc⟩ },
    hsp₁, g₁, m₁, rd₁, wr₁⟩

/-- The call, from the state after `args`. -/
theorem blocksCall_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s)
    {D : BitVec 32} {n : Nat} (hdx : s.gpr .edx = D) (hbx : s.gpr .ebx = BitVec.ofNat 32 n) (hD : VG.Proof.AesOcb.X86.DReg p s D n) :
    WP isa (.seq (.block [.mov .eax (slot ctxO), .mov .ecx (slot rndO), .alu .add .ebp (imm scrO)])
      (.seq (blocksFrame fn) (.block [.alu .sub .ebp (imm scrO)]))) s (VG.Proof.AesOcb.X86.CallPost p f D n s) := by
  obtain ⟨s₁, run₁, bc, hsp₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.callArgs_ok L E hdx hbx hD
  have bp₁ := bc.ebp
  have aS : w64 (p.W + BitVec.ofNat 32 scrO) = w64 p.W + BitVec.ofNat 64 scrO := L.aW (by decide)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.blk_call ok nosp stack bc) fun s₂ P₂ => ?_)
  have bp₂ : s₂.gpr .ebp = p.W + BitVec.ofNat 32 scrO := by rw [P₂.saved _ (by decide), bp₁]
  have sp₂ : s₂.gpr .esp = p.SP := by rw [P₂.saved _ (by decide), hsp₁]
  obtain ⟨s₃, run₃, bp₃, g₃, m₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa [.alu .sub .ebp (imm scrO)] s₂ = some s₃ ∧
      s₃.gpr .ebp = p.W ∧ (∀ r, r ≠ .ebp → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧
      s₃.wr = s₂.wr := by
    refine ⟨_, by grun [], by gregs [bp₂]; exact BitVec.add_sub_cancel _ _, fun r h => by gregs [h], by gmems [],
      by gmems [], by gmems []⟩
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have fr : Frame [⟨w64 D, 16 * n⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, VG.Proof.AesOcb.X86.stk p] s.mem s₃.mem := by
    rw [m₃, ← m₁, ← aS]
    have := P₂.frame
    rw [hsp₁] at this
    exact this.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (by rfl))
  refine ⟨E.mut L bp₃ (by rw [g₃ _ (by decide), sp₂]) (by rw [rd₃, P₂.rd, rd₁]) (by rw [wr₃, P₂.wr, wr₁])
      (fr.sub fun r hr => ?_), fr, ?_, fun r h₁ _ h₂ h₃ => ?_, by rw [rd₃, P₂.rd, rd₁], by rw [wr₃, P₂.wr, wr₁]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hD.inm _ (List.mem_singleton_self _)
    · exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
    · exact VG.Proof.AesOcb.X86.inMut_stk p
  · rw [m₃, P₂.out, m₁]
  · by_cases h₄ : r = .ebp
    · subst h₄; rw [bp₃, E.ebp]
    · rw [g₃ r h₄, P₂.saved r (by cases r <;> simp_all [calleeSaved]), g₁ r h₁ h₂ h₄]

/-- `callBlocks`: `args`, which leaves the blocks' address in `edx` and their
number in `ebx`, then the call. -/
theorem callBlocks_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s)
    {args : List Instr} {D : BitVec 32} {n : Nat}
    (hargs : ∃ s₁, runBlock isa args s = some s₁ ∧ s₁.gpr .edx = D ∧ s₁.gpr .ebx = BitVec.ofNat 32 n ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr)
    (hD : VG.Proof.AesOcb.X86.DReg p s D n) :
    WP isa (callBlocks fn args) s (VG.Proof.AesOcb.X86.CallPost p f D n s) := by
  obtain ⟨s₁, run₁, dx₁, bx₁, g₁, m₁, rd₁, wr₁⟩ := hargs
  have E₁ : VG.Proof.AesOcb.X86.Env p s₁ := E.keep (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide)])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide)]) rd₁ wr₁ m₁
  unfold callBlocks
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [← WP.seq_iff]
  refine WP.mono (VG.Proof.AesOcb.X86.blocksCall_ok ok nosp stack L E₁ dx₁ bx₁ (hD.of_eq wr₁)) fun s' P => ?_
  have fr := P.frame
  have out := P.out
  rw [m₁] at fr out
  exact ⟨P.env, fr, out,
    fun r h₁ h₂ h₃ h₄ => by rw [P.gpr r h₁ h₂ h₃ h₄, g₁ r h₁ h₂ h₃ h₄], by rw [P.rd, rd₁], by rw [P.wr, wr₁]⟩

/-- `oneBlock d`: the block at `W + d`. -/
theorem oneBlock_ok {p : VG.Proof.AesOcb.X86.Prm} {s : State} (E : VG.Proof.AesOcb.X86.Env p s) (d : Nat) :
    ∃ s₁, runBlock isa (oneBlock d) s = some s₁ ∧ s₁.gpr .edx = p.W + BitVec.ofNat 32 d ∧
      s₁.gpr .ebx = BitVec.ofNat 32 1 ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr :=
  ⟨_, by grun [oneBlock], by gregs [E.ebp], by gregs [], fun r _ h₂ _ h₄ => by gregs [h₂, h₄], by gmems [],
    by gmems [], by gmems []⟩

/-- Block `i` after `vg_aes_encrypt_blocks`. -/
theorem CallPost.enc {p : VG.Proof.AesOcb.X86.Prm} {D : BitVec 32} {n : Nat} {s s' : State} (h : VG.Proof.AesOcb.X86.CallPost p Spec.Aes.cipher D n s s')
    {i : Nat} (hi : i < n) :
    blockAtMem s'.mem (w64 D + BitVec.ofNat 64 (16 * i)) =
      Spec.Ocb.ctxCiph s.mem (w64 p.K) p.R (blockAtMem s.mem (w64 D + BitVec.ofNat 64 (16 * i))) :=
  Proof.Ocb.blockAtMem_of_state _ (Proof.Ocb.stateAt_of_statesAt h.out hi)

/-- Block `i` after `vg_aes_decrypt_blocks`. -/
theorem CallPost.dec {p : VG.Proof.AesOcb.X86.Prm} {D : BitVec 32} {n : Nat} {s s' : State}
    (h : VG.Proof.AesOcb.X86.CallPost p Spec.Aes.invCipher D n s s') {i : Nat} (hi : i < n) :
    blockAtMem s'.mem (w64 D + BitVec.ofNat 64 (16 * i)) =
      Spec.Ocb.ctxInv s.mem (w64 p.K) p.R (blockAtMem s.mem (w64 D + BitVec.ofNat 64 (16 * i))) :=
  Proof.Ocb.blockAtMem_of_state _ (Proof.Ocb.stateAt_of_statesAt h.out hi)

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Nonce`. -/
section

/-!
# AES-OCB on x86: `Offset_0` from the nonce (`nonce`)

Untrusted: everything here is checked by Lean. `nonce` writes `Nonce` with
its last 6 bits cleared and `bottom` (`nonceBlock_ok`), enciphers the block
(`Ktop`, `callBlocks_ok`), and computes `Offset_0` (`offset0_ok`), to
`W + ofsO` and `W + o0O` (`nonce_ok`): §4.2's `Offset_0`
(`Proof.Ocb.offset0_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq)

/-- What the pieces before the data write: the parts of `W` in `mutR` and
the stack. -/
abbrev wR (p : VG.Proof.AesOcb.X86.Prm) : List Region := [VG.Proof.AesOcb.X86.wA p.W, VG.Proof.AesOcb.X86.wB p.W, VG.Proof.AesOcb.X86.wV p.W, VG.Proof.AesOcb.X86.wC p.W, VG.Proof.AesOcb.X86.stk p]

theorem wR_mut {p : VG.Proof.AesOcb.X86.Prm} {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.wR p) m m') : Frame (VG.Proof.AesOcb.X86.mutR p) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp

/-- A frame within `wR`. -/
theorem frame_wR {p : VG.Proof.AesOcb.X86.Prm} {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.AesOcb.X86.wR p, Region.Sub r r') : Frame (VG.Proof.AesOcb.X86.wR p) m m' := h.sub hs

theorem inW_wR (p : VG.Proof.AesOcb.X86.Prm) {d k : Nat}
    (h : d + k ≤ 128 ∨ 144 ≤ d ∧ d + k ≤ 176 ∨ 216 ≤ d ∧ d + k ≤ 384 ∨ 384 ≤ d ∧ d + k ≤ 2560) :
    ∃ r' ∈ VG.Proof.AesOcb.X86.wR p, Region.Sub ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with h | h | h | h
  · exact ⟨VG.Proof.AesOcb.X86.wA p.W, by simp, Offset.sub_base _ h⟩
  · exact ⟨VG.Proof.AesOcb.X86.wB p.W, by simp, Offset.sub _ (by omega) (by omega)⟩
  · exact ⟨VG.Proof.AesOcb.X86.wV p.W, by simp, Offset.sub _ (by omega) (by omega)⟩
  · exact ⟨VG.Proof.AesOcb.X86.wC p.W, by simp, Offset.sub _ (by omega) (by omega)⟩

/-- The data, after a frame within `wR`. -/
theorem data_wR {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.wR p) m m') :
    bytesAt m' (w64 p.D) p.n = bytesAt m (w64 p.D) p.n :=
  Proof.AesGcm.X86.bytesAt_frame h (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.d_w.sub_right (Region.sub_prefix (by decide))
    · exact L.d_w.sub_right (Lay.wSub (by decide))
    · exact L.d_w.sub_right (Lay.wSub (by decide))
    · exact L.d_w.sub_right (Lay.wSub (by decide))
    · exact L.bd.symm) (by have := L.dw; omega)

/-- The key context is apart from what the pieces write. -/
theorem k_mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) : ∀ r ∈ VG.Proof.AesOcb.X86.mutR p, (⟨w64 p.K, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.bk.symm
  · exact L.k_d

/-- The key schedule, after a frame within `mutR`. -/
theorem ctxCiph_mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.mutR p) m m') :
    ctxCiph m' (w64 p.K) p.R = ctxCiph m (w64 p.K) p.R := by
  unfold ctxCiph
  have hb := L.rounds_le
  rw [Proof.AesGcm.X86.bytesAt_frame h (fun r hr => (VG.Proof.AesOcb.X86.k_mut L r hr).sub_left (Region.sub_prefix (by omega)))
    (by omega)]

/-- What `nonce` leaves. -/
structure NonceOk (p : VG.Proof.AesOcb.X86.Prm) (o : Block) (s s' : State) : Prop where
  env : VG.Proof.AesOcb.X86.Env p s'
  frame : Frame (VG.Proof.AesOcb.X86.wR p) s.mem s'.mem
  ofs : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 o0O) = o
  keep : ∀ {d : Nat}, 32 ≤ d → d + 16 ≤ 112 →
    blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 d)
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonce_ok (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) :
    WP isa (nonce (VG.Proof.AesOcb.X86.callees v)) s
      (VG.Proof.AesOcb.X86.NonceOk p (Spec.Ocb.offset0 (ctxCiph s.mem (w64 p.K) p.R) p.tl (bytesAt s.mem (w64 p.N) p.nl)) s) := by
  unfold nonce
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.nonceBlock_ok L E) fun s₁ P₁ => ?_)
  have F₁ : Frame (VG.Proof.AesOcb.X86.wR p) s.mem s₁.mem := VG.Proof.AesOcb.X86.frame_wR P₁.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.AesOcb.X86.inW_wR p (.inl (by decide))
    · exact VG.Proof.AesOcb.X86.inW_wR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  have E₁ : VG.Proof.AesOcb.X86.Env p s₁ := E.mut L (by rw [P₁.gpr _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (by rw [P₁.gpr _ (by decide) (by decide) (by decide) (by decide), E.esp]) P₁.rd P₁.wr (VG.Proof.AesOcb.X86.wR_mut F₁)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E₁
    (VG.Proof.AesOcb.X86.oneBlock_ok E₁ tmpO) (DReg.w L E₁ (d := tmpO) (n := 1) (by decide) (.inl (by decide)))) fun s₂ P₂ => ?_)
  have a112 : w64 (p.W + BitVec.ofNat 32 tmpO) = w64 p.W + BitVec.ofNat 64 tmpO := L.aW (by decide)
  have F₂ : Frame (VG.Proof.AesOcb.X86.wR p) s₁.mem s₂.mem := VG.Proof.AesOcb.X86.frame_wR P₂.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a112]; exact VG.Proof.AesOcb.X86.inW_wR p (.inl (by decide))
    · exact VG.Proof.AesOcb.X86.inW_wR p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
    · exact ⟨_, by simp, fun _ h => h⟩
  have ktop : blockAtMem s₂.mem (w64 p.W + BitVec.ofNat 64 tmpO) =
      ctxCiph s.mem (w64 p.K) p.R (Proof.Ocb.nonceN p.tl (bytesAt s.mem (w64 p.N) p.nl) &&& ~~~(63 : Block)) := by
    have := P₂.enc (i := 0) (by decide)
    rw [a112, show w64 p.W + BitVec.ofNat 64 tmpO + BitVec.ofNat 64 (16 * 0) = w64 p.W + BitVec.ofNat 64 tmpO from
      BitVec.add_zero _] at this
    rw [this, P₁.blk, VG.Proof.AesOcb.X86.ctxCiph_mut L (VG.Proof.AesOcb.X86.wR_mut F₁)]
  have hbv : ((Proof.Ocb.nonceN p.tl (bytesAt s.mem (w64 p.N) p.nl)).extractLsb' 0 6).toNat < 64 :=
    (BitVec.extractLsb' 0 6 _).isLt
  have bot₂ : slotv s₂.mem p.W botO =
      BitVec.ofNat 32 ((Proof.Ocb.nonceN p.tl (bytesAt s.mem (w64 p.N) p.nl)).extractLsb' 0 6).toNat := by
    rw [← P₁.bot]
    exact P₂.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 botO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a112]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  obtain ⟨s₃, run₃, P₃⟩ := VG.Proof.AesOcb.X86.offset0_ok L P₂.env hbv bot₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have F₃ : Frame (VG.Proof.AesOcb.X86.wR p) s₂.mem s₃.mem := VG.Proof.AesOcb.X86.frame_wR P₃.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Proof.AesOcb.X86.inW_wR p (.inl (by decide))
    · exact VG.Proof.AesOcb.X86.inW_wR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact VG.Proof.AesOcb.X86.inW_wR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  have E₃ : VG.Proof.AesOcb.X86.Env p s₃ := P₂.env.mut L (by rw [P₃.gpr _ (by decide) (by decide) (by decide) (by decide), P₂.env.ebp])
    (by rw [P₃.gpr _ (by decide) (by decide) (by decide) (by decide), P₂.env.esp]) P₃.rd P₃.wr (VG.Proof.AesOcb.X86.wR_mut F₃)
  refine ⟨E₃, F₁.trans (F₂.trans F₃), ?_, ?_, fun {d} h₁ h₂ => ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_,
    by rw [P₃.rd, P₂.rd, P₁.rd], by rw [P₃.wr, P₂.wr, P₁.wr]⟩
  · rw [P₃.ofs, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [P₃.o0, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [Proof.Ocb.blockAtMem_frame P₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact Lay.w_w (by simp only [ofsO, o0O, stO]; omega) (by omega) (by decide)),
      Proof.Ocb.blockAtMem_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [a112]; exact Lay.w_w (by simp only [tmpO]; omega) (by omega) (by decide)
        · exact Lay.w_w (by simp only [scrO]; omega) (by omega) (by decide)
        · exact (L.bw' (by omega)).symm),
      Proof.Ocb.blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Lay.w_w (by simp only [tmpO, botO]; omega) (by omega) (by decide))]
  · rw [P₃.gpr r h₁ h₂ h₃ h₄, P₂.gpr r h₁ h₂ h₃ h₄, P₁.gpr r h₁ h₃ h₄ h₅]

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.HashFill`. -/
section

/-!
# AES-OCB on x86: filling the buffer of `HASH` (`hashFill`)

Untrusted: everything here is checked by Lean. `hashFill` computes the next
offset of `HASH`, `Offset_{i+1} = Offset_i ⊕ L_{ntz(i+1)}` (`lNtz_ok`,
`xor16W_ok`), and writes the next block of the associated data XORed with it
to the next slot of the buffer at `W + bufO` (`hashFill_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of in_off toNat_w64 add_ofNat_assoc32
  toNat_ofNat32)

/-- The XOR of the blocks at `P` and `Q`, stored at `D` as four words. -/
def xor2Mem (m : Mem) (P Q D : Addr) : Mem :=
  Proof.Cmac.store4 m D (m.readW P 32 ^^^ m.readW Q 32)
    (m.readW (P + BitVec.ofNat 64 4) 32 ^^^ m.readW (Q + BitVec.ofNat 64 4) 32)
    (m.readW (P + BitVec.ofNat 64 8) 32 ^^^ m.readW (Q + BitVec.ofNat 64 8) 32)
    (m.readW (P + BitVec.ofNat 64 12) 32 ^^^ m.readW (Q + BitVec.ofNat 64 12) 32)

theorem xor2Mem_block (m : Mem) (P Q D : Addr) :
    blockAtMem (VG.Proof.AesOcb.X86.xor2Mem m P Q D) D = blockAtMem m P ^^^ blockAtMem m Q := by
  rw [blockAtMem, VG.Proof.AesOcb.X86.xor2Mem, Proof.Cmac.bytesAt_store4, Proof.Cmac.xor_words4, ← Proof.Ocb.xor_eq,
    Proof.Ocb.ofBytes_xor (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _)]
  rfl

theorem sub1_32 {n : Nat} (h : 1 ≤ n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 n - BitVec.ofNat 32 1 = BitVec.ofNat 32 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat32 hn, toNat_ofNat32 (by decide), toNat_ofNat32 (by omega)]
  omega

theorem beq_zero32 {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n == 0) = decide (n = 0) := by
  by_cases h : n = 0
  · subst h; rfl
  · have : BitVec.ofNat 32 n ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat32 hn] at this)
    rw [show (BitVec.ofNat 32 n == 0) = false from beq_eq_false_iff_ne.mpr this]; simp [h]

/-- The blocks of the associated data at `A`, `al` bytes. -/
structure ABuf (p : VG.Proof.AesOcb.X86.Prm) (s : State) (A : BitVec 32) (k : Nat) : Prop where
  fit : A.toNat + k ≤ 2 ^ 32
  w : (⟨w64 A, k⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  stk : (VG.Proof.AesOcb.X86.stk p).Disjoint ⟨w64 A, k⟩
  rd : Covers [⟨w64 A, k⟩] (s.rd ++ s.wr)

/-- The regions `hashFill` writes, for slot `i` of the buffer. -/
abbrev fillR (p : VG.Proof.AesOcb.X86.Prm) (i : Nat) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩, ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩, ⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩]

/-- What one `hashFill` leaves. -/
structure FillPost (p : VG.Proof.AesOcb.X86.Prm) (A : BitVec 32) (l : Block) (j i c : Nat) (t t' : State) : Prop where
  frame : Frame (VG.Proof.AesOcb.X86.fillR p i) t.mem t'.mem
  oh : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1)
  buf : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * i)) =
    blockAtMem t.mem (w64 (A + BitVec.ofNat 32 (16 * (j + i)))) ^^^ offAt 0 l (j + i + 1)
  fp : slotv t'.mem p.W fpO = p.W + BitVec.ofNat 32 (bufO + 16 * (i + 1))
  esi : t'.gpr .esi = A + BitVec.ofNat 32 (16 * (j + i + 1))
  edi : t'.gpr .edi = BitVec.ofNat 32 (j + i + 2)
  ebx : t'.gpr .ebx = BitVec.ofNat 32 (c - (i + 1))
  zf : t'.zf = some (decide (i + 1 = c))
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem hashFill_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {A : BitVec 32} {l : Block} {j i c : Nat}
    (hi : i < c) (hc : c ≤ 8) (hj : j + i + 2 < 2 ^ 32)
    (hdi : t.gpr .edi = BitVec.ofNat 32 (j + i + 1)) (hsi : t.gpr .esi = A + BitVec.ofNat 32 (16 * (j + i)))
    (hbx : t.gpr .ebx = BitVec.ofNat 32 (c - i)) (hfp : slotv t.mem p.W fpO = p.W + BitVec.ofNat 32 (bufO + 16 * i))
    (hl0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hoh : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i))
    (hA : VG.Proof.AesOcb.X86.ABuf p t (A + BitVec.ofNat 32 (16 * (j + i))) 16) :
    WP isa hashFill t (VG.Proof.AesOcb.X86.FillPost p A l j i c t) := by
  unfold hashFill
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.lNtz_ok L E (by omega) (by omega) hdi hl0) fun t₁ P₁ => ?_)
  have E₁ := P₁.env L E
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.xor16W_ok L E₁ (s := lO) (d := ohO) (by decide) (by decide) (.inl (by decide))
  have E₂ : VG.Proof.AesOcb.X86.Env p t₂ := E₁.mut L (by rw [g₂ _ (by decide), E₁.ebp]) (by rw [g₂ _ (by decide), E₁.esp]) rd₂ wr₂
    (VG.Proof.AesOcb.X86.frame_toMut (by rw [m₂]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩)))
  have fa : Frame (VG.Proof.AesOcb.X86.fillR p i) t.mem t₁.mem := P₁.frame.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp
  have fb : Frame (VG.Proof.AesOcb.X86.fillR p i) t₁.mem t₂.mem := by
    rw [m₂]
    exact (VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; simp
  have fr₂ : Frame (VG.Proof.AesOcb.X86.fillR p i) t.mem t₂.mem := fa.trans fb
  have oh₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [m₂, VG.Proof.AesOcb.X86.xorMem16_block, P₁.val, Proof.Ocb.blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), hoh]
    rfl
  -- what the block reads, in `t₂`
  have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
      ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp).trans (by
      rw [m₂]
      exact (VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _).mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; simp)
  have hfp₂ : t₂.mem.readW (w64 p.W + BitVec.ofNat 64 fpO) 32 = p.W + BitVec.ofNat 32 (bufO + 16 * i) := by
    rw [← hfp, slotv_eq]
    exact f₂.readW (r := ⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)) (by decide)
  have g₂' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₂.gpr r = t.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₂ r h₁, P₁.gpr r h₁ h₂ h₃]
  have si₂ : t₂.gpr .esi = A + BitVec.ofNat 32 (16 * (j + i)) := by
    rw [g₂' _ (by decide) (by decide) (by decide), hsi]
  have di₂ : t₂.gpr .edi = BitVec.ofNat 32 (j + i + 1) := by rw [g₂' _ (by decide) (by decide) (by decide), hdi]
  have bx₂ : t₂.gpr .ebx = BitVec.ofNat 32 (c - i) := by rw [g₂' _ (by decide) (by decide) (by decide), hbx]
  have rd₂' : t₂.rd = t.rd := by rw [rd₂, P₁.rd]
  have wr₂' : t₂.wr = t.wr := by rw [wr₂, P₁.wr]
  generalize hA' : A + BitVec.ofNat 32 (16 * (j + i)) = A' at si₂ hA ⊢
  have aA : ∀ {k : Nat}, k < 16 → w64 (A' + BitVec.ofNat 32 k) = w64 A' + BitVec.ofNat 64 k := fun hk =>
    w64_add (by have := hA.fit; omega)
  have aA0 : w64 (A' + BitVec.ofNat 32 0) = w64 A' := by rw [aA (by decide)]; exact BitVec.add_zero _
  have rA : ∀ {k : Nat}, k + 4 ≤ 16 → InRegions (t₂.rd ++ t₂.wr) (w64 A' + BitVec.ofNat 64 k) 4 := fun hk => by
    rw [rd₂', wr₂']; exact in_off hA.rd hk (by decide)
  have rA0 : InRegions (t₂.rd ++ t₂.wr) (w64 A') 4 := by simpa using rA (k := 0) (by decide)
  have hAk : (w64 A').toNat + 16 ≤ 2 ^ 32 := by rw [toNat_w64]; exact hA.fit
  have aQ : ∀ {k : Nat}, k < 16 → w64 (p.W + BitVec.ofNat 32 (bufO + 16 * i) + BitVec.ofNat 32 k) =
      w64 p.W + BitVec.ofNat 64 (bufO + 16 * i + k) := fun hk => by
    rw [add_ofNat_assoc32]; exact L.aW (by simp only [bufO]; omega)
  have aQ0 : w64 (p.W + BitVec.ofNat 32 (bufO + 16 * i) + BitVec.ofNat 32 0) = w64 p.W + BitVec.ofNat 64 (bufO + 16 * i) := by
    rw [aQ (by decide)]; rfl
  obtain ⟨t₃, run₃, m₃, si₃, di₃, bx₃, zf₃, g₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa ([.mov .edx (slot fpO)] ++
      [0, 4, 8, 12].flatMap (fun k => [.mov .eax (.mem (at_ .esi k)), .alu .xor .eax (slot (ohO + k)),
        .store (at_ .edx k) .eax]) ++
      [.alu .add .edx (imm 16), .store (at_ .ebp fpO) .edx, .alu .add .esi (imm 16), .alu .add .edi (imm 1),
       .alu .sub .ebx (imm 1)]) t₂ = some t₃ ∧
      t₃.mem = (VG.Proof.AesOcb.X86.xor2Mem t₂.mem (w64 A') (w64 p.W + BitVec.ofNat 64 ohO)
        (w64 p.W + BitVec.ofNat 64 (bufO + 16 * i))).writeW (w64 p.W + BitVec.ofNat 64 fpO)
          (p.W + BitVec.ofNat 32 (bufO + 16 * i) + BitVec.ofNat 32 16) ∧
      t₃.gpr .esi = A' + BitVec.ofNat 32 16 ∧ t₃.gpr .edi = BitVec.ofNat 32 (j + i + 1) + BitVec.ofNat 32 1 ∧
      t₃.gpr .ebx = BitVec.ofNat 32 (c - i) - BitVec.ofNat 32 1 ∧
      t₃.zf = some (BitVec.ofNat 32 (c - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → r ≠ .esi → r ≠ .edi → t₃.gpr r = t₂.gpr r) ∧
      t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by grun [List.flatMap_cons, List.flatMap_nil, E₂.ebp, L.aW, E₂.perm.wR, E₂.perm.wW, hfp₂, si₂, di₂,
      bx₂, aA, aA0, rA, rA0, aQ, aQ0, (VG.Proof.AesOcb.X86.readW_XW L hAk hA.w)], ?_, by gregs [si₂], by gregs [di₂], by gregs [bx₂],
      by gmems [bx₂], fun r h₁ h₂ h₃ h₄ h₅ => by gregs [h₁, h₂, h₃, h₄, h₅], by gmems [], by gmems []⟩
    gmems [(VG.Proof.AesOcb.X86.readW_XW L hAk hA.w)]
    simp only [VG.Proof.AesOcb.X86.xor2Mem, Proof.Cmac.store4, VG.Proof.AesOcb.X86.add_ofNat_assoc, Nat.add_zero, Nat.reduceAdd,
      show w64 A' + 0#64 = w64 A' from BitVec.add_zero _]
  refine WP.of_runBlock ⟨t₃, by simpa only [List.append_assoc] using runBlock_app_of run₂ run₃, ?_⟩
  have fQ : ∀ M : Mem, Frame [⟨w64 p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩] M
      (VG.Proof.AesOcb.X86.xor2Mem M (w64 A') (w64 p.W + BitVec.ofNat 64 ohO) (w64 p.W + BitVec.ofNat 64 (bufO + 16 * i))) :=
    fun M => Proof.Cmac.frame_store4 _ _ _ _ _
  have fF : ∀ (M : Mem) (v : BitVec 32), Frame [⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩] M
      (M.writeW (w64 p.W + BitVec.ofNat 64 fpO) v) :=
    fun M v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have dQ : ∀ {d k : Nat}, d + k ≤ bufO → (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint
      ⟨w64 p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩ := fun h => by
    simp only [bufO] at h ⊢; exact Lay.w_w (.inl (by omega)) (by omega) (by omega)
  have dF : ∀ {d k : Nat}, d + k ≤ fpO ∨ fpO + 4 ≤ d → d + k ≤ 2560 →
      (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩ :=
    fun h h' => Lay.w_w h h' (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ => ?_, by rw [rd₃, rd₂'], by rw [wr₃, wr₂']⟩
  · rw [m₃]
    exact (fr₂.trans ((fQ _).mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
      ((fF _ _).mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
  · rw [m₃, Proof.Ocb.blockAtMem_frame (fF _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dF (by decide) (by decide)),
      Proof.Ocb.blockAtMem_frame (fQ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dQ (by decide)), oh₂]
  · rw [m₃, Proof.Ocb.blockAtMem_frame (fF _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dF (.inr (by simp only [fpO, bufO]; omega)) (by simp only [bufO]; omega)),
      VG.Proof.AesOcb.X86.xor2Mem_block, oh₂, Proof.Ocb.blockAtMem_frame f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hA.w.sub_right (Lay.wSub (by decide))), hA']
  · rw [slotv_eq, m₃, Mem.readW_writeW_self32, add_ofNat_assoc32, show bufO + 16 * i + 16 = bufO + 16 * (i + 1) by omega]
  · rw [si₃, ← hA', add_ofNat_assoc32, show 16 * (j + i) + 16 = 16 * (j + i + 1) by omega]
  · rw [di₃, ← BitVec.ofNat_add]
  · rw [bx₃, VG.Proof.AesOcb.X86.sub1_32 (by omega) (by omega), show c - i - 1 = c - (i + 1) by omega]
  · rw [zf₃, VG.Proof.AesOcb.X86.sub1_32 (by omega) (by omega), VG.Proof.AesOcb.X86.beq_zero32 (by omega)]; congr 2; exact propext ⟨fun h => by omega,
      fun h => by omega⟩
  · rw [g₃ r h₁ h₂ h₄ h₅ h₆, g₂' r h₁ h₃ h₄]

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.HashChunk`. -/
section

/-!
# AES-OCB on x86: a chunk of `HASH` (`hashChunk`)

Untrusted: everything here is checked by Lean. After `j` of the `m` whole
blocks of the associated data `a`, `HInv` holds: the sum and the offset of
`HASH` are `Sum_j` and `Offset_j` (`Proof.Ocb.hsum`, `Proof.Ocb.offAt`),
`esi` points at block `j`, `edi` is `j + 1`, and `m − j` is kept in `W`.
`hashChunk` takes `c = min(8, m − j)` blocks: fills the buffer with each
block XORed with its offset (`fill_ok`), enciphers the buffer, adds it to
the sum (`hashSum_ok`), and leaves `HInv` at `j + c` (`hashChunk_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar)
open VG.Proof.Ocb (offAt hsum sumOf)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of in_off toNat_w64 add_ofNat_assoc32
  toNat_ofNat32 toNat_add32 covers_off length_bytesAt)

/-- What `HASH` writes: the sum, `L_{ntz(i)}`, the offset, `i`, the
variables at `[264, 280)`, the buffer and the working space of the functions
called, and the stack. -/
abbrev hashR (p : VG.Proof.AesOcb.X86.Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩, ⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩, VG.Proof.AesOcb.X86.wC p.W, VG.Proof.AesOcb.X86.stk p]

/-- A part of `W` within `hashR`. -/
theorem inHashR (p : VG.Proof.AesOcb.X86.Prm) {d k : Nat}
    (h : 48 ≤ d ∧ d + k ≤ 64 ∨ 96 ≤ d ∧ d + k ≤ 112 ∨ 160 ≤ d ∧ d + k ≤ 176 ∨ 220 ≤ d ∧ d + k ≤ 224 ∨
      264 ≤ d ∧ d + k ≤ 280 ∨ 384 ≤ d ∧ d + k ≤ 2560) :
    ∃ r' ∈ VG.Proof.AesOcb.X86.hashR p, Region.Sub ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with h | h | h | h | h | h
  · exact ⟨_, by simp, Offset.sub _ (e := 48) (k := 16) (by omega) (by omega)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 96) (k := 16) (by omega) (by omega)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 160) (k := 16) (by omega) (by omega)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 220) (k := 4) (by omega) (by omega)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 264) (k := 16) (by omega) (by omega)⟩
  · exact ⟨VG.Proof.AesOcb.X86.wC p.W, by simp, Offset.sub _ (by omega) (by omega)⟩

theorem hashR_wR {p : VG.Proof.AesOcb.X86.Prm} {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.hashR p) m m') : Frame (VG.Proof.AesOcb.X86.wR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.AesOcb.X86.inW_wR p (.inl (by decide))
  · exact VG.Proof.AesOcb.X86.inW_wR p (.inl (by decide))
  · exact VG.Proof.AesOcb.X86.inW_wR p (.inr (.inl ⟨by decide, by decide⟩))
  · exact VG.Proof.AesOcb.X86.inW_wR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact VG.Proof.AesOcb.X86.inW_wR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What `HASH` needs of its start, `s₀`: the key context's cipher and
`L_*`, and the associated data. -/
structure HCtx (p : VG.Proof.AesOcb.X86.Prm) (ciph : Cipher) (l : Block) (a : List Byte) (s₀ : State) : Prop where
  lay : VG.Proof.AesOcb.X86.Lay p
  ciph : ctxCiph s₀.mem (w64 p.K) p.R = ciph
  lstar : ctxLstar s₀.mem (w64 p.K) = l
  aad : bytesAt s₀.mem (w64 p.A) p.al = a

/-- What holds of `HASH` of `a` after `j` of its whole blocks, from the
state `s₀` at its start. -/
structure HInv (p : VG.Proof.AesOcb.X86.Prm) (ciph : Cipher) (l : Block) (a : List Byte) (s₀ s : State) (j : Nat) : Prop where
  env : VG.Proof.AesOcb.X86.Env p s
  frame : Frame (VG.Proof.AesOcb.X86.hashR p) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : j ≤ p.al / 16
  sum : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  oh : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l j
  esi : s.gpr .esi = p.A + BitVec.ofNat 32 (16 * j)
  edi : s.gpr .edi = BitVec.ofNat 32 (j + 1)
  hl : slotv s.mem p.W hlO = BitVec.ofNat 32 (p.al / 16 - j)
  rest : slotv s.mem p.W restO = BitVec.ofNat 32 (p.al % 16)
  l0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0

namespace HCtx

variable {p : VG.Proof.AesOcb.X86.Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86.HCtx p ciph l a s₀)
include C

theorem len : a.length = p.al := by rw [← C.aad, length_bytesAt]

/-- Block `i` of the associated data, in a state after `s₀`. -/
theorem blk {m : Mem} (h : Frame (VG.Proof.AesOcb.X86.mutR p) s₀.mem m) {i : Nat} (hi : i < p.al / 16) :
    blockAtMem m (w64 (p.A + BitVec.ofNat 32 (16 * i))) = blockAt a i := by
  have L := C.lay
  rw [w64_add (by have := L.aw; omega), ← C.aad, ← VG.Proof.AesOcb.X86.aad_mut L h, Proof.Ocb.blockAt_bytesAt _ _ (by omega)]

/-- Block `i` of the associated data, for `hashFill`. -/
theorem abuf {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {i : Nat} (hi : i < p.al / 16) :
    VG.Proof.AesOcb.X86.ABuf p s (p.A + BitVec.ofNat 32 (16 * i)) 16 := by
  have L := C.lay
  have hA := L.aw
  have a16 : w64 (p.A + BitVec.ofNat 32 (16 * i)) = w64 p.A + BitVec.ofNat 64 (16 * i) := w64_add (by omega)
  have sub : Region.Sub ⟨w64 (p.A + BitVec.ofNat 32 (16 * i)), 16⟩ ⟨w64 p.A, p.al⟩ := by
    rw [a16]; exact Offset.sub_base _ (by omega)
  refine ⟨by rw [toNat_add32 (by omega)]; omega, L.a_w.sub_left sub, L.ba.sub_right sub, ?_⟩
  rw [a16]; exact covers_off E.perm.aad (by omega) (by omega)

theorem ciph' {m : Mem} (h : Frame (VG.Proof.AesOcb.X86.mutR p) s₀.mem m) : ctxCiph m (w64 p.K) p.R = ciph := by
  rw [VG.Proof.AesOcb.X86.ctxCiph_mut C.lay h, C.ciph]

end HCtx

/-! ## Filling the buffer -/

/-- The fill loop after `i` of the `c` blocks of a chunk from block `j`. -/
structure FillInv (p : VG.Proof.AesOcb.X86.Prm) (ciph : Cipher) (l : Block) (a : List Byte) (s₀ : State) (j c : Nat) (t : State)
    (i : Nat) : Prop where
  env : VG.Proof.AesOcb.X86.Env p t
  frame : Frame (VG.Proof.AesOcb.X86.hashR p) s₀.mem t.mem
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  esi : t.gpr .esi = p.A + BitVec.ofNat 32 (16 * (j + i))
  edi : t.gpr .edi = BitVec.ofNat 32 (j + i + 1)
  ebx : t.gpr .ebx = BitVec.ofNat 32 (c - i)
  fp : slotv t.mem p.W fpO = p.W + BitVec.ofNat 32 (bufO + 16 * i)
  cnt : slotv t.mem p.W cntO = BitVec.ofNat 32 c
  oh : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i)
  buf : ∀ k < i, blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * k)) =
    blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)
  sum : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  hl : slotv t.mem p.W hlO = BitVec.ofNat 32 (p.al / 16 - j)
  rest : slotv t.mem p.W restO = BitVec.ofNat 32 (p.al % 16)
  l0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0

theorem fill_step {p : VG.Proof.AesOcb.X86.Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86.HCtx p ciph l a s₀)
    {j c : Nat} (hc : c ≤ 8) (hjc : j + c ≤ p.al / 16) {t : State} {i : Nat} (hi : i < c)
    (F : VG.Proof.AesOcb.X86.FillInv p ciph l a s₀ j c t i) :
    WP isa hashFill t fun t' => VG.Proof.AesOcb.X86.FillInv p ciph l a s₀ j c t' (i + 1) ∧ t'.zf = some (decide (i + 1 = c)) := by
  have L := C.lay
  have hal := L.al32
  refine WP.mono (VG.Proof.AesOcb.X86.hashFill_ok L F.env hi hc (by omega) F.edi F.esi F.ebx F.fp F.l0 F.oh
    (C.abuf F.env (i := j + i) (by omega))) fun t' P => ⟨?_, P.zf⟩
  have hfr : Frame (VG.Proof.AesOcb.X86.hashR p) t.mem t'.mem := P.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact VG.Proof.AesOcb.X86.inHashR p (.inr (.inl ⟨by decide, by decide⟩))
    · exact VG.Proof.AesOcb.X86.inHashR p (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))
    · exact VG.Proof.AesOcb.X86.inHashR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact VG.Proof.AesOcb.X86.inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by simp only [bufO]; omega, by simp only [bufO]; omega⟩)))))
    · exact VG.Proof.AesOcb.X86.inHashR p (.inr (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩)))))
  have dis : ∀ {d k : Nat}, (d + k ≤ lO ∨ lO + 16 ≤ d) → (d + k ≤ kO ∨ kO + 4 ≤ d) → (d + k ≤ ohO ∨ ohO + 16 ≤ d) →
      (d + k ≤ bufO + 16 * i ∨ bufO + 16 * i + 16 ≤ d) → (d + k ≤ fpO ∨ fpO + 4 ≤ d) → d + k ≤ 2560 →
      ∀ r ∈ VG.Proof.AesOcb.X86.fillR p i, (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h₁ h₂ h₃ h₄ h₅ h₆ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w h₁ h₆ (by decide)
    · exact Lay.w_w h₂ h₆ (by decide)
    · exact Lay.w_w h₃ h₆ (by decide)
    · exact Lay.w_w h₄ h₆ (by simp only [bufO]; omega)
    · exact Lay.w_w h₅ h₆ (by decide)
  have keepB : ∀ {d : Nat}, (d + 16 ≤ lO ∨ lO + 16 ≤ d) → (d + 16 ≤ kO ∨ kO + 4 ≤ d) →
      (d + 16 ≤ ohO ∨ ohO + 16 ≤ d) → (d + 16 ≤ bufO + 16 * i ∨ bufO + 16 * i + 16 ≤ d) →
      (d + 16 ≤ fpO ∨ fpO + 4 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun h₁ h₂ h₃ h₄ h₅ h₆ => Proof.Ocb.blockAtMem_frame P.frame (dis h₁ h₂ h₃ h₄ h₅ h₆)
  have keepW : ∀ {d : Nat}, (d + 4 ≤ lO ∨ lO + 16 ≤ d) → (d + 4 ≤ kO ∨ kO + 4 ≤ d) →
      (d + 4 ≤ ohO ∨ ohO + 16 ≤ d) → (d + 4 ≤ bufO + 16 * i ∨ bufO + 16 * i + 16 ≤ d) →
      (d + 4 ≤ fpO ∨ fpO + 4 ≤ d) → d + 4 ≤ 2560 → slotv t'.mem p.W d = slotv t.mem p.W d :=
    fun h₁ h₂ h₃ h₄ h₅ h₆ => P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 _, 4⟩) (Region.contains_self _ _)
      (dis h₁ h₂ h₃ h₄ h₅ h₆) (by decide)
  refine
    { env := F.env.mut L (by rw [P.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          F.env.ebp]) (by rw [P.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          F.env.esp]) P.rd P.wr (VG.Proof.AesOcb.X86.wR_mut (VG.Proof.AesOcb.X86.hashR_wR hfr))
      frame := F.frame.trans hfr
      rd := by rw [P.rd, F.rd]
      wr := by rw [P.wr, F.wr]
      esi := by rw [P.esi, show j + i + 1 = j + (i + 1) by omega]
      edi := by rw [P.edi, show j + i + 2 = j + (i + 1) + 1 by omega]
      ebx := P.ebx
      fp := P.fp
      cnt := by rw [keepW (by decide) (by decide) (by decide) (by simp only [cntO, bufO]; omega) (by decide)
        (by decide), F.cnt]
      oh := by rw [P.oh, show j + i + 1 = j + (i + 1) by omega]
      buf := fun k hk => ?_
      sum := by rw [keepB (by decide) (by decide) (by decide) (by simp only [sumO, bufO]; omega) (by decide)
        (by decide), F.sum]
      hl := by rw [keepW (by decide) (by decide) (by decide) (by simp only [hlO, bufO]; omega) (by decide)
        (by decide), F.hl]
      rest := by rw [keepW (by decide) (by decide) (by decide) (by simp only [restO, bufO]; omega) (by decide)
        (by decide), F.rest]
      l0 := by rw [keepB (by decide) (by decide) (by decide) (by simp only [l0O, bufO]; omega) (by decide)
        (by decide), F.l0] }
  rcases Nat.lt_or_ge k i with hk' | hk'
  · rw [keepB (by simp only [lO, bufO]; omega) (by simp only [kO, bufO]; omega) (by simp only [ohO, bufO]; omega)
      (by omega) (by simp only [fpO, bufO]; omega) (by simp only [bufO]; omega), F.buf k hk']
  · obtain rfl : k = i := by omega
    rw [P.buf, C.blk (VG.Proof.AesOcb.X86.wR_mut (VG.Proof.AesOcb.X86.hashR_wR F.frame)) (by omega)]

theorem fill_ok {p : VG.Proof.AesOcb.X86.Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86.HCtx p ciph l a s₀)
    {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ p.al / 16) {t : State}
    (F : VG.Proof.AesOcb.X86.FillInv p ciph l a s₀ j c t 0) :
    WP isa (.loop hashFill .ne) t fun t' => VG.Proof.AesOcb.X86.FillInv p ciph l a s₀ j c t' c := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧ VG.Proof.AesOcb.X86.FillInv p ciph l a s₀ j c u i) ?_ (c - 0) _
    ⟨0, rfl, hc0, F⟩
  rintro k u ⟨i, rfl, hi, F⟩
  refine WP.mono (VG.Proof.AesOcb.X86.fill_step C hc hjc hi F) fun u' ⟨F', hz⟩ => ?_
  by_cases he : i + 1 = c
  · left; exact ⟨(VG.Proof.AesOcb.X86.eval_ne hz).trans (by simp [he]), he ▸ F'⟩
  · right; exact ⟨(VG.Proof.AesOcb.X86.eval_ne hz).trans (by simp [he]), c - (i + 1), by omega, i + 1, rfl, by omega, F'⟩

/-! ## Adding the buffer to the sum -/

theorem hashSum_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {c : Nat} (hc0 : 0 < c) (hc : c ≤ 8)
    (hcnt : slotv t.mem p.W cntO = BitVec.ofNat 32 c) {g : Nat → Block}
    (hg : ∀ k < c, blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * k)) = g k) :
    WP isa hashSum t fun t' => Frame [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩] t.mem t'.mem ∧
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 sumO) =
        sumOf (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 sumO)) g c ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  simp only [slotv_eq] at hcnt
  obtain ⟨t₁, run₁, bx₁, dx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .ebx (slot cntO), .mov .edx (.reg .ebp),
      .alu .add .edx (imm bufO)] t = some t₁ ∧ t₁.gpr .ebx = BitVec.ofNat 32 (c - 0) ∧
      t₁.gpr .edx = p.W + BitVec.ofNat 32 (bufO + 16 * 0) ∧
      (∀ r, r ≠ .ebx → r ≠ .edx → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hcnt], by gregs [hcnt, Nat.sub_zero], by gregs [E.ebp],
      fun r h₁ h₂ => by gregs [h₁, h₂], by gmems [], by gmems [], by gmems []⟩
  unfold hashSum
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧ VG.Proof.AesOcb.X86.Env p u ∧
      u.gpr .edx = p.W + BitVec.ofNat 32 (bufO + 16 * i) ∧ u.gpr .ebx = BitVec.ofNat 32 (c - i) ∧
      Frame [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩] t.mem u.mem ∧
      blockAtMem u.mem (w64 p.W + BitVec.ofNat 64 sumO) =
        sumOf (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 sumO)) g i ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → u.gpr r = t.gpr r) ∧ u.rd = t.rd ∧ u.wr = t.wr)
    ?_ (c - 0) _ ⟨0, rfl, hc0, E.keep (by rw [g₁ _ (by decide) (by decide)]) (by rw [g₁ _ (by decide) (by decide)])
      rd₁ wr₁ m₁, dx₁, bx₁, by rw [m₁]; exact Frame.refl _ _, by rw [m₁]; rfl, fun r _ h₂ h₃ => g₁ r h₂ h₃, rd₁, wr₁⟩
  rintro k u ⟨i, rfl, hi, Eu, dx, bx, fr, sum, gu, rd, wr⟩
  obtain ⟨u₁, run₁', m₁', g₁', rd₁', wr₁'⟩ := VG.Proof.AesOcb.X86.xor16P_ok L Eu (b := .edx) (by decide) dx
    (e := bufO + 16 * i) (d := sumO) (by simp only [bufO]; omega) (by decide) (.inr (by simp only [bufO, sumO]; omega))
  have dx₁ : u₁.gpr .edx = p.W + BitVec.ofNat 32 (bufO + 16 * i) := by rw [g₁' _ (by decide), dx]
  have bx₁ : u₁.gpr .ebx = BitVec.ofNat 32 (c - i) := by rw [g₁' _ (by decide), bx]
  obtain ⟨u₂, run₂, dx₂, bx₂, zf₂, g₂, m₂, rd₂, wr₂⟩ : ∃ u₂, runBlock isa [.alu .add .edx (imm 16),
      .alu .sub .ebx (imm 1)] u₁ = some u₂ ∧ u₂.gpr .edx = p.W + BitVec.ofNat 32 (bufO + 16 * (i + 1)) ∧
      u₂.gpr .ebx = BitVec.ofNat 32 (c - (i + 1)) ∧ u₂.zf = some (decide (i + 1 = c)) ∧
      (∀ r, r ≠ .ebx → r ≠ .edx → u₂.gpr r = u₁.gpr r) ∧ u₂.mem = u₁.mem ∧ u₂.rd = u₁.rd ∧ u₂.wr = u₁.wr := by
    refine ⟨_, by grun [], ?_, ?_, ?_, fun r h₁ h₂ => by gregs [h₁, h₂], by gmems [], by gmems [], by gmems []⟩
    · gregs [dx₁]; rw [add_ofNat_assoc32, show bufO + 16 * i + 16 = bufO + 16 * (i + 1) by omega]
    · gregs [bx₁]; rw [VG.Proof.AesOcb.X86.sub1_32 (by omega) (by omega), show c - i - 1 = c - (i + 1) by omega]
    · gmems [bx₁]
      rw [VG.Proof.AesOcb.X86.sub1_32 (by omega) (by omega), VG.Proof.AesOcb.X86.beq_zero32 (by omega)]
      exact congrArg some (decide_eq_decide.mpr (by omega))
  refine WP.of_runBlock ⟨u₂, runBlock_app_of run₁' run₂, ?_⟩
  have Eu₂ : VG.Proof.AesOcb.X86.Env p u₂ := Eu.mut L (by rw [g₂ _ (by decide) (by decide), g₁' _ (by decide), Eu.ebp])
    (by rw [g₂ _ (by decide) (by decide), g₁' _ (by decide), Eu.esp]) (by rw [rd₂, rd₁']) (by rw [wr₂, wr₁'])
    (VG.Proof.AesOcb.X86.frame_toMut (by rw [m₂, m₁']; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  have hbuf : blockAtMem u.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * i)) = g i := by
    rw [Proof.Ocb.blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inr (by simp only [bufO, sumO]; omega)) (by simp only [bufO]; omega) (by decide),
      hg i hi]
  have fr' : Frame [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩] t.mem u₂.mem := by
    rw [m₂, m₁']; exact fr.trans (VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _)
  have sum' : blockAtMem u₂.mem (w64 p.W + BitVec.ofNat 64 sumO) =
      sumOf (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 sumO)) g (i + 1) := by
    rw [m₂, m₁', VG.Proof.AesOcb.X86.xorMem16_block, sum, hbuf]; rfl
  have gu' : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → u₂.gpr r = t.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₂ r h₂ h₃, g₁' r h₁, gu r h₁ h₂ h₃]
  by_cases he : i + 1 = c
  · left
    exact ⟨(VG.Proof.AesOcb.X86.eval_ne zf₂).trans (by simp [he]), fr', he ▸ sum', gu', by rw [rd₂, rd₁', rd], by rw [wr₂, wr₁', wr]⟩
  · right
    exact ⟨(VG.Proof.AesOcb.X86.eval_ne zf₂).trans (by simp [he]), c - (i + 1), by omega, i + 1, rfl, by omega, Eu₂, dx₂, bx₂, fr',
      sum', gu', by rw [rd₂, rd₁', rd], by rw [wr₂, wr₁', wr]⟩

/-! ## A chunk -/

theorem sub32' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat32 ha, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]
  omega

/-- `HInv` after code that keeps the registers it holds and changes only
words of `W` it does not mention. -/
theorem HInv.of_keep {p : VG.Proof.AesOcb.X86.Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ s s' : State} {j : Nat}
    (H : VG.Proof.AesOcb.X86.HInv p ciph l a s₀ s j) (hg : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesOcb.X86.HInv p ciph l a s₀ s' j :=
  { H with
    env := H.env.keep (by rw [hg _ (by decide) (by decide) (by decide) (by decide)])
      (by rw [hg _ (by decide) (by decide) (by decide) (by decide)]) hrd hwr hm
    frame := by rw [hm]; exact H.frame
    rd := by rw [hrd, H.rd]
    wr := by rw [hwr, H.wr]
    sum := by rw [hm, H.sum]
    oh := by rw [hm, H.oh]
    esi := by rw [hg _ (by decide) (by decide) (by decide) (by decide), H.esi]
    edi := by rw [hg _ (by decide) (by decide) (by decide) (by decide), H.edi]
    hl := by rw [hm, H.hl]
    rest := by rw [hm, H.rest]
    l0 := by rw [hm, H.l0] }

/-- `min(8, m − j)` in `ebx`. -/
theorem chunkHead_ok {p : VG.Proof.AesOcb.X86.Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86.HCtx p ciph l a s₀)
    {t : State} {j : Nat} (H : VG.Proof.AesOcb.X86.HInv p ciph l a s₀ t j) :
    WP isa (.seq (.block [.mov .ebx (slot hlO), .alu .cmp .ebx (imm 8)])
      (.ite .b (.block []) (.block [.mov .ebx (imm 8)]))) t fun t' =>
        VG.Proof.AesOcb.X86.HInv p ciph l a s₀ t' j ∧ t'.gpr .ebx = BitVec.ofNat 32 (min 8 (p.al / 16 - j)) := by
  have L := C.lay
  have hal := L.al32
  have hl := H.hl
  simp only [slotv_eq] at hl
  obtain ⟨t₁, run₁, bx₁, cf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .ebx (slot hlO), .alu .cmp .ebx (imm 8)] t =
      some t₁ ∧ t₁.gpr .ebx = BitVec.ofNat 32 (p.al / 16 - j) ∧ t₁.cf = some (decide (p.al / 16 - j < 8)) ∧
      (∀ r, r ≠ .ebx → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by grun [H.env.ebp, L.aW, H.env.perm.wR, hl], by gregs [hl], ?_, fun r h => by gregs [h], by gmems [],
      by gmems [], by gmems []⟩
    gmems [hl, toNat_ofNat32 (show p.al / 16 - j < 2 ^ 32 by omega), toNat_ofNat32 (show 8 < 2 ^ 32 by decide)]
  have H₁ := H.of_keep (fun r _ h₂ _ _ => g₁ r h₂) m₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (p.al / 16 - j < 8)) (VG.Proof.AesOcb.X86.eval_b cf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hlt : p.al / 16 - j < 8 := of_decide_eq_true hb
    rw [show min 8 (p.al / 16 - j) = p.al / 16 - j by omega]
    exact ⟨H₁, bx₁⟩
  · have hge : ¬ p.al / 16 - j < 8 := of_decide_eq_false hb
    obtain ⟨t₂, run₂, bx₂, g₂, m₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa [.mov .ebx (imm 8)] t₁ = some t₂ ∧
        t₂.gpr .ebx = BitVec.ofNat 32 8 ∧ (∀ r, r ≠ .ebx → t₂.gpr r = t₁.gpr r) ∧ t₂.mem = t₁.mem ∧ t₂.rd = t₁.rd ∧
        t₂.wr = t₁.wr :=
      ⟨_, by grun [], by gregs [], fun r h => by gregs [h], by gmems [], by gmems [], by gmems []⟩
    refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
    rw [show min 8 (p.al / 16 - j) = 8 by omega]
    exact ⟨H₁.of_keep (fun r _ h₂ _ _ => g₂ r h₂) m₂ rd₂ wr₂, bx₂⟩

/-- The start of a chunk of `c` blocks from `ebx`: its count and the buffer's
start kept in `W`. -/
theorem chunkStart_ok {p : VG.Proof.AesOcb.X86.Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : VG.Proof.AesOcb.X86.HCtx p ciph l a s₀) {t : State} {j c : Nat} (H : VG.Proof.AesOcb.X86.HInv p ciph l a s₀ t j)
    (hbx : t.gpr .ebx = BitVec.ofNat 32 c) :
    ∃ t₁, runBlock isa [.store (at_ .ebp cntO) .ebx, .mov .eax (.reg .ebp), .alu .add .eax (imm bufO),
      .store (at_ .ebp fpO) .eax] t = some t₁ ∧ VG.Proof.AesOcb.X86.FillInv p ciph l a s₀ j c t₁ 0 := by
  have L := C.lay
  have hal := L.al32
  have E := H.env
  -- the chunk's count and the buffer's start
  obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.store (at_ .ebp cntO) .ebx, .mov .eax (.reg .ebp),
      .alu .add .eax (imm bufO), .store (at_ .ebp fpO) .eax] t = some t₁ ∧
      t₁.mem = (t.mem.writeW (w64 p.W + BitVec.ofNat 64 cntO) (BitVec.ofNat 32 c)).writeW
        (w64 p.W + BitVec.ofNat 64 fpO) (p.W + BitVec.ofNat 32 bufO) ∧
      (∀ r, r ≠ .eax → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wW, hbx], by gmems [E.ebp, hbx], fun r h => by gregs [h], by gmems [],
      by gmems []⟩
  have fr₁ : Frame (VG.Proof.AesOcb.X86.hashR p) t.mem t₁.mem := by
    rw [m₁]
    have hm : (⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩ : Region) ∈ VG.Proof.AesOcb.X86.hashR p := by simp
    exact ((Frame.refl _ _).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 272) (n := 4) (by decide)
      (by decide) (by decide))).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 268) (n := 4) (by decide)
      (by decide) (by decide))
  have kW₁ : ∀ {d : Nat}, (d + 4 ≤ 268 ∨ 276 ≤ d) → d + 4 ≤ 2560 → slotv t₁.mem p.W d = slotv t.mem p.W d :=
    fun h h' => by
      rw [slotv_eq, slotv_eq, m₁, Mem.readW_writeW_sep (Offset.sep _ (by simp only [fpO]; omega) (by omega) (by decide))
        (by decide), Mem.readW_writeW_sep (Offset.sep _ (by simp only [cntO]; omega) (by omega) (by decide)) (by decide)]
  have kB₁ : ∀ {d : Nat}, d + 16 ≤ 268 → blockAtMem t₁.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) := fun h =>
    Proof.Ocb.blockAtMem_frame (rs := [⟨w64 p.W + BitVec.ofNat 64 268, 8⟩]) (by
      rw [m₁]
      have hm := List.mem_singleton_self (⟨w64 p.W + BitVec.ofNat 64 268, 8⟩ : Region)
      exact ((Frame.refl _ _).writeW hm _ (Offset.contains _ (e := 268) (k := 8) (d := 272) (n := 4) (by decide)
        (by decide) (by decide))).writeW hm _ (Offset.contains _ (e := 268) (k := 8) (d := 268) (n := 4) (by decide)
        (by decide) (by decide))) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  have F₀ : VG.Proof.AesOcb.X86.FillInv p ciph l a s₀ j c t₁ 0 :=
    { env := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
        (VG.Proof.AesOcb.X86.wR_mut (VG.Proof.AesOcb.X86.hashR_wR fr₁))
      frame := H.frame.trans fr₁
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      esi := by rw [g₁ _ (by decide), H.esi, Nat.add_zero]
      edi := by rw [g₁ _ (by decide), H.edi]
      ebx := by rw [g₁ _ (by decide), hbx, Nat.sub_zero]
      fp := by rw [slotv_eq, m₁, Mem.readW_writeW_self32]
      cnt := by
        rw [slotv_eq, m₁, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
          Mem.readW_writeW_self32]
      oh := by rw [kB₁ (by decide), H.oh, Nat.add_zero]
      buf := fun k hk => absurd hk (Nat.not_lt_zero _)
      sum := by rw [kB₁ (by decide), H.sum]
      hl := by rw [kW₁ (.inl (by decide)) (by decide), H.hl]
      rest := by rw [kW₁ (.inr (by decide)) (by decide), H.rest]
      l0 := by rw [kB₁ (by decide), H.l0] }
  exact ⟨t₁, run₁, F₀⟩

/-- A chunk of `c` blocks from `ebx`. -/
theorem chunkRest_ok (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : VG.Proof.AesOcb.X86.HCtx p ciph l a s₀) {t : State} {j c : Nat} (H : VG.Proof.AesOcb.X86.HInv p ciph l a s₀ t j) (hc0 : 0 < c) (hc : c ≤ 8)
    (hjc : j + c ≤ p.al / 16) (hbx : t.gpr .ebx = BitVec.ofNat 32 c) :
    WP isa (.seq (.block [.store (at_ .ebp cntO) .ebx, .mov .eax (.reg .ebp), .alu .add .eax (imm bufO),
          .store (at_ .ebp fpO) .eax])
        (.seq (.loop hashFill .ne)
          (.seq (callBlocks (VG.Proof.AesOcb.X86.callees v).enc [.mov .edx (.reg .ebp), .alu .add .edx (imm bufO), .mov .ebx (slot cntO)])
            (.seq hashSum
              (.block [.mov .eax (slot hlO), .alu .sub .eax (slot cntO), .store (at_ .ebp hlO) .eax]))))) t
      fun t' => VG.Proof.AesOcb.X86.HInv p ciph l a s₀ t' (j + c) ∧ t'.zf = some (decide (p.al / 16 - (j + c) = 0)) := by
  have L := C.lay
  have hal := L.al32
  obtain ⟨t₁, run₁, F₀⟩ := VG.Proof.AesOcb.X86.chunkStart_ok C H hbx
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.fill_ok C hc0 hc hjc F₀) fun t₂ F => ?_)
  -- the call
  have hcnt₂ := F.cnt
  simp only [slotv_eq] at hcnt₂
  have hargs : ∃ s₁, runBlock isa [.mov .edx (.reg .ebp), .alu .add .edx (imm bufO), .mov .ebx (slot cntO)] t₂ =
      some s₁ ∧ s₁.gpr .edx = p.W + BitVec.ofNat 32 bufO ∧ s₁.gpr .ebx = BitVec.ofNat 32 c ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = t₂.gpr r) ∧ s₁.mem = t₂.mem ∧
      s₁.rd = t₂.rd ∧ s₁.wr = t₂.wr :=
    ⟨_, by grun [F.env.ebp, L.aW, F.env.perm.wR, hcnt₂], by gregs [F.env.ebp], by gregs [hcnt₂],
      fun r _ h₂ _ h₄ => by gregs [h₂, h₄], by gmems [], by gmems [], by gmems []⟩
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L F.env hargs
    (DReg.w L F.env (d := bufO) (n := c) (by simp only [bufO, scrO]; omega) (.inr (.inr (.inr (by decide))))))
    fun t₃ P₃ => ?_)
  have aB : w64 (p.W + BitVec.ofNat 32 bufO) = w64 p.W + BitVec.ofNat 64 bufO := L.aW (by decide)
  have dis₃ : ∀ {d k : Nat}, d + k ≤ bufO → ∀ r ∈ [⟨w64 (p.W + BitVec.ofNat 32 bufO), 16 * c⟩,
      ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, VG.Proof.AesOcb.X86.stk p], (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [aB]; exact Lay.w_w (.inl h) (by simp only [bufO] at h; omega) (by simp only [bufO]; omega)
    · exact Lay.w_w (.inl (by simp only [bufO, scrO] at h ⊢; omega)) (by simp only [bufO] at h; omega) (by decide)
    · exact (L.bw' (by simp only [bufO] at h; omega)).symm
  have kB₃ : ∀ {d : Nat}, d + 16 ≤ bufO → blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 d) := fun h => Proof.Ocb.blockAtMem_frame P₃.frame (dis₃ h)
  have kW₃ : ∀ {d : Nat}, d + 4 ≤ bufO → slotv t₃.mem p.W d = slotv t₂.mem p.W d := fun h =>
    P₃.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 _, 4⟩) (Region.contains_self _ _) (dis₃ h) (by decide)
  have fr₃ : Frame (VG.Proof.AesOcb.X86.hashR p) t₂.mem t₃.mem := P₃.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [aB]; exact VG.Proof.AesOcb.X86.inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by simp only [bufO]; omega⟩)))))
    · exact VG.Proof.AesOcb.X86.inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩)))))
    · exact ⟨_, by simp, fun _ h => h⟩
  have hg : ∀ k < c, blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * k)) =
      ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)) := fun k hk => by
    have := P₃.enc hk
    rw [aB, VG.Proof.AesOcb.X86.add_ofNat_assoc] at this
    rw [this, F.buf k hk, C.ciph' (VG.Proof.AesOcb.X86.wR_mut (VG.Proof.AesOcb.X86.hashR_wR F.frame))]
  have hcnt₃ : slotv t₃.mem p.W cntO = BitVec.ofNat 32 c := by rw [kW₃ (by decide), F.cnt]
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.hashSum_ok L P₃.env hc0 hc hcnt₃ hg) fun t₄ ⟨fr₄, sum₄, g₄, rd₄, wr₄⟩ => ?_)
  have E₄ : VG.Proof.AesOcb.X86.Env p t₄ := P₃.env.mut L (by rw [g₄ _ (by decide) (by decide) (by decide), P₃.env.ebp])
    (by rw [g₄ _ (by decide) (by decide) (by decide), P₃.env.esp]) rd₄ wr₄
    (VG.Proof.AesOcb.X86.frame_toMut fr₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  have kW₄ : ∀ {d : Nat}, 64 ≤ d → d + 4 ≤ 2560 → slotv t₄.mem p.W d = slotv t₃.mem p.W d := fun h h' =>
    fr₄.readW (r := ⟨w64 p.W + BitVec.ofNat 64 _, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by simp only [sumO]; omega)) h' (by decide))
      (by decide)
  have kB₄ : ∀ {d : Nat}, (d + 16 ≤ sumO ∨ 64 ≤ d) → d + 16 ≤ 2560 → blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 d) := fun h h' =>
    Proof.Ocb.blockAtMem_frame fr₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (by simp only [sumO] at h ⊢; omega) h' (by decide)
  have hl₄ : t₄.mem.readW (w64 p.W + BitVec.ofNat 64 hlO) 32 = BitVec.ofNat 32 (p.al / 16 - j) := by
    rw [← slotv_eq, kW₄ (by decide) (by decide), kW₃ (by decide), F.hl]
  have cnt₄ : t₄.mem.readW (w64 p.W + BitVec.ofNat 64 cntO) 32 = BitVec.ofNat 32 c := by
    rw [← slotv_eq, kW₄ (by decide) (by decide), hcnt₃]
  obtain ⟨t₅, run₅, m₅, zf₅, g₅, rd₅, wr₅⟩ : ∃ t₅, runBlock isa [.mov .eax (slot hlO), .alu .sub .eax (slot cntO),
      .store (at_ .ebp hlO) .eax] t₄ = some t₅ ∧
      t₅.mem = t₄.mem.writeW (w64 p.W + BitVec.ofNat 64 hlO) (BitVec.ofNat 32 (p.al / 16 - (j + c))) ∧
      t₅.zf = some (decide (p.al / 16 - (j + c) = 0)) ∧
      (∀ r, r ≠ .eax → t₅.gpr r = t₄.gpr r) ∧ t₅.rd = t₄.rd ∧ t₅.wr = t₄.wr := by
    have e := VG.Proof.AesOcb.X86.sub32' (show c ≤ p.al / 16 - j by omega) (by omega)
    rw [show p.al / 16 - j - c = p.al / 16 - (j + c) by omega] at e
    refine ⟨_, by grun [E₄.ebp, L.aW, E₄.perm.wR, E₄.perm.wW, hl₄, cnt₄], by gmems [hl₄, cnt₄, e], ?_,
      fun r h => by gregs [h], by gmems [], by gmems []⟩
    gmems [hl₄, cnt₄, e]
    rw [VG.Proof.AesOcb.X86.beq_zero32 (by omega)]
  refine WP.of_runBlock ⟨t₅, run₅, ?_⟩
  have kB₅ : ∀ {d : Nat}, d + 16 ≤ hlO → blockAtMem t₅.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 d) := fun h => by
    rw [m₅]
    exact Proof.Ocb.blockAtMem_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl h) (by simp only [hlO] at h; omega) (by decide)
  have fr₅ : Frame (VG.Proof.AesOcb.X86.hashR p) t₄.mem t₅.mem := by
    rw [m₅]
    exact (Frame.refl _ _).writeW (by simp) _ (Offset.contains _ (e := 264) (k := 16) (d := 264) (n := 4) (by decide)
      (by decide) (by decide))
  refine ⟨⟨E₄.mut L (by rw [g₅ _ (by decide), E₄.ebp]) (by rw [g₅ _ (by decide), E₄.esp]) rd₅ wr₅
      (VG.Proof.AesOcb.X86.wR_mut (VG.Proof.AesOcb.X86.hashR_wR fr₅)), F.frame.trans (fr₃.trans ((fr₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans fr₅)),
      by rw [rd₅, rd₄, P₃.rd, F.rd], by rw [wr₅, wr₄, P₃.wr, F.wr], by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, zf₅⟩
  · rw [kB₅ (by decide), sum₄, kB₃ (by decide), F.sum, Proof.Ocb.hsum_add]
  · rw [kB₅ (by decide), kB₄ (.inr (by decide)) (by decide), kB₃ (by decide), F.oh]
  · rw [g₅ _ (by decide), g₄ _ (by decide) (by decide) (by decide), P₃.gpr _ (by decide) (by decide) (by decide)
      (by decide), F.esi]
  · rw [g₅ _ (by decide), g₄ _ (by decide) (by decide) (by decide), P₃.gpr _ (by decide) (by decide) (by decide)
      (by decide), F.edi]
  · rw [slotv_eq, m₅, Mem.readW_writeW_self32]
  · rw [slotv_eq, m₅, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), ← slotv_eq,
      kW₄ (by decide) (by decide), kW₃ (by decide), F.rest]
  · rw [kB₅ (by decide), kB₄ (.inr (by decide)) (by decide), kB₃ (by decide), F.l0]

theorem hashChunk_ok (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : VG.Proof.AesOcb.X86.HCtx p ciph l a s₀) {t : State} {j : Nat} (H : VG.Proof.AesOcb.X86.HInv p ciph l a s₀ t j) (hj : j < p.al / 16) :
    WP isa (hashChunk (VG.Proof.AesOcb.X86.callees v)) t fun t' =>
      VG.Proof.AesOcb.X86.HInv p ciph l a s₀ t' (j + min 8 (p.al / 16 - j)) ∧
        t'.zf = some (decide (p.al / 16 - (j + min 8 (p.al / 16 - j)) = 0)) := by
  unfold hashChunk
  refine VG.Proof.AesOcb.X86.seq_assoc (WP.seq (WP.mono (VG.Proof.AesOcb.X86.chunkHead_ok C H) fun t₁ ⟨H₁, bx⟩ =>
    VG.Proof.AesOcb.X86.chunkRest_ok v C H₁ (by omega) (by omega) (by omega) bx))

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.PadTo`. -/
section

/-!
# AES-OCB on x86: a padded block (`padTo`)

Untrusted: everything here is checked by Lean. `padTo d cO` writes `pad(S)`
(§4.1) of the `n < 16` bytes `S` at `esi`, `n` at `W + cO`, to `W + d`:
zeros, the bytes (`copyLoop`), and `0x80` after them (`padTo_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem pad)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 LoopPre CopyPost
  copyLoop_ok length_bytesAt)

/-- A buffer of `n` bytes at `S` that the code may read. -/
structure SBuf (p : VG.Proof.AesOcb.X86.Prm) (s : State) (S : BitVec 32) (n : Nat) : Prop where
  fit : S.toNat + n ≤ 2 ^ 32
  w : (⟨w64 S, n⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  rd : Covers [⟨w64 S, n⟩] (s.rd ++ s.wr)

theorem SBuf.of_eq {p : VG.Proof.AesOcb.X86.Prm} {s s' : State} {S : BitVec 32} {n : Nat} (h : VG.Proof.AesOcb.X86.SBuf p s S n) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesOcb.X86.SBuf p s' S n := ⟨h.fit, h.w, by rw [hrd, hwr]; exact h.rd⟩

/-- The head of `padTo`: `W + d` zeroed, the copy's arguments. -/
theorem padToHead_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {S : BitVec 32} {n d cO : Nat}
    (hd : d + 16 ≤ 2560) (hc : cO + 4 ≤ 2560) (hcd : cO + 4 ≤ d ∨ d + 16 ≤ cO)
    (hsi : s.gpr .esi = S) (hcnt : slotv s.mem p.W cO = BitVec.ofNat 32 n) :
    ∃ s₁, runBlock isa (zero4 d ++
      ([.mov .edi (.reg .esi), .mov .edx (.reg .ebp), .alu .add .edx (imm d), .mov .ecx (slot cO)] : List Instr)) s =
        some s₁ ∧
      s₁.mem = Proof.Cmac.zero4 s.mem (w64 p.W + BitVec.ofNat 64 d) ∧ s₁.gpr .edi = S ∧
      s₁.gpr .edx = p.W + BitVec.ofNat 32 d ∧ s₁.gpr .ecx = BitVec.ofNat 32 n ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have hz := VG.Proof.AesOcb.X86.zero4_fold s.mem p.W d
  have hcnt' : (Proof.Cmac.zero4 s.mem (w64 p.W + BitVec.ofNat 64 d)).readW (w64 p.W + BitVec.ofNat 64 cO) 32 =
      BitVec.ofNat 32 n := by
    rw [← hcnt, slotv_eq]
    exact (Proof.Cmac.frame_store4 _ _ _ _ _).readW (r := ⟨w64 p.W + BitVec.ofNat 64 cO, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w hcd hc hd) (by decide)
  exact ⟨_, by grun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hsi, hcnt', hz], by gmems [hz], by gregs [hsi],
    by gregs [E.ebp], by gregs [hcnt', hz], fun r h₁ h₂ h₃ h₄ => by gregs [h₁, h₂, h₃, h₄], by gmems [],
    by gmems []⟩

/-- `padTo d cO`: `W + d ← pad(S)`, for the `n` bytes `S` at `esi`, `0 < n < 16`. -/
theorem padTo_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {S : BitVec 32} {n d cO : Nat} (hn : 0 < n)
    (hn' : n < 16) (hd : d + 16 ≤ 2560) (hc : cO + 4 ≤ 2560) (hcd : cO + 4 ≤ d ∨ d + 16 ≤ cO)
    (hsi : s.gpr .esi = S) (hcnt : slotv s.mem p.W cO = BitVec.ofNat 32 n) (hS : VG.Proof.AesOcb.X86.SBuf p s S n) :
    WP isa (padTo d cO) s fun t => Frame [⟨w64 p.W + BitVec.ofNat 64 d, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) = pad (bytesAt s.mem (w64 S) n) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have aD : w64 (p.W + BitVec.ofNat 32 d) = w64 p.W + BitVec.ofNat 64 d := L.aW (by omega)
  obtain ⟨s₁, run₁, m₁, di₁, dx₁, cx₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.padToHead_ok L E hd hc hcd hsi hcnt
  have fr₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 d, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have eS : bytesAt s₁.mem (w64 S) n = bytesAt s.mem (w64 S) n :=
    Proof.AesGcm.X86.bytesAt_frame fr₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hS.w.sub_right (Lay.wSub hd)) (by omega)
  have lp : LoopPre s₁ S (p.W + BitVec.ofNat 32 d) n :=
    ⟨di₁, dx₁, cx₁, hn, by omega, hS.fit, by rw [L.nW (by omega)]; have := L.ww; omega,
      by rw [rd₁, wr₁]; exact hS.rd, by rw [aD, wr₁]; exact E.perm.wC (by omega),
      by rw [aD]; exact hS.w.sub_right (Lay.wSub (by omega))⟩
  unfold padTo
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (copyLoop_ok s₁ lp) fun s₂ P₂ => ?_)
  have aN : w64 (p.W + BitVec.ofNat 32 d + BitVec.ofNat 32 n + BitVec.ofNat 32 0) =
      w64 p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n := by
    rw [show p.W + BitVec.ofNat 32 d + BitVec.ofNat 32 n + BitVec.ofNat 32 0 = p.W + BitVec.ofNat 32 (d + n) by
      rw [BitVec.add_zero, Proof.AesGcm.X86.add_ofNat_assoc32], L.aW (by omega), VG.Proof.AesOcb.X86.add_ofNat_assoc]
  have w₂ : InRegions s₂.wr (w64 p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) 1 := by
    rw [P₂.wr, wr₁, VG.Proof.AesOcb.X86.add_ofNat_assoc]; exact E.perm.wW (by omega)
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa [.mov .eax (imm 0x80), .store8 (at_ .edx 0) .al] s₂ =
      some s₃ ∧ s₃.mem = s₂.mem.writeW (w64 p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) (0x80 : Byte) ∧
      (∀ r, r ≠ .eax → s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by grun [P₂.edx, aN, w₂], ?_, fun r h => by gregs [h], by gmems [], by gmems []⟩
    gmems [P₂.edx, aN]; rfl
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hlen : (bytesAt s.mem (w64 S) n).length = n := length_bytesAt _ _ _
  have key : s₃.mem = writeBytes s₁.mem (w64 p.W + BitVec.ofNat 64 d) (bytesAt s.mem (w64 S) n ++ [0x80]) := by
    rw [m₃, P₂.mem, eS, aD, writeBytes_snoc _ _ _ _ (by omega), hlen]
  refine ⟨?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, by rw [rd₃, P₂.rd, rd₁], by rw [wr₃, P₂.wr, wr₁]⟩
  · rw [key]
    refine fr₁.trans fun x hx => ?_
    exact writeBytes_frame _ _ _ (by
      simp only [List.length_append, hlen, List.length_singleton]; exact VG.Proof.AesOcb.X86.contains_pre _ (by omega)) x hx
  · rw [key, blockAtMem, Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by simp [hlen]; omega) (by decide), m₁,
      Proof.Cmac.zero4_bytes]
    simp only [pad, hlen, List.length_append, List.length_singleton, Spec.Cmac.zeros, Spec.Ocb.zeros,
      List.drop_replicate, List.append_assoc, List.singleton_append, show 16 - (n + 1) = 15 - n by omega]
  · rw [g₃ r h₁, P₂.other r h₁ h₄ h₃ h₂, g₁ r h₁ h₂ h₃ h₄]

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Hash`. -/
section

/-!
# AES-OCB on x86: `HASH` (`hash`)

Untrusted: everything here is checked by Lean. `hash` zeroes the sum and the
offset, keeps the number of whole blocks of the associated data and the
length of the rest in `W`, takes the whole blocks a chunk at a time
(`hashChunk_ok`), and the rest, padded, XORed with `Offset_m ⊕ L_*` and
enciphered (`hashRest_ok`): the sum is §4.1's `HASH(K, A)` (`hash_ok`,
`Proof.Ocb.hash_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt hsum)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off
  length_bytesAt)

/-- `L_*`, after a frame within `mutR`. -/
theorem lstar_mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.mutR p) m m') :
    ctxLstar m' (w64 p.K) = ctxLstar m (w64 p.K) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => (VG.Proof.AesOcb.X86.k_mut L r hr).sub_left (Offset.sub_base _ (by decide))

/-- The head of `hashRest`: `Offset_m ⊕ L_*` to `W + ohO`. -/
theorem hashRestHead_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) :
    ∃ t₂, runBlock isa (([.mov .ebx (slot ctxO)] : List Instr) ++ xor16 .ebx 240 ohO) t = some t₂ ∧ VG.Proof.AesOcb.X86.Env p t₂ ∧
      t₂.mem = VG.Proof.AesOcb.X86.xorMem16 t.mem (w64 p.K) 240 (w64 p.W) ohO ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → t₂.gpr r = t.gpr r) ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr := by
  have hc := E.slots.ctx
  simp only [slotv_eq] at hc
  obtain ⟨t₁, run₁, bx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .ebx (slot ctxO)] t = some t₁ ∧
      t₁.gpr .ebx = p.K ∧ (∀ r, r ≠ .ebx → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hc], by gregs [hc], fun r h => by gregs [h], by gmems [], by gmems [],
      by gmems []⟩
  have E₁ : VG.Proof.AesOcb.X86.Env p t₁ := E.keep (by rw [g₁ _ (by decide)]) (by rw [g₁ _ (by decide)]) rd₁ wr₁ m₁
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.xor16R_ok L E₁ (b := .ebx) (by decide) bx₁ L.kw L.k_w
    E₁.perm.k (s := 240) (d := ohO) (by decide) (by decide)
  refine ⟨t₂, runBlock_app_of run₁ run₂, E₁.mut L (by rw [g₂ _ (by decide), E₁.ebp])
    (by rw [g₂ _ (by decide), E₁.esp]) rd₂ wr₂
    (VG.Proof.AesOcb.X86.frame_toMut (by rw [m₂]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))),
    by rw [m₂, m₁], fun r h₁ h₂ => by rw [g₂ r h₁, g₁ r h₂], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- The padded rest of the associated data, after its `m` whole blocks. -/
theorem hashRest_ok (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : VG.Proof.AesOcb.X86.HCtx p ciph l a s₀) {t : State} (H : VG.Proof.AesOcb.X86.HInv p ciph l a s₀ t (p.al / 16)) (hr : 0 < p.al % 16) :
    WP isa (hashRest (VG.Proof.AesOcb.X86.callees v)) t fun t' => VG.Proof.AesOcb.X86.Env p t' ∧ Frame (VG.Proof.AesOcb.X86.hashR p) s₀.mem t'.mem ∧
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧
      t'.wr = s₀.wr := by
  have L := C.lay
  have E := H.env
  have hal := L.aw
  generalize hm : p.al / 16 = m at H
  -- `Offset_m ⊕ L_*`
  obtain ⟨t₂, run₂, E₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.hashRestHead_ok L E
  have fr₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem := by
    rw [m₂]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _
  have fH₂ : Frame (VG.Proof.AesOcb.X86.hashR p) s₀.mem t₂.mem := H.frame.trans (fr₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inHashR p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have oh₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [m₂, VG.Proof.AesOcb.X86.xorMem16_block, H.oh, ← C.lstar, ← VG.Proof.AesOcb.X86.lstar_mut L (VG.Proof.AesOcb.X86.wR_mut (VG.Proof.AesOcb.X86.hashR_wR H.frame))]; rfl
  -- `pad(A_*)`
  have si₂ : t₂.gpr .esi = p.A + BitVec.ofNat 32 (16 * m) := by rw [g₂ _ (by decide) (by decide), H.esi]
  have rest₂ : slotv t₂.mem p.W restO = BitVec.ofNat 32 (p.al % 16) := by
    rw [← H.rest]
    exact fr₂.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)
  have a16 : w64 (p.A + BitVec.ofNat 32 (16 * m)) = w64 p.A + BitVec.ofNat 64 (16 * m) := w64_add (by omega)
  have sub : Region.Sub ⟨w64 (p.A + BitVec.ofNat 32 (16 * m)), p.al % 16⟩ ⟨w64 p.A, p.al⟩ := by
    rw [a16]; exact Offset.sub_base _ (by omega)
  have hS : VG.Proof.AesOcb.X86.SBuf p t₂ (p.A + BitVec.ofNat 32 (16 * m)) (p.al % 16) := by
    refine ⟨?_, L.a_w.sub_left sub, ?_⟩
    · rw [toNat_add32 (by omega)]; omega
    · rw [a16]; exact covers_off E₂.perm.aad (by omega) (by omega)
  have hrestb : bytesAt t₂.mem (w64 (p.A + BitVec.ofNat 32 (16 * m))) (p.al % 16) = a.drop (16 * (a.length / 16)) := by
    rw [C.len, hm, ← C.aad, Proof.Ocb.bytesAt_drop _ _ (by omega), show p.al - 16 * m = p.al % 16 by omega, a16]
    have ad : ∀ r ∈ VG.Proof.AesOcb.X86.mutR p, (⟨w64 p.A, p.al⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact L.a_w.sub_right (Region.sub_prefix (by decide))
      · exact L.a_w.sub_right (Lay.wSub (by decide))
      · exact L.a_w.sub_right (Lay.wSub (by decide))
      · exact L.a_w.sub_right (Lay.wSub (by decide))
      · exact L.ba.symm
      · exact L.a_d
    exact Proof.AesGcm.X86.bytesAt_frame (VG.Proof.AesOcb.X86.wR_mut (VG.Proof.AesOcb.X86.hashR_wR fH₂))
      (fun r hr => (ad r hr).sub_left (Offset.sub_base _ (by omega))) (by omega)
  unfold hashRest
  refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.padTo_ok L E₂ (d := bufO) (cO := restO) hr (by omega) (by decide) (by decide)
    (.inl (by decide)) si₂ rest₂ hS) fun t₃ ⟨fr₃, pad₃, g₃, rd₃, wr₃⟩ => ?_)
  rw [hrestb] at pad₃
  have E₃ : VG.Proof.AesOcb.X86.Env p t₃ := E₂.mut L (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), E₂.ebp])
    (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), E₂.esp]) rd₃ wr₃
    (VG.Proof.AesOcb.X86.frame_toMut fr₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩))))
  have oh₃ : blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [Proof.Ocb.blockAtMem_frame fr₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide), oh₂]
  -- XORed with the offset
  obtain ⟨t₄, run₄, m₄, g₄, rd₄, wr₄⟩ := VG.Proof.AesOcb.X86.xor16W_ok L E₃ (s := ohO) (d := bufO) (by decide) (by decide)
    (.inl (by decide))
  have E₄ : VG.Proof.AesOcb.X86.Env p t₄ := E₃.mut L (by rw [g₄ _ (by decide), E₃.ebp]) (by rw [g₄ _ (by decide), E₃.esp]) rd₄ wr₄
    (VG.Proof.AesOcb.X86.frame_toMut (by rw [m₄]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩))))
  have buf₄ : blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 bufO) =
      pad (a.drop (16 * (a.length / 16))) ^^^ (offAt 0 l m ^^^ l) := by rw [m₄, VG.Proof.AesOcb.X86.xorMem16_block, pad₃, oh₃]
  have fH₄ : Frame (VG.Proof.AesOcb.X86.hashR p) s₀.mem t₄.mem := fH₂.trans ((fr₃.trans (by rw [m₄]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _)).sub
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.AesOcb.X86.inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩))))))
  refine WP.seq (WP.of_runBlock ⟨t₄, run₄, ?_⟩)
  -- enciphered
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E₄
    (VG.Proof.AesOcb.X86.oneBlock_ok E₄ bufO) (DReg.w L E₄ (d := bufO) (n := 1) (by decide) (.inr (.inr (.inr (by decide))))))
    fun t₅ P₅ => ?_)
  have aB : w64 (p.W + BitVec.ofNat 32 bufO) = w64 p.W + BitVec.ofNat 64 bufO := L.aW (by decide)
  have buf₅ : blockAtMem t₅.mem (w64 p.W + BitVec.ofNat 64 bufO) =
      ciph (pad (a.drop (16 * (a.length / 16))) ^^^ (offAt 0 l m ^^^ l)) := by
    have := P₅.enc (i := 0) (by decide)
    rw [aB, show w64 p.W + BitVec.ofNat 64 bufO + BitVec.ofNat 64 (16 * 0) = w64 p.W + BitVec.ofNat 64 bufO from
      BitVec.add_zero _] at this
    rw [this, buf₄, C.ciph' (VG.Proof.AesOcb.X86.wR_mut (VG.Proof.AesOcb.X86.hashR_wR fH₄))]
  have fH₅ : Frame (VG.Proof.AesOcb.X86.hashR p) s₀.mem t₅.mem := fH₄.trans (P₅.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [aB]; exact VG.Proof.AesOcb.X86.inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩)))))
    · exact VG.Proof.AesOcb.X86.inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩)))))
    · exact ⟨_, by simp, fun _ h => h⟩)
  have kS : ∀ {rs : List Region} {u u' : State}, Frame rs u.mem u'.mem →
      (∀ r ∈ rs, (⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint r) →
      blockAtMem u'.mem (w64 p.W + BitVec.ofNat 64 sumO) = blockAtMem u.mem (w64 p.W + BitVec.ofNat 64 sumO) :=
    fun h hd => Proof.Ocb.blockAtMem_frame h hd
  have sum₅ : blockAtMem t₅.mem (w64 p.W + BitVec.ofNat 64 sumO) = hsum ciph l a m := by
    rw [kS P₅.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [aB]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm),
      kS (u := t₃) (rs := [⟨w64 p.W + BitVec.ofNat 64 bufO, 16⟩]) (by rw [m₄]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)),
      kS fr₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)),
      kS (u := t) (rs := [⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩]) fr₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)),
      H.sum]
  -- added to the sum
  obtain ⟨t₆, run₆, m₆, g₆, rd₆, wr₆⟩ := VG.Proof.AesOcb.X86.xor16W_ok L P₅.env (s := bufO) (d := sumO) (by decide) (by decide)
    (.inr (by decide))
  refine WP.of_runBlock ⟨t₆, run₆, P₅.env.mut L (by rw [g₆ _ (by decide), P₅.env.ebp])
    (by rw [g₆ _ (by decide), P₅.env.esp]) rd₆ wr₆ (VG.Proof.AesOcb.X86.frame_toMut (by rw [m₆]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _)
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))),
    fH₅.trans (by
      rw [m₆]
      exact (VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inHashR p (.inl ⟨by decide, by decide⟩)), ?_,
    by rw [rd₆, P₅.rd, rd₄, rd₃, rd₂, H.rd], by rw [wr₆, P₅.wr, wr₄, wr₃, wr₂, H.wr]⟩
  rw [m₆, VG.Proof.AesOcb.X86.xorMem16_block, sum₅, buf₅, Proof.Ocb.hash_eq]
  simp only [C.len, hm]
  have hlen : (a.drop (16 * m)).length = p.al % 16 := by simp [C.len]; omega
  simp only [hlen, show p.al % 16 > 0 from hr, ↓reduceIte]

/-- After the whole blocks: the rest, if any. -/
theorem hashTail_ok (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : VG.Proof.AesOcb.X86.HCtx p ciph l a s₀) {t : State} (H : VG.Proof.AesOcb.X86.HInv p ciph l a s₀ t (p.al / 16)) :
    WP isa (.seq (.block [.mov .eax (slot restO), .alu .test .eax (.reg .eax)])
      (.ite .e (.block []) (hashRest (VG.Proof.AesOcb.X86.callees v)))) t fun t' => VG.Proof.AesOcb.X86.Env p t' ∧ Frame (VG.Proof.AesOcb.X86.hashR p) s₀.mem t'.mem ∧
        blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧
        t'.wr = s₀.wr := by
  have L := C.lay
  have rest := H.rest
  simp only [slotv_eq] at rest
  obtain ⟨t₁, run₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .eax (slot restO), .alu .test .eax (.reg .eax)] t =
      some t₁ ∧ t₁.zf = some (decide (p.al % 16 = 0)) ∧
      (∀ r, r ≠ .eax → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by grun [H.env.ebp, L.aW, H.env.perm.wR, rest], ?_, fun r h => by gregs [h], by gmems [], by gmems [],
      by gmems []⟩
    gmems [rest, BitVec.and_self, VG.Proof.AesOcb.X86.beq_zero32 (show p.al % 16 < 2 ^ 32 by omega)]
  have H₁ := H.of_keep (fun r h₁ _ _ _ => g₁ r h₁) m₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (p.al % 16 = 0)) (VG.Proof.AesOcb.X86.eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : p.al % 16 = 0 := of_decide_eq_true hb
    refine ⟨H₁.env, H₁.frame, ?_, H₁.rd, H₁.wr⟩
    rw [H₁.sum, Proof.Ocb.hash_eq, C.len]
    have hlen : (a.drop (16 * (p.al / 16))).length = 0 := by simp [C.len]; omega
    simp [hlen]
  · exact VG.Proof.AesOcb.X86.hashRest_ok v C H₁ (by have := of_decide_eq_false hb; omega)

theorem shr4_32 {v : Nat} (hv : v < 2 ^ 32) : BitVec.ofNat 32 v >>> 4 = BitVec.ofNat 32 (v / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat32 hv, toNat_ofNat32 (by omega), Nat.shiftRight_eq_div_pow]

/-- The start of `HASH`: the sum and the offset zeroed, the counts. -/
theorem hashHead_ok {p : VG.Proof.AesOcb.X86.Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86.HCtx p ciph l a s₀)
    (E : VG.Proof.AesOcb.X86.Env p s₀) (hl0 : blockAtMem s₀.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.block (zero4 sumO ++ zero4 ohO ++
      ([.mov .esi (slot aadO), .mov .eax (slot alenO), .mov .ecx (.reg .eax), .alu .and .ecx (imm 15),
       .store (at_ .ebp restO) .ecx, .shift .shr .eax 4, .store (at_ .ebp hlO) .eax, .mov .edi (imm 1),
       .alu .test .eax (.reg .eax)] : List Instr))) s₀ fun s =>
      VG.Proof.AesOcb.X86.HInv p ciph l a s₀ s 0 ∧ s.zf = some (decide (p.al / 16 = 0)) := by
  have L := C.lay
  have hal := L.al32
  have hA := E.slots.aad
  have hn := E.slots.alen
  simp only [slotv_eq] at hA hn
  have z₁ := VG.Proof.AesOcb.X86.zero4_fold s₀.mem p.W sumO
  have z₂ := VG.Proof.AesOcb.X86.zero4_fold (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO)) p.W ohO
  have fz : Frame [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩] s₀.mem
      (Proof.Cmac.zero4 (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO)) (w64 p.W + BitVec.ofNat 64 ohO)) :=
    ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp)).trans ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp))
  have rz : ∀ {d : Nat}, 176 ≤ d → d + 4 ≤ 2560 →
      (Proof.Cmac.zero4 (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO))
        (w64 p.W + BitVec.ofNat 64 ohO)).readW (w64 p.W + BitVec.ofNat 64 d) 32 =
      s₀.mem.readW (w64 p.W + BitVec.ofNat 64 d) 32 := fun h h' =>
    fz.readW (r := ⟨w64 p.W + BitVec.ofNat 64 _, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.w_w (.inr (by simp only [sumO, ohO]; omega)) h' (by decide)) (by decide)
  have hA' := (rz (d := aadO) (by decide) (by decide)).trans hA
  have hn' := (rz (d := alenO) (by decide) (by decide)).trans hn
  simp only [sumO, ohO, aadO, alenO, Nat.reduceAdd] at hA' hn'
  obtain ⟨s₁, run₁, m₁, si₁, di₁, zf₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa (zero4 sumO ++ zero4 ohO ++
      [.mov .esi (slot aadO), .mov .eax (slot alenO), .mov .ecx (.reg .eax), .alu .and .ecx (imm 15),
       .store (at_ .ebp restO) .ecx, .shift .shr .eax 4, .store (at_ .ebp hlO) .eax, .mov .edi (imm 1),
       .alu .test .eax (.reg .eax)]) s₀ = some s₁ ∧
      s₁.mem = ((Proof.Cmac.zero4 (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO))
        (w64 p.W + BitVec.ofNat 64 ohO)).writeW (w64 p.W + BitVec.ofNat 64 restO)
          (BitVec.ofNat 32 (p.al % 16))).writeW (w64 p.W + BitVec.ofNat 64 hlO) (BitVec.ofNat 32 (p.al / 16)) ∧
      s₁.gpr .esi = p.A ∧ s₁.gpr .edi = BitVec.ofNat 32 1 ∧ s₁.zf = some (decide (p.al / 16 = 0)) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₁.gpr r = s₀.gpr r) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
    refine ⟨_, by grun [zero4, E.ebp, L.aW, E.perm.wR, E.perm.wW, hA, hn, z₁, z₂, hA', hn'], ?_, by gregs [hA, hA'], by gregs [],
      ?_, fun r h₁ h₂ h₃ h₄ => by gregs [h₁, h₂, h₃, h₄], by gmems [], by gmems []⟩
    · gmems [hA', hn', z₁, z₂, VG.Proof.AesOcb.X86.and15_32 hal, VG.Proof.AesOcb.X86.shr4_32 hal]
    · gmems [hA', hn', z₁, z₂, VG.Proof.AesOcb.X86.shr4_32 hal, BitVec.and_self, VG.Proof.AesOcb.X86.beq_zero32 (show p.al / 16 < 2 ^ 32 by omega)]
  have F : Frame [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩] s₀.mem s₁.mem := by
    rw [m₁]
    have hm : (⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩ : Region) ∈ [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩,
        ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩] := by simp
    exact (((fz.mono (by simp)).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 276) (n := 4) (by decide)
      (by decide) (by decide))).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 264) (n := 4) (by decide)
      (by decide) (by decide)))
  have fH : Frame (VG.Proof.AesOcb.X86.hashR p) s₀.mem s₁.mem := F.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Proof.AesOcb.X86.inHashR p (.inl ⟨by decide, by decide⟩)
    · exact VG.Proof.AesOcb.X86.inHashR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact VG.Proof.AesOcb.X86.inHashR p (.inr (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩)))))
  have kz : ∀ {d : Nat}, d + 16 ≤ 264 → blockAtMem s₁.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem (Proof.Cmac.zero4 (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO))
        (w64 p.W + BitVec.ofNat 64 ohO)) (w64 p.W + BitVec.ofNat 64 d) := fun h => by
    rw [m₁]
    have hm := List.mem_singleton_self (⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩ : Region)
    exact Proof.Ocb.blockAtMem_frame (((Frame.refl _ _).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 276)
      (n := 4) (by decide) (by decide) (by decide))).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 264)
      (n := 4) (by decide) (by decide) (by decide))) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl h) (by omega) (by decide)
  refine WP.of_runBlock ⟨s₁, run₁, ⟨E.mut L (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd₁ wr₁ (VG.Proof.AesOcb.X86.wR_mut (VG.Proof.AesOcb.X86.hashR_wR fH)), fH,
      rd₁, wr₁, Nat.zero_le _, ?_, ?_, by rw [si₁]; exact (BitVec.add_zero _).symm, di₁, ?_, ?_, ?_⟩, zf₁⟩
  · have fz0 : ∀ (m : Mem) (c : Addr), Frame [⟨c, 16⟩] m (Proof.Cmac.zero4 m c) :=
      fun m c => Proof.Cmac.frame_store4 _ _ _ _ _
    rw [kz (by decide), Proof.Ocb.blockAtMem_frame (fz0 _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)),
      VG.Proof.AesOcb.X86.blockAtMem_zero4]; rfl
  · rw [kz (by decide), VG.Proof.AesOcb.X86.blockAtMem_zero4]; rfl
  · rw [slotv_eq, m₁, Mem.readW_writeW_self32, Nat.sub_zero]
  · rw [slotv_eq, m₁, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  · rw [kz (by decide), Proof.Ocb.blockAtMem_frame fz (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), hl0]

/-- The chunks of `HASH`, from the first. -/
theorem hashLoop_ok (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : VG.Proof.AesOcb.X86.HCtx p ciph l a s₀) {t : State} (H₀ : VG.Proof.AesOcb.X86.HInv p ciph l a s₀ t 0) (hm : 0 < p.al / 16) :
    WP isa (.loop (hashChunk (VG.Proof.AesOcb.X86.callees v)) .ne) t fun u => VG.Proof.AesOcb.X86.HInv p ciph l a s₀ u (p.al / 16) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ j, k = p.al / 16 - j ∧ j < p.al / 16 ∧ VG.Proof.AesOcb.X86.HInv p ciph l a s₀ u j) ?_
    (p.al / 16 - 0) _ ⟨0, rfl, hm, H₀⟩
  rintro k u ⟨j, rfl, hj, H⟩
  refine WP.mono (VG.Proof.AesOcb.X86.hashChunk_ok v C H hj) fun u' ⟨H', hz⟩ => ?_
  by_cases he : p.al / 16 - (j + min 8 (p.al / 16 - j)) = 0
  · left
    have hje : j + min 8 (p.al / 16 - j) = p.al / 16 := by omega
    exact ⟨(VG.Proof.AesOcb.X86.eval_ne hz).trans (by simp [he]), hje ▸ H'⟩
  · right
    exact ⟨(VG.Proof.AesOcb.X86.eval_ne hz).trans (by simp [he]), p.al / 16 - (j + min 8 (p.al / 16 - j)), by omega,
      j + min 8 (p.al / 16 - j), rfl, by omega, H'⟩

theorem hash_ok (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : VG.Proof.AesOcb.X86.HCtx p ciph l a s₀) (E : VG.Proof.AesOcb.X86.Env p s₀) (hl0 : blockAtMem s₀.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (Impl.AesOcb.X86.hash (VG.Proof.AesOcb.X86.callees v)) s₀ fun t' => VG.Proof.AesOcb.X86.Env p t' ∧ Frame (VG.Proof.AesOcb.X86.hashR p) s₀.mem t'.mem ∧
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧
      t'.wr = s₀.wr := by
  unfold Impl.AesOcb.X86.hash
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.hashHead_ok C E hl0) fun s₃ ⟨H₀, zf₃⟩ => ?_)
  refine WP.seq (WP.ite (decide (p.al / 16 = 0)) (VG.Proof.AesOcb.X86.eval_e zf₃) (fun hb => WP.block_nil ?_) (fun hb => ?_))
  · have h0 : p.al / 16 = 0 := of_decide_eq_true hb
    exact VG.Proof.AesOcb.X86.hashTail_ok v C (h0 ▸ H₀)
  · exact WP.mono (VG.Proof.AesOcb.X86.hashLoop_ok v C H₀ (Nat.pos_of_ne_zero (of_decide_eq_false hb))) fun u H => VG.Proof.AesOcb.X86.hashTail_ok v C H

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Pass`. -/
section

/-!
# AES-OCB on x86: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. `pass body` goes over the
`m` whole blocks of the data at `D`: for block `i` it computes
`Offset_{i+1}` (`lNtz_ok`, `xor16W_ok`), then runs `body` on the block, which
replaces it with `fB` of it and the offset, and the checksum with `fC` of
them (`BodyOk`: `xorOfs`, `addCk ++ xorOfs`, `xorOfs ++ addCk`); `pass_ok`
gives the blocks and the checksum after all `m`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off in_off
  in_left toNat_w64 add_ofNat_assoc32)

/-- A block of `B` that the code may read and write, apart from `W`. -/
structure BBlk (p : VG.Proof.AesOcb.X86.Prm) (t : State) (B : BitVec 32) : Prop where
  fit : B.toNat + 16 ≤ 2 ^ 32
  w : (⟨w64 B, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  wr : Covers [⟨w64 B, 16⟩] t.wr
  inm : VG.Proof.AesOcb.X86.InMut p [⟨w64 B, 16⟩]

theorem BBlk.of_eq {p : VG.Proof.AesOcb.X86.Prm} {t t' : State} {B : BitVec 32} (h : VG.Proof.AesOcb.X86.BBlk p t B) (hwr : t'.wr = t.wr) : VG.Proof.AesOcb.X86.BBlk p t' B :=
  ⟨h.fit, h.w, by rw [hwr]; exact h.wr, h.inm⟩

/-- A word of `W` after a word of a block `B` apart from it written. -/
theorem readW_BW {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {B : Addr}
    (hd : (⟨B, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) (m : Mem) (v : BitVec 32) {a b : Nat} (ha : a + 4 ≤ 2560)
    (hb : b + 4 ≤ 16) :
    (m.writeW (B + BitVec.ofNat 64 b) v).readW (w64 p.W + BitVec.ofNat 64 a) 32 =
      m.readW (w64 p.W + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (hd.symm.sep (Offset.contains_base _ ha (by have := L.ww; omega))
    (Offset.contains_base _ hb (by omega))) (by decide)

/-- What a body does to the block at `B` (in `esi`) and the checksum, with
the offset at `W + ofsO`. -/
def BodyOk (p : VG.Proof.AesOcb.X86.Prm) (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) : Prop :=
  ∀ (t : State) (B : BitVec 32), VG.Proof.AesOcb.X86.Env p t → t.gpr .esi = B → VG.Proof.AesOcb.X86.BBlk p t B →
    ∃ t', runBlock isa body t = some t' ∧
      blockAtMem t'.mem (w64 B) = fB (blockAtMem t.mem (w64 B)) (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)) ∧
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ckO) = fC (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO))
        (blockAtMem t.mem (w64 B)) (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)) ∧
      Frame [⟨w64 B, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] t.mem t'.mem ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr

theorem xorOfs_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) : VG.Proof.AesOcb.X86.BodyOk p xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t B E hsi hB
  have aB : ∀ {k : Nat}, k < 16 → w64 (B + BitVec.ofNat 32 k) = w64 B + BitVec.ofNat 64 k := fun hk =>
    w64_add (by have := hB.fit; omega)
  have rB : ∀ {k : Nat}, k + 4 ≤ 16 → InRegions (t.rd ++ t.wr) (w64 B + BitVec.ofNat 64 k) 4 := fun hk =>
    in_left (in_off hB.wr hk (by decide))
  have wB : ∀ {k : Nat}, k + 4 ≤ 16 → InRegions t.wr (w64 B + BitVec.ofNat 64 k) 4 := fun hk =>
    in_off hB.wr hk (by decide)
  obtain ⟨t', run, m', g', rd', wr'⟩ : ∃ t', runBlock isa xorOfs t = some t' ∧
      t'.mem = VG.Proof.AesOcb.X86.xor2Mem t.mem (w64 B) (w64 p.W + BitVec.ofNat 64 ofsO) (w64 B) ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
    refine ⟨_, by grun [xorOfs, List.flatMap_cons, List.flatMap_nil, hsi, aB, rB, wB, E.ebp, L.aW, E.perm.wR,
      (VG.Proof.AesOcb.X86.readW_BW L hB.w)], ?_, fun r h => by gregs [h], by gmems [], by gmems []⟩
    gmems [(VG.Proof.AesOcb.X86.readW_BW L hB.w)]
    simp only [VG.Proof.AesOcb.X86.xor2Mem, Proof.Cmac.store4, VG.Proof.AesOcb.X86.add_ofNat_assoc, Nat.reduceAdd,
      show w64 B + BitVec.ofNat 64 0 = w64 B from BitVec.add_zero _]
  have fB : Frame [⟨w64 B, 16⟩] t.mem t'.mem := by rw [m']; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine ⟨t', run, by rw [m', VG.Proof.AesOcb.X86.xor2Mem_block], ?_, fB.mono (by simp), g', rd', wr'⟩
  exact Proof.Ocb.blockAtMem_frame fB fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hB.w.sub_right (Lay.wSub (by decide))).symm

/-- `addCk`: the checksum XORed with the block at `B`. -/
theorem addCk_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {B : BitVec 32} (hsi : t.gpr .esi = B)
    (hB : VG.Proof.AesOcb.X86.BBlk p t B) :
    ∃ t', runBlock isa addCk t = some t' ∧
      t'.mem = VG.Proof.AesOcb.X86.xorMem16 t.mem (w64 B) 0 (w64 p.W) ckO ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr :=
  VG.Proof.AesOcb.X86.xor16R_ok L E (b := .esi) (by decide) hsi hB.fit hB.w (Proof.AesGcm.X86.covers_left hB.wr) (s := 0) (d := ckO) (by decide) (by decide)

theorem blockAtMem_ck {p : VG.Proof.AesOcb.X86.Prm} {B : BitVec 32} (hBW : (⟨w64 B, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) {m m' : Mem}
    (h : Frame [⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] m m') : blockAtMem m' (w64 B) = blockAtMem m (w64 B) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hBW.sub_right (Lay.wSub (by decide))

theorem blockAtMem_ofs_ck {p : VG.Proof.AesOcb.X86.Prm} {m m' : Mem} (h : Frame [⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] m m') :
    blockAtMem m' (w64 p.W + BitVec.ofNat 64 ofsO) = blockAtMem m (w64 p.W + BitVec.ofNat 64 ofsO) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)

theorem addCk_val (m : Mem) (B : BitVec 32) (W : BitVec 32) :
    blockAtMem (VG.Proof.AesOcb.X86.xorMem16 m (w64 B) 0 (w64 W) ckO) (w64 W + BitVec.ofNat 64 ckO) =
      blockAtMem m (w64 W + BitVec.ofNat 64 ckO) ^^^ blockAtMem m (w64 B) := by
  rw [VG.Proof.AesOcb.X86.xorMem16_block, show w64 B + BitVec.ofNat 64 0 = w64 B from BitVec.add_zero _]

/-- `seal`'s first pass: the checksum of the block, then the block XORed with the offset. -/
theorem sealPre_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) :
    VG.Proof.AesOcb.X86.BodyOk p (addCk ++ xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := by
  intro t B E hsi hB
  obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.addCk_ok L E hsi hB
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] t.mem t₁.mem := by rw [m₁]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _
  have E₁ : VG.Proof.AesOcb.X86.Env p t₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (VG.Proof.AesOcb.X86.frame_toMut f₁ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  obtain ⟨t₂, run₂, b₂, c₂, f₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.xorOfs_ok L t₁ B E₁ (by rw [g₁ _ (by decide), hsi]) (hB.of_eq wr₁)
  refine ⟨t₂, runBlock_app_of run₁ run₂, ?_, ?_, ?_, fun r h => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [b₂, VG.Proof.AesOcb.X86.blockAtMem_ck hB.w f₁, VG.Proof.AesOcb.X86.blockAtMem_ofs_ck f₁]
  · rw [c₂, m₁, VG.Proof.AesOcb.X86.addCk_val]
  · exact (f₁.mono (by simp)).trans f₂
  · rw [g₂ r h, g₁ r h]

/-- `open`'s third pass: the block XORed with the offset, then its checksum. -/
theorem openPost_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) :
    VG.Proof.AesOcb.X86.BodyOk p (xorOfs ++ addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := by
  intro t B E hsi hB
  obtain ⟨t₁, run₁, b₁, c₁, f₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.xorOfs_ok L t B E hsi hB
  have E₁ : VG.Proof.AesOcb.X86.Env p t₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (VG.Proof.AesOcb.X86.frame_toMut f₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hB.inm _ (List.mem_singleton_self _)
      · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.addCk_ok L E₁ (by rw [g₁ _ (by decide), hsi]) (hB.of_eq wr₁)
  have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] t₁.mem t₂.mem := by rw [m₂]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _
  refine ⟨t₂, runBlock_app_of run₁ run₂, ?_, ?_, ?_, fun r h => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [VG.Proof.AesOcb.X86.blockAtMem_ck hB.w f₂, b₁]
  · rw [m₂, VG.Proof.AesOcb.X86.addCk_val, c₁, b₁]
  · exact f₁.trans (f₂.mono (by simp))
  · rw [g₂ r h, g₁ r h]

/-- Block `i` of the data. -/
theorem dblk {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {i : Nat} (hi : 16 * (i + 1) ≤ p.n) :
    VG.Proof.AesOcb.X86.BBlk p t (p.D + BitVec.ofNat 32 (16 * i)) := by
  have hd := L.dw
  have a16 : w64 (p.D + BitVec.ofNat 32 (16 * i)) = w64 p.D + BitVec.ofNat 64 (16 * i) := w64_add (by omega)
  have sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * i)), 16⟩ ⟨w64 p.D, p.n⟩ := by
    rw [a16]; exact Offset.sub_base _ (by omega)
  refine ⟨by rw [toNat_add32 (by omega)]; omega, L.d_w.sub_left sub, ?_, fun r hr => ?_⟩
  · rw [a16]; exact covers_off E.perm.d (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, sub⟩

/-- A pass over the `m` whole blocks of the data (`X k` at its start, `t₀`),
after `i` of them. -/
structure PassInv (p : VG.Proof.AesOcb.X86.Prm) (m : Nat) (O0 l : Block) (X : Nat → Block) (fB : Block → Block → Block)
    (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : VG.Proof.AesOcb.X86.Env p t
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
    ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨w64 p.D, 16 * m⟩] t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  esi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * i)
  edi : t.gpr .edi = BitVec.ofNat 32 (i + 1)
  ebx : t.gpr .ebx = BitVec.ofNat 32 (m - i)
  ofs : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → t.gpr r = t₀.gpr r

theorem pass_step {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : VG.Proof.AesOcb.X86.BodyOk p body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) {t : State} {i : Nat} (hi : i < m)
    (P : VG.Proof.AesOcb.X86.PassInv p m O0 l X fB ckF t₀ t i) :
    WP isa (.seq nextOffset (.block (body ++ nextBlock))) t fun t' =>
      VG.Proof.AesOcb.X86.PassInv p m O0 l X fB ckF t₀ t' (i + 1) ∧ t'.zf = some (decide (m - (i + 1) = 0)) := by
  have hn := L.n32
  have hd := L.dw
  have a16 : ∀ k, 16 * (k + 1) ≤ p.n → w64 (p.D + BitVec.ofNat 32 (16 * k)) = w64 p.D + BitVec.ofNat 64 (16 * k) :=
    fun k hk => w64_add (by omega)
  unfold nextOffset
  refine WP.seq (WP.seq (WP.mono (VG.Proof.AesOcb.X86.lNtz_ok L P.env (by omega) (by omega) P.edi P.l0) fun t₁ P₁ => ?_))
  have E₁ := P₁.env L P.env
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.xor16W_ok L E₁ (s := lO) (d := ofsO) (by decide) (by decide)
    (.inr (by decide))
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  have E₂ : VG.Proof.AesOcb.X86.Env p t₂ := E₁.mut L (by rw [g₂ _ (by decide), E₁.ebp]) (by rw [g₂ _ (by decide), E₁.esp]) rd₂ wr₂
    (VG.Proof.AesOcb.X86.frame_toMut (by rw [m₂]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  have g₂' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₂.gpr r = t.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₂ r h₁, P₁.gpr r h₁ h₂ h₃]
  have fW₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
      ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp).trans (by
      rw [m₂]
      exact (VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _).mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; simp)
  have kW₂ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩ → blockAtMem t₂.mem Q = blockAtMem t.mem Q :=
    fun hQ => Proof.Ocb.blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hQ.sub_right (Lay.wSub (by decide))
  have ofs₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [m₂, VG.Proof.AesOcb.X86.xorMem16_block, Proof.Ocb.blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), P.ofs, P₁.val]
    rfl
  have ck₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF i := by
    rw [Proof.Ocb.blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), P.ck]
  have hBi := VG.Proof.AesOcb.X86.dblk L E₂ (i := i) (by omega)
  have Bi₂ : blockAtMem t₂.mem (w64 (p.D + BitVec.ofNat 32 (16 * i))) = X i := by
    rw [kW₂ hBi.w, a16 i (by omega), P.blk i hi]; simp
  obtain ⟨t₃, run₃, blk₃, ck₃, fr₃, g₃, rd₃, wr₃⟩ := hB t₂ _ E₂
    (by rw [g₂' _ (by decide) (by decide) (by decide), P.esi]) hBi
  have g₃' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₃.gpr r = t.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₃ r h₁, g₂' r h₁ h₂ h₃]
  have si₃ : t₃.gpr .esi = p.D + BitVec.ofNat 32 (16 * i) := by rw [g₃' _ (by decide) (by decide) (by decide), P.esi]
  have di₃ : t₃.gpr .edi = BitVec.ofNat 32 (i + 1) := by rw [g₃' _ (by decide) (by decide) (by decide), P.edi]
  have bx₃ : t₃.gpr .ebx = BitVec.ofNat 32 (m - i) := by rw [g₃' _ (by decide) (by decide) (by decide), P.ebx]
  obtain ⟨t₄, run₄, si₄, di₄, bx₄, zf₄, g₄, m₄, rd₄, wr₄⟩ : ∃ t₄, runBlock isa nextBlock t₃ = some t₄ ∧
      t₄.gpr .esi = p.D + BitVec.ofNat 32 (16 * (i + 1)) ∧ t₄.gpr .edi = BitVec.ofNat 32 (i + 1 + 1) ∧
      t₄.gpr .ebx = BitVec.ofNat 32 (m - (i + 1)) ∧ t₄.zf = some (decide (m - (i + 1) = 0)) ∧
      (∀ r, r ≠ .ebx → r ≠ .esi → r ≠ .edi → t₄.gpr r = t₃.gpr r) ∧ t₄.mem = t₃.mem ∧ t₄.rd = t₃.rd ∧
      t₄.wr = t₃.wr := by
    refine ⟨_, by grun [nextBlock], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [],
      by gmems []⟩
    · gregs [si₃]; rw [add_ofNat_assoc32, show 16 * i + 16 = 16 * (i + 1) by omega]
    · gregs [di₃]; rw [← BitVec.ofNat_add]
    · gregs [bx₃]; rw [VG.Proof.AesOcb.X86.sub1_32 (by omega) (by omega), show m - i - 1 = m - (i + 1) by omega]
    · gmems [bx₃]
      rw [VG.Proof.AesOcb.X86.sub1_32 (by omega) (by omega), VG.Proof.AesOcb.X86.beq_zero32 (by omega)]
      exact congrArg some (decide_eq_decide.mpr (by omega))
  refine WP.of_runBlock ⟨t₄, runBlock_app_of run₃ run₄, ?_⟩
  have kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨w64 (p.D + BitVec.ofNat 32 (16 * i)), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩ → blockAtMem t₃.mem Q = blockAtMem t.mem Q := fun h₁ h₂ => by
    rw [Proof.Ocb.blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂.sub_right (Lay.wSub (by decide))), kW₂ h₂]
  have kW₃ : ∀ {d : Nat}, (d + 16 ≤ ckO ∨ ckO + 16 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 d) := fun h h' =>
    Proof.Ocb.blockAtMem_frame fr₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hBi.w.sub_right (Lay.wSub h')).symm
      · exact Lay.w_w h h' (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_, si₄, di₄, bx₄, ?_, ?_, fun k hk => ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ => ?_⟩, zf₄⟩
  · exact E₂.mut L (by rw [g₄ _ (by decide) (by decide) (by decide), g₃ _ (by decide), E₂.ebp])
      (by rw [g₄ _ (by decide) (by decide) (by decide), g₃ _ (by decide), E₂.esp]) (by rw [rd₄, rd₃])
      (by rw [wr₄, wr₃]) (VG.Proof.AesOcb.X86.frame_toMut (by rw [m₄]; exact fr₃) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hBi.inm _ (List.mem_singleton_self _)
        · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  · rw [m₄]
    exact P.frame.trans ((fW₂.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp).trans
      (fr₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨w64 p.D, 16 * m⟩, by simp, by rw [a16 i (by omega)]; exact Offset.sub_base _ (by omega)⟩
        · exact ⟨_, by simp, fun _ h => h⟩))
  · rw [rd₄, rd₃, rd₂, P₁.rd, P.rd]
  · rw [wr₄, wr₃, wr₂, P₁.wr, P.wr]
  · rw [m₄, kW₃ (.inl (by decide)) (by decide), ofs₂]
  · rw [m₄, ck₃, ck₂, Bi₂, ofs₂, hckF i hi]
  · rw [m₄]
    by_cases hki : k = i
    · subst hki
      rw [← a16 k (by omega), blk₃, Bi₂, ofs₂]; simp
    · have hBk := VG.Proof.AesOcb.X86.dblk L E₂ (i := k) (by omega)
      rw [← a16 k (by omega), kB₃ (by
        rw [a16 k (by omega), a16 i (by omega)]; exact Offset.disjoint _ (by omega) (by omega) (by omega)) hBk.w,
        a16 k (by omega), P.blk k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]
  · rw [m₄, kW₃ (.inr (by decide)) (by decide), Proof.Ocb.blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), P.l0]
  · rw [g₄ r h₂ h₅ h₆, g₃' r h₁ h₃ h₄, P.gpr r h₁ h₂ h₃ h₄ h₅ h₆]

theorem pass_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : VG.Proof.AesOcb.X86.BodyOk p body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) (hm0 : 0 < m) {t : State} (P : VG.Proof.AesOcb.X86.PassInv p m O0 l X fB ckF t₀ t 0) :
    WP isa (pass body) t (fun t' => VG.Proof.AesOcb.X86.PassInv p m O0 l X fB ckF t₀ t' m) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ VG.Proof.AesOcb.X86.PassInv p m O0 l X fB ckF t₀ u i) ?_ (m - 0) _
    ⟨0, rfl, hm0, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (VG.Proof.AesOcb.X86.pass_step L hB hckF hm hi P) fun u' ⟨P', hz⟩ => ?_
  by_cases he : m - (i + 1) = 0
  · left
    exact ⟨(VG.Proof.AesOcb.X86.eval_ne hz).trans (by simp [he]), (show i + 1 = m by omega) ▸ P'⟩
  · right
    exact ⟨(VG.Proof.AesOcb.X86.eval_ne hz).trans (by simp [he]), m - (i + 1), by omega, i + 1, rfl, by omega, P'⟩

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Whole`. -/
section

/-!
# AES-OCB on x86: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs the
first pass (each block XORed with its offset, `pre`), `f` on all the blocks
(`ENCIPHER` or `DECIPHER`), and the second pass from `Offset_0` again
(`post`), each pass also updating the checksum (`whole_ok`): block `k`
becomes `Offset_{k+1} ⊕ g(X_k ⊕ Offset_{k+1})`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz ctxCiph ctxInv)
open VG.Proof.Ocb (offAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off in_off
  in_left toNat_w64 add_ofNat_assoc32)

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, `i`, the
working space of the functions called, the stack and the data. -/
abbrev wholeR (p : VG.Proof.AesOcb.X86.Prm) (k : Nat) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 ofsO, 32⟩, ⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
    VG.Proof.AesOcb.X86.wC p.W, VG.Proof.AesOcb.X86.stk p, ⟨w64 p.D, 16 * k⟩]

theorem wholeR_mut {p : VG.Proof.AesOcb.X86.Prm} {k : Nat} (hk : 16 * k ≤ p.n) {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.wholeR p k) m m') :
    Frame (VG.Proof.AesOcb.X86.mutR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact VG.Proof.AesOcb.X86.inMut_stk p
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

/-- The `m` blocks of the data, for a call. -/
theorem DReg.d {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {m : Nat} (hm : 16 * m ≤ p.n) : VG.Proof.AesOcb.X86.DReg p s p.D m := by
  have hd := L.dw
  have sub : Region.Sub ⟨w64 p.D, 16 * m⟩ ⟨w64 p.D, p.n⟩ := Region.sub_prefix hm
  refine ⟨by omega, (L.k_d.sub_left (Region.sub_prefix (by decide))).sub_right sub,
    (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide)), L.bd.sub_right sub, VG.Proof.AesOcb.X86.covers_prefix E.perm.d hm,
    fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, by simp, sub⟩

/-- `DECIPHER` with the key context, after a frame within `mutR`. -/
theorem ctxInv_mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.mutR p) m m') :
    ctxInv m' (w64 p.K) p.R = ctxInv m (w64 p.K) p.R := by
  unfold ctxInv
  have hb := L.rounds_le
  rw [Proof.AesGcm.X86.bytesAt_frame h (fun r hr => (VG.Proof.AesOcb.X86.k_mut L r hr).sub_left (Region.sub_prefix (by omega)))
    (by omega)]

/-- `passStart`: the data, its `m` whole blocks, `i = 1`. -/
theorem passStart_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {m : Nat}
    (hnb : slotv t.mem p.W nbO = BitVec.ofNat 32 m) :
    ∃ t', runBlock isa passStart t = some t' ∧ t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * 0) ∧
      t'.gpr .ebx = BitVec.ofNat 32 (m - 0) ∧ t'.gpr .edi = BitVec.ofNat 32 (0 + 1) ∧
      (∀ r, r ≠ .ebx → r ≠ .esi → r ≠ .edi → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  have hD := E.slots.data
  simp only [slotv_eq] at hD hnb
  exact ⟨_, by grun [passStart, E.ebp, L.aW, E.perm.wR, hD, hnb], by gregs [hD]; exact (BitVec.add_zero _).symm,
    by gregs [hnb, Nat.sub_zero], by gregs [], fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [],
    by gmems []⟩

/-- What `whole` leaves. -/
structure WholePost (p : VG.Proof.AesOcb.X86.Prm) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.X86.Env p t'
  frame : Frame (VG.Proof.AesOcb.X86.wholeR p m) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ckO) = ck

theorem whole_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : VG.Proof.AesOcb.X86.Prm} {G : Mem → Cipher}
    (hcall : ∀ {s s' : State} {D : BitVec 32} {n : Nat}, VG.Proof.AesOcb.X86.CallPost p f D n s s' → ∀ i < n,
      blockAtMem s'.mem (w64 D + BitVec.ofNat 64 (16 * i)) = G s.mem (blockAtMem s.mem (w64 D + BitVec.ofNat 64 (16 * i))))
    (hG : ∀ {m m' : Mem}, Frame (VG.Proof.AesOcb.X86.mutR p) m m' → G m' = G m)
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : VG.Proof.AesOcb.X86.BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : VG.Proof.AesOcb.X86.BodyOk p post (fun b o => b ^^^ o) fC2)
    (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {m : Nat} (hmn : 16 * m ≤ p.n) (hm0 : 0 < m)
    {O0 l : Block} (hnb : slotv t.mem p.W nbO = BitVec.ofNat 32 m)
    (hofs : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i < m, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 m)
    (hckF2 : ∀ i < m, ckF2 (i + 1) = fC2 (ckF2 i)
      (G t.mem (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1))) (offAt O0 l (i + 1))) :
    WP isa (whole fn pre post) t (VG.Proof.AesOcb.X86.WholePost p m O0 l
      (fun k => G t.mem (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 m) t) := by
  have hn := L.n32
  -- the first pass
  obtain ⟨s₁, run₁, si₁, bx₁, di₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.passStart_ok L E hnb
  have E₁ : VG.Proof.AesOcb.X86.Env p s₁ := E.keep (by rw [g₁ _ (by decide) (by decide) (by decide)])
    (by rw [g₁ _ (by decide) (by decide) (by decide)]) rd₁ wr₁ m₁
  have P₀ : VG.Proof.AesOcb.X86.PassInv p m O0 l (fun k => blockAtMem s₁.mem (w64 p.D + BitVec.ofNat 64 (16 * k))) (fun b o => b ^^^ o)
      ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, esi := si₁, edi := di₁, ebx := bx₁
      ofs := by rw [m₁, hofs]; rfl
      ck := by rw [m₁, hck]
      blk := fun k _ => by simp
      l0 := by rw [m₁, hl0]
      gpr := fun _ _ _ _ _ _ _ => rfl }
  unfold whole
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.pass_ok L hB1 (fun i hi => by rw [hckF1 i hi, m₁]) hmn hm0 P₀) fun s₂ P₂ => ?_)
  have fP₂ : Frame (VG.Proof.AesOcb.X86.mutR p) s₁.mem s₂.mem := P₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))
    · exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))
    · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))
    · exact ⟨_, by simp, Region.sub_prefix hmn⟩
  -- the call
  have hD₂ := P₂.env.slots.data
  have hnb₂' : slotv s₂.mem p.W nbO = BitVec.ofNat 32 m := by
    rw [← m₁] at hnb
    rw [← hnb]
    exact P₂.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact ((L.d_w.sub_left (Region.sub_prefix hmn)).sub_right (Lay.wSub (by decide))).symm) (by decide)
  simp only [slotv_eq] at hD₂ hnb₂'
  have hargs : ∃ s₁, runBlock isa [.mov .edx (slot dataO), .mov .ebx (slot nbO)] s₂ = some s₁ ∧
      s₁.gpr .edx = p.D ∧ s₁.gpr .ebx = BitVec.ofNat 32 m ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = s₂.gpr r) ∧ s₁.mem = s₂.mem ∧
      s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr :=
    ⟨_, by grun [P₂.env.ebp, L.aW, P₂.env.perm.wR, hD₂, hnb₂'], by gregs [hD₂], by gregs [hnb₂'],
      fun r _ h₂ _ h₄ => by gregs [h₂, h₄], by gmems [], by gmems [], by gmems []⟩
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.callBlocks_ok ok nosp stack L P₂.env hargs (DReg.d L P₂.env hmn)) fun s₃ P₃ => ?_)
  have E₃ := P₃.env
  -- what the call keeps
  have kC : ∀ {d k : Nat}, d + k ≤ scrO → (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨w64 p.D, 16 * m⟩ →
      ∀ r ∈ [⟨w64 p.D, 16 * m⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, VG.Proof.AesOcb.X86.stk p],
        (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h hD r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hD
    · exact Lay.w_w (.inl h) (by simp only [scrO] at h; omega) (by decide)
    · exact (L.bw' (by simp only [scrO] at h; omega)).symm
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨w64 p.D, 16 * m⟩ :=
    fun h => ((L.d_w.sub_left (Region.sub_prefix hmn)).sub_right (Lay.wSub h)).symm
  -- the blocks and slots of `W` the first pass and the call keep
  have kP : ∀ {d : Nat}, (d + 16 ≤ ofsO ∨ (48 ≤ d ∧ d + 16 ≤ lO) ∨ (112 ≤ d ∧ d + 16 ≤ kO) ∨ 224 ≤ d) →
      d + 16 ≤ scrO → blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun h₁ h₂ => by
      rw [Proof.Ocb.blockAtMem_frame P₃.frame (kC h₂ (dW (by simp only [scrO] at h₂; omega))),
        Proof.Ocb.blockAtMem_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₁ ⊢; omega) (by simp only [scrO] at h₂; omega) (by decide)
        · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₁ ⊢; omega) (by simp only [scrO] at h₂; omega) (by decide)
        · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₁ ⊢; omega) (by simp only [scrO] at h₂; omega) (by decide)
        · exact Lay.w_w (by simp only [ofsO, lO, kO, ckO] at h₁ ⊢; omega) (by simp only [scrO] at h₂; omega)
            (by decide)
        · exact dW (by simp only [scrO] at h₂; omega))]
  have o0₃ : blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0 := by rw [kP (by decide) (by decide), m₁, ho0]
  have ck₃ : blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [Proof.Ocb.blockAtMem_frame P₃.frame (kC (by decide) (dW (by decide))), P₂.ck, hckF2₀]
  have nb₃ : slotv s₃.mem p.W nbO = BitVec.ofNat 32 m := by
    rw [slotv_eq, ← hnb₂']
    exact P₃.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _)
      (kC (by decide) (dW (by decide))) (by decide)
  -- `Offset_0` again
  obtain ⟨s₄a, run₄a, m₄a, g₄a, rd₄a, wr₄a⟩ := VG.Proof.AesOcb.X86.copy16_ok L E₃ (s := o0O) (d := ofsO) (by decide) (by decide)
    (.inr (by decide))
  have f₄a : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩] s₃.mem s₄a.mem := by
    rw [m₄a]; exact VG.Proof.AesOcb.X86.copyMem16_frame _ _ _ _ _
  have E₄a : VG.Proof.AesOcb.X86.Env p s₄a := E₃.mut L (by rw [g₄a _ (by decide), E₃.ebp]) (by rw [g₄a _ (by decide), E₃.esp]) rd₄a wr₄a
    (VG.Proof.AesOcb.X86.frame_toMut f₄a fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  have nb₄a : slotv s₄a.mem p.W nbO = BitVec.ofNat 32 m := by
    rw [slotv_eq, ← nb₃, slotv_eq]
    exact f₄a.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)
  obtain ⟨s₄, run₄, si₄, bx₄, di₄, g₄, m₄, rd₄, wr₄⟩ := VG.Proof.AesOcb.X86.passStart_ok L E₄a nb₄a
  have E₄ : VG.Proof.AesOcb.X86.Env p s₄ := E₄a.keep (by rw [g₄ _ (by decide) (by decide) (by decide)])
    (by rw [g₄ _ (by decide) (by decide) (by decide)]) rd₄ wr₄ m₄
  have kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩ → blockAtMem s₄.mem Q = blockAtMem s₃.mem Q :=
    fun hQ => by
      rw [m₄]; exact Proof.Ocb.blockAtMem_frame f₄a fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hQ.sub_right (Lay.wSub (by decide))
  have hG₂ : G s₂.mem = G t.mem := by rw [hG fP₂, m₁]
  have X₄ : ∀ k < m, blockAtMem s₄.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) =
      G t.mem (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) := fun k hk => by
    have hBk := VG.Proof.AesOcb.X86.dblk L E₄ (i := k) (by omega)
    rw [← w64_add (show p.D.toNat + 16 * k < 2 ^ 32 by have := L.dw; omega), kB₄ hBk.w,
      w64_add (show p.D.toNat + 16 * k < 2 ^ 32 by have := L.dw; omega), hcall P₃ k hk, hG₂, P₂.blk k hk]
    simp only [hk, ↓reduceIte, m₁]
  have P₀' : VG.Proof.AesOcb.X86.PassInv p m O0 l (fun k => blockAtMem s₄.mem (w64 p.D + BitVec.ofNat 64 (16 * k))) (fun b o => b ^^^ o)
      ckF2 s₄ s₄ 0 :=
    { env := E₄, frame := Frame.refl _ _, rd := rfl, wr := rfl, esi := si₄, edi := di₄, ebx := bx₄
      ofs := by rw [m₄, m₄a, VG.Proof.AesOcb.X86.copyMem16_block, o0₃]; rfl
      ck := by
        rw [m₄, Proof.Ocb.blockAtMem_frame f₄a (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)),
          ck₃]
      blk := fun k _ => by simp
      l0 := by
        rw [m₄, Proof.Ocb.blockAtMem_frame f₄a (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)),
          kP (by decide) (by decide), m₁, hl0]
      gpr := fun _ _ _ _ _ _ _ => rfl }
  refine WP.seq (WP.of_runBlock ⟨s₄, runBlock_app_of run₄a run₄, ?_⟩)
  refine WP.mono (VG.Proof.AesOcb.X86.pass_ok L hB2 (fun i hi => by rw [hckF2 i hi, X₄ i hi]) hmn hm0 P₀') fun s₅ P₅ => ?_
  have subP : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
      ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨w64 p.D, 16 * m⟩],
      ∃ r' ∈ VG.Proof.AesOcb.X86.wholeR p m, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨_, by simp, Offset.sub _ (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨⟨w64 p.D, 16 * m⟩, by simp, fun _ h => h⟩
  refine ⟨P₅.env, ?_, by rw [P₅.rd, rd₄, rd₄a, P₃.rd, P₂.rd, rd₁], by rw [P₅.wr, wr₄, wr₄a, P₃.wr, P₂.wr, wr₁],
    fun k hk => ?_, P₅.ofs, P₅.ck⟩
  · rw [← m₁]
    refine (P₂.frame.sub subP).trans ((P₃.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨w64 p.D, 16 * m⟩, by simp, fun _ h => h⟩
      · exact ⟨VG.Proof.AesOcb.X86.wC p.W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨VG.Proof.AesOcb.X86.stk p, by simp, fun _ h => h⟩
    · have F₅ := P₅.frame
      rw [m₄] at F₅
      exact (f₄a.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, by simp, Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩).trans
        (F₅.sub subP)
  · rw [P₅.blk k hk]
    simp only [hk, ↓reduceIte]
    rw [X₄ k hk]

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.RestTag`. -/
section

/-!
# AES-OCB on x86: the rest of the data and the tag (`rest`, `tag`)

Untrusted: everything here is checked by Lean. `rest` computes
`Offset_* = Offset_m ⊕ L_*` and `Pad = ENCIPHER(K, Offset_*)` (`restHead_ok`),
then for `seal` adds `pad(P_*)` to the checksum (`padCk_ok`) and XORs `P_*`
with `Pad` (`xorPad_ok`), and for `open` XORs `C_*` with `Pad` and adds the
padded result to the checksum (`rest_ok`). `tag d` writes
`ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)` to `W + d` (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem pad ctxCiph ctxLstar)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot xorLoop)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off in_off
  in_left toNat_w64 add_ofNat_assoc32 length_bytesAt XorPre XorPost xorLoop_ok)

/-- `r` bytes of the data at `P` (in `esi`), `0 < r < 16`. -/
structure RBuf (p : VG.Proof.AesOcb.X86.Prm) (s : State) (P : BitVec 32) (r : Nat) : Prop where
  fit : P.toNat + r ≤ 2 ^ 32
  w : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  stk : (VG.Proof.AesOcb.X86.stk p).Disjoint ⟨w64 P, r⟩
  wr : Covers [⟨w64 P, r⟩] s.wr
  inm : VG.Proof.AesOcb.X86.InMut p [⟨w64 P, r⟩]

theorem RBuf.of_eq {p : VG.Proof.AesOcb.X86.Prm} {s s' : State} {P : BitVec 32} {r : Nat} (h : VG.Proof.AesOcb.X86.RBuf p s P r) (hwr : s'.wr = s.wr) :
    VG.Proof.AesOcb.X86.RBuf p s' P r := ⟨h.fit, h.w, h.stk, by rw [hwr]; exact h.wr, h.inm⟩

theorem RBuf.sbuf {p : VG.Proof.AesOcb.X86.Prm} {s : State} {P : BitVec 32} {r : Nat} (h : VG.Proof.AesOcb.X86.RBuf p s P r) : VG.Proof.AesOcb.X86.SBuf p s P r :=
  ⟨h.fit, h.w, Proof.AesGcm.X86.covers_left h.wr⟩

/-- `xorPad`: the `r` bytes at `P` (in `esi`), `0 < r < 16`, XORed with the
first `r` bytes at `W + tmpO`. -/
theorem xorPad_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {P : BitVec 32} {r : Nat} (hr : 0 < r)
    (hr' : r < 16) (hsi : s.gpr .esi = P) (hcnt : slotv s.mem p.W restO = BitVec.ofNat 32 r) (hP : VG.Proof.AesOcb.X86.RBuf p s P r) :
    WP isa xorPad s fun t => t.mem = writeBytes s.mem (w64 P)
        (Spec.Ocb.xor (bytesAt s.mem (w64 P) r) (bytesAt s.mem (w64 p.W + BitVec.ofNat 64 tmpO) r)) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  simp only [slotv_eq] at hcnt
  obtain ⟨s₁, run₁, di₁, dx₁, cx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .edi (.reg .esi), .mov .edx (.reg .ebp),
      .alu .add .edx (imm tmpO), .mov .ecx (slot restO)] s = some s₁ ∧ s₁.gpr .edi = P ∧
      s₁.gpr .edx = p.W + BitVec.ofNat 32 tmpO ∧ s₁.gpr .ecx = BitVec.ofNat 32 r ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hsi, hcnt], by gregs [hsi], by gregs [E.ebp], by gregs [hcnt],
      fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [], by gmems []⟩
  have aT : w64 (p.W + BitVec.ofNat 32 tmpO) = w64 p.W + BitVec.ofNat 64 tmpO := L.aW (by decide)
  have xp : XorPre s₁ (p.W + BitVec.ofNat 32 tmpO) P r := by
    refine ⟨dx₁, di₁, cx₁, hr, by omega, ?_, hP.fit, ?_, by rw [wr₁]; exact hP.wr, ?_⟩
    · rw [L.nW (by decide)]; have := L.ww; simp only [tmpO]; omega
    · rw [aT, rd₁, wr₁]; exact E.perm.wCR (d := tmpO) (n := r) (by simp only [tmpO]; omega)
    · rw [aT]; exact (hP.w.sub_right (Lay.wSub (by simp only [tmpO]; omega))).symm
  unfold xorPad
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (xorLoop_ok s₁ xp) fun t P' => ⟨by rw [P'.mem, m₁, aT]; rfl, fun r h₁ h₂ h₃ h₄ h₅ => by
    rw [P'.other r h₁ h₂ h₅ h₄ h₃, g₁ r h₃ h₄ h₅], by rw [P'.rd, rd₁], by rw [P'.wr, wr₁]⟩

/-- `padCk`: `W + t2O ← pad(S)` and the checksum XORed with it, for the
`r` bytes `S` at `esi`. -/
theorem padCk_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {S : BitVec 32} {r : Nat} (hr : 0 < r)
    (hr' : r < 16) (hsi : s.gpr .esi = S) (hcnt : slotv s.mem p.W restO = BitVec.ofNat 32 r) (hS : VG.Proof.AesOcb.X86.SBuf p s S r) :
    WP isa padCk s fun t => Frame [⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) =
        blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt s.mem (w64 S) r) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold padCk
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.padTo_ok L E (d := t2O) (cO := restO) hr hr' (by decide) (by decide) (.inr (by decide))
    hsi hcnt hS) fun t₁ ⟨fr₁, pad₁, g₁, rd₁, wr₁⟩ => ?_)
  have E₁ : VG.Proof.AesOcb.X86.Env p t₁ := E.mut L (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd₁ wr₁ (VG.Proof.AesOcb.X86.frame_toMut fr₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩)))
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.xor16W_ok L E₁ (s := t2O) (d := ckO) (by decide) (by decide)
    (.inr (by decide))
  have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] t₁.mem t₂.mem := by
    rw [m₂]; exact (VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _).mono (by simp)
  refine WP.of_runBlock ⟨t₂, run₂, (fr₁.mono (by simp)).trans f₂, ?_,
    fun r h₁ h₂ h₃ h₄ => by rw [g₂ r h₁, g₁ r h₁ h₂ h₃ h₄], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  rw [m₂, VG.Proof.AesOcb.X86.xorMem16_block, pad₁, Proof.Ocb.blockAtMem_frame fr₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)]

/-- The block of `rest`'s head: `Offset_* = Offset ⊕ L_*`, copied to
`W + tmpO`. -/
theorem restBlk_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) :
    ∃ t₃, runBlock isa (([.mov .ebx (slot ctxO)] : List Instr) ++ xor16 .ebx 240 ofsO ++ copy16 ofsO tmpO) t = some t₃ ∧
      VG.Proof.AesOcb.X86.Env p t₃ ∧
      Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem ∧
      blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
        blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K) ∧
      blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 tmpO) =
        blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → t₃.gpr r = t.gpr r) ∧ t₃.rd = t.rd ∧ t₃.wr = t.wr := by
  have hc := E.slots.ctx
  simp only [slotv_eq] at hc
  obtain ⟨t₁, run₁, bx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .ebx (slot ctxO)] t = some t₁ ∧
      t₁.gpr .ebx = p.K ∧ (∀ r, r ≠ .ebx → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hc], by gregs [hc], fun r h => by gregs [h], by gmems [], by gmems [],
      by gmems []⟩
  have E₁ : VG.Proof.AesOcb.X86.Env p t₁ := E.keep (by rw [g₁ _ (by decide)]) (by rw [g₁ _ (by decide)]) rd₁ wr₁ m₁
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.xor16R_ok L E₁ (b := .ebx) (by decide) bx₁ L.kw L.k_w
    E₁.perm.k (s := 240) (d := ofsO) (by decide) (by decide)
  have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩] t₁.mem t₂.mem := by rw [m₂]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _
  have E₂ : VG.Proof.AesOcb.X86.Env p t₂ := E₁.mut L (by rw [g₂ _ (by decide), E₁.ebp]) (by rw [g₂ _ (by decide), E₁.esp]) rd₂ wr₂
    (VG.Proof.AesOcb.X86.frame_toMut f₂ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  obtain ⟨t₃, run₃, m₃, g₃, rd₃, wr₃⟩ := VG.Proof.AesOcb.X86.copy16_ok L E₂ (s := ofsO) (d := tmpO) (by decide) (by decide)
    (.inl (by decide))
  have f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t₂.mem t₃.mem := by rw [m₃]; exact VG.Proof.AesOcb.X86.copyMem16_frame _ _ _ _ _
  have E₃ : VG.Proof.AesOcb.X86.Env p t₃ := E₂.mut L (by rw [g₃ _ (by decide), E₂.ebp]) (by rw [g₃ _ (by decide), E₂.esp]) rd₃ wr₃
    (VG.Proof.AesOcb.X86.frame_toMut f₃ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  have fr₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem := by
    rw [← m₁]; exact (f₂.mono (by simp)).trans (f₃.mono (by simp))
  have ofs₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K) := by
    rw [m₂, VG.Proof.AesOcb.X86.xorMem16_block, m₁]; rfl
  have ofs₃ : blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K) := by
    rw [Proof.Ocb.blockAtMem_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
  exact ⟨t₃, runBlock_app_of (runBlock_app_of run₁ run₂) run₃, E₃, fr₃, ofs₃, by rw [m₃, VG.Proof.AesOcb.X86.copyMem16_block, ofs₂],
    fun r h₁ h₂ => by rw [g₃ r h₁, g₂ r h₁, g₁ r h₂], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩

/-- What the head of `rest` leaves: `Offset_*` and `Pad`. -/
structure RestHead (p : VG.Proof.AesOcb.X86.Prm) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.X86.Env p t'
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, VG.Proof.AesOcb.X86.stk p] t.mem t'.mem
  ofs : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K)
  tmp : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 tmpO) =
    ctxCiph t.mem (w64 p.K) p.R (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K))
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem restHead_ok (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) :
    WP isa (.seq (.block (([.mov .ebx (slot ctxO)] : List Instr) ++ xor16 .ebx 240 ofsO ++ copy16 ofsO tmpO))
      (callBlocks (VG.Proof.AesOcb.X86.callees v).enc (oneBlock tmpO))) t (VG.Proof.AesOcb.X86.RestHead p t) := by
  obtain ⟨t₃, run₃, E₃, fr₃, ofs₃, tmp₃, g₃, rd₃, wr₃⟩ := VG.Proof.AesOcb.X86.restBlk_ok L E
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  refine WP.mono (VG.Proof.AesOcb.X86.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E₃ (VG.Proof.AesOcb.X86.oneBlock_ok E₃ tmpO)
    (DReg.w L E₃ (d := tmpO) (n := 1) (by decide) (.inl (by decide)))) fun t₄ P₄ => ?_
  have aT : w64 (p.W + BitVec.ofNat 32 tmpO) = w64 p.W + BitVec.ofNat 64 tmpO := L.aW (by decide)
  refine ⟨P₄.env, (fr₃.mono (by simp)).trans ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, by rw [P₄.rd, rd₃],
    by rw [P₄.wr, wr₃]⟩
  · have F := P₄.frame
    rw [aT, show 16 * 1 = 16 from rfl] at F
    exact F.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp
  · rw [Proof.Ocb.blockAtMem_frame P₄.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [aT]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm), ofs₃]
  · have := P₄.enc (i := 0) (by decide)
    rw [aT, show w64 p.W + BitVec.ofNat 64 tmpO + BitVec.ofNat 64 (16 * 0) = w64 p.W + BitVec.ofNat 64 tmpO from
      BitVec.add_zero _] at this
    rw [this, VG.Proof.AesOcb.X86.ctxCiph_mut L (VG.Proof.AesOcb.X86.frame_toMut fr₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))), tmp₃]
  · rw [P₄.gpr r h₁ h₂ h₃ h₄, g₃ r h₁ h₂]

/-- What `rest` writes. -/
abbrev restR (p : VG.Proof.AesOcb.X86.Prm) (P : BitVec 32) (r : Nat) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, VG.Proof.AesOcb.X86.stk p, ⟨w64 P, r⟩]

/-- What `rest` leaves: `Offset_*`, the data XORed with `Pad`, and the
checksum with the padded plaintext (before the XOR for `seal`, after it for
`open`). -/
structure RestPost (enc : Bool) (p : VG.Proof.AesOcb.X86.Prm) (P : BitVec 32) (r : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.X86.Env p t'
  frame : Frame (VG.Proof.AesOcb.X86.restR p P r) t.mem t'.mem
  ofs : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K)
  out : bytesAt t'.mem (w64 P) r = Spec.Ocb.xor (bytesAt t.mem (w64 P) r)
    (Spec.Ocb.toBytes (ctxCiph t.mem (w64 p.K) p.R
      (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K))))
  ck : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ckO) =
    blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) (w64 P) r)
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem rest_ok (v : BlocksImpl) (enc : Bool) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {P : BitVec 32}
    {r : Nat} (hr : 0 < r) (hr' : r < 16) (hsi : t.gpr .esi = P) (hcnt : slotv t.mem p.W restO = BitVec.ofNat 32 r)
    (hP : VG.Proof.AesOcb.X86.RBuf p t P r) :
    WP isa (rest (VG.Proof.AesOcb.X86.callees v) enc) t (VG.Proof.AesOcb.X86.RestPost enc p P r t) := by
  unfold rest
  refine VG.Proof.AesOcb.X86.seq_assoc (WP.seq (WP.mono (VG.Proof.AesOcb.X86.restHead_ok v L E) fun t₃ H => ?_))
  have si₃ : t₃.gpr .esi = P := by rw [H.gpr _ (by decide) (by decide) (by decide) (by decide), hsi]
  have hP₃ : VG.Proof.AesOcb.X86.RBuf p t₃ P r := hP.of_eq H.wr
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
    fun h => hP.w.sub_right (Lay.wSub h)
  have dH : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, VG.Proof.AesOcb.X86.stk p], (⟨w64 P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact dW (by decide)
    · exact dW (by decide)
    · exact dW (by decide)
    · exact hP.stk.symm
  have dT : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨w64 P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact dW (by decide)
  have dWW : ∀ {a d : Nat}, (a + 16 ≤ d ∨ d + 16 ≤ a) → a + 16 ≤ 2560 → d + 16 ≤ 2560 →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region)], (⟨w64 p.W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h₁ h₂ q hq => by simp only [List.mem_singleton] at hq; subst hq; exact Lay.w_w h h₁ h₂
  have dTW : ∀ {a : Nat}, (a + 16 ≤ t2O ∨ t2O + 16 ≤ a) → (a + 16 ≤ ckO ∨ ckO + 16 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩],
        (⟨w64 p.W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q := fun h₁ h₂ h q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Lay.w_w h₁ h (by decide)
    · exact Lay.w_w h₂ h (by decide)
  have pP₃ : bytesAt t₃.mem (w64 P) r = bytesAt t.mem (w64 P) r :=
    Proof.AesGcm.X86.bytesAt_frame H.frame dH (by omega)
  have hl : (bytesAt t.mem (w64 P) r).length = r := length_bytesAt _ _ _
  have hlx : ∀ ys, (Spec.Ocb.xor (bytesAt t.mem (w64 P) r) (Spec.Ocb.toBytes ys)).length = r := fun ys => by
    simp [Spec.Ocb.xor, length_bytesAt, Proof.Ocb.toBytes_length]; omega
  have fP : ∀ (m : Mem) (xs : List Byte), xs.length = r → Frame [⟨w64 P, r⟩] m (writeBytes m (w64 P) xs) :=
    fun m xs h => writeBytes_frame _ _ _ (by rw [h]; exact Region.contains_self _ _)
  have cnt₃ : slotv t₃.mem p.W restO = BitVec.ofNat 32 r := by
    rw [← hcnt]
    exact H.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  -- What `xorPad` writes, from the state it starts in.
  have xP : ∀ u : State, bytesAt u.mem (w64 P) r = bytesAt t.mem (w64 P) r →
      blockAtMem u.mem (w64 p.W + BitVec.ofNat 64 tmpO) = blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 tmpO) →
      bytesAt (writeBytes u.mem (w64 P) (Spec.Ocb.xor (bytesAt u.mem (w64 P) r)
        (bytesAt u.mem (w64 p.W + BitVec.ofNat 64 tmpO) r))) (w64 P) r =
        Spec.Ocb.xor (bytesAt t.mem (w64 P) r) (Spec.Ocb.toBytes (ctxCiph t.mem (w64 p.K) p.R
          (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K)))) := by
    intro u hu ht
    rw [hu, Proof.Ocb.xor_bytesAt_block _ _ _ hl (by omega), ht, H.tmp,
      Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [hlx]) (by omega), hlx, List.drop_of_length_le
        (by rw [length_bytesAt]), List.append_nil]
  have ck₃ : blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 ckO) = blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) :=
    Proof.Ocb.blockAtMem_frame H.frame fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm
  have pW : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ q ∈ [(⟨w64 P, r⟩ : Region)],
      (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q :=
    fun h q hq => by simp only [List.mem_singleton] at hq; subst hq; exact (dW h).symm
  have mP : VG.Proof.AesOcb.X86.InMut p [⟨w64 P, r⟩] := hP.inm
  have mT : VG.Proof.AesOcb.X86.InMut p [⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
    · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))
  have fR : ∀ {m₀ m₁ m₂ : Mem} {rs : List Region}, Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, VG.Proof.AesOcb.X86.stk p] m₀ m₁ →
      Frame rs m₁ m₂ → (∀ q ∈ rs, q ∈ VG.Proof.AesOcb.X86.restR p P r) → Frame (VG.Proof.AesOcb.X86.restR p P r) m₀ m₂ := fun h₁ h₂ hs =>
    (h₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl | rfl <;> simp).trans
      (h₂.mono hs)
  cases enc
  · -- `open`: the XOR, then the checksum.
    refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.xorPad_ok L H.env hr hr' si₃ cnt₃ hP₃) fun t₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_)
    have fr₄ : Frame [⟨w64 P, r⟩] t₃.mem t₄.mem := by rw [m₄]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    have E₄ : VG.Proof.AesOcb.X86.Env p t₄ := H.env.mut L (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide),
                          H.env.ebp]) (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), H.env.esp]) rd₄ wr₄
      (VG.Proof.AesOcb.X86.frame_toMut fr₄ mP)
    have cnt₄ : slotv t₄.mem p.W restO = BitVec.ofNat 32 r := by
      rw [← cnt₃]
      exact fr₄.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact (dW (by decide)).symm) (by decide)
    refine WP.mono (VG.Proof.AesOcb.X86.padCk_ok L E₄ hr hr' (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), si₃])
      cnt₄ (hP₃.of_eq wr₄).sbuf) fun t₅ ⟨fr₅, ck₅, g₅, rd₅, wr₅⟩ => ?_
    have p₅ : bytesAt t₅.mem (w64 P) r = bytesAt t₄.mem (w64 P) r :=
      Proof.AesGcm.X86.bytesAt_frame fr₅ dT (by omega)
    refine ⟨E₄.mut L (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), E₄.ebp])
      (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), E₄.esp]) rd₅ wr₅ (VG.Proof.AesOcb.X86.frame_toMut fr₅ mT),
      fR H.frame (rs := [⟨w64 P, r⟩, ⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩])
        ((fr₄.mono (by simp)).trans (fr₅.mono (by simp))) (by simp), ?_, ?_, ?_,
      fun q h₁ h₂ h₃ h₄ h₅ => by rw [g₅ q h₁ h₃ h₄ h₅, g₄ q h₁ h₂ h₃ h₄ h₅, H.gpr q h₁ h₂ h₃ h₄],
      by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [Proof.Ocb.blockAtMem_frame fr₅ (dTW (.inl (by decide)) (.inl (by decide)) (by decide)),
        Proof.Ocb.blockAtMem_frame fr₄ (pW (by decide)), H.ofs]
    · rw [p₅, m₄, xP t₃ pP₃ rfl]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ck₅, p₅, Proof.Ocb.blockAtMem_frame fr₄ (pW (by decide)), ck₃]
  · -- `seal`: the checksum, then the XOR.
    refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.padCk_ok L H.env hr hr' si₃ cnt₃ hP₃.sbuf) fun t₄ ⟨fr₄, ck₄, g₄, rd₄, wr₄⟩ => ?_)
    have E₄ : VG.Proof.AesOcb.X86.Env p t₄ := H.env.mut L (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), H.env.ebp])
      (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), H.env.esp]) rd₄ wr₄ (VG.Proof.AesOcb.X86.frame_toMut fr₄ mT)
    have p₄ : bytesAt t₄.mem (w64 P) r = bytesAt t₃.mem (w64 P) r := Proof.AesGcm.X86.bytesAt_frame fr₄ dT (by omega)
    have cnt₄ : slotv t₄.mem p.W restO = BitVec.ofNat 32 r := by
      rw [← cnt₃]
      exact fr₄.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    refine WP.mono (VG.Proof.AesOcb.X86.xorPad_ok L E₄ hr hr' (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), si₃]) cnt₄
      (hP₃.of_eq wr₄)) fun t₅ ⟨m₅, g₅, rd₅, wr₅⟩ => ?_
    have fr₅ : Frame [⟨w64 P, r⟩] t₄.mem t₅.mem := by rw [m₅]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine ⟨E₄.mut L (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), E₄.ebp])
      (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), E₄.esp]) rd₅ wr₅ (VG.Proof.AesOcb.X86.frame_toMut fr₅ mP),
      fR H.frame (rs := [⟨w64 P, r⟩, ⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩])
        ((fr₄.mono (by simp)).trans (fr₅.mono (by simp))) (by simp), ?_, ?_, ?_,
      fun q h₁ h₂ h₃ h₄ h₅ => by rw [g₅ q h₁ h₂ h₃ h₄ h₅, g₄ q h₁ h₃ h₄ h₅, H.gpr q h₁ h₂ h₃ h₄],
      by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [Proof.Ocb.blockAtMem_frame fr₅ (pW (by decide)),
        Proof.Ocb.blockAtMem_frame fr₄ (dTW (.inl (by decide)) (.inl (by decide)) (by decide)), H.ofs]
    · rw [m₅, xP t₄ (by rw [p₄, pP₃]) (Proof.Ocb.blockAtMem_frame fr₄
        (dTW (.inl (by decide)) (.inr (by decide)) (by decide)))]
    · simp only [↓reduceIte]
      rw [Proof.Ocb.blockAtMem_frame fr₅ (pW (by decide)), ck₄, ck₃, pP₃]

/-- What `tag d` leaves. -/
structure TagPost (p : VG.Proof.AesOcb.X86.Prm) (d : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.X86.Env p t'
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 d, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, VG.Proof.AesOcb.X86.stk p] t.mem t'.mem
  val : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 d) =
    ctxCiph t.mem (w64 p.K) p.R (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ldO)) ^^^
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 sumO)
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem tag_ok (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    WP isa (tag (VG.Proof.AesOcb.X86.callees v) d) t (VG.Proof.AesOcb.X86.TagPost p d t) := by
  have hd' : d = 0 ∨ d = 144 := hd
  have mW : ∀ {a : Nat}, a + 16 ≤ 128 ∨ 144 ≤ a ∧ a + 16 ≤ 176 → VG.Proof.AesOcb.X86.InMut p [⟨w64 p.W + BitVec.ofNat 64 a, 16⟩] :=
    fun h q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      rcases h with h | h
      · exact VG.Proof.AesOcb.X86.inMut_w p (.inl h)
      · exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inl h))
  have step : ∀ {u u' : State} {a : Nat}, VG.Proof.AesOcb.X86.Env p u → (a + 16 ≤ 128 ∨ 144 ≤ a ∧ a + 16 ≤ 176) →
      Frame [⟨w64 p.W + BitVec.ofNat 64 a, 16⟩] u.mem u'.mem → (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) →
      u'.rd = u.rd → u'.wr = u.wr → VG.Proof.AesOcb.X86.Env p u' := fun Eu ha f g rd wr =>
    Eu.mut L (by rw [g _ (by decide), Eu.ebp]) (by rw [g _ (by decide), Eu.esp]) rd wr (VG.Proof.AesOcb.X86.frame_toMut f (mW ha))
  obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.copy16_ok L E (s := ckO) (d := tmpO) (by decide) (by decide)
    (.inl (by decide))
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₁.mem := by rw [m₁]; exact VG.Proof.AesOcb.X86.copyMem16_frame _ _ _ _ _
  have E₁ := step E (.inl (by decide)) f₁ g₁ rd₁ wr₁
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.xor16W_ok L E₁ (s := ofsO) (d := tmpO) (by decide) (by decide)
    (.inl (by decide))
  have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t₁.mem t₂.mem := by rw [m₂]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _
  have E₂ := step E₁ (.inl (by decide)) f₂ g₂ rd₂ wr₂
  obtain ⟨t₃, run₃, m₃, g₃, rd₃, wr₃⟩ := VG.Proof.AesOcb.X86.xor16W_ok L E₂ (s := ldO) (d := tmpO) (by decide) (by decide)
    (.inl (by decide))
  have f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t₂.mem t₃.mem := by rw [m₃]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _
  have E₃ := step E₂ (.inl (by decide)) f₃ g₃ rd₃ wr₃
  have fr₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem := (f₁.trans f₂).trans f₃
  have tW : ∀ {a : Nat}, (a + 16 ≤ tmpO ∨ tmpO + 16 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩ : Region)], (⟨w64 p.W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact Lay.w_w h h' (by decide)
  have tmp₃ : blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ldO) := by
    have ofs₁ := Proof.Ocb.blockAtMem_frame f₁ (tW (a := ofsO) (.inl (by decide)) (by decide))
    have ld₂ := Proof.Ocb.blockAtMem_frame (f₁.trans f₂) (tW (a := ldO) (.inl (by decide)) (by decide))
    rw [m₃, VG.Proof.AesOcb.X86.xorMem16_block, ld₂, m₂, VG.Proof.AesOcb.X86.xorMem16_block, ofs₁, m₁, VG.Proof.AesOcb.X86.copyMem16_block]
  have cK : ctxCiph t₃.mem (w64 p.K) p.R = ctxCiph t.mem (w64 p.K) p.R :=
    VG.Proof.AesOcb.X86.ctxCiph_mut L (VG.Proof.AesOcb.X86.frame_toMut fr₃ (mW (.inl (by decide))))
  unfold tag
  refine WP.seq (WP.of_runBlock ⟨t₃, runBlock_app_of (runBlock_app_of run₁ run₂) run₃, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E₃ (VG.Proof.AesOcb.X86.oneBlock_ok E₃ tmpO)
    (DReg.w L E₃ (d := tmpO) (n := 1) (by decide) (.inl (by decide)))) fun t₄ P₄ => ?_)
  have aT : w64 (p.W + BitVec.ofNat 32 tmpO) = w64 p.W + BitVec.ofNat 64 tmpO := L.aW (by decide)
  have tmp₄ : blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 tmpO) =
      ctxCiph t.mem (w64 p.K) p.R (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^
        blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ldO)) := by
    have := P₄.enc (i := 0) (by decide)
    rw [aT, show w64 p.W + BitVec.ofNat 64 tmpO + BitVec.ofNat 64 (16 * 0) = w64 p.W + BitVec.ofNat 64 tmpO from
      BitVec.add_zero _] at this
    rw [this, tmp₃, cK]
  have mD : d + 16 ≤ 128 ∨ 144 ≤ d ∧ d + 16 ≤ 176 := by omega
  have dT : (d + 16 ≤ tmpO ∨ tmpO + 16 ≤ d) := by simp only [tmpO]; omega
  obtain ⟨t₅, run₅, m₅, g₅, rd₅, wr₅⟩ := VG.Proof.AesOcb.X86.copy16_ok L P₄.env (s := tmpO) (d := d) (by decide) (by omega)
    (by simp only [tmpO]; omega)
  have f₅ : Frame [⟨w64 p.W + BitVec.ofNat 64 d, 16⟩] t₄.mem t₅.mem := by rw [m₅]; exact VG.Proof.AesOcb.X86.copyMem16_frame _ _ _ _ _
  have E₅ := step P₄.env mD f₅ g₅ rd₅ wr₅
  obtain ⟨t₆, run₆, m₆, g₆, rd₆, wr₆⟩ := VG.Proof.AesOcb.X86.xor16W_ok L E₅ (s := sumO) (d := d) (by decide) (by omega)
    (by simp only [sumO]; omega)
  have f₆ : Frame [⟨w64 p.W + BitVec.ofNat 64 d, 16⟩] t₅.mem t₆.mem := by rw [m₆]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _
  refine WP.of_runBlock ⟨t₆, runBlock_app_of run₅ run₆, step E₅ mD f₆ g₆ rd₆ wr₆, ?_, ?_,
    fun r h₁ h₂ h₃ h₄ => by rw [g₆ r h₁, g₅ r h₁, P₄.gpr r h₁ h₂ h₃ h₄, g₃ r h₁, g₂ r h₁, g₁ r h₁],
    by rw [rd₆, rd₅, P₄.rd, rd₃, rd₂, rd₁], by rw [wr₆, wr₅, P₄.wr, wr₃, wr₂, wr₁]⟩
  · have F₄ := P₄.frame
    rw [aT, show 16 * 1 = 16 from rfl] at F₄
    exact (((fr₃.mono (by simp)).trans (F₄.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl <;> simp)).trans
      (f₅.mono (by simp))).trans (f₆.mono (by simp))
  · have sum₄ : blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 sumO) = blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 sumO) := by
      rw [Proof.Ocb.blockAtMem_frame P₄.frame (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · rw [aT]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm), Proof.Ocb.blockAtMem_frame fr₃ (tW (.inl (by decide)) (by decide))]
    rw [m₆, VG.Proof.AesOcb.X86.xorMem16_block, m₅, VG.Proof.AesOcb.X86.copyMem16_block, Proof.Ocb.blockAtMem_frame (VG.Proof.AesOcb.X86.copyMem16_frame _ _ _ _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact Lay.w_w (by simp only [sumO]; omega) (by decide) (by omega)),
      tmp₄, sum₄]

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Body`. -/
section

/-!
# AES-OCB on x86: the data (`body`)

Untrusted: everything here is checked by Lean. `body` keeps the number of
whole blocks `m = len / 16` in `W` and runs `whole` on them if there are any
(`wholeIte_ok`), then `rest` on the `len mod 16` bytes after them if there
are any (`restIte_ok`): for `seal` (`bodySeal_ok`) and `open`
(`bodyOpen_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxInv ctxLstar pad)
open VG.Proof.Ocb (offAt ckOf)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off
  length_bytesAt)

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}` and `Pad`,
`pad(·)`, the variables at `[216, 384)`, the working space of the functions
called, the stack and the data. -/
abbrev bodyR (p : VG.Proof.AesOcb.X86.Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 16, 32⟩, ⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, ⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩,
    VG.Proof.AesOcb.X86.wV p.W, VG.Proof.AesOcb.X86.wC p.W, VG.Proof.AesOcb.X86.stk p, ⟨w64 p.D, p.n⟩]

theorem bodyR_mut {p : VG.Proof.AesOcb.X86.Prm} {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.bodyR p) m m') : Frame (VG.Proof.AesOcb.X86.mutR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact VG.Proof.AesOcb.X86.inMut_stk p
  · exact VG.Proof.AesOcb.X86.inMut_d p

/-- A part of `W` within `bodyR`. -/
theorem inBodyR (p : VG.Proof.AesOcb.X86.Prm) {d k : Nat}
    (h : 16 ≤ d ∧ d + k ≤ 48 ∨ 96 ≤ d ∧ d + k ≤ 128 ∨ 144 ≤ d ∧ d + k ≤ 160 ∨ 216 ≤ d ∧ d + k ≤ 384 ∨
      384 ≤ d ∧ d + k ≤ 2560) :
    ∃ r' ∈ VG.Proof.AesOcb.X86.bodyR p, Region.Sub ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with h | h | h | h | h
  · exact ⟨_, by simp, Offset.sub _ (e := 16) (k := 32) (by omega) (by omega)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 96) (k := 32) (by omega) (by omega)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 144) (k := 16) (by omega) (by omega)⟩
  · exact ⟨VG.Proof.AesOcb.X86.wV p.W, by simp, Offset.sub _ (by omega) (by omega)⟩
  · exact ⟨VG.Proof.AesOcb.X86.wC p.W, by simp, Offset.sub _ (by omega) (by omega)⟩

/-- The number of whole blocks, kept in `W`. -/
theorem bodyHead_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) :
    ∃ s₁, runBlock isa [.mov .ebx (slot lenO), .shift .shr .ebx 4, .store (at_ .ebp nbO) .ebx,
        .alu .test .ebx (.reg .ebx)] s = some s₁ ∧
      s₁.mem = s.mem.writeW (w64 p.W + BitVec.ofNat 64 nbO) (BitVec.ofNat 32 (p.n / 16)) ∧
      s₁.zf = some (decide (p.n / 16 = 0)) ∧
      (∀ r, r ≠ .ebx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have hn := L.n32
  have hl := E.slots.len
  simp only [slotv_eq] at hl
  refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, E.perm.wW, hl], by gmems [hl, VG.Proof.AesOcb.X86.shr4_32 hn], ?_,
    fun r h => by gregs [h], by gmems [], by gmems []⟩
  gmems [hl, VG.Proof.AesOcb.X86.shr4_32 hn, BitVec.and_self, VG.Proof.AesOcb.X86.beq_zero32 (show p.n / 16 < 2 ^ 32 by omega)]

/-- What the whole blocks leave, if there are any. -/
structure WholeIte (p : VG.Proof.AesOcb.X86.Prm) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (s t : State) : Prop where
  env : VG.Proof.AesOcb.X86.Env p t
  frame : Frame (VG.Proof.AesOcb.X86.bodyR p) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  blk : ∀ k < m, blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = ck
  tail : 0 < p.n % 16 → bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
    bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16)

theorem wholeR_body {p : VG.Proof.AesOcb.X86.Prm} {k : Nat} (hk : 16 * k ≤ p.n) {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.wholeR p k) m m') :
    Frame (VG.Proof.AesOcb.X86.bodyR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.AesOcb.X86.inBodyR p (.inl ⟨by decide, by decide⟩)
  · exact VG.Proof.AesOcb.X86.inBodyR p (.inr (.inl ⟨by decide, by decide⟩))
  · exact VG.Proof.AesOcb.X86.inBodyR p (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : VG.Proof.AesOcb.X86.Prm} {G : Mem → Cipher}
    (hcall : ∀ {s s' : State} {D : BitVec 32} {n : Nat}, VG.Proof.AesOcb.X86.CallPost p f D n s s' → ∀ i < n,
      blockAtMem s'.mem (w64 D + BitVec.ofNat 64 (16 * i)) = G s.mem (blockAtMem s.mem (w64 D + BitVec.ofNat 64 (16 * i))))
    (hG : ∀ {m m' : Mem}, Frame (VG.Proof.AesOcb.X86.mutR p) m m' → G m' = G m)
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : VG.Proof.AesOcb.X86.BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : VG.Proof.AesOcb.X86.BodyOk p post (fun b o => b ^^^ o) fC2)
    (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {O0 l : Block}
    (hofs : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i < p.n / 16, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (p.n / 16))
    (hckF2 : ∀ i < p.n / 16, ckF2 (i + 1) = fC2 (ckF2 i)
      (G s.mem (blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1))) (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.mov .ebx (slot lenO), .shift .shr .ebx 4, .store (at_ .ebp nbO) .ebx,
        .alu .test .ebx (.reg .ebx)]) (.ite .e (.block []) (whole fn pre post))) s
      (VG.Proof.AesOcb.X86.WholeIte p (p.n / 16) O0 l
        (fun k => G s.mem (blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (p.n / 16)) s) := by
  obtain ⟨s₁, run₁, m₁, zf₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.bodyHead_ok L E
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩] s.mem s₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fB₁ : Frame (VG.Proof.AesOcb.X86.bodyR p) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inBodyR p (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have E₁ : VG.Proof.AesOcb.X86.Env p s₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (VG.Proof.AesOcb.X86.bodyR_mut fB₁)
  have kB : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩ →
      blockAtMem s₁.mem Q = blockAtMem s.mem Q := fun h =>
    Proof.Ocb.blockAtMem_frame f₁ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h
  have kW : ∀ {d : Nat}, d + 16 ≤ nbO → blockAtMem s₁.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 d) := fun h => kB (Lay.w_w (.inl h) (by simp only [nbO] at h; omega)
        (by decide))
  have kD : ∀ k, 16 * (k + 1) ≤ p.n → blockAtMem s₁.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) =
      blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) := fun k hk =>
    kB ((L.d_w.sub_left (Offset.sub_base _ (by omega))).sub_right (Lay.wSub (by decide)))
  have tail₁ : 0 < p.n % 16 → bytesAt s₁.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
      bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := fun hr => by
    have hd := L.dw
    have sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))), p.n % 16⟩ ⟨w64 p.D, p.n⟩ := by
      rw [w64_add (by omega)]; exact Offset.sub_base _ (by omega)
    exact Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))) (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite _ (Proof.AesOcb.X86.eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : p.n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, fB₁, rd₁, wr₁, fun k hk => absurd hk (by omega), by rw [kW (by decide), hofs, hm]; rfl,
      by rw [kW (by decide), hck, hm, hckF2₀, hm], fun hr => tail₁ hr⟩
  · have hm : p.n / 16 ≠ 0 := of_decide_eq_false h0
    have hG₁ : G s₁.mem = G s.mem := hG (VG.Proof.AesOcb.X86.bodyR_mut fB₁)
    refine WP.mono (VG.Proof.AesOcb.X86.whole_ok (O0 := O0) (l := l) (ckF1 := ckF1) (ckF2 := ckF2) ok nosp stack hcall hG hB1 hB2 L E₁
      (m := p.n / 16) (by omega) (by omega)
      (by rw [slotv_eq, m₁, Mem.readW_writeW_self32]) (by rw [kW (by decide), hofs]) (by rw [kW (by decide), ho0])
      (by rw [kW (by decide), hck]) (by rw [kW (by decide), hl0])
      (fun i hi => by rw [hckF1 i hi, kD i (by omega)]) hckF2₀
      (fun i hi => by rw [hckF2 i hi, hG₁, kD i (by omega)])) fun t P => ?_
    refine ⟨P.env, fB₁.trans (VG.Proof.AesOcb.X86.wholeR_body (Nat.mul_div_le p.n 16) P.frame), by rw [P.rd, rd₁], by rw [P.wr, wr₁],
      fun k hk => ?_, P.ofs, P.ck, fun hr => ?_⟩
    · rw [P.blk k hk, hG₁, kD k (by omega)]
    · rw [← tail₁ hr]
      have hd := L.dw
      have a16 : w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))) = w64 p.D + BitVec.ofNat 64 (16 * (p.n / 16)) :=
        w64_add (by omega)
      have sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))), p.n % 16⟩ ⟨w64 p.D, p.n⟩ := by
        rw [a16]; exact Offset.sub_base _ (by omega)
      exact Proof.AesGcm.X86.bytesAt_frame P.frame (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
        · exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))
        · exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))
        · exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))
        · exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))
        · exact (L.bd.sub_right sub).symm
        · rw [a16]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)) (by omega)

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) :
    ∃ t₁, runBlock isa [.mov .esi (slot dataO), .mov .eax (slot lenO), .mov .ecx (.reg .eax), .alu .and .ecx (imm 15),
        .store (at_ .ebp restO) .ecx, .alu .sub .eax (.reg .ecx), .alu .add .esi (.reg .eax),
        .alu .test .ecx (.reg .ecx)] t = some t₁ ∧
      t₁.gpr .esi = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧ t₁.zf = some (decide (p.n % 16 = 0)) ∧
      t₁.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 restO) (BitVec.ofNat 32 (p.n % 16)) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have hn := L.n32
  have hD := E.slots.data
  have hl := E.slots.len
  simp only [slotv_eq] at hD hl
  have hsub : BitVec.ofNat 32 p.n - BitVec.ofNat 32 (p.n % 16) = BitVec.ofNat 32 (16 * (p.n / 16)) := by
    rw [VG.Proof.AesOcb.X86.sub32' (Nat.mod_le _ _) hn, show p.n - p.n % 16 = 16 * (p.n / 16) by omega]
  refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, E.perm.wW, hD, hl], by gregs [hD, hl, VG.Proof.AesOcb.X86.and15_32 hn, hsub], ?_,
    by gmems [hl, VG.Proof.AesOcb.X86.and15_32 hn], fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [hl, VG.Proof.AesOcb.X86.and15_32 hn, BitVec.and_self, VG.Proof.AesOcb.X86.beq_zero32 (show p.n % 16 < 2 ^ 32 by omega)]

/-- The tail of the data. -/
theorem rbuf_tail {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) (hr : 0 < p.n % 16) :
    VG.Proof.AesOcb.X86.RBuf p s (p.D + BitVec.ofNat 32 (16 * (p.n / 16))) (p.n % 16) := by
  have hd := L.dw
  have a16 : w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))) = w64 p.D + BitVec.ofNat 64 (16 * (p.n / 16)) :=
    w64_add (by omega)
  have sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))), p.n % 16⟩ ⟨w64 p.D, p.n⟩ := by
    rw [a16]; exact Offset.sub_base _ (by omega)
  refine ⟨by rw [toNat_add32 (by omega)]; omega, L.d_w.sub_left sub, L.bd.sub_right sub, ?_, fun r hr => ?_⟩
  · rw [a16]; exact covers_off E.perm.d (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sub⟩

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (p : VG.Proof.AesOcb.X86.Prm) (P : BitVec 32) (r : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.X86.Env p t'
  frame : Frame (VG.Proof.AesOcb.X86.bodyR p) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K)
    else blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem (w64 P) r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem (w64 P) r)
      (Spec.Ocb.toBytes (ctxCiph t.mem (w64 p.K) p.R
        (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K))))
    else bytesAt t.mem (w64 P) r
  ck : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ckO) =
    if 0 < r then blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^
      pad (bytesAt (if enc then t.mem else t'.mem) (w64 P) r)
    else blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO)
  pre : bytesAt t'.mem (w64 p.D) (16 * (p.n / 16)) = bytesAt t.mem (w64 p.D) (16 * (p.n / 16))

theorem restR_body {p : VG.Proof.AesOcb.X86.Prm} {P : BitVec 32} {r : Nat}
    (hPD : Region.Sub ⟨w64 P, r⟩ ⟨w64 p.D, p.n⟩) {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.restR p P r) m m') :
    Frame (VG.Proof.AesOcb.X86.bodyR p) m m' := h.sub fun q hq => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.AesOcb.X86.inBodyR p (.inl ⟨by decide, by decide⟩)
  · exact VG.Proof.AesOcb.X86.inBodyR p (.inr (.inl ⟨by decide, by decide⟩))
  · exact VG.Proof.AesOcb.X86.inBodyR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact VG.Proof.AesOcb.X86.inBodyR p (.inl ⟨by decide, by decide⟩)
  · exact VG.Proof.AesOcb.X86.inBodyR p (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩))))
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, hPD⟩

/-- The rest of the data, if there is any. -/
theorem restIte_ok (v : BlocksImpl) (enc : Bool) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) :
    WP isa (.seq (.block [.mov .esi (slot dataO), .mov .eax (slot lenO), .mov .ecx (.reg .eax),
        .alu .and .ecx (imm 15), .store (at_ .ebp restO) .ecx, .alu .sub .eax (.reg .ecx), .alu .add .esi (.reg .eax),
        .alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) (rest (VG.Proof.AesOcb.X86.callees v) enc))) t
      (VG.Proof.AesOcb.X86.TailPost enc p (p.D + BitVec.ofNat 32 (16 * (p.n / 16))) (p.n % 16) t) := by
  obtain ⟨t₁, run₁, si₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.bodyTail_ok L E
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩] t.mem t₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fB₁ : Frame (VG.Proof.AesOcb.X86.bodyR p) t.mem t₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inBodyR p (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have E₁ : VG.Proof.AesOcb.X86.Env p t₁ := E.mut L (by rw [g₁ _ (by decide) (by decide) (by decide), E.ebp])
    (by rw [g₁ _ (by decide) (by decide) (by decide), E.esp]) rd₁ wr₁ (VG.Proof.AesOcb.X86.bodyR_mut fB₁)
  have kB : ∀ {d : Nat}, d + 16 ≤ restO → blockAtMem t₁.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) := fun h =>
    Proof.Ocb.blockAtMem_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl h) (by simp only [restO] at h; omega)
        (by decide)
  have hK : ∀ {m : Mem}, Frame (VG.Proof.AesOcb.X86.mutR p) t.mem m → ctxLstar m (w64 p.K) = ctxLstar t.mem (w64 p.K) ∧
      ctxCiph m (w64 p.K) p.R = ctxCiph t.mem (w64 p.K) p.R := fun h => ⟨VG.Proof.AesOcb.X86.lstar_mut L h, VG.Proof.AesOcb.X86.ctxCiph_mut L h⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (Proof.AesOcb.X86.eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < p.n % 16 := by have := of_decide_eq_true h0; omega
    have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q (p.n % 16) = [] := fun _ _ => by
      rw [show p.n % 16 = 0 by omega]; rfl
    have dpre : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩ : Region)],
        (⟨w64 p.D, 16 * (p.n / 16)⟩ : Region).Disjoint q := fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.d_w.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))
    refine ⟨E₁, fB₁, rd₁, wr₁, ?_, ?_, ?_, Proof.AesGcm.X86.bytesAt_frame f₁ dpre (by have := L.dw; omega)⟩ <;>
      simp only [hr, ↓reduceIte, b0]
    · exact kB (by decide)
    · exact kB (by decide)
  · have hr : 0 < p.n % 16 := by have := of_decide_eq_false h0; omega
    have hP := VG.Proof.AesOcb.X86.rbuf_tail L E₁ hr
    have cnt₁ : slotv t₁.mem p.W restO = BitVec.ofNat 32 (p.n % 16) := by rw [slotv_eq, m₁, Mem.readW_writeW_self32]
    refine WP.mono (VG.Proof.AesOcb.X86.rest_ok v enc L E₁ hr (Nat.mod_lt _ (by decide)) si₁ cnt₁ hP) fun t' P => ?_
    have hd := L.dw
    have sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))), p.n % 16⟩ ⟨w64 p.D, p.n⟩ := by
      rw [w64_add (by omega)]; exact Offset.sub_base _ (by omega)
    obtain ⟨lT, cT⟩ := hK (VG.Proof.AesOcb.X86.bodyR_mut fB₁)
    have pT : bytesAt t₁.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
        bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) :=
      Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide))) (by omega)
    have dpre : ∀ q ∈ (⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩ :: VG.Proof.AesOcb.X86.restR p (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))
        (p.n % 16)), (⟨w64 p.D, 16 * (p.n / 16)⟩ : Region).Disjoint q := by
      have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨w64 p.D, 16 * (p.n / 16)⟩ : Region).Disjoint
          ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ := fun h =>
        (L.d_w.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub h)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact dW (by decide)
      · exact dW (by decide)
      · exact dW (by decide)
      · exact dW (by decide)
      · exact dW (by decide)
      · exact dW (by decide)
      · exact (L.bd.sub_right (Region.sub_prefix (by omega))).symm
      · rw [w64_add (by omega)]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)
    have fpre : Frame (⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩ :: VG.Proof.AesOcb.X86.restR p (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))
        (p.n % 16)) t.mem t'.mem :=
      (f₁.mono (by simp)).trans (P.frame.mono fun q hq => List.mem_cons_of_mem _ hq)
    refine ⟨P.env, fB₁.trans (VG.Proof.AesOcb.X86.restR_body sub P.frame), by rw [P.rd, rd₁], by rw [P.wr, wr₁],
      ?_, ?_, ?_, Proof.AesGcm.X86.bytesAt_frame fpre dpre (by omega)⟩ <;> simp only [hr, ↓reduceIte]
    · rw [P.ofs, kB (by decide), lT]
    · rw [P.out, kB (by decide), lT, cT, pT]
    · rw [P.ck, kB (by decide)]
      cases enc
      · rfl
      · simp only [↓reduceIte, pT]

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (p : VG.Proof.AesOcb.X86.Prm) (out : List Byte) (ofs ck : Block) (s t : State) : Prop where
  env : VG.Proof.AesOcb.X86.Env p t
  frame : Frame (VG.Proof.AesOcb.X86.bodyR p) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem (w64 p.D) p.n = out
  ofs : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = ck

/-- The facts both `body` proofs use. -/
theorem body_facts {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) (m : Mem) :
    (∀ i < p.n / 16, blockAtMem m (w64 p.D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt m (w64 p.D) p.n) i) ∧
    (0 < p.n % 16 → (bytesAt m (w64 p.D) p.n).drop (16 * (p.n / 16)) =
      bytesAt m (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16)) := by
  have hd := L.dw
  refine ⟨fun i hi => (Proof.Ocb.blockAt_bytesAt m _ (by omega)).symm, fun hr => ?_⟩
  rw [Proof.Ocb.bytesAt_drop m _ (Nat.mul_div_le p.n 16), show p.n - 16 * (p.n / 16) = p.n % 16 by omega,
    w64_add (by omega)]

/-- The data after `body`, from its whole blocks and its rest. -/
theorem body_out {enc : Bool} {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t t' : State} (P : VG.Proof.AesOcb.X86.TailPost enc p (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))
    (p.n % 16) t t') {X : List Byte} (hX : bytesAt t.mem (w64 p.D) (16 * (p.n / 16)) = X) :
    bytesAt t'.mem (w64 p.D) p.n = X ++ bytesAt t'.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := by
  have hd := L.dw
  have e := Proof.Ocb.bytesAt_append t'.mem (w64 p.D) (16 * (p.n / 16)) (p.n % 16)
  rw [show 16 * (p.n / 16) + p.n % 16 = p.n by omega] at e
  rw [e, P.pre, hX]
  by_cases hr : 0 < p.n % 16
  · rw [w64_add (by omega)]
  · rw [show p.n % 16 = 0 by omega]; rfl

/-- `body` for `seal`. -/
theorem bodySeal_ok (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {O0 : Block}
    (hofs : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (w64 p.K)) 0) :
    WP isa (body (VG.Proof.AesOcb.X86.callees v) true) s (VG.Proof.AesOcb.X86.BodyPost p
      (if 0 < p.n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
            (p.n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (w64 p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (w64 p.K) p.R
              (offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K))))
      else Proof.Ocb.encBlocks (ctxCiph s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K))
        (bytesAt s.mem (w64 p.D) p.n) (p.n / 16))
      (if 0 < p.n % 16 then offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K)
       else offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16))
      (if 0 < p.n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem (w64 p.D) p.n) (p.n / 16) ^^^
          pad ((bytesAt s.mem (w64 p.D) p.n).drop (16 * (p.n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem (w64 p.D) p.n) (p.n / 16)) s) := by
  have hd := L.dw
  obtain ⟨hl, hrest⟩ := VG.Proof.AesOcb.X86.body_facts L s.mem
  simp only [body, ↓reduceIte]
  refine VG.Proof.AesOcb.X86.seq_assoc (WP.seq (WP.mono (VG.Proof.AesOcb.X86.wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (w64 p.K))
    (G := fun m => ctxCiph m (w64 p.K) p.R)
    (ckF1 := ckOf fun i => blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
    v.encOk v.encNosp v.encStack (fun P _ hi => P.enc hi) (fun h => VG.Proof.AesOcb.X86.ctxCiph_mut L h) (VG.Proof.AesOcb.X86.sealPre_ok L) (VG.Proof.AesOcb.X86.xorOfs_ok L)
    L E hofs ho0 hck hl0 (fun _ _ => rfl) rfl (fun _ _ => rfl)) fun t Pw => ?_))
  have fW : Frame (VG.Proof.AesOcb.X86.mutR p) s.mem t.mem := VG.Proof.AesOcb.X86.bodyR_mut Pw.frame
  refine WP.mono (VG.Proof.AesOcb.X86.restIte_ok v true L Pw.env) fun t' Pt => ?_
  have cT : ctxCiph t.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R := VG.Proof.AesOcb.X86.ctxCiph_mut L fW
  have lT : ctxLstar t.mem (w64 p.K) = ctxLstar s.mem (w64 p.K) := VG.Proof.AesOcb.X86.lstar_mut L fW
  have blk : bytesAt t.mem (w64 p.D) (16 * (p.n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
        (p.n / 16) := by
    rw [Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
    refine Proof.Ocb.flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, hl i hi, BitVec.xor_comm]
  have ckT : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem (w64 p.D) p.n) (p.n / 16) := by
    rw [Pw.ck, Proof.Ocb.ckOf_eq hl]
  refine ⟨Pt.env, Pw.frame.trans Pt.frame, by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [VG.Proof.AesOcb.X86.body_out L Pt blk, Pt.out]
    by_cases hr : 0 < p.n % 16
    · have pT : bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
          bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := by
        exact Pw.tail hr
      simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, hrest hr]
    · have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q (p.n % 16) = [] := fun _ _ => by
        rw [show p.n % 16 = 0 by omega]; rfl
      simp only [hr, ↓reduceIte, b0, List.append_nil]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < p.n % 16
    · have pT : bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
          bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := by
        exact Pw.tail hr
      simp only [hr, ↓reduceIte, pT, hrest hr]
    · simp only [hr, ↓reduceIte]

/-- `body` for `open`. -/
theorem bodyOpen_ok (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {O0 : Block}
    (hofs : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (w64 p.K)) 0) :
    WP isa (body (VG.Proof.AesOcb.X86.callees v) false) s (VG.Proof.AesOcb.X86.BodyPost p
      (if 0 < p.n % 16 then
        Proof.Ocb.decBlocks (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
            (p.n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (w64 p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (w64 p.K) p.R
              (offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K))))
      else Proof.Ocb.decBlocks (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K))
        (bytesAt s.mem (w64 p.D) p.n) (p.n / 16))
      (if 0 < p.n % 16 then offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K)
       else offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16))
      (if 0 < p.n % 16 then
        Proof.Ocb.dckAt (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
            (p.n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem (w64 p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (w64 p.K) p.R
              (offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K)))))
      else Proof.Ocb.dckAt (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
        (p.n / 16)) s) := by
  have hd := L.dw
  obtain ⟨hl, hrest⟩ := VG.Proof.AesOcb.X86.body_facts L s.mem
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine VG.Proof.AesOcb.X86.seq_assoc (WP.seq (WP.mono (VG.Proof.AesOcb.X86.wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (w64 p.K))
    (G := fun m => ctxInv m (w64 p.K) p.R) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => ctxInv s.mem (w64 p.K) p.R
      (blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem (w64 p.K)) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem (w64 p.K)) (i + 1))
    v.decOk v.decNosp v.decStack (fun P _ hi => P.dec hi) (fun h => VG.Proof.AesOcb.X86.ctxInv_mut L h) (VG.Proof.AesOcb.X86.xorOfs_ok L) (VG.Proof.AesOcb.X86.openPost_ok L)
    L E hofs ho0 hck hl0 (fun _ _ => rfl) rfl (fun _ _ => rfl)) fun t Pw => ?_))
  have fW : Frame (VG.Proof.AesOcb.X86.mutR p) s.mem t.mem := VG.Proof.AesOcb.X86.bodyR_mut Pw.frame
  refine WP.mono (VG.Proof.AesOcb.X86.restIte_ok v false L Pw.env) fun t' Pt => ?_
  have cT : ctxCiph t.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R := VG.Proof.AesOcb.X86.ctxCiph_mut L fW
  have lT : ctxLstar t.mem (w64 p.K) = ctxLstar s.mem (w64 p.K) := VG.Proof.AesOcb.X86.lstar_mut L fW
  have blk : bytesAt t.mem (w64 p.D) (16 * (p.n / 16)) =
      Proof.Ocb.decBlocks (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
        (p.n / 16) := by
    rw [Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
    refine Proof.Ocb.flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, hl i hi, Proof.Ocb.decBlock,
      BitVec.xor_comm]
  have ckT : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
        (p.n / 16) := by
    rw [Pw.ck, Proof.Ocb.ckOf_dck fun i hi => by rw [hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  refine ⟨Pt.env, Pw.frame.trans Pt.frame, by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [VG.Proof.AesOcb.X86.body_out L Pt blk, Pt.out]
    by_cases hr : 0 < p.n % 16
    · have pT : bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
          bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := Pw.tail hr
      simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, hrest hr]
    · have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q (p.n % 16) = [] := fun _ _ => by
        rw [show p.n % 16 = 0 by omega]; rfl
      simp only [hr, ↓reduceIte, b0, List.append_nil]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < p.n % 16
    · have pT : bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
          bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := Pw.tail hr
      simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, hrest hr]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.TagIO`. -/
section

/-!
# AES-OCB on x86: the tag in and out, checking it and masking the data

Untrusted: everything here is checked by Lean. `tagOut` copies the first
`tag_len` bytes of the tag at `W` to `tag` (`tagOut_ok`); `recv` copies the
received tag to `W` (`recv_ok`); `cmp` ORs the XORs of the first `tag_len`
bytes at `W` and `W + t2O` and leaves 1 at `W + okO` if the OR is 0, else 0
(`cmp_ok`); `mask` ANDs every byte of the data with `0 − ok` (`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off in_off
  in_left covers_left length_bytesAt LoopPre CopyPost copyLoop_ok bytesAt_succ add_ofNat_assoc32)

/-! ## The tag out and in -/

theorem tagOut_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) (htw : Covers [⟨w64 p.T, p.tl⟩] s.wr) :
    WP isa tagOut s fun s' => s'.mem = writeBytes s.mem (w64 p.T) (bytesAt s.mem (w64 p.W) p.tl) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hT := E.slots.tg
  have hv := E.slots.tlen
  simp only [slotv_eq] at hT hv
  obtain ⟨s₁, run₁, di₁, dx₁, cx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .edi (.reg .ebp), .mov .edx (slot tgO), .mov .ecx (slot tlO)] s = some s₁ ∧
      s₁.gpr .edi = p.W ∧ s₁.gpr .edx = p.T ∧ s₁.gpr .ecx = BitVec.ofNat 32 p.tl ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv, hT], by gregs [E.ebp], by gregs [hT], by gregs [hv],
      fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [], by gmems []⟩
  unfold tagOut
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ht := L.tl16
  have lp : LoopPre s₁ p.W p.T p.tl := ⟨di₁, dx₁, cx₁, L.tl1, by omega, by have := L.ww; omega, L.tw,
    by rw [rd₁, wr₁]; exact VG.Proof.AesOcb.X86.covers_prefix (covers_left E.perm.w) (by omega),
    by rw [wr₁]; exact htw, (L.t_w.sub_right (Region.sub_prefix (by omega))).symm⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s' P => ⟨by rw [P.mem, m₁], fun r h₁ h₂ h₃ h₄ => by
    rw [P.other r h₁ h₄ h₃ h₂, g₁ r h₂ h₃ h₄], by rw [P.rd, rd₁], by rw [P.wr, wr₁]⟩

theorem recv_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) :
    WP isa recv s fun s' => s'.mem = writeBytes s.mem (w64 p.W) (bytesAt s.mem (w64 p.T) p.tl) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hT := E.slots.tg
  have hv := E.slots.tlen
  simp only [slotv_eq] at hT hv
  obtain ⟨s₁, run₁, di₁, dx₁, cx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .edi (slot tgO), .mov .edx (.reg .ebp), .mov .ecx (slot tlO)] s = some s₁ ∧
      s₁.gpr .edi = p.T ∧ s₁.gpr .edx = p.W ∧ s₁.gpr .ecx = BitVec.ofNat 32 p.tl ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv, hT], by gregs [hT], by gregs [E.ebp], by gregs [hv],
      fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [], by gmems []⟩
  unfold recv
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ht := L.tl16
  have lp : LoopPre s₁ p.T p.W p.tl := ⟨di₁, dx₁, cx₁, L.tl1, by omega, L.tw, by have := L.ww; omega,
    by rw [rd₁, wr₁]; exact E.perm.t, by rw [wr₁]; exact VG.Proof.AesOcb.X86.covers_prefix E.perm.w (by omega),
    L.t_w.sub_right (Region.sub_prefix (by omega))⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s' P => ⟨by rw [P.mem, m₁], fun r h₁ h₂ h₃ h₄ => by
    rw [P.other r h₁ h₄ h₃ h₂, g₁ r h₂ h₃ h₄], by rw [P.rd, rd₁], by rw [P.wr, wr₁]⟩

/-! ## `cmp` -/

theorem setWidth_xor_eq_zero32 (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32 = 0#32) ↔ a = b := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega),
      Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)] at this
  · intro h; rw [h]

theorem toNat_setWidth_xor32 (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).toNat < 256 := by
  simp only [BitVec.toNat_xor, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega), Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.xor_lt_two_pow (n := 8) a.isLt b.isLt

/-- `(x − 1) >> 31` is 1 if `x` is 0 and 0 if `0 < x < 256`. -/
theorem okBit32 {x : BitVec 32} (h : x.toNat < 256) :
    (x - BitVec.ofNat 32 1) >>> 31 = if x = 0#32 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := by
  by_cases hx : x = 0#32
  · subst hx; decide
  · simp only [hx, ↓reduceIte]
    have hx' : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hx
      · exact h0
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [show 2 ^ 32 - 1 % 2 ^ 32 + x.toNat = (x.toNat - 1) + 2 ^ 32 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

/-- One step of `cmp`. -/
theorem cmpStep_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {u : State} (E : VG.Proof.AesOcb.X86.Env p u) {j tl : Nat} (hj : j < tl) (ht : tl ≤ 16)
    (hdi : u.gpr .edi = p.W + BitVec.ofNat 32 j) (hcx : u.gpr .ecx = BitVec.ofNat 32 (tl - j)) :
    ∃ u', runBlock isa [.movzx8 .eax (at_ .edi 0), .movzx8 .ebx (at_ .edi t2O), .alu .xor .eax (.reg .ebx),
        .alu .or .edx (.reg .eax), .alu .add .edi (imm 1), .alu .sub .ecx (imm 1)] u = some u' ∧
      u'.mem = u.mem ∧
      u'.gpr .edx = u.gpr .edx ||| ((u.mem (w64 p.W + BitVec.ofNat 64 j)).setWidth 32 ^^^
        (u.mem (w64 p.W + BitVec.ofNat 64 (t2O + j))).setWidth 32) ∧
      u'.gpr .edi = p.W + BitVec.ofNat 32 (j + 1) ∧ u'.gpr .ecx = BitVec.ofNat 32 (tl - (j + 1)) ∧
      u'.zf = some (decide (j + 1 = tl)) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧
      u'.wr = u.wr := by
  have a0 : w64 (p.W + BitVec.ofNat 32 j + BitVec.ofNat 32 0) = w64 p.W + BitVec.ofNat 64 j := by
    rw [add_ofNat_assoc32, Nat.add_zero]; exact L.aW (by omega)
  have a1 : w64 (p.W + BitVec.ofNat 32 j + BitVec.ofNat 32 t2O) = w64 p.W + BitVec.ofNat 64 (t2O + j) := by
    rw [add_ofNat_assoc32, Nat.add_comm]; exact L.aW (by simp only [t2O]; omega)
  have r0 : InRegions (u.rd ++ u.wr) (w64 p.W + BitVec.ofNat 64 j) 1 := E.perm.wR (by omega)
  have r1 : InRegions (u.rd ++ u.wr) (w64 p.W + BitVec.ofNat 64 (t2O + j)) 1 := E.perm.wR (by simp only [t2O]; omega)
  refine ⟨_, by grun [hdi, a0, a1, r0, r1], by gmems [], by gregs [], ?_, ?_, ?_,
    fun r h₁ h₂ h₃ h₄ h₅ => by gregs [h₁, h₂, h₃, h₄, h₅], by gmems [], by gmems []⟩
  · gregs [hdi]; rw [add_ofNat_assoc32]
  · gregs [hcx]; rw [VG.Proof.AesOcb.X86.sub1_32 (by omega) (by omega), show tl - j - 1 = tl - (j + 1) by omega]
  · gmems [hcx]
    rw [VG.Proof.AesOcb.X86.sub1_32 (by omega) (by omega), VG.Proof.AesOcb.X86.beq_zero32 (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- `cmp`: 1 at `W + okO` if the first `tl` bytes at `W` and `W + t2O` are equal, else 0. -/
theorem cmp_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) :
    WP isa cmp s fun t => t.mem = s.mem.writeW (w64 p.W + BitVec.ofNat 64 okO)
        (if bytesAt s.mem (w64 p.W) p.tl = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl then BitVec.ofNat 32 1
         else BitVec.ofNat 32 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have hv := E.slots.tlen
  simp only [slotv_eq] at hv
  have h1 := L.tl1
  have h16 := L.tl16
  obtain ⟨s₁, run₁, dx₁, di₁, cx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .edx (imm 0), .mov .edi (.reg .ebp), .mov .ecx (slot tlO)] s = some s₁ ∧
      s₁.gpr .edx = 0#32 ∧ s₁.gpr .edi = p.W + BitVec.ofNat 32 0 ∧ s₁.gpr .ecx = BitVec.ofNat 32 (p.tl - 0) ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv], by gregs [], by gregs [E.ebp]; exact (BitVec.add_zero _).symm,
      by gregs [hv, Nat.sub_zero], fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [], by gmems []⟩
  unfold cmp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (WP.loop (M := isa) (c := .ne)
    (Q := fun u => (u.gpr .edx).toNat < 256 ∧
      (u.gpr .edx = 0#32 ↔ bytesAt s.mem (w64 p.W) p.tl = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl) ∧
      u.mem = s.mem ∧ (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr)
    (fun (k : Nat) (u : State) => ∃ j, k = p.tl - j ∧ j < p.tl ∧ u.gpr .edi = p.W + BitVec.ofNat 32 j ∧
      u.gpr .ecx = BitVec.ofNat 32 (p.tl - j) ∧ (u.gpr .edx).toNat < 256 ∧
      (u.gpr .edx = 0#32 ↔ bytesAt s.mem (w64 p.W) j = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) j) ∧
      u.mem = s.mem ∧ (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr) ?_ (p.tl - 0) _
    ⟨0, rfl, by omega, di₁, cx₁, by rw [dx₁]; decide, by rw [dx₁]; simp [bytesAt], m₁,
      fun r _ _ h₃ h₄ h₅ => g₁ r h₃ h₄ h₅, rd₁, wr₁⟩) fun u hu => ?_)
  · rintro k u ⟨j, rfl, hj, di, cx, lt, iff, mem, g, rd, wr⟩
    have Eu : VG.Proof.AesOcb.X86.Env p u := E.keep (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]) rd wr mem
    obtain ⟨u', run', mem', dx', di', cx', zf', g', rd', wr'⟩ := VG.Proof.AesOcb.X86.cmpStep_ok L Eu hj h16 di cx
    refine WP.of_runBlock ⟨u', run', ?_⟩
    rw [mem] at dx'
    have lt' : (u'.gpr .edx).toNat < 256 := by
      rw [dx', BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 8) lt (VG.Proof.AesOcb.X86.toNat_setWidth_xor32 _ _)
    have iff' : u'.gpr .edx = 0#32 ↔
        bytesAt s.mem (w64 p.W) (j + 1) = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) (j + 1) := by
      rw [dx', BitVec.or_eq_zero_iff, iff, VG.Proof.AesOcb.X86.setWidth_xor_eq_zero32, bytesAt_succ, bytesAt_succ, VG.Proof.AesOcb.X86.add_ofNat_assoc]
      constructor
      · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
      · intro h
        obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [length_bytesAt, length_bytesAt])
        exact ⟨h₁, List.head_eq_of_cons_eq h₂⟩
    have gg : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → u'.gpr r = s.gpr r :=
      fun r h₁ h₂ h₃ h₄ h₅ => by rw [g' r h₁ h₂ h₃ h₄ h₅, g r h₁ h₂ h₃ h₄ h₅]
    by_cases he : j + 1 = p.tl
    · left
      refine ⟨(VG.Proof.AesOcb.X86.eval_ne zf').trans (by simp [he]), lt', ?_, by rw [mem', mem], gg, by rw [rd', rd], by rw [wr', wr]⟩
      rw [← he]; exact iff'
    · right
      exact ⟨(VG.Proof.AesOcb.X86.eval_ne zf').trans (by simp [he]), p.tl - (j + 1), by omega, j + 1, rfl, by omega, di', cx', lt', iff',
        by rw [mem', mem], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · obtain ⟨lt, iff, mem, g, rd, wr⟩ := hu
    have Eu : VG.Proof.AesOcb.X86.Env p u := E.keep (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]) rd wr mem
    have hb := VG.Proof.AesOcb.X86.okBit32 lt
    refine WP.of_runBlock ⟨_, by grun [Eu.ebp, L.aW, Eu.perm.wW], ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, ?_, ?_⟩
    · gmems [mem, hb]
      by_cases h : u.gpr .edx = 0#32
      · simp only [h, ↓reduceIte, iff.mp h]
      · have h' : ¬ bytesAt s.mem (w64 p.W) p.tl = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl :=
          fun e => h (iff.mpr e)
        simp only [h, h', ↓reduceIte]
    · gregs [h₄]; exact g r h₁ h₂ h₃ h₄ h₅
    · gmems []; exact rd
    · gmems []; exact wr

/-! ## `mask` -/

theorem mask_byte32 (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- One step of `mask`. -/
theorem maskStep_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {u : State} {j : Nat} {c : Bool} (hj : j < p.n)
    (hdi : u.gpr .edi = p.D + BitVec.ofNat 32 j) (hcx : u.gpr .ecx = BitVec.ofNat 32 (p.n - j))
    (hdx : u.gpr .edx = 0 - (if c then 1 else 0))
    (r : InRegions (u.rd ++ u.wr) (w64 p.D + BitVec.ofNat 64 j) 1) (w : InRegions u.wr (w64 p.D + BitVec.ofNat 64 j) 1) :
    ∃ u', runBlock isa [.movzx8 .eax (at_ .edi 0), .alu .and .eax (.reg .edx), .store8 (at_ .edi 0) .al,
        .alu .add .edi (imm 1), .alu .sub .ecx (imm 1)] u = some u' ∧
      u'.mem = u.mem.writeW (w64 p.D + BitVec.ofNat 64 j)
        ((if c then u.mem (w64 p.D + BitVec.ofNat 64 j) else 0 : Byte)) ∧
      u'.gpr .edi = p.D + BitVec.ofNat 32 (j + 1) ∧ u'.gpr .ecx = BitVec.ofNat 32 (p.n - (j + 1)) ∧
      u'.zf = some (decide (j + 1 = p.n)) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ecx → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have hn := L.n32
  have a0 : w64 (p.D + BitVec.ofNat 32 j + BitVec.ofNat 32 0) = w64 p.D + BitVec.ofNat 64 j := by
    rw [add_ofNat_assoc32, Nat.add_zero]; exact w64_add (by have := L.dw; omega)
  refine ⟨_, by grun [hdi, a0, r, w], by gmems [hdx, VG.Proof.AesOcb.X86.mask_byte32], ?_, ?_, ?_,
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  · gregs [hdi]; rw [add_ofNat_assoc32]
  · gregs [hcx]; rw [VG.Proof.AesOcb.X86.sub1_32 (by omega) (by omega), show p.n - j - 1 = p.n - (j + 1) by omega]
  · gmems [hcx]
    rw [VG.Proof.AesOcb.X86.sub1_32 (by omega) (by omega), VG.Proof.AesOcb.X86.beq_zero32 (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- Every byte of the data ANDed with `0 − ok`, for `ok` (at `W + okO`) 1 or 0. -/
theorem mask_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) {c : Bool}
    (hok : slotv s.mem p.W okO = if c then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) :
    WP isa mask s fun s' => s'.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) p.n else zeros p.n) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn := L.n32
  have hd := L.dw
  have hD := E.slots.data
  have hl := E.slots.len
  simp only [slotv_eq] at hD hl hok
  obtain ⟨s₁, run₁, di₁, cx₁, dx₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .edi (slot dataO),
      .mov .ecx (slot lenO), .mov .edx (imm 0), .alu .sub .edx (slot okO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧
      s₁.gpr .edi = p.D + BitVec.ofNat 32 0 ∧ s₁.gpr .ecx = BitVec.ofNat 32 (p.n - 0) ∧
      s₁.gpr .edx = 0 - (if c then 1 else 0) ∧ s₁.zf = some (decide (p.n = 0)) ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hD, hl, hok], by gregs [hD]; exact (BitVec.add_zero _).symm,
      by gregs [hl, Nat.sub_zero], ?_, ?_, fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [],
      by gmems []⟩
    · gregs [hok]; cases c <;> rfl
    · gmems [hl, BitVec.and_self, VG.Proof.AesOcb.X86.beq_zero32 hn]
  unfold mask
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (p.n = 0)) (VG.Proof.AesOcb.X86.eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : p.n = 0 := of_decide_eq_true hb
    refine ⟨?_, fun r h₁ h₂ h₃ h₄ => g₁ r h₂ h₃ h₄, rd₁, wr₁⟩
    rw [m₁, hn0]
    cases c <;> simp [bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < p.n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = p.n - j ∧ j < p.n ∧ t.gpr .edi = p.D + BitVec.ofNat 32 j ∧
      t.gpr .ecx = BitVec.ofNat 32 (p.n - j) ∧ t.gpr .edx = 0 - (if c then 1 else 0) ∧
      t.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) j else zeros j) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_
    (p.n - 0) _ ⟨0, rfl, hn0, di₁, cx₁, dx₁, by rw [m₁]; cases c <;> simp [bytesAt, zeros, writeBytes_nil],
      fun r _ h₂ h₃ h₄ => g₁ r h₂ h₃ h₄, rd₁, wr₁⟩
  rintro k t ⟨j, rfl, hj, di, cx, dx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', di', cx', zf', g', rd', wr'⟩ := VG.Proof.AesOcb.X86.maskStep_ok L (c := c) hj di cx dx
    (by rw [rd, wr]; exact in_left (in_off E.perm.d (by omega) (by omega)))
    (by rw [wr]; exact in_off E.perm.d (by omega) (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨w64 p.D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesOcb.X86.length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (w64 p.D + BitVec.ofNat 64 j) = s.mem (w64 p.D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 p.D) (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) (j + 1) else zeros (j + 1)) := by
    rw [mem', hq, mem, VG.Proof.AesOcb.X86.mask_succ, writeBytes_snoc _ _ _ _ (by rw [VG.Proof.AesOcb.X86.length_mask]; omega), VG.Proof.AesOcb.X86.length_mask]
  have gg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₄ h₂, g r h₁ h₂ h₃ h₄]
  by_cases he : j + 1 = p.n
  · left
    exact ⟨(VG.Proof.AesOcb.X86.eval_ne zf').trans (by simp [he]), by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    exact ⟨(VG.Proof.AesOcb.X86.eval_ne zf').trans (by simp [he]), p.n - (j + 1), by omega, j + 1, rfl, by omega, di', cx',
      by rw [g' _ (by decide) (by decide) (by decide), dx], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Front`. -/
section

/-!
# AES-OCB on x86: up to the tag (`front`)

Untrusted: everything here is checked by Lean. `front` is the entry
(`entry_ok`), `L_$`, `L_0` and the checksum (`setup_ok`), `Offset_0`
(`nonce_ok`) and `HASH` (`hash_ok`), which leave `Pre` (`pre_ok`); then the
data (`bodySeal_ok`, `bodyOpen_ok`) and the tag at `W + d` (`tag_ok`)
(`sealFront_ok`, `openFront_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxInv ctxLstar pad lDollar)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq SavedAt length_bytesAt)

/-- What the entry writes: the saved registers and the slots. -/
abbrev entryR (p : VG.Proof.AesOcb.X86.Prm) : Region := ⟨w64 p.W + BitVec.ofNat 64 128, 88⟩

/-- A buffer apart from `W` and the stack and the data keeps its bytes across
a frame of `entryR :: mutR`. -/
theorem bytes_front {p : VG.Proof.AesOcb.X86.Prm} {P : BitVec 32} {len : Nat}
    (hw : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) (hb : (VG.Proof.AesOcb.X86.stk p).Disjoint ⟨w64 P, len⟩)
    (hd : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩) (hl : len ≤ 2 ^ 64) {m m' : Mem}
    (hf : Frame (VG.Proof.AesOcb.X86.entryR p :: VG.Proof.AesOcb.X86.mutR p) m m') : bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Region.sub_prefix (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hb.symm
    · exact hd) hl

/-- What the pieces before the data leave, from the state `s` at the call. -/
structure Pre (p : VG.Proof.AesOcb.X86.Prm) (s s' : State) : Prop where
  env : VG.Proof.AesOcb.X86.Env p s'
  frame : Frame (VG.Proof.AesOcb.X86.entryR p :: VG.Proof.AesOcb.X86.mutR p) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : SavedAt s'.mem p.W s
  ofs : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (ctxCiph s.mem (w64 p.K) p.R) p.tl (bytesAt s.mem (w64 p.N) p.nl)
  o0 : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (ctxCiph s.mem (w64 p.K) p.R) p.tl (bytesAt s.mem (w64 p.N) p.nl)
  ck : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K))
  l0 : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (w64 p.K)) 0
  sum : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s.mem (w64 p.K) p.R) (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.A) p.al)
  ciph : ctxCiph s'.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R
  inv : ctxInv s'.mem (w64 p.K) p.R = ctxInv s.mem (w64 p.K) p.R
  lstar : ctxLstar s'.mem (w64 p.K) = ctxLstar s.mem (w64 p.K)
  data : bytesAt s'.mem (w64 p.D) p.n = bytesAt s.mem (w64 p.D) p.n
  tag : bytesAt s'.mem (w64 p.T) p.tl = bytesAt s.mem (w64 p.T) p.tl

/-- The key context misses `entryR :: mutR`. -/
theorem k_front {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) : ∀ r ∈ VG.Proof.AesOcb.X86.entryR p :: VG.Proof.AesOcb.X86.mutR p, (⟨w64 p.K, 256⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact L.k_w' (by decide)
  · exact VG.Proof.AesOcb.X86.k_mut L r hr

theorem front_ciph {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.entryR p :: VG.Proof.AesOcb.X86.mutR p) m m') :
    ctxCiph m' (w64 p.K) p.R = ctxCiph m (w64 p.K) p.R ∧ ctxInv m' (w64 p.K) p.R = ctxInv m (w64 p.K) p.R ∧
      ctxLstar m' (w64 p.K) = ctxLstar m (w64 p.K) := by
  have hb := L.rounds_le
  refine ⟨?_, ?_, Proof.Ocb.blockAtMem_frame h fun r hr => (VG.Proof.AesOcb.X86.k_front L r hr).sub_left (Offset.sub_base _ (by decide))⟩
  · unfold ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame h (fun r hr => (VG.Proof.AesOcb.X86.k_front L r hr).sub_left (Region.sub_prefix (by omega)))
      (by omega)]
  · unfold ctxInv
    rw [Proof.AesGcm.X86.bytesAt_frame h (fun r hr => (VG.Proof.AesOcb.X86.k_front L r hr).sub_left (Region.sub_prefix (by omega)))
      (by omega)]

theorem mut_front {p : VG.Proof.AesOcb.X86.Prm} {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.mutR p) m m') : Frame (VG.Proof.AesOcb.X86.entryR p :: VG.Proof.AesOcb.X86.mutR p) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

theorem entry_front {p : VG.Proof.AesOcb.X86.Prm} {m m' : Mem} (h : Frame [VG.Proof.AesOcb.X86.entryR p] m m') : Frame (VG.Proof.AesOcb.X86.entryR p :: VG.Proof.AesOcb.X86.mutR p) m m' :=
  h.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..

/-- The saved registers, after a frame within `mutR`. -/
theorem saved_mut {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.mutR p) m m') {s₀ : State}
    (S : SavedAt m p.W s₀) : SavedAt m' p.W s₀ := SavedAt.mut L h S

theorem pre_ok (v : BlocksImpl) {s : State} (h : VG.Proof.AesOcb.X86.onePre s) :
    WP isa (.seq ocbEntry (.seq (.block setup) (.seq (nonce (VG.Proof.AesOcb.X86.callees v)) (hash (VG.Proof.AesOcb.X86.callees v))))) s
      (VG.Proof.AesOcb.X86.Pre (VG.Proof.AesOcb.X86.prmOf s) s) := by
  have L := VG.Proof.AesOcb.X86.lay_of h
  generalize hp : VG.Proof.AesOcb.X86.prmOf s = p at L
  refine WP.seq (WP.mono (hp ▸ VG.Proof.AesOcb.X86.entry_ok h) fun s₁ En => ?_)
  have fr₁ := VG.Proof.AesOcb.X86.entry_front En.frame
  obtain ⟨c₁, i₁, l₁⟩ := VG.Proof.AesOcb.X86.front_ciph L fr₁
  have hN₁ := VG.Proof.AesOcb.X86.bytes_front L.n_w L.bn L.n_d (by have := L.nl15; omega) fr₁
  have hA₁ := VG.Proof.AesOcb.X86.bytes_front L.a_w L.ba L.a_d (by have := L.aw; omega) fr₁
  have hD₁ := Proof.AesGcm.X86.bytesAt_frame En.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by have := L.dw; omega)
  have hT₁ := VG.Proof.AesOcb.X86.bytes_front L.t_w L.bt L.t_d (by have := L.tl16; omega) fr₁
  -- `L_$`, `L_0` and the checksum
  obtain ⟨s₂, run₂, P₂⟩ := VG.Proof.AesOcb.X86.setup_ok L En.env
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have f₂ : Frame (VG.Proof.AesOcb.X86.mutR p) s₁.mem s₂.mem := P₂.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp
  have E₂ : VG.Proof.AesOcb.X86.Env p s₂ := En.env.mut L (by rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide), En.env.ebp])
    (by rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide), En.env.esp]) P₂.rd P₂.wr f₂
  -- `Offset_0`
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.nonce_ok v L E₂) fun s₃ P₃ => ?_)
  have f₃ : Frame (VG.Proof.AesOcb.X86.mutR p) s₂.mem s₃.mem := VG.Proof.AesOcb.X86.wR_mut P₃.frame
  have f₁₃ := f₂.trans f₃
  obtain ⟨c₂, -, l₂⟩ := VG.Proof.AesOcb.X86.front_ciph L (VG.Proof.AesOcb.X86.mut_front f₂)
  have hN₂ := VG.Proof.AesOcb.X86.nonce_mut L f₂
  -- `HASH`
  have C : VG.Proof.AesOcb.X86.HCtx p (ctxCiph s₃.mem (w64 p.K) p.R) (ctxLstar s₃.mem (w64 p.K)) (bytesAt s₃.mem (w64 p.A) p.al) s₃ :=
    ⟨L, rfl, rfl, rfl⟩
  have hl0₃ : blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s₃.mem (w64 p.K)) 0 := by
    rw [P₃.keep (by decide) (by decide), P₂.l0, (VG.Proof.AesOcb.X86.front_ciph L (VG.Proof.AesOcb.X86.mut_front f₃)).2.2, l₂]
  refine WP.mono (VG.Proof.AesOcb.X86.hash_ok v C P₃.env hl0₃) fun s₄ ⟨E₄, F₄, sum₄, rd₄, wr₄⟩ => ?_
  have f₄ : Frame (VG.Proof.AesOcb.X86.mutR p) s₃.mem s₄.mem := VG.Proof.AesOcb.X86.wR_mut (VG.Proof.AesOcb.X86.hashR_wR F₄)
  have f₁₄ := f₁₃.trans f₄
  have fr := fr₁.trans (VG.Proof.AesOcb.X86.mut_front f₁₄)
  obtain ⟨c₄, i₄, l₄⟩ := VG.Proof.AesOcb.X86.front_ciph L fr
  obtain ⟨c₃, -, l₃⟩ := VG.Proof.AesOcb.X86.front_ciph L (VG.Proof.AesOcb.X86.mut_front f₁₃)
  have k₄ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (176 ≤ d ∧ d + 16 ≤ 220) ∨
      (224 ≤ d ∧ d + 16 ≤ 264)) →
      blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun {d} hd => Proof.Ocb.blockAtMem_frame F₄ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Lay.w_w (by simp only [sumO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [lO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [ohO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [kO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [hlO]; omega) (by omega) (by decide)
      · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.bw' (by omega)).symm
  have kS : ∀ {d : Nat}, d + 16 ≤ 128 → 32 ≤ d → d + 16 ≤ 112 →
      blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun _ h₁ h₂ => P₃.keep h₁ h₂
  refine ⟨E₄, fr, by rw [rd₄, P₃.rd, P₂.rd, En.rd], by rw [wr₄, P₃.wr, P₂.wr, En.wr], VG.Proof.AesOcb.X86.saved_mut L f₁₄ En.saved,
    ?_, ?_, ?_, ?_, ?_, ?_, c₄, i₄, l₄, ?_, ?_⟩
  · rw [k₄ (by decide), P₃.ofs, c₂, c₁, hN₂, hN₁, ← hp]
  · rw [k₄ (by decide), P₃.o0, c₂, c₁, hN₂, hN₁, ← hp]
  · rw [k₄ (by decide), kS (by decide) (by decide) (by decide), P₂.ck]
  · rw [k₄ (by decide), kS (by decide) (by decide) (by decide), P₂.ld, l₁]
  · rw [k₄ (by decide), kS (by decide) (by decide) (by decide), P₂.l0, l₁]
  · rw [sum₄, c₃, l₃, c₁, l₁, VG.Proof.AesOcb.X86.aad_mut L f₁₃, hA₁]
  · rw [VG.Proof.AesOcb.X86.data_wR L (VG.Proof.AesOcb.X86.hashR_wR F₄), VG.Proof.AesOcb.X86.data_wR L P₃.frame, VG.Proof.AesOcb.X86.data_wR L (P₂.frame.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp), hD₁]
  · rw [VG.Proof.AesOcb.X86.tag_mut L f₁₄, hT₁]

theorem seq_cont3 {a b c d k : Prog isa} {s : State} {P Q : State → Prop}
    (h : WP isa (.seq a (.seq b (.seq c d))) s P) (hk : ∀ t, P t → WP isa k t Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d k)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h₁ => WP.seq (WP.mono (WP.seq_iff.mp h₁) fun _ h₂ =>
    WP.seq (WP.mono (WP.seq_iff.mp h₂) fun _ h₃ => WP.seq (WP.mono h₃ hk))))

/-- `body`'s frame misses a block of `W` outside the offset, the checksum,
`[96, 128)` and `[144, 160)`. -/
theorem body_keep {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86.bodyR p) m m') {d : Nat}
    (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (128 ≤ d ∧ d + 16 ≤ 144) ∨ (160 ≤ d ∧ d + 16 ≤ 216)) :
    blockAtMem m' (w64 p.W + BitVec.ofNat 64 d) = blockAtMem m (w64 p.W + BitVec.ofNat 64 d) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (by omega) (by omega) (by decide)
    · exact Lay.w_w (by omega) (by omega) (by decide)
    · exact Lay.w_w (by simp only [t2O]; omega) (by omega) (by decide)
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.bw' (by omega)).symm
    · exact (L.d_w' (by omega)).symm

/-- What `tag d` writes, within `mutR`. -/
theorem tagR_mut {p : VG.Proof.AesOcb.X86.Prm} {d : Nat} (hd : d = tagO ∨ d = t2O) {m m' : Mem}
    (h : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 d, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, VG.Proof.AesOcb.X86.stk p] m m') : Frame (VG.Proof.AesOcb.X86.mutR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))
  · rcases hd with rfl | rfl
    · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))
    · exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact VG.Proof.AesOcb.X86.inMut_stk p

/-- The data across `tag`. -/
theorem data_tag {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {d : Nat} (hd : d = tagO ∨ d = t2O) {m m' : Mem}
    (h : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 d, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, VG.Proof.AesOcb.X86.stk p] m m') :
    bytesAt m' (w64 p.D) p.n = bytesAt m (w64 p.D) p.n :=
  Proof.AesGcm.X86.bytesAt_frame h (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by rcases hd with rfl | rfl <;> decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm) (by have := L.dw; omega)

/-- What `front` leaves: the environment, our caller's registers, the data
and the tag at `W + d`. -/
structure Front (p : VG.Proof.AesOcb.X86.Prm) (s s' : State) : Prop where
  env : VG.Proof.AesOcb.X86.Env p s'
  frame : Frame (VG.Proof.AesOcb.X86.entryR p :: VG.Proof.AesOcb.X86.mutR p) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : SavedAt s'.mem p.W s

/-- `front` for `seal`: the ciphertext over the data and the tag at `W`. -/
theorem sealFront_ok (v : BlocksImpl) {s : State} (h : VG.Proof.AesOcb.X86.onePre s) :
    WP isa (front (VG.Proof.AesOcb.X86.callees v) true tagO) s fun s' => VG.Proof.AesOcb.X86.Front (VG.Proof.AesOcb.X86.prmOf s) s s' ∧
      Spec.Ocb.encryptWith (ctxCiph s.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).K) (VG.Proof.AesOcb.X86.prmOf s).R) (ctxLstar s.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).K))
          (VG.Proof.AesOcb.X86.prmOf s).tl (bytesAt s.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).N) (VG.Proof.AesOcb.X86.prmOf s).nl) (bytesAt s.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).A) (VG.Proof.AesOcb.X86.prmOf s).al)
          (bytesAt s.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).D) (VG.Proof.AesOcb.X86.prmOf s).n) =
        (bytesAt s'.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).D) (VG.Proof.AesOcb.X86.prmOf s).n, bytesAt s'.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).W) (VG.Proof.AesOcb.X86.prmOf s).tl) := by
  have L := VG.Proof.AesOcb.X86.lay_of h
  have Pp := VG.Proof.AesOcb.X86.pre_ok v h
  generalize VG.Proof.AesOcb.X86.prmOf s = p at L Pp ⊢
  unfold front
  refine VG.Proof.AesOcb.X86.seq_cont3 Pp fun s₃ P₃ => ?_
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.bodySeal_ok v L P₃.env P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar])) fun s₄ B => ?_)
  have F₄ : Frame (VG.Proof.AesOcb.X86.mutR p) s₃.mem s₄.mem := VG.Proof.AesOcb.X86.bodyR_mut B.frame
  have cK₄ : ctxCiph s₄.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R := (VG.Proof.AesOcb.X86.ctxCiph_mut L F₄).trans P₃.ciph
  have ld₄ : blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K)) := by
    rw [VG.Proof.AesOcb.X86.body_keep L B.frame (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem (w64 p.K) p.R) (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.A) p.al) := by
    rw [VG.Proof.AesOcb.X86.body_keep L B.frame (d := sumO) (by decide), P₃.sum]
  refine WP.mono (VG.Proof.AesOcb.X86.tag_ok v L B.env (d := tagO) (.inl rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (VG.Proof.AesOcb.X86.mutR p) s₄.mem s₅.mem := VG.Proof.AesOcb.X86.tagR_mut (.inl rfl) T₅.frame
  refine ⟨⟨T₅.env, P₃.frame.trans (VG.Proof.AesOcb.X86.mut_front (F₄.trans F₅)), by rw [T₅.rd, B.rd, P₃.rd],
    by rw [T₅.wr, B.wr, P₃.wr], VG.Proof.AesOcb.X86.saved_mut L (F₄.trans F₅) P₃.saved⟩, ?_⟩
  have hout := B.out
  rw [P₃.ciph, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [P₃.data] at hck
  have tv := T₅.val
  rw [show w64 p.W + BitVec.ofNat 64 tagO = w64 p.W from BitVec.add_zero _] at tv
  rw [Proof.Ocb.encryptWith_eq, VG.Proof.AesOcb.X86.data_tag L (.inl rfl) T₅.frame, hout, Proof.Ocb.bytesAt_take_block _ _ L.tl16, tv,
    hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < p.n % 16
  · have h' : p.n - 16 * (p.n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (p.n - 16 * (p.n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte]

/-- `front` for `open`: the plaintext over the data and the tag at
`W + t2O`, which decide `OCB-DECRYPT` with the tag `tag`. -/
theorem openFront_ok (v : BlocksImpl) {s : State} (h : VG.Proof.AesOcb.X86.onePre s) (tag : List Byte) :
    WP isa (front (VG.Proof.AesOcb.X86.callees v) false t2O) s fun s' => VG.Proof.AesOcb.X86.Front (VG.Proof.AesOcb.X86.prmOf s) s s' ∧
      Spec.Ocb.decryptWith (ctxCiph s.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).K) (VG.Proof.AesOcb.X86.prmOf s).R) (ctxInv s.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).K) (VG.Proof.AesOcb.X86.prmOf s).R)
          (ctxLstar s.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).K)) (VG.Proof.AesOcb.X86.prmOf s).tl (bytesAt s.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).N) (VG.Proof.AesOcb.X86.prmOf s).nl)
          (bytesAt s.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).A) (VG.Proof.AesOcb.X86.prmOf s).al) (bytesAt s.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).D) (VG.Proof.AesOcb.X86.prmOf s).n) tag =
        if bytesAt s'.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).W + BitVec.ofNat 64 t2O) (VG.Proof.AesOcb.X86.prmOf s).tl = tag then
          some (bytesAt s'.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).D) (VG.Proof.AesOcb.X86.prmOf s).n)
        else none := by
  have L := VG.Proof.AesOcb.X86.lay_of h
  have Pp := VG.Proof.AesOcb.X86.pre_ok v h
  generalize VG.Proof.AesOcb.X86.prmOf s = p at L Pp ⊢
  unfold front
  refine VG.Proof.AesOcb.X86.seq_cont3 Pp fun s₃ P₃ => ?_
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.bodyOpen_ok v L P₃.env P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar])) fun s₄ B => ?_)
  have F₄ : Frame (VG.Proof.AesOcb.X86.mutR p) s₃.mem s₄.mem := VG.Proof.AesOcb.X86.bodyR_mut B.frame
  have cK₄ : ctxCiph s₄.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R := (VG.Proof.AesOcb.X86.ctxCiph_mut L F₄).trans P₃.ciph
  have ld₄ : blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K)) := by
    rw [VG.Proof.AesOcb.X86.body_keep L B.frame (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem (w64 p.K) p.R) (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.A) p.al) := by
    rw [VG.Proof.AesOcb.X86.body_keep L B.frame (d := sumO) (by decide), P₃.sum]
  refine WP.mono (VG.Proof.AesOcb.X86.tag_ok v L B.env (d := t2O) (.inr rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (VG.Proof.AesOcb.X86.mutR p) s₄.mem s₅.mem := VG.Proof.AesOcb.X86.tagR_mut (.inr rfl) T₅.frame
  refine ⟨⟨T₅.env, P₃.frame.trans (VG.Proof.AesOcb.X86.mut_front (F₄.trans F₅)), by rw [T₅.rd, B.rd, P₃.rd],
    by rw [T₅.wr, B.wr, P₃.wr], VG.Proof.AesOcb.X86.saved_mut L (F₄.trans F₅) P₃.saved⟩, ?_⟩
  have hout := B.out
  rw [P₃.ciph, P₃.inv, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [P₃.ciph, P₃.inv, P₃.lstar, P₃.data] at hck
  rw [Proof.Ocb.decryptWith_eq, VG.Proof.AesOcb.X86.data_tag L (.inr rfl) T₅.frame, hout, Proof.Ocb.bytesAt_take_block _ _ L.tl16,
    T₅.val, hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < p.n % 16
  · have h' : p.n - 16 * (p.n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (p.n - 16 * (p.n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte]

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Seal`. -/
section

/-!
# AES-OCB on x86: `vg_aes_ocb_seal` and `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `seal` is `front` (the
ciphertext and the tag at `W`), the copy of the tag to `tag` (`tagOut`) and
`restore` (`seal_wp`); `open` is `front` (the plaintext and the tag at
`W + t2O`), the received tag copied to `W` (`recv`), their comparison
(`cmp`), the mask of the data (`mask`), and `ok` in `eax` before `restore`
(`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot restore)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq SavedAt exit_ok covers_left length_bytesAt bytesAt_writeBytes_self
  writeBytes_frame')

/-- The return address misses what `front` writes. -/
theorem ret_front {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) : ∀ r ∈ VG.Proof.AesOcb.X86.entryR p :: VG.Proof.AesOcb.X86.mutR p, (⟨w64 p.SP, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.retW.sub_right (Lay.wSub (by decide))
  · exact L.retW.sub_right (Region.sub_prefix (by decide))
  · exact L.retW.sub_right (Lay.wSub (by decide))
  · exact L.retW.sub_right (Lay.wSub (by decide))
  · exact L.retW.sub_right (Lay.wSub (by decide))
  · exact Proof.AesGcm.X86.ret_below L.sp
  · exact L.retD

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp (v : BlocksImpl) {s : State} (h : VG.Proof.AesOcb.X86.sealPre s) :
    WP isa («seal» (VG.Proof.AesOcb.X86.callees v)) s fun s' => abiPreserved s s' ∧ sealX86.post s s' := by
  have h₁ := VG.Proof.AesOcb.X86.onePre_seal h
  have L := VG.Proof.AesOcb.X86.lay_of h₁
  have hTw : Covers [VG.Proof.AesOcb.X86.tagR s] s.wr := VG.Proof.AesOcb.X86.covers_of_mem (by rw [h.2.1]; simp)
  unfold «seal»
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.sealFront_ok v h₁) fun s₅ ⟨F, out⟩ => ?_)
  -- The copy of the tag.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.tagOut_ok L F.env (by rw [F.wr]; exact hTw)) fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  have f₆ : Frame [⟨w64 (VG.Proof.AesOcb.X86.prmOf s).T, (VG.Proof.AesOcb.X86.prmOf s).tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have S₆ : SavedAt s₆.mem (VG.Proof.AesOcb.X86.prmOf s).W s := F.saved.frame f₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (L.t_w' (d := 128) (k := 16) (by decide)).symm
  have hret : s₆.mem.readW (w64 (s.gpr .esp)) 32 = s.mem.readW (w64 (s.gpr .esp)) 32 := by
    rw [f₆.readW (r := ⟨w64 (VG.Proof.AesOcb.X86.prmOf s).SP, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.retT) (by decide)]
    exact F.frame.readW (r := ⟨w64 (VG.Proof.AesOcb.X86.prmOf s).SP, 4⟩) (Region.contains_self _ _) (VG.Proof.AesOcb.X86.ret_front L) (by decide)
  -- `restore`.
  refine WP.mono (exit_ok (s₀ := s) (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), F.env.ebp])
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), F.env.esp]; rfl)
    (by rw [rd₆, wr₆]; exact covers_left F.env.perm.w) L.ww S₆ hret) fun s₇ ⟨ab, m₇, _, _, _⟩ => ⟨ab, ?_⟩
  have hd : bytesAt s₆.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).D) (VG.Proof.AesOcb.X86.prmOf s).n = bytesAt s₅.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).D) (VG.Proof.AesOcb.X86.prmOf s).n :=
    Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_d.symm) (by have := L.dw; omega)
  have ht : bytesAt s₆.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).T) (VG.Proof.AesOcb.X86.prmOf s).tl = bytesAt s₅.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).W) (VG.Proof.AesOcb.X86.prmOf s).tl := by
    have := bytesAt_writeBytes_self s₅.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).T) (bytesAt s₅.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).W) (VG.Proof.AesOcb.X86.prmOf s).tl)
      (by rw [length_bytesAt]; have := L.tl16; omega)
    rw [length_bytesAt] at this
    rw [m₆]; exact this
  show _ = (bytesAt s₇.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).D) (VG.Proof.AesOcb.X86.prmOf s).n, bytesAt s₇.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).T) (VG.Proof.AesOcb.X86.prmOf s).tl)
  rw [m₇, hd, ht]
  exact out

/-- `ok` into `eax`. -/
theorem retEax_ok {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {s : State} (E : VG.Proof.AesOcb.X86.Env p s) :
    ∃ s', runBlock isa [.mov .eax (slot okO)] s = some s' ∧ s'.gpr .eax = slotv s.mem p.W okO ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by grun [E.ebp, L.aW, E.perm.wR], by gregs [], fun r h₁ => by gregs [h₁], by gmems [], by gmems [],
    by gmems []⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp (v : BlocksImpl) {s : State} (h : VG.Proof.AesOcb.X86.openPre s) :
    WP isa («open» (VG.Proof.AesOcb.X86.callees v)) s fun s' => abiPreserved s s' ∧ openX86.post s s' := by
  have h₁ := VG.Proof.AesOcb.X86.onePre_open h
  have L := VG.Proof.AesOcb.X86.lay_of h₁
  unfold «open»
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.openFront_ok v h₁ (bytesAt s.mem (w64 (VG.Proof.AesOcb.X86.prmOf s).T) (VG.Proof.AesOcb.X86.prmOf s).tl)) fun s₅ ⟨F, out⟩ => ?_)
  set p := VG.Proof.AesOcb.X86.prmOf s with hp
  have ht := L.tl16
  -- The received tag.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.recv_ok L F.env) fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  have f₆ : Frame [⟨w64 p.W, p.tl⟩] s₅.mem s₆.mem := by rw [m₆]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have F₆ : Frame (VG.Proof.AesOcb.X86.mutR p) s₅.mem s₆.mem := VG.Proof.AesOcb.X86.frame_toMut f₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.AesOcb.X86.wA p.W, by simp, Region.sub_prefix (by omega)⟩
  have E₆ : VG.Proof.AesOcb.X86.Env p s₆ := F.env.mut L (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), F.env.ebp])
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), F.env.esp]) rd₆ wr₆ F₆
  -- The comparison.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.cmp_ok L E₆) fun s₇ ⟨m₇, g₇, rd₇, wr₇⟩ => ?_)
  have f₇ : Frame [⟨w64 p.W + BitVec.ofNat 64 okO, 4⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have F₇ : Frame (VG.Proof.AesOcb.X86.mutR p) s₆.mem s₇.mem := VG.Proof.AesOcb.X86.frame_toMut f₇ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  have E₇ : VG.Proof.AesOcb.X86.Env p s₇ := E₆.mut L
    (by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), E₆.ebp])
    (by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), E₆.esp]) rd₇ wr₇ F₇
  have hok : slotv s₇.mem p.W okO = if decide (bytesAt s₆.mem (w64 p.W) p.tl =
      bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl) then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := by
    rw [slotv_eq, m₇, Mem.readW_writeW_self32]; simp only [decide_eq_true_eq]
  -- The mask.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86.mask_ok L E₇ hok) fun s₈ ⟨m₈, g₈, rd₈, wr₈⟩ => ?_)
  have f₈ : Frame [⟨w64 p.D, p.n⟩] s₇.mem s₈.mem := by rw [m₈]; exact writeBytes_frame' _ (VG.Proof.AesOcb.X86.length_mask _ _ _ _)
  have F₈ : Frame (VG.Proof.AesOcb.X86.mutR p) s₇.mem s₈.mem := VG.Proof.AesOcb.X86.frame_toMut f₈ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_d p
  have E₈ : VG.Proof.AesOcb.X86.Env p s₈ := E₇.mut L (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), E₇.ebp])
    (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), E₇.esp]) rd₈ wr₈ F₈
  -- `ok` and `restore`.
  rw [WP.block_append_iff]
  obtain ⟨s₉, run₉, ax₉, g₉, m₉, rd₉, wr₉⟩ := VG.Proof.AesOcb.X86.retEax_ok L E₈
  refine WP.of_runBlock ⟨s₉, run₉, ?_⟩
  have fr := (F₆.trans F₇).trans F₈
  have hret : s₉.mem.readW (w64 (s.gpr .esp)) 32 = s.mem.readW (w64 (s.gpr .esp)) 32 := by
    rw [m₉, show s.gpr .esp = p.SP from rfl, VG.Proof.AesOcb.X86.ret_mut L fr]
    exact F.frame.readW (r := ⟨w64 p.SP, 4⟩) (Region.contains_self _ _) (VG.Proof.AesOcb.X86.ret_front L) (by decide)
  refine WP.mono (exit_ok (s₀ := s) (by rw [g₉ _ (by decide), E₈.ebp])
    (by rw [g₉ _ (by decide), E₈.esp]; rfl) (by rw [rd₉, wr₉]; exact covers_left E₈.perm.w) L.ww
    (by rw [m₉]; exact SavedAt.mut L fr F.saved) hret) fun s₁₀ ⟨ab, m₁₀, ax₁₀, _, _⟩ => ⟨ab, ?_⟩
  -- The values.
  have tg₆ : bytesAt s₆.mem (w64 p.W) p.tl = bytesAt s.mem (w64 p.T) p.tl := by
    have := bytesAt_writeBytes_self s₅.mem (w64 p.W) (bytesAt s₅.mem (w64 p.T) p.tl)
      (by rw [length_bytesAt]; omega)
    rw [length_bytesAt] at this
    rw [m₆, this]
    exact VG.Proof.AesOcb.X86.bytes_front L.t_w L.bt L.t_d (by omega) F.frame
  have t2₆ : bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl = bytesAt s₅.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl :=
    Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using Lay.w_w (W := p.W) (a := t2O) (n := p.tl) (d := 0) (k := p.tl) (.inr (by simp only [t2O]; omega))
        (by simp only [t2O]; omega) (by omega)) (by omega)
  have d₇ : bytesAt s₇.mem (w64 p.D) p.n = bytesAt s₅.mem (w64 p.D) p.n := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by have := L.dw; omega),
      Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.d_w.sub_right (Region.sub_prefix (by omega)))
        (by have := L.dw; omega)]
  have ok₈ : slotv s₈.mem p.W okO = slotv s₇.mem p.W okO :=
    f₈.readW (r := ⟨w64 p.W + BitVec.ofNat 64 okO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.d_w' (by decide)).symm) (by decide)
  have out₈ : bytesAt s₈.mem (w64 p.D) p.n = if decide (bytesAt s₆.mem (w64 p.W) p.tl =
      bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl) then bytesAt s₇.mem (w64 p.D) p.n else zeros p.n := by
    have hlm := VG.Proof.AesOcb.X86.length_mask s₇.mem (w64 p.D) (decide (bytesAt s₆.mem (w64 p.W) p.tl =
      bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl)) p.n
    have := bytesAt_writeBytes_self s₇.mem (w64 p.D) _ (by rw [hlm]; have := L.dw; omega)
    rw [hlm] at this
    rw [m₈]; exact this
  have eax : s₁₀.gpr .eax = if decide (bytesAt s₆.mem (w64 p.W) p.tl =
      bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl) then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := by
    rw [ax₁₀, ax₉, ok₈, hok]
  rw [tg₆, t2₆, d₇] at out₈
  rw [tg₆, t2₆] at eax
  have mem : bytesAt s₁₀.mem (w64 p.D) p.n = bytesAt s₈.mem (w64 p.D) p.n := by rw [m₁₀, m₉]
  show VG.Proof.AesOcb.X86.openPost (VG.Proof.AesOcb.X86.openResult s) s₁₀ (w64 p.D) p.n
  by_cases hc : bytesAt s₅.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl = bytesAt s.mem (w64 p.T) p.tl
  · have hc' : bytesAt s.mem (w64 p.T) p.tl = bytesAt s₅.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl := hc.symm
    have r : VG.Proof.AesOcb.X86.openResult s = some (bytesAt s₅.mem (w64 p.D) p.n) := out.trans (by simp only [hc, ↓reduceIte])
    have a : s₁₀.gpr .eax = 1 := by rw [eax]; simp only [hc', decide_true, ↓reduceIte]; rfl
    have d : bytesAt s₁₀.mem (w64 p.D) p.n = bytesAt s₅.mem (w64 p.D) p.n := by
      rw [mem, out₈]; simp only [hc', decide_true, ↓reduceIte]
    exact VG.Proof.AesOcb.X86.openPost_some r a d
  · have hc' : ¬ bytesAt s.mem (w64 p.T) p.tl = bytesAt s₅.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl :=
      fun e => hc e.symm
    have r : VG.Proof.AesOcb.X86.openResult s = none := out.trans (by simp only [hc, ↓reduceIte])
    have a : s₁₀.gpr .eax = 0 := by rw [eax]; simp only [hc', decide_false, Bool.false_eq_true, ↓reduceIte]; rfl
    have d : bytesAt s₁₀.mem (w64 p.D) p.n = zeros p.n := by
      rw [mem, out₈]; simp only [hc', decide_false, Bool.false_eq_true, ↓reduceIte]
    exact VG.Proof.AesOcb.X86.openPost_none r a d

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.CTBase`. -/
section

/-!
# AES-OCB on x86: constant time, the shared pieces

Untrusted: everything here is checked by Lean. The taint analysis knows the
registers, not memory, so a value loaded from a slot is secret to it: where
a block uses such a value as an address, it is split there
(`RelCT.block_append`), and the value is pinned by what the first part
leaves. The loops whose condition comes from memory are run for their
number of iterations (`CT.loopN`). Here: pinned registers (`pin1` …),
`lNtz` (`lNtz_ct`), the calls of `vg_aes_*_blocks` (`callBlocks_ct`) and
`padTo` (`padTo_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ntz)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq copyLoop_ct)

/-- One register pinned. -/
theorem pin1 {I : State → Prop} {a : Reg} {x : BitVec 32} (h : ∀ s, I s → s.gpr a = x) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h _ h₁, h _ h₂]

/-- Four registers pinned. -/
theorem pin4 {I : State → Prop} {a b c d : Reg} {x y z w : BitVec 32}
    (h : ∀ s, I s → s.gpr a = x ∧ s.gpr b = y ∧ s.gpr c = z ∧ s.gpr d = w) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a, b, c, d], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [(h _ h₁).1, (h _ h₂).1]
  · rw [(h _ h₁).2.1, (h _ h₂).2.1]
  · rw [(h _ h₁).2.2.1, (h _ h₂).2.2.1]
  · rw [(h _ h₁).2.2.2, (h _ h₂).2.2.2]

/-- A loop of `n` iterations, its body constant time and leaving the
condition to loop back exactly while iterations are left. -/
theorem CT.loopN {body : Prog isa} {c : Cond} (Inv : Nat → State → Prop)
    (hb : ∀ n, CT (Inv n) body)
    (hw : ∀ n s, Inv n s → WP isa body s fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s'))
    (n : Nat) : CT (Inv n) (.loop body c) := by
  refine RelCT.loop (M := isa) (Q := fun _ _ => True) (fun n (s₁ s₂ : State) => Inv n s₁ ∧ Inv n s₂) (fun n => ?_) n
  have h := RelCT.wp (hb n) (F₁ := fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s')) (F₂ := fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s')) fun s₁ s₂ h => ⟨hw n s₁ h.1, hw n s₂ h.2⟩
  refine RelCT.mono h (fun _ _ h => h) fun s₁ s₂ ⟨_, ⟨hn, c₁, i₁⟩, ⟨_, c₂, i₂⟩⟩ => ⟨by rw [c₁, c₂], fun _ => trivial,
    fun ht => ?_⟩
  rw [c₁] at ht
  have h1 : n ≠ 1 := by simpa using ht
  exact ⟨n - 1, by omega, i₁ h1, i₂ h1⟩

/-! ## `lNtz` -/

/-- What `lNtz`'s loop needs: `n` iterations are left while `W + kO` holds
an even `k` with `ntz(k) = n`. -/
def NtzInv (p : VG.Proof.AesOcb.X86.Prm) (n : Nat) (t : State) : Prop :=
  VG.Proof.AesOcb.X86.Env p t ∧ ∃ k, 0 < k ∧ k % 2 = 0 ∧ k < 2 ^ 32 ∧ ntz k = n ∧ slotv t.mem p.W kO = BitVec.ofNat 32 k

theorem lNtz_ct {I : State → Prop} {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {i : Nat} (hi : 0 < i) (hi' : i < 2 ^ 32)
    (hI : ∀ s, I s → VG.Proof.AesOcb.X86.Env p s ∧ s.gpr .edi = BitVec.ofNat 32 i) : CT I lNtz := by
  unfold lNtz
  refine CT.seq (J := fun t => VG.Proof.AesOcb.X86.Env p t ∧ slotv t.mem p.W kO = BitVec.ofNat 32 i ∧
      t.zf = some (decide (i % 2 = 0)))
    (CT.taint [.ebp, .edi] (VG.Proof.AesOcb.X86.pin2 fun s h => ⟨(hI s h).1.ebp, (hI s h).2⟩) (by taint_decide)) (fun s hs => ?_) ?_
  · obtain ⟨E, hdi⟩ := hI s hs
    obtain ⟨s₂, run₂, fr₂, -, k₂, zf₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.lNtzHead_ok L E hi' hdi
    exact WP.of_runBlock ⟨s₂, run₂, E.mut L (by rw [g₂ _ (by decide), E.ebp]) (by rw [g₂ _ (by decide), E.esp])
      rd₂ wr₂ (VG.Proof.AesOcb.X86.frame_toMut fr₂ (VG.Proof.AesOcb.X86.inMut_lNtzR p)), k₂, zf₂⟩
  refine CT.ite (decide (i % 2 = 0)) (fun _ h => VG.Proof.AesOcb.X86.eval_e h.2.2) (fun hb => ?_) (fun _ => CT.nil)
  have he : i % 2 = 0 := of_decide_eq_true hb
  refine (CT.loopN (VG.Proof.AesOcb.X86.NtzInv p) (fun _ => by exact CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin1 fun _ h => h.1.ebp) (by taint_decide))
    (fun n t ⟨Et, k, hk0, hke, hk, hn, kt⟩ => ?_) (ntz i)).mono fun t ⟨Et, kt, _⟩ => ⟨Et, i, hi, he, hi', rfl, kt⟩
  obtain ⟨t₂, run, fr, -, kt', zf', g', rd', wr'⟩ := VG.Proof.AesOcb.X86.lNtzStep_ok L Et hk kt
  have hn' : n = ntz (k / 2) + 1 := by rw [← hn, Proof.Ocb.ntz_even hk0 hke]
  have hodd : k / 2 % 2 = 0 ↔ n ≠ 1 := by
    constructor
    · intro h; rw [hn', Proof.Ocb.ntz_even (by omega) h]; omega
    · intro h; by_contra h'; exact h (by rw [hn', Proof.Ocb.ntz_odd (by omega)])
  refine WP.of_runBlock ⟨t₂, run, by omega, (VG.Proof.AesOcb.X86.eval_e zf').trans (by simp only [decide_eq_decide.mpr hodd]),
    fun h1 => ⟨Et.mut L (by rw [g' _ (by decide) (by decide) (by decide), Et.ebp])
      (by rw [g' _ (by decide) (by decide) (by decide), Et.esp]) rd' wr' (VG.Proof.AesOcb.X86.frame_toMut fr (VG.Proof.AesOcb.X86.inMut_lNtzR p)),
      k / 2, by omega, hodd.mpr h1, by omega, by omega, kt'⟩⟩

/-! ## Calls -/

/-- `callBlocks`: `args` (constant time from `ebp`, `hct`), which leave the
blocks' address and number public, then the call. -/
theorem callBlocks_ct {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub fn.code)
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {I : State → Prop} {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p)
    {args : List Instr} {D : BitVec 32} {n : Nat}
    (hI : ∀ s, I s → VG.Proof.AesOcb.X86.Env p s ∧ VG.Proof.AesOcb.X86.DReg p s D n ∧ ∃ s₁, runBlock isa args s = some s₁ ∧ s₁.gpr .edx = D ∧
      s₁.gpr .ebx = BitVec.ofNat 32 n ∧ (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr)
    (hct : ∀ {J : State → Prop}, (∀ s, J s → s.gpr .ebp = p.W) →
      CT J (.block (args ++ ([.mov .eax (slot ctxO), .mov .ecx (slot rndO), .alu .add .ebp (imm scrO)] : List Instr)))) :
    CT I (callBlocks fn args) := by
  unfold callBlocks
  refine CT.seq (J := fun s₁ => VG.Proof.AesOcb.X86.BCall s₁ p.K D (p.W + BitVec.ofNat 32 scrO) p.R n ∧ s₁.gpr .esp = p.SP)
    (hct fun s h => (hI s h).1.ebp) (fun s hs => ?_)
    (CT.seq (J := fun s => s.gpr .ebp = p.W + BitVec.ofNat 32 scrO) (VG.Proof.AesOcb.X86.blk_ct ok ct fun s h => h)
      (fun s h => WP.mono (VG.Proof.AesOcb.X86.blk_call ok nosp stack h.1) fun s' P => by rw [P.saved _ (by decide), h.1.ebp])
      (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h) (by taint_decide)))
  obtain ⟨E, hD, s₁, run₁, dx₁, bx₁, g₁, m₁, rd₁, wr₁⟩ := hI s hs
  have E₁ : VG.Proof.AesOcb.X86.Env p s₁ := E.keep (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide)])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide)]) rd₁ wr₁ m₁
  obtain ⟨s₂, run₂, bc, hsp, -⟩ := VG.Proof.AesOcb.X86.callArgs_ok L E₁ dx₁ bx₁ (hD.of_eq wr₁)
  exact WP.of_runBlock ⟨s₂, Proof.AesGcm.X86.runBlock_app_of run₁ run₂, bc, hsp⟩

/-- `callBlocks` of one block of `W`. -/
theorem oneCall_ct {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub fn.code)
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {I : State → Prop} {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {d : Nat}
    (hd : d = tmpO ∨ d = bufO) (hI : ∀ s, I s → VG.Proof.AesOcb.X86.Env p s) : CT I (callBlocks fn (oneBlock d)) := by
  refine VG.Proof.AesOcb.X86.callBlocks_ct ok ct nosp stack L (fun s h => ⟨hI s h, DReg.w L (hI s h) (n := 1)
    (by rcases hd with rfl | rfl <;> decide) (by rcases hd with rfl | rfl <;> decide), VG.Proof.AesOcb.X86.oneBlock_ok (hI s h) d⟩) fun hJ => ?_
  rcases hd with rfl | rfl
  · exact CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp hJ) (by taint_decide)
  · exact CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp hJ) (by taint_decide)

/-! ## `padTo` -/

theorem padTo_ct {I : State → Prop} {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {S : BitVec 32} {n d : Nat}
    (hd : d = bufO ∨ d = t2O)
    (hI : ∀ s, I s → VG.Proof.AesOcb.X86.Env p s ∧ s.gpr .esi = S ∧ slotv s.mem p.W restO = BitVec.ofNat 32 n) :
    CT I (padTo d restO) := by
  have hJ : ∀ s, I s → WP isa (.block (zero4 d ++ ([.mov .edi (.reg .esi), .mov .edx (.reg .ebp),
      .alu .add .edx (imm d), .mov .ecx (slot restO)] : List Instr))) s
      (fun t => t.gpr .edi = S ∧ t.gpr .edx = p.W + BitVec.ofNat 32 d ∧ t.gpr .ecx = BitVec.ofNat 32 n) :=
    fun s hs => by
      obtain ⟨E, hsi, hc⟩ := hI s hs
      obtain ⟨s₁, run₁, -, di₁, dx₁, cx₁, -⟩ := VG.Proof.AesOcb.X86.padToHead_ok L E (S := S) (n := n) (d := d) (cO := restO)
        (by rcases hd with rfl | rfl <;> decide) (by decide) (by rcases hd with rfl | rfl <;> decide) hsi hc
      exact WP.of_runBlock ⟨s₁, run₁, di₁, dx₁, cx₁⟩
  unfold padTo
  rcases hd with rfl | rfl
  · exact CT.seq (CT.taint [.ebp, .esi] (VG.Proof.AesOcb.X86.pin2 fun s h => ⟨(hI s h).1.ebp, (hI s h).2.1⟩) (by taint_decide)) hJ
      (CT.taint [.edi, .edx, .ecx] (VG.Proof.AesOcb.X86.pin3 fun _ h => h) (by taint_decide))
  · exact CT.seq (CT.taint [.ebp, .esi] (VG.Proof.AesOcb.X86.pin2 fun s h => ⟨(hI s h).1.ebp, (hI s h).2.1⟩) (by taint_decide)) hJ
      (CT.taint [.edi, .edx, .ecx] (VG.Proof.AesOcb.X86.pin3 fun _ h => h) (by taint_decide))

/-! ## Loads of public slots -/

/-- A block followed by code, as its two parts in sequence: it runs the same
and leaks the same trace. -/
theorem CT.block_split {I : State → Prop} {l₁ l₂ : List Instr} {c : Prog isa}
    (h : CT I (.seq (.block l₁) (.seq (.block l₂) c))) : CT I (.seq (.block (l₁ ++ l₂)) c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq b₁ k₁ =>
    cases e₂ with
    | seq b₂ k₂ =>
      rw [Exec.block_iff, execBlock_append] at b₁ b₂
      obtain ⟨⟨a₁, u₁⟩, ha₁, hb₁⟩ := Option.bind_eq_some_iff.mp b₁
      obtain ⟨⟨c₁, w₁⟩, hc₁, he₁⟩ := Option.map_eq_some_iff.mp hb₁
      obtain ⟨⟨a₂, u₂⟩, ha₂, hb₂⟩ := Option.bind_eq_some_iff.mp b₂
      obtain ⟨⟨c₂, w₂⟩, hc₂, he₂⟩ := Option.map_eq_some_iff.mp hb₂
      simp only [Prod.mk.injEq] at he₁ he₂
      obtain ⟨rfl, rfl⟩ := he₁
      obtain ⟨rfl, rfl⟩ := he₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.block ha₁) (.seq (.block hc₁) k₁))
        (.seq (.block ha₂) (.seq (.block hc₂) k₂))
      simp only [List.append_assoc]
      exact ⟨ht, hq⟩

/-- What a load of `v` into `r` leaves, from a state satisfying `I`. -/
def Ld (I : State → Prop) (r : Reg) (v : BitVec 32) (s : State) : Prop :=
  ∃ s₀, I s₀ ∧ s.gpr r = v ∧ (∀ q, q ≠ r → s.gpr q = s₀.gpr q) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

/-- A block that starts with a load of a public slot, then code: the rest
is constant time once the value is in its register. -/
theorem load_ct {I : State → Prop} {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {r : Reg} {o : Nat} (ho : o + 4 ≤ 2560) {v : BitVec 32}
    {rest : List Instr} {c : Prog isa} (hI : ∀ s, I s → VG.Proof.AesOcb.X86.Env p s ∧ slotv s.mem p.W o = v)
    (h₁ : CT (fun s => s.gpr .ebp = p.W) (.block [.mov r (slot o)]))
    (h : CT (VG.Proof.AesOcb.X86.Ld I r v) (.seq (.block rest) c)) : CT I (.seq (.block (.mov r (slot o) :: rest)) c) := by
  rw [← List.singleton_append]
  refine CT.block_split (CT.seq (J := VG.Proof.AesOcb.X86.Ld I r v) (h₁.mono fun s hs => (hI s hs).1.ebp) (fun s hs => ?_) h)
  obtain ⟨E, hv⟩ := hI s hs
  simp only [slotv_eq] at hv
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR ho, hv], s, hs, by gregs [hv],
    fun q hq => by gregs [hq], by gmems [], by gmems [], by gmems []⟩

/-- A block that starts with a load of a public slot. -/
theorem load_blk_ct {I : State → Prop} {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {r : Reg} {o : Nat} (ho : o + 4 ≤ 2560)
    {v : BitVec 32} {rest : List Instr} (hI : ∀ s, I s → VG.Proof.AesOcb.X86.Env p s ∧ slotv s.mem p.W o = v)
    (h₁ : CT (fun s => s.gpr .ebp = p.W) (.block [.mov r (slot o)]))
    (h : CT (VG.Proof.AesOcb.X86.Ld I r v) (.block rest)) : CT I (.block (.mov r (slot o) :: rest)) := by
  rw [← List.singleton_append]
  refine RelCT.block_append (CT.seq (J := VG.Proof.AesOcb.X86.Ld I r v) (h₁.mono fun s hs => (hI s hs).1.ebp) (fun s hs => ?_) h)
  obtain ⟨E, hv⟩ := hI s hs
  simp only [slotv_eq] at hv
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR ho, hv], s, hs, by gregs [hv],
    fun q hq => by gregs [hq], by gmems [], by gmems [], by gmems []⟩

/-- A register other than the one loaded keeps what `I` says of it. -/
theorem Ld.reg {I : State → Prop} {r q : Reg} {v x : BitVec 32} (hq : q ≠ r) (h : ∀ s, I s → s.gpr q = x) :
    ∀ s, VG.Proof.AesOcb.X86.Ld I r v s → s.gpr q = x := fun _ ⟨s₀, h₀, _, g, _⟩ => by rw [g q hq, h s₀ h₀]

/-- The environment, across a load into a register other than `ebp` and `esp`. -/
theorem Ld.env {I : State → Prop} {p : VG.Proof.AesOcb.X86.Prm} {r : Reg} {v : BitVec 32} (h1 : r ≠ .ebp) (h2 : r ≠ .esp)
    (h : ∀ s, I s → VG.Proof.AesOcb.X86.Env p s) : ∀ s, VG.Proof.AesOcb.X86.Ld I r v s → VG.Proof.AesOcb.X86.Env p s := fun _ ⟨s₀, h₀, _, g, m, rd, wr⟩ =>
  (h s₀ h₀).keep (g _ (Ne.symm h1)) (g _ (Ne.symm h2)) rd wr m

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.FrontCT`. -/
section

/-!
# AES-OCB on x86: the entry, the setup and `Offset_0` in constant time

Untrusted: everything here is checked by Lean. The entry addresses only the
stack and `W` (`entry_ct`); `setup` doubles `L_*` from the key context,
whose address it loads from its slot (`setup_ct`); `nonceBlock` copies the
nonce to an address computed from its length, loaded from its slot
(`nonceBlock_ct`); then a call and `Offset_0`, which addresses only `W`
(`nonce_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq copyLoop_ct arg0_ok argIn_of LoopPre)

/-- The entry. -/
theorem entry_ct (p : VG.Proof.AesOcb.X86.Prm) : CT (fun s => VG.Proof.AesOcb.X86.onePre s ∧ VG.Proof.AesOcb.X86.prmOf s = p) ocbEntry := by
  rw [VG.Proof.AesOcb.X86.ocbEntry_eq]
  refine CT.seq (J := fun s => s.gpr .eax = p.W ∧ s.gpr .esp = p.SP)
    (CT.taint [.esp] (VG.Proof.AesOcb.X86.pin1 (x := p.SP) fun s h => by rw [← h.2]; rfl) (by taint_decide)) (fun s hs => ?_)
    (CT.taint [.eax, .esp] (VG.Proof.AesOcb.X86.pin2 fun _ h => h) (by taint_decide))
  have Ao := VG.Proof.AesOcb.X86.argsOk_of hs.1
  refine WP.mono (arg0_ok (argIn_of Ao.rA Ao.fa (i := 10) (by decide))) fun s' ⟨ax, sp⟩ => ⟨?_, ?_⟩
  · rw [ax, ← hs.2]; rfl
  · rw [sp, ← hs.2]; rfl

/-- `L_$`, `L_0` and the checksum. -/
theorem setup_ct {I : State → Prop} {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) (hI : ∀ s, I s → VG.Proof.AesOcb.X86.Env p s) : CT I (.block setup) := by
  show CT I (.block (([.mov .ebx (slot ctxO)] : List Instr) ++ (dbl .ebx 240 ldO ++ dbl .ebp ldO l0O ++ zero4 ckO)))
  refine RelCT.block_append
    (CT.seq (J := fun s => s.gpr .ebp = p.W ∧ s.gpr .ebx = p.K)
      (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun s h => (hI s h).ebp) (by taint_decide)) (fun s hs => ?_)
      (CT.taint [.ebp, .ebx] (VG.Proof.AesOcb.X86.pin2 fun _ h => h) (by taint_decide)))
  have E := hI s hs
  have hc := E.slots.ctx
  simp only [slotv_eq] at hc
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hc], by gregs [E.ebp], by gregs [hc]⟩

/-- The nonce block. -/
theorem nonceBlock_ct {I : State → Prop} {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) (hI : ∀ s, I s → VG.Proof.AesOcb.X86.Env p s) : CT I nonceBlock := by
  unfold nonceBlock
  refine CT.seq (J := fun s => VG.Proof.AesOcb.X86.Env p s ∧ LoopPre s p.N (p.W + BitVec.ofNat 32 (128 - p.nl)) p.nl)
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun s h => (hI s h).ebp) (by taint_decide)) (fun s hs => ?_) ?_
  · obtain ⟨s₂, run₂, E₂, lp, -⟩ := VG.Proof.AesOcb.X86.nonceHead_ok L (hI s hs)
    exact WP.of_runBlock ⟨s₂, run₂, E₂, lp⟩
  refine CT.seq (J := VG.Proof.AesOcb.X86.Env p) (copyLoop_ct (VG.Proof.AesOcb.X86.pin3 fun _ h => ⟨h.2.edi, h.2.edx, h.2.ecx⟩))
    (fun s h => WP.mono (VG.Proof.AesOcb.X86.copyW_ok L h.1 (d := 128 - p.nl) (n := p.nl) (by have := L.nl15; omega) h.2) fun _ h' => h'.1) ?_
  rw [← List.singleton_append (x := Instr.mov .ecx (slot nlO))]
  refine RelCT.block_append
    (CT.seq (J := fun s => s.gpr .ebp = p.W ∧ s.gpr .ecx = BitVec.ofNat 32 p.nl)
      (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun s h => h.ebp) (by taint_decide)) (fun s (E : VG.Proof.AesOcb.X86.Env p s) => ?_)
      (CT.taint [.ebp, .ecx] (VG.Proof.AesOcb.X86.pin2 fun _ h => h) (by taint_decide)))
  have hnl := E.slots.nlen
  simp only [slotv_eq] at hnl
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hnl], by gregs [E.ebp], by gregs [hnl]⟩

/-- `Offset_0`. -/
theorem nonce_ct (v : BlocksImpl) {I : State → Prop} {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) (hI : ∀ s, I s → VG.Proof.AesOcb.X86.Env p s) :
    CT I (nonce (VG.Proof.AesOcb.X86.callees v)) := by
  unfold nonce
  refine CT.seq (J := VG.Proof.AesOcb.X86.Env p) (VG.Proof.AesOcb.X86.nonceBlock_ct L hI) (fun s hs => ?_) ?_
  · have E := hI s hs
    refine WP.mono (VG.Proof.AesOcb.X86.nonceBlock_ok L E) fun s₁ P₁ => ?_
    have F₁ : Frame (VG.Proof.AesOcb.X86.wR p) s.mem s₁.mem := VG.Proof.AesOcb.X86.frame_wR P₁.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Proof.AesOcb.X86.inW_wR p (.inl (by decide))
      · exact VG.Proof.AesOcb.X86.inW_wR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    exact E.mut L (by rw [P₁.gpr _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [P₁.gpr _ (by decide) (by decide) (by decide) (by decide), E.esp]) P₁.rd P₁.wr (VG.Proof.AesOcb.X86.wR_mut F₁)
  refine CT.seq (J := VG.Proof.AesOcb.X86.Env p) (VG.Proof.AesOcb.X86.oneCall_ct v.encOk v.encCt v.encNosp v.encStack L (.inl rfl) fun _ h => h)
    (fun s E => WP.mono (VG.Proof.AesOcb.X86.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E
      (VG.Proof.AesOcb.X86.oneBlock_ok E tmpO) (DReg.w L E (d := tmpO) (n := 1) (by decide) (.inl (by decide)))) fun _ P => P.env)
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun s h => h.ebp) (by taint_decide))

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.HashCT`. -/
section

/-!
# AES-OCB on x86: `HASH` in constant time

Untrusted: everything here is checked by Lean. `HASH` runs a loop of
chunks, each a loop filling the buffer (`hashFill_ct`, `fillLoop_ct`), a
call and a loop adding the buffer to the sum (`hashSum_ct`): `chunk_ct`;
the number of chunks and of their blocks is public (`hashLoop_ct`). The
counts and the buffer's address are loaded from their slots. Then the rest
(`hashRest_ct`) if there is one (`hashTail_ct`): `hash_ct`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4)
open VG.Proof.AesGcm.X86 (CT w64 w64_add slotv slotv_eq toNat_add32 covers_off)

/-- The fill loop's state after `i` of the `c` blocks of a chunk from block
`j`, for some cipher, `L_*`, associated data and start. -/
def FillI (p : VG.Proof.AesOcb.X86.Prm) (j c i : Nat) (t : State) : Prop :=
  ∃ ciph l a s₀, VG.Proof.AesOcb.X86.HCtx p ciph l a s₀ ∧ VG.Proof.AesOcb.X86.FillInv p ciph l a s₀ j c t i

/-- `HASH`'s state after `j` whole blocks. -/
def HI (p : VG.Proof.AesOcb.X86.Prm) (j : Nat) (t : State) : Prop :=
  ∃ ciph l a s₀, VG.Proof.AesOcb.X86.HCtx p ciph l a s₀ ∧ VG.Proof.AesOcb.X86.HInv p ciph l a s₀ t j

/-- One block into the buffer. -/
theorem hashFill_ct {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {j c i : Nat} (hi : i < c) (hjc : j + c ≤ p.al / 16) :
    CT (VG.Proof.AesOcb.X86.FillI p j c i) hashFill := by
  have hal := L.al32
  unfold hashFill
  refine CT.seq (J := fun t => VG.Proof.AesOcb.X86.Env p t ∧ t.gpr .esi = p.A + BitVec.ofNat 32 (16 * (j + i)) ∧
      slotv t.mem p.W fpO = p.W + BitVec.ofNat 32 (bufO + 16 * i))
    (VG.Proof.AesOcb.X86.lNtz_ct L (i := j + i + 1) (by omega) (by omega) fun t ⟨_, _, _, _, _, F⟩ => ⟨F.env, F.edi⟩)
    (fun t ⟨_, _, _, _, _, F⟩ => WP.mono (VG.Proof.AesOcb.X86.lNtz_ok L F.env (by omega) (by omega) F.edi F.l0) fun t₁ P₁ =>
      ⟨P₁.env L F.env, by rw [P₁.gpr _ (by decide) (by decide) (by decide), F.esi], by
        rw [← F.fp]
        exact P₁.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)) (by decide)⟩) ?_
  simp only [List.append_assoc, List.singleton_append]
  refine RelCT.block_append (CT.seq (J := fun t => VG.Proof.AesOcb.X86.Env p t ∧ t.gpr .esi = p.A + BitVec.ofNat 32 (16 * (j + i)) ∧
      slotv t.mem p.W fpO = p.W + BitVec.ofNat 32 (bufO + 16 * i))
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun t h => h.1.ebp) (by taint_decide)) (fun t h => ?_) ?_)
  · obtain ⟨E, si, fp⟩ := h
    obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.xor16W_ok L E (s := lO) (d := ohO) (by decide) (by decide)
      (.inl (by decide))
    have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem := by
      rw [m₂]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _
    refine WP.of_runBlock ⟨t₂, run₂, E.mut L (by rw [g₂ _ (by decide), E.ebp]) (by rw [g₂ _ (by decide), E.esp])
      rd₂ wr₂ (VG.Proof.AesOcb.X86.frame_toMut f₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))),
      by rw [g₂ _ (by decide), si], ?_⟩
    rw [← fp]
    exact f₂.readW (r := ⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (by decide) (by decide) (by decide)) (by decide)
  refine VG.Proof.AesOcb.X86.load_blk_ct L (r := .edx) (o := fpO) (by decide) (fun t h => ⟨h.1, h.2.2⟩)
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h) (by taint_decide)) (CT.taint [.ebp, .esi, .edx]
      (VG.Proof.AesOcb.X86.pin3 fun t h => ⟨Ld.reg (by decide) (fun s h => h.1.ebp) t h, Ld.reg (by decide) (fun s h => h.2.1) t h,
        by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide))

/-- The fill loop: `c` blocks into the buffer. -/
theorem fillLoop_ct {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ p.al / 16) :
    CT (VG.Proof.AesOcb.X86.FillI p j c 0) (.loop hashFill .ne) := by
  refine (CT.loopN (fun n t => 0 < n ∧ n ≤ c ∧ VG.Proof.AesOcb.X86.FillI p j c (c - n) t) (fun n => ?_)
    (fun n t ⟨hn0, hn, _, _, _, _, C, F⟩ => WP.mono (VG.Proof.AesOcb.X86.fill_step C hc hjc (by omega) F) fun t' ⟨F', zf'⟩ =>
      ⟨hn0, by rw [VG.Proof.AesOcb.X86.eval_ne zf']; congr 1; by_cases h : n = 1 <;> simp [h] <;> omega,
        fun h1 => ⟨by omega, by omega, _, _, _, _, C, by rw [show c - (n - 1) = c - n + 1 by omega]; exact F'⟩⟩) c).mono
    fun t h => ⟨hc0, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  by_cases hn : 0 < n
  · exact (VG.Proof.AesOcb.X86.hashFill_ct L (i := c - n) (by omega) hjc).mono fun _ h => h.2.2
  · exact RelCT.of_false fun _ _ h => hn h.1.1

/-- The sum of the buffer. -/
theorem hashSum_ct {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {c : Nat} :
    CT (fun t => VG.Proof.AesOcb.X86.Env p t ∧ slotv t.mem p.W cntO = BitVec.ofNat 32 c) hashSum := by
  unfold hashSum
  exact VG.Proof.AesOcb.X86.load_ct L (r := .ebx) (o := cntO) (by decide) (fun t h => h)
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h) (by taint_decide))
    (CT.taint [.ebp, .ebx] (VG.Proof.AesOcb.X86.pin2 fun t h => ⟨Ld.reg (by decide) (fun s h => h.1.ebp) t h,
      by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide))

/-- A chunk, from block `j`. -/
theorem chunk_ct (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {j : Nat} (hj : j < p.al / 16) :
    CT (VG.Proof.AesOcb.X86.HI p j) (hashChunk (VG.Proof.AesOcb.X86.callees v)) := by
  have hal := L.al32
  unfold hashChunk
  refine RelCT.assoc (CT.seq (J := fun t => VG.Proof.AesOcb.X86.HI p j t ∧ t.gpr .ebx = BitVec.ofNat 32 (min 8 (p.al / 16 - j)))
    (VG.Proof.AesOcb.X86.load_ct L (r := .ebx) (o := hlO) (v := BitVec.ofNat 32 (p.al / 16 - j)) (by decide)
      (fun t ⟨_, _, _, _, _, H⟩ => ⟨H.env, H.hl⟩) (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h) (by taint_decide))
      (CT.taint [.ebx] (VG.Proof.AesOcb.X86.pin1 fun t h => by obtain ⟨_, _, hv, _⟩ := h; exact hv) (by taint_decide)))
    (fun t ⟨_, _, _, _, C, H⟩ => WP.mono (VG.Proof.AesOcb.X86.chunkHead_ok C H) fun t' ⟨H', bx⟩ => ⟨⟨_, _, _, _, C, H'⟩, bx⟩) ?_)
  generalize hc : min 8 (p.al / 16 - j) = c
  have hc0 : 0 < c := by omega
  have hc8 : c ≤ 8 := by omega
  have hjc : j + c ≤ p.al / 16 := by omega
  -- The chunk's count and the buffer's start.
  refine CT.seq (J := VG.Proof.AesOcb.X86.FillI p j c 0)
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun t h => by obtain ⟨⟨_, _, _, _, _, H⟩, _⟩ := h; exact H.env.ebp) (by taint_decide))
    (fun t ⟨⟨_, _, _, _, C, H⟩, bx⟩ => by
      obtain ⟨t₁, run₁, F⟩ := VG.Proof.AesOcb.X86.chunkStart_ok C H bx
      exact WP.of_runBlock ⟨t₁, run₁, _, _, _, _, C, F⟩) ?_
  -- The fill loop.
  refine CT.seq (J := VG.Proof.AesOcb.X86.FillI p j c c) (VG.Proof.AesOcb.X86.fillLoop_ct L hc0 hc8 hjc)
    (fun t ⟨_, _, _, _, C, F⟩ => WP.mono (VG.Proof.AesOcb.X86.fill_ok C hc0 hc8 hjc F) fun t' F' => ⟨_, _, _, _, C, F'⟩) ?_
  -- The call.
  have hargs : ∀ t, VG.Proof.AesOcb.X86.FillI p j c c t → ∃ s₁, runBlock isa [.mov .edx (.reg .ebp), .alu .add .edx (imm bufO),
      .mov .ebx (slot cntO)] t = some s₁ ∧ s₁.gpr .edx = p.W + BitVec.ofNat 32 bufO ∧
      s₁.gpr .ebx = BitVec.ofNat 32 c ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = t.gpr r) ∧ s₁.mem = t.mem ∧
      s₁.rd = t.rd ∧ s₁.wr = t.wr := fun t ⟨_, _, _, _, _, F⟩ => by
    have hcnt := F.cnt
    simp only [slotv_eq] at hcnt
    exact ⟨_, by grun [F.env.ebp, L.aW, F.env.perm.wR, hcnt], by gregs [F.env.ebp], by gregs [hcnt],
      fun r _ h₂ _ h₄ => by gregs [h₂, h₄], by gmems [], by gmems [], by gmems []⟩
  have hD : ∀ t, VG.Proof.AesOcb.X86.FillI p j c c t → VG.Proof.AesOcb.X86.DReg p t (p.W + BitVec.ofNat 32 bufO) c := fun t ⟨_, _, _, _, _, F⟩ =>
    DReg.w L F.env (d := bufO) (n := c) (by simp only [bufO, scrO]; omega) (.inr (.inr (.inr (by decide))))
  refine CT.seq (J := fun t => VG.Proof.AesOcb.X86.Env p t ∧ slotv t.mem p.W cntO = BitVec.ofNat 32 c)
    (VG.Proof.AesOcb.X86.callBlocks_ct v.encOk v.encCt v.encNosp v.encStack L
      (fun t h => ⟨by obtain ⟨_, _, _, _, _, F⟩ := h; exact F.env, hD t h, hargs t h⟩)
      fun hJ => by exact CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp hJ) (by taint_decide))
    (fun t h => ?_) ?_
  · obtain ⟨_, _, _, _, _, F⟩ := h
    refine WP.mono (VG.Proof.AesOcb.X86.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L F.env
      (hargs t ⟨_, _, _, _, ‹_›, F⟩) (hD t ⟨_, _, _, _, ‹_›, F⟩)) fun t' P => ⟨P.env, ?_⟩
    rw [← F.cnt]
    have aB : w64 (p.W + BitVec.ofNat 32 bufO) = w64 p.W + BitVec.ofNat 64 bufO := L.aW (by decide)
    exact P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 cntO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [aB]; exact Lay.w_w (.inl (by decide)) (by decide) (by simp only [bufO]; omega)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  -- The sum, and the blocks left.
  refine CT.seq (J := VG.Proof.AesOcb.X86.Env p) (VG.Proof.AesOcb.X86.hashSum_ct L) (fun t ⟨E, hcnt⟩ => WP.mono (VG.Proof.AesOcb.X86.hashSum_ok L E hc0 hc8 hcnt
      (g := fun k => blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * k))) fun _ _ => rfl)
      fun t' ⟨fr, _, g, rd, wr⟩ => E.mut L (by rw [g _ (by decide) (by decide) (by decide), E.ebp])
        (by rw [g _ (by decide) (by decide) (by decide), E.esp]) rd wr
        (VG.Proof.AesOcb.X86.frame_toMut fr fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide))))
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.ebp) (by taint_decide))

/-- The chunks: from block `8 (k − n)`, `n` of the `k = ⌈m / 8⌉` left. -/
theorem hashLoop_ct (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) (hm : 0 < p.al / 16) :
    CT (VG.Proof.AesOcb.X86.HI p 0) (.loop (hashChunk (VG.Proof.AesOcb.X86.callees v)) .ne) := by
  have hal := L.al32
  have hk : ∀ n, 0 < n → n ≤ (p.al / 16 + 7) / 8 → 8 * ((p.al / 16 + 7) / 8 - n) < p.al / 16 := fun n h₁ h₂ => by
    omega
  refine (CT.loopN (fun n t => 0 < n ∧ n ≤ (p.al / 16 + 7) / 8 ∧ VG.Proof.AesOcb.X86.HI p (8 * ((p.al / 16 + 7) / 8 - n)) t)
    (fun n => ?_) (fun n t ⟨hn0, hn, _, _, _, _, C, H⟩ => ?_) ((p.al / 16 + 7) / 8)).mono
    fun t h => ⟨by omega, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  · by_cases h : 0 < n ∧ n ≤ (p.al / 16 + 7) / 8
    · exact (VG.Proof.AesOcb.X86.chunk_ct v L (hk n h.1 h.2)).mono fun _ h => h.2.2
    · exact RelCT.of_false fun _ _ h' => h ⟨h'.1.1, h'.1.2.1⟩
  refine WP.mono (VG.Proof.AesOcb.X86.hashChunk_ok v C H (hk n hn0 hn)) fun t' ⟨H', zf'⟩ => ⟨hn0, ?_, fun h1 => ⟨by omega, by omega,
    _, _, _, _, C, ?_⟩⟩
  · rw [VG.Proof.AesOcb.X86.eval_ne zf']; congr 1; by_cases h : n = 1 <;> simp [h] <;> omega
  · rw [show 8 * ((p.al / 16 + 7) / 8 - (n - 1)) = 8 * ((p.al / 16 + 7) / 8 - n) +
      min 8 (p.al / 16 - 8 * ((p.al / 16 + 7) / 8 - n)) by omega]
    exact H'

/-- The rest of the associated data. -/
theorem hashRest_ct (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) (hr : 0 < p.al % 16) :
    CT (VG.Proof.AesOcb.X86.HI p (p.al / 16)) (hashRest (VG.Proof.AesOcb.X86.callees v)) := by
  have hal := L.aw
  have hS : ∀ t, VG.Proof.AesOcb.X86.Env p t → VG.Proof.AesOcb.X86.SBuf p t (p.A + BitVec.ofNat 32 (16 * (p.al / 16))) (p.al % 16) := fun t E => by
    have a16 : w64 (p.A + BitVec.ofNat 32 (16 * (p.al / 16))) = w64 p.A + BitVec.ofNat 64 (16 * (p.al / 16)) :=
      w64_add (by omega)
    have sub : Region.Sub ⟨w64 (p.A + BitVec.ofNat 32 (16 * (p.al / 16))), p.al % 16⟩ ⟨w64 p.A, p.al⟩ := by
      rw [a16]; exact Offset.sub_base _ (by omega)
    refine ⟨?_, L.a_w.sub_left sub, ?_⟩
    · rw [toNat_add32 (by omega)]; omega
    · rw [a16]; exact covers_off E.perm.aad (by omega) (by omega)
  -- After the head: the environment, the rest's address and length.
  let J : State → Prop := fun t => VG.Proof.AesOcb.X86.Env p t ∧ t.gpr .esi = p.A + BitVec.ofNat 32 (16 * (p.al / 16)) ∧
    slotv t.mem p.W restO = BitVec.ofNat 32 (p.al % 16)
  unfold hashRest
  refine CT.seq (J := J) ?_ (fun t ⟨_, _, _, _, _, H⟩ => ?_) ?_
  · exact VG.Proof.AesOcb.X86.load_blk_ct L (r := .ebx) (o := ctxO) (by decide) (fun t ⟨_, _, _, _, _, H⟩ => ⟨H.env, H.env.slots.ctx⟩)
      (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h) (by taint_decide))
      (CT.taint [.ebp, .ebx] (VG.Proof.AesOcb.X86.pin2 fun t h => ⟨Ld.reg (by decide)
        (fun s (h : VG.Proof.AesOcb.X86.HI p (p.al / 16) s) => by obtain ⟨_, _, _, _, _, H⟩ := h; exact H.env.ebp) t h,
        by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide))
  · obtain ⟨t₂, run₂, E₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.hashRestHead_ok L H.env
    refine WP.of_runBlock ⟨t₂, run₂, E₂, by rw [g₂ _ (by decide) (by decide), H.esi], ?_⟩
    rw [← H.rest, slotv_eq, slotv_eq, m₂]
    exact (VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _).readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)
  -- `pad(A_*)`, its offset, the call and the sum.
  refine CT.seq (J := VG.Proof.AesOcb.X86.Env p) (VG.Proof.AesOcb.X86.padTo_ct L (.inl rfl) fun t h => h)
    (fun t ⟨E, si, rest⟩ => WP.mono (VG.Proof.AesOcb.X86.padTo_ok L E (d := bufO) (cO := restO) hr (by omega) (by decide) (by decide)
      (.inl (by decide)) si rest (hS t E)) fun t' ⟨fr, _, g, rd, wr⟩ =>
        E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
          (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr
          (VG.Proof.AesOcb.X86.frame_toMut fr fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))))
    ?_
  refine CT.seq (J := VG.Proof.AesOcb.X86.Env p) (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_) ?_
  · obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.xor16W_ok L E (s := ohO) (d := bufO) (by decide) (by decide)
      (.inl (by decide))
    exact WP.of_runBlock ⟨t₂, run₂, E.mut L (by rw [g₂ _ (by decide), E.ebp]) (by rw [g₂ _ (by decide), E.esp])
      rd₂ wr₂ (VG.Proof.AesOcb.X86.frame_toMut (by rw [m₂]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩))))⟩
  refine CT.seq (J := VG.Proof.AesOcb.X86.Env p) (VG.Proof.AesOcb.X86.oneCall_ct v.encOk v.encCt v.encNosp v.encStack L (.inr rfl) fun _ h => h)
    (fun t E => WP.mono (VG.Proof.AesOcb.X86.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E
      (VG.Proof.AesOcb.X86.oneBlock_ok E bufO) (DReg.w L E (d := bufO) (n := 1) (by decide) (.inr (.inr (.inr (by decide))))))
      fun _ P => P.env)
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.ebp) (by taint_decide))

/-- The rest, if there is one. -/
theorem hashTail_ct (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) :
    CT (VG.Proof.AesOcb.X86.HI p (p.al / 16)) (.seq (.block [.mov .eax (slot restO), .alu .test .eax (.reg .eax)])
      (.ite .e (.block []) (hashRest (VG.Proof.AesOcb.X86.callees v)))) := by
  refine VG.Proof.AesOcb.X86.load_ct L (r := .eax) (o := restO) (v := BitVec.ofNat 32 (p.al % 16)) (by decide)
    (fun t ⟨_, _, _, _, _, H⟩ => ⟨H.env, H.rest⟩) (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h) (by taint_decide)) ?_
  refine CT.seq (J := fun t => VG.Proof.AesOcb.X86.HI p (p.al / 16) t ∧ t.zf = some (decide (p.al % 16 = 0)))
    (CT.taint [] (fun _ _ _ _ _ h => by simp at h) (by taint_decide)) (fun t ⟨s₀, h₀, ax, g, m, rd, wr⟩ => ?_)
    (CT.ite (decide (p.al % 16 = 0)) (fun _ h => VG.Proof.AesOcb.X86.eval_e h.2) (fun _ => CT.nil)
      (fun hb => (VG.Proof.AesOcb.X86.hashRest_ct v L (by have := of_decide_eq_false hb; omega)).mono fun _ h => h.1))
  obtain ⟨_, _, _, _, C, H⟩ := h₀
  have hal := L.al32
  refine WP.of_runBlock ⟨_, by grun [], ⟨_, _, _, _, C, H.of_keep (fun r h₁ _ _ _ => by gregs [g r h₁]) (by gmems [m])
    (by gmems [rd]) (by gmems [wr])⟩, ?_⟩
  gmems [ax, BitVec.and_self, VG.Proof.AesOcb.X86.beq_zero32 (show p.al % 16 < 2 ^ 32 by omega)]

/-- `HASH`. -/
theorem hash_ct (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) :
    CT (fun t => ∃ ciph l a, VG.Proof.AesOcb.X86.HCtx p ciph l a t ∧ VG.Proof.AesOcb.X86.Env p t ∧
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt l 0) (Impl.AesOcb.X86.hash (VG.Proof.AesOcb.X86.callees v)) := by
  unfold Impl.AesOcb.X86.hash
  refine CT.seq (J := fun t => VG.Proof.AesOcb.X86.HI p 0 t ∧ t.zf = some (decide (p.al / 16 = 0)))
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => by obtain ⟨_, _, _, _, E, _⟩ := h; exact E.ebp) (by taint_decide))
    (fun t ⟨_, _, _, C, E, hl0⟩ => WP.mono (VG.Proof.AesOcb.X86.hashHead_ok C E hl0) fun t' ⟨H, zf⟩ => ⟨⟨_, _, _, _, C, H⟩, zf⟩) ?_
  refine CT.seq (J := VG.Proof.AesOcb.X86.HI p (p.al / 16))
    (CT.ite (decide (p.al / 16 = 0)) (fun _ h => VG.Proof.AesOcb.X86.eval_e h.2) (fun _ => CT.nil)
      (fun hb => (VG.Proof.AesOcb.X86.hashLoop_ct v L (by have := of_decide_eq_false hb; omega)).mono fun _ h => h.1))
    (fun t ⟨⟨_, _, _, _, C, H⟩, zf⟩ => WP.ite (decide (p.al / 16 = 0)) (VG.Proof.AesOcb.X86.eval_e zf)
      (fun hb => WP.block_nil ⟨_, _, _, _, C, by rw [of_decide_eq_true hb]; exact H⟩)
      (fun hb => WP.mono (VG.Proof.AesOcb.X86.hashLoop_ok v C H (by have := of_decide_eq_false hb; omega)) fun t' H' =>
        ⟨_, _, _, _, C, H'⟩)) (VG.Proof.AesOcb.X86.hashTail_ct v L)

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.BodyCT`. -/
section

/-!
# AES-OCB on x86: the data and the tag in constant time

Untrusted: everything here is checked by Lean. A pass over the whole blocks
runs for their number, public, each block's offset by `lNtz` (`pass_ct`);
`whole` is two passes around a call (`whole_ct`); the rest addresses the
data's end and `W` (`rest_ct`); `body` branches on the data's length
(`body_ct`); the tag addresses only `W` (`tag_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxInv ctxLstar)
open VG.Proof.Ocb (offAt ckOf)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop xorLoop)
open VG.Proof.AesGcm.X86 (CT w64 w64_add slotv slotv_eq xorLoop_ct runBlock_app_of length_bytesAt)

/-! ## A pass -/

/-- Checksums by `fC` from `c0`. -/
def ckRec (fC : Block → Block → Block → Block) (O0 l : Block) (X : Nat → Block) (c0 : Block) : Nat → Block
  | 0 => c0
  | k + 1 => fC (VG.Proof.AesOcb.X86.ckRec fC O0 l X c0 k) (X k) (offAt O0 l (k + 1))

/-- A pass's state after `i` of its `m` blocks, for some offset, `L_*`,
blocks and checksums. -/
def PassI (p : VG.Proof.AesOcb.X86.Prm) (fC : Block → Block → Block → Block) (m i : Nat) (t : State) : Prop :=
  ∃ O0 l X ckF t₀, (∀ k < m, ckF (k + 1) = fC (ckF k) (X k) (offAt O0 l (k + 1))) ∧
    VG.Proof.AesOcb.X86.PassInv p m O0 l X (fun b o => b ^^^ o) ckF t₀ t i

theorem PassI.start {p : VG.Proof.AesOcb.X86.Prm} {fC : Block → Block → Block → Block} {m : Nat} {t : State} (E : VG.Proof.AesOcb.X86.Env p t)
    (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * 0)) (hdi : t.gpr .edi = BitVec.ofNat 32 (0 + 1))
    (hbx : t.gpr .ebx = BitVec.ofNat 32 (m - 0)) {l : Block}
    (hl0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) : VG.Proof.AesOcb.X86.PassI p fC m 0 t :=
  ⟨_, l, fun k => blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)),
    VG.Proof.AesOcb.X86.ckRec fC (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)) l
      (fun k => blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k))) (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO)),
    t, fun _ _ => rfl,
    { env := E, frame := Frame.refl _ _, rd := rfl, wr := rfl, esi := hsi, edi := hdi, ebx := hbx, ofs := rfl,
      ck := rfl, blk := fun k _ => by simp, l0 := hl0, gpr := fun _ _ _ _ _ _ _ => rfl }⟩

/-- A pass of `body` over the `m` whole blocks; `body ++ nextBlock` is
constant time from `ebp` and `esi` (`hct`). -/
theorem pass_ct {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {body : List Instr} {fC : Block → Block → Block → Block}
    (hB : VG.Proof.AesOcb.X86.BodyOk p body (fun b o => b ^^^ o) fC)
    (hct : ∀ {J : State → Prop} {B : BitVec 32}, (∀ s, J s → s.gpr .ebp = p.W ∧ s.gpr .esi = B) →
      CT J (.block (body ++ nextBlock)))
    {m : Nat} (hm0 : 0 < m) (hmn : 16 * m ≤ p.n) : CT (VG.Proof.AesOcb.X86.PassI p fC m 0) (pass body) := by
  have hn := L.n32
  unfold pass
  refine (CT.loopN (fun n t => 0 < n ∧ n ≤ m ∧ VG.Proof.AesOcb.X86.PassI p fC m (m - n) t) (fun n => ?_)
    (fun n t ⟨hn0, hnm, _, _, _, _, _, hck, P⟩ => WP.mono (VG.Proof.AesOcb.X86.pass_step L hB hck hmn (by omega) P) fun t' ⟨P', zf'⟩ =>
      ⟨hn0, by rw [VG.Proof.AesOcb.X86.eval_ne zf']; congr 1; by_cases h : n = 1 <;> simp [h] <;> omega,
        fun h1 => ⟨by omega, by omega, _, _, _, _, _, hck, by
          rw [show m - (n - 1) = m - n + 1 by omega]; exact P'⟩⟩) m).mono
    fun t h => ⟨hm0, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  by_cases hn : 0 < n ∧ n ≤ m
  swap
  · exact RelCT.of_false fun _ _ h => hn ⟨h.1.1, h.1.2.1⟩
  unfold nextOffset
  have hw : ∀ t, (0 < n ∧ n ≤ m ∧ VG.Proof.AesOcb.X86.PassI p fC m (m - n) t) → WP isa lNtz t fun t' =>
      VG.Proof.AesOcb.X86.Env p t' ∧ t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * (m - n)) := fun t ⟨_, _, _, _, _, _, _, _, P⟩ =>
    WP.mono (VG.Proof.AesOcb.X86.lNtz_ok L P.env (by omega) (by omega) P.edi P.l0) fun t₁ P₁ =>
      ⟨P₁.env L P.env, by rw [P₁.gpr _ (by decide) (by decide) (by decide), P.esi]⟩
  refine CT.seq (J := fun t => t.gpr .ebp = p.W ∧ t.gpr .esi = p.D + BitVec.ofNat 32 (16 * (m - n)))
    (CT.seq (J := fun t => VG.Proof.AesOcb.X86.Env p t ∧ t.gpr .esi = p.D + BitVec.ofNat 32 (16 * (m - n)))
      (VG.Proof.AesOcb.X86.lNtz_ct L (i := m - n + 1) (by omega) (by omega) fun t ⟨_, _, _, _, _, _, _, _, P⟩ => ⟨P.env, P.edi⟩) hw
      (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun t h => h.1.ebp) (by taint_decide)))
    (fun t h => WP.seq (WP.mono (hw t h) fun t₁ ⟨E₁, si₁⟩ => ?_)) (hct fun _ h => h)
  obtain ⟨t₂, run₂, -, g₂, -⟩ := VG.Proof.AesOcb.X86.xor16W_ok L E₁ (s := lO) (d := ofsO) (by decide) (by decide) (.inr (by decide))
  exact WP.of_runBlock ⟨t₂, run₂, by rw [g₂ _ (by decide), E₁.ebp], by rw [g₂ _ (by decide), si₁]⟩

/-! ## The whole blocks -/

/-- What `whole` needs. -/
def WhI (p : VG.Proof.AesOcb.X86.Prm) (m : Nat) (t : State) : Prop :=
  VG.Proof.AesOcb.X86.Env p t ∧ slotv t.mem p.W nbO = BitVec.ofNat 32 m ∧ ∃ l, blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0

theorem whole_ct {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub fn.code)
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {pre post : List Instr}
    {fC1 fC2 : Block → Block → Block → Block}
    (hB1 : VG.Proof.AesOcb.X86.BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : VG.Proof.AesOcb.X86.BodyOk p post (fun b o => b ^^^ o) fC2)
    (hct1 : ∀ {J : State → Prop} {B : BitVec 32}, (∀ s, J s → s.gpr .ebp = p.W ∧ s.gpr .esi = B) →
      CT J (.block (pre ++ nextBlock)))
    (hct2 : ∀ {J : State → Prop} {B : BitVec 32}, (∀ s, J s → s.gpr .ebp = p.W ∧ s.gpr .esi = B) →
      CT J (.block (post ++ nextBlock)))
    {m : Nat} (hm0 : 0 < m) (hmn : 16 * m ≤ p.n) : CT (VG.Proof.AesOcb.X86.WhI p m) (whole fn pre post) := by
  have hn := L.n32
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨w64 p.D, 16 * m⟩ :=
    fun h => ((L.d_w.sub_left (Region.sub_prefix hmn)).sub_right (Lay.wSub h)).symm
  -- What a pass keeps.
  have kP : ∀ {d k : Nat} {m' : Mem} {O0 l : Block} {X : Nat → Block} {ckF : Nat → Block} {t₀ t : State} {i : Nat},
      VG.Proof.AesOcb.X86.PassInv p m O0 l X (fun b o => b ^^^ o) ckF t₀ t i → d + k ≤ 2560 →
      (d + k ≤ ofsO ∨ (48 ≤ d ∧ d + k ≤ lO) ∨ (112 ≤ d ∧ d + k ≤ kO) ∨ 224 ≤ d) → t₀.mem = m' →
      ∀ r ∈ [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
        ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨w64 p.D, 16 * m⟩],
        (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun _ h₁ h₂ _ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₂ ⊢; omega) h₁ (by decide)
    · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₂ ⊢; omega) h₁ (by decide)
    · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₂ ⊢; omega) h₁ (by decide)
    · exact Lay.w_w (by simp only [ofsO, lO, kO, ckO] at h₂ ⊢; omega) h₁ (by decide)
    · exact dW h₁
  -- What a call keeps.
  have kC : ∀ {d k : Nat}, d + k ≤ scrO → ∀ r ∈ [⟨w64 p.D, 16 * m⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, VG.Proof.AesOcb.X86.stk p],
      (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dW (by simp only [scrO] at h; omega)
    · exact Lay.w_w (.inl h) (by simp only [scrO] at h; omega) (by decide)
    · exact (L.bw' (by simp only [scrO] at h; omega)).symm
  have start : ∀ {fC : Block → Block → Block → Block} t, VG.Proof.AesOcb.X86.WhI p m t → ∃ t', runBlock isa passStart t = some t' ∧
      VG.Proof.AesOcb.X86.PassI p fC m 0 t' := fun t ⟨E, nb, l, hl0⟩ => by
    obtain ⟨t₁, run₁, si₁, bx₁, di₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.passStart_ok L E nb
    exact ⟨t₁, run₁, PassI.start (E.keep (by rw [g₁ _ (by decide) (by decide) (by decide)])
      (by rw [g₁ _ (by decide) (by decide) (by decide)]) rd₁ wr₁ m₁) si₁ di₁ bx₁ (by rw [m₁]; exact hl0)⟩
  -- `nbO` and `l0O`, across a pass.
  have nbP : ∀ {O0 l : Block} {X : Nat → Block} {ckF : Nat → Block} {t₀ t t' : State} {i i' : Nat},
      VG.Proof.AesOcb.X86.PassInv p m O0 l X (fun b o => b ^^^ o) ckF t₀ t i → VG.Proof.AesOcb.X86.PassInv p m O0 l X (fun b o => b ^^^ o) ckF t₀ t' i' →
      slotv t'.mem p.W nbO = slotv t.mem p.W nbO := fun P P' => by
    rw [slotv_eq, slotv_eq, P'.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _)
      (kP P' (by decide) (.inr (.inr (.inr (by decide)))) rfl) (by decide),
      P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _)
      (kP P (by decide) (.inr (.inr (.inr (by decide)))) rfl) (by decide)]
  have hargs : ∀ t, VG.Proof.AesOcb.X86.WhI p m t → ∃ s₁, runBlock isa [.mov .edx (slot dataO), .mov .ebx (slot nbO)] t = some s₁ ∧
      s₁.gpr .edx = p.D ∧ s₁.gpr .ebx = BitVec.ofNat 32 m ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = t.gpr r) ∧ s₁.mem = t.mem ∧
      s₁.rd = t.rd ∧ s₁.wr = t.wr := fun t ⟨E, nb, _⟩ => by
    have hD := E.slots.data
    simp only [slotv_eq] at hD nb
    exact ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hD, nb], by gregs [hD], by gregs [nb],
      fun r _ h₂ _ h₄ => by gregs [h₂, h₄], by gmems [], by gmems [], by gmems []⟩
  unfold whole
  -- The first pass.
  refine CT.seq (J := fun t => VG.Proof.AesOcb.X86.PassI p fC1 m 0 t ∧ slotv t.mem p.W nbO = BitVec.ofNat 32 m)
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.1.ebp) (by taint_decide))
    (fun t ⟨E, nb, l, hl0⟩ => by
      obtain ⟨t₁, run₁, si₁, bx₁, di₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.passStart_ok L E nb
      exact WP.of_runBlock ⟨t₁, run₁, PassI.start (E.keep (by rw [g₁ _ (by decide) (by decide) (by decide)])
        (by rw [g₁ _ (by decide) (by decide) (by decide)]) rd₁ wr₁ m₁) si₁ di₁ bx₁ (by rw [m₁]; exact hl0),
        by rw [m₁]; exact nb⟩) ?_
  refine CT.seq (J := VG.Proof.AesOcb.X86.WhI p m) ((VG.Proof.AesOcb.X86.pass_ct L hB1 hct1 hm0 hmn).mono fun _ h => h.1)
    (fun t ⟨⟨_, _, _, _, _, hck, P⟩, nb⟩ => WP.mono (VG.Proof.AesOcb.X86.pass_ok L hB1 hck hmn hm0 P) fun t' P' =>
      ⟨P'.env, by rw [nbP P P', nb], _, P'.l0⟩) ?_
  -- The call.
  refine CT.seq (J := VG.Proof.AesOcb.X86.WhI p m) (VG.Proof.AesOcb.X86.callBlocks_ct ok ct nosp stack L
      (fun t h => ⟨h.1, DReg.d L h.1 hmn, hargs t h⟩) fun hJ => by exact CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp hJ) (by taint_decide))
    (fun t h => WP.mono (VG.Proof.AesOcb.X86.callBlocks_ok ok nosp stack L h.1 (hargs t h) (DReg.d L h.1 hmn)) fun t' P => ?_) ?_
  · obtain ⟨E, nb, l, hl0⟩ := h
    refine ⟨P.env, ?_, l, ?_⟩
    · rw [← nb]
      exact P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _) (kC (by decide))
        (by decide)
    · rw [Proof.Ocb.blockAtMem_frame P.frame (kC (by decide)), hl0]
  -- `Offset_0` again, and the second pass.
  refine CT.seq (J := VG.Proof.AesOcb.X86.PassI p fC2 m 0) (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.1.ebp) (by taint_decide))
    (fun t ⟨E, nb, l, hl0⟩ => ?_) ((VG.Proof.AesOcb.X86.pass_ct L hB2 hct2 hm0 hmn))
  obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.copy16_ok L E (s := o0O) (d := ofsO) (by decide) (by decide)
    (.inr (by decide))
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₁.mem := by
    rw [m₁]; exact VG.Proof.AesOcb.X86.copyMem16_frame _ _ _ _ _
  have k₁ : ∀ {d k : Nat}, (d + k ≤ ofsO ∨ ofsO + 16 ≤ d) → d + k ≤ 2560 →
      ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region)], (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun h h' r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w h h' (by decide)
  have E₁ : VG.Proof.AesOcb.X86.Env p t₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (VG.Proof.AesOcb.X86.frame_toMut f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  have nb₁ : slotv t₁.mem p.W nbO = BitVec.ofNat 32 m := by
    rw [← nb]
    exact f₁.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _)
      (k₁ (.inr (by decide)) (by decide)) (by decide)
  have l0₁ : blockAtMem t₁.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0 := by
    rw [Proof.Ocb.blockAtMem_frame f₁ (k₁ (.inr (by decide)) (by decide)), hl0]
  obtain ⟨t', run', P⟩ := start (fC := fC2) t₁ ⟨E₁, nb₁, l, l0₁⟩
  exact WP.of_runBlock ⟨t', runBlock_app_of run₁ run', P⟩

/-! ## The rest -/

/-- What the rest's pieces need: the environment, the rest's address in
`esi` and its length in `W + restO`. -/
def RI (p : VG.Proof.AesOcb.X86.Prm) (P : BitVec 32) (r : Nat) (t : State) : Prop :=
  VG.Proof.AesOcb.X86.Env p t ∧ t.gpr .esi = P ∧ slotv t.mem p.W restO = BitVec.ofNat 32 r ∧ VG.Proof.AesOcb.X86.RBuf p t P r

theorem padCk_ct {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {P : BitVec 32} {r : Nat} (hr : 0 < r) (hr' : r < 16) :
    CT (VG.Proof.AesOcb.X86.RI p P r) padCk := by
  unfold padCk
  refine CT.seq (J := VG.Proof.AesOcb.X86.Env p) (VG.Proof.AesOcb.X86.padTo_ct L (.inr rfl) fun t h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun t ⟨E, si, rest, hP⟩ => WP.mono (VG.Proof.AesOcb.X86.padTo_ok L E (d := t2O) (cO := restO) hr hr' (by decide) (by decide)
      (.inr (by decide)) si rest hP.sbuf) fun t' ⟨fr, _, g, rd, wr⟩ =>
        E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
          (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr
          (VG.Proof.AesOcb.X86.frame_toMut fr fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))))
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.ebp) (by taint_decide))

theorem padCk_ri {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {P : BitVec 32} {r : Nat} (hr : 0 < r) (hr' : r < 16) {t : State}
    (h : VG.Proof.AesOcb.X86.RI p P r t) : WP isa padCk t (VG.Proof.AesOcb.X86.RI p P r) := by
  obtain ⟨E, si, rest, hP⟩ := h
  refine WP.mono (VG.Proof.AesOcb.X86.padCk_ok L E hr hr' si rest hP.sbuf) fun t' ⟨fr, _, g, rd, wr⟩ => ⟨?_, ?_, ?_, hP.of_eq wr⟩
  · exact E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr
      (VG.Proof.AesOcb.X86.frame_toMut fr fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
        · exact VG.Proof.AesOcb.X86.inMut_w p (.inl (by decide)))
  · rw [g _ (by decide) (by decide) (by decide) (by decide), si]
  · rw [← rest]
    exact fr.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)

theorem xorPad_ct {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {P : BitVec 32} {r : Nat} : CT (VG.Proof.AesOcb.X86.RI p P r) xorPad := by
  unfold xorPad
  refine CT.seq (J := fun t => t.gpr .edi = P ∧ t.gpr .edx = p.W + BitVec.ofNat 32 tmpO ∧
      t.gpr .ecx = BitVec.ofNat 32 r)
    (CT.taint [.ebp, .esi] (VG.Proof.AesOcb.X86.pin2 fun _ h => ⟨h.1.ebp, h.2.1⟩) (by taint_decide)) (fun t ⟨E, si, rest, _⟩ => ?_)
    (xorLoop_ct (VG.Proof.AesOcb.X86.pin3 fun _ h => h))
  simp only [slotv_eq] at rest
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, si, rest], by gregs [si], by gregs [E.ebp],
    by gregs [rest]⟩

theorem xorPad_ri {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {P : BitVec 32} {r : Nat} (hr : 0 < r) (hr' : r < 16) {t : State}
    (h : VG.Proof.AesOcb.X86.RI p P r t) : WP isa xorPad t (VG.Proof.AesOcb.X86.RI p P r) := by
  obtain ⟨E, si, rest, hP⟩ := h
  refine WP.mono (VG.Proof.AesOcb.X86.xorPad_ok L E hr hr' si rest hP) fun t' ⟨m, g, rd, wr⟩ => ?_
  have fr : Frame [⟨w64 P, r⟩] t.mem t'.mem := by
    rw [m]
    exact writeBytes_frame _ _ _ (by
      simp only [Spec.Ocb.xor, List.length_zipWith, length_bytesAt, Nat.min_self]; exact Region.contains_self _ _)
  refine ⟨E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.ebp])
    (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr (VG.Proof.AesOcb.X86.frame_toMut fr hP.inm),
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), si], ?_, hP.of_eq wr⟩
  rw [← rest]
  exact fr.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact (hP.w.sub_right (Lay.wSub (by decide))).symm) (by decide)

theorem rest_ct (v : BlocksImpl) (enc : Bool) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {P : BitVec 32} {r : Nat} (hr : 0 < r)
    (hr' : r < 16) : CT (VG.Proof.AesOcb.X86.RI p P r) (rest (VG.Proof.AesOcb.X86.callees v) enc) := by
  unfold rest
  refine RelCT.assoc (CT.seq (J := VG.Proof.AesOcb.X86.RI p P r) (CT.seq (J := VG.Proof.AesOcb.X86.Env p) ?_ (fun t h => ?_)
    (VG.Proof.AesOcb.X86.oneCall_ct v.encOk v.encCt v.encNosp v.encStack L (.inl rfl) fun _ h => h))
    (fun t ⟨E, si, rest, hP⟩ => WP.mono (VG.Proof.AesOcb.X86.restHead_ok v L E) fun t' H => ⟨H.env, ?_, ?_, hP.of_eq H.wr⟩) ?_)
  · rw [show ([.mov .ebx (slot ctxO)] ++ xor16 .ebx 240 ofsO ++ copy16 ofsO tmpO : List Instr) =
      .mov .ebx (slot ctxO) :: (xor16 .ebx 240 ofsO ++ copy16 ofsO tmpO) from rfl]
    exact VG.Proof.AesOcb.X86.load_blk_ct L (r := .ebx) (o := ctxO) (by decide) (fun t h => ⟨h.1, h.1.slots.ctx⟩)
      (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h) (by taint_decide))
      (CT.taint [.ebp, .ebx] (VG.Proof.AesOcb.X86.pin2 fun t h => ⟨Ld.reg (by decide)
        (fun s (h : VG.Proof.AesOcb.X86.RI p P r s) => h.1.ebp) t h, by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide))
  · obtain ⟨t₃, run₃, E₃, -⟩ := VG.Proof.AesOcb.X86.restBlk_ok L h.1
    exact WP.of_runBlock ⟨t₃, run₃, E₃⟩
  · rw [H.gpr _ (by decide) (by decide) (by decide) (by decide), si]
  · rw [← rest]
    exact H.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  cases enc
  · exact CT.seq (VG.Proof.AesOcb.X86.xorPad_ct L) (fun t h => VG.Proof.AesOcb.X86.xorPad_ri L hr hr' h) (VG.Proof.AesOcb.X86.padCk_ct L hr hr')
  · exact CT.seq (VG.Proof.AesOcb.X86.padCk_ct L hr hr') (fun t h => VG.Proof.AesOcb.X86.padCk_ri L hr hr' h) (VG.Proof.AesOcb.X86.xorPad_ct L)

/-! ## `body` -/

/-- What `body` needs at its start. -/
def BI (p : VG.Proof.AesOcb.X86.Prm) (t : State) : Prop :=
  VG.Proof.AesOcb.X86.Env p t ∧ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 o0O) = blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ∧
    blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0 ∧
    blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar t.mem (w64 p.K)) 0

theorem bodyHead_whi {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) {l : Block}
    (hl0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.block [.mov .ebx (slot lenO), .shift .shr .ebx 4, .store (at_ .ebp nbO) .ebx,
        .alu .test .ebx (.reg .ebx)]) t fun t' => VG.Proof.AesOcb.X86.WhI p (p.n / 16) t' ∧ t'.zf = some (decide (p.n / 16 = 0)) := by
  obtain ⟨t₁, run₁, m₁, zf₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.bodyHead_ok L E
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩] t.mem t₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨t₁, run₁, ⟨E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (VG.Proof.AesOcb.X86.frame_toMut f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))),
    by rw [slotv_eq, m₁, Mem.readW_writeW_self32], l, ?_⟩, zf₁⟩
  rw [Proof.Ocb.blockAtMem_frame f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)), hl0]

theorem bodyTail_ri {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {t : State} (E : VG.Proof.AesOcb.X86.Env p t) :
    WP isa (.block [.mov .esi (slot dataO), .mov .eax (slot lenO), .mov .ecx (.reg .eax), .alu .and .ecx (imm 15),
        .store (at_ .ebp restO) .ecx, .alu .sub .eax (.reg .ecx), .alu .add .esi (.reg .eax),
        .alu .test .ecx (.reg .ecx)]) t fun t' => VG.Proof.AesOcb.X86.Env p t' ∧
      t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧
      slotv t'.mem p.W restO = BitVec.ofNat 32 (p.n % 16) ∧ t'.zf = some (decide (p.n % 16 = 0)) := by
  obtain ⟨t₁, run₁, si₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.bodyTail_ok L E
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩] t.mem t₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact WP.of_runBlock ⟨t₁, run₁, E.mut L (by rw [g₁ _ (by decide) (by decide) (by decide), E.ebp])
    (by rw [g₁ _ (by decide) (by decide) (by decide), E.esp]) rd₁ wr₁ (VG.Proof.AesOcb.X86.frame_toMut f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))),
    si₁, by rw [slotv_eq, m₁, Mem.readW_writeW_self32], zf₁⟩

/-- The rest of `body`, if there is one. -/
theorem bodyRest_ct (v : BlocksImpl) (enc : Bool) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) :
    CT (VG.Proof.AesOcb.X86.Env p) (.seq (.block [.mov .esi (slot dataO), .mov .eax (slot lenO), .mov .ecx (.reg .eax),
        .alu .and .ecx (imm 15), .store (at_ .ebp restO) .ecx, .alu .sub .eax (.reg .ecx), .alu .add .esi (.reg .eax),
        .alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) (rest (VG.Proof.AesOcb.X86.callees v) enc))) :=
  CT.seq (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => VG.Proof.AesOcb.X86.bodyTail_ri L E)
    (CT.ite _ (fun _ h => VG.Proof.AesOcb.X86.eval_e h.2.2.2) (fun _ => CT.nil) fun hb => by
      have hr : 0 < p.n % 16 := by have := of_decide_eq_false hb; omega
      exact (VG.Proof.AesOcb.X86.rest_ct v enc L hr (Nat.mod_lt _ (by decide))).mono fun t h =>
        ⟨h.1, h.2.1, h.2.2.1, VG.Proof.AesOcb.X86.rbuf_tail L h.1 hr⟩)

theorem bodySeal_ct (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) : CT (VG.Proof.AesOcb.X86.BI p) (body (VG.Proof.AesOcb.X86.callees v) true) := by
  have hn := L.n32
  simp only [body, ↓reduceIte]
  refine RelCT.assoc (CT.seq (J := VG.Proof.AesOcb.X86.Env p) (CT.seq (J := fun t => VG.Proof.AesOcb.X86.WhI p (p.n / 16) t ∧ t.zf = some (decide (p.n / 16 = 0)))
      (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.1.ebp) (by taint_decide)) (fun t ⟨E, _, _, hl0⟩ => VG.Proof.AesOcb.X86.bodyHead_whi L E hl0)
      (CT.ite _ (fun _ h => VG.Proof.AesOcb.X86.eval_e h.2) (fun _ => CT.nil) fun hb => ?_)) (fun t ⟨E, ho0, hck, hl0⟩ => ?_)
    (VG.Proof.AesOcb.X86.bodyRest_ct v true L))
  · exact (VG.Proof.AesOcb.X86.whole_ct v.encOk v.encCt v.encNosp v.encStack L (VG.Proof.AesOcb.X86.sealPre_ok L) (VG.Proof.AesOcb.X86.xorOfs_ok L)
      (fun h => by exact CT.taint [.ebp, .esi] (VG.Proof.AesOcb.X86.pin2 h) (by taint_decide))
      (fun h => by exact CT.taint [.ebp, .esi] (VG.Proof.AesOcb.X86.pin2 h) (by taint_decide))
      (by have := of_decide_eq_false hb; omega) (Nat.mul_div_le _ _)).mono fun _ h => h.1
  · exact WP.mono (VG.Proof.AesOcb.X86.wholeIte_ok (O0 := blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO))
      (l := ctxLstar t.mem (w64 p.K)) (G := fun m => ctxCiph m (w64 p.K) p.R)
      (ckF1 := ckOf fun i => blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)))
      (ckF2 := fun _ => ckOf (fun i => blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
      v.encOk v.encNosp v.encStack (fun P _ hi => P.enc hi) (fun h => VG.Proof.AesOcb.X86.ctxCiph_mut L h) (VG.Proof.AesOcb.X86.sealPre_ok L) (VG.Proof.AesOcb.X86.xorOfs_ok L)
      L E rfl ho0 hck hl0 (fun _ _ => rfl) rfl (fun _ _ => rfl)) fun _ Pw => Pw.env

theorem bodyOpen_ct (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) : CT (VG.Proof.AesOcb.X86.BI p) (body (VG.Proof.AesOcb.X86.callees v) false) := by
  have hn := L.n32
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine RelCT.assoc (CT.seq (J := VG.Proof.AesOcb.X86.Env p) (CT.seq (J := fun t => VG.Proof.AesOcb.X86.WhI p (p.n / 16) t ∧ t.zf = some (decide (p.n / 16 = 0)))
      (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.1.ebp) (by taint_decide)) (fun t ⟨E, _, _, hl0⟩ => VG.Proof.AesOcb.X86.bodyHead_whi L E hl0)
      (CT.ite _ (fun _ h => VG.Proof.AesOcb.X86.eval_e h.2) (fun _ => CT.nil) fun hb => ?_)) (fun t ⟨E, ho0, hck, hl0⟩ => ?_)
    (VG.Proof.AesOcb.X86.bodyRest_ct v false L))
  · exact (VG.Proof.AesOcb.X86.whole_ct v.decOk v.decCt v.decNosp v.decStack L (VG.Proof.AesOcb.X86.xorOfs_ok L) (VG.Proof.AesOcb.X86.openPost_ok L)
      (fun h => by exact CT.taint [.ebp, .esi] (VG.Proof.AesOcb.X86.pin2 h) (by taint_decide))
      (fun h => by exact CT.taint [.ebp, .esi] (VG.Proof.AesOcb.X86.pin2 h) (by taint_decide))
      (by have := of_decide_eq_false hb; omega) (Nat.mul_div_le _ _)).mono fun _ h => h.1
  · exact WP.mono (VG.Proof.AesOcb.X86.wholeIte_ok (O0 := blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO))
      (l := ctxLstar t.mem (w64 p.K)) (G := fun m => ctxInv m (w64 p.K) p.R) (ckF1 := fun _ => 0)
      (ckF2 := ckOf fun i => ctxInv t.mem (w64 p.K) p.R
        (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) ^^^
          offAt (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)) (ctxLstar t.mem (w64 p.K)) (i + 1)) ^^^
        offAt (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)) (ctxLstar t.mem (w64 p.K)) (i + 1))
      v.decOk v.decNosp v.decStack (fun P _ hi => P.dec hi) (fun h => VG.Proof.AesOcb.X86.ctxInv_mut L h) (VG.Proof.AesOcb.X86.xorOfs_ok L) (VG.Proof.AesOcb.X86.openPost_ok L)
      L E rfl ho0 hck hl0 (fun _ _ => rfl) rfl (fun _ _ => rfl)) fun _ Pw => Pw.env

/-! ## The tag -/

theorem tag_ct (v : BlocksImpl) {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    CT (VG.Proof.AesOcb.X86.Env p) (tag (VG.Proof.AesOcb.X86.callees v) d) := by
  have step : ∀ {u u' : State} {a : Nat}, VG.Proof.AesOcb.X86.Env p u → a + 16 ≤ 128 →
      Frame [⟨w64 p.W + BitVec.ofNat 64 a, 16⟩] u.mem u'.mem → (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) →
      u'.rd = u.rd → u'.wr = u.wr → VG.Proof.AesOcb.X86.Env p u' := fun Eu ha f g rd wr =>
    Eu.mut L (by rw [g _ (by decide), Eu.ebp]) (by rw [g _ (by decide), Eu.esp]) rd wr (VG.Proof.AesOcb.X86.frame_toMut f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inl ha))
  unfold tag
  refine CT.seq (J := VG.Proof.AesOcb.X86.Env p) (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_)
    (CT.seq (J := VG.Proof.AesOcb.X86.Env p) (VG.Proof.AesOcb.X86.oneCall_ct v.encOk v.encCt v.encNosp v.encStack L (.inl rfl) fun _ h => h)
      (fun t E => WP.mono (VG.Proof.AesOcb.X86.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E
        (VG.Proof.AesOcb.X86.oneBlock_ok E tmpO) (DReg.w L E (d := tmpO) (n := 1) (by decide) (.inl (by decide)))) fun _ P => P.env) ?_)
  · obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86.copy16_ok L E (s := ckO) (d := tmpO) (by decide) (by decide)
      (.inl (by decide))
    have E₁ := step E (a := tmpO) (by decide) (by rw [m₁]; exact VG.Proof.AesOcb.X86.copyMem16_frame _ _ _ _ _) g₁ rd₁ wr₁
    obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86.xor16W_ok L E₁ (s := ofsO) (d := tmpO) (by decide) (by decide)
      (.inl (by decide))
    have E₂ := step E₁ (a := tmpO) (by decide) (by rw [m₂]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _) g₂ rd₂ wr₂
    obtain ⟨t₃, run₃, m₃, g₃, rd₃, wr₃⟩ := VG.Proof.AesOcb.X86.xor16W_ok L E₂ (s := ldO) (d := tmpO) (by decide) (by decide)
      (.inl (by decide))
    exact WP.of_runBlock ⟨t₃, runBlock_app_of (runBlock_app_of run₁ run₂) run₃,
      step E₂ (a := tmpO) (by decide) (by rw [m₃]; exact VG.Proof.AesOcb.X86.xorMem16_frame _ _ _ _ _) g₃ rd₃ wr₃⟩
  · rcases hd with rfl | rfl
    · exact CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.ebp) (by taint_decide)
    · exact CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.ebp) (by taint_decide)

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.SealCT`. -/
section

/-!
# AES-OCB on x86: `vg_aes_ocb_seal` and `vg_aes_ocb_open` in constant time

Untrusted: everything here is checked by Lean. `front` is its pieces in
sequence, each started from what the pieces before it leave (`front_ct`);
then the copies of the tag, the comparison and the mask, which address `W`,
the tag and the data, their addresses and lengths loaded from their slots
(`seal_ct`, `open_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop restore)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq copyLoop_ct length_bytesAt)

/-- `front`: the entry, the setup, `Offset_0`, `HASH`, the data and the tag. -/
theorem front_ct (v : BlocksImpl) (enc : Bool) (p : VG.Proof.AesOcb.X86.Prm) {d : Nat} (hd : d = tagO ∨ d = t2O)
    (hbody : VG.Proof.AesOcb.X86.Lay p → CT (VG.Proof.AesOcb.X86.BI p) (body (VG.Proof.AesOcb.X86.callees v) enc))
    (hbw : VG.Proof.AesOcb.X86.Lay p → ∀ t, VG.Proof.AesOcb.X86.BI p t → WP isa (body (VG.Proof.AesOcb.X86.callees v) enc) t (VG.Proof.AesOcb.X86.Env p)) :
    CT (fun s => VG.Proof.AesOcb.X86.onePre s ∧ VG.Proof.AesOcb.X86.prmOf s = p) (front (VG.Proof.AesOcb.X86.callees v) enc d) := by
  by_cases hex : ∃ s, VG.Proof.AesOcb.X86.onePre s ∧ VG.Proof.AesOcb.X86.prmOf s = p
  swap
  · exact RelCT.of_false fun s _ h => hex ⟨s, h.1⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : VG.Proof.AesOcb.X86.Lay p := hzp ▸ VG.Proof.AesOcb.X86.lay_of hz
  have kL : ∀ {m m' : Mem}, Frame (VG.Proof.AesOcb.X86.mutR p) m m' → ctxLstar m' (w64 p.K) = ctxLstar m (w64 p.K) := fun h => VG.Proof.AesOcb.X86.lstar_mut L h
  unfold front
  -- The entry.
  refine CT.seq (J := VG.Proof.AesOcb.X86.Env p) (VG.Proof.AesOcb.X86.entry_ct p) (fun s ⟨h, hp⟩ => WP.mono (VG.Proof.AesOcb.X86.entry_ok h) fun _ En => hp ▸ En.env) ?_
  -- The setup.
  refine CT.seq (J := fun t => VG.Proof.AesOcb.X86.Env p t ∧ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0 ∧
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar t.mem (w64 p.K)) 0)
    (VG.Proof.AesOcb.X86.setup_ct L fun _ h => h) (fun t E => ?_) ?_
  · obtain ⟨t₂, run₂, P₂⟩ := VG.Proof.AesOcb.X86.setup_ok L E
    have f₂ : Frame (VG.Proof.AesOcb.X86.mutR p) t.mem t₂.mem := P₂.frame.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp
    exact WP.of_runBlock ⟨t₂, run₂, E.mut L (by rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide), E.esp]) P₂.rd P₂.wr f₂, P₂.ck,
      by rw [P₂.l0, kL f₂]⟩
  -- `Offset_0`.
  refine CT.seq (J := VG.Proof.AesOcb.X86.BI p) (VG.Proof.AesOcb.X86.nonce_ct v L fun _ h => h.1) (fun t ⟨E, ck, l0⟩ => WP.mono (VG.Proof.AesOcb.X86.nonce_ok v L E)
    fun t' P => ⟨P.env, by rw [P.o0, P.ofs], by rw [P.keep (by decide) (by decide), ck],
      by rw [P.keep (by decide) (by decide), l0, kL (VG.Proof.AesOcb.X86.wR_mut P.frame)]⟩) ?_
  -- `HASH`.
  have kH : ∀ {m m' : Mem}, Frame (VG.Proof.AesOcb.X86.hashR p) m m' → ∀ {d : Nat},
      (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (176 ≤ d ∧ d + 16 ≤ 220) ∨ (224 ≤ d ∧ d + 16 ≤ 264)) →
      blockAtMem m' (w64 p.W + BitVec.ofNat 64 d) = blockAtMem m (w64 p.W + BitVec.ofNat 64 d) :=
    fun {m m'} F {d} hd => Proof.Ocb.blockAtMem_frame F fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Lay.w_w (by simp only [sumO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [lO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [ohO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [kO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [hlO]; omega) (by omega) (by decide)
      · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.bw' (by omega)).symm
  refine CT.seq (J := VG.Proof.AesOcb.X86.BI p) ((VG.Proof.AesOcb.X86.hash_ct v L).mono fun t ⟨E, _, _, l0⟩ => ⟨_, _, _, ⟨L, rfl, rfl, rfl⟩, E, l0⟩)
    (fun t ⟨E, o0, ck, l0⟩ => WP.mono (VG.Proof.AesOcb.X86.hash_ok v ⟨L, rfl, rfl, rfl⟩ E l0) fun t' ⟨E', F, _, _, _⟩ =>
      ⟨E', by rw [kH F (by decide), kH F (by decide), o0], by rw [kH F (by decide), ck],
        by rw [kH F (by decide), l0, kL (VG.Proof.AesOcb.X86.wR_mut (VG.Proof.AesOcb.X86.hashR_wR F))]⟩) ?_
  -- The data and the tag.
  exact CT.seq (J := VG.Proof.AesOcb.X86.Env p) (hbody L) (hbw L) (VG.Proof.AesOcb.X86.tag_ct v L hd)

/-! ## The tag out and in, the comparison and the mask -/

theorem tagOut_ct {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) : CT (VG.Proof.AesOcb.X86.Env p) tagOut := by
  unfold tagOut
  refine CT.seq (J := fun t => t.gpr .edi = p.W ∧ t.gpr .edx = p.T ∧ t.gpr .ecx = BitVec.ofNat 32 p.tl)
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_) (copyLoop_ct (VG.Proof.AesOcb.X86.pin3 fun _ h => h))
  have hT := E.slots.tg
  have hv := E.slots.tlen
  simp only [slotv_eq] at hT hv
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv, hT], by gregs [E.ebp], by gregs [hT], by gregs [hv]⟩

theorem recv_ct {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) : CT (VG.Proof.AesOcb.X86.Env p) recv := by
  unfold recv
  refine CT.seq (J := fun t => t.gpr .edi = p.T ∧ t.gpr .edx = p.W ∧ t.gpr .ecx = BitVec.ofNat 32 p.tl)
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_) (copyLoop_ct (VG.Proof.AesOcb.X86.pin3 fun _ h => h))
  have hT := E.slots.tg
  have hv := E.slots.tlen
  simp only [slotv_eq] at hT hv
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv, hT], by gregs [hT], by gregs [E.ebp], by gregs [hv]⟩

theorem cmp_ct {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) : CT (VG.Proof.AesOcb.X86.Env p) cmp := by
  unfold cmp
  refine CT.seq (J := fun t => t.gpr .ebp = p.W ∧ t.gpr .edi = p.W ∧ t.gpr .ecx = BitVec.ofNat 32 p.tl)
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_)
    (CT.taint [.ebp, .edi, .ecx] (VG.Proof.AesOcb.X86.pin3 fun _ h => h) (by taint_decide))
  have hv := E.slots.tlen
  simp only [slotv_eq] at hv
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv], by gregs [E.ebp], by gregs [E.ebp], by gregs [hv]⟩

theorem mask_ct {p : VG.Proof.AesOcb.X86.Prm} (L : VG.Proof.AesOcb.X86.Lay p) : CT (VG.Proof.AesOcb.X86.Env p) mask := by
  unfold mask
  refine VG.Proof.AesOcb.X86.load_ct L (r := .edi) (o := dataO) (by decide) (fun t E => ⟨E, E.slots.data⟩)
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h) (by taint_decide)) ?_
  refine VG.Proof.AesOcb.X86.load_ct L (r := .ecx) (o := lenO) (by decide)
    (fun t h => ⟨Ld.env (by decide) (by decide) (fun _ h => h) t h, (Ld.env (by decide) (by decide) (fun _ h => h) t h).slots.len⟩)
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h) (by taint_decide)) ?_
  exact CT.taint [.ebp, .edi, .ecx] (VG.Proof.AesOcb.X86.pin3 fun t h => ⟨Ld.reg (by decide) (fun s h =>
      Ld.reg (by decide) (fun s (h : VG.Proof.AesOcb.X86.Env p s) => h.ebp) s h) t h,
    Ld.reg (by decide) (fun s h => by obtain ⟨_, _, hv, _⟩ := h; exact hv) t h,
    by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide)

/-! ## The functions -/

theorem prmOf_eq {s₁ s₂ : State} (h : VG.Proof.AesOcb.X86.onePub s₁ s₂) : VG.Proof.AesOcb.X86.prmOf s₁ = VG.Proof.AesOcb.X86.prmOf s₂ := by
  obtain ⟨hsp, ha⟩ := h
  simp only [VG.Proof.AesOcb.X86.prmOf, hsp, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide)]

theorem seal_ct (v : BlocksImpl) : ConstantTime isa sealX86.pre sealX86.pub («seal» (VG.Proof.AesOcb.X86.callees v)) := by
  refine CT.constantTime VG.Proof.AesOcb.X86.prmOf (fun _ _ _ _ h => VG.Proof.AesOcb.X86.prmOf_eq h) fun p => ?_
  by_cases hex : ∃ s, sealX86.pre s ∧ VG.Proof.AesOcb.X86.prmOf s = p
  swap
  · exact RelCT.of_false fun s _ h => hex ⟨s, h.1⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : VG.Proof.AesOcb.X86.Lay p := hzp ▸ VG.Proof.AesOcb.X86.lay_of (VG.Proof.AesOcb.X86.onePre_seal hz)
  unfold «seal»
  refine CT.seq (J := fun t => VG.Proof.AesOcb.X86.Env p t ∧ Covers [⟨w64 p.T, p.tl⟩] t.wr)
    ((VG.Proof.AesOcb.X86.front_ct v true p (.inl rfl) (fun L => VG.Proof.AesOcb.X86.bodySeal_ct v L) fun L t ⟨E, o0, ck, l0⟩ =>
      WP.mono (VG.Proof.AesOcb.X86.bodySeal_ok v L E rfl o0 ck l0) fun _ B => B.env).mono fun s ⟨h, hp⟩ => ⟨VG.Proof.AesOcb.X86.onePre_seal h, hp⟩)
    (fun s ⟨h, hp⟩ => WP.mono (VG.Proof.AesOcb.X86.sealFront_ok v (VG.Proof.AesOcb.X86.onePre_seal h)) fun _ ⟨F, _⟩ => hp ▸ ⟨F.env, by
      rw [F.wr]; exact VG.Proof.AesOcb.X86.covers_of_mem (r := VG.Proof.AesOcb.X86.tagR s) (by rw [h.2.1]; simp)⟩) ?_
  refine CT.seq (J := fun t => t.gpr .ebp = p.W) ((VG.Proof.AesOcb.X86.tagOut_ct L).mono fun _ h => h.1)
    (fun t ⟨E, hT⟩ => WP.mono (VG.Proof.AesOcb.X86.tagOut_ok L E hT) fun _ ⟨_, g, _⟩ => by
      rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h) (by taint_decide))

theorem open_ct (v : BlocksImpl) : ConstantTime isa openX86.pre openX86.pub («open» (VG.Proof.AesOcb.X86.callees v)) := by
  refine CT.constantTime VG.Proof.AesOcb.X86.prmOf (fun _ _ _ _ h => VG.Proof.AesOcb.X86.prmOf_eq h) fun p => ?_
  by_cases hex : ∃ s, openX86.pre s ∧ VG.Proof.AesOcb.X86.prmOf s = p
  swap
  · exact RelCT.of_false fun s _ h => hex ⟨s, h.1⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : VG.Proof.AesOcb.X86.Lay p := hzp ▸ VG.Proof.AesOcb.X86.lay_of (VG.Proof.AesOcb.X86.onePre_open hz)
  unfold «open»
  refine CT.seq (J := VG.Proof.AesOcb.X86.Env p)
    ((VG.Proof.AesOcb.X86.front_ct v false p (.inr rfl) (fun L => VG.Proof.AesOcb.X86.bodyOpen_ct v L) fun L t ⟨E, o0, ck, l0⟩ =>
      WP.mono (VG.Proof.AesOcb.X86.bodyOpen_ok v L E rfl o0 ck l0) fun _ B => B.env).mono fun s ⟨h, hp⟩ => ⟨VG.Proof.AesOcb.X86.onePre_open h, hp⟩)
    (fun s ⟨h, hp⟩ => WP.mono (VG.Proof.AesOcb.X86.openFront_ok v (VG.Proof.AesOcb.X86.onePre_open h) []) fun _ ⟨F, _⟩ => hp ▸ F.env) ?_
  -- The received tag.
  refine CT.seq (J := VG.Proof.AesOcb.X86.Env p) (VG.Proof.AesOcb.X86.recv_ct L) (fun t E => WP.mono (VG.Proof.AesOcb.X86.recv_ok L E) fun t' ⟨m, g, rd, wr⟩ => ?_) ?_
  · have ht := L.tl16
    exact E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr
      (VG.Proof.AesOcb.X86.frame_toMut (rs := [⟨w64 p.W, p.tl⟩]) (by
        rw [m]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _))
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesOcb.X86.wA p.W, by simp, Region.sub_prefix (by omega)⟩)
  -- The comparison.
  refine CT.seq (J := fun t => VG.Proof.AesOcb.X86.Env p t ∧ ∃ c : Bool,
      slotv t.mem p.W okO = if c then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) (VG.Proof.AesOcb.X86.cmp_ct L)
    (fun t E => WP.mono (VG.Proof.AesOcb.X86.cmp_ok L E) fun t' ⟨m, g, rd, wr⟩ => ⟨?_, decide (bytesAt t.mem (w64 p.W) p.tl =
      bytesAt t.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl), by
        rw [slotv_eq, m, Mem.readW_writeW_self32]; simp only [decide_eq_true_eq]⟩) ?_
  · have f : Frame [⟨w64 p.W + BitVec.ofNat 64 okO, 4⟩] t.mem t'.mem := by
      rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    exact E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr
      (VG.Proof.AesOcb.X86.frame_toMut f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  -- The mask, and the result.
  refine CT.seq (J := fun t => t.gpr .ebp = p.W) ((VG.Proof.AesOcb.X86.mask_ct L).mono fun _ h => h.1)
    (fun t ⟨E, c, hok⟩ => WP.mono (VG.Proof.AesOcb.X86.mask_ok L E hok) fun _ ⟨_, g, _⟩ => by
      rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (CT.taint [.ebp] (VG.Proof.AesOcb.X86.pin_ebp fun _ h => h) (by taint_decide))

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Init`. -/
section

/-!
# AES-OCB on x86: `vg_aes_ocb_init`

Untrusted: everything here is checked by Lean. The entry (our caller's
registers saved in `scratch`, the arguments into its slots), the key
schedule (`vg_aes_expand_key_scratch`), then `L_* = ENCIPHER(K, zeros(128))`
(`vg_aes_encrypt_blocks` on a zero block at byte 240 of the key context),
as one `Pc` (`init_pc`): correct (`init_correct`) and constant time
(`init_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem KeyRepr)
open VG.Proof.AesOcb.X86 (zero4_fold)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt restore)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq argA argsR argsR_eq argA_contains argA_sub SavedAt save_ok
  KeepEnv keeps_ok keepR runBlock_app_of in_off below_eq covers_left covers_off covers_cons covers_nil Pc pubOf
  pubOf_arg pubOf_esp pubOf_eq argIn_of arg0_ok ret_kept ret_below ofNat_lit ofNat_toNat32 toNat_add32
  toNat_ofNat32 exit_ok KeyCall KeyPost add_ofNat_assoc32 CT length_bytesAt)

/-- The facts of `init`'s precondition about the public data `p` alone. -/
structure InitPure (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  kc : (⟨w64 (p.2 0), (p.2 1).toNat⟩ : Region).Disjoint ⟨w64 (p.2 2), 256⟩
  kw : (⟨w64 (p.2 0), (p.2 1).toNat⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  cw : (⟨w64 (p.2 2), 256⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  r_c : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 2), 256⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  k_k : (below p.1 24).Disjoint ⟨w64 (p.2 0), (p.2 1).toNat⟩
  k_c : (below p.1 24).Disjoint ⟨w64 (p.2 2), 256⟩
  k_w : (below p.1 24).Disjoint ⟨w64 (p.2 3), 2560⟩
  fk : (p.2 0).toNat + (p.2 1).toNat ≤ 2 ^ 32
  fc : (p.2 2).toNat + 256 ≤ 2 ^ 32
  fw : (p.2 3).toNat + 2560 ≤ 2 ^ 32
  sp : 24 ≤ p.1.toNat
  len : (p.2 1).toNat = 16 ∨ (p.2 1).toNat = 24 ∨ (p.2 1).toNat = 32

theorem initPure_of {p : BitVec 32 × (Nat → BitVec 32)} {s : State} (h : VG.Proof.AesOcb.X86.initPre s) (hp : pubOf 4 s = p) :
    VG.Proof.AesOcb.X86.InitPure p := by
  simp only [VG.Proof.AesOcb.X86.initPre] at h
  obtain ⟨-, -, d_kc, d_kw, -, d_cw, -, -, -, r_c, r_w, -, k_k, k_c, k_w, -, fk, fc, fw, sp, -, hl⟩ := h
  simp only [VG.Proof.AesOcb.X86.keyR, VG.Proof.AesOcb.X86.ictxR, VG.Proof.AesOcb.X86.scrR, VG.Proof.AesOcb.X86.retR, VG.Proof.AesOcb.X86.stackR] at d_kc d_kw d_cw r_c r_w k_k k_c k_w
  rw [show (24 : Addr) = BitVec.ofNat 64 24 from rfl, below_eq sp] at k_k k_c k_w
  have a0 := pubOf_arg hp (i := 0) (by decide); have a1 := pubOf_arg hp (i := 1) (by decide)
  have a2 := pubOf_arg hp (i := 2) (by decide); have a3 := pubOf_arg hp (i := 3) (by decide)
  have e := pubOf_esp hp
  simp only [a0, a1, a2, a3, e] at d_kc d_kw d_cw r_c r_w k_k k_c k_w fk fc fw sp hl
  exact ⟨d_kc, d_kw, d_cw, r_c, r_w, k_k, k_c, k_w, fk, fc, fw, sp, hl⟩

/-- The arguments the entry copies, and where. -/
abbrev initPs : List (Nat × Nat) := [(0, nO), (1, nlO), (2, ctxO)]

theorem initEntry_eq : (entry 3 (VG.Impl.AesGcm.X86.keep 0 nO ++ VG.Impl.AesGcm.X86.keep 1 nlO ++ VG.Impl.AesGcm.X86.keep 2 ctxO) : Prog isa) =
    entry 3 (initPs.flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2)) := rfl

/-- After the entry. -/
structure IEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : VG.Proof.AesOcb.X86.initPre s₀
  pub : pubOf 4 s₀ = p
  ebp : s.gpr .ebp = p.2 3
  esp : s.gpr .esp = p.1
  sK : slotv s.mem (p.2 3) nO = p.2 0
  sL : slotv s.mem (p.2 3) nlO = p.2 1
  sC : slotv s.mem (p.2 3) ctxO = p.2 2
  saved : SavedAt s.mem (p.2 3) s₀
  frame : Frame [⟨w64 (p.2 3) + BitVec.ofNat 64 128, 64⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem iEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => VG.Proof.AesOcb.X86.initPre s₀ ∧ pubOf 4 s₀ = p ∧ s = s₀)
      (entry 3 (VG.Impl.AesGcm.X86.keep 0 nO ++ VG.Impl.AesGcm.X86.keep 1 nlO ++ VG.Impl.AesGcm.X86.keep 2 ctxO)) (VG.Proof.AesOcb.X86.IEnt p) := by
  rw [VG.Proof.AesOcb.X86.initEntry_eq]
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have hc := VG.Proof.AesOcb.X86.initPure_of hpre hpub
    have hp := hpre
    simp only [VG.Proof.AesOcb.X86.initPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, d_wa, -, -, -, -, -, -, -, -, -, -, -, -, fa, -⟩ := hp
    have a : ∀ i, i < 4 → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
    have wW : Covers [⟨w64 (arg s₀ 3), 2560⟩] s₀.wr := by rw [hwr]; exact VG.Proof.AesOcb.X86.covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 4] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact VG.Proof.AesOcb.X86.covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 4).Disjoint ⟨w64 (arg s₀ 3), 2560⟩ := by rw [argsR_eq]; exact d_wa.symm
    have fw : (arg s₀ 3).toNat + 2560 ≤ 2 ^ 32 := by rw [a 3 (by decide)]; exact hc.fw
    have fa' : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by omega
    generalize hSP : s₀.gpr .esp = SP at rA aw fa'
    have i₀ : InRegions (s₀.rd ++ s₀.wr) (argA SP 3) 4 :=
      rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa'⟩
    refine WP.seq (WP.of_runBlock ⟨_, by grun [hSP, i₀], ?_⟩)
    have hax : (s₀.setReg .eax (s₀.mem.readW (argA SP 3) 32)).gpr .eax = arg s₀ 3 := by
      rw [gpr_setReg_self, ← hSP]; rfl
    set t₀ := s₀.setReg .eax (s₀.mem.readW (argA SP 3) 32) with ht₀
    obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := save_ok t₀ hax (by rw [ht₀]; exact wW) fw
    have sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), ht₀, gpr_setReg_of_ne _ _ (by decide), hSP]
    have hA₁ : ∀ i < 4, s₁.mem.readW (argA SP i) 32 = arg s₀ i := fun i hi => by
      rw [f₁.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (aw.sub_left (argA_sub hi fa')).sub_right (Lay.wSub (by decide))) (by decide)]
      rw [arg, argAddr, hSP]
      exact rfl
    have ke : KeepEnv (arg s₀ 3) SP 4 s₁ := ⟨bp₁, sp₁, by rw [wr₁]; exact wW, by rw [rd₁, wr₁]; exact rA, aw, fa', fw⟩
    obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := keeps_ok VG.Proof.AesOcb.X86.initPs (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide) (by decide) ke
    refine WP.of_runBlock ⟨_, runBlock_app_of run₁ run₃, ?_⟩
    have f₃' : Frame [⟨w64 (arg s₀ 3) + BitVec.ofNat 64 128, 64⟩] s₀.mem s₃.mem := by
      refine (f₁.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
      · simp only [List.mem_map] at hr
        obtain ⟨q, hq, rfl⟩ := hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    have hsv : SavedAt s₃.mem (arg s₀ 3) s₀ := by
      have := sv₁.frame f₃ fun r hr => by
        simp only [List.mem_map] at hr
        obtain ⟨q, hq, rfl⟩ := hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      obtain ⟨a, b, c, d⟩ := this
      refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_⟩ <;>
        simp only [ht₀, gpr_setReg_of_ne _ _ (by decide : Reg.ebx ≠ .eax),
          gpr_setReg_of_ne _ _ (by decide : Reg.esi ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.edi ≠ .eax),
          gpr_setReg_of_ne _ _ (by decide : Reg.ebp ≠ .eax)]
    have sl : ∀ q ∈ VG.Proof.AesOcb.X86.initPs, slotv s₃.mem (arg s₀ 3) q.2 = p.2 q.1 := fun q hq => by
      have e := sl₃ q hq
      have hq1 : q.1 < 4 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> decide
      rw [hA₁ q.1 hq1, a q.1 hq1] at e
      exact e
    rw [a 3 (by decide)] at f₃' hsv sl
    exact ⟨hpre, hpub, by rw [g₃ _ (by decide), bp₁, a 3 (by decide)],
      by rw [g₃ _ (by decide), sp₁, ← hSP]; exact pubOf_esp hpub, sl (0, nO) (by simp), sl (1, nlO) (by simp),
      sl (2, ctxO) (by simp), hsv, f₃', by rw [rd₃, rd₁]; rfl, by rw [wr₃, wr₁]; rfl⟩
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 3 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [pubOf_esp h₁, pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    subst s
    have hp := hpre
    simp only [VG.Proof.AesOcb.X86.initPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fa, -⟩ := hp
    have rA : Covers [argsR (s₀.gpr .esp) 4] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact VG.Proof.AesOcb.X86.covers_of_mem (by simp)
    exact WP.mono (arg0_ok (argIn_of rA (by omega) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubOf_arg hpub (by decide), by rw [sp]; exact pubOf_esp hpub⟩

theorem shr2_32 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 2 = BitVec.ofNat 32 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- `W` and the key context apart, at offsets. -/
theorem InitPure.cw' {p : BitVec 32 × (Nat → BitVec 32)} (h : VG.Proof.AesOcb.X86.InitPure p) {a n d k : Nat} (ha : a + n ≤ 256)
    (hd : d + k ≤ 2560) :
    (⟨w64 (p.2 2) + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 (p.2 3) + BitVec.ofNat 64 d, k⟩ :=
  (h.cw.sub_left (Offset.sub_base _ ha)).sub_right (Lay.wSub hd)

/-- The arguments of `vg_aes_expand_key_scratch`. -/
abbrev iArgs : List Instr :=
  [.mov .eax (slot nO), .mov .ecx (slot nlO), .mov .edx (slot ctxO), .alu .add .ebp (imm scrO)]

/-- After `iArgs`: the call of `vg_aes_expand_key_scratch`. -/
structure IArg (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : VG.Proof.AesOcb.X86.initPre s₀
  pub : pubOf 4 s₀ = p
  call : KeyCall s (p.2 0) (p.2 2) (p.2 3 + BitVec.ofNat 32 512) (p.2 1).toNat
  esp : s.gpr .esp = p.1
  sL : slotv s.mem (p.2 3) nlO = p.2 1
  sC : slotv s.mem (p.2 3) ctxO = p.2 2
  saved : SavedAt s.mem (p.2 3) s₀
  frame : Frame [⟨w64 (p.2 3) + BitVec.ofNat 64 128, 64⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What the precondition lets `init` read and write. -/
theorem init_perm {p : BitVec 32 × (Nat → BitVec 32)} {s₀ : State} (hpre : VG.Proof.AesOcb.X86.initPre s₀) (hpub : pubOf 4 s₀ = p) :
    s₀.rd = [⟨w64 (p.2 0), (p.2 1).toNat⟩] ∧
      s₀.wr = [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩] := by
  have hp := hpre
  simp only [VG.Proof.AesOcb.X86.initPre] at hp
  rw [hp.1, hp.2.1]
  simp only [VG.Proof.AesOcb.X86.keyR, VG.Proof.AesOcb.X86.ictxR, VG.Proof.AesOcb.X86.scrR, VG.Proof.AesOcb.X86.iargsR, pubOf_arg hpub (i := 0) (by decide), pubOf_arg hpub (i := 1) (by decide),
    pubOf_arg hpub (i := 2) (by decide), pubOf_arg hpub (i := 3) (by decide), and_self]

theorem iArgs_pc (p : BitVec 32 × (Nat → BitVec 32)) : Pc (VG.Proof.AesOcb.X86.IEnt p) (.block VG.Proof.AesOcb.X86.iArgs) (VG.Proof.AesOcb.X86.IArg p) := by
  refine Pc.taint [.ebp] (fun s₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ebp, h₂.ebp]) (by taint_decide)
  have hc := VG.Proof.AesOcb.X86.initPure_of h.pre h.pub
  obtain ⟨hrd, hwr⟩ := VG.Proof.AesOcb.X86.init_perm h.pre h.pub
  have wW : Covers [⟨w64 (p.2 3), 2560⟩] s.wr := by rw [h.wr, hwr]; exact VG.Proof.AesOcb.X86.covers_of_mem (by simp)
  have wC : Covers [⟨w64 (p.2 2), 256⟩] s.wr := by rw [h.wr, hwr]; exact VG.Proof.AesOcb.X86.covers_of_mem (by simp)
  have aW : ∀ {o}, o < 2560 → w64 (p.2 3 + BitVec.ofNat 32 o) = w64 (p.2 3) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by have := hc.fw; omega)
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 (p.2 3) + BitVec.ofNat 64 o) 4 :=
    fun ho => Proof.AesGcm.X86.in_left (in_off wW ho (by decide))
  have sK := h.sK
  have sL := h.sL
  have sC := h.sC
  simp only [slotv_eq] at sK sL sC
  have eS := w64_add (x := p.2 3) (k := 512) (by have := hc.fw; omega)
  have bsub : Region.Sub (below p.1 20) (below p.1 24) := VG.X86.below_sub (by decide) hc.sp
  refine WP.of_runBlock ⟨_, by grun [h.ebp, aW, rIn, sK, sL, sC], ?_⟩
  refine ⟨h.pre, h.pub, ⟨by gregs [sK], by gregs [sL]; exact (ofNat_toNat32 _).symm, by gregs [sC],
    by gregs [h.ebp], hc.len, by gregs [h.esp]; have := hc.sp; omega,
    hc.kc.sub_right (Region.sub_prefix (by decide)), by rw [eS]; exact hc.kw.sub_right (Lay.wSub (by decide)),
    by rw [eS]; exact (hc.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)),
    by gregs [h.esp]; exact hc.k_k.sub_left bsub,
    by gregs [h.esp]; exact (hc.k_c.sub_left bsub).sub_right (Region.sub_prefix (by decide)),
    by gregs [h.esp]; rw [eS]; exact (hc.k_w.sub_left bsub).sub_right (Lay.wSub (by decide)),
    hc.fk, by have := hc.fc; omega, by rw [toNat_add32 (by have := hc.fw; omega)]; have := hc.fw; omega,
    by gmems [h.rd, h.wr, hrd]; exact VG.Proof.AesOcb.X86.covers_of_mem (by simp), ?_⟩, by gregs [h.esp], by gmems []; exact h.sL,
    by gmems []; exact h.sC, by gmems []; exact h.saved, by gmems []; exact h.frame, by gmems [h.rd],
    by gmems [h.wr]⟩
  rw [eS]
  gmems [h.wr, hwr]
  have c₁ : Covers [⟨w64 (p.2 2), 240⟩] [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩] := by
    have := covers_off (p := w64 (p.2 2)) (k := 256) (d := 0) (n := 240)
      (rs := [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩]) (VG.Proof.AesOcb.X86.covers_of_mem (by simp)) (by decide)
      (by decide)
    simpa using this
  exact covers_cons c₁ (covers_cons (covers_off (p := w64 (p.2 3)) (k := 2560) (d := 512) (n := 512)
    (VG.Proof.AesOcb.X86.covers_of_mem (by simp)) (by decide) (by decide)) covers_nil)

/-- After the key schedule: `0` into bytes 240–255 of the key context. -/
abbrev mid1 : List Instr :=
  [.alu .sub .ebp (imm scrO), .mov .edx (slot ctxO), .mov .eax (imm 0), .store (at_ .edx 240) .eax,
    .store (at_ .edx 244) .eax, .store (at_ .edx 248) .eax, .store (at_ .edx 252) .eax]

/-- The arguments of `vg_aes_encrypt_blocks` for `L_*`. -/
abbrev mid2 : List Instr :=
  [.mov .eax (.reg .edx), .mov .ecx (slot nlO), .shift .shr .ecx 2, .alu .add .ecx (imm 6),
    .alu .add .edx (imm 240), .mov .ebx (imm 1), .alu .add .ebp (imm scrO)]

/-- After `mid1 ++ mid2`: the call of `vg_aes_encrypt_blocks` on the block at byte 240. -/
structure IMid (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : VG.Proof.AesOcb.X86.initPre s₀
  pub : pubOf 4 s₀ = p
  call : VG.Proof.AesOcb.X86.BCall s (p.2 2) (p.2 2 + BitVec.ofNat 32 240) (p.2 3 + BitVec.ofNat 32 512) ((p.2 1).toNat / 4 + 6) 1
  esp : s.gpr .esp = p.1
  sched : bytesAt s.mem (w64 (p.2 2)) (16 * ((p.2 1).toNat / 4 + 6 + 1)) =
    Spec.Aes.expandKey (bytesAt s₀.mem (w64 (p.2 0)) (p.2 1).toNat)
  zero : blockAtMem s.mem (w64 (p.2 2) + BitVec.ofNat 64 240) = 0
  saved : SavedAt s.mem (p.2 3) s₀
  frame : Frame [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, below p.1 24] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem rounds_of_len {L : Nat} (h : L = 16 ∨ L = 24 ∨ L = 32) : L / 4 + 6 = 10 ∨ L / 4 + 6 = 12 ∨ L / 4 + 6 = 14 := by
  rcases h with rfl | rfl | rfl <;> decide

theorem iMid_ok {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ s : State} (h : VG.Proof.AesOcb.X86.IArg p s₀ s₁)
    (g : KeyPost s₁ (p.2 0) (p.2 2) (p.2 3 + BitVec.ofNat 32 512) (p.2 1).toNat s) :
    WP isa (.block (VG.Proof.AesOcb.X86.mid1 ++ VG.Proof.AesOcb.X86.mid2)) s (VG.Proof.AesOcb.X86.IMid p s₀) := by
  have hc := VG.Proof.AesOcb.X86.initPure_of h.pre h.pub
  obtain ⟨hrd, hwr⟩ := VG.Proof.AesOcb.X86.init_perm h.pre h.pub
  have hfw := hc.fw
  have hfc := hc.fc
  have hsp := hc.sp
  have eS := w64_add (x := p.2 3) (k := 512) (by omega)
  have eH := w64_add (x := p.2 2) (k := 240) (by omega)
  have bp : s.gpr .ebp = p.2 3 + BitVec.ofNat 32 512 := by rw [g.saved .ebp (by decide), h.call.ebp]
  have sp : s.gpr .esp = p.1 := by rw [g.saved .esp (by decide), h.esp]
  have hb0 : p.2 3 + BitVec.ofNat 32 512 - BitVec.ofNat 32 512 = p.2 3 := BitVec.add_sub_cancel _ _
  have bsub : Region.Sub (below p.1 20) (below p.1 24) := VG.X86.below_sub (by decide) hsp
  have gf := g.frame
  rw [h.esp, eS] at gf
  -- What the key call keeps: the slots, the saved registers.
  have dG : ∀ {d k : Nat}, (128 ≤ d ∧ d + k ≤ 512) → ∀ r ∈ [(⟨w64 (p.2 2), 240⟩ : Region),
      ⟨w64 (p.2 3) + BitVec.ofNat 64 512, 512⟩, below p.1 20],
      (⟨w64 (p.2 3) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun {d k} hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hc.cw.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Lay.wSub (d := d) (n := k) (by omega))
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact ((hc.k_w.sub_left bsub).sub_right (Lay.wSub (by omega))).symm
  have sC := h.sC
  have sL := h.sL
  rw [slotv_eq, ← gf.readW (Region.contains_self _ _) (dG ⟨by decide, by decide⟩) (by decide)] at sC sL
  have wW : Covers [⟨w64 (p.2 3), 2560⟩] s.wr := by rw [g.wr, h.wr, hwr]; exact VG.Proof.AesOcb.X86.covers_of_mem (by simp)
  have wC : Covers [⟨w64 (p.2 2), 256⟩] s.wr := by rw [g.wr, h.wr, hwr]; exact VG.Proof.AesOcb.X86.covers_of_mem (by simp)
  have aW : ∀ {o}, o < 2560 → w64 (p.2 3 + BitVec.ofNat 32 o) = w64 (p.2 3) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by omega)
  have aC : ∀ {o}, o < 256 → w64 (p.2 2 + BitVec.ofNat 32 o) = w64 (p.2 2) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by omega)
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 (p.2 3) + BitVec.ofNat 64 o) 4 :=
    fun ho => Proof.AesGcm.X86.in_left (in_off wW ho (by decide))
  have cIn : ∀ {o}, o + 4 ≤ 256 → InRegions s.wr (w64 (p.2 2) + BitVec.ofNat 64 o) 4 :=
    fun ho => in_off wC ho (by decide)
  -- `mid1`.
  obtain ⟨t, run₁, m₁, bp₁, dx₁, g₁, rd₁, wr₁⟩ : ∃ t, runBlock isa VG.Proof.AesOcb.X86.mid1 s = some t ∧
      t.mem = Proof.Cmac.zero4 s.mem (w64 (p.2 2) + BitVec.ofNat 64 240) ∧ t.gpr .ebp = p.2 3 ∧
      t.gpr .edx = p.2 2 ∧ (∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebp → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr :=
    ⟨_, by grun [bp, hb0, aW, rIn, sC, aC, cIn], by gmems []; exact VG.Proof.AesOcb.X86.zero4_fold _ _ _, by gregs [bp, hb0],
      by gregs [sC], fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  have f₁ : Frame [⟨w64 (p.2 2) + BitVec.ofNat 64 240, 16⟩] s.mem t.mem := by
    rw [m₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have sL₁ : t.mem.readW (w64 (p.2 3) + BitVec.ofNat 64 nlO) 32 = p.2 1 := by
    rw [f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hc.cw' (by decide) (by decide)).symm) (by decide)]
    exact sL
  have hL : (p.2 1).toNat < 2 ^ 32 := (p.2 1).isLt
  have hsh : p.2 1 >>> 2 + BitVec.ofNat 32 6 = BitVec.ofNat 32 ((p.2 1).toNat / 4 + 6) := by
    rw [← ofNat_toNat32 (p.2 1), VG.Proof.AesOcb.X86.shr2_32 hL, Proof.AesGcm.X86.ofNat_add_ofNat32, toNat_ofNat32 hL]
  have rIn₁ : ∀ {o}, o + 4 ≤ 2560 → InRegions (t.rd ++ t.wr) (w64 (p.2 3) + BitVec.ofNat 64 o) 4 := fun ho => by
    rw [rd₁, wr₁]; exact rIn ho
  -- `mid2`.
  obtain ⟨u, run₂, m₂, ax₂, cx₂, dx₂, bx₂, bp₂, g₂, rd₂, wr₂⟩ : ∃ u, runBlock isa VG.Proof.AesOcb.X86.mid2 t = some u ∧
      u.mem = t.mem ∧ u.gpr .eax = p.2 2 ∧ u.gpr .ecx = BitVec.ofNat 32 ((p.2 1).toNat / 4 + 6) ∧
      u.gpr .edx = p.2 2 + BitVec.ofNat 32 240 ∧ u.gpr .ebx = BitVec.ofNat 32 1 ∧
      u.gpr .ebp = p.2 3 + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebx → r ≠ .ebp → u.gpr r = t.gpr r) ∧ u.rd = t.rd ∧
      u.wr = t.wr :=
    ⟨_, by grun [bp₁, aW, rIn₁, sL₁, dx₁], by gmems [], by gregs [dx₁], by gregs [sL₁, hsh], by gregs [dx₁],
      by gregs [], by gregs [bp₁], fun r h₁ h₂ h₃ h₄ h₅ => by gregs [h₁, h₂, h₃, h₄, h₅], by gmems [], by gmems []⟩
  refine WP.of_runBlock ⟨u, runBlock_app_of run₁ run₂, ?_⟩
  have spU : u.gpr .esp = p.1 := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide), sp]
  have hR := VG.Proof.AesOcb.X86.rounds_of_len hc.len
  have hRb : 16 * ((p.2 1).toNat / 4 + 6 + 1) ≤ 240 := by rcases hR with h' | h' | h' <;> omega
  have go := g.out
  rw [Proof.AesGcm.X86.bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hc.kw.sub_right (Lay.wSub (by decide)))
    (by have := hc.fk; omega)] at go
  have hrw : u.wr = s₀.wr := by rw [wr₂, wr₁, g.wr, h.wr]
  have hrd' : u.rd = s₀.rd := by rw [rd₂, rd₁, g.rd, h.rd]
  have kd : (⟨w64 (p.2 2), 240⟩ : Region).Disjoint ⟨w64 (p.2 2 + BitVec.ofNat 32 240), 16 * 1⟩ := by
    rw [eH]
    have := Offset.disjoint (w64 (p.2 2)) (d := 0) (n := 240) (e := 240) (k := 16 * 1) (.inl (by omega)) (by omega)
      (by omega)
    simpa using this
  have uW : Covers [⟨w64 (p.2 3), 2560⟩] u.wr := by rw [hrw, hwr]; exact VG.Proof.AesOcb.X86.covers_of_mem (by simp)
  have uC : Covers [⟨w64 (p.2 2), 256⟩] u.wr := by rw [hrw, hwr]; exact VG.Proof.AesOcb.X86.covers_of_mem (by simp)
  have rC : Covers [⟨w64 (p.2 2), 240⟩] (u.rd ++ u.wr) := by
    have := covers_off (p := w64 (p.2 2)) (k := 256) (d := 0) (n := 240) (rs := u.wr) uC (by decide) (by decide)
    exact covers_left (by simpa using this)
  have wB : Covers [⟨w64 (p.2 2 + BitVec.ofNat 32 240), 16 * 1⟩, ⟨w64 (p.2 3 + BitVec.ofNat 32 512), 2048⟩] u.wr := by
    rw [eH, eS]
    exact covers_cons (covers_off uC (by decide) (by decide)) (covers_cons (covers_off uW (by decide) (by decide))
      covers_nil)
  refine ⟨h.pre, h.pub, ⟨ax₂, cx₂, dx₂, bx₂, bp₂, hR, by rw [spU]; exact hsp, kd,
    by rw [eS]; exact (hc.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)),
    by rw [eH, eS]; exact hc.cw' (by decide) (by decide),
    by rw [spU]; exact hc.k_c.sub_right (Region.sub_prefix (by decide)),
    by rw [spU, eH]; exact hc.k_c.sub_right (Offset.sub_base _ (by decide)),
    by rw [spU, eS]; exact hc.k_w.sub_right (Lay.wSub (by decide)),
    by omega, by rw [Proof.AesGcm.X86.toNat_add32 (by omega)]; omega,
    by rw [Proof.AesGcm.X86.toNat_add32 (by omega)]; omega, rC, wB⟩, spU, ?_, ?_, ?_, ?_, hrd', hrw⟩
  · have dZ : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 240, 16⟩ : Region)],
        (⟨w64 (p.2 2), 16 * ((p.2 1).toNat / 4 + 6 + 1)⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := Offset.disjoint (w64 (p.2 2)) (d := 0) (n := 16 * ((p.2 1).toNat / 4 + 6 + 1)) (e := 240) (k := 16)
        (.inl (by omega)) (by omega) (by omega)
      simpa using this
    rw [m₂, Proof.AesGcm.X86.bytesAt_frame f₁ dZ (by omega)]
    exact go
  · rw [m₂, m₁]; exact VG.Proof.AesOcb.X86.blockAtMem_zero4 _ _
  · rw [m₂]
    exact (h.saved.frame gf (dG ⟨by decide, by decide⟩)).frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hc.cw' (by decide) (by decide)).symm
  · rw [m₂]
    refine ((h.frame.sub fun r hr => ?_).trans (gf.sub fun r hr => ?_)).trans (f₁.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
      · exact ⟨_, by simp, bsub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩

/-- The first two instructions of `mid1`: `ebp` back to `W`, the key context
into `edx`. -/
theorem mid0_ok {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ s : State} (h : VG.Proof.AesOcb.X86.IArg p s₀ s₁)
    (g : KeyPost s₁ (p.2 0) (p.2 2) (p.2 3 + BitVec.ofNat 32 512) (p.2 1).toNat s) :
    WP isa (.block [.alu .sub .ebp (imm scrO), .mov .edx (slot ctxO)]) s
      fun t => t.gpr .ebp = p.2 3 ∧ t.gpr .edx = p.2 2 := by
  have hc := VG.Proof.AesOcb.X86.initPure_of h.pre h.pub
  obtain ⟨-, hwr⟩ := VG.Proof.AesOcb.X86.init_perm h.pre h.pub
  have hfw := hc.fw
  have eS := w64_add (x := p.2 3) (k := 512) (by omega)
  have bp : s.gpr .ebp = p.2 3 + BitVec.ofNat 32 512 := by rw [g.saved .ebp (by decide), h.call.ebp]
  have hb0 : p.2 3 + BitVec.ofNat 32 512 - BitVec.ofNat 32 512 = p.2 3 := BitVec.add_sub_cancel _ _
  have bsub : Region.Sub (below p.1 20) (below p.1 24) := VG.X86.below_sub (by decide) hc.sp
  have gf := g.frame
  rw [h.esp, eS] at gf
  have sC := h.sC
  rw [slotv_eq, ← gf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hc.cw.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Lay.wSub (by decide))
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact ((hc.k_w.sub_left bsub).sub_right (Lay.wSub (by decide))).symm) (by decide)] at sC
  have wW : Covers [⟨w64 (p.2 3), 2560⟩] s.wr := by rw [g.wr, h.wr, hwr]; exact VG.Proof.AesOcb.X86.covers_of_mem (by simp)
  have aW : ∀ {o}, o < 2560 → w64 (p.2 3 + BitVec.ofNat 32 o) = w64 (p.2 3) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by omega)
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 (p.2 3) + BitVec.ofNat 64 o) 4 :=
    fun ho => Proof.AesGcm.X86.in_left (in_off wW ho (by decide))
  exact WP.of_runBlock ⟨_, by grun [bp, hb0, aW, rIn, sC], by gregs [bp, hb0], by gregs [sC]⟩

theorem iMid_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun s₀ s' => ∃ s, VG.Proof.AesOcb.X86.IArg p s₀ s ∧ KeyPost s (p.2 0) (p.2 2) (p.2 3 + BitVec.ofNat 32 512) (p.2 1).toNat s')
      (.block (VG.Proof.AesOcb.X86.mid1 ++ VG.Proof.AesOcb.X86.mid2)) (VG.Proof.AesOcb.X86.IMid p) := by
  refine ⟨fun s₀ s ⟨s₁, h, g⟩ => VG.Proof.AesOcb.X86.iMid_ok h g, ?_⟩
  rw [show VG.Proof.AesOcb.X86.mid1 ++ VG.Proof.AesOcb.X86.mid2 = [.alu .sub .ebp (imm scrO), .mov .edx (slot ctxO)] ++
    ([.mov .eax (imm 0), .store (at_ .edx 240) .eax, .store (at_ .edx 244) .eax, .store (at_ .edx 248) .eax,
      .store (at_ .edx 252) .eax] ++ VG.Proof.AesOcb.X86.mid2) from rfl]
  refine RelCT.block_append (CT.seq (J := fun s => s.gpr .ebp = p.2 3 ∧ s.gpr .edx = p.2 2)
    (CT.taint [.ebp] (fun s₁ s₂ ⟨_, _, h₁, g₁⟩ ⟨_, _, h₂, g₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [g₁.saved .ebp (by decide), g₂.saved .ebp (by decide), h₁.call.ebp, h₂.call.ebp]) (by taint_decide))
    (fun s ⟨_, _, h, g⟩ => VG.Proof.AesOcb.X86.mid0_ok h g)
    (CT.taint [.ebp, .edx] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2, h₂.2]) (by taint_decide)))

theorem init_eq (v : BlocksImpl) : init (VG.Proof.AesOcb.X86.callees v) = .seq (entry 3 (VG.Impl.AesGcm.X86.keep 0 nO ++ VG.Impl.AesGcm.X86.keep 1 nlO ++ VG.Impl.AesGcm.X86.keep 2 ctxO))
    (.seq (.block VG.Proof.AesOcb.X86.iArgs) (.seq (keyFrame (VG.Proof.AesOcb.X86.callees v)) (.seq (.block (VG.Proof.AesOcb.X86.mid1 ++ VG.Proof.AesOcb.X86.mid2))
      (.seq (blocksFrame (VG.Proof.AesOcb.X86.callees v).enc) (.block (([.alu .sub .ebp (imm scrO)] : List Instr) ++ restore)))))) := rfl

theorem init_pc (v : BlocksImpl) (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => VG.Proof.AesOcb.X86.initPre s₀ ∧ pubOf 4 s₀ = p ∧ s = s₀) (init (VG.Proof.AesOcb.X86.callees v))
      (fun s₀ s' => abiPreserved s₀ s' ∧ initX86.post s₀ s') := by
  rw [VG.Proof.AesOcb.X86.init_eq]
  refine Pc.seq (VG.Proof.AesOcb.X86.iEntry_pc p) (Pc.seq (VG.Proof.AesOcb.X86.iArgs_pc p) ?_)
  refine Pc.seq (Pc.of (I := fun s => KeyCall s (p.2 0) (p.2 2) (p.2 3 + BitVec.ofNat 32 512) (p.2 1).toNat ∧
    s.gpr .esp = p.1) (fun s h => VG.Proof.AesOcb.X86.key_ok v h.1) (VG.Proof.AesOcb.X86.key_ct v fun s h => h) _ fun _ _ h => ⟨h.call, h.esp⟩) ?_
  refine Pc.seq (VG.Proof.AesOcb.X86.iMid_pc p) ?_
  refine Pc.seq (Pc.of (I := fun s => VG.Proof.AesOcb.X86.BCall s (p.2 2) (p.2 2 + BitVec.ofNat 32 240) (p.2 3 + BitVec.ofNat 32 512)
    ((p.2 1).toNat / 4 + 6) 1 ∧ s.gpr .esp = p.1) (fun s h => VG.Proof.AesOcb.X86.blk_call v.encOk v.encNosp v.encStack h.1)
    (VG.Proof.AesOcb.X86.blk_ct v.encOk v.encCt fun s h => h) _ fun _ _ h => ⟨h.call, h.esp⟩) ?_
  refine Pc.taint [.ebp] (fun s₀ s' ⟨s, hm, g⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, h₁, g₁⟩ ⟨_, h₂, g₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [g₁.saved .ebp (by decide), g₂.saved .ebp (by decide), h₁.call.ebp, h₂.call.ebp]) (by taint_decide)
  have hc := VG.Proof.AesOcb.X86.initPure_of hm.pre hm.pub
  obtain ⟨-, hwr⟩ := VG.Proof.AesOcb.X86.init_perm hm.pre hm.pub
  have hfw := hc.fw
  have hfc := hc.fc
  have hsp := hc.sp
  have eS := w64_add (x := p.2 3) (k := 512) (by omega)
  have eH := w64_add (x := p.2 2) (k := 240) (by omega)
  have bp : s'.gpr .ebp = p.2 3 + BitVec.ofNat 32 512 := by rw [g.saved .ebp (by decide), hm.call.ebp]
  have hb0 : p.2 3 + BitVec.ofNat 32 512 - BitVec.ofNat 32 512 = p.2 3 := BitVec.add_sub_cancel _ _
  have gf := g.frame
  rw [hm.esp, eH, eS] at gf
  have hR := VG.Proof.AesOcb.X86.rounds_of_len hc.len
  have hRb : 16 * ((p.2 1).toNat / 4 + 6 + 1) ≤ 240 := by rcases hR with h' | h' | h' <;> omega
  have hsv : SavedAt s'.mem (p.2 3) s₀ := hm.saved.frame gf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hc.cw' (by decide) (by decide)).symm
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact ((hc.k_w.sub_right (Lay.wSub (by decide)))).symm
  have rG : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 240, 16 * 1⟩ : Region),
      ⟨w64 (p.2 3) + BitVec.ofNat 64 512, 2048⟩, below p.1 24], (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hc.r_c.sub_right (Offset.sub_base _ (by decide))
    · exact hc.r_w.sub_right (Lay.wSub (by decide))
    · exact ret_below hsp
  have rF : ∀ r ∈ [(⟨w64 (p.2 2), 256⟩ : Region), ⟨w64 (p.2 3), 2560⟩, below p.1 24],
      (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hc.r_c
    · exact hc.r_w
    · exact ret_below hsp
  have hret : s'.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [pubOf_esp hm.pub, ret_kept gf rG, ret_kept hm.frame rF]
  have wW : Covers [⟨w64 (p.2 3), 2560⟩] s'.wr := by rw [g.wr, hm.wr, hwr]; exact VG.Proof.AesOcb.X86.covers_of_mem (by simp)
  refine WP.block_append (WP.of_runBlock ⟨_, by grun [bp, hb0], ?_⟩)
  refine WP.mono (exit_ok (W := p.2 3) (by gregs [bp, hb0])
    (by gregs [g.saved .esp (by decide), hm.esp, pubOf_esp hm.pub]) (by gmems []; exact covers_left wW) hc.fw
    (by gmems []; exact hsv) (by gmems []; exact hret)) fun s'' ⟨abi, m'', _, _, _⟩ => ⟨abi, ?_⟩
  have hA : ∀ i, i < 4 → arg s₀ i = p.2 i := fun i hi => pubOf_arg hm.pub hi
  show KeyRepr s''.mem _ _
  rw [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide), m'']
  simp only [mem_setReg, mem_arithFlags]
  have hlen := length_bytesAt s₀.mem (w64 (p.2 0)) (p.2 1).toNat
  have hs : bytesAt s'.mem (w64 (p.2 2)) (16 * ((p.2 1).toNat / 4 + 6 + 1)) =
      Spec.Aes.expandKey (bytesAt s₀.mem (w64 (p.2 0)) (p.2 1).toNat) := by
    rw [Proof.AesGcm.X86.bytesAt_frame gf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · have := Offset.disjoint (w64 (p.2 2)) (d := 0) (n := 16 * ((p.2 1).toNat / 4 + 6 + 1)) (e := 240)
          (k := 16 * 1) (.inl (by omega)) (by omega) (by omega)
        simpa using this
      · exact (hc.cw.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))
      · exact (hc.k_c.sub_right (Region.sub_prefix (by omega))).symm) (by omega)]
    exact hm.sched
  refine ⟨by rw [hlen]; exact hs, ?_⟩
  have e : blockAtMem s'.mem (w64 (p.2 2 + BitVec.ofNat 32 240) + BitVec.ofNat 64 (16 * 0)) =
      Spec.Ocb.ctxCiph s.mem (w64 (p.2 2)) ((p.2 1).toNat / 4 + 6)
        (blockAtMem s.mem (w64 (p.2 2 + BitVec.ofNat 32 240) + BitVec.ofNat 64 (16 * 0))) :=
    Proof.Ocb.blockAtMem_of_state _ (Proof.Ocb.stateAt_of_statesAt g.out (by decide))
  rw [eH, show 16 * 0 = 0 from rfl, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero,
    hm.zero] at e
  show blockAtMem s'.mem (w64 (p.2 2) + BitVec.ofNat 64 240) = _
  rw [e, Spec.Ocb.ctxCiph, hm.sched]
  simp only [Spec.Ocb.aes, hlen, Spec.Aes.rounds]

theorem init_correct (v : BlocksImpl) (s : State) (hs : initX86.pre s) :
    ∃ t s', Exec isa (init (VG.Proof.AesOcb.X86.callees v)) s t s' ∧ abiPreserved s s' ∧ initX86.post s s' :=
  ((VG.Proof.AesOcb.X86.init_pc v (pubOf 4 s)).wp s s ⟨hs, rfl, rfl⟩)

theorem init_ct (v : BlocksImpl) : ConstantTime isa initX86.pre initX86.pub (init (VG.Proof.AesOcb.X86.callees v)) :=
  Pc.constantTime (pubOf 4) (fun _ _ _ _ h => pubOf_eq h) (VG.Proof.AesOcb.X86.init_pc v) fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Verified`. -/
section

/-!
# AES-OCB on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness (`seal_wp`,
`open_wp`, `init_correct`) and constant time (`seal_ct`, `open_ct`,
`init_ct`) for any implementations `v` of `vg_aes_encrypt_blocks`,
`vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch`, a state satisfying each
precondition, and the shared contracts with the working space as a last
argument (`Proof/AesOcb/Scratch.lean`), with 24 bytes of stack: the
arguments and return address of the calls, whose callees use no stack.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.Impl.AesOcb.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem seal_correct (v : BlocksImpl) (s : State) (hs : sealX86.pre s) :
    ∃ t s', Exec isa («seal» (VG.Proof.AesOcb.X86.callees v)) s t s' ∧ abiPreserved s s' ∧ sealX86.post s s' :=
  VG.Proof.AesOcb.X86.seal_wp v hs

theorem open_correct (v : BlocksImpl) (s : State) (hs : openX86.pre s) :
    ∃ t s', Exec isa («open» (VG.Proof.AesOcb.X86.callees v)) s t s' ∧ abiPreserved s s' ∧ openX86.post s s' :=
  VG.Proof.AesOcb.X86.open_wp v hs

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: the key
context at `0x1000`, 10 rounds, a 7-byte nonce at `0x2000`, no associated
data (at `0x2100`), no data (at `0x3000`), a 4-byte tag at `0x4000` and
`work` at `0x5000`, as stack arguments at `0x8004`. -/
def sealSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8010 then 7 else if a = 0x8015 then 0x21 else if a = 0x801d then 0x30
    else if a = 0x8025 then 0x40 else if a = 0x8028 then 4 else if a = 0x802d then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 4⟩, ⟨0x5000, 2560⟩, ⟨0x8004, 44⟩]

/-- As `sealSat`, with the tag read only. -/
def openSat : State :=
  { VG.Proof.AesOcb.X86.sealSat with
                 rd := [⟨0x1000, 256⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x4000, 4⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x5000, 2560⟩, ⟨0x8004, 44⟩] }

theorem sealSat_args : arg VG.Proof.AesOcb.X86.sealSat 0 = 0x1000 ∧ arg VG.Proof.AesOcb.X86.sealSat 1 = 10 ∧ arg VG.Proof.AesOcb.X86.sealSat 2 = 0x2000 ∧ arg VG.Proof.AesOcb.X86.sealSat 3 = 7 ∧
    arg VG.Proof.AesOcb.X86.sealSat 4 = 0x2100 ∧ arg VG.Proof.AesOcb.X86.sealSat 5 = 0 ∧ arg VG.Proof.AesOcb.X86.sealSat 6 = 0x3000 ∧ arg VG.Proof.AesOcb.X86.sealSat 7 = 0 ∧
    arg VG.Proof.AesOcb.X86.sealSat 8 = 0x4000 ∧ arg VG.Proof.AesOcb.X86.sealSat 9 = 4 ∧ arg VG.Proof.AesOcb.X86.sealSat 10 = 0x5000 ∧ argAddr VG.Proof.AesOcb.X86.sealSat 0 = 0x8004 := by
  decide

theorem openSat_args : arg VG.Proof.AesOcb.X86.openSat 0 = 0x1000 ∧ arg VG.Proof.AesOcb.X86.openSat 1 = 10 ∧ arg VG.Proof.AesOcb.X86.openSat 2 = 0x2000 ∧ arg VG.Proof.AesOcb.X86.openSat 3 = 7 ∧
    arg VG.Proof.AesOcb.X86.openSat 4 = 0x2100 ∧ arg VG.Proof.AesOcb.X86.openSat 5 = 0 ∧ arg VG.Proof.AesOcb.X86.openSat 6 = 0x3000 ∧ arg VG.Proof.AesOcb.X86.openSat 7 = 0 ∧
    arg VG.Proof.AesOcb.X86.openSat 8 = 0x4000 ∧ arg VG.Proof.AesOcb.X86.openSat 9 = 4 ∧ arg VG.Proof.AesOcb.X86.openSat 10 = 0x5000 ∧ argAddr VG.Proof.AesOcb.X86.openSat 0 = 0x8004 :=
  VG.Proof.AesOcb.X86.sealSat_args

theorem seal_verified (v : BlocksImpl) :
    Verified X86.target («seal» (VG.Proof.AesOcb.X86.callees v)) (Proof.AesOcb.sealScratchContract X86.abi 24) :=
  Verified.of_correct (VG.Proof.AesOcb.X86.seal_correct v) (VG.Proof.AesOcb.X86.seal_ct v) (by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e⟩ := VG.Proof.AesOcb.X86.sealSat_args
    have esp : sealSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Spec.Ocb.sealPost, VG.Proof.AesOcb.X86.sealX86, VG.Proof.AesOcb.X86.sealPre, VG.Proof.AesOcb.X86.oneLay, VG.Proof.AesOcb.X86.onePub, VG.Proof.AesOcb.X86.ctxR, VG.Proof.AesOcb.X86.nonceR, VG.Proof.AesOcb.X86.aadR, VG.Proof.AesOcb.X86.dataR, VG.Proof.AesOcb.X86.tagR, VG.Proof.AesOcb.X86.workR, VG.Proof.AesOcb.X86.argsR', VG.Proof.AesOcb.X86.retR,
      VG.Proof.AesOcb.X86.stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp] using VG.Proof.AesOcb.X86.sealSat)

theorem open_verified (v : BlocksImpl) :
    Verified X86.target («open» (VG.Proof.AesOcb.X86.callees v)) (Proof.AesOcb.openScratchContract X86.abi 24) :=
  Verified.of_correct (VG.Proof.AesOcb.X86.open_correct v) (VG.Proof.AesOcb.X86.open_ct v) (by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e⟩ := VG.Proof.AesOcb.X86.openSat_args
    have esp : openSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
      Spec.Ocb.openPost, Spec.Ocb.openLeak, VG.Proof.AesOcb.X86.openX86, VG.Proof.AesOcb.X86.openPost, VG.Proof.AesOcb.X86.openResult, VG.Proof.AesOcb.X86.openPre, VG.Proof.AesOcb.X86.oneLay, VG.Proof.AesOcb.X86.onePub, VG.Proof.AesOcb.X86.ctxR, VG.Proof.AesOcb.X86.nonceR,
      VG.Proof.AesOcb.X86.aadR, VG.Proof.AesOcb.X86.dataR, VG.Proof.AesOcb.X86.tagR, VG.Proof.AesOcb.X86.workR, VG.Proof.AesOcb.X86.argsR', VG.Proof.AesOcb.X86.retR, VG.Proof.AesOcb.X86.stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp] using VG.Proof.AesOcb.X86.openSat)

/-- A state satisfying `vg_aes_ocb_init`'s precondition: a key of 16 bytes
at `0x1000`, the context at `0x2000` and the scratch buffer at `0x4000`, as
stack arguments at `0x8004`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20
    else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 16⟩]

theorem init_verified (v : BlocksImpl) :
    Verified X86.target (init (VG.Proof.AesOcb.X86.callees v)) (Proof.AesOcb.initScratchContract X86.abi 24) :=
  Verified.of_correct (VG.Proof.AesOcb.X86.init_correct v) (VG.Proof.AesOcb.X86.init_ct v) (by
    have a0 : arg VG.Proof.AesOcb.X86.initSat 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.AesOcb.X86.initSat 1 = 16 := by decide
    have a2 : arg VG.Proof.AesOcb.X86.initSat 2 = 0x2000 := by decide
    have a3 : arg VG.Proof.AesOcb.X86.initSat 3 = 0x4000 := by decide
    have e : argAddr VG.Proof.AesOcb.X86.initSat 0 = 0x8004 := by decide
    have esp : initSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesOcb.initScratchContract, Proof.AesOcb.initScratchSig, Spec.Ocb.initPre,
      Spec.Ocb.initPost, VG.Proof.AesOcb.X86.initX86, VG.Proof.AesOcb.X86.initPre, VG.Proof.AesOcb.X86.keyR, VG.Proof.AesOcb.X86.ictxR, VG.Proof.AesOcb.X86.scrR, VG.Proof.AesOcb.X86.iargsR, VG.Proof.AesOcb.X86.retR, VG.Proof.AesOcb.X86.stackR, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes] [a0, a1, a2, a3, e, esp] using VG.Proof.AesOcb.X86.initSat)

end VG.Proof.AesOcb.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86.Frame`. -/
section

/-!
# AES-OCB on x86, with its working space on the stack

Every function runs its code, proved with the working space as its last
argument (`Verified.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the argument slots (ten for `seal` and `open`, three for `init`) and the 2560
bytes of working space, 2608 and 2580 bytes. The code's own calls use 24
bytes below it. The copies are read only where the pre- and postconditions
read the buffers, and `open`'s leak, whether it succeeds, reads only its
buffers (`Proof/AesOcb/Scratch.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.Impl.AesOcb.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (v : BlocksImpl)

theorem seal_noEsp : («seal» (VG.Proof.AesOcb.X86.callees v)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«seal», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, tagOut, callBlocks, blocksFrame, VG.Proof.AesOcb.X86.callees, Code.allInstrs,
    VG.Proof.AesOcb.X86.noEsp_of v.encNosp, VG.Proof.AesOcb.X86.noEsp_of v.decNosp, ↓reduceIte]
  decide +kernel

theorem open_noEsp : («open» (VG.Proof.AesOcb.X86.callees v)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«open», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, recv, cmp, mask, callBlocks, blocksFrame, VG.Proof.AesOcb.X86.callees, Code.allInstrs,
    VG.Proof.AesOcb.X86.noEsp_of v.encNosp, VG.Proof.AesOcb.X86.noEsp_of v.decNosp, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_noEsp : (init (VG.Proof.AesOcb.X86.callees v)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [init, Impl.AesGcm.X86.entry, keyFrame, blocksFrame, VG.Proof.AesOcb.X86.callees, Code.allInstrs, VG.Proof.AesOcb.X86.noEsp_of v.encNosp,
    VG.Proof.AesOcb.X86.noEsp_of v.expandNosp]
  decide +kernel

theorem seal_stackUse : stackUse («seal» (VG.Proof.AesOcb.X86.callees v)) ≤ 24 := by
  simp only [«seal», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, tagOut, callBlocks, blocksFrame, VG.Proof.AesOcb.X86.callees, stackUse, v.encStack,
    v.decStack, ↓reduceIte]
  decide +kernel

theorem open_stackUse : stackUse («open» (VG.Proof.AesOcb.X86.callees v)) ≤ 24 := by
  simp only [«open», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, recv, cmp, mask, callBlocks, blocksFrame, VG.Proof.AesOcb.X86.callees, stackUse,
    v.encStack, v.decStack, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_stackUse : stackUse (init (VG.Proof.AesOcb.X86.callees v)) ≤ 24 := by
  simp only [init, Impl.AesGcm.X86.entry, keyFrame, blocksFrame, VG.Proof.AesOcb.X86.callees, stackUse, v.encStack, v.expandStack]
  decide +kernel

theorem seal_spSafe : («seal» (VG.Proof.AesOcb.X86.callees v)).all (fun i => !isa.writesSp i) = true := by
  simp only [«seal», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, tagOut, callBlocks, blocksFrame, VG.Proof.AesOcb.X86.callees, Code.all, v.encSpSafe,
    v.decSpSafe, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_spSafe : («open» (VG.Proof.AesOcb.X86.callees v)).all (fun i => !isa.writesSp i) = true := by
  simp only [«open», front, ocbEntry, Impl.AesGcm.X86.entry, nonce, nonceBlock, Impl.AesGcm.X86.copyLoop,
    Impl.AesOcb.X86.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest,
    padCk, xorPad, Impl.AesGcm.X86.xorLoop, tag, recv, cmp, mask, callBlocks, blocksFrame, VG.Proof.AesOcb.X86.callees, Code.all,
    v.encSpSafe, v.decSpSafe, Bool.false_eq_true, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem init_spSafe : (init (VG.Proof.AesOcb.X86.callees v)).all (fun i => !isa.writesSp i) = true := by
  simp only [init, Impl.AesGcm.X86.entry, keyFrame, blocksFrame, VG.Proof.AesOcb.X86.callees, Code.all, v.encSpSafe, v.expandSpSafe,
    Bool.and_true]
  decide +kernel

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: as `sealSat`, with ten stack arguments. -/
def sealFrameSat : State :=
  { VG.Proof.AesOcb.X86.sealSat with
                 rd := [⟨0x1000, 256⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x4000, 4⟩, ⟨0x8004, 40⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ocb.sealContract X86.abi 2632).pre s := by
  implies_sat [Spec.Ocb.sealContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Spec.Ocb.sealPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [sealFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.AesOcb.X86.sealFrameSat

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: as `sealFrameSat`, with the tag read only. -/
def openFrameSat : State :=
  { VG.Proof.AesOcb.X86.sealSat with
                 rd := [⟨0x1000, 256⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x4000, 4⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x8004, 40⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ocb.openContract X86.abi 2632).pre s := by
  implies_sat [Spec.Ocb.openContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Spec.Ocb.openPost,
    Spec.Ocb.openLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [openFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.AesOcb.X86.openFrameSat

/-- A state satisfying `vg_aes_ocb_init`'s precondition, without the working
space. -/
def initFrameSat : State := { VG.Proof.AesOcb.X86.initSat with
                                           wr := [⟨0x2000, 256⟩, ⟨0x8004, 12⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Ocb.initContract X86.abi 2604).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.AesOcb.X86.initFrameSat

theorem seal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («seal» (VG.Proof.AesOcb.X86.callees v)))
      (Spec.Ocb.sealContract X86.abi 2632) :=
  X86.Verified.stackScratch (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.sealPre X86.abi.ptrBits) (post := Spec.Ocb.sealPost X86.abi.ptrBits)
    (wa := true) (stack := 24) (bytes := 2608) (VG.Proof.AesOcb.X86.seal_verified v) (by decide) (VG.Proof.AesOcb.X86.seal_noEsp v)
    (VG.Proof.AesOcb.X86.seal_stackUse v) (sealPre_local _) (sealPost_local _) VG.Proof.AesOcb.X86.sealFrameSat_pre

theorem open_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («open» (VG.Proof.AesOcb.X86.callees v)))
      (Spec.Ocb.openContract X86.abi 2632) :=
  X86.Verified.stackScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.openPre X86.abi.ptrBits) (post := Spec.Ocb.openPost X86.abi.ptrBits)
    (wa := true) (stack := 24) (leak := some (Spec.Ocb.openLeak X86.abi.ptrBits)) (bytes := 2608)
    (VG.Proof.AesOcb.X86.open_verified v) (by decide) (VG.Proof.AesOcb.X86.open_noEsp v) (VG.Proof.AesOcb.X86.open_stackUse v) (openPre_local _) (openPost_local _)
    VG.Proof.AesOcb.X86.openFrameSat_pre (hleak := openLeak_local _)

theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2580 3 (init (VG.Proof.AesOcb.X86.callees v)))
      (Spec.Ocb.initContract X86.abi 2604) :=
  X86.Verified.stackScratch (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Ocb.initPre X86.abi.ptrBits) (post := Spec.Ocb.initPost X86.abi.ptrBits)
    (wa := true) (stack := 24) (bytes := 2580) (VG.Proof.AesOcb.X86.init_verified v) (by decide) (VG.Proof.AesOcb.X86.init_noEsp v)
    (VG.Proof.AesOcb.X86.init_stackUse v) (initPre_local _) (initPost_local _) VG.Proof.AesOcb.X86.initFrameSat_pre

end VG.Proof.AesOcb.X86

end
