import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesGcm.X86.Fn
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.AesCcm.X86
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
import VerifiedGarbage.Proof.AesCcm.Words32
import VerifiedGarbage.Proof.AesGcm.X86.StreamCrypt
import VerifiedGarbage.Proof.CmacAes.X86.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCcm.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Contract`. -/
section

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
abbrev schR (s : State) : Region := ⟨(VG.X86.arg s 0).setWidth 64, 240⟩
abbrev nonceR (s : State) : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
abbrev aadR (s : State) : Region := ⟨(VG.X86.arg s 4).setWidth 64, (VG.X86.arg s 5).toNat⟩
abbrev dataR (s : State) : Region := ⟨(VG.X86.arg s 6).setWidth 64, (VG.X86.arg s 7).toNat⟩
abbrev tagR (s : State) : Region := ⟨(VG.X86.arg s 8).setWidth 64, (VG.X86.arg s 9).toNat⟩
abbrev workR (s : State) : Region := ⟨(VG.X86.arg s 10).setWidth 64, 2560⟩
abbrev argsR' (s : State) : Region := ⟨argAddr s 0, 44⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev stackR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 56, 56⟩

/-- What both functions' preconditions say of the buffers and the
arguments, but for which may be written. -/
def oneLay (s : State) : Prop :=
  (VG.Proof.AesCcm.X86.schR s).Disjoint (VG.Proof.AesCcm.X86.dataR s) ∧ (VG.Proof.AesCcm.X86.schR s).Disjoint (VG.Proof.AesCcm.X86.workR s) ∧ (VG.Proof.AesCcm.X86.schR s).Disjoint (VG.Proof.AesCcm.X86.argsR' s) ∧
  (VG.Proof.AesCcm.X86.nonceR s).Disjoint (VG.Proof.AesCcm.X86.dataR s) ∧ (VG.Proof.AesCcm.X86.nonceR s).Disjoint (VG.Proof.AesCcm.X86.workR s) ∧ (VG.Proof.AesCcm.X86.nonceR s).Disjoint (VG.Proof.AesCcm.X86.argsR' s) ∧
  (VG.Proof.AesCcm.X86.aadR s).Disjoint (VG.Proof.AesCcm.X86.dataR s) ∧ (VG.Proof.AesCcm.X86.aadR s).Disjoint (VG.Proof.AesCcm.X86.workR s) ∧ (VG.Proof.AesCcm.X86.aadR s).Disjoint (VG.Proof.AesCcm.X86.argsR' s) ∧
  (VG.Proof.AesCcm.X86.dataR s).Disjoint (VG.Proof.AesCcm.X86.tagR s) ∧ (VG.Proof.AesCcm.X86.dataR s).Disjoint (VG.Proof.AesCcm.X86.workR s) ∧ (VG.Proof.AesCcm.X86.dataR s).Disjoint (VG.Proof.AesCcm.X86.argsR' s) ∧
  (VG.Proof.AesCcm.X86.tagR s).Disjoint (VG.Proof.AesCcm.X86.workR s) ∧ (VG.Proof.AesCcm.X86.tagR s).Disjoint (VG.Proof.AesCcm.X86.argsR' s) ∧ (VG.Proof.AesCcm.X86.workR s).Disjoint (VG.Proof.AesCcm.X86.argsR' s) ∧
  (VG.Proof.AesCcm.X86.retR s).Disjoint (VG.Proof.AesCcm.X86.schR s) ∧ (VG.Proof.AesCcm.X86.retR s).Disjoint (VG.Proof.AesCcm.X86.nonceR s) ∧ (VG.Proof.AesCcm.X86.retR s).Disjoint (VG.Proof.AesCcm.X86.aadR s) ∧
  (VG.Proof.AesCcm.X86.retR s).Disjoint (VG.Proof.AesCcm.X86.dataR s) ∧ (VG.Proof.AesCcm.X86.retR s).Disjoint (VG.Proof.AesCcm.X86.tagR s) ∧ (VG.Proof.AesCcm.X86.retR s).Disjoint (VG.Proof.AesCcm.X86.workR s) ∧
  (VG.Proof.AesCcm.X86.retR s).Disjoint (VG.Proof.AesCcm.X86.argsR' s) ∧
  (VG.Proof.AesCcm.X86.stackR s).Disjoint (VG.Proof.AesCcm.X86.schR s) ∧ (VG.Proof.AesCcm.X86.stackR s).Disjoint (VG.Proof.AesCcm.X86.nonceR s) ∧ (VG.Proof.AesCcm.X86.stackR s).Disjoint (VG.Proof.AesCcm.X86.aadR s) ∧
  (VG.Proof.AesCcm.X86.stackR s).Disjoint (VG.Proof.AesCcm.X86.dataR s) ∧ (VG.Proof.AesCcm.X86.stackR s).Disjoint (VG.Proof.AesCcm.X86.tagR s) ∧ (VG.Proof.AesCcm.X86.stackR s).Disjoint (VG.Proof.AesCcm.X86.workR s) ∧
  (VG.Proof.AesCcm.X86.stackR s).Disjoint (VG.Proof.AesCcm.X86.argsR' s) ∧
  (VG.X86.arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧
  (VG.X86.arg s 4).toNat + (VG.X86.arg s 5).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 6).toNat + (VG.X86.arg s 7).toNat ≤ 2 ^ 32 ∧
  (VG.X86.arg s 8).toNat + (VG.X86.arg s 9).toNat ≤ 2 ^ 32 ∧
  (VG.X86.arg s 10).toNat + 2560 ≤ 2 ^ 32 ∧ 56 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 48 ≤ 2 ^ 32 ∧
  ((VG.X86.arg s 1).toNat = 10 ∨ (VG.X86.arg s 1).toNat = 12 ∨ (VG.X86.arg s 1).toNat = 14) ∧
  valid (VG.X86.arg s 9).toNat (VG.X86.arg s 3).toNat (VG.X86.arg s 5).toNat (VG.X86.arg s 7).toNat = true

/-- `seal` writes the tag. -/
def sealPre (s : State) : Prop :=
  s.rd = [VG.Proof.AesCcm.X86.schR s, VG.Proof.AesCcm.X86.nonceR s, VG.Proof.AesCcm.X86.aadR s] ∧ s.wr = [VG.Proof.AesCcm.X86.dataR s, VG.Proof.AesCcm.X86.tagR s, VG.Proof.AesCcm.X86.workR s, VG.Proof.AesCcm.X86.argsR' s] ∧ VG.Proof.AesCcm.X86.oneLay s

/-- `open` reads it. -/
def openPre (s : State) : Prop :=
  s.rd = [VG.Proof.AesCcm.X86.schR s, VG.Proof.AesCcm.X86.nonceR s, VG.Proof.AesCcm.X86.aadR s, VG.Proof.AesCcm.X86.tagR s] ∧ s.wr = [VG.Proof.AesCcm.X86.dataR s, VG.Proof.AesCcm.X86.workR s, VG.Proof.AesCcm.X86.argsR' s] ∧ VG.Proof.AesCcm.X86.oneLay s

/-- All eleven stack arguments are public, and the stack pointer. -/
def onePub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 11, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- What `open` computes. -/
abbrev openRes (s : State) : Option (List Byte) :=
  VG.Spec.Ccm.decryptWith (VG.Spec.Ccm.ctxCiph s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat) (VG.X86.arg s 9).toNat
    (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat) (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat)
    (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 4).setWidth 64) (VG.X86.arg s 5).toNat) (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 8).setWidth 64) (VG.X86.arg s 9).toNat)

/-- `vg_aes_ccm_seal`. -/
def sealX86 : Contract isa where
  pre := VG.Proof.AesCcm.X86.sealPre
  post s s' :=
    VG.Spec.Ccm.encryptWith (VG.Spec.Ccm.ctxCiph s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat) (VG.X86.arg s 9).toNat
        (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat) (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat)
        (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 4).setWidth 64) (VG.X86.arg s 5).toNat) =
      (VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat, VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 8).setWidth 64) (VG.X86.arg s 9).toNat)
  pub := VG.Proof.AesCcm.X86.onePub

/-- What `vg_aes_ccm_open` may leak (`Spec.Ccm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬((VG.X86.arg s 1).toNat = 10 ∨ (VG.X86.arg s 1).toNat = 12 ∨ (VG.X86.arg s 1).toNat = 14) then [] else
  [if (VG.Proof.AesCcm.X86.openRes s).isSome then 1 else 0]

/-- `vg_aes_ccm_open`. -/
def openX86 : Contract isa where
  pre := VG.Proof.AesCcm.X86.openPre
  post s s' :=
    match VG.Proof.AesCcm.X86.openRes s with
    | some pt => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧ VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat = pt
    | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧
      VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 6).setWidth 64) (VG.X86.arg s 7).toNat = VG.Spec.Ccm.zeros (VG.X86.arg s 7).toNat
  pub s₁ s₂ := VG.Proof.AesCcm.X86.onePub s₁ s₂ ∧ VG.Proof.AesCcm.X86.openLeak s₁ = VG.Proof.AesCcm.X86.openLeak s₂

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Env`. -/
section

/-!
# AES-CCM on x86: where everything is

Untrusted: everything here is checked by Lean. The key schedule (240 bytes
at `K`), the working space (2560 bytes at `W`) and the 56 bytes of stack
below `SP` that the calls use (`Lay`); what a state may access (`Perm`); the
registers holding `W` and the stack pointer (`Env`); and the public values
the entry keeps in `W` (`Slots`). The pieces write the parts of `W` in
`mutR` (and the data, and the stack below `SP`), so the slots and our
caller's registers saved in `W` stay as the entry left them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_off in_off in_left covers_left
  covers_cons covers_nil slotv)

/-! ## Covering -/

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem covers_append {xs ys ts : List Region} (h₁ : Covers xs ts) (h₂ : Covers ys ts) :
    Covers (xs ++ ys) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ a n ⟨x, hx, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

/-! ## The regions -/

/-- The key schedule, `W` and the stack below `SP` used by the calls. -/
structure Lay (K W SP : BitVec 32) : Prop where
  fk : K.toNat + 240 ≤ 2 ^ 32
  fw : W.toNat + 2560 ≤ 2 ^ 32
  sp : 56 ≤ SP.toNat
  k_w : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  stk_k : (below SP 56).Disjoint ⟨w64 K, 240⟩
  stk_w : (below SP 56).Disjoint ⟨w64 W, 2560⟩

/-- What a state may access. -/
structure Perm (K W : BitVec 32) (s : State) : Prop where
  k : Covers [⟨w64 K, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨w64 W, 2560⟩] s.wr

/-- The registers holding `W` and the stack pointer, and what the state may
access. -/
structure Env (K W SP : BitVec 32) (s : State) : Prop where
  ebp : s.gpr .ebp = W
  esp : s.gpr .esp = SP
  perm : VG.Proof.AesCcm.X86.Perm K W s

theorem Perm.of_eq {K W : BitVec 32} {s s' : State} (h : VG.Proof.AesCcm.X86.Perm K W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesCcm.X86.Perm K W s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `ebp`, `esp` and the permissions. -/
theorem Env.keep {K W SP : BitVec 32} {s s' : State} (h : VG.Proof.AesCcm.X86.Env K W SP s) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.X86.Env K W SP s' :=
  ⟨by rw [hbp, h.ebp], by rw [hsp, h.esp], h.perm.of_eq hrd hwr⟩

namespace Lay

theorem kSub {K : Addr} {d n : Nat} (h : d + n ≤ 240) : Region.Sub ⟨K + BitVec.ofNat 64 d, n⟩ ⟨K, 240⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

/-- Parts of `W` are disjoint. -/
theorem w_w {W : BitVec 32} {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

variable {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP)
include L

theorem k_w' {a n d k : Nat} (ha : a + n ≤ 240) (hd : d + k ≤ 2560) :
    (⟨w64 K + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  (L.k_w.sub_left (VG.Proof.AesCcm.X86.Lay.kSub ha)).sub_right (VG.Proof.AesCcm.X86.Lay.wSub hd)

theorem stk_w' {a n : Nat} (ha : a + n ≤ 2560) : (below SP 56).Disjoint ⟨w64 W + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (VG.Proof.AesCcm.X86.Lay.wSub ha)

theorem aW {o : Nat} (ho : o < 2560) : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o :=
  w64_add (by have := L.fw; omega)

theorem nW {o : Nat} (ho : o < 2560) : (W + BitVec.ofNat 32 o).toNat = W.toNat + o :=
  toNat_add32 (by have := L.fw; omega)

end Lay

namespace Perm

variable {K W : BitVec 32} {s : State} (P : VG.Proof.AesCcm.X86.Perm K W s)
include P

theorem kR {d n : Nat} (h : d + n ≤ 240) : InRegions (s.rd ++ s.wr) (w64 K + BitVec.ofNat 64 d) n :=
  in_off P.k h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (w64 W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem kC {d n : Nat} (h : d + n ≤ 240) : Covers [⟨w64 K + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.k h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨w64 W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W`, the
key schedule and the stack below `SP`. -/
structure Buf (W SP : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨w64 D, n⟩] (s.rd ++ s.wr)
  wrap : D.toNat + n ≤ 2 ^ 32
  w : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  stk : (below SP 56).Disjoint ⟨w64 D, n⟩

namespace Buf

variable {W SP : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : VG.Proof.AesCcm.X86.Buf W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.X86.Buf W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem lt : n < 2 ^ 64 := by have := h.wrap; omega

omit h in
/-- The address of byte `k`. -/
theorem ptr {k : Nat} (hk : D.toNat + k < 2 ^ 32) : w64 (D + BitVec.ofNat 32 k) = w64 D + BitVec.ofNat 64 k :=
  w64_add hk

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) (hw : D.toNat + k < 2 ^ 32) : VG.Proof.AesCcm.X86.Buf W SP s (D + BitVec.ofNat 32 k) (n - k) where
  rd := by rw [VG.Proof.AesCcm.X86.Buf.ptr hw]; exact covers_off h.rd (by omega) h.lt
  wrap := by rw [toNat_add32 hw]; have := h.wrap; omega
  w := by rw [VG.Proof.AesCcm.X86.Buf.ptr hw]; exact h.w.sub_left (Offset.sub_base _ (by omega))
  stk := by rw [VG.Proof.AesCcm.X86.Buf.ptr hw]; exact h.stk.sub_right (Offset.sub_base _ (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesCcm.X86.Buf W SP s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

end Buf

/-! ## The slots -/

/-- The public values the entry keeps in `W`: the key schedule, the rounds,
the nonce and its length, the associated data and its length, the data and
its length, the tag and its length. -/
structure Slots (W K : BitVec 32) (R : Nat) (N A D T : BitVec 32) (nl al n tl : Nat) (m : Mem) : Prop where
  ctx : slotv m W Impl.AesCcm.X86.ctxO = K
  rounds : slotv m W Impl.AesCcm.X86.roundsO = BitVec.ofNat 32 R
  nonce : slotv m W Impl.AesCcm.X86.nonceO = N
  nlen : slotv m W Impl.AesCcm.X86.nlenO = BitVec.ofNat 32 nl
  aad : slotv m W Impl.AesCcm.X86.aadO = A
  alen : slotv m W Impl.AesCcm.X86.alenO = BitVec.ofNat 32 al
  data : slotv m W Impl.AesCcm.X86.dataO = D
  len : slotv m W Impl.AesCcm.X86.lenO = BitVec.ofNat 32 n
  tl : slotv m W Impl.AesGcm.X86.tglO = BitVec.ofNat 32 tl
  tp : slotv m W Impl.AesGcm.X86.tpO = T

/-- The parts of `W` the pieces write: the blocks at `[0, 112)`, the result of
the comparison at `[176, 180)`, the padded received tag at `[196, 212)`, and
`[240, 2560)` (the padded computed tag, the arguments of the piece running
and the working space of the functions called). -/
abbrev wA (W : BitVec 32) : Region := ⟨w64 W, 112⟩
abbrev wO (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 176, 4⟩
abbrev wT (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 196, 16⟩
abbrev wC (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 240, 2320⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (W SP D : BitVec 32) (n : Nat) : List Region :=
  [VG.Proof.AesCcm.X86.wA W, VG.Proof.AesCcm.X86.wO W, VG.Proof.AesCcm.X86.wT W, VG.Proof.AesCcm.X86.wC W, below SP 56, ⟨w64 D, n⟩]

/-- The parts of `W` the pieces write. -/
abbrev wR (W SP : BitVec 32) : List Region := [VG.Proof.AesCcm.X86.wA W, VG.Proof.AesCcm.X86.wO W, VG.Proof.AesCcm.X86.wT W, VG.Proof.AesCcm.X86.wC W, below SP 56]

theorem wR_mut (W SP D : BitVec 32) (n : Nat) : ∀ r ∈ VG.Proof.AesCcm.X86.wR W SP, ∃ r' ∈ VG.Proof.AesCcm.X86.mutR W SP D n, Region.Sub r r' :=
  fun r hr => ⟨r, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;>
    simp [h], fun _ h => h⟩

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {K W SP D : BitVec 32} {n : Nat} (L : VG.Proof.AesCcm.X86.Lay K W SP)
    (hD : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2560⟩) {d k : Nat}
    (hd : 112 ≤ d ∧ d + k ≤ 176 ∨ 180 ≤ d ∧ d + k ≤ 196 ∨ 212 ≤ d ∧ d + k ≤ 240) :
    ∀ r ∈ VG.Proof.AesCcm.X86.mutR W SP D n, (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Lay.w_w (W := W) (a := d) (n := k) (d := 0) (k := 112) (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (by omega) (by omega) (by decide)
  · exact Lay.w_w (by omega) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm
  · exact (hD.sub_right (Lay.wSub (by omega))).symm

/-- The slots, after code that changes only `mutR`. -/
theorem slots_mut {K W SP D' : BitVec 32} {n' : Nat} (L : VG.Proof.AesCcm.X86.Lay K W SP)
    (hD : (⟨w64 D', n'⟩ : Region).Disjoint ⟨w64 W, 2560⟩) {m m' : Mem} (hf : Frame (VG.Proof.AesCcm.X86.mutR W SP D' n') m m')
    {R : Nat} {N A D T : BitVec 32} {nl al n tl : Nat} (S : VG.Proof.AesCcm.X86.Slots W K R N A D T nl al n tl m) :
    VG.Proof.AesCcm.X86.Slots W K R N A D T nl al n tl m' := by
  have k : ∀ o, (112 ≤ o ∧ o + 4 ≤ 176 ∨ 180 ≤ o ∧ o + 4 ≤ 196 ∨ 212 ≤ o ∧ o + 4 ≤ 240) →
      slotv m' W o = slotv m W o := fun o ho =>
    hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (VG.Proof.AesCcm.X86.kept_mut L hD ho) (by decide)
  exact ⟨by rw [k _ (by decide)]; exact S.ctx, by rw [k _ (by decide)]; exact S.rounds,
    by rw [k _ (by decide)]; exact S.nonce, by rw [k _ (by decide)]; exact S.nlen,
    by rw [k _ (by decide)]; exact S.aad, by rw [k _ (by decide)]; exact S.alen,
    by rw [k _ (by decide)]; exact S.data, by rw [k _ (by decide)]; exact S.len,
    by rw [k _ (by decide)]; exact S.tl, by rw [k _ (by decide)]; exact S.tp⟩

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Run`. -/
section

/-!
# AES-CCM on x86: running straight-line blocks

Untrusted: everything here is checked by Lean. `crun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`,
keeping the registers folded), as AES-GCM's `xrun` does, with the offsets
of the AES-CCM code.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp tglO rO vO tpO dO nO bO)
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

/-- Runs a block of the instructions the AES-CCM code uses. The facts given
rewrite the addresses and discharge the permissions. -/
macro "crun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, execAlu, execShift, State.load32, store32_eq, State.load8, store8_eq,
    State.ea, at_, imm, slot, argOp, blkO, c0O, c1O, ksO, uO, ctxO, roundsO, nonceO, nlenO, aadO, alenO, dataO,
    lenO, okO, scrO, tglO, rO, vO, tpO, dO, nO, bO, List.cons_append, List.nil_append, List.append_assoc,
    Option.bind_some, Option.map_some, readW_writeW_off, readW_writeB_off, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
    wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags, gpr_setMem, mem_setMem, rd_setMem,
    wr_setMem, cf_setMem, zf_setMem, ite_true, ite_false, reduceCtorEq, Nat.reduceAdd, ↓reduceIte, Nat.reduceLT,
    Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceMul, and_self, and_true, true_and,
    eq_self_iff_true, Reg8.reg, $ts,*]) <;>
  try rfl)

/-- Reads registers through the writes of a block. -/
macro "cregs" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | with_reducible assumption) only [gpr_setMem, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags,
    $ts,*]))

/-- Reads the memory, flags and permissions through the writes of a block. -/
macro "cmems" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [mem_setMem, mem_setReg, mem_arithFlags, mem_setFlags,
    rd_setMem, rd_setReg, rd_arithFlags, rd_setFlags, wr_setMem, wr_setReg, wr_arithFlags, wr_setFlags,
    zf_setMem, zf_setReg, zf_arithFlags, cf_setMem, cf_setReg, cf_arithFlags, gpr_setMem, gpr_setReg_self,
    gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, Mem.readW_writeW_self32, readW_writeW_off, readW_writeB_off, blkO, c0O, c1O,
    ksO, uO, ctxO, roundsO, nonceO, nlenO, aadO, alenO, dataO, lenO, okO, scrO, tglO, rO, vO, tpO, dO, nO, bO,
    Nat.reduceAdd, Reg8.reg, eq_self_iff_true, and_self, $ts,*]))

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

/-- `a; (b; (c; d))` from `(a; (b; c)); d`. -/
theorem CT.assoc3 {I : State → Prop} {a b c d : Prog isa}
    (h : Proof.AesGcm.X86.CT I (.seq (.seq a (.seq b c)) d)) : Proof.AesGcm.X86.CT I (.seq a (.seq b (.seq c d))) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ e₁ =>
    cases e₁ with
    | seq b₁ e₁ =>
      cases e₁ with
      | seq c₁ d₁ =>
        cases e₂ with
        | seq a₂ e₂ =>
          cases e₂ with
          | seq b₂ e₂ =>
            cases e₂ with
            | seq c₂ d₂ =>
              obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ c₁)) d₁) (.seq (.seq a₂ (.seq b₂ c₂)) d₂)
              simp only [List.append_assoc] at ht
              exact ⟨ht, hq⟩

/-- A register pinned. -/
theorem pin1 {I : State → Prop} {a : Reg} {x : BitVec 32} (h : ∀ s, I s → s.gpr a = x) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h _ h₁, h _ h₂]

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

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Callee`. -/
section

/-!
# AES-CCM on x86: the functions called

Untrusted: everything here is checked by Lean. The calls of
`vg_cmac_aes_update` are those of streaming AES-CMAC
(`Proof.CmacAes.Stream.X86.upd_call`), and those of `vg_aes_ctr32` those of
AES-GCM (`Proof.AesGcm.X86.ctr_call`, whose frame and call depend only on
the implementation of `vg_aes_ctr32`), with `ebp` moved to the working space
around them (`ctrCall_ok`). Their arguments are built from the
environment: the key schedule, a block of `W` as the state or the counter
block, the data or blocks of `W` as the data (`Src`), and the working space
at `W + 384`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt blocksAt ctr32 aesWith)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (imm)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_left covers_cons covers_nil CtrCall CtrPost
  GcmImpl GhashImpl gpr_setMem)
open VG.Proof.CmacAes.Stream.X86 (UArgs UPost)
open VG.Proof.AesGcm.X86 (CT)

theorem below_sub56 {SP : BitVec 32} {k : Nat} (hk : k ≤ 56) (hs : 56 ≤ SP.toNat) :
    Region.Sub (below SP k) (below SP 56) :=
  VG.X86.below_sub hk hs

/-! ## Data for a call -/

/-- `k` bytes at `Q`, which the code may read, apart from the parts of `W`
from `384` on and the stack below `SP`. -/
structure Src (W SP : BitVec 32) (s : State) (Q : BitVec 32) (k : Nat) : Prop where
  rd : Covers [⟨w64 Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 32
  qs : (⟨w64 Q, k⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 384, 2176⟩
  stk : (below SP 56).Disjoint ⟨w64 Q, k⟩

/-- Bytes of `W` below 384 as data. -/
theorem srcW {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (P : VG.Proof.AesCcm.X86.Perm K W s) {t k : Nat} (hk : t + k ≤ 384) :
    VG.Proof.AesCcm.X86.Src W SP s (W + BitVec.ofNat 32 t) k where
  rd := by rw [L.aW (o := t) (by omega)]; exact covers_left (P.wC (by omega))
  wrap := by rw [L.nW (by omega)]; have := L.fw; omega
  qs := by rw [L.aW (o := t) (by omega)]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  stk := by rw [L.aW (o := t) (by omega)]; exact L.stk_w' (by omega)

/-- A buffer as data. -/
theorem srcBuf {W SP : BitVec 32} {s : State} {Q : BitVec 32} {k : Nat} (h : VG.Proof.AesCcm.X86.Buf W SP s Q k) : VG.Proof.AesCcm.X86.Src W SP s Q k :=
  ⟨h.rd, h.wrap, h.w.sub_right (Lay.wSub (by decide)), h.stk⟩

theorem Src.of_eq {W SP : BitVec 32} {s s' : State} {Q : BitVec 32} {k : Nat} (h : VG.Proof.AesCcm.X86.Src W SP s Q k)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.X86.Src W SP s' Q k :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-! ## `vg_cmac_aes_update` -/

/-- `W + d`, as the 64-bit address it is. -/
theorem wAddr {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {d : Nat} (hd : d < 2560) :
    (W + BitVec.ofNat 32 d).setWidth 64 = w64 W + BitVec.ofNat 64 d := L.aW hd

/-- The arguments of `vg_cmac_aes_update`: the key schedule, the state at
`W + y`, `n` blocks at `Q`, and the working space at `W + 384`. -/
theorem uargs {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : y + 16 ≤ 384) {Q : BitVec 32} {n : Nat}
    (hq : VG.Proof.AesCcm.X86.Src W SP s Q (16 * n)) (hqy : (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩)
    (hn : 16 * n < 2 ^ 32) (eax : s.gpr .eax = K) (ecx : s.gpr .ecx = BitVec.ofNat 32 R)
    (edx : s.gpr .edx = W + BitVec.ofNat 32 y) (ebx : s.gpr .ebx = Q) (esi : s.gpr .esi = BitVec.ofNat 32 n)
    (edi : s.gpr .edi = W + BitVec.ofNat 32 384) :
    UArgs s K (W + BitVec.ofNat 32 y) Q (W + BitVec.ofNat 32 384) R n where
  eax := eax
  ecx := ecx
  edx := edx
  ebx := ebx
  esi := esi
  edi := edi
  rounds := hR
  esp := by rw [E.esp]; exact L.sp
  hn := hn
  wc := by rw [VG.Proof.AesCcm.X86.wAddr L (by omega)]; simpa using L.k_w' (a := 0) (n := 240) (d := y) (k := 16) (by decide) (by omega)
  ws := by rw [VG.Proof.AesCcm.X86.wAddr L (by omega)]; simpa using L.k_w' (a := 0) (n := 240) (d := 384) (k := 2176) (by decide) (by decide)
  dc := by rw [VG.Proof.AesCcm.X86.wAddr L (by omega)]; exact hqy
  ds := by rw [VG.Proof.AesCcm.X86.wAddr L (by omega)]; exact hq.qs
  cs := by rw [VG.Proof.AesCcm.X86.wAddr L (by omega), VG.Proof.AesCcm.X86.wAddr L (by omega)]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  bW := by rw [E.esp]; exact L.stk_k
  bD := by rw [E.esp]; exact hq.stk
  bC := by rw [E.esp, VG.Proof.AesCcm.X86.wAddr L (by omega)]; exact L.stk_w' (by omega)
  bS := by rw [E.esp, VG.Proof.AesCcm.X86.wAddr L (by omega)]; exact L.stk_w' (by decide)
  fW := by have := L.fk; omega
  fC := by rw [L.nW (by omega)]; have := L.fw; omega
  fD := hq.wrap
  fS := by rw [L.nW (by omega)]; have := L.fw; omega
  reads := covers_cons E.perm.k (covers_cons hq.rd covers_nil)
  writes := by
    rw [VG.Proof.AesCcm.X86.wAddr L (by omega), VG.Proof.AesCcm.X86.wAddr L (by omega)]
    exact covers_cons (E.perm.wC (by omega)) (covers_cons (E.perm.wC (by decide)) covers_nil)

/-- A call of `vg_cmac_aes_update`, with its arguments (`uargs`). -/
theorem updCall_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : y + 16 ≤ 384) {Q : BitVec 32} {n : Nat}
    (hq : VG.Proof.AesCcm.X86.Src W SP s Q (16 * n)) (hqy : (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩)
    (hn : 16 * n < 2 ^ 32) (eax : s.gpr .eax = K) (ecx : s.gpr .ecx = BitVec.ofNat 32 R)
    (edx : s.gpr .edx = W + BitVec.ofNat 32 y) (ebx : s.gpr .ebx = Q) (esi : s.gpr .esi = BitVec.ofNat 32 n)
    (edi : s.gpr .edi = W + BitVec.ofNat 32 384) :
    WP isa (updCall v.callee v.suffix) s fun s' => VG.Proof.AesCcm.X86.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 384, 2176⟩, below SP 56] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
          (Spec.Cmac.blocksAt s.mem (w64 Q) 16 n) := by
  refine WP.mono (Proof.CmacAes.Stream.X86.upd_call v (VG.Proof.AesCcm.X86.uargs L E hR hy hq hqy hn eax ecx edx ebx esi edi))
    fun s' h => ⟨E.keep (h.saved _ (by decide)) (h.saved _ (by decide)) h.rd h.wr, h.rd, h.wr, h.saved, ?_, ?_⟩
  · have f := h.frame
    rw [VG.Proof.AesCcm.X86.wAddr L (by omega), VG.Proof.AesCcm.X86.wAddr L (by omega), E.esp] at f
    exact f
  · have o := h.out
    rw [VG.Proof.AesCcm.X86.wAddr L (by omega)] at o
    exact o

/-! ## `vg_aes_ctr32` -/

/-- The frame and call of `vg_aes_ctr32`: AES-GCM's, with any implementation
of `vg_aes_ghash` beside it. -/
theorem ctrFrame_ok (v : Ctr32Impl) {s : State} {K C D S : BitVec 32} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa (.frame (.push [.ebp, .edi, .ebx, .edx, .ecx, .eax]) (.call v.callee.name v.callee.code) (.pop .eax 6)) s
      (CtrPost s K C D S R n) :=
  Proof.AesGcm.X86.ctr_call ⟨v, .scalar⟩ h

/-- A call of `vg_aes_ctr32` on `n` blocks at `Q`, from the counter block at
`W + c`, with its working space at `W + 384`. -/
theorem ctrCall_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {c : Nat} (hc : c + 16 ≤ 384) {Q : BitVec 32} {n : Nat}
    (hq : VG.Proof.AesCcm.X86.Src W SP s Q (16 * n)) (hqc : (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 c, 16⟩)
    (hqk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 Q, 16 * n⟩) (hqw : Covers [⟨w64 Q, 16 * n⟩] s.wr)
    (eax : s.gpr .eax = K) (ecx : s.gpr .ecx = BitVec.ofNat 32 R) (edx : s.gpr .edx = W + BitVec.ofNat 32 c)
    (ebx : s.gpr .ebx = Q) (edi : s.gpr .edi = BitVec.ofNat 32 n) :
    WP isa (ctrCall v.callee) s fun s' => VG.Proof.AesCcm.X86.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.ebx, .esi, .edi], s'.gpr r = s.gpr r) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 c, 16⟩, ⟨w64 Q, 16 * n⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 56]
        s.mem s'.mem ∧
      blocksAt s'.mem (w64 Q) n = ctr32 (aesWith R (bytesAt s.mem (w64 K) (16 * (R + 1))))
        (blockAt s.mem (w64 W + BitVec.ofNat 64 c)) (blocksAt s.mem (w64 Q) n) := by
  have hsp := L.sp
  have b28 : Region.Sub (below SP 28) (below SP 56) := VG.Proof.AesCcm.X86.below_sub56 (by decide) hsp
  -- `ebp := W + 384`.
  refine WP.seq (WP.of_runBlock ⟨_, by crun [], ?_⟩)
  -- The call.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.ctrFrame_ok v (K := K) (C := W + BitVec.ofNat 32 c) (D := Q)
    (S := W + BitVec.ofNat 32 384) (R := R) (n := n) ?_) fun s₂ P => ?_)
  · have e384 : s.gpr .ebp + BitVec.ofNat 32 384 = W + BitVec.ofNat 32 384 := by rw [E.ebp]
    refine ⟨by cregs [eax], by cregs [ecx], by cregs [edx], by cregs [ebx], by cregs [edi], by cregs [e384], hR,
      by cregs [E.esp]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [L.aW (o := c) (by omega)]; simpa using L.k_w' (a := 0) (n := 240) (d := c) (k := 16) (by decide) (by omega)
    · exact hqk
    · rw [L.aW (o := 384) (by omega)]
      simpa using L.k_w' (a := 0) (n := 240) (d := 384) (k := 2048) (by decide) (by decide)
    · rw [L.aW (o := c) (by omega)]; exact hqc.symm
    · rw [L.aW (o := c) (by omega), L.aW (o := 384) (by omega)]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · rw [L.aW (o := 384) (by omega)]; exact hq.qs.sub_right (Region.sub_prefix (by decide))
    · cregs [E.esp]; exact L.stk_k.sub_left b28
    · cregs [E.esp]; rw [L.aW (o := c) (by omega)]; exact (L.stk_w' (by omega)).sub_left b28
    · cregs [E.esp]; exact hq.stk.sub_left b28
    · cregs [E.esp]; rw [L.aW (o := 384) (by omega)]; exact (L.stk_w' (by decide)).sub_left b28
    · have := L.fk; omega
    · rw [L.nW (by omega)]; have := L.fw; omega
    · exact hq.wrap
    · rw [L.nW (by omega)]; have := L.fw; omega
    · cmems []; exact covers_cons E.perm.k covers_nil
    · cmems []; rw [L.aW (o := c) (by omega), L.aW (o := 384) (by omega)]
      exact covers_cons (E.perm.wC (by omega)) (covers_cons hqw (covers_cons (E.perm.wC (by decide)) covers_nil))
  -- `ebp := W`.
  have hbp₂ : s₂.gpr .ebp = W + BitVec.ofNat 32 384 := by
    rw [P.saved _ (by decide)]; cregs [E.ebp]
  have hsp₂ : s₂.gpr .esp = SP := by rw [P.saved _ (by decide)]; cregs [E.esp]
  refine WP.of_runBlock ⟨_, by crun [hbp₂], ?_⟩
  refine ⟨⟨by cregs [hbp₂]; exact BitVec.add_sub_cancel _ _, by cregs [hsp₂],
    E.perm.of_eq (by cmems [P.rd]) (by cmems [P.wr])⟩, by cmems [P.rd], by cmems [P.wr], ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (cregs []; rw [P.saved _ (by decide)]; cregs [])
  · have f := P.frame
    rw [L.aW (o := c) (by omega), L.aW (o := 384) (by omega)] at f
    cmems []
    refine f.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨below SP 56, by simp, ?_⟩
      have : (s.gpr .ebp + BitVec.ofNat 32 384).setWidth 64 = (W + BitVec.ofNat 32 384).setWidth 64 := by rw [E.ebp]
      simpa [gpr_setReg_of_ne, E.esp] using b28
  · have o := P.out
    rw [L.aW (o := c) (by omega)] at o
    cmems []
    exact o

/-! ## Constant time -/

/-- Calls of `vg_cmac_aes_update` with the same arguments are constant time. -/
theorem updCall_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y + 16 ≤ 384) {Q : BitVec 32} {n : Nat} (hn : 16 * n < 2 ^ 32) {I : State → Prop}
    (hI : ∀ s, I s → VG.Proof.AesCcm.X86.Env K W SP s ∧ VG.Proof.AesCcm.X86.Src W SP s Q (16 * n) ∧
      (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ ∧ s.gpr .eax = K ∧
      s.gpr .ecx = BitVec.ofNat 32 R ∧ s.gpr .edx = W + BitVec.ofNat 32 y ∧ s.gpr .ebx = Q ∧
      s.gpr .esi = BitVec.ofNat 32 n ∧ s.gpr .edi = W + BitVec.ofNat 32 384) :
    CT I (updCall v.callee v.suffix) :=
  Proof.CmacAes.Stream.X86.upd_rel v (E := SP) fun s₁ s₂ ⟨h₁, h₂⟩ => by
    obtain ⟨E₁, q₁, y₁, a₁, c₁, d₁, b₁, i₁, j₁⟩ := hI s₁ h₁
    obtain ⟨E₂, q₂, y₂, a₂, c₂, d₂, b₂, i₂, j₂⟩ := hI s₂ h₂
    exact ⟨VG.Proof.AesCcm.X86.uargs L E₁ hR hy q₁ y₁ hn a₁ c₁ d₁ b₁ i₁ j₁, VG.Proof.AesCcm.X86.uargs L E₂ hR hy q₂ y₂ hn a₂ c₂ d₂ b₂ i₂ j₂, E₁.esp, E₂.esp⟩

/-- Calls of `vg_aes_ctr32` with the same arguments are constant time. -/
theorem ctrCall_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {c : Nat} (hc : c + 16 ≤ 384) {Q : BitVec 32} {n : Nat} {I : State → Prop}
    (hI : ∀ s, I s → VG.Proof.AesCcm.X86.Env K W SP s ∧ VG.Proof.AesCcm.X86.Src W SP s Q (16 * n) ∧ Covers [⟨w64 Q, 16 * n⟩] s.wr ∧
      (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 c, 16⟩ ∧
      (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 Q, 16 * n⟩ ∧ s.gpr .eax = K ∧
      s.gpr .ecx = BitVec.ofNat 32 R ∧ s.gpr .edx = W + BitVec.ofNat 32 c ∧ s.gpr .ebx = Q ∧
      s.gpr .edi = BitVec.ofNat 32 n) :
    CT I (ctrCall v.callee) := by
  have hsp := L.sp
  have b28 : Region.Sub (below SP 28) (below SP 56) := VG.Proof.AesCcm.X86.below_sub56 (by decide) hsp
  -- The state after `ebp := W + 384`, as `CtrCall` needs it.
  have call : ∀ s, I s → ∀ s', runBlock isa [.alu .add .ebp (imm scrO)] s = some s' →
      CtrCall s' K (W + BitVec.ofNat 32 c) Q (W + BitVec.ofNat 32 384) R n ∧ s'.gpr .esp = SP := by
    intro s hs s' run
    obtain ⟨E, hq, hqw, hqc, hqk, eax, ecx, edx, ebx, edi⟩ := hI s hs
    have e := run
    simp (disch := first | decide | omega) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      imm, scrO, Option.bind_some, Option.some.injEq] at e
    subst e
    have e384 : s.gpr .ebp + BitVec.ofNat 32 384 = W + BitVec.ofNat 32 384 := by rw [E.ebp]
    refine ⟨⟨by cregs [eax], by cregs [ecx], by cregs [edx], by cregs [ebx], by cregs [edi], by cregs [e384], hR,
      by cregs [E.esp]; omega, ?_, hqk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by cregs [E.esp]⟩
    · rw [L.aW (o := c) (by omega)]; simpa using L.k_w' (a := 0) (n := 240) (d := c) (k := 16) (by decide) (by omega)
    · rw [L.aW (o := 384) (by omega)]
      simpa using L.k_w' (a := 0) (n := 240) (d := 384) (k := 2048) (by decide) (by decide)
    · rw [L.aW (o := c) (by omega)]; exact hqc.symm
    · rw [L.aW (o := c) (by omega), L.aW (o := 384) (by omega)]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · rw [L.aW (o := 384) (by omega)]; exact hq.qs.sub_right (Region.sub_prefix (by decide))
    · cregs [E.esp]; exact L.stk_k.sub_left b28
    · cregs [E.esp]; rw [L.aW (o := c) (by omega)]; exact (L.stk_w' (by omega)).sub_left b28
    · cregs [E.esp]; exact hq.stk.sub_left b28
    · cregs [E.esp]; rw [L.aW (o := 384) (by omega)]; exact (L.stk_w' (by decide)).sub_left b28
    · have := L.fk; omega
    · rw [L.nW (by omega)]; have := L.fw; omega
    · exact hq.wrap
    · rw [L.nW (by omega)]; have := L.fw; omega
    · cmems []; exact covers_cons E.perm.k covers_nil
    · cmems []; rw [L.aW (o := c) (by omega), L.aW (o := 384) (by omega)]
      exact covers_cons (E.perm.wC (by omega)) (covers_cons hqw (covers_cons (E.perm.wC (by decide)) covers_nil))
  refine CT.seq (J := fun s' => ∃ s, I s ∧ runBlock isa [.alu .add .ebp (imm scrO)] s = some s')
    (CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(hI _ h₁).1.ebp, (hI _ h₂).1.ebp]) (by taint_decide))
    (fun s hs => WP.of_runBlock ⟨_, by crun [], s, hs, by crun []⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = W + BitVec.ofNat 32 384)
    ((Proof.AesGcm.X86.ctr_ct ⟨v, .scalar⟩ (E := SP) fun s ⟨s₀, h₀, run⟩ => call s₀ h₀ s run :
      CT _ (.frame (.push [.ebp, .edi, .ebx, .edx, .ecx, .eax]) (.call v.callee.name v.callee.code) (.pop .eax 6))))
    (fun s ⟨s₀, h₀, run⟩ => WP.mono (VG.Proof.AesCcm.X86.ctrFrame_ok v (call s₀ h₀ s run).1) fun s₁ g => by
      rw [g.saved .ebp (by decide), (call s₀ h₀ s run).1.ebp]) ?_
  exact CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Blocks`. -/
section

/-!
# AES-CCM on x86: `Ctr₀`, counter blocks and chaining a block

Untrusted: everything here is checked by Lean. `ctrs` zeroes the block at
`W + 48`, writes `q − 1 = 14 − n` to its first byte and copies the nonce
after it: `Ctr₀` (`ctrs_ok`). `ctrAt` makes `Ctrᵢ` at `W + 64` from `Ctr₀`
(`ctrAt_ok`); `updBlock y` chains the block `B` at `W + 32` into the MAC
state at `W + y` (`updBlock_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv LoopPre CopyPost copyLoop_ok zero4_fold zero4_bytes'
  length_bytesAt CT)

/-! ## `Ctr₀` -/

/-- `ctrs`'s block: `Ctr₀`'s first byte, and the copy's arguments. -/
theorem ctrsBlk_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {N : BitVec 32} {nl : Nat}
    (hNp : slotv s.mem W nonceO = N) (hnl : slotv s.mem W nlenO = BitVec.ofNat 32 nl) (h13 : nl ≤ 13) :
    ∃ s₁, runBlock isa
      (zero4 c0O ++ ([.mov .eax (imm 14), .alu .sub .eax (slot nlenO), .store8 (at_ .ebp c0O) .al,
        .mov .edi (slot nonceO), .mov .edx (.reg .ebp), .alu .add .edx (imm (c0O + 1)), .mov .ecx (slot nlenO)] : List Instr)) s =
        some s₁ ∧
      s₁.mem = (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 48)).writeW (w64 W + BitVec.ofNat 64 48)
        (BitVec.ofNat 8 (15 - nl - 1)) ∧
      s₁.gpr .edi = N ∧ s₁.gpr .edx = W + BitVec.ofNat 32 49 ∧ s₁.gpr .ecx = BitVec.ofNat 32 nl ∧
      s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have hz := zero4_fold s.mem W 48
  simp only [Nat.reduceAdd] at hz
  have hb := sub_low_byte32 (show nl ≤ 14 by omega)
  refine ⟨_, by crun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hnl, hNp], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hz, hb]
  · cregs [hNp]
  · cregs [E.ebp]
  · cregs [hnl]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals rfl

/-- `Ctr₀`, from the nonce `N` of `nl` bytes. -/
theorem ctrs_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {N : BitVec 32} {nl : Nat}
    (hNp : slotv s.mem W nonceO = N) (hnl : slotv s.mem W nlenO = BitVec.ofNat 32 nl) (hN : VG.Proof.AesCcm.X86.Buf W SP s N nl)
    (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    WP isa ctrs s fun s' => VG.Proof.AesCcm.X86.Env K W SP s' ∧ Frame [⟨w64 W + BitVec.ofNat 64 48, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, hm₁, hdi, hdx, hcx, hbp, hsp, hrd₁, hwr₁⟩ := VG.Proof.AesCcm.X86.ctrsBlk_ok L E hNp hnl h13
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  have a49 : w64 (W + BitVec.ofNat 32 49) = w64 W + BitVec.ofNat 64 49 := L.aW (by decide)
  have dNW : (⟨w64 N, nl⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 49, nl⟩ :=
    hN.w.sub_right (Lay.wSub (by omega))
  have lp : LoopPre s₁ N (W + BitVec.ofNat 32 49) nl :=
    ⟨hdi, hdx, hcx, by omega, by omega, hN.wrap, by rw [L.nW (by decide)]; have := L.fw; omega,
      by rw [hrd₁, hwr₁]; exact hN.rd, by rw [a49]; exact E₁.perm.wC (by omega), by rw [a49]; exact dNW⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s₂ P => ?_
  have hfz : Frame [⟨w64 W + BitVec.ofNat 64 48, 16⟩] s.mem s₁.mem := by
    rw [hm₁]
    exact (Cmac.frame_store4 _ _ _ _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 48) (n := 1) (e := 48) (k := 16) (by decide) (by decide) (by decide))
  have hNs : bytesAt s₁.mem (w64 N) nl = bytesAt s.mem (w64 N) nl :=
    Proof.AesGcm.X86.bytesAt_frame hfz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hN.w.sub_right (Lay.wSub (by decide))) (by have := hN.lt; omega)
  refine ⟨E₁.keep (by rw [P.other _ (by decide) (by decide) (by decide) (by decide)])
      (by rw [P.other _ (by decide) (by decide) (by decide) (by decide)]) P.rd P.wr, ?_, ?_,
    by rw [P.rd, hrd₁], by rw [P.wr, hwr₁]⟩
  · refine hfz.trans ?_
    rw [P.mem, a49]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains (w64 W) (d := 49) (n := nl) (e := 48) (k := 16) (by decide) (by omega) (by decide))
  · -- The bytes of the block.
    have hz' : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 48) 16 = BitVec.ofNat 8 (15 - nl - 1) :: Spec.Ccm.zeros 15 := by
      rw [hm₁, bytesAt_writeW8_base _ _ _ (by decide) (by decide), zero4_bytes']
      rfl
    have hl := length_bytesAt s.mem (w64 N) nl
    rw [P.mem, a49, show w64 W + BitVec.ofNat 64 49 = w64 W + BitVec.ofNat 64 48 + BitVec.ofNat 64 1 by
        rw [VG.Proof.AesCcm.X86.add_ofNat_assoc],
      bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega) (by decide), length_bytesAt, hz', hNs,
      Spec.Ccm.ctrBlock, hl, be_zero, show 1 + nl = nl + 1 by omega]
    simp only [Spec.Ccm.zeros, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_replicate,
      List.cons_append, List.nil_append]

/-! ## `ctrAt` -/

/-- Four words stored at `p + 64` (`Cmac.store4`), as the code stores them. -/
theorem store4_fold (m : Mem) (p : Addr) (d : Nat) (a b c e : BitVec 32) :
    (((m.writeW (p + BitVec.ofNat 64 d) a).writeW (p + BitVec.ofNat 64 (d + 4)) b).writeW
      (p + BitVec.ofNat 64 (d + 8)) c).writeW (p + BitVec.ofNat 64 (d + 12)) e =
      Cmac.store4 m (p + BitVec.ofNat 64 d) a b c e := by
  simp only [Cmac.store4, VG.Proof.AesCcm.X86.add_ofNat_assoc]

/-- A block as its four words. -/
theorem bytesAt_words (m : Mem) (p : Addr) (d : Nat) :
    bytesAt m (p + BitVec.ofNat 64 d) 16 = le4 (m.readW (p + BitVec.ofNat 64 d) 32) ++
      le4 (m.readW (p + BitVec.ofNat 64 (d + 4)) 32) ++ le4 (m.readW (p + BitVec.ofNat 64 (d + 8)) 32) ++
      le4 (m.readW (p + BitVec.ofNat 64 (d + 12)) 32) := by
  rw [Cmac.bytesAt_split4, VG.Proof.AesCcm.X86.add_ofNat_assoc, VG.Proof.AesCcm.X86.add_ofNat_assoc, VG.Proof.AesCcm.X86.add_ofNat_assoc, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW]

/-- `Ctrᵢ` at `W + 64`, for `i` in `eax`. -/
theorem ctrAt_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {i : Nat}
    (hi : i < 256 ^ (15 - nonce.length)) (hi32 : i < 2 ^ 32) (hax : s.gpr .eax = BitVec.ofNat 32 i) :
    ∃ s', runBlock isa ctrAt s = some s' ∧ Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hf := VG.Proof.AesCcm.X86.store4_fold s.mem (w64 W) 64 (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)
    (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32) (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)
    (bswap (BitVec.ofNat 32 i) ||| s.mem.readW (w64 W + BitVec.ofNat 64 60) 32)
  simp only [Nat.reduceAdd] at hf
  obtain ⟨s', run, hm, hg, hrd, hwr⟩ : ∃ s', runBlock isa ctrAt s = some s' ∧
      s'.mem = Cmac.store4 s.mem (w64 W + BitVec.ofNat 64 64) (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)
        (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32) (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)
        (bswap (BitVec.ofNat 32 i) ||| s.mem.readW (w64 W + BitVec.ofNat 64 60) 32) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by crun [ctrAt, E.ebp, L.aW, E.perm.wW, E.perm.wR], ?_, ?_, ?_, ?_⟩
    · cmems [hax, hf]
    · intro r a b; cregs [a, b]
    all_goals rfl
  refine ⟨s', run, by rw [hm]; exact Cmac.frame_store4 _ _ _ _ _, ?_, hg, hrd, hwr⟩
  have e := VG.Proof.AesCcm.X86.bytesAt_words s.mem (w64 W) 48
  simp only [Nat.reduceAdd] at e
  rw [hc0] at e
  have l12 : (le4 (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32) ++ le4 (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32) ++
      le4 (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)).length = 12 := by
    simp only [List.length_append, Proof.Cmac.length_le4]
  have hw : le4 (s.mem.readW (w64 W + BitVec.ofNat 64 60) 32) = (Spec.Ccm.ctrBlock nonce 0).drop 12 := by
    rw [e, List.drop_left' l12]
  rw [hm, Cmac.bytesAt_store4, show bswap (BitVec.ofNat 32 i) = byteRev32 (BitVec.ofNat 32 i) from rfl,
    ctr_or32 h7 h13 hw hi hi32]
  conv_rhs => rw [← List.take_append_drop 12 (Spec.Ccm.ctrBlock nonce i)]
  rw [ctrBlock_take12 h7 h13 hi32, e, List.take_left' l12]

/-! ## Chaining `B` -/

/-- The arguments of `updBlock y`'s call. -/
theorem updBlockArgs_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (y : Nat) :
    ∃ s₁, runBlock isa (keyArgs y ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm blkO), .mov .esi (imm 1)] : List Instr) ++ updScr) s =
      some s₁ ∧ s₁.mem = s.mem ∧ s₁.gpr .eax = K ∧ s₁.gpr .ecx = BitVec.ofNat 32 R ∧
      s₁.gpr .edx = W + BitVec.ofNat 32 y ∧ s₁.gpr .ebx = W + BitVec.ofNat 32 32 ∧ s₁.gpr .esi = BitVec.ofNat 32 1 ∧
      s₁.gpr .edi = W + BitVec.ofNat 32 384 ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by crun [keyArgs, updScr, E.ebp, L.aW, E.perm.wR, hK, hRo], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hK]
  · cregs [hRo]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs []
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals rfl

/-- `B` (at `W + 32`) chained into the MAC state at `W + y`. -/
theorem updBlock_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (updBlock v.callee v.suffix y) s fun s' => VG.Proof.AesCcm.X86.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 384, 2176⟩, below SP 56] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
          [bytesAt s.mem (w64 W + BitVec.ofNat 64 32) 16] := by
  obtain ⟨s₁, run₁, hm₁, hax, hcx, hdx, hbx, hsi, hdi, hbp, hsp, hrd₁, hwr₁⟩ := VG.Proof.AesCcm.X86.updBlockArgs_ok L E hK hRo y
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  have hq := VG.Proof.AesCcm.X86.srcW (s := s₁) L E₁.perm (t := 32) (k := 16 * 1) (by decide)
  have hqy : (⟨w64 (W + BitVec.ofNat 32 32), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ := by
    rw [L.aW (o := 32) (by decide)]
    rcases hy with rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine WP.mono (VG.Proof.AesCcm.X86.updCall_ok v L E₁ hR (by omega) hq hqy (by decide) hax hcx hdx hbx hsi hdi)
    fun s₂ ⟨E₂, rd₂, wr₂, _, f₂, o₂⟩ => ⟨E₂, by rw [rd₂, hrd₁], by rw [wr₂, hwr₁], by rw [← hm₁]; exact f₂, ?_⟩
  rw [o₂, Proof.Cmac.Stream.blocksAt_eq, Nat.mul_one, Proof.Cmac.Stream.blocks_single
    (Proof.Cmac.bytesAt_length _ _ _), hm₁, L.aW (o := 32) (by decide)]

/-- `updBlock y` is constant time. -/
theorem updBlock_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {I : State → Prop}
    (hI : ∀ s, I s → VG.Proof.AesCcm.X86.Env K W SP s ∧ slotv s.mem W ctxO = K ∧ slotv s.mem W roundsO = BitVec.ofNat 32 R) :
    CT I (updBlock v.callee v.suffix y) := by
  have hqy : (⟨w64 (W + BitVec.ofNat 32 32), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ := by
    rw [L.aW (o := 32) (by decide)]
    rcases hy with rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine CT.seq (J := fun s₁ => ∃ s, I s ∧ s₁.mem = s.mem ∧ s₁.gpr .eax = K ∧ s₁.gpr .ecx = BitVec.ofNat 32 R ∧
      s₁.gpr .edx = W + BitVec.ofNat 32 y ∧ s₁.gpr .ebx = W + BitVec.ofNat 32 32 ∧ s₁.gpr .esi = BitVec.ofNat 32 1 ∧
      s₁.gpr .edi = W + BitVec.ofNat 32 384 ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr)
    (by
      have hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [(hI _ h₁).1.ebp, (hI _ h₂).1.ebp]
      rcases hy with rfl | rfl
      · exact CT.taint [.ebp] hr (by taint_decide)
      · exact CT.taint [.ebp] hr (by taint_decide))
    (fun s hs => by
      obtain ⟨E, hK, hRo⟩ := hI s hs
      obtain ⟨s₁, run₁, h⟩ := VG.Proof.AesCcm.X86.updBlockArgs_ok L E hK hRo y
      exact WP.of_runBlock ⟨s₁, run₁, s, hs, h⟩) ?_
  refine VG.Proof.AesCcm.X86.updCall_ct v L hR (y := y) (Q := W + BitVec.ofNat 32 32) (n := 1)
    (by rcases hy with rfl | rfl <;> decide) (by decide) fun s₁ ⟨s, hs, _, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ => ?_
  have E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁ := ⟨bp, sp, (hI s hs).1.perm.of_eq rd wr⟩
  exact ⟨E₁, VG.Proof.AesCcm.X86.srcW L E₁.perm (by decide), hqy, ax, cx, dx, bx, si, di⟩

/-- `ctrs` is constant time. -/
theorem ctrs_ct {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {N : BitVec 32} {nl : Nat} (h13 : nl ≤ 13) {I : State → Prop}
    (hI : ∀ s, I s → VG.Proof.AesCcm.X86.Env K W SP s ∧ slotv s.mem W nonceO = N ∧ slotv s.mem W nlenO = BitVec.ofNat 32 nl) :
    CT I ctrs :=
  CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun s h => (hI s h).1.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesCcm.X86.ctrsBlk_ok L (hI s hs).1 (hI s hs).2.1 (hI s hs).2.2 h13)
    (Proof.AesGcm.X86.copyLoop_ct (VG.Proof.AesCcm.X86.pin3 fun _ ⟨_, _, _, hdi, hdx, hcx, _⟩ => ⟨hdi, hdx, hcx⟩))

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Absorb`. -/
section

/-!
# AES-CCM on x86: a buffer padded, chained (`absorbPad y`)

Untrusted: everything here is checked by Lean. `absorbPad y` chains the
`len` bytes at `P` (kept at `W + dO`, `len` at `W + nO`), padded with zeros
to whole blocks, into the MAC state at `W + y`: its whole blocks in one call
of `vg_cmac_aes_update` (`absorbWhole_ok`), then its last `len mod 16` bytes
copied into the zeroed block `B` (`absorbTail_ok`); together, the blocks of
the padded string (`absorbPad_ok`, `Proof.AesCcm.blocks_pad16`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4 splitWhole dO nO)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold length_bytesAt WEnv padLoop_ok shr4 and15
  ofNat_sub32 and_self_beq32)

/-! ## What the pieces write -/

/-- What chaining into `W + y` writes: the state, `B`, `[240, 2560)` (the
arguments of the piece running and the working space of the functions
called) and the stack below `SP`. -/
abbrev macR (W SP : BitVec 32) (y : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 32, 16⟩, VG.Proof.AesCcm.X86.wC W, below SP 56]

theorem sub_mac {W SP : BitVec 32} {y : Nat} {r : Region} (hr : r ∈ VG.Proof.AesCcm.X86.macR W SP y) :
    ∃ r' ∈ VG.Proof.AesCcm.X86.macR W SP y, Region.Sub r r' := ⟨r, hr, fun _ h => h⟩

/-- `[o, o + 4)` of `W`, for `112 ≤ o` and `o + 4 ≤ 240`, is kept. -/
theorem slot_kept {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {y : Nat} (hy : y = 0 ∨ y = 96) {m m' : Mem}
    (hf : Frame (VG.Proof.AesCcm.X86.macR W SP y) m m') {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 240) : slotv m' W o = slotv m W o :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
      · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
    · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.stk_w' (by omega)).symm) (by decide)

/-- A buffer missing `W` and the stack below `SP` keeps its bytes. -/
theorem buf_kept {W SP : BitVec 32} {s : State} {P : BitVec 32} {len : Nat} (hP : VG.Proof.AesCcm.X86.Buf W SP s P len) {y : Nat}
    (hy : y + 16 ≤ 2560) {m m' : Mem} (hf : Frame (VG.Proof.AesCcm.X86.macR W SP y) m m') :
    bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub hy)
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

theorem k_macR {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {y : Nat} (hy : y + 16 ≤ 2560) :
    ∀ r ∈ VG.Proof.AesCcm.X86.macR W SP y, (⟨w64 K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Lay.wSub hy)
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.stk_k.symm

/-- The cipher of a key schedule outside a frame's regions. -/
theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : BitVec 32}
    (hd : ∀ r ∈ rs, (⟨w64 K, 240⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Ccm.ctxCiph m' (w64 K) R = Spec.Ccm.ctxCiph m (w64 K) R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

/-- What `absorbPad`'s pieces keep: the environment, and what they write. -/
structure Absorbed (K W SP : BitVec 32) (s : State) (y : Nat) (Y : List Byte) (s' : State) : Prop where
  env : VG.Proof.AesCcm.X86.Env K W SP s'
  frame : Frame (VG.Proof.AesCcm.X86.macR W SP y) s.mem s'.mem
  out : bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-! ## Splitting off the whole blocks -/

/-- `splitWhole`, from the slots `dO = P` and `nO = r`: `ebx = P`,
`edi = r / 16` whole blocks, and the slots the rest; ZF is set if there are
none. -/
theorem split_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {P : BitVec 32} {r : Nat}
    (hd : slotv s.mem W dO = P) (hn : slotv s.mem W nO = BitVec.ofNat 32 r) (hr : r < 2 ^ 32) :
    ∃ s', runBlock isa splitWhole s = some s' ∧ s'.gpr .ebx = P ∧ s'.gpr .edi = BitVec.ofNat 32 (r / 16) ∧
      s'.zf = some (decide (r / 16 = 0)) ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧
      s'.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 (r % 16))).writeW
        (w64 W + BitVec.ofNat 64 dO) (P + BitVec.ofNat 32 (16 * (r / 16))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsh := VG.Proof.AesGcm.X86.shr4 hr
  have hand := VG.Proof.AesGcm.X86.and15 (BitVec.ofNat 32 r)
  rw [VG.Proof.AesGcm.X86.toNat_ofNat32 hr] at hand
  have h16 : BitVec.ofNat 32 r - BitVec.ofNat 32 (r % 16) = BitVec.ofNat 32 (16 * (r / 16)) := by
    rw [ofNat_sub32 (Nat.mod_le _ _) hr]; congr 1; omega
  refine ⟨_, by crun [splitWhole, E.ebp, L.aW, E.perm.wW, E.perm.wR, hd, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cregs [hd]
  · cregs [hn, hsh]
  · cmems [hn, hsh]; rw [and_self_beq32 (by omega)]
  · cregs [E.ebp]
  · cregs [E.esp]
  · cmems [hn, hd, hsh, hand, h16]
    rw [BitVec.add_comm (BitVec.ofNat 32 (16 * (r / 16)))]
  all_goals cmems []

/-- The arguments of the call chaining the whole blocks. -/
theorem wholeArgs_ok {K W SP : BitVec 32} {s₁ : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁) {R : Nat}
    (hK₁ : slotv s₁.mem W ctxO = K) (hR₁ : slotv s₁.mem W roundsO = BitVec.ofNat 32 R) {P : BitVec 32} {b : Nat}
    (hbx : s₁.gpr .ebx = P) (hdi : s₁.gpr .edi = BitVec.ofNat 32 b) (y : Nat) :
    ∃ s₂, runBlock isa (keyArgs y ++ ([.mov .esi (.reg .edi)] : List Instr) ++ updScr) s₁ = some s₂ ∧
      s₂.mem = s₁.mem ∧ s₂.gpr .eax = K ∧ s₂.gpr .ecx = BitVec.ofNat 32 R ∧ s₂.gpr .edx = W + BitVec.ofNat 32 y ∧
      s₂.gpr .ebx = P ∧ s₂.gpr .esi = BitVec.ofNat 32 b ∧
      s₂.gpr .edi = W + BitVec.ofNat 32 384 ∧ s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
  have hbp := E₁.ebp
  refine ⟨_, by crun [keyArgs, updScr, hbp, L.aW, E₁.perm.wR, hK₁, hR₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hK₁]
  · cregs [hR₁]
  · cregs [hbp]
  · cregs [hbx]
  · cregs [hdi]
  · cregs [hbp]
  · cregs [hbp]
  · cregs [E₁.esp]
  all_goals rfl

/-- The slots `splitWhole` does not write are kept. -/
theorem split_kept {W : BitVec 32} {m m' : Mem} {a b : BitVec 32}
    (hm : m' = (m.writeW (w64 W + BitVec.ofNat 64 nO) a).writeW (w64 W + BitVec.ofNat 64 dO) b) {o : Nat}
    (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 240) : slotv m' W o = slotv m W o := by
  have f₁ : Frame [VG.Proof.AesCcm.X86.wC W] m m' := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
  exact f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
    (by decide)

/-! ## The whole blocks -/

/-- The whole blocks of the string at `P` (kept at `W + dO`, its length at
`W + nO`), chained into `W + y`; `dO` and `nO` then the rest. -/
theorem absorbWhole_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : BitVec 32} {len : Nat} (hP : 0 < len → VG.Proof.AesCcm.X86.Buf W SP s P len)
    (hl : len < 2 ^ 32) (hd : slotv s.mem W dO = P) (hn : slotv s.mem W nO = BitVec.ofNat 32 len) :
    WP isa (.seq (.block splitWhole)
        (.ite .e (.block []) (.seq (.block (keyArgs y ++ ([.mov .esi (.reg .edi)] : List Instr) ++ updScr)) (updCall v.callee v.suffix))))
      s fun s' => VG.Proof.AesCcm.X86.Absorbed K W SP s y
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
          (Spec.Cmac.blocks 16 ((bytesAt s.mem (w64 P) len).take (16 * (len / 16))))) s' ∧
        slotv s'.mem W dO = P + BitVec.ofNat 32 (16 * (len / 16)) ∧
        slotv s'.mem W nO = BitVec.ofNat 32 (len % 16) := by
  obtain ⟨s₁, run₁, hbx, hdi, hzf, hbp, hsp, hm₁, hrd₁, hwr₁⟩ := VG.Proof.AesCcm.X86.split_ok L E hd hn hl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  have f₁ : Frame [VG.Proof.AesCcm.X86.wC W] s.mem s₁.mem := by
    rw [hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
  have k₁ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
      (by decide)
  have hd₁ : slotv s₁.mem W dO = P + BitVec.ofNat 32 (16 * (len / 16)) := by
    rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _
  have hn₁ : slotv s₁.mem W nO = BitVec.ofNat 32 (len % 16) := by
    rw [hm₁, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  have hY₁ : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16 :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl <;> exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hc₁ : Spec.Ccm.ctxCiph s₁.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    VG.Proof.AesCcm.X86.ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  have fm : Frame (VG.Proof.AesCcm.X86.macR W SP y) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.X86.sub_mac (by simp)
  refine WP.ite (decide (len / 16 = 0)) (VG.Proof.AesCcm.X86.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len / 16 = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨s₁, rfl, ⟨E₁, fm, ?_, hrd₁, hwr₁⟩, hd₁, hn₁⟩
    rw [hY₁, h0, Nat.mul_zero, List.take_zero]; rfl
  · have h0 : len / 16 ≠ 0 := of_decide_eq_false hf
    have hP := hP (by omega)
    have hP₁ : bytesAt s₁.mem (w64 P) len = bytesAt s.mem (w64 P) len :=
      Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
        (by have := hP.lt; omega)
    obtain ⟨s₂, run₂, hm₂, hax, hcx, hdx, hbx₂, hsi, hdi₂, hbp₂, hsp₂, hrd₂, hwr₂⟩ :=
      VG.Proof.AesCcm.X86.wholeArgs_ok L E₁ (by rw [k₁ _ (by decide) (by decide)]; exact hK) (by rw [k₁ _ (by decide) (by decide)]; exact hRo)
        hbx hdi y
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have E₂ : VG.Proof.AesCcm.X86.Env K W SP s₂ := E₁.keep (by rw [hbp₂, hbp]) (by rw [hsp₂, hsp]) hrd₂ hwr₂
    have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
    have hq := VG.Proof.AesCcm.X86.srcBuf ((hP.take hb).of_eq (s' := s₂) (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁]))
    have hqy : (⟨w64 P, 16 * (len / 16)⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ :=
      (hP.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by omega))
    refine WP.mono (VG.Proof.AesCcm.X86.updCall_ok v L E₂ hR (by omega) hq hqy (by omega) hax hcx hdx hbx₂ hsi hdi₂)
      fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, o₃⟩ => ⟨⟨E₃, fm.trans ?_, ?_, by rw [rd₃, hrd₂, hrd₁], by rw [wr₃, hwr₂, hwr₁]⟩, ?_, ?_⟩
    · rw [← hm₂]
      exact f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact VG.Proof.AesCcm.X86.sub_mac (by simp)
        · exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
        · exact VG.Proof.AesCcm.X86.sub_mac (by simp)
    · rw [o₃, Proof.Cmac.Stream.blocksAt_eq, hm₂, hY₁, hc₁, Proof.AesCcm.bytesAt_prefix _ _ hb, hP₁]
    · have k : slotv s₃.mem W dO = slotv s₂.mem W dO :=
        f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 dO, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rcases hy with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
          · exact (L.stk_w' (by decide)).symm) (by decide)
      rw [k, hm₂, hd₁]
    · have k : slotv s₃.mem W nO = slotv s₂.mem W nO :=
        f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 nO, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rcases hy with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
          · exact (L.stk_w' (by decide)).symm) (by decide)
      rw [k, hm₂, hn₁]

/-- `[mov ecx [nO], test ecx ecx]`: ZF is whether `nO` holds 0. -/
theorem testN_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {r : Nat} (hr : r < 2 ^ 32)
    (hn : slotv s.mem W nO = BitVec.ofNat 32 r) :
    ∃ s₁, runBlock isa [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.zf = some (decide (r = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hn], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cmems [hn]; rw [and_self_beq32 hr]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- The arguments of the copy of the last bytes into the zeroed `B`. -/
theorem tailArgs_ok {K W SP : BitVec 32} {s₁ : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁) {Q : BitVec 32} {t : Nat}
    (hd₁ : slotv s₁.mem W dO = Q) (hn₁ : slotv s₁.mem W nO = BitVec.ofNat 32 t) :
    ∃ s₂, runBlock isa
        (zero4 blkO ++ ([.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm blkO), .mov .ecx (slot nO)] : List Instr))
          s₁ = some s₂ ∧ s₂.mem = Cmac.zero4 s₁.mem (w64 W + BitVec.ofNat 64 32) ∧
        s₂.gpr .edi = Q ∧ s₂.gpr .edx = W + BitVec.ofNat 32 32 ∧ s₂.gpr .ecx = BitVec.ofNat 32 t ∧
        s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
  have hbp := E₁.ebp
  have hz := zero4_fold s₁.mem W 32
  simp only [Nat.reduceAdd] at hz
  refine ⟨_, by crun [zero4, hbp, L.aW, E₁.perm.wW, E₁.perm.wR, hd₁, hn₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hz]
  · cregs [hd₁]
  · cregs [hbp]
  · cregs [hn₁]
  · cregs [hbp]
  · cregs [E₁.esp]
  all_goals cmems []

/-! ## The last bytes -/

/-- The last `t < 16` bytes, at `Q` (kept at `W + dO`, `t` at `W + nO`),
padded with zeros in `B` and chained into `W + y`, if there are any. -/
theorem absorbTail_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {Q : BitVec 32} {t : Nat} (ht : t < 16) (hd : slotv s.mem W dO = Q)
    (hn : slotv s.mem W nO = BitVec.ofNat 32 t) (hQ : 0 < t → VG.Proof.AesCcm.X86.Buf W SP s Q t) :
    WP isa (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
        (.ite .e (.block [])
          (.seq (.block (zero4 blkO ++ ([.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm blkO),
              .mov .ecx (slot nO)] : List Instr)))
            (.seq copyLoop (updBlock v.callee v.suffix y)))))
      s (VG.Proof.AesCcm.X86.Absorbed K W SP s y
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
          (if t = 0 then [] else [bytesAt s.mem (w64 Q) t ++ Spec.Ccm.zeros (16 - t)]))) := by
  obtain ⟨s₁, run₁, hm₁, hzf, hbp, hsp, hrd₁, hwr₁⟩ := VG.Proof.AesCcm.X86.testN_ok L E (r := t) (by omega) hn
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  refine WP.ite (decide (t = 0)) (VG.Proof.AesCcm.X86.eval_e hzf) (fun h => ?_) (fun h => ?_)
  · have h0 : t = 0 := of_decide_eq_true h
    refine WP.of_runBlock ⟨s₁, rfl, E₁, by rw [hm₁]; exact Frame.refl _ _, ?_, hrd₁, hwr₁⟩
    simp only [hm₁, h0, ↓reduceIte]; rfl
  · have h0 : t ≠ 0 := of_decide_eq_false h
    have hB := hQ (by omega)
    obtain ⟨s₂, run₂, hm₂, hdi, hdx, hcx, hbp₂, hsp₂, hrd₂, hwr₂⟩ :=
      VG.Proof.AesCcm.X86.tailArgs_ok L E₁ (Q := Q) (t := t) (by rw [hm₁]; exact hd) (by rw [hm₁]; exact hn)
    rw [hm₁] at hm₂
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he : WEnv W s₂ := ⟨hbp₂, by rw [hwr₂, hwr₁]; exact E.perm.w, L.fw⟩
    have sd : (⟨w64 Q, t⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 32, 16⟩ := hB.w.sub_right (Lay.wSub (by decide))
    refine WP.seq (WP.mono (padLoop_ok (S := Q) (d := 32) (t := t) (m := s.mem) he hm₂ hdi hdx hcx (by omega)
      (by omega) (by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact hB.rd) hB.wrap sd (by decide))
      fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
    have E₃ : VG.Proof.AesCcm.X86.Env K W SP s₃ := ⟨by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hbp₂],
      by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hsp₂],
      E.perm.of_eq (by rw [rd₃, hrd₂, hrd₁]) (by rw [wr₃, hwr₂, hwr₁])⟩
    have k₃ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
      f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
        (by decide)
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    refine WP.mono (VG.Proof.AesCcm.X86.updBlock_ok v L E₃ hR (by rw [k₃ _ (by decide) (by decide)]; exact hK)
      (by rw [k₃ _ (by decide) (by decide)]; exact hRo) hy)
      fun s₄ ⟨E₄, rd₄, wr₄, f₄, o₄⟩ => ⟨E₄, ?_, ?_, by rw [rd₄, rd₃, hrd₂, hrd₁], by rw [wr₄, wr₃, hwr₂, hwr₁]⟩
    · refine (f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.X86.sub_mac (by simp)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact VG.Proof.AesCcm.X86.sub_mac (by simp)
        · exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
        · exact VG.Proof.AesCcm.X86.sub_mac (by simp)
    · have hY₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16 :=
        Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rcases hy with rfl | rfl
          · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
          · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
      rw [o₄, hY₃, b₃, VG.Proof.AesCcm.X86.ctxCiph_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb]
      simp only [h0, ↓reduceIte]
      rfl

/-! ## The padded string -/

/-- The `len` bytes at `P` (kept at `W + dO`, `len` at `W + nO`), padded with
zeros to whole blocks, chained into the MAC state at `W + y`. -/
theorem absorbPad_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : BitVec 32} {len : Nat} (hP : 0 < len → VG.Proof.AesCcm.X86.Buf W SP s P len)
    (hl : len < 2 ^ 32) (hd : slotv s.mem W dO = P) (hn : slotv s.mem W nO = BitVec.ofNat 32 len) :
    WP isa (absorbPad v.callee v.suffix y) s (VG.Proof.AesCcm.X86.Absorbed K W SP s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem (w64 P) len))))) := by
  refine VG.Proof.AesCcm.X86.seq_assoc (WP.seq (WP.mono (VG.Proof.AesCcm.X86.absorbWhole_ok v L E hR hK hRo hy hP hl hd hn) fun s₁ ⟨A₁, hd₁, hn₁⟩ => ?_))
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  have hQ : 0 < len % 16 → VG.Proof.AesCcm.X86.Buf W SP s₁ (P + BitVec.ofNat 32 (16 * (len / 16))) (len % 16) := fun h => by
    have hP := hP (by omega)
    have := (hP.drop hb (by have := hP.wrap; omega)).of_eq A₁.rd A₁.wr
    rwa [show len - 16 * (len / 16) = len % 16 by omega] at this
  refine WP.mono (VG.Proof.AesCcm.X86.absorbTail_ok v L A₁.env hR (by rw [VG.Proof.AesCcm.X86.slot_kept L hy A₁.frame (by decide) (by decide)]; exact hK)
    (by rw [VG.Proof.AesCcm.X86.slot_kept L hy A₁.frame (by decide) (by decide)]; exact hRo) hy (Nat.mod_lt _ (by decide)) hd₁ hn₁ hQ)
    fun s₂ A₂ => ⟨A₂.env, A₁.frame.trans A₂.frame, ?_, A₂.rd.trans A₁.rd, A₂.wr.trans A₁.wr⟩
  rw [A₂.out, A₁.out, VG.Proof.AesCcm.X86.ctxCiph_frame A₁.frame (VG.Proof.AesCcm.X86.k_macR L (by omega)) hRb, ← Proof.Cmac.chain_append,
    Proof.AesCcm.blocks_pad16, length_bytesAt]
  congr 2
  by_cases h0 : len % 16 = 0
  · simp only [h0, ↓reduceIte]
  · simp only [h0, ↓reduceIte, List.cons.injEq, and_true]
    have hP := hP (by omega)
    have hw : P.toNat + 16 * (len / 16) < 2 ^ 32 := by have := hP.wrap; omega
    have e : bytesAt s₁.mem (w64 (P + BitVec.ofNat 32 (16 * (len / 16)))) (len % 16) =
        (bytesAt s.mem (w64 P) len).drop (16 * (len / 16)) := by
      rw [show len % 16 = len - 16 * (len / 16) by omega, VG.Proof.AesCcm.X86.buf_kept (hP.drop hb hw) (by omega) A₁.frame, Buf.ptr hw,
        Proof.AesCcm.bytesAt_suffix _ _ hb]
    rw [e]

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Aad`. -/
section

/-!
# AES-CCM on x86: the associated data (`header`, `aadHead y`, `aad y`)

Untrusted: everything here is checked by Lean. `header` zeroes `B` and
writes the encoding of the length `a < 2³²` of the associated data (kept at
`W + nO`) to its start, and its length `h` (2 or 6) to `W + bO`
(`header_ok`); `aadHead y` copies the first `min (a, 16 − h)` bytes of the
associated data after it and chains the block (`aadHead_ok`); `aad y` does
that and chains the rest of the associated data, padded, if there is any
(`aad_ok`): the blocks `Proof.AesCcm.adataBlocks`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4 minLen dO nO bO)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold zero4_bytes' length_bytesAt LoopPre
  CopyPost copyLoop_ok ofNat_sub32 and_self_beq32 ofNat16_sub)
open VG.Proof.AesCcm (hdrLen headLen adataBlocks)

/-! ## `minLen` -/

theorem minLen1_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {n b : Nat}
    (hn : slotv s.mem W nO = BitVec.ofNat 32 n) (hb : slotv s.mem W bO = BitVec.ofNat 32 b) (hb16 : b ≤ 16)
    (hnlt : n < 2 ^ 32) :
    ∃ s₁, runBlock isa
      [.mov .ecx (imm 16), .alu .sub .ecx (slot bO), .mov .eax (slot nO), .alu .cmp .eax (.reg .ecx)] s = some s₁ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 (16 - b) ∧ s₁.gpr .eax = BitVec.ofNat 32 n ∧
      s₁.cf = some (decide (n < 16 - b)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have e16 := ofNat16_sub hb16
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hn, hb], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cregs [e16]
  · cregs []
  · cmems [e16, VG.Proof.AesGcm.X86.toNat_ofNat32 hnlt, VG.Proof.AesGcm.X86.toNat_ofNat32 (show 16 - b < 2 ^ 32 by omega)]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []


/-- `ecx := min (16 − b, n)`, for `n` at `W + nO` and `b` at `W + bO`. -/
theorem minLen_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {n b : Nat}
    (hn : slotv s.mem W nO = BitVec.ofNat 32 n) (hb : slotv s.mem W bO = BitVec.ofNat 32 b) (hb16 : b ≤ 16)
    (hnlt : n < 2 ^ 32) :
    WP isa minLen s fun s' => s'.gpr .ecx = BitVec.ofNat 32 (min (16 - b) n) ∧ s'.gpr .ebp = W ∧
      s'.gpr .esp = SP ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, cx, ax, cf, bp, sp, m₁, rd₁, wr₁⟩ := VG.Proof.AesCcm.X86.minLen1_ok L E hn hb hb16 hnlt
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n < 16 - b)) (VG.Proof.AesCcm.X86.eval_b cf) (fun ht => ?_) (fun hf => ?_)
  · have hlt : n < 16 - b := by simpa using ht
    refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cregs [ax]; congr 1; omega
    · cregs [bp]
    · cregs [sp]
    all_goals cmems [m₁, rd₁, wr₁]
  · have hle : ¬ n < 16 - b := by simpa using hf
    exact WP.block_nil ⟨by rw [cx]; congr 1; omega, bp, sp, m₁, rd₁, wr₁⟩

/-! ## The encoding of the length -/

theorem headerBlk_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {a : Nat} (ha : a < 2 ^ 32)
    (hn : slotv s.mem W nO = BitVec.ofNat 32 a) :
    ∃ s₁, runBlock isa
      (zero4 blkO ++ ([.mov .eax (slot nO), .alu .cmp .eax (imm 0xff00)] : List Instr)) s = some s₁ ∧
      s₁.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 32) ∧ s₁.gpr .eax = BitVec.ofNat 32 a ∧
      s₁.cf = some (decide (a < 2 ^ 16 - 2 ^ 8)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have hz := zero4_fold s.mem W 32
  simp only [Nat.reduceAdd] at hz
  refine ⟨_, by crun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hz]
  · cregs [hn]
  · cmems [hn, VG.Proof.AesGcm.X86.toNat_ofNat32 ha]; rfl
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []


/-- `B` zeroed, then the encoding of the length `a` (at `W + nO`) of the
associated data at its start, and its length at `W + bO`. -/
theorem header_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {a : Nat} (ha : a < 2 ^ 32)
    (hn : slotv s.mem W nO = BitVec.ofNat 32 a) :
    WP isa header s fun s' => VG.Proof.AesCcm.X86.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩, ⟨w64 W + BitVec.ofNat 64 bO, 4⟩] s.mem s'.mem ∧
      slotv s'.mem W bO = BitVec.ofNat 32 (hdrLen a) ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 32) 16 = Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  obtain ⟨s₁, run₁, hm₁, hax, hcf₁, hbp, hsp, hrd₁, hwr₁⟩ := VG.Proof.AesCcm.X86.headerBlk_ok L E ha hn
  have hz' : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by rw [hm₁, zero4_bytes']; rfl
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩, ⟨w64 W + BitVec.ofNat 64 bO, 4⟩] s.mem s₁.mem := by
    rw [hm₁]; exact (Cmac.frame_store4 _ _ _ _ _).mono (by simp)
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 →
      (⟨w64 W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (w64 W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains (w64 W) h₁ (by omega) (by decide)
  have cO : (⟨w64 W + BitVec.ofNat 64 bO, 4⟩ : Region).Contains (w64 W + BitVec.ofNat 64 280) 4 :=
    Region.contains_self _ _
  have E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (a < 2 ^ 16 - 2 ^ 8)) (VG.Proof.AesCcm.X86.eval_b hcf₁) (fun ht => ?_) (fun hf => ?_)
  · -- `[a]₁₆`.
    have h₁ := of_decide_eq_true ht
    refine WP.of_runBlock ⟨_, by crun [hbp, L.aW, E₁.perm.wW], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact E₁.keep (by cregs []) (by cregs []) (by cmems []) (by cmems [])
    · cmems [hrd₁]
    · cmems [hwr₁]
    · cmems []
      exact (fz.writeW (List.mem_cons_self) _ (cB 32 4 (by decide) (by decide))).writeW
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ cO
    · cmems []; rw [hdrLen_lo h₁]
    · cmems [hax]
      rw [Proof.AesGcm.X86.bytesAt_frame (rs := [⟨w64 W + BitVec.ofNat 64 280, 4⟩])
          ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
          (by decide),
        bytesAt_writeW32_base _ _ _ (by decide) (by decide), hz', show bswap (BitVec.ofNat 32 a) =
          byteRev32 (BitVec.ofNat 32 a) from rfl, ← enc_lo32 h₁]
      rfl
  · -- `0xff ‖ 0xfe ‖ [a]₃₂`.
    have h₁ := of_decide_eq_false hf
    refine WP.of_runBlock ⟨_, by crun [hbp, L.aW, E₁.perm.wW], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact E₁.keep (by cregs []) (by cregs []) (by cmems []) (by cmems [])
    · cmems [hrd₁]
    · cmems [hwr₁]
    · cmems []
      exact ((fz.writeW (List.mem_cons_self) _ (cB 32 4 (by decide) (by decide))).writeW
        (List.mem_cons_self) _ (cB 34 4 (by decide) (by decide))).writeW
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ cO
    · cmems []; rw [hdrLen_mid h₁ ha]
    · cmems [hax]
      rw [Proof.AesGcm.X86.bytesAt_frame (rs := [⟨w64 W + BitVec.ofNat 64 280, 4⟩])
          ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
          (by decide),
        show w64 W + BitVec.ofNat 64 34 = w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 2 by rw [VG.Proof.AesCcm.X86.add_ofNat_assoc],
        bytesAt_writeW32_at _ _ _ (by decide) (by decide), bytesAt_writeW32_base _ _ _ (by decide) (by decide), hz',
        show bswap (BitVec.ofNat 32 a) = byteRev32 (BitVec.ofNat 32 a) from rfl, ← enc_mid32 h₁ ha]
      rfl

/-! ## The first block of the associated data -/

theorem aadHeadArgs_ok {K W SP : BitVec 32} {s₂ : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E₂ : VG.Proof.AesCcm.X86.Env K W SP s₂) {A : BitVec 32}
    {a k b : Nat} (hd₂ : slotv s₂.mem W dO = A) (hn₂ : slotv s₂.mem W nO = BitVec.ofNat 32 a)
    (hb₂ : slotv s₂.mem W bO = BitVec.ofNat 32 b) (hcx₂ : s₂.gpr .ecx = BitVec.ofNat 32 k) (hk : k ≤ a)
    (ha : a < 2 ^ 32) :
    ∃ s₃, runBlock isa
      [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm blkO), .alu .add .edx (slot bO),
        .mov .eax (slot nO), .alu .sub .eax (.reg .ecx), .store (at_ .ebp nO) .eax,
        .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store (at_ .ebp dO) .eax] s₂ = some s₃ ∧
      s₃.mem = (s₂.mem.writeW (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 (a - k))).writeW
        (w64 W + BitVec.ofNat 64 dO) (A + BitVec.ofNat 32 k) ∧
      s₃.gpr .edi = A ∧ s₃.gpr .edx = W + BitVec.ofNat 32 (32 + b) ∧
      s₃.gpr .ecx = BitVec.ofNat 32 k ∧ s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
  have hbp₂ := E₂.ebp
  have eh : W + BitVec.ofNat 32 32 + BitVec.ofNat 32 b = W + BitVec.ofNat 32 (32 + b) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have es : BitVec.ofNat 32 a - BitVec.ofNat 32 k = BitVec.ofNat 32 (a - k) := ofNat_sub32 hk ha
  refine ⟨_, by crun [hbp₂, L.aW, E₂.perm.wW, E₂.perm.wR, hd₂, hn₂, hb₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hd₂, hn₂, hcx₂, es]
  · cregs [hd₂]
  · cregs [hbp₂, eh]
  · cregs [hcx₂]
  · cregs [hbp₂]
  · cregs [E₂.esp]
  all_goals cmems []


/-- The first block of the associated data (`a` bytes at `A`, kept at
`W + dO`, `a` at `W + nO`), chained into `W + y`; `dO` and `nO` then the
rest. -/
theorem aadHead_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : BitVec 32} {a : Nat} (hA : VG.Proof.AesCcm.X86.Buf W SP s A a) (ha0 : 0 < a) (ha : a < 2 ^ 32)
    (hd : slotv s.mem W dO = A) (hn : slotv s.mem W nO = BitVec.ofNat 32 a) :
    WP isa (aadHead v.callee v.suffix y) s fun s' => VG.Proof.AesCcm.X86.Absorbed K W SP s y
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
          [Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem (w64 A) a).take (headLen a))]) s' ∧
        slotv s'.mem W dO = A + BitVec.ofNat 32 (headLen a) ∧
        slotv s'.mem W nO = BitVec.ofNat 32 (a - headLen a) := by
  have hh := Proof.AesCcm.hdrLen_le a
  have hh2 : 2 ≤ hdrLen a := by unfold hdrLen; split <;> (try split) <;> omega
  have hh6 : hdrLen a ≤ 6 := by unfold hdrLen; split <;> (try split) <;> omega
  have hn1 : 1 ≤ headLen a ∧ headLen a ≤ a ∧ hdrLen a + headLen a ≤ 16 := by unfold headLen; omega
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.header_ok L E ha hn) fun s₁ ⟨E₁, hrd₁, hwr₁, f₁, hb₁, hB₁⟩ => ?_)
  have k₁ : ∀ o, (112 ≤ o ∧ o + 4 ≤ 280 ∨ 284 ≤ o ∧ o + 4 ≤ 2560) → slotv s₁.mem W o = slotv s.mem W o :=
    fun o ho => f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
      · exact Lay.w_w (by simp only [bO]; omega) (by omega) (by decide)) (by decide)
  have hn₁ : slotv s₁.mem W nO = BitVec.ofNat 32 a := by rw [k₁ _ (by decide)]; exact hn
  have hd₁ : slotv s₁.mem W dO = A := by rw [k₁ _ (by decide)]; exact hd
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.minLen_ok L E₁ hn₁ hb₁ (by omega) ha) fun s₂ ⟨hcx₂, hbp₂, hsp₂, hm₂, hrd₂, hwr₂⟩ => ?_)
  rw [show min (16 - hdrLen a) a = headLen a by unfold headLen; omega] at hcx₂
  have hn₂ : slotv s₂.mem W nO = BitVec.ofNat 32 a := by rw [hm₂]; exact hn₁
  have hd₂ : slotv s₂.mem W dO = A := by rw [hm₂]; exact hd₁
  have hb₂ : slotv s₂.mem W bO = BitVec.ofNat 32 (hdrLen a) := by rw [hm₂]; exact hb₁
  obtain ⟨s₃, run₃, hm₃, hdi, hdx, hcx₃, hbp₃, hsp₃, hrd₃, hwr₃⟩ :=
    VG.Proof.AesCcm.X86.aadHeadArgs_ok L ⟨hbp₂, hsp₂, E₁.perm.of_eq hrd₂ hwr₂⟩ hd₂ hn₂ hb₂ hcx₂ hn1.2.1 ha
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : VG.Proof.AesCcm.X86.Env K W SP s₃ := ⟨hbp₃, hsp₃, E.perm.of_eq (by rw [hrd₃, hrd₂, hrd₁]) (by rw [hwr₃, hwr₂, hwr₁])⟩
  have hA₃ := hA.of_eq (s' := s₃) (by rw [hrd₃, hrd₂, hrd₁]) (by rw [hwr₃, hwr₂, hwr₁])
  have aB : w64 (W + BitVec.ofNat 32 (32 + hdrLen a)) = w64 W + BitVec.ofNat 64 (32 + hdrLen a) := L.aW (by omega)
  have dAB : (⟨w64 A, headLen a⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 (32 + hdrLen a), headLen a⟩ :=
    (hA.w.sub_left (Region.sub_prefix hn1.2.1)).sub_right (Lay.wSub (by omega))
  have lp : LoopPre s₃ A (W + BitVec.ofNat 32 (32 + hdrLen a)) (headLen a) :=
    ⟨hdi, hdx, hcx₃, hn1.1, by omega, by have := hA.wrap; omega, by rw [L.nW (by omega)]; have := L.fw; omega,
      (hA₃.take hn1.2.1).rd, by rw [aB]; exact E₃.perm.wC (by omega), by rw [aB]; exact dAB⟩
  refine WP.seq (WP.mono (copyLoop_ok s₃ lp) fun s₄ P₄ => ?_)
  have E₄ : VG.Proof.AesCcm.X86.Env K W SP s₄ := E₃.keep (by rw [P₄.other _ (by decide) (by decide) (by decide) (by decide)])
    (by rw [P₄.other _ (by decide) (by decide) (by decide) (by decide)]) P₄.rd P₄.wr
  -- What was written.
  have f₃ : Frame [VG.Proof.AesCcm.X86.wC W] s₂.mem s₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
  have fC : Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
    rw [P₄.mem, aB]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains (w64 W) (d := 32 + hdrLen a) (n := headLen a) (e := 32) (k := 16) (by omega) (by omega)
        (by decide))
  have fB : Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩, VG.Proof.AesCcm.X86.wC W] s.mem s₄.mem := by
    refine ((f₁.sub fun r hr => ?_).trans ?_).trans (fC.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · rw [← hm₂]; exact f₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  have fM : Frame (VG.Proof.AesCcm.X86.macR W SP y) s.mem s₄.mem := fB.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact VG.Proof.AesCcm.X86.sub_mac (by simp)
  have hAk : bytesAt s₃.mem (w64 A) (headLen a) = (bytesAt s.mem (w64 A) a).take (headLen a) := by
    have dA : ∀ {rs : List Region}, (∀ r ∈ rs, ∃ r', r' = (⟨w64 W, 2560⟩ : Region) ∧ Region.Sub r r') →
        ∀ r ∈ rs, (⟨w64 A, headLen a⟩ : Region).Disjoint r := fun h r hr => by
      obtain ⟨r', rfl, hs⟩ := h r hr
      exact (hA.w.sub_left (Region.sub_prefix hn1.2.1)).sub_right hs
    rw [Proof.AesGcm.X86.bytesAt_frame f₃ (dA fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, rfl, Lay.wSub (by decide)⟩) (by omega), hm₂,
      Proof.AesGcm.X86.bytesAt_frame f₁ (dA fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨_, rfl, Lay.wSub (by decide)⟩) (by omega),
      Proof.AesCcm.bytesAt_prefix _ _ hn1.2.1]
  have hB₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 32) 16 =
      Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem (w64 A) a).take (headLen a)) := by
    have hl := Proof.AesCcm.length_encodeLen a
    have htl : ((bytesAt s.mem (w64 A) a).take (headLen a)).length = headLen a := by
      rw [List.length_take, length_bytesAt]; omega
    have hB₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 32) 16 = bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) 16 := by
      rw [Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
        (by decide), hm₂]
    rw [P₄.mem, aB, show w64 W + BitVec.ofNat 64 (32 + hdrLen a) = w64 W + BitVec.ofNat 64 32 +
        BitVec.ofNat 64 (hdrLen a) by rw [VG.Proof.AesCcm.X86.add_ofNat_assoc],
      bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega) (by decide), length_bytesAt, hAk, hB₃, hB₁]
    rcases Proof.AesCcm.pad16_short (r := Spec.Ccm.encodeLen a ++ (bytesAt s.mem (w64 A) a).take (headLen a))
      (by rw [List.length_append, hl, htl]; omega) with e | e
    · rw [e, List.length_append, hl, htl, List.take_left' hl, ← hl, List.drop_append, hl, List.append_assoc]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      rw [List.drop_eq_nil_of_le (by rw [hl]; omega), List.nil_append, List.append_assoc,
        show 16 - hdrLen a - (hdrLen a + headLen a - hdrLen a) = 16 - (hdrLen a + headLen a) by omega]
    · exact absurd (congrArg List.length e) (by rw [List.length_append, hl]; simp; omega)
  -- The slots.
  have k₄ : ∀ o, (112 ≤ o ∧ o + 4 ≤ 240 ∨ 240 ≤ o ∧ o + 4 ≤ 2560) →
      slotv s₄.mem W o = slotv s₃.mem W o := fun o ho =>
    fC.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
      (by decide)
  have k₃ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ => by
    rw [show slotv s₃.mem W o = slotv s₂.mem W o from f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
      (by decide), hm₂, k₁ _ (.inl ⟨h₁, by omega⟩)]
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (VG.Proof.AesCcm.X86.updBlock_ok v L E₄ hR (by rw [k₄ _ (by decide), k₃ _ (by decide) (by decide)]; exact hK)
    (by rw [k₄ _ (by decide), k₃ _ (by decide) (by decide)]; exact hRo) hy)
    fun s₅ ⟨E₅, rd₅, wr₅, f₅, o₅⟩ => ⟨⟨E₅, fM.trans (f₅.sub fun r hr => ?_), ?_,
      by rw [rd₅, P₄.rd, hrd₃, hrd₂, hrd₁], by rw [wr₅, P₄.wr, hwr₃, hwr₂, hwr₁]⟩, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Proof.AesCcm.X86.sub_mac (by simp)
    · exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact VG.Proof.AesCcm.X86.sub_mac (by simp)
  · have hY₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16 := by
      refine Proof.AesGcm.X86.bytesAt_frame fB (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rcases hy with rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · rcases hy with rfl | rfl <;> exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    rw [o₅, hY₄, hB₄, VG.Proof.AesCcm.X86.ctxCiph_frame fM (VG.Proof.AesCcm.X86.k_macR L (by omega)) hRb]
  · have k : slotv s₅.mem W dO = slotv s₄.mem W dO := f₅.readW (r := ⟨w64 W + BitVec.ofNat 64 dO, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rcases hy with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w' (by decide)).symm) (by decide)
    rw [k, k₄ _ (by decide), hm₃]
    exact Mem.readW_writeW_self32 _ _ _
  · have k : slotv s₅.mem W nO = slotv s₄.mem W nO := f₅.readW (r := ⟨w64 W + BitVec.ofNat 64 nO, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rcases hy with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w' (by decide)).symm) (by decide)
    rw [k, k₄ _ (by decide), hm₃, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _

/-! ## The associated data -/

theorem aadBlk_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {A : BitVec 32} {al : Nat}
    (hAp : slotv s.mem W aadO = A) (hal : slotv s.mem W alenO = BitVec.ofNat 32 al) (hl : al < 2 ^ 32) :
    ∃ s₁, runBlock isa
      [.mov .eax (slot aadO), .store (at_ .ebp dO) .eax, .mov .eax (slot alenO), .store (at_ .ebp nO) .eax,
        .alu .test .eax (.reg .eax)] s = some s₁ ∧
      s₁.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 dO) A).writeW (w64 W + BitVec.ofNat 64 nO)
        (BitVec.ofNat 32 al) ∧
      s₁.zf = some (decide (al = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hAp, hal], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hAp, hal]
  · cmems [hal]; rw [and_self_beq32 hl]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []


/-- The associated data (`al` bytes at `A`, kept at `W + aadO` and
`W + alenO`), formatted and chained into `W + y`. -/
theorem aad_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : BitVec 32} {al : Nat} (hAp : slotv s.mem W aadO = A)
    (hal : slotv s.mem W alenO = BitVec.ofNat 32 al) (hA : VG.Proof.AesCcm.X86.Buf W SP s A al) (hl : al < 2 ^ 32) :
    WP isa (aad v.callee v.suffix y) s (VG.Proof.AesCcm.X86.Absorbed K W SP s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
        (adataBlocks (bytesAt s.mem (w64 A) al)))) := by
  obtain ⟨s₁, run₁, hm₁, hzf, hbp, hsp, hrd₁, hwr₁⟩ := VG.Proof.AesCcm.X86.aadBlk_ok L E hAp hal hl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  have f₁ : Frame [VG.Proof.AesCcm.X86.wC W] s.mem s₁.mem := by
    rw [hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
  have fm : Frame (VG.Proof.AesCcm.X86.macR W SP y) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.X86.sub_mac (by simp)
  have k₁ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
      (by decide)
  have hY₁ : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16 :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl <;> exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)
  have hA₁ : bytesAt s₁.mem (w64 A) al = bytesAt s.mem (w64 A) al :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hA.w.sub_right (Lay.wSub (by decide)))
      (by have := hA.lt; omega)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hc₁ : Spec.Ccm.ctxCiph s₁.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    VG.Proof.AesCcm.X86.ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  refine WP.ite (decide (al = 0)) (VG.Proof.AesCcm.X86.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : al = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨s₁, rfl, E₁, fm, ?_, hrd₁, hwr₁⟩
    simp only [hY₁, adataBlocks, length_bytesAt, h0, ↓reduceIte]; rfl
  · have h0 : al ≠ 0 := of_decide_eq_false hf
    have hK₁ : slotv s₁.mem W ctxO = K := by rw [k₁ _ (by decide) (by decide)]; exact hK
    have hR₁ : slotv s₁.mem W roundsO = BitVec.ofNat 32 R := by rw [k₁ _ (by decide) (by decide)]; exact hRo
    have hd₁ : slotv s₁.mem W dO = A := by
      rw [hm₁, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
      exact Mem.readW_writeW_self32 _ _ _
    have hn₁ : slotv s₁.mem W nO = BitVec.ofNat 32 al := by rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _
    have hk : headLen al ≤ al := by unfold headLen; omega
    refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.aadHead_ok v L E₁ hR hK₁ hR₁ hy (hA.of_eq hrd₁ hwr₁) (by omega) hl hd₁ hn₁)
      fun s₂ ⟨A₂, hd₂, hn₂⟩ => ?_)
    have hT : 0 < al - headLen al → VG.Proof.AesCcm.X86.Buf W SP s₂ (A + BitVec.ofNat 32 (headLen al)) (al - headLen al) := fun h =>
      (hA.drop hk (by have := hA.wrap; omega)).of_eq (by rw [A₂.rd, hrd₁]) (by rw [A₂.wr, hwr₁])
    refine WP.mono (VG.Proof.AesCcm.X86.absorbPad_ok v L A₂.env hR (by rw [VG.Proof.AesCcm.X86.slot_kept L hy A₂.frame (by decide) (by decide)]; exact hK₁)
      (by rw [VG.Proof.AesCcm.X86.slot_kept L hy A₂.frame (by decide) (by decide)]; exact hR₁) hy hT (by omega) hd₂ hn₂)
      fun s₃ A₃ => ⟨A₃.env, fm.trans (A₂.frame.trans A₃.frame), ?_, by rw [A₃.rd, A₂.rd, hrd₁],
        by rw [A₃.wr, A₂.wr, hwr₁]⟩
    have hrest : bytesAt s₂.mem (w64 (A + BitVec.ofNat 32 (headLen al))) (al - headLen al) =
        (bytesAt s.mem (w64 A) al).drop (headLen al) := by
      by_cases h : al - headLen al = 0
      · rw [h, List.drop_eq_nil_of_le (by rw [length_bytesAt]; omega)]; rfl
      · have hw : A.toNat + headLen al < 2 ^ 32 := by have := hA.wrap; omega
        rw [VG.Proof.AesCcm.X86.buf_kept (hT (by omega)) (by omega) A₂.frame, Buf.ptr hw, Proof.AesCcm.bytesAt_suffix _ _ hk, hA₁]
    rw [A₃.out, A₂.out, VG.Proof.AesCcm.X86.ctxCiph_frame A₂.frame (VG.Proof.AesCcm.X86.k_macR L (by omega)) hRb, hrest, hY₁, hc₁, hA₁,
      ← Proof.Cmac.chain_append]
    simp only [adataBlocks, length_bytesAt, h0, ↓reduceIte]

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.AbsorbCT`. -/
section

/-!
# AES-CCM on x86: `absorbPad y` is constant time

Untrusted: everything here is checked by Lean. What `absorbPad` starts from
(`PadPre`) is public: the pointers and the length it branches on, and the
slots holding them; its pieces are constant time from it (`absorbWhole_ct`,
`absorbTail_ct`, `absorbPad_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4 splitWhole dO nO)
open VG.Proof.AesGcm.X86 (CT w64 slotv WEnv padLoop_ok)

/-- The slots are kept when `dO` and `nO` are written. -/
theorem dn_kept {W : BitVec 32} {m m' : Mem} {a b : BitVec 32}
    (hm : m' = (m.writeW (w64 W + BitVec.ofNat 64 dO) a).writeW (w64 W + BitVec.ofNat 64 nO) b) {o : Nat}
    (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 240) : slotv m' W o = slotv m W o := by
  have f₁ : Frame [VG.Proof.AesCcm.X86.wC W] m m' := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
  exact f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
    (by decide)

/-- `dO` and `nO`, after they are written. -/
theorem dn_read {W : BitVec 32} {m m' : Mem} {a b : BitVec 32}
    (hm : m' = (m.writeW (w64 W + BitVec.ofNat 64 dO) a).writeW (w64 W + BitVec.ofNat 64 nO) b) :
    slotv m' W dO = a ∧ slotv m' W nO = b := by
  subst hm
  refine ⟨?_, Mem.readW_writeW_self32 _ _ _⟩
  rw [slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
  exact Mem.readW_writeW_self32 _ _ _

/-- What `absorbPad` of the `len` bytes at `P` starts from. -/
structure PadPre (K W SP : BitVec 32) (R : Nat) (P : BitVec 32) (len : Nat) (s : State) : Prop where
  env : VG.Proof.AesCcm.X86.Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  buf : 0 < len → VG.Proof.AesCcm.X86.Buf W SP s P len
  d : slotv s.mem W dO = P
  n : slotv s.mem W nO = BitVec.ofNat 32 len

/-- The arguments of the call chaining the whole blocks, from `ebp` and
`edi`. -/
theorem wholeArgs_ct {y : Nat} (hy : y = 0 ∨ y = 96) {I : State → Prop} {c : Prog isa} {F : State → State → Prop}
    (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp, .edi], s₁.gpr r = s₂.gpr r)
    (blk : ∀ s, I s → ∃ s', runBlock isa (keyArgs y ++ ([.mov .esi (.reg .edi)] : List Instr) ++ updScr) s = some s' ∧ F s s')
    (h₂ : CT (fun s' => ∃ s, I s ∧ F s s') c) :
    CT I (.seq (.block (keyArgs y ++ ([.mov .esi (.reg .edi)] : List Instr) ++ updScr)) c) := by
  rcases hy with rfl | rfl
  · exact CT.block_seq [.ebp, .edi] hr (by taint_decide) blk h₂
  · exact CT.block_seq [.ebp, .edi] hr (by taint_decide) blk h₂

theorem absorbWhole_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (VG.Proof.AesCcm.X86.PadPre K W SP R P len) (.seq (.block splitWhole)
        (.ite .e (.block []) (.seq (.block (keyArgs y ++ ([.mov .esi (.reg .edi)] : List Instr) ++ updScr)) (updCall v.callee v.suffix)))) := by
  refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesCcm.X86.split_ok L hs.env hs.d hs.n hl) ?_
  refine CT.ite (decide (len / 16 = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => VG.Proof.AesCcm.X86.eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : len / 16 ≠ 0 := of_decide_eq_false hf
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  refine VG.Proof.AesCcm.X86.wholeArgs_ct hy (VG.Proof.AesCcm.X86.pin2 fun _ ⟨_, _, _, hdi, _, hbp, _⟩ => ⟨hbp, hdi⟩)
    (fun s₁ ⟨s, hs, hbx, hdi, _, hbp, hsp, hm₁, hrd₁, hwr₁⟩ =>
      VG.Proof.AesCcm.X86.wholeArgs_ok L ⟨hbp, hsp, hs.env.perm.of_eq hrd₁ hwr₁⟩
        (by rw [VG.Proof.AesCcm.X86.split_kept hm₁ (by decide) (by decide)]; exact hs.ctx)
        (by rw [VG.Proof.AesCcm.X86.split_kept hm₁ (by decide) (by decide)]; exact hs.rounds) hbx hdi y) ?_
  refine VG.Proof.AesCcm.X86.updCall_ct v L hR (y := y) (Q := P) (n := len / 16) (by rcases hy with rfl | rfl <;> decide) (by omega)
    fun s₂ ⟨s₁, ⟨s, hs, _, _, _, _, _, _, hrd₁, hwr₁⟩, _, ax, cx, dx, bx, si, di, bp, sp, rd₂, wr₂⟩ => ?_
  have hP := hs.buf (by omega)
  exact ⟨⟨bp, sp, hs.env.perm.of_eq (by rw [rd₂, hrd₁]) (by rw [wr₂, hwr₁])⟩,
    VG.Proof.AesCcm.X86.srcBuf ((hP.take hb).of_eq (by rw [rd₂, hrd₁]) (by rw [wr₂, hwr₁])),
    (hP.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by rcases hy with rfl | rfl <;> decide)),
    ax, cx, dx, bx, si, di⟩

/-- What the last bytes' piece starts from. -/
structure TailPre (K W SP : BitVec 32) (R : Nat) (Q : BitVec 32) (t : Nat) (s : State) : Prop where
  env : VG.Proof.AesCcm.X86.Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  buf : 0 < t → VG.Proof.AesCcm.X86.Buf W SP s Q t
  d : slotv s.mem W dO = Q
  n : slotv s.mem W nO = BitVec.ofNat 32 t

theorem absorbTail_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {Q : BitVec 32} {t : Nat} (ht : t < 16) :
    CT (VG.Proof.AesCcm.X86.TailPre K W SP R Q t) (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
        (.ite .e (.block [])
          (.seq (.block (zero4 blkO ++ ([.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm blkO),
              .mov .ecx (slot nO)] : List Instr)))
            (.seq copyLoop (updBlock v.callee v.suffix y))))) := by
  refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesCcm.X86.testN_ok L hs.env (r := t) (by omega) hs.n) ?_
  refine CT.ite (decide (t = 0)) (fun _ ⟨_, _, _, hzf, _⟩ => VG.Proof.AesCcm.X86.eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : t ≠ 0 := of_decide_eq_false hf
  refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ ⟨_, _, _, _, hbp, _⟩ => hbp) (by taint_decide)
    (fun s₁ ⟨s, hs, hm₁, _, hbp, hsp, hrd₁, hwr₁⟩ =>
      VG.Proof.AesCcm.X86.tailArgs_ok L ⟨hbp, hsp, hs.env.perm.of_eq hrd₁ hwr₁⟩ (Q := Q) (t := t) (by rw [hm₁]; exact hs.d)
        (by rw [hm₁]; exact hs.n)) ?_
  refine CT.seq (J := fun s₃ => VG.Proof.AesCcm.X86.Env K W SP s₃ ∧ slotv s₃.mem W ctxO = K ∧ slotv s₃.mem W roundsO = BitVec.ofNat 32 R)
    (Proof.AesGcm.X86.copyLoop_ct (VG.Proof.AesCcm.X86.pin3 fun _ ⟨_, _, _, hdi, hdx, hcx, _⟩ => ⟨hdi, hdx, hcx⟩))
    (fun s₂ ⟨s₁, ⟨s, hs, hm₁, _, _, _, hrd₁, hwr₁⟩, hm₂, hdi, hdx, hcx, hbp₂, hsp₂, hrd₂, hwr₂⟩ => ?_)
    (VG.Proof.AesCcm.X86.updBlock_ct v L hR hy fun _ h => h)
  have hB := hs.buf (by omega)
  have he : WEnv W s₂ := ⟨hbp₂, by rw [hwr₂, hwr₁]; exact hs.env.perm.w, L.fw⟩
  refine WP.mono (padLoop_ok (S := Q) (d := 32) (t := t) (m := s₁.mem) he hm₂ hdi hdx hcx (by omega)
    (by omega) (by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact hB.rd) hB.wrap (hB.w.sub_right (Lay.wSub (by decide)))
    (by decide)) fun s₃ ⟨_, f₃, g₃, rd₃, wr₃⟩ => ?_
  have k₃ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ => by
    rw [← hm₁]
    exact f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
      (by decide)
  exact ⟨⟨by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hbp₂],
      by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hsp₂],
      hs.env.perm.of_eq (by rw [rd₃, hrd₂, hrd₁]) (by rw [wr₃, hwr₂, hwr₁])⟩,
    by rw [k₃ _ (by decide) (by decide)]; exact hs.ctx, by rw [k₃ _ (by decide) (by decide)]; exact hs.rounds⟩

theorem absorbPad_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (VG.Proof.AesCcm.X86.PadPre K W SP R P len) (absorbPad v.callee v.suffix y) := by
  refine RelCT.assoc (CT.seq (J := VG.Proof.AesCcm.X86.TailPre K W SP R (P + BitVec.ofNat 32 (16 * (len / 16))) (len % 16))
    (VG.Proof.AesCcm.X86.absorbWhole_ct v L hR hy hl)
    (fun s hs => WP.mono (VG.Proof.AesCcm.X86.absorbWhole_ok v L hs.env hR hs.ctx hs.rounds hy hs.buf hl hs.d hs.n)
      fun s₁ ⟨A₁, hd₁, hn₁⟩ => ⟨A₁.env, by rw [VG.Proof.AesCcm.X86.slot_kept L hy A₁.frame (by decide) (by decide)]; exact hs.ctx,
        by rw [VG.Proof.AesCcm.X86.slot_kept L hy A₁.frame (by decide) (by decide)]; exact hs.rounds, fun h => ?_, hd₁, hn₁⟩)
    (VG.Proof.AesCcm.X86.absorbTail_ct v L hR hy (Nat.mod_lt _ (by decide))))
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  have hP := hs.buf (by omega)
  have := (hP.drop hb (by have := hP.wrap; omega)).of_eq A₁.rd A₁.wr
  rwa [show len - 16 * (len / 16) = len % 16 by omega] at this

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.AadCT`. -/
section

/-!
# AES-CCM on x86: the associated data is chained in constant time

Untrusted: everything here is checked by Lean. `minLen` and `header` branch
on the length of the associated data, `aadHead` and `aad` also on the
slots holding it and its address: all public (`minLen_ct`, `header_ct`,
`aadHead_ct`, `aad_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4 minLen dO nO bO)
open VG.Proof.AesGcm.X86 (CT w64 slotv LoopPre copyLoop_ok length_bytesAt)
open VG.Proof.AesCcm (hdrLen headLen)

theorem minLen_ct {I : State → Prop} {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {n b : Nat}
    (hp : ∀ s, I s → VG.Proof.AesCcm.X86.Env K W SP s ∧ slotv s.mem W nO = BitVec.ofNat 32 n ∧ slotv s.mem W bO = BitVec.ofNat 32 b ∧
      b ≤ 16 ∧ n < 2 ^ 32) :
    CT I minLen := by
  refine CT.seq (J := fun s => s.cf = some (decide (n < 16 - b)))
    (CT.taint [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun s h => (hp s h).1.ebp) (by taint_decide)) (fun s hs => ?_)
    (CT.ite (decide (n < 16 - b)) (fun _ h => VG.Proof.AesCcm.X86.eval_b h)
      (fun _ => by exact CT.taint [] (fun _ _ _ _ _ h => by simp at h) (by taint_decide)) (fun _ => CT.nil))
  obtain ⟨E, hn, hb, hb16, hnlt⟩ := hp s hs
  obtain ⟨s₁, run₁, -, -, cf, -⟩ := VG.Proof.AesCcm.X86.minLen1_ok L E hn hb hb16 hnlt
  exact WP.of_runBlock ⟨s₁, run₁, cf⟩

theorem header_ct {I : State → Prop} {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {a : Nat} (ha : a < 2 ^ 32)
    (hp : ∀ s, I s → VG.Proof.AesCcm.X86.Env K W SP s ∧ slotv s.mem W nO = BitVec.ofNat 32 a) : CT I header := by
  refine CT.seq (J := fun s => s.cf = some (decide (a < 2 ^ 16 - 2 ^ 8)) ∧ s.gpr .ebp = W)
    (CT.taint [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun s h => (hp s h).1.ebp) (by taint_decide)) (fun s hs => ?_)
    (CT.ite (decide (a < 2 ^ 16 - 2 ^ 8)) (fun _ h => VG.Proof.AesCcm.X86.eval_b h.1)
      (fun _ => by exact CT.taint [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ h => h.2) (by taint_decide))
      (fun _ => by exact CT.taint [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ h => h.2) (by taint_decide)))
  obtain ⟨s₁, run₁, -, -, cf, bp, -⟩ := VG.Proof.AesCcm.X86.headerBlk_ok L (hp s hs).1 ha (hp s hs).2
  exact WP.of_runBlock ⟨s₁, run₁, cf, bp⟩

/-- The slots `header` does not write are kept. -/
theorem header_kept {W : BitVec 32} {m m' : Mem}
    (f : Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩, ⟨w64 W + BitVec.ofNat 64 bO, 4⟩] m m') {o : Nat}
    (ho : 112 ≤ o ∧ o + 4 ≤ 280 ∨ 284 ≤ o ∧ o + 4 ≤ 2560) : slotv m' W o = slotv m W o :=
  f.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
    · exact Lay.w_w (by simp only [bO]; omega) (by omega) (by decide)) (by decide)

/-- After `header`: what `PadPre` says, and the length of the encoding at
`W + bO`. -/
structure HeadPre (K W SP : BitVec 32) (R : Nat) (A : BitVec 32) (a : Nat) (s : State) : Prop
    extends VG.Proof.AesCcm.X86.PadPre K W SP R A a s where
  b : slotv s.mem W bO = BitVec.ofNat 32 (hdrLen a)

theorem aadHead_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : BitVec 32} {a : Nat} (ha0 : 0 < a) (ha : a < 2 ^ 32) :
    CT (VG.Proof.AesCcm.X86.PadPre K W SP R A a) (aadHead v.callee v.suffix y) := by
  have hh6 : hdrLen a ≤ 6 := by unfold hdrLen; split <;> (try split) <;> omega
  have hn1 : 1 ≤ headLen a ∧ headLen a ≤ a ∧ hdrLen a + headLen a ≤ 16 := by unfold headLen; omega
  -- `header`.
  refine CT.seq (J := VG.Proof.AesCcm.X86.HeadPre K W SP R A a) (VG.Proof.AesCcm.X86.header_ct L ha fun s hs => ⟨hs.env, hs.n⟩)
    (fun s hs => WP.mono (VG.Proof.AesCcm.X86.header_ok L hs.env ha hs.n) fun s₁ ⟨E₁, rd, wr, f, hb, _⟩ =>
      ⟨⟨E₁, by rw [VG.Proof.AesCcm.X86.header_kept f (.inl ⟨by decide, by decide⟩)]; exact hs.ctx,
        by rw [VG.Proof.AesCcm.X86.header_kept f (.inl ⟨by decide, by decide⟩)]; exact hs.rounds,
        fun h => (hs.buf h).of_eq rd wr, by rw [VG.Proof.AesCcm.X86.header_kept f (.inl ⟨by decide, by decide⟩)]; exact hs.d,
        by rw [VG.Proof.AesCcm.X86.header_kept f (.inl ⟨by decide, by decide⟩)]; exact hs.n⟩, hb⟩) ?_
  -- `minLen`.
  refine CT.seq (J := fun s => VG.Proof.AesCcm.X86.HeadPre K W SP R A a s ∧ s.gpr .ecx = BitVec.ofNat 32 (headLen a))
    (VG.Proof.AesCcm.X86.minLen_ct L fun s hs => ⟨hs.env, hs.n, hs.b, by omega, ha⟩)
    (fun s hs => WP.mono (VG.Proof.AesCcm.X86.minLen_ok L hs.env hs.n hs.b (by omega) ha) fun s₁ ⟨cx, bp, sp, m, rd, wr⟩ =>
      ⟨⟨⟨⟨bp, sp, hs.env.perm.of_eq rd wr⟩, by rw [m]; exact hs.ctx, by rw [m]; exact hs.rounds,
        fun h => (hs.buf h).of_eq rd wr, by rw [m]; exact hs.d, by rw [m]; exact hs.n⟩, by rw [m]; exact hs.b⟩,
        by rw [cx]; congr 1; unfold headLen; omega⟩) ?_
  -- The arguments of the copy.
  refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ h => h.1.env.ebp) (by taint_decide)
    (fun s ⟨hs, cx⟩ => VG.Proof.AesCcm.X86.aadHeadArgs_ok L hs.env hs.d hs.n hs.b cx hn1.2.1 ha) ?_
  -- The copy, then the block chained.
  refine CT.seq (J := fun s₃ => VG.Proof.AesCcm.X86.Env K W SP s₃ ∧ slotv s₃.mem W ctxO = K ∧ slotv s₃.mem W roundsO = BitVec.ofNat 32 R)
    (Proof.AesGcm.X86.copyLoop_ct (VG.Proof.AesCcm.X86.pin3 fun _ ⟨_, _, _, hdi, hdx, hcx, _⟩ => ⟨hdi, hdx, hcx⟩))
    (fun s₃ ⟨s₂, ⟨hs, _⟩, hm₃, hdi, hdx, hcx₃, hbp₃, hsp₃, hrd₃, hwr₃⟩ => ?_)
    (VG.Proof.AesCcm.X86.updBlock_ct v L hR hy fun _ h => h)
  have E₃ : VG.Proof.AesCcm.X86.Env K W SP s₃ := ⟨hbp₃, hsp₃, hs.env.perm.of_eq hrd₃ hwr₃⟩
  have hA₃ := (hs.buf ha0).of_eq hrd₃ hwr₃
  have aB : w64 (W + BitVec.ofNat 32 (32 + hdrLen a)) = w64 W + BitVec.ofNat 64 (32 + hdrLen a) := L.aW (by omega)
  have lp : LoopPre s₃ A (W + BitVec.ofNat 32 (32 + hdrLen a)) (headLen a) :=
    ⟨hdi, hdx, hcx₃, hn1.1, by omega, by have := hA₃.wrap; omega, by rw [L.nW (by omega)]; have := L.fw; omega,
      (hA₃.take hn1.2.1).rd, by rw [aB]; exact E₃.perm.wC (by omega),
      by rw [aB]; exact (hA₃.w.sub_left (Region.sub_prefix hn1.2.1)).sub_right (Lay.wSub (by omega))⟩
  refine WP.mono (copyLoop_ok s₃ lp) fun s₄ P₄ => ?_
  have fC : Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
    rw [P₄.mem, aB]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains (w64 W) (d := 32 + hdrLen a) (n := headLen a) (e := 32) (k := 16) (by omega) (by omega)
        (by decide))
  have k₄ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₄.mem W o = slotv s₂.mem W o := fun o h₁ h₂ =>
    (fC.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
      (by decide)).trans (VG.Proof.AesCcm.X86.split_kept hm₃ h₁ h₂)
  exact ⟨E₃.keep (by rw [P₄.other _ (by decide) (by decide) (by decide) (by decide)])
      (by rw [P₄.other _ (by decide) (by decide) (by decide) (by decide)]) P₄.rd P₄.wr,
    by rw [k₄ _ (by decide) (by decide)]; exact hs.ctx, by rw [k₄ _ (by decide) (by decide)]; exact hs.rounds⟩

/-- What `aad` starts from. -/
structure AadPre (K W SP : BitVec 32) (R : Nat) (A : BitVec 32) (al : Nat) (s : State) : Prop where
  env : VG.Proof.AesCcm.X86.Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  aad : slotv s.mem W aadO = A
  alen : slotv s.mem W alenO = BitVec.ofNat 32 al
  buf : VG.Proof.AesCcm.X86.Buf W SP s A al

theorem aad_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : BitVec 32} {al : Nat} (hl : al < 2 ^ 32) :
    CT (VG.Proof.AesCcm.X86.AadPre K W SP R A al) (aad v.callee v.suffix y) := by
  refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ h => h.env.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesCcm.X86.aadBlk_ok L hs.env hs.aad hs.alen hl) ?_
  refine CT.ite (decide (al = 0)) (fun _ ⟨_, _, _, hzf, _⟩ => VG.Proof.AesCcm.X86.eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : al ≠ 0 := of_decide_eq_false hf
  have hk : headLen al ≤ al := by unfold headLen; omega
  have toPad : ∀ s₁, (∃ s, VG.Proof.AesCcm.X86.AadPre K W SP R A al s ∧ s₁.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 dO) A).writeW
      (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 al) ∧ s₁.zf = some (decide (al = 0)) ∧ s₁.gpr .ebp = W ∧
      s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr) → VG.Proof.AesCcm.X86.PadPre K W SP R A al s₁ :=
    fun s₁ ⟨s, hs, hm₁, _, hbp, hsp, hrd₁, hwr₁⟩ =>
      have f₁ : Frame [VG.Proof.AesCcm.X86.wC W] s.mem s₁.mem := by
        rw [hm₁]
        exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide)
            (by decide))).writeW (List.mem_singleton_self _) _
          (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
      have k₁ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
        f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
          (by decide)
      ⟨⟨hbp, hsp, hs.env.perm.of_eq hrd₁ hwr₁⟩, by rw [k₁ _ (by decide) (by decide)]; exact hs.ctx,
        by rw [k₁ _ (by decide) (by decide)]; exact hs.rounds, fun _ => hs.buf.of_eq hrd₁ hwr₁,
        by rw [hm₁, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
           exact Mem.readW_writeW_self32 _ _ _,
        by rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _⟩
  refine CT.seq (J := VG.Proof.AesCcm.X86.PadPre K W SP R (A + BitVec.ofNat 32 (headLen al)) (al - headLen al))
    ((VG.Proof.AesCcm.X86.aadHead_ct v L hR hy (by omega) hl).mono toPad) (fun s₁ h => ?_) (VG.Proof.AesCcm.X86.absorbPad_ct v L hR hy (by omega))
  have P := toPad s₁ h
  obtain ⟨s, hs, -⟩ := h
  refine WP.mono (VG.Proof.AesCcm.X86.aadHead_ok v L P.env hR P.ctx P.rounds hy (P.buf (by omega)) (by omega) hl P.d P.n)
    fun s₂ ⟨A₂, hd₂, hn₂⟩ => ⟨A₂.env, by rw [VG.Proof.AesCcm.X86.slot_kept L hy A₂.frame (by decide) (by decide)]; exact P.ctx,
      by rw [VG.Proof.AesCcm.X86.slot_kept L hy A₂.frame (by decide) (by decide)]; exact P.rounds, fun _ => ?_, hd₂, hn₂⟩
  have hA := P.buf (by omega)
  exact (hA.drop hk (by have := hA.wrap; omega)).of_eq A₂.rd A₂.wr

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Mac`. -/
section

/-!
# AES-CCM on x86: `B₀`, the CBC-MAC and the tag (`b0 y`, `mac y`, `tag y`)

Untrusted: everything here is checked by Lean. `b0 y` builds `B₀` in `B`
from `Ctr₀` and the flags, zeroes the MAC state at `W + y` and chains `B₀`
into it (`b0_ok`); `mac y` chains the formatted associated data and payload
after it (`mac_ok`): the CBC-MAC of the formatted input (§6.1 steps 1–4);
`tag y` XORs `CIPH_K(Ctr₀)` into it (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 tglO dO nO)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 slotv zero4_fold zero4_bytes' length_bytesAt and_self_beq32)

theorem seq_assoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => WP.assoc h)

/-! ## `B₀` -/

/-- The flags, without `64 [a > 0]`, and ZF for `a = 0`. -/
theorem b0Flags_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {nl al tl : Nat}
    (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (hal : al < 2 ^ 32)
    (htl : slotv s.mem W tglO = BitVec.ofNat 32 tl) (hnlv : slotv s.mem W nlenO = BitVec.ofNat 32 nl)
    (halv : slotv s.mem W alenO = BitVec.ofNat 32 al) :
    ∃ s₁, runBlock isa
      [.mov .eax (slot tglO), .alu .sub .eax (imm 2), .alu .add .eax (.reg .eax),
        .alu .add .eax (.reg .eax), .mov .ecx (imm 14), .alu .sub .ecx (slot nlenO), .alu .add .eax (.reg .ecx),
        .mov .ecx (slot alenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .eax = BitVec.ofNat 32 (4 * (tl - 2) + (14 - nl)) ∧
      s₁.zf = some (decide (al = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, htl, hnlv, halv], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [htl, hnlv]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · cmems [halv]; rw [and_self_beq32 hal]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `B₀` in `B`, and the MAC state at `W + y` zeroed. -/
theorem b0Pre_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {nonce : List Byte}
    {nl al n tl : Nat} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32)
    (htl : slotv s.mem W tglO = BitVec.ofNat 32 tl) (hnlv : slotv s.mem W nlenO = BitVec.ofNat 32 nl)
    (halv : slotv s.mem W alenO = BitVec.ofNat 32 al) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n)
    (hc0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.seq (.block [.mov .eax (slot tglO), .alu .sub .eax (imm 2), .alu .add .eax (.reg .eax),
        .alu .add .eax (.reg .eax), .mov .ecx (imm 14), .alu .sub .ecx (slot nlenO), .alu .add .eax (.reg .ecx),
        .mov .ecx (slot alenO), .alu .test .ecx (.reg .ecx)])
      (.seq (.ite .e (.block []) (.block [.alu .add .eax (imm 64)]))
      (.block (([.mov .ecx (slot c0O), .store (at_ .ebp blkO) .ecx, .mov .ecx (slot (c0O + 4)),
        .store (at_ .ebp (blkO + 4)) .ecx, .mov .ecx (slot (c0O + 8)), .store (at_ .ebp (blkO + 8)) .ecx,
        .store8 (at_ .ebp blkO) .al, .mov .eax (slot lenO), .bswap .eax, .alu .or .eax (slot (c0O + 12)),
        .store (at_ .ebp (blkO + 12)) .eax] : List Instr) ++ zero4 y)))) s fun s' =>
      VG.Proof.AesCcm.X86.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 = Spec.Cmac.zeros 16 ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 tl nonce al n := by
  -- The flags, without `64 [a > 0]`, and ZF for `a = 0`.
  obtain ⟨s₁, run₁, hm₁, hax₁, hzf₁, hbp₁, hsp₁, hrd₁, hwr₁⟩ := VG.Proof.AesCcm.X86.b0Flags_ok L E h13 ht4 hal htl hnlv halv
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- `64 [a > 0]`.
  have hite : WP isa (.ite .e (.block []) (.block [.alu .add .eax (imm 64)])) s₁ fun s₂ =>
      s₂.mem = s.mem ∧ s₂.gpr .eax = BitVec.ofNat 32 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64) ∧
      s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine WP.ite (decide (al = 0)) (VG.Proof.AesCcm.X86.eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : al = 0 := of_decide_eq_true ht
      exact WP.of_runBlock ⟨s₁, rfl, hm₁, by rw [hax₁, h0]; rfl, hbp₁, hsp₁, hrd₁, hwr₁⟩
    · have h0 : al ≠ 0 := of_decide_eq_false hf
      refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · cmems [hm₁]
      · cregs [hax₁, h0]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h0, ↓reduceIte]
        omega
      · cregs [hbp₁]
      · cregs [hsp₁]
      · cmems [hrd₁]
      · cmems [hwr₁]
  refine WP.seq (WP.mono hite fun s₂ ⟨hm₂, hax₂, hbp₂, hsp₂, hrd₂, hwr₂⟩ => ?_)
  -- `B₀`, and the state zeroed.
  have hlen₂ : slotv s₂.mem W lenO = BitVec.ofNat 32 n := by rw [hm₂]; exact hlen
  have hf := flags_val32 (al := al) ht4 ht16 hte h7 h13
  have hz := zero4_fold (((((s.mem.writeW (w64 W + BitVec.ofNat 64 32) (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)).writeW
    (w64 W + BitVec.ofNat 64 36) (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32)).writeW
    (w64 W + BitVec.ofNat 64 40) (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)).writeW
    (w64 W + BitVec.ofNat 64 32) (Spec.Ccm.flags tl (15 - nl) al)).writeW (w64 W + BitVec.ofNat 64 44)
    (bswap (BitVec.ofNat 32 n) ||| s.mem.readW (w64 W + BitVec.ofNat 64 60) 32)) W y
  obtain ⟨s₃, run₃, hm₃, hbp₃, hsp₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      (([.mov .ecx (slot c0O), .store (at_ .ebp blkO) .ecx, .mov .ecx (slot (c0O + 4)),
        .store (at_ .ebp (blkO + 4)) .ecx, .mov .ecx (slot (c0O + 8)), .store (at_ .ebp (blkO + 8)) .ecx,
        .store8 (at_ .ebp blkO) .al, .mov .eax (slot lenO), .bswap .eax, .alu .or .eax (slot (c0O + 12)),
        .store (at_ .ebp (blkO + 12)) .eax] : List Instr) ++ zero4 y) s₂ = some s₃ ∧
      s₃.mem = Cmac.zero4 (((((s.mem.writeW (w64 W + BitVec.ofNat 64 32) (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)).writeW
        (w64 W + BitVec.ofNat 64 36) (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32)).writeW
        (w64 W + BitVec.ofNat 64 40) (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)).writeW
        (w64 W + BitVec.ofNat 64 32) (Spec.Ccm.flags tl (15 - nl) al)).writeW (w64 W + BitVec.ofNat 64 44)
        (bswap (BitVec.ofNat 32 n) ||| s.mem.readW (w64 W + BitVec.ofNat 64 60) 32)) (w64 W + BitVec.ofNat 64 y) ∧
      s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [zero4, hbp₂, L.aW, E.perm.wW, E.perm.wR, hrd₂, hwr₂, hm₂, hlen₂], ?_, ?_, ?_, ?_, ?_⟩
    · cmems [hm₂, hax₂, hf, hlen, ← hz]
    · cregs [hbp₂]
    · cregs [hsp₂]
    all_goals cmems []
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have E₃ : VG.Proof.AesCcm.X86.Env K W SP s₃ := ⟨hbp₃, hsp₃, E.perm.of_eq (by rw [hrd₃, hrd₂]) (by rw [hwr₃, hwr₂])⟩
  obtain ⟨mB, hmB⟩ : ∃ mB, mB = ((((s.mem.writeW (w64 W + BitVec.ofNat 64 32) (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)).writeW
      (w64 W + BitVec.ofNat 64 36) (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32)).writeW
      (w64 W + BitVec.ofNat 64 40) (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)).writeW
      (w64 W + BitVec.ofNat 64 32) (Spec.Ccm.flags tl (15 - nl) al)).writeW (w64 W + BitVec.ofNat 64 44)
      (bswap (BitVec.ofNat 32 n) ||| s.mem.readW (w64 W + BitVec.ofNat 64 60) 32) := ⟨_, rfl⟩
  rw [← hmB] at hm₃
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 →
      (⟨w64 W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (w64 W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains (w64 W) h₁ (by omega) (by decide)
  have fB : Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩] s.mem mB := by
    rw [hmB]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cB 32 4 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 36 4 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 40 4 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 32 1 (by decide) (by decide)) |>.writeW
      (List.mem_singleton_self _) _ (cB 44 4 (by decide) (by decide))
  have dYB : (⟨w64 W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine ⟨E₃, by rw [hrd₃, hrd₂], by rw [hwr₃, hwr₂], ?_, ?_, ?_⟩
  · rw [hm₃]
    exact (fB.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)
  · rw [hm₃, zero4_bytes']; rfl
  · -- `B₀`.
    have fZ : Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩] mB (Cmac.zero4 mB (w64 W + BitVec.ofNat 64 y)) :=
      Cmac.frame_store4 _ _ _ _ _
    rw [hm₃, Proof.AesGcm.X86.bytesAt_frame fZ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dYB) (by decide), hmB]
    rw [show w64 W + BitVec.ofNat 64 36 = w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 4 by rw [VG.Proof.AesCcm.X86.add_ofNat_assoc],
      show w64 W + BitVec.ofNat 64 40 = w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 by rw [VG.Proof.AesCcm.X86.add_ofNat_assoc],
      show w64 W + BitVec.ofNat 64 44 = w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 12 by rw [VG.Proof.AesCcm.X86.add_ofNat_assoc],
      b0_bytes]
    have e := VG.Proof.AesCcm.X86.bytesAt_words s.mem (w64 W) 48
    simp only [Nat.reduceAdd] at e
    rw [hc0] at e
    have l12 : (le4 (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32) ++ le4 (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32) ++
        le4 (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)).length = 12 := by
      simp only [List.length_append, Proof.Cmac.length_le4]
    have hw : le4 (s.mem.readW (w64 W + BitVec.ofNat 64 60) 32) = (Spec.Ccm.ctrBlock nonce 0).drop 12 := by
      rw [e, List.drop_left' l12]
    have h7' : 7 ≤ nonce.length := by omega
    have h13' : nonce.length ≤ 13 := by omega
    rw [show bswap (BitVec.ofNat 32 n) = byteRev32 (BitVec.ofNat 32 n) from rfl,
      ctr_or32 h7' h13' hw (by rw [hnl]; exact hn) hn32]
    have hb0 : Spec.Ccm.b0 tl nonce al n = Spec.Ccm.flags tl (15 - nl) al :: (Spec.Ccm.ctrBlock nonce n).drop 1 := by
      simp [Spec.Ccm.b0, Spec.Ccm.ctrBlock, hnl]
    have ht : (Spec.Ccm.ctrBlock nonce n).take 12 = (Spec.Ccm.ctrBlock nonce 0).take 12 := ctrBlock_take12 h7' h13' hn32
    rw [hb0]
    conv_rhs => rw [← List.take_append_drop 12 (Spec.Ccm.ctrBlock nonce n)]
    rw [ht, e, List.take_left' l12, List.drop_append_of_le_length (by rw [l12]; decide)]
    simp only [List.cons_append, List.append_assoc, List.drop_append_of_le_length
      (show 1 ≤ (le4 (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)).length by rw [Proof.Cmac.length_le4]; decide)]

/-- The slots, after code that writes only `macR`. -/
theorem Slots.macR {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {y : Nat} (hy : y = 0 ∨ y = 96) {m m' : Mem}
    (hf : Frame (VG.Proof.AesCcm.X86.macR W SP y) m m') {R : Nat} {N A D T : BitVec 32} {nl al n tl : Nat}
    (S : VG.Proof.AesCcm.X86.Slots W K R N A D T nl al n tl m) : VG.Proof.AesCcm.X86.Slots W K R N A D T nl al n tl m' :=
  ⟨by rw [VG.Proof.AesCcm.X86.slot_kept L hy hf (by decide) (by decide)]; exact S.ctx,
    by rw [VG.Proof.AesCcm.X86.slot_kept L hy hf (by decide) (by decide)]; exact S.rounds,
    by rw [VG.Proof.AesCcm.X86.slot_kept L hy hf (by decide) (by decide)]; exact S.nonce,
    by rw [VG.Proof.AesCcm.X86.slot_kept L hy hf (by decide) (by decide)]; exact S.nlen,
    by rw [VG.Proof.AesCcm.X86.slot_kept L hy hf (by decide) (by decide)]; exact S.aad,
    by rw [VG.Proof.AesCcm.X86.slot_kept L hy hf (by decide) (by decide)]; exact S.alen,
    by rw [VG.Proof.AesCcm.X86.slot_kept L hy hf (by decide) (by decide)]; exact S.data,
    by rw [VG.Proof.AesCcm.X86.slot_kept L hy hf (by decide) (by decide)]; exact S.len,
    by rw [VG.Proof.AesCcm.X86.slot_kept L hy hf (by decide) (by decide)]; exact S.tl,
    by rw [VG.Proof.AesCcm.X86.slot_kept L hy hf (by decide) (by decide)]; exact S.tp⟩

/-- `B₀` chained into a zeroed MAC state at `W + y`. -/
theorem b0_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D T : BitVec 32} {nl al n tl : Nat} (S : VG.Proof.AesCcm.X86.Slots W K R N A D T nl al n tl s.mem)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32)
    (hc0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (b0 v.callee v.suffix y) s fun s' => VG.Proof.AesCcm.X86.Env K W SP s' ∧ Frame (VG.Proof.AesCcm.X86.macR W SP y) s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (Spec.Cmac.zeros 16) [Spec.Ccm.b0 tl nonce al n] ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine VG.Proof.AesCcm.X86.seq_assoc3 (WP.seq (WP.mono (VG.Proof.AesCcm.X86.b0Pre_ok L E hnl h7 h13 ht4 ht16 hte hal hn hn32 S.tl S.nlen S.alen S.len hc0 hy)
    fun s₃ ⟨E₃, rd₃, wr₃, f₃, hz, hB⟩ => ?_))
  have k₃ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
      · rcases hy with rfl | rfl
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)) (by decide)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (VG.Proof.AesCcm.X86.updBlock_ok v L E₃ hR (by rw [k₃ _ (by decide) (by decide)]; exact S.ctx)
    (by rw [k₃ _ (by decide) (by decide)]; exact S.rounds) hy) fun s₄ ⟨E₄, hrd₄, hwr₄, f₄, h₄⟩ =>
    ⟨E₄, ?_, ?_, by rw [hrd₄, rd₃], by rw [hwr₄, wr₃]⟩
  · refine (f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact VG.Proof.AesCcm.X86.sub_mac (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact VG.Proof.AesCcm.X86.sub_mac (by simp)
      · exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact VG.Proof.AesCcm.X86.sub_mac (by simp)
  · rw [h₄, hz, hB, VG.Proof.AesCcm.X86.ctxCiph_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w.sub_right (Lay.wSub (by decide))
      · exact L.k_w.sub_right (Lay.wSub (by omega))) hRb]

/-! ## The CBC-MAC -/

/-- The data, as the string to chain: its address and length at `dO`, `nO`. -/
theorem dataArgs_ok {K W SP : BitVec 32} {s₂ : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E₂ : VG.Proof.AesCcm.X86.Env K W SP s₂) {D : BitVec 32} {n : Nat}
    (hD : slotv s₂.mem W dataO = D) (hn : slotv s₂.mem W lenO = BitVec.ofNat 32 n) :
    ∃ s₃, runBlock isa
      [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO), .store (at_ .ebp nO) .eax] s₂ =
        some s₃ ∧
      s₃.mem = (s₂.mem.writeW (w64 W + BitVec.ofNat 64 dO) D).writeW (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 n) ∧
      s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
  refine ⟨_, by crun [E₂.ebp, L.aW, E₂.perm.wW, E₂.perm.wR, hD, hn], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hD, hn]
  · cregs [E₂.ebp]
  · cregs [E₂.esp]
  all_goals cmems []


/-- CBC-MAC of the formatted nonce, associated data and payload into `W + y`. -/
theorem mac_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D T : BitVec 32} {nl al n tl : Nat} (S : VG.Proof.AesCcm.X86.Slots W K R N A D T nl al n tl s.mem)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32)
    (hc0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96)
    (hA : VG.Proof.AesCcm.X86.Buf W SP s A al) (hD : VG.Proof.AesCcm.X86.Buf W SP s D n) :
    WP isa (VG.Impl.AesCcm.X86.mac v.callee v.suffix y) s (VG.Proof.AesCcm.X86.Absorbed K W SP s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (Spec.Cmac.zeros 16)
        (Spec.Ccm.format tl nonce (bytesAt s.mem (w64 A) al) (bytesAt s.mem (w64 D) n)))) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hy16 : y + 16 ≤ 2560 := by omega
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.b0_ok v L E hR S hnl h7 h13 ht4 ht16 hte hal hn hn32 hc0 hy)
    fun s₁ ⟨E₁, f₁, h₁, hrd₁, hwr₁⟩ => ?_)
  have S₁ := S.macR L hy f₁
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.aad_ok v L E₁ hR S₁.ctx S₁.rounds hy S₁.aad S₁.alen (hA.of_eq hrd₁ hwr₁) hal)
    fun s₂ M₂ => ?_)
  have S₂ := S₁.macR L hy M₂.frame
  have E₂ := M₂.env
  obtain ⟨s₃, run₃, hm₃, hbp, hsp, hrd₃, hwr₃⟩ := VG.Proof.AesCcm.X86.dataArgs_ok L E₂ S₂.data S₂.len
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : VG.Proof.AesCcm.X86.Env K W SP s₃ := E₂.keep (by rw [hbp, E₂.ebp]) (by rw [hsp, E₂.esp]) hrd₃ hwr₃
  have f₃ : Frame [VG.Proof.AesCcm.X86.wC W] s₂.mem s₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
  have fm₃ : Frame (VG.Proof.AesCcm.X86.macR W SP y) s₂.mem s₃.mem := f₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.X86.sub_mac (by simp)
  have S₃ := S₂.macR L hy fm₃
  have rd₃ : s₃.rd = s.rd := by rw [hrd₃, M₂.rd, hrd₁]
  have wr₃ : s₃.wr = s.wr := by rw [hwr₃, M₂.wr, hwr₁]
  have hd₃ : slotv s₃.mem W dO = D := by
    rw [hm₃, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  have hn₃ : slotv s₃.mem W nO = BitVec.ofNat 32 n := by rw [hm₃]; exact Mem.readW_writeW_self32 _ _ _
  refine WP.mono (VG.Proof.AesCcm.X86.absorbPad_ok v L E₃ hR S₃.ctx S₃.rounds hy (fun _ => hD.of_eq rd₃ wr₃) hn32 hd₃ hn₃) fun s₄ A₄ => ?_
  have f₂ : Frame (VG.Proof.AesCcm.X86.macR W SP y) s.mem s₂.mem := f₁.trans M₂.frame
  have hk := VG.Proof.AesCcm.X86.k_macR L hy16
  have hY₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 y) 16 = bytesAt s₂.mem (w64 W + BitVec.ofNat 64 y) 16 :=
    Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl <;> exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)
  refine ⟨A₄.env, (f₂.trans fm₃).trans A₄.frame, ?_, by rw [A₄.rd, rd₃], by rw [A₄.wr, wr₃]⟩
  have hl : nonce.length ≤ 15 := by omega
  rw [A₄.out, hY₃, M₂.out, h₁, VG.Proof.AesCcm.X86.ctxCiph_frame (f₂.trans fm₃) hk hRb, VG.Proof.AesCcm.X86.ctxCiph_frame f₁ hk hRb,
    VG.Proof.AesCcm.X86.buf_kept hD hy16 (f₂.trans fm₃), VG.Proof.AesCcm.X86.buf_kept hA hy16 f₁, Proof.AesCcm.format_eq tl hl, length_bytesAt,
    length_bytesAt, Proof.Cmac.chain_append, Proof.Cmac.chain_append]

/-! ## The tag -/

/-- The arguments of the call of `vg_aes_ctr32` making the tag: `Ctr₀` at
`W + 64`. -/
theorem tagArgs_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) (y : Nat) :
    ∃ s₃, runBlock isa (([.mov .eax (imm 0)] : List Instr) ++ ctrAt ++ keyArgs c1O ++
        ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm y), .mov .edi (imm 1)] : List Instr)) s = some s₃ ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩] s.mem s₃.mem ∧
      bytesAt s₃.mem (w64 W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce 0 ∧
      s₃.gpr .eax = K ∧ s₃.gpr .ecx = BitVec.ofNat 32 R ∧ s₃.gpr .edx = W + BitVec.ofNat 32 64 ∧
      s₃.gpr .ebx = W + BitVec.ofNat 32 y ∧ s₃.gpr .edi = BitVec.ofNat 32 1 ∧ s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧
      s₃.rd = s.rd ∧ s₃.wr = s.wr := by
  obtain ⟨s₁, run₁, hm₁, hax₁, hbp₁, hsp₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .eax (imm 0)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .eax = BitVec.ofNat 32 0 ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs []
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  have E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁ := E.keep (by rw [hbp₁, E.ebp]) (by rw [hsp₁, E.esp]) hrd₁ hwr₁
  obtain ⟨s₂, run₂, f₂, hc₂, hg₂, hrd₂, hwr₂⟩ :=
    VG.Proof.AesCcm.X86.ctrAt_ok L E₁ h7 h13 (by rw [hm₁]; exact hc0) (Nat.pow_pos (by decide)) (by decide) hax₁
  have hbp₂ : s₂.gpr .ebp = W := by rw [hg₂ _ (by decide) (by decide), hbp₁]
  have hsp₂ : s₂.gpr .esp = SP := by rw [hg₂ _ (by decide) (by decide), hsp₁]
  have k₂ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₂.mem W o = slotv s.mem W o := fun o h₁ h₂ => by
    rw [← hm₁]
    exact f₂.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
      (by decide)
  have hK₂ : slotv s₂.mem W ctxO = K := by rw [k₂ _ (by decide) (by decide)]; exact hK
  have hR₂ : slotv s₂.mem W roundsO = BitVec.ofNat 32 R := by rw [k₂ _ (by decide) (by decide)]; exact hRo
  have E₂ : VG.Proof.AesCcm.X86.Env K W SP s₂ := E₁.keep (by rw [hbp₂, hbp₁]) (by rw [hsp₂, hsp₁]) hrd₂ hwr₂
  obtain ⟨s₃, run₃, hm₃, hax, hcx, hdx, hbx, hdi, hbp₃, hsp₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      (keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm y), .mov .edi (imm 1)] : List Instr)) s₂ = some s₃ ∧
      s₃.mem = s₂.mem ∧ s₃.gpr .eax = K ∧ s₃.gpr .ecx = BitVec.ofNat 32 R ∧ s₃.gpr .edx = W + BitVec.ofNat 32 64 ∧
      s₃.gpr .ebx = W + BitVec.ofNat 32 y ∧ s₃.gpr .edi = BitVec.ofNat 32 1 ∧ s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [keyArgs, hbp₂, L.aW, E₂.perm.wR, hK₂, hR₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hK₂]
    · cregs [hR₂]
    · cregs [hbp₂]
    · cregs [hbp₂]
    · cregs []
    · cregs [hbp₂]
    · cregs [hsp₂]
    all_goals cmems []
  refine ⟨s₃, by
    rw [List.append_assoc]
    exact Proof.AesGcm.X86.runBlock_app_of (Proof.AesGcm.X86.runBlock_app_of run₁ run₂) run₃,
    by rw [hm₃, ← hm₁]; exact f₂, by rw [hm₃]; exact hc₂, hax, hcx, hdx, hbx, hdi, hbp₃, hsp₃,
    by rw [hrd₃, hrd₂, hrd₁], by rw [hwr₃, hwr₂, hwr₁]⟩

/-- The arguments of `tag`'s call, as `ctrCall_ok` and `ctrCall_ct` take them. -/
theorem tagCall_pre {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {y : Nat}
    (hy : y = 0 ∨ y = 96) :
    VG.Proof.AesCcm.X86.Src W SP s (W + BitVec.ofNat 32 y) (16 * 1) ∧ Covers [⟨w64 (W + BitVec.ofNat 32 y), 16 * 1⟩] s.wr ∧
      (⟨w64 (W + BitVec.ofNat 32 y), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ ∧
      (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 y), 16 * 1⟩ := by
  have hy' : y + 16 ≤ 384 := by rcases hy with rfl | rfl <;> decide
  have aY : w64 (W + BitVec.ofNat 32 y) = w64 W + BitVec.ofNat 64 y := L.aW (by omega)
  refine ⟨VG.Proof.AesCcm.X86.srcW L E.perm (t := y) (k := 16 * 1) (by omega), by rw [aY]; exact E.perm.wC (by omega), ?_,
    by rw [aY]; exact L.k_w.sub_right (Lay.wSub (by omega))⟩
  rw [aY]
  rcases hy with rfl | rfl
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)

/-- The MAC state at `W + y` XORed with `CIPH_K(Ctr₀)`. -/
theorem tag_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (VG.Impl.AesCcm.X86.tag v.callee y) s fun s' => VG.Proof.AesCcm.X86.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, VG.Proof.AesCcm.X86.wC W, below SP 56] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 0 (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16) := by
  obtain ⟨s₃, run₃, f₃, hc₃, hax, hcx, hdx, hbx, hdi, hbp₃, hsp₃, hrd₃, hwr₃⟩ :=
    VG.Proof.AesCcm.X86.tagArgs_ok L E hK hRo h7 h13 hc0 y
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : VG.Proof.AesCcm.X86.Env K W SP s₃ := E.keep (by rw [hbp₃, E.ebp]) (by rw [hsp₃, E.esp]) hrd₃ hwr₃
  have aY : w64 (W + BitVec.ofNat 32 y) = w64 W + BitVec.ofNat 64 y := L.aW (by omega)
  obtain ⟨hq, hqw, hqc, hqk⟩ := VG.Proof.AesCcm.X86.tagCall_pre L E₃ hy
  refine WP.mono (VG.Proof.AesCcm.X86.ctrCall_ok v L E₃ hR (c := 64) (by decide) hq hqc hqk hqw hax hcx hdx hbx hdi)
    fun s₄ ⟨E₄, rd₄, wr₄, _, f₄, o₄⟩ => ⟨E₄, by rw [rd₄, hrd₃], by rw [wr₄, hwr₃], ?_, ?_⟩
  · have f₄' := f₄
    rw [aY] at f₄'
    refine (f₃.sub fun r hr => ?_).trans (f₄'.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨w64 W + BitVec.ofNat 64 y, 16⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    have hc := Proof.AesCcm.ctr32_ccm (m := s₃.mem) (m' := s₄.mem) (K := w64 K) (C := w64 W + BitVec.ofNat 64 64)
      (D := w64 (W + BitVec.ofNat 32 y)) (R := R) (nonce := nonce) (by omega) (j := 0) (k := 1)
      (fun i hi => by
        rw [show i = 0 by omega, Nat.zero_add]
        show Spec.Gcm.ofBytes _ = _
        rw [hc₃]) o₄
    rw [Nat.mul_one, aY] at hc
    rw [hc, VG.Proof.AesCcm.X86.ctxCiph_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb,
      Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [← aY]; exact hqc) (by decide)]

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Crypt`. -/
section

/-!
# AES-CCM on x86: counter mode (`ctr`)

Untrusted: everything here is checked by Lean. `ctr` encrypts the whole
blocks of the data with one call of `vg_aes_ctr32` from `Ctr₁`, whose low 32
bits do not wrap around as there are fewer than 2²⁸ blocks (`ctrWhole_ok`),
then its last `n mod 16` bytes with `CIPH_K(Ctr₁₊ₙ/₁₆)`, which
`vg_aes_ctr32` writes over a zero block (`ctrTail_ok`): the data XORed with
CCM's keystream from `Ctr₁` (`ctr_ok`), which is its encryption
(`Proof.AesCcm.crypt_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop splitWhole dO nO)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold zero4_bytes' length_bytesAt and_self_beq32
  XorPre XorPost xorLoop_ok xorBytes shr4 and15 runBlock_app_of covers_left covers_off)

/-- What `ctr` writes: `Ctrⱼ` and the keystream block at `[64, 96)`, `[240, 2560)`, the stack and the data. -/
abbrev ctrR (W SP D : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 64, 32⟩, VG.Proof.AesCcm.X86.wC W, below SP 56, ⟨w64 D, n⟩]

/-- What `ctr` needs. -/
structure CtrCtx (K W SP : BitVec 32) (s : State) (R : Nat) (nonce : List Byte) (D : BitVec 32) (n : Nat) : Prop where
  lay : VG.Proof.AesCcm.X86.Lay K W SP
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  h7 : 7 ≤ nonce.length
  h13 : nonce.length ≤ 13
  hn : n < 256 ^ (15 - nonce.length)
  hn32 : n < 2 ^ 32
  c0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0
  buf : VG.Proof.AesCcm.X86.Buf W SP s D n
  dw : Covers [⟨w64 D, n⟩] s.wr
  dk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩

namespace CtrCtx

variable {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32} {n : Nat}
  (C : VG.Proof.AesCcm.X86.CtrCtx K W SP s R nonce D n)
include C

/-- The parts of `W` that `ctr` does not write. -/
theorem disj {d k : Nat} (h : d + k ≤ 64 ∨ (96 ≤ d ∧ d + k ≤ 240)) :
    ∀ r ∈ VG.Proof.AesCcm.X86.ctrR W SP D n, (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rcases h with h | h
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (C.lay.stk_w' (by omega)).symm
  · exact (C.buf.w.sub_right (Lay.wSub (by omega))).symm

theorem slot_kept {m : Mem} (hf : Frame (VG.Proof.AesCcm.X86.ctrR W SP D n) s.mem m) {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 240) :
    slotv m W o = slotv s.mem W o :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (C.disj (.inr ⟨by omega, h₂⟩)) (by decide)

theorem c0_kept {m : Mem} (hf : Frame (VG.Proof.AesCcm.X86.ctrR W SP D n) s.mem m) :
    bytesAt m (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
  rw [Proof.AesGcm.X86.bytesAt_frame hf (C.disj (.inl (by decide))) (by decide), C.c0]

theorem ciph_kept {m : Mem} (hf : Frame (VG.Proof.AesCcm.X86.ctrR W SP D n) s.mem m) :
    Spec.Ccm.ctxCiph m (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases C.rounds with h | h | h <;> subst h <;> decide
  refine VG.Proof.AesCcm.X86.ctxCiph_frame hf (fun r hr => ?_) hRb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.stk_k.symm
  · exact C.dk

end CtrCtx

/-- After the whole blocks. -/
structure CtrMid (K W SP : BitVec 32) (s : State) (R : Nat) (nonce : List Byte) (D : BitVec 32) (n : Nat) (t : State) :
    Prop where
  env : VG.Proof.AesCcm.X86.Env K W SP t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.AesCcm.X86.ctrR W SP D n) s.mem t.mem
  dO : slotv t.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16))
  nO : slotv t.mem W nO = BitVec.ofNat 32 (n % 16)
  done : bytesAt t.mem (w64 D) (16 * (n / 16)) =
    xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 1 (bytesAt s.mem (w64 D) (16 * (n / 16)))
  rest : bytesAt t.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
    bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)

/-! ## The whole blocks -/

/-- The data and its length into `dO` and `nO`, and split. -/
theorem ctrSplit_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {D : BitVec 32} {n : Nat}
    (hDp : slotv s.mem W dataO = D) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) :
    ∃ s₁, runBlock isa (([.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp nO) .eax] : List Instr) ++ splitWhole) s = some s₁ ∧
      s₁.gpr .ebx = D ∧ s₁.gpr .edi = BitVec.ofNat 32 (n / 16) ∧ s₁.zf = some (decide (n / 16 = 0)) ∧
      VG.Proof.AesCcm.X86.Env K W SP s₁ ∧ Frame [VG.Proof.AesCcm.X86.wC W] s.mem s₁.mem ∧ slotv s₁.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
      slotv s₁.mem W nO = BitVec.ofNat 32 (n % 16) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  obtain ⟨sa, runa, hma, hbpa, hspa, hrda, hwra⟩ : ∃ sa, runBlock isa
      [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO), .store (at_ .ebp nO) .eax] s =
        some sa ∧
      sa.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 dO) D).writeW (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 n) ∧
      sa.gpr .ebp = W ∧ sa.gpr .esp = SP ∧ sa.rd = s.rd ∧ sa.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hDp, hlen], ?_, ?_, ?_, ?_, ?_⟩
    · cmems [hDp, hlen]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  have Ea : VG.Proof.AesCcm.X86.Env K W SP sa := E.keep (by rw [hbpa, E.ebp]) (by rw [hspa, E.esp]) hrda hwra
  have hda : slotv sa.mem W dO = D := by
    rw [hma, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  have hna : slotv sa.mem W nO = BitVec.ofNat 32 n := by rw [hma]; exact Mem.readW_writeW_self32 _ _ _
  obtain ⟨s₁, run₁, hbx, hdi, hzf, hbp, hsp, hm₁, hrd₁, hwr₁⟩ := VG.Proof.AesCcm.X86.split_ok L Ea hda hna hn32
  have cw : ∀ d, 240 ≤ d → d + 4 ≤ 2560 → (VG.Proof.AesCcm.X86.wC W).Contains (w64 W + BitVec.ofNat 64 d) 4 := fun d h₁ h₂ =>
    Offset.contains (w64 W) h₁ (by omega) (by decide)
  refine ⟨s₁, runBlock_app_of runa run₁, hbx, hdi, hzf, Ea.keep (by rw [hbp, hbpa]) (by rw [hsp, hspa]) hrd₁ hwr₁,
    ?_, ?_, ?_, by rw [hrd₁, hrda], by rw [hwr₁, hwra]⟩
  · rw [hm₁, hma]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cw 272 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cw 276 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cw 276 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cw 272 (by decide) (by decide))
  · rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _
  · rw [hm₁, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _

/-- `Ctrᵢ` at `W + 64`, and the key schedule, the number of rounds and
`W + 64` in `eax`, `ecx`, `edx`, for `vg_aes_ctr32`. -/
theorem ctrArgs_ok {K W SP : BitVec 32} {s₁ : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁) {R : Nat}
    (hK₁ : slotv s₁.mem W ctxO = K) (hR₁ : slotv s₁.mem W roundsO = BitVec.ofNat 32 R) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {i : Nat}
    (hi : i < 256 ^ (15 - nonce.length)) (hi32 : i < 2 ^ 32) {Q : BitVec 32} {b : BitVec 32}
    (hbx : s₁.gpr .ebx = Q) (hdi : s₁.gpr .edi = b) :
    ∃ sc, runBlock isa (([.mov .eax (imm i)] : List Instr) ++ ctrAt ++ keyArgs c1O) s₁ = some sc ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩] s₁.mem sc.mem ∧
      bytesAt sc.mem (w64 W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i ∧
      sc.gpr .eax = K ∧ sc.gpr .ecx = BitVec.ofNat 32 R ∧ sc.gpr .edx = W + BitVec.ofNat 32 64 ∧ sc.gpr .ebx = Q ∧
      sc.gpr .edi = b ∧ sc.gpr .ebp = W ∧ sc.gpr .esp = SP ∧ sc.rd = s₁.rd ∧ sc.wr = s₁.wr := by
  obtain ⟨sa, runa, hma, haxa, hbxa, hdia, hbpa, hspa, hrda, hwra⟩ : ∃ sa, runBlock isa [.mov .eax (imm i)] s₁ =
      some sa ∧ sa.mem = s₁.mem ∧ sa.gpr .eax = BitVec.ofNat 32 i ∧ sa.gpr .ebx = Q ∧
      sa.gpr .edi = b ∧ sa.gpr .ebp = W ∧ sa.gpr .esp = SP ∧ sa.rd = s₁.rd ∧ sa.wr = s₁.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs []
    · cregs [hbx]
    · cregs [hdi]
    · cregs [E₁.ebp]
    · cregs [E₁.esp]
    all_goals cmems []
  have Ea : VG.Proof.AesCcm.X86.Env K W SP sa := E₁.keep (by rw [hbpa, E₁.ebp]) (by rw [hspa, E₁.esp]) hrda hwra
  obtain ⟨sb, runb, fb, hcb, hgb, hrdb, hwrb⟩ := VG.Proof.AesCcm.X86.ctrAt_ok L Ea h7 h13 (by rw [hma]; exact hc0) hi hi32 haxa
  have Eb : VG.Proof.AesCcm.X86.Env K W SP sb := Ea.keep (by rw [hgb .ebp (by decide) (by decide)]) (by rw [hgb .esp (by decide) (by decide)])
    hrdb hwrb
  have kb : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv sb.mem W o = slotv s₁.mem W o := fun o h₁ h₂ => by
    show sb.mem.readW (w64 W + BitVec.ofNat 64 o) 32 = _
    rw [fb.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
      (by decide), hma]
  have hKb : slotv sb.mem W ctxO = K := by rw [kb _ (by decide) (by decide)]; exact hK₁
  have hRb' : slotv sb.mem W roundsO = BitVec.ofNat 32 R := by rw [kb _ (by decide) (by decide)]; exact hR₁
  obtain ⟨sc, runc, hmc, hax, hcx, hdx, hbxc, hdic, hbpc, hspc, hrdc, hwrc⟩ : ∃ sc, runBlock isa (keyArgs c1O) sb =
      some sc ∧ sc.mem = sb.mem ∧ sc.gpr .eax = K ∧ sc.gpr .ecx = BitVec.ofNat 32 R ∧
      sc.gpr .edx = W + BitVec.ofNat 32 64 ∧ sc.gpr .ebx = Q ∧ sc.gpr .edi = b ∧
      sc.gpr .ebp = W ∧ sc.gpr .esp = SP ∧ sc.rd = sb.rd ∧ sc.wr = sb.wr := by
    refine ⟨_, by crun [keyArgs, Eb.ebp, L.aW, Eb.perm.wR, hKb, hRb'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hKb]
    · cregs [hRb']
    · cregs [Eb.ebp]
    · cregs [hgb .ebx (by decide) (by decide), hbxa]
    · cregs [hgb .edi (by decide) (by decide), hdia]
    · cregs [Eb.ebp]
    · cregs [Eb.esp]
    all_goals cmems []
  exact ⟨sc, runBlock_app_of (runBlock_app_of runa runb) runc, by rw [hmc, ← hma]; exact fb, by rw [hmc]; exact hcb,
    hax, hcx, hdx, hbxc, hdic, hbpc, hspc, by rw [hrdc, hrdb, hrda], by rw [hwrc, hwrb, hwra]⟩

/-- The whole blocks of the data, by one call of `vg_aes_ctr32` from `Ctr₁`. -/
theorem ctrWhole_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n : Nat} (C : VG.Proof.AesCcm.X86.CtrCtx K W SP s R nonce D n) (E : VG.Proof.AesCcm.X86.Env K W SP s) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hDp : slotv s.mem W dataO = D)
    (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) :
    WP isa (.seq (.block (([.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp nO) .eax] : List Instr) ++ splitWhole))
      (.ite .e (.block []) (.seq (.block (([.mov .eax (imm 1)] : List Instr) ++ ctrAt ++ keyArgs c1O)) (ctrCall v.callee)))) s
      (VG.Proof.AesCcm.X86.CtrMid K W SP s R nonce D n) := by
  have L := C.lay
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  obtain ⟨s₁, run₁, hbx, hdi, hzf, E₁, f₁, hd₁, hn₁, hrd₁, hwr₁⟩ := VG.Proof.AesCcm.X86.ctrSplit_ok L E hDp hlen C.hn32
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have fr₁ : Frame (VG.Proof.AesCcm.X86.ctrR W SP D n) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, fun _ h => h⟩
  have dD : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [VG.Proof.AesCcm.X86.wC W], (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l h r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (C.buf.w.sub_left (Offset.sub_base _ h)).sub_right (Lay.wSub (by decide))
  have hrest₁ : bytesAt s₁.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (dD (by omega)) (by omega)
  refine WP.ite (decide (n / 16 = 0)) (VG.Proof.AesCcm.X86.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n / 16 = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨s₁, rfl, E₁, hrd₁, hwr₁, fr₁, hd₁, hn₁, ?_, hrest₁⟩
    rw [h0, Nat.mul_zero]; rfl
  · have h0 : n / 16 ≠ 0 := of_decide_eq_false hf
    have k₁ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ => C.slot_kept fr₁ h₁ h₂
    obtain ⟨sc, runc, fc, hcc, hax, hcx, hdx, hbxc, hdic, hbpc, hspc, hrdc, hwrc⟩ :=
      VG.Proof.AesCcm.X86.ctrArgs_ok L E₁ (by rw [k₁ _ (by decide) (by decide)]; exact hK) (by rw [k₁ _ (by decide) (by decide)]; exact hRo)
        C.h7 C.h13 (C.c0_kept fr₁) (i := 1) (by
          have : 1 ≤ 256 ^ (15 - nonce.length) := Nat.pow_pos (by decide)
          have := C.hn
          omega) (by decide) hbx hdi
    refine WP.seq (WP.of_runBlock ⟨sc, runc, ?_⟩)
    have Ec : VG.Proof.AesCcm.X86.Env K W SP sc := E₁.keep (by rw [hbpc, E₁.ebp]) (by rw [hspc, E₁.esp]) hrdc hwrc
    have rdc : sc.rd = s.rd := by rw [hrdc, hrd₁]
    have wrc : sc.wr = s.wr := by rw [hwrc, hwr₁]
    have hq := VG.Proof.AesCcm.X86.srcBuf ((C.buf.take hb).of_eq rdc wrc)
    have hqc : (⟨w64 D, 16 * (n / 16)⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ :=
      (C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide))
    have hqk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, 16 * (n / 16)⟩ := C.dk.sub_right (Region.sub_prefix hb)
    have hqw : Covers [⟨w64 D, 16 * (n / 16)⟩] sc.wr := by
      rw [wrc]
      intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      exact C.dw a k ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
    refine WP.mono (VG.Proof.AesCcm.X86.ctrCall_ok v L Ec C.rounds (c := 64) (by decide) hq hqc hqk hqw hax hcx hdx hbxc hdic)
      fun s₄ ⟨E₄, rd₄, wr₄, _, f₄, o₄⟩ => ?_
    -- What was written.
    have fsc : Frame (VG.Proof.AesCcm.X86.ctrR W SP D n) s.mem sc.mem :=
      fr₁.trans (fc.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩)
    have f₄' : Frame (VG.Proof.AesCcm.X86.ctrR W SP D n) sc.mem s₄.mem := f₄.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨w64 D, n⟩, by simp, Region.sub_prefix hb⟩
      · exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨below SP 56, by simp, fun _ h => h⟩
    have k₄ : ∀ o, 240 ≤ o → o + 4 ≤ 384 → slotv s₄.mem W o = slotv sc.mem W o := fun o h₁ h₂ =>
      f₄.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
        · exact ((C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by omega))).symm
        · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
        · exact (L.stk_w' (by omega)).symm) (by decide)
    have kc : ∀ o, 240 ≤ o → o + 4 ≤ 384 → slotv sc.mem W o = slotv s₁.mem W o := fun o h₁ h₂ =>
      fc.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
        (by decide)
    refine ⟨E₄, by rw [rd₄, rdc], by rw [wr₄, wrc], fsc.trans f₄', by rw [k₄ _ (by decide) (by decide),
      kc _ (by decide) (by decide), hd₁], by rw [k₄ _ (by decide) (by decide), kc _ (by decide) (by decide), hn₁],
      ?_, ?_⟩
    · have hDsc : bytesAt sc.mem (w64 D) (16 * (n / 16)) = bytesAt s.mem (w64 D) (16 * (n / 16)) := by
        rw [Proof.AesGcm.X86.bytesAt_frame fc (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide)))
            (by have := C.hn32; omega),
          Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide)))
            (by have := C.hn32; omega)]
      have hc := Proof.AesCcm.ctr32_ccm (m := sc.mem) (m' := s₄.mem) (K := w64 K) (C := w64 W + BitVec.ofNat 64 64)
        (D := w64 D) (R := R) (nonce := nonce) (by have := C.h13; omega) (j := 1) (k := n / 16)
        (fun i hi => by
          rw [show Spec.Gcm.blockAt sc.mem (w64 W + BitVec.ofNat 64 64) = Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce 1)
            from by show Spec.Gcm.ofBytes _ = _; rw [hcc]]
          exact Proof.AesCcm.repeat_inc32_ctrBlock C.h7 C.h13 (j := 1) (k := n / 16)
            (by have := C.hn32; omega) (by have := C.hn; omega) i hi) o₄
      rw [hc, C.ciph_kept fsc, hDsc]
    · have sR : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ ⟨w64 D, n⟩ :=
        Offset.sub_base (w64 D) (d := 16 * (n / 16)) (n := n % 16) (k := n) (by omega)
      have hlt : n % 16 ≤ 2 ^ 64 := by omega
      rw [Proof.AesGcm.X86.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (C.buf.w.sub_left sR).sub_right (Lay.wSub (by decide))
        · simpa using Offset.disjoint (w64 D) (d := 16 * (n / 16)) (n := n % 16) (e := 0) (k := 16 * (n / 16))
            (.inr (by omega)) (by have := C.hn32; omega) (by have := C.hn32; omega)
        · exact (C.buf.w.sub_left sR).sub_right (Lay.wSub (by decide))
        · exact (C.buf.stk.sub_right sR).symm) hlt,
        Proof.AesGcm.X86.bytesAt_frame fc (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (C.buf.w.sub_left sR).sub_right (Lay.wSub (by decide))) hlt, hrest₁]

/-! ## The last bytes -/

/-- `Ctrⱼ`, `j = ⌊n / 16⌋ + 1`, at `W + 64`, the keystream block at `W + 80`
zeroed, and the arguments of `vg_aes_ctr32` to encrypt it. -/
theorem ctrTailArgs_ok {K W SP : BitVec 32} {t₀ : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E₀ : VG.Proof.AesCcm.X86.Env K W SP t₀) {R : Nat}
    (hK₀ : slotv t₀.mem W ctxO = K) (hR₀ : slotv t₀.mem W roundsO = BitVec.ofNat 32 R) {n : Nat}
    (hl₀ : slotv t₀.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt t₀.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (hj : n / 16 + 1 < 256 ^ (15 - nonce.length)) :
    ∃ tc, runBlock isa (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++ zero4 ksO ++
        keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)) t₀ = some tc ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩] t₀.mem tc.mem ∧
      bytesAt tc.mem (w64 W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (n / 16 + 1) ∧
      bytesAt tc.mem (w64 W + BitVec.ofNat 64 80) 16 = Spec.Gcm.zeros 16 ∧
      tc.gpr .eax = K ∧ tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
      tc.gpr .esp = SP ∧ tc.rd = t₀.rd ∧ tc.wr = t₀.wr := by
  have hbp₀ := E₀.ebp
  have hsp₀ := E₀.esp
  obtain ⟨ta, runa, hma, haxa, hbpa, hspa, hrda, hwra⟩ : ∃ ta, runBlock isa
      [.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] t₀ = some ta ∧ ta.mem = t₀.mem ∧
      ta.gpr .eax = BitVec.ofNat 32 (n / 16 + 1) ∧ ta.gpr .ebp = W ∧ ta.gpr .esp = SP ∧ ta.rd = t₀.rd ∧
      ta.wr = t₀.wr := by
    refine ⟨_, by crun [hbp₀, L.aW, E₀.perm.wR, hl₀], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hl₀, VG.Proof.AesGcm.X86.shr4 hn32]; exact (BitVec.ofNat_add _ _).symm
    · cregs [hbp₀]
    · cregs [hsp₀]
    all_goals cmems []
  have Ea : VG.Proof.AesCcm.X86.Env K W SP ta := E₀.keep (by rw [hbpa, hbp₀]) (by rw [hspa, hsp₀]) hrda hwra
  obtain ⟨tb, runb, fb, hcb, hgb, hrdb, hwrb⟩ := VG.Proof.AesCcm.X86.ctrAt_ok L Ea h7 h13 (by rw [hma]; exact hc0) hj (by omega) haxa
  have hbpb : tb.gpr .ebp = W := by rw [hgb .ebp (by decide) (by decide), hbpa]
  have hspb : tb.gpr .esp = SP := by rw [hgb .esp (by decide) (by decide), hspa]
  have Eb : VG.Proof.AesCcm.X86.Env K W SP tb := Ea.keep (by rw [hbpb, hbpa]) (by rw [hspb, hspa]) hrdb hwrb
  have kb : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv tb.mem W o = slotv t₀.mem W o := fun o h₁ h₂ => by
    show tb.mem.readW (w64 W + BitVec.ofNat 64 o) 32 = _
    rw [fb.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
      (by decide), hma]
  have hKb : slotv tb.mem W ctxO = K := by rw [kb _ (by decide) (by decide)]; exact hK₀
  have hRb' : slotv tb.mem W roundsO = BitVec.ofNat 32 R := by rw [kb _ (by decide) (by decide)]; exact hR₀
  have hz := zero4_fold tb.mem W 80
  simp only [Nat.reduceAdd] at hz
  obtain ⟨tc, runc, hmc, hax, hcx, hdx, hbx, hdi, hbpc, hspc, hrdc, hwrc⟩ : ∃ tc, runBlock isa
      (zero4 ksO ++ (keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr))) tb =
        some tc ∧ tc.mem = Cmac.zero4 tb.mem (w64 W + BitVec.ofNat 64 80) ∧ tc.gpr .eax = K ∧
      tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
      tc.gpr .esp = SP ∧ tc.rd = tb.rd ∧ tc.wr = tb.wr := by
    refine ⟨_, by crun [zero4, keyArgs, hbpb, L.aW, Eb.perm.wW, Eb.perm.wR, hKb, hRb'], ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · cmems [hz]
    · cregs [hKb]
    · cregs [hRb']
    · cregs [hbpb]
    · cregs [hbpb]
    · cregs []
    · cregs [hbpb]
    · cregs [hspb]
    all_goals cmems []
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 80, 16⟩] tb.mem tc.mem := by rw [hmc]; exact Cmac.frame_store4 _ _ _ _ _
  refine ⟨tc, by
      simp only [List.append_assoc]
      exact runBlock_app_of runa (runBlock_app_of runb runc), ?_, ?_, by rw [hmc, zero4_bytes'],
    hax, hcx, hdx, hbx, hdi, hbpc, hspc, by rw [hrdc, hrdb, hrda], by rw [hwrc, hwrb, hwra]⟩
  · rw [← hma]
    exact (fb.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩).trans
      (fz.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩)
  · rw [Proof.AesGcm.X86.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), hcb]

/-- The arguments of the XOR of the last bytes with the keystream block. -/
theorem xorArgs_ok {K W SP : BitVec 32} {td : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (Ed : VG.Proof.AesCcm.X86.Env K W SP td) {P : BitVec 32} {t : Nat}
    (hdd : slotv td.mem W dO = P) (hnd : slotv td.mem W nO = BitVec.ofNat 32 t) :
    ∃ te, runBlock isa
      [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksO), .mov .ecx (slot nO)] td = some te ∧
      te.mem = td.mem ∧ te.gpr .edi = P ∧ te.gpr .edx = W + BitVec.ofNat 32 80 ∧
      te.gpr .ecx = BitVec.ofNat 32 t ∧ te.gpr .ebp = W ∧ te.gpr .esp = SP ∧ te.rd = td.rd ∧ te.wr = td.wr := by
  have hbpd := Ed.ebp
  refine ⟨_, by crun [hbpd, L.aW, Ed.perm.wR, hdd, hnd], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hdd]
  · cregs [hbpd]
  · cregs [hnd]
  · cregs [hbpd]
  · cregs [Ed.esp]
  all_goals cmems []

/-- The last `n mod 16` bytes, with `CIPH_K(Ctr₁₊ₙ/₁₆)`, after the whole blocks. -/
theorem ctrTail_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n : Nat} (C : VG.Proof.AesCcm.X86.CtrCtx K W SP s R nonce D n) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) {t : State}
    (I : VG.Proof.AesCcm.X86.CtrMid K W SP s R nonce D n t) :
    WP isa (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
      (.ite .e (.block [])
        (.seq (.block (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++ zero4 ksO ++
            keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)))
        (.seq (ctrCall v.callee)
          (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksO), .mov .ecx (slot nO)])
            xorLoop))))) t
      fun t' => VG.Proof.AesCcm.X86.Env K W SP t' ∧ t'.rd = s.rd ∧ t'.wr = s.wr ∧ Frame (VG.Proof.AesCcm.X86.ctrR W SP D n) s.mem t'.mem ∧
        bytesAt t'.mem (w64 D) n = xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 1 (bytesAt s.mem (w64 D) n) := by
  have L := C.lay
  have E := I.env
  have hn32 := C.hn32
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have k₀ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv t.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    C.slot_kept I.frame h₁ h₂
  obtain ⟨t₀, run₀, hm₀, hzf, hbp₀, hsp₀, hrd₀, hwr₀⟩ := VG.Proof.AesCcm.X86.testN_ok L E (r := n % 16) (by omega) I.nO
  refine WP.seq (WP.of_runBlock ⟨t₀, run₀, ?_⟩)
  have E₀ : VG.Proof.AesCcm.X86.Env K W SP t₀ := E.keep (by rw [hbp₀, E.ebp]) (by rw [hsp₀, E.esp]) hrd₀ hwr₀
  refine WP.ite (decide (n % 16 = 0)) (VG.Proof.AesCcm.X86.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨t₀, rfl, E₀, by rw [hrd₀, I.rd], by rw [hwr₀, I.wr], by rw [hm₀]; exact I.frame, ?_⟩
    have hd := I.done
    rw [show 16 * (n / 16) = n by omega] at hd
    rw [hm₀, hd]
  · have h0 : n % 16 ≠ 0 := of_decide_eq_false hf
    have hj : n / 16 + 1 < 256 ^ (15 - nonce.length) := by have := C.hn; omega
    obtain ⟨tc, runc, ft, hcc, hz80, hax, hcx, hdx, hbx, hdi, hbpc, hspc, hrdc, hwrc⟩ :=
      VG.Proof.AesCcm.X86.ctrTailArgs_ok L E₀ (by rw [hm₀, k₀ _ (by decide) (by decide)]; exact hK)
        (by rw [hm₀, k₀ _ (by decide) (by decide)]; exact hRo) (by rw [hm₀, k₀ _ (by decide) (by decide)]; exact hlen)
        hn32 C.h7 C.h13 (by rw [hm₀]; exact C.c0_kept I.frame) hj
    refine WP.seq (WP.of_runBlock ⟨tc, runc, ?_⟩)
    have Ec : VG.Proof.AesCcm.X86.Env K W SP tc := E₀.keep (by rw [hbpc, hbp₀]) (by rw [hspc, hsp₀]) hrdc hwrc
    -- The keystream block.
    have hq := VG.Proof.AesCcm.X86.srcW (s := tc) L Ec.perm (t := 80) (k := 16 * 1) (by decide)
    have a80 : w64 (W + BitVec.ofNat 32 80) = w64 W + BitVec.ofNat 64 80 := L.aW (by decide)
    have hqc : (⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ := by
      rw [a80]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    have hqk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ := by
      rw [a80]; exact L.k_w.sub_right (Lay.wSub (by decide))
    have hqw : Covers [⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩] tc.wr := by rw [a80]; exact Ec.perm.wC (by decide)
    refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.ctrCall_ok v L Ec C.rounds (c := 64) (by decide) hq hqc hqk hqw hax hcx hdx hbx hdi)
      fun td ⟨Ed, rdd, wrd, _, fd, od⟩ => ?_)
    -- What was written before the XOR.
    have fd' := fd
    rw [a80] at fd'
    have fbd : Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 56]
        t.mem td.mem := by
      rw [← hm₀]
      refine (ft.sub fun r hr => ?_).trans (fd'.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨below SP 56, by simp, fun _ h => h⟩
    have fR : Frame (VG.Proof.AesCcm.X86.ctrR W SP D n) s.mem td.mem := I.frame.trans (fbd.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
    have kd : ∀ o, 96 ≤ o → o + 4 ≤ 384 → slotv td.mem W o = slotv t.mem W o := fun o h₁ h₂ =>
      fbd.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
        · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
        · exact (L.stk_w' (by omega)).symm) (by decide)
    have hbpd : td.gpr .ebp = W := Ed.ebp
    -- The XOR.
    obtain ⟨te, rune, hme, hdie, hdxe, hcxe, hbpe, hspe, hrde, hwre⟩ :=
      VG.Proof.AesCcm.X86.xorArgs_ok L Ed (P := D + BitVec.ofNat 32 (16 * (n / 16))) (t := n % 16) (by rw [kd _ (by decide) (by decide)]; exact I.dO)
        (by rw [kd _ (by decide) (by decide)]; exact I.nO)
    refine WP.seq (WP.of_runBlock ⟨te, rune, ?_⟩)
    have rde : te.rd = s.rd := by rw [hrde, rdd, hrdc, hrd₀, I.rd]
    have wre : te.wr = s.wr := by rw [hwre, wrd, hwrc, hwr₀, I.wr]
    have hw : D.toNat + 16 * (n / 16) < 2 ^ 32 := by have := C.buf.wrap; omega
    have pT : w64 (D + BitVec.ofNat 32 (16 * (n / 16))) = w64 D + BitVec.ofNat 64 (16 * (n / 16)) := Buf.ptr hw
    have sR : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ ⟨w64 D, n⟩ :=
      Offset.sub_base (w64 D) (d := 16 * (n / 16)) (n := n % 16) (k := n) (by omega)
    have xp : XorPre te (W + BitVec.ofNat 32 80) (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) := by
      refine ⟨hdxe, hdie, hcxe, by omega, by omega, by rw [L.nW (by decide)]; have := L.fw; omega,
        by rw [toNat_add32 hw]; have := C.buf.wrap; omega, ?_, ?_, ?_⟩
      · rw [a80]; exact covers_left (Perm.wC (Ed.perm.of_eq hrde hwre) (d := 80) (n := n % 16) (by omega))
      · rw [pT, wre]; exact covers_off C.dw (by omega) (by have := C.buf.lt; omega)
      · rw [a80, pT]; exact ((C.buf.w.sub_left sR).sub_right (Lay.wSub (d := 80) (n := n % 16) (by omega))).symm
    refine WP.mono (xorLoop_ok te xp) fun tf P => ?_
    obtain ⟨xs, hxs⟩ : ∃ xs, xs = xorBytes te.mem (w64 (D + BitVec.ofNat 32 (16 * (n / 16))))
        (w64 (W + BitVec.ofNat 32 80)) (n % 16) := ⟨_, rfl⟩
    have hm₄ := P.mem
    rw [← hxs] at hm₄
    have hxl : xs.length = n % 16 := by simp [hxs, xorBytes, length_bytesAt]
    have fw : Frame [⟨w64 D, n⟩] te.mem tf.mem := by
      rw [hm₄, pT]
      exact VG.WriteBytes.writeBytes_frame _ _ _ (by
        rw [hxl]; exact Offset.contains_base (w64 D) (show 16 * (n / 16) + n % 16 ≤ n by omega)
          (by have := C.buf.lt; omega))
    refine ⟨E.keep (by rw [P.other _ (by decide) (by decide) (by decide) (by decide) (by decide), hbpe, E.ebp])
        (by rw [P.other _ (by decide) (by decide) (by decide) (by decide) (by decide), hspe, E.esp])
        (by rw [P.rd, rde, I.rd]) (by rw [P.wr, wre, I.wr]), by rw [P.rd, rde], by rw [P.wr, wre], ?_, ?_⟩
    · rw [← hme] at fR
      exact fR.trans (fw.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
    · -- The bytes.
      have dD : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 64, 32⟩ : Region),
          ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 56], (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
        intro a l hl r hr
        have sA : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base (w64 D) hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
        · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
        · exact (C.buf.stk.sub_right sA).symm
      have h₁ : bytesAt te.mem (w64 D) (16 * (n / 16)) = bytesAt t.mem (w64 D) (16 * (n / 16)) := by
        rw [hme]
        have := Proof.AesGcm.X86.bytesAt_frame fbd (dD (a := 0) (l := 16 * (n / 16)) (by omega)) (by omega)
        rwa [BitVec.add_zero] at this
      have h₂ : bytesAt te.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
          bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
        rw [hme, Proof.AesGcm.X86.bytesAt_frame fbd (dD (by omega)) (by omega), I.rest]
      have hBC : BlockCipher (Spec.Ccm.ctxCiph s.mem (w64 K) R) := fun x => Proof.Cmac.aesWith_length _ _ x
      have fRc : Frame (VG.Proof.AesCcm.X86.ctrR W SP D n) s.mem tc.mem := I.frame.trans (by
        rw [← hm₀]
        exact ft.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
      have hks : bytesAt te.mem (w64 W + BitVec.ofNat 64 80) 16 =
          Spec.Ccm.ctxCiph s.mem (w64 K) R (Spec.Ccm.ctrBlock nonce (n / 16 + 1)) := by
        have hx := Proof.AesCcm.ctr32_ccm (m := tc.mem) (m' := td.mem) (K := w64 K) (C := w64 W + BitVec.ofNat 64 64)
          (D := w64 (W + BitVec.ofNat 32 80)) (R := R) (nonce := nonce) (by have := C.h13; omega) (k := 1)
          (j := n / 16 + 1) (fun i hi => by
            rw [show i = 0 by omega, Nat.add_zero]
            show Spec.Gcm.ofBytes _ = _
            rw [hcc]) od
        rw [Nat.mul_one, a80] at hx
        rw [hme, hx, hz80, C.ciph_kept fRc]
        exact Proof.AesCcm.xorFrom_zeros hBC _ _
      have ht := Proof.AesCcm.xorFrom_tail (ciph := Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce (n / 16 + 1)
        (d := bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)) (by rw [length_bytesAt]; omega)
      rw [length_bytesAt, hBC] at ht
      have ht' := ht.resolve_right (by omega)
      rw [hm₄, pT, bytesAt_writeBytes_at te.mem (w64 D) xs (by rw [hxl]; omega) (by have := C.buf.lt; omega),
        List.drop_eq_nil_of_le (by rw [length_bytesAt, hxl]; omega), List.append_nil,
        ← Proof.AesCcm.bytesAt_prefix te.mem (w64 D) hb, h₁, I.done, hxs, xorBytes, pT, a80, h₂,
        Proof.AesCcm.bytesAt_prefix te.mem (w64 W + BitVec.ofNat 64 80) (show n % 16 ≤ 16 by omega), hks, ht']
      conv => rhs; rw [show n = 16 * (n / 16) + n % 16 from (Nat.div_add_mod n 16).symm]
      rw [Proof.Cmac.Stream.bytesAt_append, Proof.AesCcm.xorFrom_append _ _ _ (length_bytesAt _ _ _),
        Nat.add_comm 1 (n / 16)]

/-- Counter mode: the data XORed with CCM's keystream from `Ctr₁`. -/
theorem ctr_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n : Nat} (C : VG.Proof.AesCcm.X86.CtrCtx K W SP s R nonce D n) (E : VG.Proof.AesCcm.X86.Env K W SP s) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hDp : slotv s.mem W dataO = D)
    (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) :
    WP isa (VG.Impl.AesCcm.X86.ctr v.callee) s fun s' => VG.Proof.AesCcm.X86.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (VG.Proof.AesCcm.X86.ctrR W SP D n) s.mem s'.mem ∧
      bytesAt s'.mem (w64 D) n = xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 1 (bytesAt s.mem (w64 D) n) :=
  VG.Proof.AesCcm.X86.seq_assoc (WP.seq (WP.mono (VG.Proof.AesCcm.X86.ctrWhole_ok v C E hK hRo hDp hlen) fun _ I => VG.Proof.AesCcm.X86.ctrTail_ok v C hK hRo hlen I))


end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Entry`. -/
section

/-!
# AES-CCM on x86: the entry and the exit

Untrusted: everything here is checked by Lean. The entry (`entry_ok`) saves
our caller's registers in `W` (AES-GCM's `save_ok`), copies the stack
arguments into their slots (`keeps_ok`): the slots (`Slots`) hold the
arguments. The exit is AES-GCM's (`exit_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt tglO tpO)
open VG.Proof.AesGcm.X86 (w64 slotv argA argsR argA_contains argA_sub SavedAt save_ok KeepEnv keeps_ok keepR
  runBlock_app_of in_off)

/-- The arguments the entry copies, and where. -/
abbrev entryPs : List (Nat × Nat) :=
  [(0, ctxO), (1, roundsO), (2, nonceO), (3, nlenO), (4, aadO), (5, alenO), (6, dataO), (7, lenO), (8, tpO),
    (9, tglO)]

theorem ccmEntry_eq : ccmEntry = entry 10 (entryPs.flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2)) := rfl

/-- What the entry leaves. -/
structure Entered (s : State) (W : BitVec 32) (s' : State) : Prop where
  ebp : s'.gpr .ebp = W
  esp : s'.gpr .esp = s.gpr .esp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : SavedAt s'.mem W s
  slots : ∀ p ∈ VG.Proof.AesCcm.X86.entryPs, slotv s'.mem W p.2 = VG.X86.arg s p.1
  frame : Frame [⟨w64 W + BitVec.ofNat 64 128, 2432⟩] s.mem s'.mem

/-- The entry, from `W` (the stack argument 10). -/
theorem entry_ok {s : State} {W : BitVec 32} (hW : VG.X86.arg s 10 = W) (wW : Covers [⟨w64 W, 2560⟩] s.wr)
    (rA : Covers [argsR (s.gpr .esp) 11] (s.rd ++ s.wr)) (aw : (argsR (s.gpr .esp) 11).Disjoint ⟨w64 W, 2560⟩)
    (fa : (s.gpr .esp).toNat + 4 + 4 * 11 ≤ 2 ^ 32) (fw : W.toNat + 2560 ≤ 2 ^ 32) :
    WP isa ccmEntry s (VG.Proof.AesCcm.X86.Entered s W) := by
  rw [VG.Proof.AesCcm.X86.ccmEntry_eq]
  generalize hSP : s.gpr .esp = SP at rA aw fa
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 10) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.seq (WP.of_runBlock ⟨_, by crun [hSP, i₀], ?_⟩)
  have hax : (s.setReg .eax (s.mem.readW (argA SP 10) 32)).gpr .eax = W := by
    rw [gpr_setReg_self, ← hSP]; exact hW
  set s₀ := s.setReg .eax (s.mem.readW (argA SP 10) 32) with hs₀
  obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := save_ok s₀ hax (by rw [hs₀]; exact wW) fw
  have sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide), hSP]
  have f₁' : Frame [⟨w64 W + BitVec.ofNat 64 128, 16⟩] s.mem s₁.mem := f₁
  have argW : ∀ {i}, i < 11 → ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region)],
      (⟨argA SP i, 4⟩ : Region).Disjoint r := fun hi _ _ hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (aw.sub_left (argA_sub hi fa)).sub_right (Lay.wSub hk)
  have hA₁ : ∀ i < 11, s₁.mem.readW (argA SP i) 32 = VG.X86.arg s i := fun i hi => by
    rw [f₁'.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (argW hi (by decide)) (by decide)]
    rw [VG.X86.arg, argAddr, hSP]
  have ke : KeepEnv W SP 11 s₁ := ⟨bp₁, sp₁, by rw [wr₁]; exact wW, by rw [rd₁, wr₁]; exact rA, aw, fa, fw⟩
  obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := keeps_ok VG.Proof.AesCcm.X86.entryPs (fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) ke
  have bp₃ : s₃.gpr .ebp = W := by rw [g₃ _ (by decide), bp₁]
  have sp₃ : s₃.gpr .esp = SP := by rw [g₃ _ (by decide), sp₁]
  refine WP.of_runBlock ⟨_, runBlock_app_of run₁ run₃, ?_⟩
  -- What the entry wrote.
  have f₃' : Frame [⟨w64 W + BitVec.ofNat 64 128, 2432⟩] s.mem s₃.mem := by
    refine (f₁'.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hsv : SavedAt s₃.mem W s := by
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
  refine ⟨bp₃, by rw [sp₃, hSP], by rw [rd₃, rd₁]; rfl, by rw [wr₃, wr₁]; rfl, hsv, ?_, f₃'⟩
  intro p hp
  have e := sl₃ p hp
  have hp1 : p.1 < 11 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [hA₁ p.1 hp1] at e
  exact e

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Args`. -/
section

/-!
# AES-CCM on x86: the arguments

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`args_of_seal`, `args_of_open`).
Between the entry and the exit, the pieces only write the parts of `W` in
`mutR`, the stack below `SP` and the data, so they keep the slots, the saved
registers, the key schedule, the nonce and the associated data.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 slotv argsR argsR_eq below_eq SavedAt savedR ofNat_toNat32)

/-- What `seal` and `open` are given: the key schedule at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`), the working
space at `W` and the stack pointer `SP`. -/
structure Args (s : State) (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) : Prop where
  lay : VG.Proof.AesCcm.X86.Lay K W SP
  perm : VG.Proof.AesCcm.X86.Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : VG.Proof.AesCcm.X86.Buf W SP s N nl
  aad : VG.Proof.AesCcm.X86.Buf W SP s A al
  data : VG.Proof.AesCcm.X86.Buf W SP s D n
  tag : VG.Proof.AesCcm.X86.Buf W SP s T tl
  dw : Covers [⟨w64 D, n⟩] s.wr
  dk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩
  nd : (⟨w64 N, nl⟩ : Region).Disjoint ⟨w64 D, n⟩
  ad : (⟨w64 A, al⟩ : Region).Disjoint ⟨w64 D, n⟩
  td : (⟨w64 T, tl⟩ : Region).Disjoint ⟨w64 D, n⟩
  h7 : 7 ≤ nl
  h13 : nl ≤ 13
  t4 : 4 ≤ tl
  t16 : tl ≤ 16
  te : tl % 2 = 0
  hn : n < 256 ^ (15 - nl)
  al32 : al < 2 ^ 32
  n32 : n < 2 ^ 32
  retW : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  retD : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 D, n⟩
  retT : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 T, tl⟩
  args : Covers [argsR SP 11] (s.rd ++ s.wr)
  argsW : (argsR SP 11).Disjoint ⟨w64 W, 2560⟩
  fa : SP.toNat + 4 + 4 * 11 ≤ 2 ^ 32

/-- `Args`, from what both preconditions say, with the key schedule, the
nonce, the associated data and the tag readable and the data, the working
space and the arguments writable. -/
theorem args_of_lay {s : State} (h : VG.Proof.AesCcm.X86.oneLay s)
    (mrd : ∀ r ∈ [VG.Proof.AesCcm.X86.schR s, VG.Proof.AesCcm.X86.nonceR s, VG.Proof.AesCcm.X86.aadR s, VG.Proof.AesCcm.X86.tagR s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [VG.Proof.AesCcm.X86.dataR s, VG.Proof.AesCcm.X86.workR s, VG.Proof.AesCcm.X86.argsR' s], Covers [r] s.wr) :
    VG.Proof.AesCcm.X86.Args s (VG.X86.arg s 0) (VG.X86.arg s 10) (s.gpr .esp) (VG.X86.arg s 2) (VG.X86.arg s 4) (VG.X86.arg s 6) (VG.X86.arg s 8) (VG.X86.arg s 1).toNat
      (VG.X86.arg s 3).toNat (VG.X86.arg s 5).toNat (VG.X86.arg s 7).toNat (VG.X86.arg s 9).toNat := by
  simp only [VG.Proof.AesCcm.X86.oneLay, VG.Proof.AesCcm.X86.stackR] at h
  obtain ⟨d1, d2, _, d4, d5, _, d7, d8, _, d10, d11, _, d13, _, d15, _, _, _, d19, d20, d21, _,
    b1, b2, b3, b4, b5, b6, _, f1, f2, f3, f4, f5, f6, hsp, hfa, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  rw [show (56 : Addr) = BitVec.ofNat 64 56 from rfl, VG.Proof.AesGcm.X86.below_eq hsp] at b1 b2 b3 b4 b5 b6
  exact {
    lay := ⟨f1, f6, hsp, d2, b1, b6⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), f2, d5, b2⟩
    aad := ⟨mrd _ (by simp), f3, d8, b3⟩
    data := ⟨Proof.AesGcm.X86.covers_left (mwr _ (by simp)), f4, d11, b4⟩
    tag := ⟨mrd _ (by simp), f5, d13, b5⟩
    dw := mwr _ (by simp)
    dk := d1
    nd := d4
    ad := d7
    td := d10.symm
    h7 := hn7
    h13 := hn13
    t4 := ht4
    t16 := ht16
    te := hte
    hn := hp
    al32 := BitVec.isLt _
    n32 := BitVec.isLt _
    retW := d21
    retD := d19
    retT := d20
    args := by rw [argsR_eq]; exact Proof.AesGcm.X86.covers_left (mwr _ (by simp))
    argsW := by rw [argsR_eq]; exact d15.symm
    fa := by omega }

theorem args_of_seal {s : State} (h : VG.Proof.AesCcm.X86.sealPre s) :
    VG.Proof.AesCcm.X86.Args s (VG.X86.arg s 0) (VG.X86.arg s 10) (s.gpr .esp) (VG.X86.arg s 2) (VG.X86.arg s 4) (VG.X86.arg s 6) (VG.X86.arg s 8) (VG.X86.arg s 1).toNat
      (VG.X86.arg s 3).toNat (VG.X86.arg s 5).toNat (VG.X86.arg s 7).toNat (VG.X86.arg s 9).toNat := by
  obtain ⟨hrd, hwr, hl⟩ := h
  refine VG.Proof.AesCcm.X86.args_of_lay hl (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact VG.Proof.AesCcm.X86.covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact VG.Proof.AesCcm.X86.covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact VG.Proof.AesCcm.X86.covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact VG.Proof.AesCcm.X86.covers_of_mem (List.mem_append_right _ (by rw [hwr]; simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact VG.Proof.AesCcm.X86.covers_of_mem (by rw [hwr]; simp)

/-- In `seal`, the tag is writable. -/
theorem tag_wr {s : State} (h : VG.Proof.AesCcm.X86.sealPre s) : Covers [VG.Proof.AesCcm.X86.tagR s] s.wr :=
  VG.Proof.AesCcm.X86.covers_of_mem (by rw [h.2.1]; simp)

theorem args_of_open {s : State} (h : VG.Proof.AesCcm.X86.openPre s) :
    VG.Proof.AesCcm.X86.Args s (VG.X86.arg s 0) (VG.X86.arg s 10) (s.gpr .esp) (VG.X86.arg s 2) (VG.X86.arg s 4) (VG.X86.arg s 6) (VG.X86.arg s 8) (VG.X86.arg s 1).toNat
      (VG.X86.arg s 3).toNat (VG.X86.arg s 5).toNat (VG.X86.arg s 7).toNat (VG.X86.arg s 9).toNat := by
  obtain ⟨hrd, hwr, hl⟩ := h
  exact VG.Proof.AesCcm.X86.args_of_lay hl (fun r hr => VG.Proof.AesCcm.X86.covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr)))
    (fun r hr => VG.Proof.AesCcm.X86.covers_of_mem (by rw [hwr]; exact hr))

/-! ## What the pieces keep -/

section
variable {K W SP D : BitVec 32} {n : Nat} {m m' : Mem}

theorem saved_mut (L : VG.Proof.AesCcm.X86.Lay K W SP) (hD : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2560⟩)
    (hf : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) m m') {s₀ : State} (S : SavedAt m W s₀) : SavedAt m' W s₀ :=
  S.frame hf fun r hr => (VG.Proof.AesCcm.X86.kept_mut L hD (d := 128) (k := 16) (.inl ⟨by decide, by decide⟩) r hr)

theorem ciph_mut (L : VG.Proof.AesCcm.X86.Lay K W SP) (hdk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hf : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) m m') :
    Spec.Ccm.ctxCiph m' (w64 K) R = Spec.Ccm.ctxCiph m (w64 K) R :=
  VG.Proof.AesCcm.X86.ctxCiph_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact L.k_w.sub_right (Region.sub_prefix (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.stk_k.symm
    · exact hdk) (by rcases hR with h | h | h <;> subst h <;> decide)

theorem buf_mut {s : State} {P : BitVec 32} {len : Nat} (hP : VG.Proof.AesCcm.X86.Buf W SP s P len)
    (hPD : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 D, n⟩) (hf : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) m m') :
    bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
    · exact hPD) (by have := hP.lt; omega)

end

/-- Every region of `rs` is part of one of `mutR`. -/
abbrev InMut (W SP D : BitVec 32) (n : Nat) (rs : List Region) : Prop :=
  ∀ r ∈ rs, ∃ r' ∈ VG.Proof.AesCcm.X86.mutR W SP D n, Region.Sub r r'

theorem inMut_macR (W SP D : BitVec 32) (n : Nat) {y : Nat} (hy : y = 0 ∨ y = 96) : VG.Proof.AesCcm.X86.InMut W SP D n (VG.Proof.AesCcm.X86.macR W SP y) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨VG.Proof.AesCcm.X86.wA W, by simp, by rcases hy with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩
  · exact ⟨VG.Proof.AesCcm.X86.wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 56, by simp, fun _ h => h⟩

theorem inMut_ctrR (W SP D : BitVec 32) (n : Nat) : VG.Proof.AesCcm.X86.InMut W SP D n (VG.Proof.AesCcm.X86.ctrR W SP D n) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨VG.Proof.AesCcm.X86.wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 56, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem frame_toMut {W SP D : BitVec 32} {n : Nat} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (h : VG.Proof.AesCcm.X86.InMut W SP D n rs) : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) m m' := hf.sub h

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.CryptCT`. -/
section

/-!
# AES-CCM on x86: counter mode in constant time

Untrusted: everything here is checked by Lean. `ctr` branches on the length
of the data and addresses memory by `W` and the data's address, all public
(`ctr_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop splitWhole dO nO)
open VG.Proof.AesGcm.X86 (CT w64 slotv)

/-- What `ctr` starts from. -/
structure CtrPre (K W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : VG.Proof.AesCcm.X86.Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  data : slotv s.mem W dataO = D
  len : slotv s.mem W lenO = BitVec.ofNat 32 n
  c : ∃ nonce, VG.Proof.AesCcm.X86.CtrCtx K W SP s R nonce D n

theorem ctrWhole_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32) :
    CT (VG.Proof.AesCcm.X86.CtrPre K W SP R D n) (.seq (.block (([.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp nO) .eax] : List Instr) ++ splitWhole))
      (.ite .e (.block []) (.seq (.block (([.mov .eax (imm 1)] : List Instr) ++ ctrAt ++ keyArgs c1O)) (ctrCall v.callee)))) := by
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ h => h.env.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesCcm.X86.ctrSplit_ok L hs.env hs.data hs.len hn32) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => VG.Proof.AesCcm.X86.eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : n / 16 ≠ 0 := of_decide_eq_false hf
  have blk : ∀ s₁ : State, (∃ s, VG.Proof.AesCcm.X86.CtrPre K W SP R D n s ∧ s₁.gpr .ebx = D ∧ s₁.gpr .edi = BitVec.ofNat 32 (n / 16) ∧
      s₁.zf = some (decide (n / 16 = 0)) ∧ VG.Proof.AesCcm.X86.Env K W SP s₁ ∧ Frame [VG.Proof.AesCcm.X86.wC W] s.mem s₁.mem ∧
      slotv s₁.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16)) ∧ slotv s₁.mem W nO = BitVec.ofNat 32 (n % 16) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr) →
      ∃ sc, runBlock isa (([.mov .eax (imm 1)] : List Instr) ++ ctrAt ++ keyArgs c1O) s₁ = some sc ∧
        sc.gpr .eax = K ∧ sc.gpr .ecx = BitVec.ofNat 32 R ∧ sc.gpr .edx = W + BitVec.ofNat 32 64 ∧ sc.gpr .ebx = D ∧
        sc.gpr .edi = BitVec.ofNat 32 (n / 16) ∧ sc.gpr .ebp = W ∧ sc.gpr .esp = SP ∧ sc.rd = s₁.rd ∧
        sc.wr = s₁.wr := fun s₁ ⟨s, hs, hbx, hdi, _, E₁, f₁, _, _, rd, wr⟩ => by
    obtain ⟨nonce, C⟩ := hs.c
    have fr₁ : Frame (VG.Proof.AesCcm.X86.ctrR W SP D n) s.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, fun _ h => h⟩
    obtain ⟨sc, run, -, -, rest⟩ := VG.Proof.AesCcm.X86.ctrArgs_ok L E₁
      (by rw [C.slot_kept fr₁ (by decide) (by decide)]; exact hs.ctx)
      (by rw [C.slot_kept fr₁ (by decide) (by decide)]; exact hs.rounds) C.h7 C.h13 (C.c0_kept fr₁) (i := 1)
      (by
        have : 1 ≤ 256 ^ (15 - nonce.length) := Nat.pow_pos (by decide)
        have := C.hn
        omega) (by decide) hbx hdi
    exact ⟨sc, run, rest⟩
  refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ ⟨_, _, _, _, _, E₁, _⟩ => E₁.ebp) (by taint_decide) blk ?_
  refine VG.Proof.AesCcm.X86.ctrCall_ct v L hR (c := 64) (Q := D) (n := n / 16) (by decide)
    fun sc ⟨s₁, ⟨s, hs, _, _, _, E₁, _, _, _, rd₁, wr₁⟩, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ => ?_
  obtain ⟨nonce, C⟩ := hs.c
  have rdc : sc.rd = s.rd := by rw [rd, rd₁]
  have wrc : sc.wr = s.wr := by rw [wr, wr₁]
  refine ⟨⟨bp, sp, hs.env.perm.of_eq rdc wrc⟩, VG.Proof.AesCcm.X86.srcBuf ((C.buf.take hb).of_eq rdc wrc), ?_,
    (C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide)), C.dk.sub_right (Region.sub_prefix hb),
    ax, cx, dx, bx, di⟩
  rw [wrc]
  intro a k ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact C.dw a k ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

/-- What `ctr`'s last bytes start from. -/
abbrev CtrTailPre (K W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (t : State) : Prop :=
  ∃ s, VG.Proof.AesCcm.X86.CtrPre K W SP R D n s ∧ ∃ nonce, VG.Proof.AesCcm.X86.CtrCtx K W SP s R nonce D n ∧ VG.Proof.AesCcm.X86.CtrMid K W SP s R nonce D n t

theorem ctrTail_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32) :
    CT (VG.Proof.AesCcm.X86.CtrTailPre K W SP R D n) (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
      (.ite .e (.block [])
        (.seq (.block (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++ zero4 ksO ++
            keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)))
        (.seq (ctrCall v.callee)
          (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksO), .mov .ecx (slot nO)])
            xorLoop))))) := by
  refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ ⟨_, _, _, _, I⟩ => I.env.ebp) (by taint_decide)
    (fun t ⟨_, _, _, _, I⟩ => VG.Proof.AesCcm.X86.testN_ok L I.env (r := n % 16) (by omega) I.nO) ?_
  refine CT.ite (decide (n % 16 = 0)) (fun _ ⟨_, _, _, hzf, _⟩ => VG.Proof.AesCcm.X86.eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : n % 16 ≠ 0 := of_decide_eq_false hf
  -- The arguments of the call making the keystream block.
  have blk : ∀ t₀ : State, (∃ t, VG.Proof.AesCcm.X86.CtrTailPre K W SP R D n t ∧ t₀.mem = t.mem ∧ t₀.zf = some (decide (n % 16 = 0)) ∧
      t₀.gpr .ebp = W ∧ t₀.gpr .esp = SP ∧ t₀.rd = t.rd ∧ t₀.wr = t.wr) →
      ∃ tc, runBlock isa (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++
          zero4 ksO ++ keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)) t₀ =
          some tc ∧
        Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩] t₀.mem tc.mem ∧
        tc.gpr .eax = K ∧ tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
        tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
        tc.gpr .esp = SP ∧ tc.rd = t₀.rd ∧ tc.wr = t₀.wr :=
    fun t₀ ⟨t, ⟨s, hs, nonce, C, I⟩, hm₀, _, hbp₀, hsp₀, hrd₀, hwr₀⟩ => by
      have E₀ : VG.Proof.AesCcm.X86.Env K W SP t₀ := I.env.keep (by rw [hbp₀, I.env.ebp]) (by rw [hsp₀, I.env.esp]) hrd₀ hwr₀
      have k₀ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv t₀.mem W o = slotv s.mem W o := fun o h₁ h₂ => by
        rw [hm₀]; exact C.slot_kept I.frame h₁ h₂
      obtain ⟨tc, run, ft, -, -, rest⟩ := VG.Proof.AesCcm.X86.ctrTailArgs_ok L E₀ (by rw [k₀ _ (by decide) (by decide)]; exact hs.ctx)
        (by rw [k₀ _ (by decide) (by decide)]; exact hs.rounds) (by rw [k₀ _ (by decide) (by decide)]; exact hs.len)
        hn32 C.h7 C.h13 (by rw [hm₀]; exact C.c0_kept I.frame) (by have := C.hn; omega)
      exact ⟨tc, run, ft, rest⟩
  refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ ⟨_, _, _, _, hbp, _⟩ => hbp) (by taint_decide) blk ?_
  -- The call.
  have a80 : w64 (W + BitVec.ofNat 32 80) = w64 W + BitVec.ofNat 64 80 := L.aW (by decide)
  have pre : ∀ tc : State, (∃ t₀ : State, (∃ t, VG.Proof.AesCcm.X86.CtrTailPre K W SP R D n t ∧ t₀.mem = t.mem ∧
      t₀.zf = some (decide (n % 16 = 0)) ∧ t₀.gpr .ebp = W ∧ t₀.gpr .esp = SP ∧ t₀.rd = t.rd ∧ t₀.wr = t.wr) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩] t₀.mem tc.mem ∧
      tc.gpr .eax = K ∧ tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
      tc.gpr .esp = SP ∧ tc.rd = t₀.rd ∧ tc.wr = t₀.wr) →
      VG.Proof.AesCcm.X86.Env K W SP tc ∧ VG.Proof.AesCcm.X86.Src W SP tc (W + BitVec.ofNat 32 80) (16 * 1) ∧
      Covers [⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩] tc.wr ∧
      (⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ ∧
      (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ ∧ tc.gpr .eax = K ∧
      tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 :=
    fun tc ⟨t₀, ⟨t, ⟨_, _, _, _, I⟩, _, _, _, _, hrd₀, hwr₀⟩, _, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ => by
      have Ec : VG.Proof.AesCcm.X86.Env K W SP tc := ⟨bp, sp, I.env.perm.of_eq (by rw [rd, hrd₀]) (by rw [wr, hwr₀])⟩
      exact ⟨Ec, VG.Proof.AesCcm.X86.srcW L Ec.perm (by decide), by rw [a80]; exact Ec.perm.wC (by decide),
        by rw [a80]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide),
        by rw [a80]; exact L.k_w.sub_right (Lay.wSub (by decide)), ax, cx, dx, bx, di⟩
  refine CT.seq (J := fun td => VG.Proof.AesCcm.X86.Env K W SP td ∧ slotv td.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
      slotv td.mem W nO = BitVec.ofNat 32 (n % 16))
    (VG.Proof.AesCcm.X86.ctrCall_ct v L hR (c := 64) (by decide) pre) (fun tc h => ?_) ?_
  · obtain ⟨Ec, hq, hqw, hqc, hqk, ax, cx, dx, bx, di⟩ := pre tc h
    obtain ⟨t₀, ⟨t, ⟨_, _, _, _, I⟩, hm₀, _⟩, ft, _⟩ := h
    refine WP.mono (VG.Proof.AesCcm.X86.ctrCall_ok v L Ec hR (c := 64) (by decide) hq hqc hqk hqw ax cx dx bx di)
      fun td ⟨Ed, _, _, _, fd, _⟩ => ?_
    have fd' := fd
    rw [a80] at fd'
    have kd : ∀ o, 96 ≤ o → o + 4 ≤ 384 → slotv td.mem W o = slotv t.mem W o := fun o h₁ h₂ => by
      rw [← hm₀]
      exact ((ft.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans
        (fd'.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
          · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
          · exact ⟨⟨w64 W + BitVec.ofNat 64 384, 2048⟩, by simp, fun _ h => h⟩
          · exact ⟨below SP 56, by simp, fun _ h => h⟩) :
          Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 56]
            t₀.mem td.mem).readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
          · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
          · exact (L.stk_w' (by omega)).symm) (by decide)
    exact ⟨Ed, by rw [kd _ (by decide) (by decide)]; exact I.dO, by rw [kd _ (by decide) (by decide)]; exact I.nO⟩
  -- The XOR.
  refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ h => h.1.ebp) (by taint_decide)
    (fun td hd => VG.Proof.AesCcm.X86.xorArgs_ok L hd.1 hd.2.1 hd.2.2) ?_
  exact Proof.AesGcm.X86.xorLoop_ct (VG.Proof.AesCcm.X86.pin3 fun _ ⟨_, _, _, hdi, hdx, hcx, _⟩ => ⟨hdi, hdx, hcx⟩)

theorem ctr_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32) : CT (VG.Proof.AesCcm.X86.CtrPre K W SP R D n) (VG.Impl.AesCcm.X86.ctr v.callee) :=
  RelCT.assoc (CT.seq (J := VG.Proof.AesCcm.X86.CtrTailPre K W SP R D n) (VG.Proof.AesCcm.X86.ctrWhole_ct v L hR hn32)
    (fun s hs => by
      obtain ⟨nonce, C⟩ := hs.c
      exact WP.mono (VG.Proof.AesCcm.X86.ctrWhole_ok v C hs.env hs.ctx hs.rounds hs.data hs.len) fun t I => ⟨s, hs, nonce, C, I⟩)
    (VG.Proof.AesCcm.X86.ctrTail_ct v L hR hn32))

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Top`. -/
section

/-!
# AES-CCM on x86: the start of both functions

Untrusted: everything here is checked by Lean. `seal` and `open` both start
with the entry and `Ctr₀` (`start_ok`); after them, the slots hold the
arguments and `W + 48` holds `Ctr₀`, and the key schedule, the nonce, the
associated data, the data, the received tag and the return address are as
they were (`Started`). The pieces after them write only `mutR`, which keeps
all of that but the data (`Started.mut`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 slotv SavedAt ret_below ofNat_toNat32)

/-- After the entry and `Ctr₀`. -/
structure Started (s : State) (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s' : State) : Prop where
  env : VG.Proof.AesCcm.X86.Env K W SP s'
  slots : VG.Proof.AesCcm.X86.Slots W K R N A D T nl al n tl s'.mem
  saved : SavedAt s'.mem W s
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  c0 : bytesAt s'.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0
  ciph : Spec.Ccm.ctxCiph s'.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R
  aadB : bytesAt s'.mem (w64 A) al = bytesAt s.mem (w64 A) al
  dataB : bytesAt s'.mem (w64 D) n = bytesAt s.mem (w64 D) n
  tagB : bytesAt s'.mem (w64 T) tl = bytesAt s.mem (w64 T) tl
  ret : s'.mem.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32

/-- The entry and `Ctr₀`. -/
theorem start_ok {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : VG.Proof.AesCcm.X86.Args s K W SP N A D T R nl al n tl) (hsp : s.gpr .esp = SP) (a0 : VG.X86.arg s 0 = K)
    (a1 : VG.X86.arg s 1 = BitVec.ofNat 32 R) (a2 : VG.X86.arg s 2 = N) (a3 : VG.X86.arg s 3 = BitVec.ofNat 32 nl) (a4 : VG.X86.arg s 4 = A)
    (a5 : VG.X86.arg s 5 = BitVec.ofNat 32 al) (a6 : VG.X86.arg s 6 = D) (a7 : VG.X86.arg s 7 = BitVec.ofNat 32 n) (a8 : VG.X86.arg s 8 = T)
    (a9 : VG.X86.arg s 9 = BitVec.ofNat 32 tl) (a10 : VG.X86.arg s 10 = W) :
    WP isa (.seq ccmEntry ctrs) s (VG.Proof.AesCcm.X86.Started s K W SP N A D T R nl al n tl) := by
  have L := Ar.lay
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.entry_ok a10 Ar.perm.w (by rw [hsp]; exact Ar.args) (by rw [hsp]; exact Ar.argsW)
    (by rw [hsp]; exact Ar.fa) L.fw) fun s₁ E₀ => ?_)
  have E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁ := ⟨E₀.ebp, by rw [E₀.esp, hsp], Ar.perm.of_eq E₀.rd E₀.wr⟩
  have sl : ∀ p ∈ VG.Proof.AesCcm.X86.entryPs, slotv s₁.mem W p.2 = VG.X86.arg s p.1 := E₀.slots
  have S₁ : VG.Proof.AesCcm.X86.Slots W K R N A D T nl al n tl s₁.mem :=
    ⟨by rw [sl (0, ctxO) (by simp), a0], by rw [sl (1, roundsO) (by simp), a1],
      by rw [sl (2, nonceO) (by simp), a2], by rw [sl (3, nlenO) (by simp), a3],
      by rw [sl (4, aadO) (by simp), a4], by rw [sl (5, alenO) (by simp), a5],
      by rw [sl (6, dataO) (by simp), a6], by rw [sl (7, lenO) (by simp), a7],
      by rw [sl (9, Impl.AesGcm.X86.tglO) (by simp), a9], by rw [sl (8, Impl.AesGcm.X86.tpO) (by simp), a8]⟩
  have fE := E₀.frame
  have bE : ∀ {P : BitVec 32} {len : Nat}, VG.Proof.AesCcm.X86.Buf W SP s P len → bytesAt s₁.mem (w64 P) len = bytesAt s.mem (w64 P) len :=
    fun hP => Proof.AesGcm.X86.bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  have cE : Spec.Ccm.ctxCiph s₁.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    VG.Proof.AesCcm.X86.ctxCiph_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  refine WP.mono (VG.Proof.AesCcm.X86.ctrs_ok L E₁ S₁.nonce S₁.nlen (Ar.nonce.of_eq E₀.rd E₀.wr) Ar.h7 Ar.h13)
    fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_
  have f₂' : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86.wA W, by simp, Offset.sub_base _ (by decide)⟩
  have b₂ : ∀ {P : BitVec 32} {len : Nat}, VG.Proof.AesCcm.X86.Buf W SP s P len → bytesAt s₂.mem (w64 P) len = bytesAt s₁.mem (w64 P) len :=
    fun hP => Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  refine ⟨E₂, VG.Proof.AesCcm.X86.slots_mut L Ar.data.w f₂' S₁, VG.Proof.AesCcm.X86.saved_mut L Ar.data.w f₂' E₀.saved, by rw [rd₂, E₀.rd],
    by rw [wr₂, E₀.wr], by rw [c₂, bE Ar.nonce], ?_, by rw [b₂ Ar.aad, bE Ar.aad], by rw [b₂ Ar.data, bE Ar.data],
    ?_, ?_⟩
  · rw [VG.Proof.AesCcm.X86.ctxCiph_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb, cE]
  · rw [b₂ Ar.tag, bE Ar.tag]
  · rw [Proof.AesGcm.X86.ret_kept f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.retW.sub_right (Lay.wSub (by decide))),
      Proof.AesGcm.X86.ret_kept fE (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.retW.sub_right (Lay.wSub (by decide)))]

/-- What the pieces after the start keep. -/
theorem Started.mut {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : VG.Proof.AesCcm.X86.Args s K W SP N A D T R nl al n tl) {s₁ : State} (St : VG.Proof.AesCcm.X86.Started s K W SP N A D T R nl al n tl s₁) {m : Mem}
    (hf : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) s₁.mem m) :
    VG.Proof.AesCcm.X86.Slots W K R N A D T nl al n tl m ∧ SavedAt m W s ∧
      Spec.Ccm.ctxCiph m (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R ∧
      bytesAt m (w64 A) al = bytesAt s.mem (w64 A) al ∧ m.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32 := by
  have L := Ar.lay
  refine ⟨VG.Proof.AesCcm.X86.slots_mut L Ar.data.w hf St.slots, VG.Proof.AesCcm.X86.saved_mut L Ar.data.w hf St.saved,
    by rw [VG.Proof.AesCcm.X86.ciph_mut L Ar.dk Ar.rounds hf, St.ciph], by rw [VG.Proof.AesCcm.X86.buf_mut Ar.aad Ar.ad hf, St.aadB], ?_⟩
  rw [Proof.AesGcm.X86.ret_kept hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Ar.retW.sub_right (Region.sub_prefix (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact VG.Proof.AesGcm.X86.ret_below L.sp
    · exact Ar.retD), St.ret]

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Mask`. -/
section

/-!
# AES-CCM on x86: masking the data, and the tag copied out

Untrusted: everything here is checked by Lean. `mask` ANDs every byte of the
data with `0 − ok`: the data if `ok = 1`, zeros if `ok = 0` (`mask_ok`).
`tagOut` copies the first `tag_len` bytes of the tag at `W` to `tag`
(`tagOut_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop tglO tpO rO)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv in_of_covers covers_left succ_ofNat32 add_zero32 pred_count pred_beq bytesAt_succ
  length_bytesAt and_self_beq32 WEnv padLoop_ok zero4_fold toNat_ofNat32 LoopPre CopyPost copyLoop_ok CT)

/-! ## `mask` -/

theorem mask_byte32 (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.movzx8 .edx (at_ .edi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .edi 0) .dl, .alu .add .edi (imm 1),
    .alu .sub .ecx (imm 1)]

theorem maskStep_ok (s : State) {P : BitVec 32} {i n : Nat} {c : Bool} (hs : s.gpr .edi = P + BitVec.ofNat 32 i)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i)) (hb : s.gpr .ebx = 0 - (if c then 1 else 0))
    (eP : w64 (P + BitVec.ofNat 32 i) = w64 P + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 P + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa VG.Proof.AesCcm.X86.maskBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 P + BitVec.ofNat 64 i) ((if c then s.mem (w64 P + BitVec.ofNat 64 i) else 0 : Byte)) ∧
      s'.gpr .edi = P + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [VG.Proof.AesCcm.X86.maskBody, add_zero32, hs, eP, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hb, VG.Proof.AesCcm.X86.mask_byte32]
  · cregs [hs, succ_ofNat32]
  · cregs [hc]
  · cmems [hc]
  · intro r h₁ h₂ h₃; cregs [h₁, h₂, h₃]
  all_goals cmems []

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`, for `ok` (at `W + okO`) 1 or 0. -/
theorem mask_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {D : BitVec 32} {n : Nat}
    (hDp : slotv s.mem W dataO = D) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32)
    (hD : VG.Proof.AesCcm.X86.Buf W SP s D n) (hDw : Covers [⟨w64 D, n⟩] s.wr) {c : Bool}
    (hok : slotv s.mem W okO = if c then 1 else 0) :
    WP isa mask s fun s' => VG.Proof.AesCcm.X86.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) n else zeros n) := by
  obtain ⟨s₁, run₁, m₁, cx₁, zf₁, bp₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n ∧ s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hlen]
    · cmems [hlen]; rw [and_self_beq32 hn32]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  have E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁ := E.keep (by rw [bp₁, E.ebp]) (by rw [sp₁, E.esp]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (VG.Proof.AesCcm.X86.eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨E₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [Spec.Aes.bytesAt, zeros, VG.WriteBytes.writeBytes_nil]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  obtain ⟨s₂, run₂, m₂, bx₂, di₂, cx₂, bp₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧ s₂.mem = s.mem ∧
      s₂.gpr .ebx = 0 - (if c then 1 else 0) ∧ s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n ∧
      s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    have hok₁ : slotv s₁.mem W okO = if c then 1 else 0 := by rw [m₁]; exact hok
    have hd₁ : slotv s₁.mem W dataO = D := by rw [m₁]; exact hDp
    refine ⟨_, by crun [bp₁, L.aW, E₁.perm.wR, hok₁, hd₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [m₁]
    · cregs [hok₁]; rfl
    · cregs [hd₁]
    · cregs [cx₁]
    · cregs [bp₁]
    · cregs [sp₁]
    · cmems [rd₁]
    · cmems [wr₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hfD := hD.wrap
  refine WP.loop (M := isa) (body := .block VG.Proof.AesCcm.X86.maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .edi = D + BitVec.ofNat 32 j ∧
      t.gpr .ecx = BitVec.ofNat 32 (n - j) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) j else zeros j) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t.gpr r = s₂.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn0, by rw [di₂, add_zero32], by rw [cx₂, Nat.sub_zero], by
      rw [m₂]; cases c <;> simp [Spec.Aes.bytesAt, zeros, VG.WriteBytes.writeBytes_nil], fun r _ _ _ => rfl, rd₂, wr₂⟩
  rintro k t ⟨j, rfl, hj, di, cx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', di', cx', zf', g', rd', wr'⟩ := VG.Proof.AesCcm.X86.maskStep_ok t (P := D) (i := j) (n := n) (c := c) di cx
    (by rw [g _ (by decide) (by decide) (by decide), bx₂]) (w64_add (by omega))
    (by rw [rd, wr]; exact in_of_covers hD.rd hj (by omega))
    (by rw [wr]; exact in_of_covers hDw hj (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨w64 D, j⟩] s.mem t.mem := by
    rw [mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.AesCcm.X86.length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (w64 D + BitVec.ofNat 64 j) = s.mem (w64 D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 D) (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = VG.WriteBytes.writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) (j + 1) else zeros (j + 1)) := by
    rw [mem', hq, mem, VG.Proof.AesCcm.X86.mask_succ, VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [VG.Proof.AesCcm.X86.length_mask]; omega), VG.Proof.AesCcm.X86.length_mask]
  have hz : t'.zf = some (decide (j + 1 = n)) := by rw [zf', pred_beq hj hn32]
  have gg : ∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t'.gpr r = s₂.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  have E' : VG.Proof.AesCcm.X86.Env K W SP t' := ⟨by rw [gg _ (by decide) (by decide) (by decide), bp₂],
    by rw [gg _ (by decide) (by decide) (by decide), sp₂], E.perm.of_eq (by rw [rd', rd]) (by rw [wr', wr])⟩
  by_cases he : j + 1 = n
  · left
    exact ⟨by simp [eval, hz, he], E', by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (j + 1), by omega, j + 1, rfl, by omega, di',
      by rw [cx', pred_count hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The tag copied out -/

/-- `tagOut`: the first `t` bytes at `W` written to `tag` (kept at `W + tpO`). -/
theorem tagOut_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {T : BitVec 32} {t : Nat}
    (hv : slotv s.mem W tglO = BitVec.ofNat 32 t) (hT : slotv s.mem W tpO = T) (ht1 : 1 ≤ t) (ht : t ≤ 16)
    (Tb : VG.Proof.AesCcm.X86.Buf W SP s T t) (tw : Covers [⟨w64 T, t⟩] s.wr) :
    WP isa tagOut s fun s' => s'.mem = VG.WriteBytes.writeBytes s.mem (w64 T) (bytesAt s.mem (w64 W) t) ∧ VG.Proof.AesCcm.X86.Env K W SP s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, hm₁, hdi, hdx, hcx, hbp, hsp, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .edi (.reg .ebp), .mov .edx (slot tpO), .mov .ecx (slot tglO)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .edi = W ∧ s₁.gpr .edx = T ∧ s₁.gpr .ecx = BitVec.ofNat 32 t ∧ s₁.gpr .ebp = W ∧
      s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hv, hT], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems []
    · cregs [E.ebp]
    · cregs [hT]
    · cregs [hv]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have lp : LoopPre s₁ W T t := ⟨hdi, hdx, hcx, ht1, by omega, by have := L.fw; omega, Tb.wrap,
    by rw [hrd₁, hwr₁]; simpa using covers_left (E.perm.wC (d := 0) (n := t) (by omega)),
    by rw [hwr₁]; exact tw, (Tb.w.sub_right (Region.sub_prefix (by omega))).symm⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s' P => ⟨by rw [P.mem, hm₁], ⟨?_, ?_, E.perm.of_eq ?_ ?_⟩, ?_, ?_⟩
  · rw [P.other _ (by decide) (by decide) (by decide) (by decide), hbp]
  · rw [P.other _ (by decide) (by decide) (by decide) (by decide), hsp]
  all_goals first | rw [P.rd, hrd₁] | rw [P.wr, hwr₁]

theorem tagOut_ct {K W SP T : BitVec 32} {t : Nat} {I : State → Prop} (L : VG.Proof.AesCcm.X86.Lay K W SP)
    (h : ∀ s, I s → VG.Proof.AesCcm.X86.Env K W SP s ∧ slotv s.mem W tglO = BitVec.ofNat 32 t ∧ slotv s.mem W tpO = T) :
    CT I tagOut := by
  refine CT.seq (J := fun s => s.gpr .edi = W ∧ s.gpr .edx = T ∧ s.gpr .ecx = BitVec.ofNat 32 t)
    (CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h _ h₁).1.ebp, (h _ h₂).1.ebp]) (by taint_decide))
    (fun s hs => ?_) (Proof.AesGcm.X86.copyLoop_ct fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2])
  obtain ⟨E, hv, hT⟩ := h s hs
  exact WP.of_runBlock ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hv, hT], by cregs [E.ebp], by cregs [hT], by cregs [hv]⟩

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Seal`. -/
section

/-!
# AES-CCM on x86: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `seal` is the start (the
entry and `Ctr₀`, `start_ok`), the MAC of the payload at `W` (`mac_ok`),
encrypted (`tag_ok`), counter mode over the data (`ctr_ok`), the tag copied
to `tag` (`tagOut_ok`) and the exit (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Proof.AesGcm.X86 (w64 slotv SavedAt exit_ok ofNat_toNat32 length_bytesAt covers_left writeBytes_frame'
  bytesAt_writeBytes_self)

/-- What `tag y` writes, in `mutR`. -/
theorem inMut_tag (W SP D : BitVec 32) (n : Nat) {y : Nat} (hy : y = 0 ∨ y = 96) :
    VG.Proof.AesCcm.X86.InMut W SP D n [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, VG.Proof.AesCcm.X86.wC W, below SP 56] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨VG.Proof.AesCcm.X86.wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨VG.Proof.AesCcm.X86.wA W, by simp, by rcases hy with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩
  · exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 56, by simp, fun _ h => h⟩

/-- A buffer apart from `W` and the stack keeps its bytes across a frame of
parts of `W` and the stack. -/
theorem buf_kept' {W SP : BitVec 32} {s : State} {P : BitVec 32} {len : Nat} (hP : VG.Proof.AesCcm.X86.Buf W SP s P len)
    {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨w64 W, 2560⟩ ∨ r = below SP 56) {m m' : Mem}
    (hf : Frame rs m m') : bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    rcases hrs r hr with h | rfl
    · exact hP.w.sub_right h
    · exact hP.stk.symm) (by have := hP.lt; omega)

/-- `Ctr₀` is kept by a frame of parts of `W` apart from it. -/
theorem c0_kept {W : BitVec 32} {rs : List Region}
    (hrs : ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r) {m m' : Mem} (hf : Frame rs m m') :
    bytesAt m' (w64 W + BitVec.ofNat 64 48) 16 = bytesAt m (w64 W + BitVec.ofNat 64 48) 16 :=
  Proof.AesGcm.X86.bytesAt_frame hf hrs (by decide)

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' (v : Ctr32Impl) {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : VG.Proof.AesCcm.X86.Args s K W SP N A D T R nl al n tl) (hsp : s.gpr .esp = SP) (a0 : VG.X86.arg s 0 = K)
    (a1 : VG.X86.arg s 1 = BitVec.ofNat 32 R) (a2 : VG.X86.arg s 2 = N) (a3 : VG.X86.arg s 3 = BitVec.ofNat 32 nl) (a4 : VG.X86.arg s 4 = A)
    (a5 : VG.X86.arg s 5 = BitVec.ofNat 32 al) (a6 : VG.X86.arg s 6 = D) (a7 : VG.X86.arg s 7 = BitVec.ofNat 32 n) (a8 : VG.X86.arg s 8 = T)
    (a9 : VG.X86.arg s 9 = BitVec.ofNat 32 tl) (a10 : VG.X86.arg s 10 = W) (tw : Covers [⟨w64 T, tl⟩] s.wr) :
    WP isa («seal» v.callee v.suffix) s fun s' => abiPreserved s s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n)
        (bytesAt s.mem (w64 A) al) = (bytesAt s'.mem (w64 D) n, bytesAt s'.mem (w64 T) tl) := by
  have L := Ar.lay
  have hnl := length_bytesAt s.mem (w64 N) nl
  have h7' : 7 ≤ (bytesAt s.mem (w64 N) nl).length := by rw [hnl]; exact Ar.h7
  have h13' : (bytesAt s.mem (w64 N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  refine VG.Proof.AesCcm.X86.seq_assoc (WP.seq (WP.mono (VG.Proof.AesCcm.X86.start_ok Ar hsp a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) fun s₂ St => ?_))
  -- The MAC.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.mac_ok v L St.env Ar.rounds St.slots hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn
    Ar.n32 St.c0 (y := 0) (.inl rfl) (Ar.aad.of_eq St.rd St.wr) (Ar.data.of_eq St.rd St.wr)) fun s₃ A₃ => ?_)
  have f₃ : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) s₂.mem s₃.mem := VG.Proof.AesCcm.X86.frame_toMut A₃.frame (VG.Proof.AesCcm.X86.inMut_macR W SP D n (.inl rfl))
  obtain ⟨S₃, -, -, -, -⟩ := St.mut Ar f₃
  have hc₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 := by
    rw [VG.Proof.AesCcm.X86.c0_kept (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) A₃.frame, St.c0]
  -- The tag.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.tag_ok v L A₃.env Ar.rounds S₃.ctx S₃.rounds h7' h13' hc₃ (y := 0) (.inl rfl))
    fun s₄ ⟨E₄, rd₄, wr₄, f₄, h₄⟩ => ?_)
  have f₂₄ : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) s₂.mem s₄.mem := f₃.trans (VG.Proof.AesCcm.X86.frame_toMut f₄ (VG.Proof.AesCcm.X86.inMut_tag W SP D n (.inl rfl)))
  obtain ⟨S₄, -, -, -, -⟩ := St.mut Ar f₂₄
  have hc₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 := by
    rw [VG.Proof.AesCcm.X86.c0_kept (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) f₄, hc₃]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, A₃.rd, St.rd]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, A₃.wr, St.wr]
  have hD₄ : bytesAt s₄.mem (w64 D) n = bytesAt s.mem (w64 D) n := by
    rw [VG.Proof.AesCcm.X86.buf_kept' Ar.data (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inr rfl) f₄,
      VG.Proof.AesCcm.X86.buf_kept Ar.data (y := 0) (by decide) A₃.frame, St.dataB]
  -- Counter mode.
  have C₄ : VG.Proof.AesCcm.X86.CtrCtx K W SP s₄ R (bytesAt s.mem (w64 N) nl) D n :=
    ⟨L, Ar.rounds, h7', h13', by rw [hnl]; exact Ar.hn, Ar.n32, hc₄, Ar.data.of_eq rd₄' wr₄',
      by rw [wr₄']; exact Ar.dw, Ar.dk⟩
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.ctr_ok v C₄ E₄ S₄.ctx S₄.rounds S₄.data S₄.len) fun s₅ ⟨E₅, rd₅, wr₅, f₅, h₅⟩ => ?_)
  have f₂₅ : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) s₂.mem s₅.mem := f₂₄.trans (VG.Proof.AesCcm.X86.frame_toMut f₅ (VG.Proof.AesCcm.X86.inMut_ctrR W SP D n))
  obtain ⟨S₅, sv₅, ci₅, -, rt₅⟩ := St.mut Ar f₂₅
  have rd₅' : s₅.rd = s.rd := by rw [rd₅, rd₄']
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, wr₄']
  -- The tag copied out.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.tagOut_ok L E₅ S₅.tl S₅.tp (by have := Ar.t4; omega) Ar.t16
    (Ar.tag.of_eq rd₅' wr₅') (by rw [wr₅']; exact tw)) fun s₆ ⟨m₆', E₆, rd₆, wr₆⟩ => ?_)
  have hTl : tl < 2 ^ 64 := by have := Ar.t16; omega
  have fT : Frame [⟨w64 T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆']; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have tW : ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨w64 T, tl⟩ : Region)],
      (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (Ar.tag.w.sub_right (Lay.wSub hk)).symm
  have sv₆ : SavedAt s₆.mem W s := sv₅.frame fT (tW (by decide))
  have rt₆ : s₆.mem.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32 := by
    rw [Proof.AesGcm.X86.ret_kept fT (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.retT), rt₅]
  -- The exit.
  refine WP.mono (exit_ok (W := W) (s₀ := s) E₆.ebp (by rw [E₆.esp, hsp])
    (by rw [rd₆, wr₆, rd₅', wr₅']; exact covers_left Ar.perm.w) L.fw sv₆ (by rw [hsp]; exact rt₆))
    fun s₇ ⟨abi, m₇, _, _, _⟩ => ⟨abi, ?_⟩
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (w64 K) R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  have ci₄ : Spec.Ccm.ctxCiph s₄.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    (St.mut Ar f₂₄).2.2.1
  have ci₃ : Spec.Ccm.ctxCiph s₃.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    (St.mut Ar f₃).2.2.1
  have hW₅ : bytesAt s₅.mem (w64 W) tl = bytesAt s₄.mem (w64 W) tl := by
    have ht := Ar.t16
    exact Proof.AesGcm.X86.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simpa using Lay.w_w (W := W) (a := 0) (n := tl) (d := 64) (k := 32) (.inl (by omega)) (by omega) (by decide)
      · simpa using Lay.w_w (W := W) (a := 0) (n := tl) (d := 240) (k := 2320) (.inl (by omega)) (by omega)
          (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by omega))).symm
      · exact (Ar.data.w.sub_right (Region.sub_prefix (by omega))).symm) (by omega)
  have e0 : w64 W + BitVec.ofNat 64 0 = w64 W := BitVec.add_zero _
  have o₃ := A₃.out
  rw [e0] at h₄ o₃
  have hY := congrArg List.length o₃
  rw [length_bytesAt] at hY
  simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [m₇, Proof.AesGcm.X86.bytesAt_frame fT (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by have := Ar.data.lt; omega), h₅, ci₄, hD₄, crypt_eq (hBC _)]
  · have hT₇ : bytesAt s₇.mem (w64 T) tl = bytesAt s₅.mem (w64 W) tl := by
      have := VG.Proof.AesGcm.X86.bytesAt_writeBytes_self s₅.mem (w64 T) (bytesAt s₅.mem (w64 W) tl) (by rw [length_bytesAt]; omega)
      rw [length_bytesAt] at this
      rw [m₇, m₆', this]
    rw [hT₇, hW₅, Proof.AesCcm.bytesAt_prefix s₄.mem (w64 W) Ar.t16, h₄,
      take_xorFrom_zero (hBC _) _ (by rw [length_bytesAt]) Ar.t16, o₃, ci₃,
      ← Proof.AesCcm.mac_eq _ _ (by rw [hnl]; have := Ar.h13; omega), St.ciph, St.aadB, St.dataB]

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.MacCT`. -/
section

/-!
# AES-CCM on x86: the CBC-MAC and the tag in constant time

Untrusted: everything here is checked by Lean. `b0`, `mac` and `tag` branch
and address memory only by the slots, the lengths and `W`: all public
(`b0_ct`, `mac_ct`, `tag_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 tglO dO nO)
open VG.Proof.AesGcm.X86 (CT w64 slotv)

/-- What the MAC's pieces keep: the slots, and the associated data and the
data readable. -/
structure MacMid (K W SP : BitVec 32) (R : Nat) (N A D T : BitVec 32) (nl al n tl : Nat) (s : State) : Prop where
  env : VG.Proof.AesCcm.X86.Env K W SP s
  slots : VG.Proof.AesCcm.X86.Slots W K R N A D T nl al n tl s.mem
  aad : VG.Proof.AesCcm.X86.Buf W SP s A al
  data : VG.Proof.AesCcm.X86.Buf W SP s D n

theorem MacMid.next {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} {N A D T : BitVec 32} {nl al n tl : Nat} {s : State}
    (h : VG.Proof.AesCcm.X86.MacMid K W SP R N A D T nl al n tl s) {y : Nat} (hy : y = 0 ∨ y = 96) {s' : State} (E : VG.Proof.AesCcm.X86.Env K W SP s')
    (f : Frame (VG.Proof.AesCcm.X86.macR W SP y) s.mem s'.mem) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) :
    VG.Proof.AesCcm.X86.MacMid K W SP R N A D T nl al n tl s' :=
  ⟨E, h.slots.macR L hy f, h.aad.of_eq rd wr, h.data.of_eq rd wr⟩

/-- What `b0` and `mac` start from: also `Ctr₀` at `W + 48`. -/
structure MacPre (K W SP : BitVec 32) (R : Nat) (N A D T : BitVec 32) (nl al n tl : Nat) (s : State) : Prop
    extends VG.Proof.AesCcm.X86.MacMid K W SP R N A D T nl al n tl s where
  c0 : ∃ nonce : List Byte, nonce.length = nl ∧
    bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

theorem b0Blk_ct {y : Nat} (hy : y = 0 ∨ y = 96) {I : State → Prop}
    (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp], s₁.gpr r = s₂.gpr r) :
    CT I (.block (([.mov .ecx (slot c0O), .store (at_ .ebp blkO) .ecx, .mov .ecx (slot (c0O + 4)),
        .store (at_ .ebp (blkO + 4)) .ecx, .mov .ecx (slot (c0O + 8)), .store (at_ .ebp (blkO + 8)) .ecx,
        .store8 (at_ .ebp blkO) .al, .mov .eax (slot lenO), .bswap .eax, .alu .or .eax (slot (c0O + 12)),
        .store (at_ .ebp (blkO + 12)) .eax] : List Instr) ++ zero4 y)) := by
  rcases hy with rfl | rfl
  · exact CT.taint [.ebp] hr (by taint_decide)
  · exact CT.taint [.ebp] hr (by taint_decide)

theorem b0_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D T : BitVec 32} {nl al n tl : Nat} (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32) {y : Nat}
    (hy : y = 0 ∨ y = 96) :
    CT (VG.Proof.AesCcm.X86.MacPre K W SP R N A D T nl al n tl) (b0 v.callee v.suffix y) := by
  refine CT.assoc3 (CT.seq (J := fun s => VG.Proof.AesCcm.X86.Env K W SP s ∧ slotv s.mem W ctxO = K ∧
      slotv s.mem W roundsO = BitVec.ofNat 32 R) ?_ (fun s hs => ?_) (VG.Proof.AesCcm.X86.updBlock_ct v L hR hy fun _ h => h))
  · refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ h => h.env.ebp) (by taint_decide)
      (fun s hs => VG.Proof.AesCcm.X86.b0Flags_ok L hs.env h13 ht4 hal hs.slots.tl hs.slots.nlen hs.slots.alen) ?_
    refine CT.seq (J := fun s => s.gpr .ebp = W)
      (CT.ite (decide (al = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => VG.Proof.AesCcm.X86.eval_e hzf) (fun _ => CT.nil)
        (fun _ => by exact CT.taint [] (fun _ _ _ _ _ h => by simp at h) (by taint_decide)))
      (fun s₁ ⟨_, _, _, _, hzf, hbp, _⟩ => ?_) (VG.Proof.AesCcm.X86.b0Blk_ct hy (VG.Proof.AesCcm.X86.pin_ebp fun _ h => h))
    refine WP.ite (decide (al = 0)) (VG.Proof.AesCcm.X86.eval_e hzf) (fun _ => WP.of_runBlock ⟨s₁, rfl, hbp⟩) (fun _ => ?_)
    exact WP.of_runBlock ⟨_, by crun [], by cregs [hbp]⟩
  · obtain ⟨nonce, hnl, hc0⟩ := hs.c0
    refine WP.mono (VG.Proof.AesCcm.X86.b0Pre_ok L hs.env hnl h7 h13 ht4 ht16 hte hal hn hn32 hs.slots.tl hs.slots.nlen hs.slots.alen
      hs.slots.len hc0 hy) fun s₃ ⟨E₃, _, _, f₃, _⟩ => ?_
    have k₃ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
      f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
        · rcases hy with rfl | rfl
          · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
          · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)) (by decide)
    exact ⟨E₃, by rw [k₃ _ (by decide) (by decide)]; exact hs.slots.ctx,
      by rw [k₃ _ (by decide) (by decide)]; exact hs.slots.rounds⟩

theorem mac_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D T : BitVec 32} {nl al n tl : Nat} (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32) {y : Nat}
    (hy : y = 0 ∨ y = 96) :
    CT (VG.Proof.AesCcm.X86.MacPre K W SP R N A D T nl al n tl) (VG.Impl.AesCcm.X86.mac v.callee v.suffix y) := by
  refine CT.seq (J := VG.Proof.AesCcm.X86.MacMid K W SP R N A D T nl al n tl) (VG.Proof.AesCcm.X86.b0_ct v L hR h7 h13 ht4 ht16 hte hal hn hn32 hy)
    (fun s hs => ?_) ?_
  · obtain ⟨nonce, hnl, hc0⟩ := hs.c0
    exact WP.mono (VG.Proof.AesCcm.X86.b0_ok v L hs.env hR hs.slots hnl h7 h13 ht4 ht16 hte hal hn hn32 hc0 hy)
      fun s₁ ⟨E₁, f₁, _, rd, wr⟩ => hs.toMacMid.next L hy E₁ f₁ rd wr
  refine CT.seq (J := VG.Proof.AesCcm.X86.MacMid K W SP R N A D T nl al n tl)
    ((VG.Proof.AesCcm.X86.aad_ct v L hR hy hal).mono fun s hs => ⟨hs.env, hs.slots.ctx, hs.slots.rounds, hs.slots.aad, hs.slots.alen,
      hs.aad⟩)
    (fun s hs => WP.mono (VG.Proof.AesCcm.X86.aad_ok v L hs.env hR hs.slots.ctx hs.slots.rounds hy hs.slots.aad hs.slots.alen hs.aad hal)
      fun s₂ M => hs.next L hy M.env M.frame M.rd M.wr) ?_
  refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ h => h.env.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesCcm.X86.dataArgs_ok L hs.env hs.slots.data hs.slots.len) ?_
  exact (VG.Proof.AesCcm.X86.absorbPad_ct v L hR hy hn32).mono fun s₃ ⟨s, hs, hm₃, hbp, hsp, hrd, hwr⟩ =>
    ⟨⟨hbp, hsp, hs.env.perm.of_eq hrd hwr⟩, by rw [VG.Proof.AesCcm.X86.dn_kept hm₃ (by decide) (by decide)]; exact hs.slots.ctx,
      by rw [VG.Proof.AesCcm.X86.dn_kept hm₃ (by decide) (by decide)]; exact hs.slots.rounds, fun _ => hs.data.of_eq hrd hwr,
      (VG.Proof.AesCcm.X86.dn_read hm₃).1, (VG.Proof.AesCcm.X86.dn_read hm₃).2⟩

/-- What `tag` starts from. -/
structure TagPre (K W SP : BitVec 32) (R : Nat) (s : State) : Prop where
  env : VG.Proof.AesCcm.X86.Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  c0 : ∃ nonce : List Byte, 7 ≤ nonce.length ∧ nonce.length ≤ 13 ∧
    bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

theorem tag_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) : CT (VG.Proof.AesCcm.X86.TagPre K W SP R) (VG.Impl.AesCcm.X86.tag v.callee y) := by
  have blk : ∀ s, VG.Proof.AesCcm.X86.TagPre K W SP R s → ∃ s₃, runBlock isa (([.mov .eax (imm 0)] : List Instr) ++ ctrAt ++ keyArgs c1O ++
      ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm y), .mov .edi (imm 1)] : List Instr)) s = some s₃ ∧
      s₃.gpr .eax = K ∧ s₃.gpr .ecx = BitVec.ofNat 32 R ∧ s₃.gpr .edx = W + BitVec.ofNat 32 64 ∧
      s₃.gpr .ebx = W + BitVec.ofNat 32 y ∧ s₃.gpr .edi = BitVec.ofNat 32 1 ∧ s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧
      s₃.rd = s.rd ∧ s₃.wr = s.wr := fun s hs => by
    obtain ⟨nonce, h7, h13, hc0⟩ := hs.c0
    obtain ⟨s₃, run, -, -, rest⟩ := VG.Proof.AesCcm.X86.tagArgs_ok L hs.env hs.ctx hs.rounds h7 h13 hc0 y
    exact ⟨s₃, run, rest⟩
  have h₂ := VG.Proof.AesCcm.X86.ctrCall_ct v L hR (c := 64) (Q := W + BitVec.ofNat 32 y) (n := 1) (by decide)
    (I := fun s' => ∃ s, VG.Proof.AesCcm.X86.TagPre K W SP R s ∧ s'.gpr .eax = K ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧
      s'.gpr .edx = W + BitVec.ofNat 32 64 ∧ s'.gpr .ebx = W + BitVec.ofNat 32 y ∧ s'.gpr .edi = BitVec.ofNat 32 1 ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    fun s₃ ⟨s, hs, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ => by
      have E₃ : VG.Proof.AesCcm.X86.Env K W SP s₃ := ⟨bp, sp, hs.env.perm.of_eq rd wr⟩
      obtain ⟨hq, hqw, hqc, hqk⟩ := VG.Proof.AesCcm.X86.tagCall_pre L E₃ hy
      exact ⟨E₃, hq, hqw, hqc, hqk, ax, cx, dx, bx, di⟩
  rcases hy with rfl | rfl
  · exact CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ h => h.env.ebp) (by taint_decide) blk h₂
  · exact CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ h => h.env.ebp) (by taint_decide) blk h₂

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.TopCT`. -/
section

/-!
# AES-CCM on x86: the start, and what the pieces after it keep, for
constant time

Untrusted: everything here is checked by Lean. The arguments and `esp` are
public (`pubOf`); from them, `seal` and `open` start (`Top`), the entry and
`Ctr₀` are constant time (`start_ct`), and after them each piece keeps `Run`,
from which the next one's precondition follows.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt tglO tpO)
open VG.Proof.AesGcm.X86 (CT w64 slotv argA argsR argA_contains ofNat_toNat32 length_bytesAt)

/-- What is public: `esp` and the arguments. -/
def pubOf (s : State) : BitVec 32 × (Nat → BitVec 32) := (s.gpr .esp, fun i => if i < 11 then VG.X86.arg s i else 0)

theorem pubOf_eq {s₁ s₂ : State} (h : VG.Proof.AesCcm.X86.onePub s₁ s₂) : VG.Proof.AesCcm.X86.pubOf s₁ = VG.Proof.AesCcm.X86.pubOf s₂ := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [VG.Proof.AesCcm.X86.pubOf, h₁, Prod.mk.injEq, true_and]
  funext i
  split
  · next hi => exact h₂ i hi
  · rfl

/-- `seal` and `open` from their arguments. -/
structure Top (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop where
  args : VG.Proof.AesCcm.X86.Args s K W SP N A D T R nl al n tl
  sp : s.gpr .esp = SP
  a0 : VG.X86.arg s 0 = K
  a1 : VG.X86.arg s 1 = BitVec.ofNat 32 R
  a2 : VG.X86.arg s 2 = N
  a3 : VG.X86.arg s 3 = BitVec.ofNat 32 nl
  a4 : VG.X86.arg s 4 = A
  a5 : VG.X86.arg s 5 = BitVec.ofNat 32 al
  a6 : VG.X86.arg s 6 = D
  a7 : VG.X86.arg s 7 = BitVec.ofNat 32 n
  a8 : VG.X86.arg s 8 = T
  a9 : VG.X86.arg s 9 = BitVec.ofNat 32 tl
  a10 : VG.X86.arg s 10 = W

/-- `Top` for the public values `p`. -/
abbrev TopOf (p : BitVec 32 × (Nat → BitVec 32)) : State → Prop :=
  VG.Proof.AesCcm.X86.Top (p.2 0) (p.2 10) p.1 (p.2 2) (p.2 4) (p.2 6) (p.2 8) (p.2 1).toNat (p.2 3).toNat (p.2 5).toNat
    (p.2 7).toNat (p.2 9).toNat

theorem top_of {s : State}
    (h : VG.Proof.AesCcm.X86.Args s (VG.X86.arg s 0) (VG.X86.arg s 10) (s.gpr .esp) (VG.X86.arg s 2) (VG.X86.arg s 4) (VG.X86.arg s 6) (VG.X86.arg s 8) (VG.X86.arg s 1).toNat
      (VG.X86.arg s 3).toNat (VG.X86.arg s 5).toNat (VG.X86.arg s 7).toNat (VG.X86.arg s 9).toNat)
    {p : BitVec 32 × (Nat → BitVec 32)} (hp : VG.Proof.AesCcm.X86.pubOf s = p) : VG.Proof.AesCcm.X86.TopOf p s := by
  subst hp
  simp only [VG.Proof.AesCcm.X86.pubOf, show (0 : Nat) < 11 from by decide, show (1 : Nat) < 11 from by decide,
    show (2 : Nat) < 11 from by decide, show (3 : Nat) < 11 from by decide, show (4 : Nat) < 11 from by decide,
    show (5 : Nat) < 11 from by decide, show (6 : Nat) < 11 from by decide, show (7 : Nat) < 11 from by decide,
    show (8 : Nat) < 11 from by decide, show (9 : Nat) < 11 from by decide, show (10 : Nat) < 11 from by decide,
    ↓reduceIte]
  exact ⟨h, rfl, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm,
    rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl⟩

/-! ## The start -/

theorem entry_ct {I : State → Prop} {W SP : BitVec 32}
    (h : ∀ s, I s → s.gpr .esp = SP ∧ VG.X86.arg s 10 = W ∧ Covers [argsR SP 11] (s.rd ++ s.wr) ∧
      SP.toNat + 4 + 4 * 11 ≤ 2 ^ 32) : CT I ccmEntry := by
  refine CT.seq (J := fun s => s.gpr .eax = W ∧ s.gpr .esp = SP)
    (CT.taint [.esp] (VG.Proof.AesCcm.X86.pin1 fun s h' => (h s h').1) (by taint_decide)) (fun s hs => ?_)
    (CT.taint [.eax, .esp] (VG.Proof.AesCcm.X86.pin2 fun _ h => h) (by taint_decide))
  obtain ⟨hSP, hW, rA, fa⟩ := h s hs
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 10) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.of_runBlock ⟨_, by crun [hSP, i₀], ?_, ?_⟩
  · rw [gpr_setReg_self, ← hSP]; exact hW
  · rw [gpr_setReg_of_ne _ _ (by decide), hSP]

theorem start_ct {K W SP N A D T : BitVec 32} {R nl al n tl : Nat} (L : VG.Proof.AesCcm.X86.Lay K W SP) (h13 : nl ≤ 13) :
    CT (VG.Proof.AesCcm.X86.Top K W SP N A D T R nl al n tl) (.seq ccmEntry ctrs) := by
  refine CT.seq (J := fun s₁ => ∃ s, VG.Proof.AesCcm.X86.Top K W SP N A D T R nl al n tl s ∧ VG.Proof.AesCcm.X86.Entered s W s₁)
    (VG.Proof.AesCcm.X86.entry_ct fun s hs => ⟨hs.sp, hs.a10, hs.args.args, hs.args.fa⟩)
    (fun s hs => WP.mono (VG.Proof.AesCcm.X86.entry_ok hs.a10 hs.args.perm.w (by rw [hs.sp]; exact hs.args.args)
      (by rw [hs.sp]; exact hs.args.argsW) (by rw [hs.sp]; exact hs.args.fa) L.fw) fun s₁ E => ⟨s, hs, E⟩)
    (VG.Proof.AesCcm.X86.ctrs_ct L h13 fun s₁ ⟨s, hs, E₀⟩ => ⟨⟨E₀.ebp, by rw [E₀.esp, hs.sp], hs.args.perm.of_eq E₀.rd E₀.wr⟩,
      by rw [E₀.slots (2, nonceO) (by simp), hs.a2], by rw [E₀.slots (3, nlenO) (by simp), hs.a3]⟩)

/-! ## What the pieces keep -/

/-- After the start, and the pieces after it. -/
structure Run (s₀ : State) (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop where
  env : VG.Proof.AesCcm.X86.Env K W SP s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  st : ∃ s₂, VG.Proof.AesCcm.X86.Started s₀ K W SP N A D T R nl al n tl s₂ ∧ Frame (VG.Proof.AesCcm.X86.mutR W SP D n) s₂.mem s.mem
  c0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s₀.mem (w64 N) nl) 0

section
variable {s₀ : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}

theorem Run.of_started {s₂ : State} (St : VG.Proof.AesCcm.X86.Started s₀ K W SP N A D T R nl al n tl s₂) :
    VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s₂ :=
  ⟨St.env, St.rd, St.wr, ⟨s₂, St, Frame.refl _ _⟩, St.c0⟩

theorem Run.step {s : State} (h : VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s) {s' : State} (E : VG.Proof.AesCcm.X86.Env K W SP s')
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) {rs : List Region} (f : Frame rs s.mem s'.mem) (hm : VG.Proof.AesCcm.X86.InMut W SP D n rs)
    (hc : ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r) : VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s' := by
  obtain ⟨s₂, St, f₂⟩ := h.st
  exact ⟨E, by rw [rd, h.rd], by rw [wr, h.wr], ⟨s₂, St, f₂.trans (VG.Proof.AesCcm.X86.frame_toMut f hm)⟩,
    by rw [Proof.AesGcm.X86.bytesAt_frame f hc (by decide), h.c0]⟩

theorem Run.slots {s : State} (Ar : VG.Proof.AesCcm.X86.Args s₀ K W SP N A D T R nl al n tl) (h : VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s) :
    VG.Proof.AesCcm.X86.Slots W K R N A D T nl al n tl s.mem := by
  obtain ⟨s₂, St, f₂⟩ := h.st
  exact (St.mut Ar f₂).1

theorem Run.mac_pre {s : State} (Ar : VG.Proof.AesCcm.X86.Args s₀ K W SP N A D T R nl al n tl) (h : VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s) :
    VG.Proof.AesCcm.X86.MacPre K W SP R N A D T nl al n tl s :=
  ⟨⟨h.env, h.slots Ar, Ar.aad.of_eq h.rd h.wr, Ar.data.of_eq h.rd h.wr⟩,
    ⟨_, length_bytesAt _ _ _, h.c0⟩⟩

theorem Run.tag_pre {s : State} (Ar : VG.Proof.AesCcm.X86.Args s₀ K W SP N A D T R nl al n tl) (h : VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s) :
    VG.Proof.AesCcm.X86.TagPre K W SP R s :=
  ⟨h.env, (h.slots Ar).ctx, (h.slots Ar).rounds,
    ⟨_, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13, h.c0⟩⟩

theorem Run.ctr_pre {s : State} (Ar : VG.Proof.AesCcm.X86.Args s₀ K W SP N A D T R nl al n tl) (h : VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s) :
    VG.Proof.AesCcm.X86.CtrPre K W SP R D n s :=
  ⟨h.env, (h.slots Ar).ctx, (h.slots Ar).rounds, (h.slots Ar).data, (h.slots Ar).len,
    ⟨_, ⟨Ar.lay, Ar.rounds, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13,
      by rw [length_bytesAt]; exact Ar.hn, Ar.n32, h.c0, Ar.data.of_eq h.rd h.wr, by rw [h.wr]; exact Ar.dw,
      Ar.dk⟩⟩⟩

/-- After the MAC into `W + y`. -/
theorem Run.mac {s : State} (Ar : VG.Proof.AesCcm.X86.Args s₀ K W SP N A D T R nl al n tl) (h : VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {Y : List Byte} {s' : State} (A' : VG.Proof.AesCcm.X86.Absorbed K W SP s y Y s') :
    VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s' :=
  h.step A'.env A'.rd A'.wr A'.frame (VG.Proof.AesCcm.X86.inMut_macR W SP D n hy) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (Ar.lay.stk_w' (by decide)).symm

/-- After the tag at `W + y`. -/
theorem Run.tag {s : State} (Ar : VG.Proof.AesCcm.X86.Args s₀ K W SP N A D T R nl al n tl) (h : VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {s' : State} (E : VG.Proof.AesCcm.X86.Env K W SP s') (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (f : Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, VG.Proof.AesCcm.X86.wC W, below SP 56] s.mem s'.mem) :
    VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s' :=
  h.step E rd wr f (VG.Proof.AesCcm.X86.inMut_tag W SP D n hy) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · rcases hy with rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (Ar.lay.stk_w' (by decide)).symm

/-- After counter mode. -/
theorem Run.ctr {s : State} (Ar : VG.Proof.AesCcm.X86.Args s₀ K W SP N A D T R nl al n tl) (h : VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s)
    {s' : State} (E : VG.Proof.AesCcm.X86.Env K W SP s') (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (f : Frame (VG.Proof.AesCcm.X86.ctrR W SP D n) s.mem s'.mem) :
    VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s' :=
  h.step E rd wr f (VG.Proof.AesCcm.X86.inMut_ctrR W SP D n) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (Ar.lay.stk_w' (by decide)).symm
    · exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm

end

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.SealCT`. -/
section

/-!
# AES-CCM on x86: `vg_aes_ccm_seal` is constant time

Untrusted: everything here is checked by Lean. From the public values (the
arguments and `esp`), the start, the MAC, the tag, counter mode, the tag
copied out and the exit are each constant time (`seal_top_ct`); so is `seal`
(`seal_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (restore)
open VG.Proof.AesGcm.X86 (CT w64 length_bytesAt)

/-- `seal` from its arguments: `Top`, with the tag writable. -/
structure SealTop (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop
    extends VG.Proof.AesCcm.X86.Top K W SP N A D T R nl al n tl s where
  tw : Covers [⟨w64 T, tl⟩] s.wr

theorem seal_top_of {s : State} (h : VG.Proof.AesCcm.X86.sealPre s) {p : BitVec 32 × (Nat → BitVec 32)} (hp : VG.Proof.AesCcm.X86.pubOf s = p) :
    VG.Proof.AesCcm.X86.SealTop (p.2 0) (p.2 10) p.1 (p.2 2) (p.2 4) (p.2 6) (p.2 8) (p.2 1).toNat (p.2 3).toNat (p.2 5).toNat
      (p.2 7).toNat (p.2 9).toNat s := by
  refine ⟨VG.Proof.AesCcm.X86.top_of (VG.Proof.AesCcm.X86.args_of_seal h) hp, ?_⟩
  subst hp
  simp only [VG.Proof.AesCcm.X86.pubOf, show (8 : Nat) < 11 from by decide, show (9 : Nat) < 11 from by decide, ↓reduceIte]
  exact VG.Proof.AesCcm.X86.tag_wr h

theorem seal_top_ct (v : Ctr32Impl) {K W SP N A D T : BitVec 32} {R nl al n tl : Nat} (z : State)
    (Tz : VG.Proof.AesCcm.X86.SealTop K W SP N A D T R nl al n tl z) :
    CT (VG.Proof.AesCcm.X86.SealTop K W SP N A D T R nl al n tl) («seal» v.callee v.suffix) := by
  have Ar := Tz.args
  have L := Ar.lay
  have h7' : ∀ m : Mem, 7 ≤ (bytesAt m (w64 N) nl).length := fun m => by rw [length_bytesAt]; exact Ar.h7
  have h13' : ∀ m : Mem, (bytesAt m (w64 N) nl).length ≤ 13 := fun m => by rw [length_bytesAt]; exact Ar.h13
  refine RelCT.assoc (CT.seq (J := fun s => ∃ s₀, VG.Proof.AesCcm.X86.SealTop K W SP N A D T R nl al n tl s₀ ∧ VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s)
    ((VG.Proof.AesCcm.X86.start_ct L Ar.h13).mono fun s hs => hs.toTop) (fun s hs => WP.mono (VG.Proof.AesCcm.X86.start_ok hs.args hs.sp hs.a0 hs.a1 hs.a2 hs.a3 hs.a4 hs.a5 hs.a6 hs.a7
      hs.a8 hs.a9 hs.a10) fun _ St => ⟨s, hs, Run.of_started St⟩) ?_)
  -- The MAC.
  refine CT.seq (J := fun s => ∃ s₀, VG.Proof.AesCcm.X86.SealTop K W SP N A D T R nl al n tl s₀ ∧ VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s)
    ((VG.Proof.AesCcm.X86.mac_ct v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 (.inl rfl)).mono
      fun s ⟨_, Tp, h⟩ => h.mac_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (VG.Proof.AesCcm.X86.mac_ok v L h.env Ar.rounds (h.slots Tp.args) (length_bytesAt _ _ _) Ar.h7 Ar.h13
      Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 h.c0 (.inl rfl) (Tp.args.aad.of_eq h.rd h.wr)
      (Tp.args.data.of_eq h.rd h.wr)) fun _ A' => ⟨s₀, Tp, h.mac Tp.args (.inl rfl) A'⟩) ?_
  -- The tag.
  refine CT.seq (J := fun s => ∃ s₀, VG.Proof.AesCcm.X86.SealTop K W SP N A D T R nl al n tl s₀ ∧ VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s)
    ((VG.Proof.AesCcm.X86.tag_ct v L Ar.rounds (.inl rfl)).mono fun s ⟨_, Tp, h⟩ => h.tag_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (VG.Proof.AesCcm.X86.tag_ok v L h.env Ar.rounds (h.slots Tp.args).ctx (h.slots Tp.args).rounds (h7' _)
      (h13' _) h.c0 (.inl rfl)) fun _ ⟨E, rd, wr, f, _⟩ => ⟨s₀, Tp, h.tag Tp.args (.inl rfl) E rd wr f⟩) ?_
  -- Counter mode.
  refine CT.seq (J := fun s => ∃ s₀, VG.Proof.AesCcm.X86.SealTop K W SP N A D T R nl al n tl s₀ ∧ VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s)
    ((VG.Proof.AesCcm.X86.ctr_ct v L Ar.rounds Ar.n32).mono fun s ⟨_, Tp, h⟩ => h.ctr_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => by
      obtain ⟨E, hK, hRo, hDp, hlen, nonce, C⟩ := h.ctr_pre Tp.args
      exact WP.mono (VG.Proof.AesCcm.X86.ctr_ok v C E hK hRo hDp hlen) fun _ ⟨E', rd, wr, f, _⟩ => ⟨s₀, Tp, h.ctr Tp.args E' rd wr f⟩) ?_
  -- The tag copied out.
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    (VG.Proof.AesCcm.X86.tagOut_ct L fun s ⟨_, Tp, h⟩ => ⟨h.env, (h.slots Tp.args).tl, (h.slots Tp.args).tp⟩)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (VG.Proof.AesCcm.X86.tagOut_ok L h.env (h.slots Tp.args).tl (h.slots Tp.args).tp
      (by have := Ar.t4; omega) Ar.t16 (Tp.args.tag.of_eq h.rd h.wr) (by rw [h.wr]; exact Tp.tw))
      fun _ ⟨_, E, _, _⟩ => E.ebp) ?_
  -- The exit.
  exact CT.taint [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ h => h) (by taint_decide)

theorem seal_ct (v : Ctr32Impl) : ConstantTime isa sealX86.pre sealX86.pub («seal» v.callee v.suffix) :=
  CT.constantTime VG.Proof.AesCcm.X86.pubOf (fun _ _ _ _ h => VG.Proof.AesCcm.X86.pubOf_eq h) fun p => by
    by_cases hex : ∃ s, sealX86.pre s ∧ VG.Proof.AesCcm.X86.pubOf s = p
    · obtain ⟨z, hz, hp⟩ := hex
      exact (VG.Proof.AesCcm.X86.seal_top_ct v z (VG.Proof.AesCcm.X86.seal_top_of hz hp)).mono fun s hs => VG.Proof.AesCcm.X86.seal_top_of hs.1 hs.2
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Open`. -/
section

/-!
# AES-CCM on x86: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is the start (the
entry and `Ctr₀`), counter mode over the data, which decrypts it (`ctr_ok`),
the MAC of the plaintext at `W + 96` (`mac_ok`), encrypted (`tag_ok`), the
received tag padded (AES-GCM's `recv_ok`) and compared with it without a branch
(AES-GCM's `cmp_ok`), the data masked (`mask_ok`) and the exit
(`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot cmp recv tglO tpO rO vO)
open VG.Proof.AesGcm.X86 (w64 slotv SavedAt exit_ok ofNat_toNat32 length_bytesAt covers_left WEnv)

theorem ofNat_ite (p : Prop) [Decidable p] :
    BitVec.ofNat 32 (if p then 1 else 0) = if decide p = true then 1 else 0 := by
  by_cases h : p <;> simp [h]

theorem append_zeros_iff {x y : List Byte} {k : Nat} :
    x ++ Spec.Gcm.zeros k = y ++ Spec.Gcm.zeros k ↔ x = y :=
  ⟨List.append_cancel_right, fun h => by rw [h]⟩

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp' (v : Ctr32Impl) {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : VG.Proof.AesCcm.X86.Args s K W SP N A D T R nl al n tl) (hsp : s.gpr .esp = SP) (a0 : VG.X86.arg s 0 = K)
    (a1 : VG.X86.arg s 1 = BitVec.ofNat 32 R) (a2 : VG.X86.arg s 2 = N) (a3 : VG.X86.arg s 3 = BitVec.ofNat 32 nl) (a4 : VG.X86.arg s 4 = A)
    (a5 : VG.X86.arg s 5 = BitVec.ofNat 32 al) (a6 : VG.X86.arg s 6 = D) (a7 : VG.X86.arg s 7 = BitVec.ofNat 32 n) (a8 : VG.X86.arg s 8 = T)
    (a9 : VG.X86.arg s 9 = BitVec.ofNat 32 tl) (a10 : VG.X86.arg s 10 = W) :
    WP isa («open» v.callee v.suffix) s fun s' => abiPreserved s s' ∧
      match Spec.Ccm.decryptWith (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl)
          (bytesAt s.mem (w64 D) n) (bytesAt s.mem (w64 A) al) (bytesAt s.mem (w64 T) tl) with
      | some pt => s'.gpr .eax = 1 ∧ bytesAt s'.mem (w64 D) n = pt
      | none => s'.gpr .eax = 0 ∧ bytesAt s'.mem (w64 D) n = Spec.Ccm.zeros n := by
  have L := Ar.lay
  have hnl := length_bytesAt s.mem (w64 N) nl
  have h7' : 7 ≤ (bytesAt s.mem (w64 N) nl).length := by rw [hnl]; exact Ar.h7
  have h13' : (bytesAt s.mem (w64 N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  have ht16 := Ar.t16
  have ht4 := Ar.t4
  refine VG.Proof.AesCcm.X86.seq_assoc (WP.seq (WP.mono (VG.Proof.AesCcm.X86.start_ok Ar hsp a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) fun s₂ St => ?_))
  -- Counter mode: the plaintext.
  have C₂ : VG.Proof.AesCcm.X86.CtrCtx K W SP s₂ R (bytesAt s.mem (w64 N) nl) D n :=
    ⟨L, Ar.rounds, h7', h13', by rw [hnl]; exact Ar.hn, Ar.n32, St.c0, Ar.data.of_eq St.rd St.wr,
      by rw [St.wr]; exact Ar.dw, Ar.dk⟩
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.ctr_ok v C₂ St.env St.slots.ctx St.slots.rounds St.slots.data St.slots.len)
    fun s₃ ⟨E₃, rd₃, wr₃, f₃, h₃⟩ => ?_)
  have f₂₃ : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) s₂.mem s₃.mem := VG.Proof.AesCcm.X86.frame_toMut f₃ (VG.Proof.AesCcm.X86.inMut_ctrR W SP D n)
  obtain ⟨S₃, -, -, -, -⟩ := St.mut Ar f₂₃
  have hc₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 :=
    C₂.c0_kept f₃
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, St.rd]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, St.wr]
  -- The MAC of the plaintext.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.mac_ok v L E₃ Ar.rounds S₃ hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn
    Ar.n32 hc₃ (y := 96) (.inr rfl) (Ar.aad.of_eq rd₃' wr₃') (Ar.data.of_eq rd₃' wr₃')) fun s₄ A₄ => ?_)
  have f₂₄ : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) s₂.mem s₄.mem := f₂₃.trans (VG.Proof.AesCcm.X86.frame_toMut A₄.frame (VG.Proof.AesCcm.X86.inMut_macR W SP D n (.inr rfl)))
  obtain ⟨S₄, -, -, -, -⟩ := St.mut Ar f₂₄
  have hc₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 := by
    rw [VG.Proof.AesCcm.X86.c0_kept (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) A₄.frame, hc₃]
  -- The tag of the plaintext.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.tag_ok v L A₄.env Ar.rounds S₄.ctx S₄.rounds h7' h13' hc₄ (y := 96) (.inr rfl))
    fun s₅ ⟨E₅, rd₅, wr₅, f₅, h₅⟩ => ?_)
  have f₂₅ : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) s₂.mem s₅.mem := f₂₄.trans (VG.Proof.AesCcm.X86.frame_toMut f₅ (VG.Proof.AesCcm.X86.inMut_tag W SP D n (.inr rfl)))
  obtain ⟨S₅, -, -, -, -⟩ := St.mut Ar f₂₅
  have rd₅' : s₅.rd = s.rd := by rw [rd₅, A₄.rd, rd₃']
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, A₄.wr, wr₃']
  -- The received tag.
  have Tb₅ := Ar.tag.of_eq rd₅' wr₅'
  refine WP.seq (WP.mono (Proof.AesGcm.X86.recv_ok ⟨E₅.ebp, E₅.perm.w, L.fw⟩ S₅.tl S₅.tp Tb₅.rd Tb₅.wrap Tb₅.w
    (by omega) ht16) fun s₆ ⟨b₆, f₆, bp₆, _, sp₆, rd₆, wr₆⟩ => ?_)
  have E₆ : VG.Proof.AesCcm.X86.Env K W SP s₆ := ⟨by rw [bp₆, E₅.ebp], by rw [sp₆, E₅.esp], E₅.perm.of_eq rd₆ wr₆⟩
  -- The comparison.
  have hv₆ : slotv s₆.mem W tglO = BitVec.ofNat 32 tl := by
    show s₆.mem.readW (w64 W + BitVec.ofNat 64 tglO) 32 = _
    rw [f₆.readW (r := ⟨w64 W + BitVec.ofNat 64 tglO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)]
    exact S₅.tl
  refine WP.seq (WP.mono (Proof.AesGcm.X86.cmp_ok (o := uO) ⟨E₆.ebp, E₆.perm.w, L.fw⟩ hv₆ (by omega) ht16 (by decide))
    fun s₇ ⟨ax₇, f₇, bp₇, _, sp₇, rd₇, wr₇⟩ => ?_)
  rw [VG.Proof.AesCcm.X86.ofNat_ite] at ax₇
  generalize hc : decide (bytesAt s₆.mem (w64 W + BitVec.ofNat 64 uO) tl ++ Spec.Gcm.zeros (16 - tl) =
    bytesAt s₆.mem (w64 W + BitVec.ofNat 64 rO) 16) = c at ax₇
  have E₇ : VG.Proof.AesCcm.X86.Env K W SP s₇ := ⟨by rw [bp₇, E₆.ebp], by rw [sp₇, E₆.esp], E₆.perm.of_eq rd₇ wr₇⟩
  -- `ok` kept.
  obtain ⟨s₈, run₈, hm₈, bp₈, sp₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [.store (at_ .ebp okO) .eax] s₇ = some s₈ ∧
      s₈.mem = s₇.mem.writeW (w64 W + BitVec.ofNat 64 okO) (if c = true then (1 : BitVec 32) else 0) ∧
      s₈.gpr .ebp = W ∧ s₈.gpr .esp = SP ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by crun [E₇.ebp, L.aW, E₇.perm.wW], ?_, ?_, ?_, ?_, ?_⟩
    · cmems [ax₇]
    · cregs [E₇.ebp]
    · cregs [E₇.esp]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  have E₈ : VG.Proof.AesCcm.X86.Env K W SP s₈ := ⟨bp₈, sp₈, E₇.perm.of_eq rd₈ wr₈⟩
  have f₅₈ : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) s₅.mem s₈.mem := by
    rw [hm₈]
    refine (((f₆.sub fun r hr => ?_).trans (f₇.sub fun r hr => ?_)).writeW (r := VG.Proof.AesCcm.X86.wO W) (by simp) _
      (Region.contains_self _ _))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86.wT W, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
  have f₂₈ : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) s₂.mem s₈.mem := f₂₅.trans f₅₈
  obtain ⟨S₈, -, -, -, -⟩ := St.mut Ar f₂₈
  have rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₇, rd₆, rd₅']
  have wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₇, wr₆, wr₅']
  -- The data masked.
  have hok : slotv s₈.mem W okO = if c = true then 1 else 0 := by rw [hm₈]; exact Mem.readW_writeW_self32 _ _ _
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86.mask_ok L E₈ S₈.data S₈.len Ar.n32 (Ar.data.of_eq rd₈' wr₈') (by rw [wr₈']; exact Ar.dw) hok)
    fun s₉ ⟨E₉, rd₉, wr₉, hm₉⟩ => ?_)
  have f₈₉ : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) s₈.mem s₉.mem := by
    rw [hm₉]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [Proof.AesCcm.X86.length_mask]; exact Region.contains_self _ _) |>.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have f₂₉ : Frame (VG.Proof.AesCcm.X86.mutR W SP D n) s₂.mem s₉.mem := f₂₈.trans f₈₉
  obtain ⟨S₉, sv₉, -, -, rt₉⟩ := St.mut Ar f₂₉
  have hok₉ : slotv s₉.mem W okO = if c = true then 1 else 0 := by
    rw [hm₉]
    refine (VG.WriteBytes.writeBytes_frame _ _ _ (R := ⟨w64 D, n⟩) (by rw [VG.Proof.AesCcm.X86.length_mask]; exact Region.contains_self _ _)).readW
      (r := ⟨w64 W + BitVec.ofNat 64 okO, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide) |>.trans hok
    simp only [List.mem_singleton] at hr; subst hr; exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm
  -- `ok` returned.
  obtain ⟨s₁₀, run₁₀, hm₁₀, ax₁₀, bp₁₀, sp₁₀, rd₁₀, wr₁₀⟩ : ∃ s₁₀, runBlock isa [.mov .eax (slot okO)] s₉ = some s₁₀ ∧
      s₁₀.mem = s₉.mem ∧ s₁₀.gpr .eax = (if c = true then 1 else 0) ∧ s₁₀.gpr .ebp = W ∧ s₁₀.gpr .esp = SP ∧
      s₁₀.rd = s₉.rd ∧ s₁₀.wr = s₉.wr := by
    refine ⟨_, by crun [E₉.ebp, L.aW, E₉.perm.wR, hok₉], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hok₉]
    · cregs [E₉.ebp]
    · cregs [E₉.esp]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩)
  -- The exit.
  have rd₁₀' : s₁₀.rd = s.rd := by rw [rd₁₀, rd₉, rd₈']
  have wr₁₀' : s₁₀.wr = s.wr := by rw [wr₁₀, wr₉, wr₈']
  refine WP.mono (exit_ok (W := W) (s₀ := s) bp₁₀ (by rw [sp₁₀, hsp])
    (by rw [rd₁₀', wr₁₀']; exact covers_left Ar.perm.w) L.fw (by rw [hm₁₀]; exact sv₉)
    (by rw [hm₁₀, hsp]; exact rt₉)) fun s' ⟨abi, m', ax', _, _⟩ => ⟨abi, ?_⟩
  -- The plaintext, the tags and the comparison.
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (w64 K) R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  have ci₃ := (St.mut Ar f₂₃).2.2.1
  have ci₄ := (St.mut Ar f₂₄).2.2.1
  have aa₃ := (St.mut Ar f₂₃).2.2.2.1
  have dW : ∀ (r : Region), Region.Sub r ⟨w64 W, 2560⟩ ∨ r = below SP 56 → (⟨w64 D, n⟩ : Region).Disjoint r :=
    fun r h => by rcases h with h | rfl; exact Ar.data.w.sub_right h; exact Ar.data.stk.symm
  have pt₃ : bytesAt s₃.mem (w64 D) n =
      Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n) := by
    rw [h₃, St.ciph, St.dataB, crypt_eq (hBC _)]
  have pt₈ : bytesAt s₈.mem (w64 D) n = bytesAt s₃.mem (w64 D) n := by
    rw [hm₈, bytesAt_writeW_sep _ _ (Ar.data.w.sub_right (Lay.wSub (by decide))) (by have := Ar.data.lt; omega),
      Proof.AesGcm.X86.bytesAt_frame f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
        (by have := Ar.data.lt; omega),
      Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
        (by have := Ar.data.lt; omega),
      VG.Proof.AesCcm.X86.buf_kept' Ar.data (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inr rfl) f₅,
      VG.Proof.AesCcm.X86.buf_kept Ar.data (y := 96) (by decide) A₄.frame]
  have tg₅ : bytesAt s₅.mem (w64 T) tl = bytesAt s.mem (w64 T) tl := by
    rw [VG.Proof.AesCcm.X86.buf_mut Ar.tag Ar.td f₂₅, St.tagB]
  have hl : (bytesAt s.mem (w64 N) nl).length ≤ 15 := by rw [hnl]; have := Ar.h13; omega
  have o₄ := A₄.out
  rw [ci₃, aa₃, pt₃] at o₄
  have hY := congrArg List.length o₄
  rw [length_bytesAt] at hY
  have hV : bytesAt s₆.mem (w64 W + BitVec.ofNat 64 uO) tl =
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 A) al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n))) := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (.inl (by simp only [uO, rO]; omega)) (by simp only [uO]; omega) (by decide)) (by omega),
      Proof.AesCcm.bytesAt_prefix s₅.mem _ ht16, h₅, ci₄, o₄, take_xorFrom_zero (hBC _) _ hY.symm ht16,
      ← Proof.AesCcm.mac_eq _ _ hl]
  have hML : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 A) al)
      (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n))).length =
        tl := by
    rw [Proof.AesCcm.mac_eq _ _ hl, List.length_take, length_bytesAt] at *; omega
  have key : c = true ↔
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 T) tl) =
        Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 A) al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n)) := by
    rw [← hc, b₆, tg₅, hV, decide_eq_true_iff,
      VG.Proof.AesCcm.X86.append_zeros_iff, cryptTag_eq_iff (hBC _) ht16 _ hML (length_bytesAt _ _ _), eq_comm]
  simp only [Spec.Ccm.decryptWith]
  have hD₉ : bytesAt s'.mem (w64 D) n = if c then bytesAt s₈.mem (w64 D) n else Spec.Ccm.zeros n := by
    rw [m', hm₁₀, hm₉, bytesAt_writeBytes_base _ _ _ (by rw [VG.Proof.AesCcm.X86.length_mask]) (by have := Ar.data.lt; omega),
      List.drop_eq_nil_of_le (by rw [VG.Proof.AesCcm.X86.length_mask, length_bytesAt]), List.append_nil]
  by_cases hk : c = true
  · have hk' := key.mp hk
    simp only [hk', ↓reduceIte]
    refine ⟨by rw [ax', ax₁₀, hk]; rfl, by rw [hD₉, hk]; simp only [↓reduceIte]; rw [pt₈, pt₃]⟩
  · have hk' : ¬ _ := fun e => hk (key.mpr e)
    simp only [hk', ↓reduceIte]
    have hf : c = false := by simpa using hk
    refine ⟨by rw [ax', ax₁₀, hf]; rfl, by rw [hD₉, hf]; rfl⟩

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.OpenCT`. -/
section

/-!
# AES-CCM on x86: `vg_aes_ccm_open` is constant time

Untrusted: everything here is checked by Lean. After the pieces `seal` also
has (`SealCT.lean`), `open` compares the tags without a branch (AES-GCM's
`recv` and `cmp`, `cmp96_ct`), keeps the result and masks the data with it,
looping over the data's length alone (`mask_ct`): `open_top_ct`, `open_ct`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop cmp recv restore tglO tpO rO vO)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq WEnv cmp_ok recv_ct recv_ok length_bytesAt and_self_beq32 readW_writeW_off)

/-- `cmp 96` (AES-GCM's `cmp_ct`, for CCM's offset of the computed tag). -/
theorem cmp96_ct {I : State → Prop} {W : BitVec 32} {t : Nat}
    (h : ∀ s, I s → WEnv W s ∧ slotv s.mem W tglO = BitVec.ofNat 32 t) : CT I (cmp uO) := by
  have hb : CT I (.block (zero4 vO ++ [.mov .edi (.reg .ebp), .alu .add .edi (imm uO), .mov .edx (.reg .ebp),
      .alu .add .edx (imm vO), .mov .ecx (slot tglO)])) :=
    CT.taint [.ebp] (VG.Proof.AesCcm.X86.pin1 fun s hs => (h s hs).1.ebp) (by taint_decide)
  refine CT.seq (J := fun s => s.gpr .edi = W + BitVec.ofNat 32 uO ∧ s.gpr .edx = W + BitVec.ofNat 32 vO ∧
      s.gpr .ecx = BitVec.ofNat 32 t ∧ s.gpr .ebp = W) hb
    (fun s hs => ?_) (CT.taint [.edi, .edx, .ecx, .ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide))
  obtain ⟨he, hv⟩ := h s hs
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => he.aW ho
  have wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn ho
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn' ho
  rw [slotv_eq] at hv
  simp only [tglO] at hv
  exact WP.of_runBlock ⟨_, by xrun [zero4, he.ebp, aW, wIn, rIn, readW_writeW_off, hv], by regs [he.ebp],
    by regs [he.ebp], by regs [], by regs [he.ebp]⟩

/-! ## Masking the data -/

theorem maskTest_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) {n : Nat}
    (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) :
    ∃ s₁, runBlock isa [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n ∧ s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hlen]
  · cmems [hlen]; rw [and_self_beq32 hn32]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

theorem maskArgs_ok {K W SP : BitVec 32} {s₁ : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E₁ : VG.Proof.AesCcm.X86.Env K W SP s₁) {D : BitVec 32} {n : Nat}
    (hd₁ : slotv s₁.mem W dataO = D) (cx₁ : s₁.gpr .ecx = BitVec.ofNat 32 n) :
    ∃ s₂, runBlock isa [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧
      s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n := by
  refine ⟨_, by crun [E₁.ebp, L.aW, E₁.perm.wR, hd₁], ?_, ?_⟩
  · cregs [hd₁]
  · cregs [cx₁]

theorem mask_ct {K W SP : BitVec 32} (L : VG.Proof.AesCcm.X86.Lay K W SP) {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32)
    {I : State → Prop}
    (h : ∀ s, I s → VG.Proof.AesCcm.X86.Env K W SP s ∧ slotv s.mem W dataO = D ∧ slotv s.mem W lenO = BitVec.ofNat 32 n) :
    CT I mask := by
  refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun s hs => (h s hs).1.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesCcm.X86.maskTest_ok L (h s hs).1 (h s hs).2.2 hn32) ?_
  refine CT.ite (decide (n = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => VG.Proof.AesCcm.X86.eval_e hzf) (fun _ => CT.nil) fun _ => ?_
  refine CT.block_seq [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ ⟨_, _, _, _, _, hbp, _⟩ => hbp) (by taint_decide)
    (fun s₁ ⟨s, hs, m₁, cx₁, _, bp₁, sp₁, rd₁, wr₁⟩ => VG.Proof.AesCcm.X86.maskArgs_ok L
      ⟨bp₁, sp₁, (h s hs).1.perm.of_eq rd₁ wr₁⟩ (by rw [m₁]; exact (h s hs).2.1) cx₁) ?_
  exact CT.taint [.edi, .ecx] (VG.Proof.AesCcm.X86.pin2 fun _ ⟨_, _, hdi, hcx⟩ => ⟨hdi, hcx⟩) (by taint_decide)

/-! ## `open` -/

theorem okStore_ok {K W SP : BitVec 32} {s : State} (L : VG.Proof.AesCcm.X86.Lay K W SP) (E : VG.Proof.AesCcm.X86.Env K W SP s) :
    ∃ s', runBlock isa [.store (at_ .ebp okO) .eax] s = some s' ∧
      s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 okO) (s.gpr .eax) ∧ VG.Proof.AesCcm.X86.Env K W SP s' ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW], ?_, E.keep (by cregs []) (by cregs []) (by cmems []) (by cmems []), ?_, ?_⟩
  all_goals cmems []

theorem open_top_ct (v : Ctr32Impl) {K W SP N A D T : BitVec 32} {R nl al n tl : Nat} (z : State)
    (Tz : VG.Proof.AesCcm.X86.Top K W SP N A D T R nl al n tl z) :
    CT (VG.Proof.AesCcm.X86.Top K W SP N A D T R nl al n tl) («open» v.callee v.suffix) := by
  have Ar := Tz.args
  have L := Ar.lay
  have h7' : ∀ m : Mem, 7 ≤ (bytesAt m (w64 N) nl).length := fun m => by rw [length_bytesAt]; exact Ar.h7
  have h13' : ∀ m : Mem, (bytesAt m (w64 N) nl).length ≤ 13 := fun m => by rw [length_bytesAt]; exact Ar.h13
  have c0W : ∀ {d k : Nat}, (64 ≤ d ∨ d + k ≤ 48) → d + k ≤ 2560 →
      (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := fun h₁ h₂ =>
    Lay.w_w (by omega) (by decide) h₂
  refine RelCT.assoc (CT.seq (J := fun s => ∃ s₀, VG.Proof.AesCcm.X86.Top K W SP N A D T R nl al n tl s₀ ∧ VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s)
    (VG.Proof.AesCcm.X86.start_ct L Ar.h13) (fun s hs => WP.mono (VG.Proof.AesCcm.X86.start_ok hs.args hs.sp hs.a0 hs.a1 hs.a2 hs.a3 hs.a4 hs.a5 hs.a6 hs.a7
      hs.a8 hs.a9 hs.a10) fun _ St => ⟨s, hs, Run.of_started St⟩) ?_)
  -- Counter mode.
  refine CT.seq (J := fun s => ∃ s₀, VG.Proof.AesCcm.X86.Top K W SP N A D T R nl al n tl s₀ ∧ VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s)
    ((VG.Proof.AesCcm.X86.ctr_ct v L Ar.rounds Ar.n32).mono fun s ⟨_, Tp, h⟩ => h.ctr_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => by
      obtain ⟨E, hK, hRo, hDp, hlen, nonce, C⟩ := h.ctr_pre Tp.args
      exact WP.mono (VG.Proof.AesCcm.X86.ctr_ok v C E hK hRo hDp hlen) fun _ ⟨E', rd, wr, f, _⟩ => ⟨s₀, Tp, h.ctr Tp.args E' rd wr f⟩) ?_
  -- The MAC.
  refine CT.seq (J := fun s => ∃ s₀, VG.Proof.AesCcm.X86.Top K W SP N A D T R nl al n tl s₀ ∧ VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s)
    ((VG.Proof.AesCcm.X86.mac_ct v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 (.inr rfl)).mono
      fun s ⟨_, Tp, h⟩ => h.mac_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (VG.Proof.AesCcm.X86.mac_ok v L h.env Ar.rounds (h.slots Tp.args) (length_bytesAt _ _ _) Ar.h7 Ar.h13
      Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 h.c0 (.inr rfl) (Tp.args.aad.of_eq h.rd h.wr)
      (Tp.args.data.of_eq h.rd h.wr)) fun _ A' => ⟨s₀, Tp, h.mac Tp.args (.inr rfl) A'⟩) ?_
  -- The tag.
  refine CT.seq (J := fun s => ∃ s₀, VG.Proof.AesCcm.X86.Top K W SP N A D T R nl al n tl s₀ ∧ VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s)
    ((VG.Proof.AesCcm.X86.tag_ct v L Ar.rounds (.inr rfl)).mono fun s ⟨_, Tp, h⟩ => h.tag_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (VG.Proof.AesCcm.X86.tag_ok v L h.env Ar.rounds (h.slots Tp.args).ctx (h.slots Tp.args).rounds (h7' _)
      (h13' _) h.c0 (.inr rfl)) fun _ ⟨E, rd, wr, f, _⟩ => ⟨s₀, Tp, h.tag Tp.args (.inr rfl) E rd wr f⟩) ?_
  -- The received tag.
  refine CT.seq (J := fun s => ∃ s₀, VG.Proof.AesCcm.X86.Top K W SP N A D T R nl al n tl s₀ ∧ VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s)
    (recv_ct (W := W) (T := T) (t := tl) fun s ⟨_, Tp, h⟩ =>
      ⟨⟨h.env.ebp, h.env.perm.w, L.fw⟩, (h.slots Tp.args).tl, (h.slots Tp.args).tp⟩)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (recv_ok ⟨h.env.ebp, h.env.perm.w, L.fw⟩ (h.slots Tp.args).tl (h.slots Tp.args).tp
      (Tp.args.tag.of_eq h.rd h.wr).rd (Tp.args.tag.of_eq h.rd h.wr).wrap (Tp.args.tag.of_eq h.rd h.wr).w
      (by have := Ar.t4; omega) Ar.t16) fun _ ⟨_, f, bp, _, sp, rd, wr⟩ => ⟨s₀, Tp,
        h.step ⟨by rw [bp, h.env.ebp], by rw [sp, h.env.esp], h.env.perm.of_eq rd wr⟩ rd wr f
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86.wT W, by simp, fun _ h => h⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact c0W (.inl (by decide)) (by decide))⟩) ?_
  -- The comparison.
  refine CT.seq (J := fun s => (∃ s₀, VG.Proof.AesCcm.X86.Top K W SP N A D T R nl al n tl s₀ ∧ VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s) ∧
      ∃ c : Bool, s.gpr .eax = if c then 1 else 0)
    (VG.Proof.AesCcm.X86.cmp96_ct (W := W) (t := tl) fun s ⟨_, Tp, h⟩ => ⟨⟨h.env.ebp, h.env.perm.w, L.fw⟩, (h.slots Tp.args).tl⟩)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (cmp_ok (o := uO) ⟨h.env.ebp, h.env.perm.w, L.fw⟩ (h.slots Tp.args).tl
      (by have := Ar.t4; omega) Ar.t16 (by decide)) fun s' ⟨ax, f, bp, _, sp, rd, wr⟩ =>
        ⟨⟨s₀, Tp, h.step ⟨by rw [bp, h.env.ebp], by rw [sp, h.env.esp], h.env.perm.of_eq rd wr⟩ rd wr f
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86.wC W, by simp, Offset.sub _ (by decide) (by decide)⟩)
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact c0W (.inl (by decide)) (by decide))⟩,
          _, by rw [ax, VG.Proof.AesCcm.X86.ofNat_ite]⟩) ?_
  -- `ok` kept.
  refine CT.seq (J := fun s => (∃ s₀, VG.Proof.AesCcm.X86.Top K W SP N A D T R nl al n tl s₀ ∧ VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s) ∧
      ∃ c : Bool, slotv s.mem W okO = if c then 1 else 0)
    (CT.taint [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ ⟨⟨_, _, h⟩, _⟩ => h.env.ebp) (by taint_decide))
    (fun s ⟨⟨s₀, Tp, h⟩, c, hc⟩ => by
      obtain ⟨s', run, hm, E', rd, wr⟩ := VG.Proof.AesCcm.X86.okStore_ok L h.env
      refine WP.of_runBlock ⟨s', run, ⟨s₀, Tp, h.step E' rd wr (rs := [VG.Proof.AesCcm.X86.wO W]) ?_ ?_ ?_⟩, c, ?_⟩
      · rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
      · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86.wO W, by simp, fun _ h => h⟩
      · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact c0W (.inl (by decide)) (by decide)
      · rw [hm, ← hc]; exact Mem.readW_writeW_self32 _ _ _) ?_
  -- The data masked.
  refine CT.seq (J := fun s => ∃ s₀, VG.Proof.AesCcm.X86.Top K W SP N A D T R nl al n tl s₀ ∧ VG.Proof.AesCcm.X86.Run s₀ K W SP N A D T R nl al n tl s)
    (VG.Proof.AesCcm.X86.mask_ct L Ar.n32 fun s ⟨⟨_, Tp, h⟩, _⟩ => ⟨h.env, (h.slots Tp.args).data, (h.slots Tp.args).len⟩)
    (fun s ⟨⟨s₀, Tp, h⟩, c, hc⟩ => WP.mono (VG.Proof.AesCcm.X86.mask_ok L h.env (h.slots Tp.args).data (h.slots Tp.args).len Ar.n32
      (Tp.args.data.of_eq h.rd h.wr) (by rw [h.wr]; exact Tp.args.dw) hc) fun s' ⟨E, rd, wr, hm⟩ =>
        ⟨s₀, Tp, h.step E rd wr (rs := [⟨w64 D, n⟩])
          (by rw [hm]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.AesCcm.X86.length_mask]; exact Region.contains_self _ _))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (Tp.args.data.w.sub_right (Lay.wSub (by decide))).symm)⟩) ?_
  -- `ok` returned, and the exit.
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    (CT.taint [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ ⟨_, _, h⟩ => h.env.ebp) (by taint_decide))
    (fun s ⟨_, _, h⟩ => WP.of_runBlock ⟨_, by crun [h.env.ebp, L.aW, h.env.perm.wR], by cregs [h.env.ebp]⟩)
    (CT.taint [.ebp] (VG.Proof.AesCcm.X86.pin_ebp fun _ h => h) (by taint_decide))

theorem open_ct (v : Ctr32Impl) : ConstantTime isa openX86.pre openX86.pub («open» v.callee v.suffix) :=
  CT.constantTime VG.Proof.AesCcm.X86.pubOf (fun _ _ _ _ h => VG.Proof.AesCcm.X86.pubOf_eq h.1) fun p => by
    by_cases hex : ∃ s, openX86.pre s ∧ VG.Proof.AesCcm.X86.pubOf s = p
    · obtain ⟨z, hz, hp⟩ := hex
      exact (VG.Proof.AesCcm.X86.open_top_ct v z (VG.Proof.AesCcm.X86.top_of (VG.Proof.AesCcm.X86.args_of_open hz) hp)).mono fun s hs => VG.Proof.AesCcm.X86.top_of (VG.Proof.AesCcm.X86.args_of_open hs.1) hs.2
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Verified`. -/
section

/-!
# AES-CCM on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness (`seal_wp'`,
`open_wp'`) and constant time (`seal_ct`, `open_ct`) for any implementation
`v` of `vg_aes_ctr32`, a state satisfying the precondition, and the shared
contracts with the working space as a last argument
(`Proof/AesCcm/Scratch.lean`), with 56 bytes of stack: a call of
`vg_cmac_aes_update` (its six arguments and return address) and its own
calls of `vg_aes_ctr32`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Proof.AesGcm.X86 (ofNat_toNat32)

theorem seal_correct (v : Ctr32Impl) (s : State) (hs : sealX86.pre s) :
    ∃ t s', Exec isa («seal» v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ sealX86.post s s' := by
  obtain ⟨t, s', e, abi, h⟩ := VG.Proof.AesCcm.X86.seal_wp' v (VG.Proof.AesCcm.X86.args_of_seal hs) rfl rfl (ofNat_toNat32 _).symm rfl
    (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl
    (VG.Proof.AesCcm.X86.tag_wr hs)
  exact ⟨t, s', e, abi, h⟩

/-- The return value: the low word of `edx:eax`. -/
theorem setWidth_ret (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := b.isLt
  rw [Nat.shiftLeft_eq, Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.zero_or, Nat.mod_eq_of_lt this]

theorem open_correct (v : Ctr32Impl) (s : State) (hs : openX86.pre s) :
    ∃ t s', Exec isa («open» v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ openX86.post s s' := by
  obtain ⟨t, s', e, abi, h⟩ := VG.Proof.AesCcm.X86.open_wp' v (VG.Proof.AesCcm.X86.args_of_open hs) rfl rfl (ofNat_toNat32 _).symm rfl
    (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl
  refine ⟨t, s', e, abi, ?_⟩
  simp only [VG.Proof.AesCcm.X86.openX86, VG.Proof.AesCcm.X86.setWidth_ret]
  exact h

theorem seal_spSafe (v : Ctr32Impl) : («seal» v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [«seal», ccmEntry, Impl.AesGcm.X86.entry, ctrs, VG.Impl.AesCcm.X86.mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, VG.Impl.AesCcm.X86.tag, VG.Impl.AesCcm.X86.ctr, ctrCall, tagOut, Code.all, Proof.CmacAes.X86.update_spSafe v,
    v.spSafe, Bool.and_true]
  decide +kernel

theorem open_spSafe (v : Ctr32Impl) : («open» v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [«open», ccmEntry, Impl.AesGcm.X86.entry, ctrs, VG.Impl.AesCcm.X86.mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, VG.Impl.AesCcm.X86.tag, VG.Impl.AesCcm.X86.ctr, ctrCall, mask, Impl.AesGcm.X86.recv, Impl.AesGcm.X86.cmp,
    Code.all, Proof.CmacAes.X86.update_spSafe v, v.spSafe, Bool.and_true]
  decide +kernel

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: the key
schedule at `0x1000`, 10 rounds, a 7-byte nonce at `0x2000`, no associated
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
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 4⟩, ⟨0x5000, 2560⟩, ⟨0x8004, 44⟩]

/-- As `sealSat`, with the tag read only. -/
def openSat : State :=
  { VG.Proof.AesCcm.X86.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x4000, 4⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x5000, 2560⟩, ⟨0x8004, 44⟩] }

theorem sealSat_args : VG.X86.arg VG.Proof.AesCcm.X86.sealSat 0 = 0x1000 ∧ VG.X86.arg VG.Proof.AesCcm.X86.sealSat 1 = 10 ∧ VG.X86.arg VG.Proof.AesCcm.X86.sealSat 2 = 0x2000 ∧ VG.X86.arg VG.Proof.AesCcm.X86.sealSat 3 = 7 ∧
    VG.X86.arg VG.Proof.AesCcm.X86.sealSat 4 = 0x2100 ∧ VG.X86.arg VG.Proof.AesCcm.X86.sealSat 5 = 0 ∧ VG.X86.arg VG.Proof.AesCcm.X86.sealSat 6 = 0x3000 ∧ VG.X86.arg VG.Proof.AesCcm.X86.sealSat 7 = 0 ∧
    VG.X86.arg VG.Proof.AesCcm.X86.sealSat 8 = 0x4000 ∧ VG.X86.arg VG.Proof.AesCcm.X86.sealSat 9 = 4 ∧ VG.X86.arg VG.Proof.AesCcm.X86.sealSat 10 = 0x5000 ∧ argAddr VG.Proof.AesCcm.X86.sealSat 0 = 0x8004 := by
  decide

theorem openSat_args : VG.X86.arg VG.Proof.AesCcm.X86.openSat 0 = 0x1000 ∧ VG.X86.arg VG.Proof.AesCcm.X86.openSat 1 = 10 ∧ VG.X86.arg VG.Proof.AesCcm.X86.openSat 2 = 0x2000 ∧ VG.X86.arg VG.Proof.AesCcm.X86.openSat 3 = 7 ∧
    VG.X86.arg VG.Proof.AesCcm.X86.openSat 4 = 0x2100 ∧ VG.X86.arg VG.Proof.AesCcm.X86.openSat 5 = 0 ∧ VG.X86.arg VG.Proof.AesCcm.X86.openSat 6 = 0x3000 ∧ VG.X86.arg VG.Proof.AesCcm.X86.openSat 7 = 0 ∧
    VG.X86.arg VG.Proof.AesCcm.X86.openSat 8 = 0x4000 ∧ VG.X86.arg VG.Proof.AesCcm.X86.openSat 9 = 4 ∧ VG.X86.arg VG.Proof.AesCcm.X86.openSat 10 = 0x5000 ∧ argAddr VG.Proof.AesCcm.X86.openSat 0 = 0x8004 :=
  VG.Proof.AesCcm.X86.sealSat_args

theorem seal_verified (v : Ctr32Impl) :
    Verified X86.target («seal» v.callee v.suffix) (Proof.AesCcm.sealScratchContract X86.abi 56) :=
  Verified.of_correct (VG.Proof.AesCcm.X86.seal_correct v) (VG.Proof.AesCcm.X86.seal_ct v) (by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e⟩ := VG.Proof.AesCcm.X86.sealSat_args
    have esp : sealSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
      Spec.Ccm.sealPost, VG.Proof.AesCcm.X86.sealX86, VG.Proof.AesCcm.X86.sealPre, VG.Proof.AesCcm.X86.oneLay, VG.Proof.AesCcm.X86.onePub, VG.Proof.AesCcm.X86.schR, VG.Proof.AesCcm.X86.nonceR, VG.Proof.AesCcm.X86.aadR, VG.Proof.AesCcm.X86.dataR, VG.Proof.AesCcm.X86.tagR, VG.Proof.AesCcm.X86.workR, VG.Proof.AesCcm.X86.argsR', VG.Proof.AesCcm.X86.retR,
      VG.Proof.AesCcm.X86.stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp] using VG.Proof.AesCcm.X86.sealSat)

theorem open_verified (v : Ctr32Impl) :
    Verified X86.target («open» v.callee v.suffix) (Proof.AesCcm.openScratchContract X86.abi 56) :=
  Verified.of_correct (VG.Proof.AesCcm.X86.open_correct v) (VG.Proof.AesCcm.X86.open_ct v)
    { pre := by
        sig_implies_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openLeak, VG.Proof.AesCcm.X86.openX86, VG.Proof.AesCcm.X86.openLeak, VG.Proof.AesCcm.X86.openRes, VG.Proof.AesCcm.X86.openPre, VG.Proof.AesCcm.X86.oneLay, VG.Proof.AesCcm.X86.onePub, VG.Proof.AesCcm.X86.schR, VG.Proof.AesCcm.X86.nonceR, VG.Proof.AesCcm.X86.aadR, VG.Proof.AesCcm.X86.dataR, VG.Proof.AesCcm.X86.tagR, VG.Proof.AesCcm.X86.workR, VG.Proof.AesCcm.X86.argsR', VG.Proof.AesCcm.X86.retR,
          VG.Proof.AesCcm.X86.stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by
        sig_implies_post [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openPost, Spec.Ccm.openLeak, VG.Proof.AesCcm.X86.openX86, VG.Proof.AesCcm.X86.openLeak, VG.Proof.AesCcm.X86.openRes, VG.Proof.AesCcm.X86.openPre, VG.Proof.AesCcm.X86.oneLay, VG.Proof.AesCcm.X86.onePub, VG.Proof.AesCcm.X86.schR, VG.Proof.AesCcm.X86.nonceR, VG.Proof.AesCcm.X86.aadR, VG.Proof.AesCcm.X86.dataR, VG.Proof.AesCcm.X86.tagR,
          VG.Proof.AesCcm.X86.workR, VG.Proof.AesCcm.X86.argsR', VG.Proof.AesCcm.X86.retR, VG.Proof.AesCcm.X86.stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openLeak, VG.Proof.AesCcm.X86.openX86, VG.Proof.AesCcm.X86.openLeak, VG.Proof.AesCcm.X86.openRes, VG.Proof.AesCcm.X86.openPre, VG.Proof.AesCcm.X86.oneLay, VG.Proof.AesCcm.X86.onePub, VG.Proof.AesCcm.X86.schR, VG.Proof.AesCcm.X86.nonceR, VG.Proof.AesCcm.X86.aadR, VG.Proof.AesCcm.X86.dataR, VG.Proof.AesCcm.X86.tagR, VG.Proof.AesCcm.X86.workR, VG.Proof.AesCcm.X86.argsR', VG.Proof.AesCcm.X86.retR,
          VG.Proof.AesCcm.X86.stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
        sig_split h
        sig_reduce [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openLeak, VG.Proof.AesCcm.X86.openX86, VG.Proof.AesCcm.X86.openLeak, VG.Proof.AesCcm.X86.openRes, VG.Proof.AesCcm.X86.openPre, VG.Proof.AesCcm.X86.oneLay, VG.Proof.AesCcm.X86.onePub, VG.Proof.AesCcm.X86.schR, VG.Proof.AesCcm.X86.nonceR, VG.Proof.AesCcm.X86.aadR, VG.Proof.AesCcm.X86.dataR, VG.Proof.AesCcm.X86.tagR, VG.Proof.AesCcm.X86.workR, VG.Proof.AesCcm.X86.argsR', VG.Proof.AesCcm.X86.retR,
          VG.Proof.AesCcm.X86.stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
        sig_simp [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openLeak, VG.Proof.AesCcm.X86.openX86, VG.Proof.AesCcm.X86.openLeak, VG.Proof.AesCcm.X86.openRes, VG.Proof.AesCcm.X86.openPre, VG.Proof.AesCcm.X86.oneLay, VG.Proof.AesCcm.X86.onePub, VG.Proof.AesCcm.X86.schR, VG.Proof.AesCcm.X86.nonceR, VG.Proof.AesCcm.X86.aadR, VG.Proof.AesCcm.X86.dataR, VG.Proof.AesCcm.X86.tagR, VG.Proof.AesCcm.X86.workR, VG.Proof.AesCcm.X86.argsR', VG.Proof.AesCcm.X86.retR,
          VG.Proof.AesCcm.X86.stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [Nat.forall_lt_succ_right, Nat.not_lt_zero,
          false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by
        obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e⟩ := VG.Proof.AesCcm.X86.openSat_args
        have esp : openSat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openPost, Spec.Ccm.openLeak, VG.Proof.AesCcm.X86.openX86, VG.Proof.AesCcm.X86.openLeak, VG.Proof.AesCcm.X86.openRes, VG.Proof.AesCcm.X86.openPre, VG.Proof.AesCcm.X86.oneLay, VG.Proof.AesCcm.X86.onePub, VG.Proof.AesCcm.X86.schR, VG.Proof.AesCcm.X86.nonceR, VG.Proof.AesCcm.X86.aadR, VG.Proof.AesCcm.X86.dataR, VG.Proof.AesCcm.X86.tagR,
          VG.Proof.AesCcm.X86.workR, VG.Proof.AesCcm.X86.argsR', VG.Proof.AesCcm.X86.retR, VG.Proof.AesCcm.X86.stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
          [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp] using VG.Proof.AesCcm.X86.openSat }

end VG.Proof.AesCcm.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86.Frame`. -/
section

/-!
# AES-CCM on x86, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the ten argument slots and the 2560 bytes of working space, 2608 bytes. The
code's own calls use 56 bytes below it. The copies are read only where the
pre- and postconditions read the buffers, and `open`'s leak, whether it
succeeds, reads only its buffers (`Proof/AesCcm/Scratch.lean`).
-/

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86

theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem seal_noEsp : («seal» v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«seal», ccmEntry, Impl.AesGcm.X86.entry, ctrs, VG.Impl.AesCcm.X86.mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, VG.Impl.AesCcm.X86.tag, VG.Impl.AesCcm.X86.ctr, ctrCall, tagOut, Code.allInstrs,
    VG.Proof.AesCcm.X86.noEsp_of (Proof.CmacAes.X86.update_nosp v), VG.Proof.AesCcm.X86.noEsp_of v.nosp]
  decide +kernel

theorem open_noEsp : («open» v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«open», ccmEntry, Impl.AesGcm.X86.entry, ctrs, VG.Impl.AesCcm.X86.mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, VG.Impl.AesCcm.X86.tag, VG.Impl.AesCcm.X86.ctr, ctrCall, mask, Impl.AesGcm.X86.recv, Impl.AesGcm.X86.cmp,
    Code.allInstrs, VG.Proof.AesCcm.X86.noEsp_of (Proof.CmacAes.X86.update_nosp v), VG.Proof.AesCcm.X86.noEsp_of v.nosp]
  decide +kernel

theorem seal_stackUse : stackUse («seal» v.callee v.suffix) ≤ 56 := by
  simp only [«seal», ccmEntry, Impl.AesGcm.X86.entry, ctrs, VG.Impl.AesCcm.X86.mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, VG.Impl.AesCcm.X86.tag, VG.Impl.AesCcm.X86.ctr, ctrCall, tagOut, stackUse,
    Proof.CmacAes.X86.update_stack v, v.stack]
  decide +kernel

theorem open_stackUse : stackUse («open» v.callee v.suffix) ≤ 56 := by
  simp only [«open», ccmEntry, Impl.AesGcm.X86.entry, ctrs, VG.Impl.AesCcm.X86.mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, VG.Impl.AesCcm.X86.tag, VG.Impl.AesCcm.X86.ctr, ctrCall, mask, Impl.AesGcm.X86.recv, Impl.AesGcm.X86.cmp,
    stackUse, Proof.CmacAes.X86.update_stack v, v.stack]
  decide +kernel

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: as `sealSat`, with ten stack arguments. -/
def sealFrameSat : State :=
  { VG.Proof.AesCcm.X86.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x4000, 4⟩, ⟨0x8004, 40⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ccm.sealContract X86.abi 2664).pre s := by
  implies_sat [Spec.Ccm.sealContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Spec.Ccm.sealPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [sealFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.AesCcm.X86.sealFrameSat

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: as `sealFrameSat`, with the tag read only. -/
def openFrameSat : State :=
  { VG.Proof.AesCcm.X86.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x4000, 4⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x8004, 40⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ccm.openContract X86.abi 2664).pre s := by
  implies_sat [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Spec.Ccm.openPost,
    Spec.Ccm.openLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [openFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.AesCcm.X86.openFrameSat

theorem seal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («seal» v.callee v.suffix))
      (Spec.Ccm.sealContract X86.abi 2664) :=
  X86.Verified.stackScratch (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ccm.sealPre X86.abi.ptrBits) (post := Spec.Ccm.sealPost X86.abi.ptrBits)
    (wa := true) (stack := 56) (bytes := 2608) (VG.Proof.AesCcm.X86.seal_verified v) (by decide) (VG.Proof.AesCcm.X86.seal_noEsp v)
    (VG.Proof.AesCcm.X86.seal_stackUse v) (sealPre_local _) (sealPost_local _) VG.Proof.AesCcm.X86.sealFrameSat_pre

theorem open_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («open» v.callee v.suffix))
      (Spec.Ccm.openContract X86.abi 2664) :=
  X86.Verified.stackScratch (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ccm.openPre X86.abi.ptrBits) (post := Spec.Ccm.openPost X86.abi.ptrBits)
    (wa := true) (stack := 56) (leak := some (Spec.Ccm.openLeak X86.abi.ptrBits)) (bytes := 2608)
    (VG.Proof.AesCcm.X86.open_verified v) (by decide) (VG.Proof.AesCcm.X86.open_noEsp v) (VG.Proof.AesCcm.X86.open_stackUse v) (openPre_local _) (openPost_local _)
    VG.Proof.AesCcm.X86.openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.AesCcm.X86

end
