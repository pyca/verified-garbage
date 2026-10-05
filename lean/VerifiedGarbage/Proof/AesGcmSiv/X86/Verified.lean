import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.AesGcm.X86.Fn
import VerifiedGarbage.Proof.AesGcm.X86.StreamCrypt
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.AesGcmSiv.X86
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.X86.Callee
import VerifiedGarbage.Proof.GcmSiv.Words32
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcmSiv.Scratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Contract`. -/
section

/-!
# AES-GCM-SIV on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The code is proved with its
working space as a ninth argument, `work`, against the shared contracts
with it appended (`Proof/AesGcmSiv/Scratch.lean`), which imply these
(`Verified.lean`); a frame allocates it (`Frame.lean`). The arguments are on
the stack, from `[esp + 4]` (cdecl), and may be overwritten (`writeArgs`);
the calls of `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`, which make
no calls, push their arguments and return addresses in the 28 bytes below
`esp`, which no buffer overlaps, nor the return address.
-/

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.GcmSiv (ctxCiph keyLen encryptWith decryptWith zeros)

/-- The buffers of `vg_aes_gcm_siv_seal(schedule, rounds, nonce, aad, aad_len, data, len, tag, work)`
and `vg_aes_gcm_siv_open`, with the same arguments. -/
abbrev schR (s : State) : Region := ⟨(VG.X86.arg s 0).setWidth 64, 240⟩
abbrev nonceR (s : State) : Region := ⟨(VG.X86.arg s 2).setWidth 64, 12⟩
abbrev aadR (s : State) : Region := ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩
abbrev dataR (s : State) : Region := ⟨(VG.X86.arg s 5).setWidth 64, (VG.X86.arg s 6).toNat⟩
abbrev tagR (s : State) : Region := ⟨(VG.X86.arg s 7).setWidth 64, 16⟩
abbrev workR (s : State) : Region := ⟨(VG.X86.arg s 8).setWidth 64, 2816⟩
abbrev argsR' (s : State) : Region := ⟨argAddr s 0, 36⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev stackR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 28, 28⟩

/-- What both functions' preconditions say of the buffers and the
arguments, but for which may be written. -/
def oneLay (s : State) : Prop :=
  (VG.Proof.AesGcmSiv.X86.schR s).Disjoint (VG.Proof.AesGcmSiv.X86.dataR s) ∧ (VG.Proof.AesGcmSiv.X86.schR s).Disjoint (VG.Proof.AesGcmSiv.X86.workR s) ∧ (VG.Proof.AesGcmSiv.X86.schR s).Disjoint (VG.Proof.AesGcmSiv.X86.argsR' s) ∧
  (VG.Proof.AesGcmSiv.X86.nonceR s).Disjoint (VG.Proof.AesGcmSiv.X86.dataR s) ∧ (VG.Proof.AesGcmSiv.X86.nonceR s).Disjoint (VG.Proof.AesGcmSiv.X86.workR s) ∧ (VG.Proof.AesGcmSiv.X86.nonceR s).Disjoint (VG.Proof.AesGcmSiv.X86.argsR' s) ∧
  (VG.Proof.AesGcmSiv.X86.aadR s).Disjoint (VG.Proof.AesGcmSiv.X86.dataR s) ∧ (VG.Proof.AesGcmSiv.X86.aadR s).Disjoint (VG.Proof.AesGcmSiv.X86.workR s) ∧ (VG.Proof.AesGcmSiv.X86.aadR s).Disjoint (VG.Proof.AesGcmSiv.X86.argsR' s) ∧
  (VG.Proof.AesGcmSiv.X86.dataR s).Disjoint (VG.Proof.AesGcmSiv.X86.tagR s) ∧ (VG.Proof.AesGcmSiv.X86.dataR s).Disjoint (VG.Proof.AesGcmSiv.X86.workR s) ∧ (VG.Proof.AesGcmSiv.X86.dataR s).Disjoint (VG.Proof.AesGcmSiv.X86.argsR' s) ∧
  (VG.Proof.AesGcmSiv.X86.tagR s).Disjoint (VG.Proof.AesGcmSiv.X86.workR s) ∧ (VG.Proof.AesGcmSiv.X86.tagR s).Disjoint (VG.Proof.AesGcmSiv.X86.argsR' s) ∧ (VG.Proof.AesGcmSiv.X86.workR s).Disjoint (VG.Proof.AesGcmSiv.X86.argsR' s) ∧
  (VG.Proof.AesGcmSiv.X86.retR s).Disjoint (VG.Proof.AesGcmSiv.X86.schR s) ∧ (VG.Proof.AesGcmSiv.X86.retR s).Disjoint (VG.Proof.AesGcmSiv.X86.nonceR s) ∧ (VG.Proof.AesGcmSiv.X86.retR s).Disjoint (VG.Proof.AesGcmSiv.X86.aadR s) ∧
  (VG.Proof.AesGcmSiv.X86.retR s).Disjoint (VG.Proof.AesGcmSiv.X86.dataR s) ∧ (VG.Proof.AesGcmSiv.X86.retR s).Disjoint (VG.Proof.AesGcmSiv.X86.tagR s) ∧ (VG.Proof.AesGcmSiv.X86.retR s).Disjoint (VG.Proof.AesGcmSiv.X86.workR s) ∧
  (VG.Proof.AesGcmSiv.X86.retR s).Disjoint (VG.Proof.AesGcmSiv.X86.argsR' s) ∧
  (VG.Proof.AesGcmSiv.X86.stackR s).Disjoint (VG.Proof.AesGcmSiv.X86.schR s) ∧ (VG.Proof.AesGcmSiv.X86.stackR s).Disjoint (VG.Proof.AesGcmSiv.X86.nonceR s) ∧ (VG.Proof.AesGcmSiv.X86.stackR s).Disjoint (VG.Proof.AesGcmSiv.X86.aadR s) ∧
  (VG.Proof.AesGcmSiv.X86.stackR s).Disjoint (VG.Proof.AesGcmSiv.X86.dataR s) ∧ (VG.Proof.AesGcmSiv.X86.stackR s).Disjoint (VG.Proof.AesGcmSiv.X86.tagR s) ∧ (VG.Proof.AesGcmSiv.X86.stackR s).Disjoint (VG.Proof.AesGcmSiv.X86.workR s) ∧
  (VG.Proof.AesGcmSiv.X86.stackR s).Disjoint (VG.Proof.AesGcmSiv.X86.argsR' s) ∧
  (VG.X86.arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + 12 ≤ 2 ^ 32 ∧
  (VG.X86.arg s 3).toNat + (VG.X86.arg s 4).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 5).toNat + (VG.X86.arg s 6).toNat ≤ 2 ^ 32 ∧
  (VG.X86.arg s 7).toNat + 16 ≤ 2 ^ 32 ∧ (VG.X86.arg s 8).toNat + 2816 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 40 ≤ 2 ^ 32 ∧ ((VG.X86.arg s 1).toNat = 10 ∨ (VG.X86.arg s 1).toNat = 14)

/-- `seal` writes the tag. -/
def sealPre (s : State) : Prop :=
  s.rd = [VG.Proof.AesGcmSiv.X86.schR s, VG.Proof.AesGcmSiv.X86.nonceR s, VG.Proof.AesGcmSiv.X86.aadR s] ∧ s.wr = [VG.Proof.AesGcmSiv.X86.dataR s, VG.Proof.AesGcmSiv.X86.tagR s, VG.Proof.AesGcmSiv.X86.workR s, VG.Proof.AesGcmSiv.X86.argsR' s] ∧ VG.Proof.AesGcmSiv.X86.oneLay s

/-- `open` reads it. -/
def openPre (s : State) : Prop :=
  s.rd = [VG.Proof.AesGcmSiv.X86.schR s, VG.Proof.AesGcmSiv.X86.nonceR s, VG.Proof.AesGcmSiv.X86.aadR s, VG.Proof.AesGcmSiv.X86.tagR s] ∧ s.wr = [VG.Proof.AesGcmSiv.X86.dataR s, VG.Proof.AesGcmSiv.X86.workR s, VG.Proof.AesGcmSiv.X86.argsR' s] ∧ VG.Proof.AesGcmSiv.X86.oneLay s

/-- All nine stack arguments are public, and the stack pointer. -/
def onePub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 9, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `vg_aes_gcm_siv_seal`. -/
def sealX86 : Contract isa where
  pre := VG.Proof.AesGcmSiv.X86.sealPre
  post s s' :=
    VG.Spec.GcmSiv.encryptWith (VG.Spec.GcmSiv.ctxCiph s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat) (VG.Spec.GcmSiv.keyLen (VG.X86.arg s 1).toNat)
        (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) 12) (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 5).setWidth 64) (VG.X86.arg s 6).toNat)
        (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 3).setWidth 64) (VG.X86.arg s 4).toNat) =
      (VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 5).setWidth 64) (VG.X86.arg s 6).toNat, VG.Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 7).setWidth 64) 16)
  pub := VG.Proof.AesGcmSiv.X86.onePub

/-- What `vg_aes_gcm_siv_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  VG.Spec.GcmSiv.decryptWith (VG.Spec.GcmSiv.ctxCiph s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat) (VG.Spec.GcmSiv.keyLen (VG.X86.arg s 1).toNat)
    (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) 12) (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 5).setWidth 64) (VG.X86.arg s 6).toNat)
    (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 3).setWidth 64) (VG.X86.arg s 4).toNat) (VG.Spec.Aes.bytesAt s.mem ((VG.X86.arg s 7).setWidth 64) 16)

/-- What `vg_aes_gcm_siv_open` leaves in `eax` and in the `n` bytes of data
at `D`, for the result `r`. Irreducible, so that checking a state against
it never evaluates `r`. -/
@[irreducible] def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => s'.gpr .eax = 1 ∧ VG.Spec.Aes.bytesAt s'.mem D n = pt
  | none => s'.gpr .eax = 0 ∧ VG.Spec.Aes.bytesAt s'.mem D n = VG.Spec.GcmSiv.zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : s'.gpr .eax = 1) (hd : VG.Spec.Aes.bytesAt s'.mem D n = pt) : VG.Proof.AesGcmSiv.X86.openPost r s' D n := by
  subst hr; unfold VG.Proof.AesGcmSiv.X86.openPost; exact ⟨hax, hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : s'.gpr .eax = 0) (hd : VG.Spec.Aes.bytesAt s'.mem D n = VG.Spec.GcmSiv.zeros n) : VG.Proof.AesGcmSiv.X86.openPost r s' D n := by
  subst hr; unfold VG.Proof.AesGcmSiv.X86.openPost; exact ⟨hax, hd⟩

/-- `vg_aes_gcm_siv_open`. It does not branch on whether the tag is right,
so its runs are related without the leak the shared contract allows. -/
def openX86 : Contract isa where
  pre := VG.Proof.AesGcmSiv.X86.openPre
  post s s' := VG.Proof.AesGcmSiv.X86.openPost (VG.Proof.AesGcmSiv.X86.openResult s) s' ((VG.X86.arg s 5).setWidth 64) (VG.X86.arg s 6).toNat
  pub := VG.Proof.AesGcmSiv.X86.onePub

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Env`. -/
section

/-!
# AES-GCM-SIV on x86: where everything is

Untrusted: everything here is checked by Lean. The public arguments
(`Prm`): the key schedule of the key-generating key (240 bytes at `K`), the
working space (2816 bytes at `W`), the nonce (12 bytes at `N`), the
additional data (`al` bytes at `A`), the data (`n` bytes at `D`), the tag
(16 bytes at `T`), the stack
pointer and the number of rounds, all 32-bit; how their regions lie, apart
from each other and from the 28 bytes below `SP` that the calls use
(`Lay`); what a state may access (`Perm`); and `W` in `ebp`, the stack
pointer, and the arguments the entry keeps in `W` (`Env`). The pieces
write only the parts of `W` in `mutR` (and the data, and the stack below
`SP`), so they keep the slots and our caller's registers saved in `W`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

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
  /-- The key schedule of the key-generating key. -/
  K : BitVec 32
  /-- The working space. -/
  W : BitVec 32
  /-- The nonce. -/
  N : BitVec 32
  /-- The additional data. -/
  A : BitVec 32
  /-- The data. -/
  D : BitVec 32
  /-- The tag. -/
  T : BitVec 32
  /-- The stack pointer. -/
  SP : BitVec 32
  /-- The number of rounds. -/
  R : Nat
  /-- The length of the additional data. -/
  al : Nat
  /-- The length of the data. -/
  n : Nat

/-- The stack the calls use. -/
abbrev stk (p : VG.Proof.AesGcmSiv.X86.Prm) : Region := below p.SP 28

/-- How the regions lie. -/
structure Lay (p : VG.Proof.AesGcmSiv.X86.Prm) : Prop where
  kw : p.K.toNat + 240 ≤ 2 ^ 32
  ww : p.W.toNat + 2816 ≤ 2 ^ 32
  nw : p.N.toNat + 12 ≤ 2 ^ 32
  aw : p.A.toNat + p.al ≤ 2 ^ 32
  dw : p.D.toNat + p.n ≤ 2 ^ 32
  tw : p.T.toNat + 16 ≤ 2 ^ 32
  sp : 28 ≤ p.SP.toNat
  k_w : (⟨w64 p.K, 240⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩
  k_d : (⟨w64 p.K, 240⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  n_w : (⟨w64 p.N, 12⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩
  n_d : (⟨w64 p.N, 12⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  a_w : (⟨w64 p.A, p.al⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩
  a_d : (⟨w64 p.A, p.al⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  d_w : (⟨w64 p.D, p.n⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩
  t_w : (⟨w64 p.T, 16⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩
  t_d : (⟨w64 p.T, 16⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  bk : (VG.Proof.AesGcmSiv.X86.stk p).Disjoint ⟨w64 p.K, 240⟩
  bn : (VG.Proof.AesGcmSiv.X86.stk p).Disjoint ⟨w64 p.N, 12⟩
  ba : (VG.Proof.AesGcmSiv.X86.stk p).Disjoint ⟨w64 p.A, p.al⟩
  bd : (VG.Proof.AesGcmSiv.X86.stk p).Disjoint ⟨w64 p.D, p.n⟩
  bw : (VG.Proof.AesGcmSiv.X86.stk p).Disjoint ⟨w64 p.W, 2816⟩
  bt : (VG.Proof.AesGcmSiv.X86.stk p).Disjoint ⟨w64 p.T, 16⟩
  rounds : p.R = 10 ∨ p.R = 14
  al32 : p.al < 2 ^ 32
  n32 : p.n < 2 ^ 32
  retW : (⟨w64 p.SP, 4⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩
  retD : (⟨w64 p.SP, 4⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  retT : (⟨w64 p.SP, 4⟩ : Region).Disjoint ⟨w64 p.T, 16⟩

/-- What a state may access. -/
structure Perm (p : VG.Proof.AesGcmSiv.X86.Prm) (s : State) : Prop where
  k : Covers [⟨w64 p.K, 240⟩] (s.rd ++ s.wr)
  non : Covers [⟨w64 p.N, 12⟩] (s.rd ++ s.wr)
  aad : Covers [⟨w64 p.A, p.al⟩] (s.rd ++ s.wr)
  d : Covers [⟨w64 p.D, p.n⟩] s.wr
  w : Covers [⟨w64 p.W, 2816⟩] s.wr
  t : Covers [⟨w64 p.T, 16⟩] (s.rd ++ s.wr)

theorem Perm.of_eq {p : VG.Proof.AesGcmSiv.X86.Prm} {s s' : State} (h : VG.Proof.AesGcmSiv.X86.Perm p s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesGcmSiv.X86.Perm p s' := by
  obtain ⟨a, b, c, d, e, f⟩ := h
  exact ⟨by rw [hrd, hwr]; exact a, by rw [hrd, hwr]; exact b, by rw [hrd, hwr]; exact c, by rw [hwr]; exact d,
    by rw [hwr]; exact e, by rw [hrd, hwr]; exact f⟩

/-- The public values the entry keeps in `W`: all the arguments but `work`. -/
structure Slots (p : VG.Proof.AesGcmSiv.X86.Prm) (m : Mem) : Prop where
  ctx : slotv m p.W Impl.AesGcmSiv.X86.ctxO = p.K
  rounds : slotv m p.W Impl.AesGcmSiv.X86.roundsO = BitVec.ofNat 32 p.R
  nonce : slotv m p.W Impl.AesGcmSiv.X86.nonceO = p.N
  aad : slotv m p.W Impl.AesGcmSiv.X86.aadO = p.A
  alen : slotv m p.W Impl.AesGcmSiv.X86.alenO = BitVec.ofNat 32 p.al
  data : slotv m p.W Impl.AesGcmSiv.X86.dataO = p.D
  len : slotv m p.W Impl.AesGcmSiv.X86.lenO = BitVec.ofNat 32 p.n
  tp : slotv m p.W Impl.AesGcmSiv.X86.tpO = p.T

/-- `W` in `ebp`, the stack pointer, what the state may access, and the
slots. -/
structure Env (p : VG.Proof.AesGcmSiv.X86.Prm) (s : State) : Prop where
  ebp : s.gpr .ebp = p.W
  esp : s.gpr .esp = p.SP
  perm : VG.Proof.AesGcmSiv.X86.Perm p s
  slots : VG.Proof.AesGcmSiv.X86.Slots p s.mem

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2816) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2816⟩ :=
  Offset.sub_base _ h

/-- Parts of `W` are disjoint. -/
theorem w_w {W : BitVec 32} {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2816) (hd : d + k ≤ 2816) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

variable {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p)
include L

/-- An offset into `W`, as a 64-bit address. -/
theorem aW {o : Nat} (ho : o < 2816) : w64 (p.W + BitVec.ofNat 32 o) = w64 p.W + BitVec.ofNat 64 o :=
  w64_add (by have := L.ww; omega)

theorem nW {o : Nat} (ho : o < 2816) : (p.W + BitVec.ofNat 32 o).toNat = p.W.toNat + o :=
  toNat_add32 (by have := L.ww; omega)

/-- An offset into the nonce. -/
theorem aN {o : Nat} (ho : o < 12) : w64 (p.N + BitVec.ofNat 32 o) = w64 p.N + BitVec.ofNat 64 o :=
  w64_add (by have := L.nw; omega)

theorem k_w' {d k : Nat} (hd : d + k ≤ 2816) : (⟨w64 p.K, 240⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (VG.Proof.AesGcmSiv.X86.Lay.wSub hd)

theorem n_w' {d k : Nat} (hd : d + k ≤ 2816) : (⟨w64 p.N, 12⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.n_w.sub_right (VG.Proof.AesGcmSiv.X86.Lay.wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 2816) :
    (⟨w64 p.A, p.al⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (VG.Proof.AesGcmSiv.X86.Lay.wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 2816) :
    (⟨w64 p.D, p.n⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (VG.Proof.AesGcmSiv.X86.Lay.wSub hd)

theorem bw' {d k : Nat} (hd : d + k ≤ 2816) : (VG.Proof.AesGcmSiv.X86.stk p).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.bw.sub_right (VG.Proof.AesGcmSiv.X86.Lay.wSub hd)

/-- The stack below `SP` that a call uses, within the 28 bytes. -/
theorem stkSub {k : Nat} (hk : k ≤ 28) : Region.Sub (below p.SP k) (VG.Proof.AesGcmSiv.X86.stk p) := VG.X86.below_sub hk L.sp

theorem rounds_le : 16 * (p.R + 1) ≤ 240 := by rcases L.rounds with h | h <;> rw [h] <;> decide

theorem rounds3 : p.R = 10 ∨ p.R = 12 ∨ p.R = 14 := by rcases L.rounds with h | h <;> simp [h]

theorem toNat_R : (BitVec.ofNat 32 p.R).toNat = p.R := by
  rcases L.rounds with h | h <;> rw [h] <;> rfl

theorem R_lt : p.R < 2 ^ 32 := by rcases L.rounds with h | h <;> rw [h] <;> decide

end Lay

namespace Perm

variable {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} (P : VG.Proof.AesGcmSiv.X86.Perm p s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 2816) : InRegions s.wr (w64 p.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2816) : InRegions (s.rd ++ s.wr) (w64 p.W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 2816) : Covers [⟨w64 p.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 2816) : Covers [⟨w64 p.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_left (P.wC h)

/-- The first 2560 bytes of `W`, where AES-GCM's save area is. -/
theorem w2560 : Covers [⟨w64 p.W, 2560⟩] s.wr := VG.Proof.AesGcmSiv.X86.covers_prefix P.w (by decide)

theorem nR {d k : Nat} (h : d + k ≤ 12) : InRegions (s.rd ++ s.wr) (w64 p.N + BitVec.ofNat 64 d) k :=
  in_off P.non h (by decide)

end Perm

/-! ## What the pieces write -/

/-- The parts of `W` the pieces write: the blocks at `[0, 128)`, the
variables at `[176, 184)`, the blocks at `[224, 256)`, and from `512` on. -/
abbrev wA (W : BitVec 32) : Region := ⟨w64 W, 128⟩
abbrev wV (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 176, 8⟩
abbrev wB (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 224, 32⟩
abbrev wC (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 512, 2304⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (p : VG.Proof.AesGcmSiv.X86.Prm) : List Region := [VG.Proof.AesGcmSiv.X86.wA p.W, VG.Proof.AesGcmSiv.X86.wV p.W, VG.Proof.AesGcmSiv.X86.wB p.W, VG.Proof.AesGcmSiv.X86.wC p.W, VG.Proof.AesGcmSiv.X86.stk p, ⟨w64 p.D, p.n⟩]

/-- The regions `rs` are within `mutR`. -/
abbrev InMut (p : VG.Proof.AesGcmSiv.X86.Prm) (rs : List Region) : Prop := ∀ r ∈ rs, ∃ r' ∈ VG.Proof.AesGcmSiv.X86.mutR p, Region.Sub r r'

theorem frame_toMut {p : VG.Proof.AesGcmSiv.X86.Prm} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (h : VG.Proof.AesGcmSiv.X86.InMut p rs) :
    Frame (VG.Proof.AesGcmSiv.X86.mutR p) m m' := hf.sub h

/-- A part of `W` in `wA`, `wV`, `wB` or `wC`. -/
theorem inMut_w (p : VG.Proof.AesGcmSiv.X86.Prm) {d k : Nat}
    (h : d + k ≤ 128 ∨ 176 ≤ d ∧ d + k ≤ 184 ∨ 224 ≤ d ∧ d + k ≤ 256 ∨ 512 ≤ d ∧ d + k ≤ 2816) :
    ∃ r' ∈ VG.Proof.AesGcmSiv.X86.mutR p, Region.Sub ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with h | h | h | h
  · exact ⟨VG.Proof.AesGcmSiv.X86.wA p.W, by simp, Offset.sub_base _ h⟩
  · exact ⟨VG.Proof.AesGcmSiv.X86.wV p.W, by simp, Offset.sub _ (by omega) (by omega)⟩
  · exact ⟨VG.Proof.AesGcmSiv.X86.wB p.W, by simp, Offset.sub _ (by omega) (by omega)⟩
  · exact ⟨VG.Proof.AesGcmSiv.X86.wC p.W, by simp, Offset.sub _ (by omega) (by omega)⟩

theorem inMut_stk (p : VG.Proof.AesGcmSiv.X86.Prm) : ∃ r' ∈ VG.Proof.AesGcmSiv.X86.mutR p, Region.Sub (VG.Proof.AesGcmSiv.X86.stk p) r' := ⟨VG.Proof.AesGcmSiv.X86.stk p, by simp, fun _ h => h⟩

theorem inMut_d (p : VG.Proof.AesGcmSiv.X86.Prm) : ∃ r' ∈ VG.Proof.AesGcmSiv.X86.mutR p, Region.Sub ⟨w64 p.D, p.n⟩ r' := ⟨_, by simp, fun _ h => h⟩

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {d k : Nat} (hd : 128 ≤ d ∧ d + k ≤ 176) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86.mutR p, (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Lay.w_w (W := p.W) (a := d) (n := k) (d := 0) (k := 128) (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.bw' (by omega)).symm
  · exact (L.d_w' (by omega)).symm

/-- The slots, after code that changes only `mutR`. -/
theorem Slots.mut {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.X86.mutR p) m m') (S : VG.Proof.AesGcmSiv.X86.Slots p m) : VG.Proof.AesGcmSiv.X86.Slots p m' := by
  have k : ∀ o, 128 ≤ o ∧ o + 4 ≤ 176 → slotv m' p.W o = slotv m p.W o := fun o ho =>
    hf.readW (r := ⟨w64 p.W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (VG.Proof.AesGcmSiv.X86.kept_mut L ho) (by decide)
  exact ⟨by rw [k _ (by decide)]; exact S.ctx, by rw [k _ (by decide)]; exact S.rounds,
    by rw [k _ (by decide)]; exact S.nonce, by rw [k _ (by decide)]; exact S.aad,
    by rw [k _ (by decide)]; exact S.alen, by rw [k _ (by decide)]; exact S.data,
    by rw [k _ (by decide)]; exact S.len, by rw [k _ (by decide)]; exact S.tp⟩

/-- Our caller's registers saved at `W + 128`, after code that changes only
`mutR`. -/
theorem SavedAt.mut {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.X86.mutR p) m m') {s₀ : State}
    (h : Proof.AesGcm.X86.SavedAt m p.W s₀) : Proof.AesGcm.X86.SavedAt m' p.W s₀ :=
  h.frame hf (VG.Proof.AesGcmSiv.X86.kept_mut L (by decide))

/-- An environment, after code that keeps `ebp`, `esp` and the permissions,
and changes only `mutR`. -/
theorem Env.mut {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {s s' : State} (h : VG.Proof.AesGcmSiv.X86.Env p s) (hbp : s'.gpr .ebp = p.W)
    (hsp : s'.gpr .esp = p.SP) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame (VG.Proof.AesGcmSiv.X86.mutR p) s.mem s'.mem) :
    VG.Proof.AesGcmSiv.X86.Env p s' :=
  ⟨hbp, hsp, h.perm.of_eq hrd hwr, h.slots.mut L hf⟩

/-- An environment, after code that keeps `ebp`, `esp`, the permissions and
the memory. -/
theorem Env.keep {p : VG.Proof.AesGcmSiv.X86.Prm} {s s' : State} (h : VG.Proof.AesGcmSiv.X86.Env p s) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hm : s'.mem = s.mem) : VG.Proof.AesGcmSiv.X86.Env p s' :=
  ⟨by rw [hbp, h.ebp], by rw [hsp, h.esp], h.perm.of_eq hrd hwr, by rw [hm]; exact h.slots⟩

/-- The return address, after code that changes only `mutR`. -/
theorem ret_mut {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.X86.mutR p) m m') :
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
theorem bytes_mut {p : VG.Proof.AesGcmSiv.X86.Prm} {P : BitVec 32} {len : Nat}
    (hw : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩) (hb : (VG.Proof.AesGcmSiv.X86.stk p).Disjoint ⟨w64 P, len⟩)
    (hd : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩) (hl : len ≤ 2 ^ 64) {m m' : Mem}
    (hf : Frame (VG.Proof.AesGcmSiv.X86.mutR p) m m') : bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hw.sub_right (Region.sub_prefix (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hb.symm
    · exact hd) hl

theorem ciph_mut {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.X86.mutR p) m m') :
    Spec.GcmSiv.ctxCiph m' (w64 p.K) p.R = Spec.GcmSiv.ctxCiph m (w64 p.K) p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [VG.Proof.AesGcmSiv.X86.bytes_mut (L.k_w.sub_left (Region.sub_prefix L.rounds_le)) (L.bk.sub_right (Region.sub_prefix L.rounds_le))
    (L.k_d.sub_left (Region.sub_prefix L.rounds_le)) (by have := L.rounds_le; omega) hf]

theorem nonce_mut {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.X86.mutR p) m m') :
    bytesAt m' (w64 p.N) 12 = bytesAt m (w64 p.N) 12 := VG.Proof.AesGcmSiv.X86.bytes_mut L.n_w L.bn L.n_d (by decide) hf

theorem aad_mut {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.X86.mutR p) m m') :
    bytesAt m' (w64 p.A) p.al = bytesAt m (w64 p.A) p.al :=
  VG.Proof.AesGcmSiv.X86.bytes_mut L.a_w L.ba L.a_d (by have := L.aw; omega) hf

/-! ## Arithmetic -/

theorem ofNat_lsr32 {a : Nat} (ha : a < 2 ^ 32) (k : Nat) : BitVec.ofNat 32 a >>> k = BitVec.ofNat 32 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by have := Nat.div_le_self a (2 ^ k); omega)]

/-- `x + x` is `x << 1`. -/
theorem add_self32 (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  congr 1; omega

/-- Three doublings are a shift by 3. -/
theorem add_self32_3 (x : BitVec 32) : (x + x + (x + x)) + (x + x + (x + x)) = x <<< 3 := by
  rw [VG.Proof.AesGcmSiv.X86.add_self32, VG.Proof.AesGcmSiv.X86.add_self32, VG.Proof.AesGcmSiv.X86.add_self32, ← BitVec.shiftLeft_add, ← BitVec.shiftLeft_add]

/-- `ror (x & 1), 1` is `x << 31`. -/
theorem ror_and1 (x : BitVec 32) : (x &&& 1#32).rotateRight 1 = x <<< 31 := by
  have h1 : ∀ j < 32, (1#32 : BitVec 32).getLsbD j = decide (j = 0) := by decide
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and]
  by_cases h : i < 31
  · simp only [show i < 32 - 1 % 32 from by omega, ↓reduceIte, h1 _ (show 1 % 32 + i < 32 by omega),
      show ¬ (1 % 32 + i = 0) by omega, decide_false, Bool.and_false, show i < 31 from h, decide_true,
      Bool.not_true, Bool.and_false, Bool.false_and]
  · have hi31 : i = 31 := by omega
    subst hi31
    simp only [show ¬ (31 < 32 - 1 % 32) from by decide, ↓reduceIte, h1 _ (by decide : (31 - (32 - 1 % 32)) < 32)]
    simp

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Run`. -/
section

/-!
# AES-GCM-SIV on x86: running straight-line blocks

Untrusted: everything here is checked by Lean. `grun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`,
keeping the registers folded), as AES-GCM's `xrun` does, with the offsets
of the AES-GCM-SIV code; `gregs` and `gmems` read registers, memory, flags
and permissions through the writes of a block.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
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

/-- Runs a block of the instructions the AES-GCM-SIV code uses. The facts
given rewrite the addresses and discharge the permissions. -/
macro "grun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, execAlu, execShift, State.load32, store32_eq, State.load8, store8_eq,
    State.ea, at_, imm, slot, argOp, tagO, akO, ekO, hO, yO, cbO, ccO, ctxO, roundsO, nonceO, aadO, alenO,
    dataO, lenO, nO, iO, bO, t2O, skO, revO, ghO, scrO, List.cons_append, List.nil_append, List.append_assoc,
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
    tagO, akO, ekO, hO, yO, cbO, ccO, ctxO, roundsO, nonceO, aadO, alenO, dataO, lenO, nO, iO, bO, t2O, skO,
    revO, ghO, scrO, Nat.reduceAdd, Reg8.reg, eq_self_iff_true, and_self, $ts,*]))

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

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Entry`. -/
section

/-!
# AES-GCM-SIV on x86: the arguments and the entry

Untrusted: everything here is checked by Lean. The precondition `onePre`
gives the public arguments (`prmOf`), how they lie (`lay_of`) and what the
state may access (`perm_of`). The entry saves our caller's registers in `W`
(AES-GCM's `save_ok`) and copies the stack arguments into their slots
(`keeps_ok`): after it, `Env` holds (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt)
open VG.Proof.AesGcm.X86 (w64 slotv argA argsR argsR_eq argA_contains argA_sub SavedAt save_ok KeepEnv keeps_ok
  keepR runBlock_app_of in_off below_eq covers_left)

/-- What both preconditions say: the layout, and that the buffers may be
read (the key schedule, the nonce, the additional data and the tag) or
written (the data, `work` and the arguments). -/
structure onePre (s : State) : Prop where
  lay : VG.Proof.AesGcmSiv.X86.oneLay s
  rd : ∀ r ∈ [VG.Proof.AesGcmSiv.X86.schR s, VG.Proof.AesGcmSiv.X86.nonceR s, VG.Proof.AesGcmSiv.X86.aadR s, VG.Proof.AesGcmSiv.X86.tagR s], Covers [r] (s.rd ++ s.wr)
  wr : ∀ r ∈ [VG.Proof.AesGcmSiv.X86.dataR s, VG.Proof.AesGcmSiv.X86.workR s, VG.Proof.AesGcmSiv.X86.argsR' s], Covers [r] s.wr

theorem onePre_seal {s : State} (h : VG.Proof.AesGcmSiv.X86.sealPre s) : VG.Proof.AesGcmSiv.X86.onePre s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  refine ⟨hl, fun r hr => ?_, fun r hr => ?_⟩
  swap
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact VG.Proof.AesGcmSiv.X86.covers_of_mem (by rw [hwr]; simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcmSiv.X86.covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · exact VG.Proof.AesGcmSiv.X86.covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · exact VG.Proof.AesGcmSiv.X86.covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · exact VG.Proof.AesGcmSiv.X86.covers_of_mem (List.mem_append_right _ (by rw [hwr]; simp))

theorem onePre_open {s : State} (h : VG.Proof.AesGcmSiv.X86.openPre s) : VG.Proof.AesGcmSiv.X86.onePre s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  refine ⟨hl, fun r hr => VG.Proof.AesGcmSiv.X86.covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr)),
    fun r hr => VG.Proof.AesGcmSiv.X86.covers_of_mem (by rw [hwr]; exact hr)⟩

/-- The public arguments of a state. -/
def prmOf (s : State) : VG.Proof.AesGcmSiv.X86.Prm where
  K := arg s 0
  W := arg s 8
  N := arg s 2
  A := arg s 3
  D := arg s 5
  T := arg s 7
  SP := s.gpr .esp
  R := (arg s 1).toNat
  al := (arg s 4).toNat
  n := (arg s 6).toNat

/-- What the precondition says of the stack arguments. -/
structure ArgsOk (s : State) : Prop where
  rA : Covers [argsR (s.gpr .esp) 9] (s.rd ++ s.wr)
  aw : (argsR (s.gpr .esp) 9).Disjoint ⟨w64 (arg s 8), 2816⟩
  fa : (s.gpr .esp).toNat + 4 + 4 * 9 ≤ 2 ^ 32

theorem lay_of {s : State} (h : VG.Proof.AesGcmSiv.X86.onePre s) : VG.Proof.AesGcmSiv.X86.Lay (VG.Proof.AesGcmSiv.X86.prmOf s) := by
  obtain ⟨sd, sw, _, nd, nw, _, ad, aw, _, dt, dw, _, tw, _, _, _, _, _, rd, rt, rw, _, bs, bn, ba, bd, bt, bw, _,
    fK, fN, fA, fD, fT, fW, sp28, _, hR⟩ := h.lay
  simp only [VG.Proof.AesGcmSiv.X86.stackR] at bs bn ba bd bt bw
  rw [show (28 : Addr) = BitVec.ofNat 64 28 from rfl, below_eq sp28] at bs bn ba bd bt bw
  exact ⟨fK, fW, fN, fA, fD, fT, sp28, sw, sd, nw, nd, aw, ad, dw, tw, dt.symm, bs, bn, ba, bd, bw, bt, hR,
    BitVec.isLt _, BitVec.isLt _, rw, rd, rt⟩

theorem perm_of {s : State} (h : VG.Proof.AesGcmSiv.X86.onePre s) : VG.Proof.AesGcmSiv.X86.Perm (VG.Proof.AesGcmSiv.X86.prmOf s) s :=
  ⟨h.rd (VG.Proof.AesGcmSiv.X86.schR s) (by simp), h.rd (VG.Proof.AesGcmSiv.X86.nonceR s) (by simp), h.rd (VG.Proof.AesGcmSiv.X86.aadR s) (by simp), h.wr (VG.Proof.AesGcmSiv.X86.dataR s) (by simp),
    h.wr (VG.Proof.AesGcmSiv.X86.workR s) (by simp), h.rd (VG.Proof.AesGcmSiv.X86.tagR s) (by simp)⟩

theorem argsOk_of {s : State} (h : VG.Proof.AesGcmSiv.X86.onePre s) : VG.Proof.AesGcmSiv.X86.ArgsOk s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, wa, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, spf, -⟩ := h.lay
  refine ⟨?_, ?_, by omega⟩
  · rw [argsR_eq]; exact covers_left (h.wr (VG.Proof.AesGcmSiv.X86.argsR' s) (by simp))
  · rw [argsR_eq]; exact wa.symm

/-- The arguments the entry copies, and where. -/
abbrev entryPs : List (Nat × Nat) :=
  [(0, ctxO), (1, roundsO), (2, nonceO), (3, aadO), (4, alenO), (5, dataO), (6, lenO), (7, tpO)]

theorem sivEntry_eq : sivEntry = entry 8 (entryPs.flatMap (fun p => VG.Impl.AesGcm.X86.keep p.1 p.2)) := rfl

/-- What the entry leaves. -/
structure Entered (s : State) (p : VG.Proof.AesGcmSiv.X86.Prm) (s' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p s'
  saved : SavedAt s'.mem p.W s
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 128, 48⟩] s.mem s'.mem

/-- The entry. -/
theorem entry_ok {s : State} (h : VG.Proof.AesGcmSiv.X86.onePre s) : WP isa sivEntry s (VG.Proof.AesGcmSiv.X86.Entered s (VG.Proof.AesGcmSiv.X86.prmOf s)) := by
  have L := VG.Proof.AesGcmSiv.X86.lay_of h
  have P := VG.Proof.AesGcmSiv.X86.perm_of h
  have Ao := VG.Proof.AesGcmSiv.X86.argsOk_of h
  rw [VG.Proof.AesGcmSiv.X86.sivEntry_eq]
  generalize hSP : s.gpr .esp = SP at Ao
  have rA := Ao.rA
  have aw := Ao.aw
  have fa := Ao.fa
  rw [hSP] at rA aw fa
  have fw : (arg s 8).toNat + 2560 ≤ 2 ^ 32 := by have := L.ww; simp only [VG.Proof.AesGcmSiv.X86.prmOf] at this; omega
  have wW : Covers [⟨w64 (arg s 8), 2560⟩] s.wr := P.w2560
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 8) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.seq (WP.of_runBlock ⟨_, by grun [hSP, i₀], ?_⟩)
  have hax : (s.setReg .eax (s.mem.readW (argA SP 8) 32)).gpr .eax = arg s 8 := by
    rw [gpr_setReg_self, ← hSP]; rfl
  set s₀ := s.setReg .eax (s.mem.readW (argA SP 8) 32) with hs₀
  obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := save_ok s₀ hax (by rw [hs₀]; exact wW) fw
  have sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide), hSP]
  have argW : ∀ {i}, i < 9 → ∀ {d k : Nat}, d + k ≤ 2816 →
      ∀ r ∈ [(⟨w64 (arg s 8) + BitVec.ofNat 64 d, k⟩ : Region)], (⟨argA SP i, 4⟩ : Region).Disjoint r :=
    fun hi _ _ hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (aw.sub_left (argA_sub hi fa)).sub_right (Lay.wSub hk)
  have hA₁ : ∀ i < 9, s₁.mem.readW (argA SP i) 32 = arg s i := fun i hi => by
    rw [f₁.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (argW hi (by decide)) (by decide)]
    rw [arg, argAddr, hSP]
    exact rfl
  have aw' : (argsR SP 9).Disjoint ⟨w64 (arg s 8), 2560⟩ := aw.sub_right (Region.sub_prefix (by decide))
  have ke : KeepEnv (arg s 8) SP 9 s₁ := ⟨bp₁, sp₁, by rw [wr₁]; exact wW, by rw [rd₁, wr₁]; exact rA, aw', fa, fw⟩
  obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := keeps_ok VG.Proof.AesGcmSiv.X86.entryPs (fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) ke
  have bp₃ : s₃.gpr .ebp = arg s 8 := by rw [g₃ _ (by decide), bp₁]
  have sp₃ : s₃.gpr .esp = SP := by rw [g₃ _ (by decide), sp₁]
  refine WP.of_runBlock ⟨_, runBlock_app_of run₁ run₃, ?_⟩
  -- What the entry wrote.
  have f₃' : Frame [⟨w64 (arg s 8) + BitVec.ofNat 64 128, 48⟩] s.mem s₃.mem := by
    refine (f₁.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hsv : SavedAt s₃.mem (arg s 8) s := by
    have := sv₁.frame f₃ fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    obtain ⟨a, b, c, d⟩ := this
    refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_⟩ <;>
      simp only [hs₀, gpr_setReg_of_ne _ _ (by decide : Reg.ebx ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.esi ≠ .eax),
        gpr_setReg_of_ne _ _ (by decide : Reg.edi ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.ebp ≠ .eax)]
  have sl : ∀ q ∈ VG.Proof.AesGcmSiv.X86.entryPs, slotv s₃.mem (arg s 8) q.2 = arg s q.1 := fun q hq => by
    have e := sl₃ q hq
    have hq1 : q.1 < 9 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hA₁ q.1 hq1] at e
    exact e
  have ofN : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => BitVec.eq_of_toNat_eq (by simp)
  refine ⟨⟨bp₃, by rw [sp₃, ← hSP]; rfl, P.of_eq (by rw [rd₃, rd₁]; rfl) (by rw [wr₃, wr₁]; rfl),
    ⟨sl (0, ctxO) (by simp), by simp only [VG.Proof.AesGcmSiv.X86.prmOf]; rw [sl (1, roundsO) (by simp)]; exact (ofN _).symm,
      sl (2, nonceO) (by simp), sl (3, aadO) (by simp),
      by simp only [VG.Proof.AesGcmSiv.X86.prmOf]; rw [sl (4, alenO) (by simp)]; exact (ofN _).symm, sl (5, dataO) (by simp),
      by simp only [VG.Proof.AesGcmSiv.X86.prmOf]; rw [sl (6, lenO) (by simp)]; exact (ofN _).symm, sl (7, tpO) (by simp)⟩⟩, hsv, by rw [rd₃, rd₁]; rfl, by rw [wr₃, wr₁]; rfl, f₃'⟩

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Callee`. -/
section

/-!
# AES-GCM-SIV on x86: the functions called

Untrusted: everything here is checked by Lean. The calls of `vg_aes_ctr32`,
`vg_ghash` and `vg_aes_expand_key` are AES-GCM's (`Proof.AesGcm.X86`'s
`ctr_call`, `gh_call`, `key_call`), with `ebp` moved to the callee's working
space around them (`callCtr_ok`, `callGh_ok`, `callKey_ok`). Their arguments
are built from the environment:

* `vg_aes_ctr32`: a key schedule (`KeyOk`: the key-generating key's, or the
  encryption key's at `W + 512`), the counter block's copy at `W + 112`,
  `n` blocks at `D` (`Dst`), and the working space at `W + 768`;
* `vg_ghash`: GHASH's key at `W + 64`, the accumulator at `W + 80`, `n` (at
  most 64) reversed blocks at `W + 768` and the working space at
  `W + 1792`;
* `vg_aes_expand_key`: the encryption key at `W + 32`, its schedule at
  `W + 512` and the working space at `W + 768`.

Each call writes only parts of `mutR`, so `Env` holds after it.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt blocksAt ctr32 aesWith ghashFrom)
open VG.Impl.AesGcm.X86 (imm)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_left covers_cons covers_nil CtrCall CtrPost
  GhCall GhPost KeyCall KeyPost GcmImpl gpr_setMem CT)

/-! ## `vg_aes_ctr32` -/

/-- A key schedule of 240 bytes at `Q`, which the code may read, apart from
the counter block's copy at `W + 112`, the working space at `W + 768` and
the stack the calls use. -/
structure KeyOk (p : VG.Proof.AesGcmSiv.X86.Prm) (s : State) (Q : BitVec 32) : Prop where
  rd : Covers [⟨w64 Q, 240⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + 240 ≤ 2 ^ 32
  kc : (⟨w64 Q, 240⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 112, 16⟩
  ks : (⟨w64 Q, 240⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩
  stk : (VG.Proof.AesGcmSiv.X86.stk p).Disjoint ⟨w64 Q, 240⟩

theorem KeyOk.of_eq {p : VG.Proof.AesGcmSiv.X86.Prm} {s s' : State} {Q : BitVec 32} (h : VG.Proof.AesGcmSiv.X86.KeyOk p s Q) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcmSiv.X86.KeyOk p s' Q :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The key-generating key's schedule. -/
theorem keyK {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} (L : VG.Proof.AesGcmSiv.X86.Lay p) (P : VG.Proof.AesGcmSiv.X86.Perm p s) : VG.Proof.AesGcmSiv.X86.KeyOk p s p.K :=
  ⟨P.k, L.kw, L.k_w' (by decide), L.k_w' (by decide), L.bk⟩

/-- The encryption key's schedule at `W + 512`. -/
theorem keyS {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} (L : VG.Proof.AesGcmSiv.X86.Lay p) (P : VG.Proof.AesGcmSiv.X86.Perm p s) : VG.Proof.AesGcmSiv.X86.KeyOk p s (p.W + BitVec.ofNat 32 512) where
  rd := by rw [L.aW (by decide)]; exact P.wCR (by decide)
  wrap := by rw [L.nW (by decide)]; have := L.ww; omega
  kc := by rw [L.aW (by decide)]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  ks := by rw [L.aW (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  stk := by rw [L.aW (by decide)]; exact L.bw' (by decide)

/-- `k` bytes at `D` that `vg_aes_ctr32` may write: apart from the key
schedule at `Q`, the counter block's copy, the working space and the stack
the calls use. -/
structure Dst (p : VG.Proof.AesGcmSiv.X86.Prm) (s : State) (Q D : BitVec 32) (k : Nat) : Prop where
  wr : Covers [⟨w64 D, k⟩] s.wr
  wrap : D.toNat + k ≤ 2 ^ 32
  dk : (⟨w64 Q, 240⟩ : Region).Disjoint ⟨w64 D, k⟩
  dc : (⟨w64 D, k⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 112, 16⟩
  ds : (⟨w64 D, k⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩
  stk : (VG.Proof.AesGcmSiv.X86.stk p).Disjoint ⟨w64 D, k⟩

theorem Dst.of_eq {p : VG.Proof.AesGcmSiv.X86.Prm} {s s' : State} {Q D : BitVec 32} {k : Nat} (h : VG.Proof.AesGcmSiv.X86.Dst p s Q D k) (hwr : s'.wr = s.wr) :
    VG.Proof.AesGcmSiv.X86.Dst p s' Q D k :=
  { h with wr := by rw [hwr]; exact h.wr }

/-- A block of `W` as `vg_aes_ctr32`'s data, with the key schedule `Q`. -/
theorem dstW {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} (L : VG.Proof.AesGcmSiv.X86.Lay p) (P : VG.Proof.AesGcmSiv.X86.Perm p s) {Q : BitVec 32} {q : Nat}
    (hq : q + 16 ≤ 128 ∧ (q + 16 ≤ 112 ∨ 128 ≤ q) ∨ 224 ≤ q ∧ q + 16 ≤ 256)
    (hk : (⟨w64 Q, 240⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 q, 16⟩) :
    VG.Proof.AesGcmSiv.X86.Dst p s Q (p.W + BitVec.ofNat 32 q) 16 where
  wr := by rw [L.aW (o := q) (by omega)]; exact P.wC (by omega)
  wrap := by rw [L.nW (o := q) (by omega)]; have := L.ww; omega
  dk := by rw [L.aW (o := q) (by omega)]; exact hk
  dc := by rw [L.aW (o := q) (by omega)]; exact Lay.w_w (by omega) (by omega) (by decide)
  ds := by rw [L.aW (o := q) (by omega)]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  stk := by rw [L.aW (o := q) (by omega)]; exact L.bw' (by omega)

/-- The arguments of `vg_aes_ctr32`: the key schedule at `Q`, the counter
block's copy at `W + 112`, `n` blocks at `D`, and the working space at
`W + 768` (where `ebp` is moved). -/
theorem cargs {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} (L : VG.Proof.AesGcmSiv.X86.Lay p) (esp : s.gpr .esp = p.SP) (P : VG.Proof.AesGcmSiv.X86.Perm p s) {Q D : BitVec 32}
    {n : Nat} (hQ : VG.Proof.AesGcmSiv.X86.KeyOk p s Q) (hD : VG.Proof.AesGcmSiv.X86.Dst p s Q D (16 * n)) (eax : s.gpr .eax = Q)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 p.R) (edx : s.gpr .edx = p.W + BitVec.ofNat 32 112)
    (ebx : s.gpr .ebx = D) (edi : s.gpr .edi = BitVec.ofNat 32 n)
    (ebp : s.gpr .ebp = p.W + BitVec.ofNat 32 768) :
    CtrCall s Q (p.W + BitVec.ofNat 32 112) D (p.W + BitVec.ofNat 32 768) p.R n := by
  have hsp := L.sp
  refine ⟨eax, ecx, edx, ebx, edi, ebp, L.rounds3, by rw [esp]; omega, ?_, hD.dk, ?_, ?_, ?_, hD.ds.sub_right ?_,
    ?_, ?_, ?_, ?_, hQ.wrap, ?_, hD.wrap, ?_, hQ.rd, ?_⟩
  · rw [L.aW (by decide)]; exact hQ.kc
  · rw [L.aW (by decide)]; exact hQ.ks
  · rw [L.aW (by decide)]; exact hD.dc.symm
  · rw [L.aW (by decide), L.aW (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [L.aW (by decide)]; exact fun _ h => h
  · rw [esp]; exact hQ.stk
  · rw [esp, L.aW (by decide)]; exact L.bw' (by decide)
  · rw [esp]; exact hD.stk
  · rw [esp, L.aW (by decide)]; exact L.bw' (by decide)
  · rw [L.nW (by decide)]; have := L.ww; omega
  · rw [L.nW (by decide)]; have := L.ww; omega
  · rw [L.aW (by decide), L.aW (by decide)]
    exact covers_cons (P.wC (by decide)) (covers_cons hD.wr (covers_cons (P.wC (by decide)) covers_nil))

/-- What a call of `vg_aes_ctr32` leaves. -/
structure CtrOut (p : VG.Proof.AesGcmSiv.X86.Prm) (s : State) (Q D : BitVec 32) (n : Nat) (s' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ [Reg.ebx, .esi, .edi], s'.gpr r = s.gpr r
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 D, 16 * n⟩,
    ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, VG.Proof.AesGcmSiv.X86.stk p] s.mem s'.mem
  out : blocksAt s'.mem (w64 D) n =
    ctr32 (aesWith p.R (bytesAt s.mem (w64 Q) (16 * (p.R + 1)))) (blockAt s.mem (w64 p.W + BitVec.ofNat 64 112))
      (blocksAt s.mem (w64 D) n)

/-- A call of `vg_aes_ctr32` on `n` blocks at `D`, which must lie in `mutR`,
from the counter block's copy at `W + 112`, under the key schedule `Q`. -/
theorem callCtr_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} (L : VG.Proof.AesGcmSiv.X86.Lay p) (E : VG.Proof.AesGcmSiv.X86.Env p s) {Q D : BitVec 32} {n : Nat}
    (hQ : VG.Proof.AesGcmSiv.X86.KeyOk p s Q) (hD : VG.Proof.AesGcmSiv.X86.Dst p s Q D (16 * n)) (hm : ∃ r' ∈ VG.Proof.AesGcmSiv.X86.mutR p, Region.Sub ⟨w64 D, 16 * n⟩ r')
    (eax : s.gpr .eax = Q) (ecx : s.gpr .ecx = BitVec.ofNat 32 p.R) (edx : s.gpr .edx = p.W + BitVec.ofNat 32 112)
    (ebx : s.gpr .ebx = D) (edi : s.gpr .edi = BitVec.ofNat 32 n) :
    WP isa (callCtr v.callees) s (VG.Proof.AesGcmSiv.X86.CtrOut p s Q D n) := by
  -- `ebp := W + 768`.
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  -- The call.
  have e768 : s.gpr .ebp + BitVec.ofNat 32 768 = p.W + BitVec.ofNat 32 768 := by rw [E.ebp]
  refine WP.seq (WP.mono (Proof.AesGcm.X86.ctr_call v (VG.Proof.AesGcmSiv.X86.cargs L (by gregs [E.esp])
    (E.perm.of_eq (by gmems []) (by gmems [])) (hQ.of_eq (by gmems []) (by gmems [])) (hD.of_eq (by gmems []))
    (by gregs [eax]) (by gregs [ecx]) (by gregs [edx]) (by gregs [ebx]) (by gregs [edi]) (by gregs [e768])))
    fun s₂ P => ?_)
  -- `ebp := W`.
  have hbp₂ : s₂.gpr .ebp = p.W + BitVec.ofNat 32 768 := by
    rw [P.saved _ (by decide)]; gregs [E.ebp]
  have hsp₂ : s₂.gpr .esp = p.SP := by rw [P.saved _ (by decide)]; gregs [E.esp]
  have f : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 D, 16 * n⟩,
      ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, VG.Proof.AesGcmSiv.X86.stk p] s.mem s₂.mem := by
    have f := P.frame
    rw [L.aW (by decide), L.aW (by decide)] at f
    simp only [mem_setReg, mem_arithFlags] at f
    refine f.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨VG.Proof.AesGcmSiv.X86.stk p, by simp, ?_⟩
      simpa [gpr_setReg_of_ne, E.esp] using L.stkSub (k := 28) (by decide)
  have fm : Frame (VG.Proof.AesGcmSiv.X86.mutR p) s.mem s₂.mem := VG.Proof.AesGcmSiv.X86.frame_toMut f fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (d := 112) (k := 16) (.inl (by decide))
    · exact hm
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (d := 768) (k := 2048) (.inr (.inr (.inr ⟨by decide, by decide⟩)))
    · exact VG.Proof.AesGcmSiv.X86.inMut_stk p
  refine WP.of_runBlock ⟨_, by grun [hbp₂], ?_⟩
  refine ⟨E.mut L (by gregs [hbp₂]; exact BitVec.add_sub_cancel _ _) (by gregs [hsp₂]) (by gmems [P.rd])
    (by gmems [P.wr]) (by gmems []; exact fm), by gmems [P.rd], by gmems [P.wr], ?_, by gmems []; exact f, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (gregs []; rw [P.saved _ (by decide)]; gregs [])
  · have o := P.out
    rw [L.aW (by decide)] at o
    gmems []
    exact o

/-- Calls of `vg_aes_ctr32` with the same arguments are constant time. -/
theorem callCtr_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {Q D : BitVec 32} {n : Nat} {I : State → Prop}
    (hI : ∀ s, I s → VG.Proof.AesGcmSiv.X86.Env p s ∧ VG.Proof.AesGcmSiv.X86.KeyOk p s Q ∧ VG.Proof.AesGcmSiv.X86.Dst p s Q D (16 * n) ∧ s.gpr .eax = Q ∧
      s.gpr .ecx = BitVec.ofNat 32 p.R ∧ s.gpr .edx = p.W + BitVec.ofNat 32 112 ∧ s.gpr .ebx = D ∧
      s.gpr .edi = BitVec.ofNat 32 n) :
    CT I (callCtr v.callees) := by
  -- The state after `ebp := W + 768`, as `CtrCall` needs it.
  have call : ∀ s, I s → ∀ s', runBlock isa [.alu .add .ebp (imm scrO)] s = some s' →
      CtrCall s' Q (p.W + BitVec.ofNat 32 112) D (p.W + BitVec.ofNat 32 768) p.R n ∧ s'.gpr .esp = p.SP := by
    intro s hs s' run
    obtain ⟨E, hQ, hD, eax, ecx, edx, ebx, edi⟩ := hI s hs
    have e := run
    simp (disch := first | decide | omega) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      imm, scrO, Option.bind_some, Option.some.injEq] at e
    subst e
    have e768 : s.gpr .ebp + BitVec.ofNat 32 768 = p.W + BitVec.ofNat 32 768 := by rw [E.ebp]
    exact ⟨VG.Proof.AesGcmSiv.X86.cargs L (by gregs [E.esp]) (E.perm.of_eq (by gmems []) (by gmems [])) (hQ.of_eq (by gmems []) (by gmems []))
      (hD.of_eq (by gmems [])) (by gregs [eax]) (by gregs [ecx]) (by gregs [edx]) (by gregs [ebx]) (by gregs [edi])
      (by gregs [e768]), by gregs [E.esp]⟩
  refine CT.seq (J := fun s' => ∃ s, I s ∧ runBlock isa [.alu .add .ebp (imm scrO)] s = some s')
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun s h => (hI s h).1.ebp) (by taint_decide))
    (fun s hs => WP.of_runBlock ⟨_, by grun [], s, hs, by grun []⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W + BitVec.ofNat 32 768)
    (Proof.AesGcm.X86.ctr_ct v (E := p.SP) fun s ⟨s₀, h₀, run⟩ => call s₀ h₀ s run)
    (fun s ⟨s₀, h₀, run⟩ => WP.mono (Proof.AesGcm.X86.ctr_call v (call s₀ h₀ s run).1) fun s₁ g => by
      rw [g.saved .ebp (by decide), (call s₀ h₀ s run).1.ebp]) ?_
  exact CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h) (by taint_decide)

/-! ## `vg_ghash` -/

/-- The arguments of `vg_ghash`: GHASH's key at `W + 64`, the accumulator at
`W + 80`, `n ≤ 64` blocks at `W + 768`, and the working space at `W + 1792`
(where `ebp` is moved). -/
theorem gargs {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} (L : VG.Proof.AesGcmSiv.X86.Lay p) (esp : s.gpr .esp = p.SP) (P : VG.Proof.AesGcmSiv.X86.Perm p s) {n : Nat} (hn : n ≤ 64)
    (eax : s.gpr .eax = p.W + BitVec.ofNat 32 64) (edx : s.gpr .edx = p.W + BitVec.ofNat 32 80)
    (ebx : s.gpr .ebx = p.W + BitVec.ofNat 32 768) (edi : s.gpr .edi = BitVec.ofNat 32 n)
    (ebp : s.gpr .ebp = p.W + BitVec.ofNat 32 1792) :
    GhCall s (p.W + BitVec.ofNat 32 64) (p.W + BitVec.ofNat 32 80) (p.W + BitVec.ofNat 32 768)
      (p.W + BitVec.ofNat 32 1792) n := by
  have hsp := L.sp
  have b24 := L.stkSub (k := 24) (by decide)
  have ww := L.ww
  refine ⟨eax, edx, ebx, edi, ebp, by rw [esp]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [L.aW (show 64 < 2816 by decide), L.aW (show 80 < 2816 by decide), L.aW (show 768 < 2816 by decide),
      L.aW (show 1792 < 2816 by decide), L.nW (show 64 < 2816 by decide), L.nW (show 80 < 2816 by decide),
      L.nW (show 768 < 2816 by decide), L.nW (show 1792 < 2816 by decide), esp]
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by decide) (by omega)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.bw' (by decide)).sub_left b24
  · exact (L.bw' (by decide)).sub_left b24
  · exact (L.bw' (by omega)).sub_left b24
  · exact (L.bw' (by decide)).sub_left b24
  · omega
  · omega
  · omega
  · omega
  · exact covers_cons (P.wCR (by decide)) (covers_cons (P.wCR (by omega)) covers_nil)
  · exact covers_cons (P.wC (by decide)) (covers_cons (P.wC (by decide)) covers_nil)

/-- What a call of `vg_ghash` leaves. -/
structure GhOut (p : VG.Proof.AesGcmSiv.X86.Prm) (s : State) (n : Nat) (s' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ [Reg.ebx, .esi, .edi], s'.gpr r = s.gpr r
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 80, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 1792, 256⟩, VG.Proof.AesGcmSiv.X86.stk p] s.mem s'.mem
  out : blockAt s'.mem (w64 p.W + BitVec.ofNat 64 80) =
    ghashFrom (blockAt s.mem (w64 p.W + BitVec.ofNat 64 64)) (blockAt s.mem (w64 p.W + BitVec.ofNat 64 80))
      (blocksAt s.mem (w64 p.W + BitVec.ofNat 64 768) n)

/-- A call of `vg_ghash` on the `n ≤ 64` blocks at `W + 768`. -/
theorem callGh_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} (L : VG.Proof.AesGcmSiv.X86.Lay p) (E : VG.Proof.AesGcmSiv.X86.Env p s) {n : Nat} (hn : n ≤ 64)
    (eax : s.gpr .eax = p.W + BitVec.ofNat 32 64) (edx : s.gpr .edx = p.W + BitVec.ofNat 32 80)
    (ebx : s.gpr .ebx = p.W + BitVec.ofNat 32 768) (edi : s.gpr .edi = BitVec.ofNat 32 n) :
    WP isa (callGh v.callees) s (VG.Proof.AesGcmSiv.X86.GhOut p s n) := by
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  have e1792 : s.gpr .ebp + BitVec.ofNat 32 1792 = p.W + BitVec.ofNat 32 1792 := by rw [E.ebp]
  refine WP.seq (WP.mono (Proof.AesGcm.X86.gh_call v (VG.Proof.AesGcmSiv.X86.gargs L (by gregs [E.esp])
    (E.perm.of_eq (by gmems []) (by gmems [])) hn (by gregs [eax]) (by gregs [edx]) (by gregs [ebx]) (by gregs [edi])
    (by gregs [e1792]))) fun s₂ P => ?_)
  have hbp₂ : s₂.gpr .ebp = p.W + BitVec.ofNat 32 1792 := by
    rw [P.saved _ (by decide)]; gregs [E.ebp]
  have hsp₂ : s₂.gpr .esp = p.SP := by rw [P.saved _ (by decide)]; gregs [E.esp]
  have f : Frame [⟨w64 p.W + BitVec.ofNat 64 80, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 1792, 256⟩, VG.Proof.AesGcmSiv.X86.stk p] s.mem s₂.mem := by
    have f := P.frame
    rw [L.aW (by decide), L.aW (by decide)] at f
    simp only [mem_setReg, mem_arithFlags] at f
    refine f.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨VG.Proof.AesGcmSiv.X86.stk p, by simp, ?_⟩
      simpa [gpr_setReg_of_ne, E.esp] using L.stkSub (k := 24) (by decide)
  have fm : Frame (VG.Proof.AesGcmSiv.X86.mutR p) s.mem s₂.mem := VG.Proof.AesGcmSiv.X86.frame_toMut f fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (d := 80) (k := 16) (.inl (by decide))
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (d := 1792) (k := 256) (.inr (.inr (.inr ⟨by decide, by decide⟩)))
    · exact VG.Proof.AesGcmSiv.X86.inMut_stk p
  refine WP.of_runBlock ⟨_, by grun [hbp₂], ?_⟩
  refine ⟨E.mut L (by gregs [hbp₂]; exact BitVec.add_sub_cancel _ _) (by gregs [hsp₂]) (by gmems [P.rd])
    (by gmems [P.wr]) (by gmems []; exact fm), by gmems [P.rd], by gmems [P.wr], ?_, by gmems []; exact f, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (gregs []; rw [P.saved _ (by decide)]; gregs [])
  · have o := P.out
    rw [L.aW (by decide), L.aW (by decide), L.aW (by decide)] at o
    gmems []
    exact o

/-- Calls of `vg_ghash` on the `n ≤ 64` blocks at `W + 768` are constant
time. -/
theorem callGh_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {n : Nat} (hn : n ≤ 64) {I : State → Prop}
    (hI : ∀ s, I s → VG.Proof.AesGcmSiv.X86.Env p s ∧ s.gpr .eax = p.W + BitVec.ofNat 32 64 ∧ s.gpr .edx = p.W + BitVec.ofNat 32 80 ∧
      s.gpr .ebx = p.W + BitVec.ofNat 32 768 ∧ s.gpr .edi = BitVec.ofNat 32 n) :
    CT I (callGh v.callees) := by
  have call : ∀ s, I s → ∀ s', runBlock isa [.alu .add .ebp (imm ghO)] s = some s' →
      GhCall s' (p.W + BitVec.ofNat 32 64) (p.W + BitVec.ofNat 32 80) (p.W + BitVec.ofNat 32 768)
        (p.W + BitVec.ofNat 32 1792) n ∧ s'.gpr .esp = p.SP := by
    intro s hs s' run
    obtain ⟨E, eax, edx, ebx, edi⟩ := hI s hs
    have e := run
    simp (disch := first | decide | omega) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      imm, ghO, Option.bind_some, Option.some.injEq] at e
    subst e
    have e1792 : s.gpr .ebp + BitVec.ofNat 32 1792 = p.W + BitVec.ofNat 32 1792 := by rw [E.ebp]
    exact ⟨VG.Proof.AesGcmSiv.X86.gargs L (by gregs [E.esp]) (E.perm.of_eq (by gmems []) (by gmems [])) hn (by gregs [eax]) (by gregs [edx])
      (by gregs [ebx]) (by gregs [edi]) (by gregs [e1792]), by gregs [E.esp]⟩
  refine CT.seq (J := fun s' => ∃ s, I s ∧ runBlock isa [.alu .add .ebp (imm ghO)] s = some s')
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun s h => (hI s h).1.ebp) (by taint_decide))
    (fun s hs => WP.of_runBlock ⟨_, by grun [], s, hs, by grun []⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W + BitVec.ofNat 32 1792)
    (Proof.AesGcm.X86.gh_ct v (E := p.SP) fun s ⟨s₀, h₀, run⟩ => call s₀ h₀ s run)
    (fun s ⟨s₀, h₀, run⟩ => WP.mono (Proof.AesGcm.X86.gh_call v (call s₀ h₀ s run).1) fun s₁ g => by
      rw [g.saved .ebp (by decide), (call s₀ h₀ s run).1.ebp]) ?_
  exact CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h) (by taint_decide)

/-! ## `vg_aes_expand_key` -/

/-- The key length of `R` rounds, as the code computes it. -/
theorem keyLen_eq {R : Nat} (hR : R = 10 ∨ R = 14) :
    (BitVec.ofNat 32 R - BitVec.ofNat 32 6 + (BitVec.ofNat 32 R - BitVec.ofNat 32 6) +
      (BitVec.ofNat 32 R - BitVec.ofNat 32 6 + (BitVec.ofNat 32 R - BitVec.ofNat 32 6))) =
      BitVec.ofNat 32 (Spec.GcmSiv.keyLen R) := by
  rcases hR with rfl | rfl <;> decide

/-- The arguments of `vg_aes_expand_key`: the encryption key at `W + 32`,
its schedule at `W + 512` and the working space at `W + 768` (where `ebp`
is moved). -/
theorem kargs {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} (L : VG.Proof.AesGcmSiv.X86.Lay p) (esp : s.gpr .esp = p.SP) (P : VG.Proof.AesGcmSiv.X86.Perm p s)
    (eax : s.gpr .eax = p.W + BitVec.ofNat 32 32) (ecx : s.gpr .ecx = BitVec.ofNat 32 (Spec.GcmSiv.keyLen p.R))
    (edx : s.gpr .edx = p.W + BitVec.ofNat 32 512) (ebp : s.gpr .ebp = p.W + BitVec.ofNat 32 768) :
    KeyCall s (p.W + BitVec.ofNat 32 32) (p.W + BitVec.ofNat 32 512) (p.W + BitVec.ofNat 32 768)
      (Spec.GcmSiv.keyLen p.R) := by
  have hsp := L.sp
  have b20 := L.stkSub (k := 20) (by decide)
  have ww := L.ww
  have hk : Spec.GcmSiv.keyLen p.R = 16 ∨ Spec.GcmSiv.keyLen p.R = 32 := by
    rcases L.rounds with h | h <;> rw [h] <;> decide
  have hk32 : Spec.GcmSiv.keyLen p.R ≤ 32 := by omega
  refine ⟨eax, ecx, edx, ebp, by omega, by rw [esp]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [L.aW (show 32 < 2816 by decide), L.aW (show 512 < 2816 by decide), L.aW (show 768 < 2816 by decide),
      L.nW (show 32 < 2816 by decide), L.nW (show 512 < 2816 by decide), L.nW (show 768 < 2816 by decide), esp]
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.bw' (by omega)).sub_left b20
  · exact (L.bw' (by decide)).sub_left b20
  · exact (L.bw' (by decide)).sub_left b20
  · omega
  · omega
  · omega
  · exact covers_cons (P.wCR (by omega)) covers_nil
  · exact covers_cons (P.wC (by decide)) (covers_cons (P.wC (by decide)) covers_nil)

/-- What a call of `vg_aes_expand_key` leaves. -/
structure KeyOut (p : VG.Proof.AesGcmSiv.X86.Prm) (s : State) (s' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ [Reg.ebx, .esi, .edi], s'.gpr r = s.gpr r
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 512, 240⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 512⟩, VG.Proof.AesGcmSiv.X86.stk p] s.mem s'.mem
  out : bytesAt s'.mem (w64 p.W + BitVec.ofNat 64 512) (16 * (Spec.Aes.rounds (Spec.GcmSiv.keyLen p.R / 4) + 1)) =
    Spec.Aes.expandKey (bytesAt s.mem (w64 p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R))

/-- The call of `vg_aes_expand_key` on the encryption key. -/
theorem callKey_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} (L : VG.Proof.AesGcmSiv.X86.Lay p) (E : VG.Proof.AesGcmSiv.X86.Env p s)
    (eax : s.gpr .eax = p.W + BitVec.ofNat 32 32) (ecx : s.gpr .ecx = BitVec.ofNat 32 (Spec.GcmSiv.keyLen p.R))
    (edx : s.gpr .edx = p.W + BitVec.ofNat 32 512) :
    WP isa (callKey v.callees) s (VG.Proof.AesGcmSiv.X86.KeyOut p s) := by
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  have e768 : s.gpr .ebp + BitVec.ofNat 32 768 = p.W + BitVec.ofNat 32 768 := by rw [E.ebp]
  refine WP.seq (WP.mono (Proof.AesGcm.X86.key_call v (VG.Proof.AesGcmSiv.X86.kargs L (by gregs [E.esp])
    (E.perm.of_eq (by gmems []) (by gmems [])) (by gregs [eax]) (by gregs [ecx]) (by gregs [edx]) (by gregs [e768])))
    fun s₂ P => ?_)
  have hbp₂ : s₂.gpr .ebp = p.W + BitVec.ofNat 32 768 := by
    rw [P.saved _ (by decide)]; gregs [E.ebp]
  have hsp₂ : s₂.gpr .esp = p.SP := by rw [P.saved _ (by decide)]; gregs [E.esp]
  have f : Frame [⟨w64 p.W + BitVec.ofNat 64 512, 240⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 512⟩, VG.Proof.AesGcmSiv.X86.stk p]
      s.mem s₂.mem := by
    have f := P.frame
    rw [L.aW (by decide), L.aW (by decide)] at f
    simp only [mem_setReg, mem_arithFlags] at f
    refine f.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨VG.Proof.AesGcmSiv.X86.stk p, by simp, ?_⟩
      simpa [gpr_setReg_of_ne, E.esp] using L.stkSub (k := 20) (by decide)
  have fm : Frame (VG.Proof.AesGcmSiv.X86.mutR p) s.mem s₂.mem := VG.Proof.AesGcmSiv.X86.frame_toMut f fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (d := 512) (k := 240) (.inr (.inr (.inr ⟨by decide, by decide⟩)))
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (d := 768) (k := 512) (.inr (.inr (.inr ⟨by decide, by decide⟩)))
    · exact VG.Proof.AesGcmSiv.X86.inMut_stk p
  refine WP.of_runBlock ⟨_, by grun [hbp₂], ?_⟩
  refine ⟨E.mut L (by gregs [hbp₂]; exact BitVec.add_sub_cancel _ _) (by gregs [hsp₂]) (by gmems [P.rd])
    (by gmems [P.wr]) (by gmems []; exact fm), by gmems [P.rd], by gmems [P.wr], ?_, by gmems []; exact f, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (gregs []; rw [P.saved _ (by decide)]; gregs [])
  have o := P.out
  rw [L.aW (by decide), L.aW (by decide)] at o
  gmems []
  exact o

/-- The call of `vg_aes_expand_key` on the encryption key is constant time. -/
theorem callKey_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {I : State → Prop}
    (hI : ∀ s, I s → VG.Proof.AesGcmSiv.X86.Env p s ∧ s.gpr .eax = p.W + BitVec.ofNat 32 32 ∧
      s.gpr .ecx = BitVec.ofNat 32 (Spec.GcmSiv.keyLen p.R) ∧ s.gpr .edx = p.W + BitVec.ofNat 32 512) :
    CT I (callKey v.callees) := by
  have call : ∀ s, I s → ∀ s', runBlock isa [.alu .add .ebp (imm scrO)] s = some s' →
      KeyCall s' (p.W + BitVec.ofNat 32 32) (p.W + BitVec.ofNat 32 512) (p.W + BitVec.ofNat 32 768)
        (Spec.GcmSiv.keyLen p.R) ∧ s'.gpr .esp = p.SP := by
    intro s hs s' run
    obtain ⟨E, eax, ecx, edx⟩ := hI s hs
    have e := run
    simp (disch := first | decide | omega) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      imm, scrO, Option.bind_some, Option.some.injEq] at e
    subst e
    have e768 : s.gpr .ebp + BitVec.ofNat 32 768 = p.W + BitVec.ofNat 32 768 := by rw [E.ebp]
    exact ⟨VG.Proof.AesGcmSiv.X86.kargs L (by gregs [E.esp]) (E.perm.of_eq (by gmems []) (by gmems [])) (by gregs [eax]) (by gregs [ecx])
      (by gregs [edx]) (by gregs [e768]), by gregs [E.esp]⟩
  refine CT.seq (J := fun s' => ∃ s, I s ∧ runBlock isa [.alu .add .ebp (imm scrO)] s = some s')
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun s h => (hI s h).1.ebp) (by taint_decide))
    (fun s hs => WP.of_runBlock ⟨_, by grun [], s, hs, by grun []⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W + BitVec.ofNat 32 768)
    (Proof.AesGcm.X86.key_ct v (E := p.SP) fun s ⟨s₀, h₀, run⟩ => call s₀ h₀ s run)
    (fun s ⟨s₀, h₀, run⟩ => WP.mono (Proof.AesGcm.X86.key_call v (call s₀ h₀ s run).1) fun s₁ g => by
      rw [g.saved .ebp (by decide), (call s₀ h₀ s run).1.ebp]) ?_
  exact CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h) (by taint_decide)

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Derive`. -/
section

/-!
# AES-GCM-SIV on x86: the message keys (`derive`)

Untrusted: everything here is checked by Lean. Each step of `derive` writes
`little_endian_uint32(i) ‖ nonce` at `W + 112` and a zero block at
`W + 224` (`derArgs_ok`), on which `vg_aes_ctr32` leaves
`CIPH_K(little_endian_uint32(i) ‖ nonce)`, of which the first 8 bytes are
kept at `W + 16 + 8 i` (`derPost_ok`): after the loop, the halves of
`derive_keys` (`derive_ok`, `DInv.keys`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv slotv_eq zero4_fold zero4_bytes' length_bytesAt
  GcmImpl CT readW_writeW_off)

/-! ## Arithmetic -/

theorem ofNat_add32 (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) := by
  rw [BitVec.ofNat_add]

/-- The offset of the 8 bytes a step keeps, as the code computes it. -/
theorem eaKeep {W : BitVec 32} {i k : Nat} (hw : W.toNat + 2816 ≤ 2 ^ 32) (hi : 8 * i + k < 2816) :
    w64 (BitVec.ofNat 32 i + BitVec.ofNat 32 i + (BitVec.ofNat 32 i + BitVec.ofNat 32 i) +
      (BitVec.ofNat 32 i + BitVec.ofNat 32 i + (BitVec.ofNat 32 i + BitVec.ofNat 32 i)) + W + BitVec.ofNat 32 k) =
      w64 W + BitVec.ofNat 64 (k + 8 * i) := by
  simp only [VG.Proof.AesGcmSiv.X86.ofNat_add32]
  rw [BitVec.add_comm (BitVec.ofNat 32 _) W, BitVec.add_assoc, VG.Proof.AesGcmSiv.X86.ofNat_add32]
  exact Proof.AesGcm.X86.w64_add (by omega) |>.trans (by congr 2; omega)

/-- A block as its four words. -/
theorem bytesAt_words (m : Mem) (p : Addr) (d : Nat) :
    bytesAt m (p + BitVec.ofNat 64 d) 16 = le4 (m.readW (p + BitVec.ofNat 64 d) 32) ++
      le4 (m.readW (p + BitVec.ofNat 64 (d + 4)) 32) ++ le4 (m.readW (p + BitVec.ofNat 64 (d + 8)) 32) ++
      le4 (m.readW (p + BitVec.ofNat 64 (d + 12)) 32) := by
  rw [Proof.Cmac.bytesAt_split4, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW]

/-! ## A step's block -/

/-- The memory after a step's block. -/
def derMem (m : Mem) (W N : Addr) (i : Nat) : Mem :=
  Proof.Cmac.zero4 ((((m.writeW (W + BitVec.ofNat 64 116) (m.readW N 32)).writeW (W + BitVec.ofNat 64 120)
      (m.readW (N + BitVec.ofNat 64 4) 32)).writeW (W + BitVec.ofNat 64 124) (m.readW (N + BitVec.ofNat 64 8) 32)).writeW
    (W + BitVec.ofNat 64 112) (BitVec.ofNat 32 i)) (W + BitVec.ofNat 64 224)

/-- The arguments of a step: the counter block and a zero block. -/
theorem derArgs_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {i : Nat}
    (hi : slotv t.mem p.W iO = BitVec.ofNat 32 i) :
    ∃ t₁ : State, runBlock isa deriveBlock t = some t₁ ∧ t₁.mem = VG.Proof.AesGcmSiv.X86.derMem t.mem (w64 p.W) (w64 p.N) i ∧
      t₁.gpr .eax = p.K ∧ t₁.gpr .ecx = BitVec.ofNat 32 p.R ∧ t₁.gpr .edx = p.W + BitVec.ofNat 32 112 ∧
      t₁.gpr .ebx = p.W + BitVec.ofNat 32 224 ∧ t₁.gpr .edi = BitVec.ofNat 32 1 ∧
      t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧ t₁.gpr .esi = t.gpr .esi ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have S := E.slots
  have n₀ := E.perm.nR (d := 0) (k := 4) (by decide)
  have n₄ := E.perm.nR (d := 4) (k := 4) (by decide)
  have n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  have hz := zero4_fold (t.mem.writeW (w64 p.W + BitVec.ofNat 64 116) (t.mem.readW (w64 p.N) 32) |>.writeW
      (w64 p.W + BitVec.ofNat 64 120) (t.mem.readW (w64 p.N + BitVec.ofNat 64 4) 32) |>.writeW
      (w64 p.W + BitVec.ofNat 64 124) (t.mem.readW (w64 p.N + BitVec.ofNat 64 8) 32) |>.writeW
      (w64 p.W + BitVec.ofNat 64 112) (BitVec.ofNat 32 i)) p.W 224
  simp only [Nat.reduceAdd] at hz
  simp only [slotv_eq] at hi
  have hN := S.nonce
  have hK := S.ctx
  have hR := S.rounds
  simp only [slotv_eq, nonceO, ctxO, roundsO, iO] at hN hK hR hi
  refine ⟨_, by simp only [deriveBlock, zero4]; grun [E.ebp, L.aW, L.aN, E.perm.wW, E.perm.wR, hN, n₀, n₄, n₈],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hi, BitVec.add_zero, hz, VG.Proof.AesGcmSiv.X86.derMem]
  · gregs [hK]
  · gregs [hR]
  · gregs [E.ebp]
  · gregs [E.ebp]
  · gregs []
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []
  all_goals rfl

/-- The counter block of a step: `little_endian_uint32(i) ‖ nonce`. -/
theorem derBlock_bytes (m : Mem) (W N : Addr) (i : Nat) :
    bytesAt (VG.Proof.AesGcmSiv.X86.derMem m W N i) (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt m N 12 := by
  rw [VG.Proof.AesGcmSiv.X86.derMem, Proof.Cmac.zero4, Proof.AesGcm.X86.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide),
    VG.Proof.AesGcmSiv.X86.bytesAt_words]
  simp (disch := decide) only [Nat.reduceAdd, Mem.readW_writeW_self32, readW_writeW_off]
  rw [GcmSiv.le4_ofNat, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    show (12 : Nat) = 4 + (4 + 4) from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc]
  simp only [List.append_assoc]

/-- The zero block of a step. -/
theorem derZero_block (W N : Addr) (m : Mem) (i : Nat) :
    Spec.Gcm.blockAt (VG.Proof.AesGcmSiv.X86.derMem m W N i) (W + BitVec.ofNat 64 224) = 0 := by
  rw [VG.Proof.AesGcmSiv.X86.derMem, Spec.Gcm.blockAt, Proof.Cmac.zero4_bytes]
  decide

theorem derMem_frame (m : Mem) (W N : Addr) (i : Nat) :
    Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 16⟩] m (VG.Proof.AesGcmSiv.X86.derMem m W N i) := by
  have c : ∀ d, 112 ≤ d → d + 4 ≤ 128 → (⟨W + BitVec.ofNat 64 112, 16⟩ : Region).Contains (W + BitVec.ofNat 64 d)
      (32 / 8) := fun d h₁ h₂ => Offset.contains W (by omega) (by omega) (by omega)
  have mem₀ : (⟨W + BitVec.ofNat 64 112, 16⟩ : Region) ∈
      [(⟨W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨W + BitVec.ofNat 64 224, 16⟩] := List.mem_cons_self
  refine (((((Frame.refl _ _).writeW mem₀ _ (c 116 (by decide) (by decide))).writeW mem₀ _
    (c 120 (by decide) (by decide))).writeW mem₀ _ (c 124 (by decide) (by decide))).writeW mem₀ _
    (c 112 (by decide) (by decide))).trans ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self)

/-! ## After a step's call -/

/-- What the code after the call of a step writes: the 8 bytes kept, and
the next `i`. -/
def postMem (m : Mem) (W : Addr) (i : Nat) : Mem :=
  ((m.writeW (W + BitVec.ofNat 64 (16 + 8 * i)) (m.readW (W + BitVec.ofNat 64 224) 32)).writeW
    (W + BitVec.ofNat 64 (20 + 8 * i)) (m.readW (W + BitVec.ofNat 64 228) 32)).writeW (W + BitVec.ofNat 64 180)
    (BitVec.ofNat 32 (i + 1))

/-- The code after the call of a step. -/
theorem derPost_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {i : Nat} (hi : i < p.R / 2 - 1)
    (hix : slotv t.mem p.W iO = BitVec.ofNat 32 i) :
    ∃ t' : State, runBlock isa derivePost t = some t' ∧ t'.mem = VG.Proof.AesGcmSiv.X86.postMem t.mem (w64 p.W) i ∧
      t'.zf = some (decide (i + 1 = p.R / 2 - 1)) ∧ t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧
      t'.gpr .esi = t.gpr .esi ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR := L.rounds
  have S := E.slots
  have hRs := S.rounds
  simp only [slotv_eq, iO, roundsO] at hix hRs
  have hi6 : i ≤ 5 := by rcases hR with h | h <;> rw [h] at hi <;> omega
  have ea₀ := VG.Proof.AesGcmSiv.X86.eaKeep (W := p.W) (i := i) (k := 16) L.ww (by omega)
  have ea₁ := VG.Proof.AesGcmSiv.X86.eaKeep (W := p.W) (i := i) (k := 20) L.ww (by omega)
  have wo₀ := E.perm.wW (d := 16 + 8 * i) (n := 4) (by omega)
  have wo₁ := E.perm.wW (d := 20 + 8 * i) (n := 4) (by omega)
  have r224 : (t.mem.writeW (w64 p.W + BitVec.ofNat 64 (16 + 8 * i)) (t.mem.readW (w64 p.W + BitVec.ofNat 64 224) 32)).readW
      (w64 p.W + BitVec.ofNat 64 228) 32 = t.mem.readW (w64 p.W + BitVec.ofNat 64 228) 32 :=
    readW_writeW_off _ _ _ (by omega) (by decide) (by omega)
  have rI : ((t.mem.writeW (w64 p.W + BitVec.ofNat 64 (16 + 8 * i)) (t.mem.readW (w64 p.W + BitVec.ofNat 64 224) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 (20 + 8 * i)) (t.mem.readW (w64 p.W + BitVec.ofNat 64 228) 32)).readW
      (w64 p.W + BitVec.ofNat 64 180) 32 = t.mem.readW (w64 p.W + BitVec.ofNat 64 180) 32 := by
    rw [readW_writeW_off _ _ _ (by omega) (by decide) (by omega), readW_writeW_off _ _ _ (by omega) (by decide) (by omega)]
  have rR : ∀ v, (((t.mem.writeW (w64 p.W + BitVec.ofNat 64 (16 + 8 * i)) (t.mem.readW (w64 p.W + BitVec.ofNat 64 224) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 (20 + 8 * i)) (t.mem.readW (w64 p.W + BitVec.ofNat 64 228) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 180) v).readW (w64 p.W + BitVec.ofNat 64 148) 32 =
      t.mem.readW (w64 p.W + BitVec.ofNat 64 148) 32 := fun v => by
    rw [readW_writeW_off _ _ _ (by decide) (by decide) (by decide), readW_writeW_off _ _ _ (by omega) (by decide) (by omega),
      readW_writeW_off _ _ _ (by omega) (by decide) (by omega)]
  refine ⟨_, by simp only [derivePost]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hix, ea₀, ea₁, wo₀, wo₁, r224, rI, rR,
    hRs], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hix, VG.Proof.AesGcmSiv.X86.ofNat_add32, VG.Proof.AesGcmSiv.X86.postMem]
  · gmems [hix, hRs, rR, VG.Proof.AesGcmSiv.X86.ofNat_add32]
    rw [VG.Proof.AesGcmSiv.X86.ofNat_lsr32 L.R_lt, Nat.pow_one, show BitVec.ofNat 32 (p.R / 2) - BitVec.ofNat 32 1 =
      BitVec.ofNat 32 (p.R / 2 - 1) by rcases hR with h | h <;> rw [h] <;> decide,
      Proof.AesGcm.X86.sub_beq32 (by omega) (by rcases hR with h | h <;> rw [h] <;> decide)]
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []
  all_goals rfl

theorem postMem_frame (m : Mem) (W : Addr) (i : Nat) (hi : 8 * i + 24 < 2 ^ 64) :
    Frame [⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩, ⟨W + BitVec.ofNat 64 180, 4⟩] m (VG.Proof.AesGcmSiv.X86.postMem m W i) := by
  have c₀ : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩ : Region).Contains (W + BitVec.ofNat 64 (16 + 8 * i)) (32 / 8) :=
    Offset.contains W (by omega) (by omega) (by omega)
  have c₁ : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩ : Region).Contains (W + BitVec.ofNat 64 (20 + 8 * i)) (32 / 8) :=
    Offset.contains W (by omega) (by omega) (by omega)
  unfold VG.Proof.AesGcmSiv.X86.postMem
  exact (((Frame.refl _ _).writeW List.mem_cons_self _ c₀).writeW List.mem_cons_self _ c₁).writeW
    (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)

/-- The 8 bytes a step keeps: the first 8 of the block at `W + 224`. -/
theorem postMem_bytes (m : Mem) (W : Addr) {i : Nat} (hi : i ≤ 5) :
    bytesAt (VG.Proof.AesGcmSiv.X86.postMem m W i) (W + BitVec.ofNat 64 (16 + 8 * i)) 8 = bytesAt m (W + BitVec.ofNat 64 224) 8 := by
  have e : W + BitVec.ofNat 64 (20 + 8 * i) = W + BitVec.ofNat 64 (16 + 8 * i) + BitVec.ofNat 64 4 := by
    rw [VG.Proof.AesGcmSiv.X86.add_ofNat_assoc]; congr 2; omega
  have d : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 4⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (20 + 8 * i), 4⟩ :=
    Offset.disjoint W (.inl (by omega)) (by omega) (by omega)
  have d₁ : (⟨W + BitVec.ofNat 64 180, 4⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (16 + 8 * i), 4⟩ :=
    Offset.disjoint W (.inr (by omega)) (by omega) (by omega)
  have d₂ : (⟨W + BitVec.ofNat 64 180, 4⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (20 + 8 * i), 4⟩ :=
    Offset.disjoint W (.inr (by omega)) (by omega) (by omega)
  rw [show (8 : Nat) = 4 + 4 from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, ← e,
    ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, VG.Proof.AesGcmSiv.X86.postMem,
    Proof.Cmac.readW_writeW_disj _ d₁, Proof.Cmac.readW_writeW_disj _ d₂,
    Proof.Cmac.readW_writeW_disj _ d.symm, Mem.readW_writeW_self32, Mem.readW_writeW_self32, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc]

/-! ## The loop -/

/-- What `derive` writes. -/
abbrev derR (p : VG.Proof.AesGcmSiv.X86.Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 16, 48⟩, ⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 8⟩,
    ⟨w64 p.W + BitVec.ofNat 64 224, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, VG.Proof.AesGcmSiv.X86.stk p]

theorem inMut_derR (p : VG.Proof.AesGcmSiv.X86.Prm) : VG.Proof.AesGcmSiv.X86.InMut p (VG.Proof.AesGcmSiv.X86.derR p) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide))
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide))
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact VG.Proof.AesGcmSiv.X86.inMut_stk p

/-- After `i` steps of `derive` from `σ`: the first `8 i` bytes of the halves
at `W + 16`. -/
structure DInv (p : VG.Proof.AesGcmSiv.X86.Prm) (σ : State) (i : Nat) (t : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t
  ix : slotv t.mem p.W iO = BitVec.ofNat 32 i
  le : i ≤ p.R / 2 - 1
  esi : t.gpr .esi = σ.gpr .esi
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  frame : Frame (VG.Proof.AesGcmSiv.X86.derR p) σ.mem t.mem
  out : bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) (8 * i) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem (w64 p.K) p.R) (bytesAt σ.mem (w64 p.N) 12) i

/-- A step of `derive`. -/
theorem derStep_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {σ : State} {i : Nat} (hi : i < p.R / 2 - 1) {t : State}
    (I : VG.Proof.AesGcmSiv.X86.DInv p σ i t) :
    WP isa (.seq (.block deriveBlock) (.seq (callCtr v.callees) (.block derivePost))) t fun t' =>
      VG.Proof.AesGcmSiv.X86.DInv p σ (i + 1) t' ∧ t'.zf = some (decide (i + 1 = p.R / 2 - 1)) := by
  have hR := L.rounds
  have hw := L.ww
  have hi6 : i ≤ 5 := by rcases hR with h | h <;> rw [h] at hi <;> omega
  have fm := VG.Proof.AesGcmSiv.X86.frame_toMut I.frame (VG.Proof.AesGcmSiv.X86.inMut_derR p)
  have eN : bytesAt t.mem (w64 p.N) 12 = bytesAt σ.mem (w64 p.N) 12 := VG.Proof.AesGcmSiv.X86.nonce_mut L fm
  have eK := VG.Proof.AesGcmSiv.X86.ciph_mut L fm
  obtain ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, ebp₁, esp₁, esi₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.derArgs_ok L I.env I.ix
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by
    rw [hm₁]; exact VG.Proof.AesGcmSiv.X86.derMem_frame _ _ _ _
  have E₁ : VG.Proof.AesGcmSiv.X86.Env p t₁ := I.env.mut L ebp₁ esp₁ rd₁ wr₁ (VG.Proof.AesGcmSiv.X86.frame_toMut f₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide))
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have hb₁ : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 112) 16 =
      Spec.GcmSiv.le32 i ++ bytesAt t.mem (w64 p.N) 12 := by
    rw [hm₁]; exact VG.Proof.AesGcmSiv.X86.derBlock_bytes _ _ _ _
  have hz₁ : Spec.Gcm.blockAt t₁.mem (w64 p.W + BitVec.ofNat 64 224) = 0 := by
    rw [hm₁]; exact VG.Proof.AesGcmSiv.X86.derZero_block _ _ _ _
  have hD : VG.Proof.AesGcmSiv.X86.Dst p t₁ p.K (p.W + BitVec.ofNat 32 224) (16 * 1) :=
    VG.Proof.AesGcmSiv.X86.dstW L E₁.perm (q := 224) (.inr ⟨by decide, by decide⟩) (L.k_w' (by decide))
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.callCtr_ok v L E₁ (VG.Proof.AesGcmSiv.X86.keyK L E₁.perm) hD
    (by rw [L.aW (by decide)]; exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))) eax ecx edx ebx edi)
    fun t₂ P => ?_)
  have E₂ := P.env
  have hix₂ : slotv t₂.mem p.W iO = BitVec.ofNat 32 i := by
    have := I.ix
    rw [← this]
    refine (P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 180, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)).trans (f₁.readW (r := ⟨w64 p.W + BitVec.ofNat 64 180, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · rw [L.aW (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  have fc := P.frame
  have hout := P.out
  rw [L.aW (show 224 < 2816 by decide)] at fc hout
  obtain ⟨t₃, run₃, hm₃, z₃, ebp₃, esp₃, esi₃, rd₃, wr₃⟩ := VG.Proof.AesGcmSiv.X86.derPost_ok L E₂ hi hix₂
  have f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 (16 + 8 * i), 8⟩, ⟨w64 p.W + BitVec.ofNat 64 180, 4⟩] t₂.mem t₃.mem := by
    rw [hm₃]; exact VG.Proof.AesGcmSiv.X86.postMem_frame _ _ _ (by omega)
  have E₃ : VG.Proof.AesGcmSiv.X86.Env p t₃ := E₂.mut L ebp₃ esp₃ rd₃ wr₃ (VG.Proof.AesGcmSiv.X86.frame_toMut f₃ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by omega))
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩)))
  refine WP.of_runBlock ⟨t₃, run₃, ⟨E₃, ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩, z₃⟩
  · -- The next `i`.
    rw [slotv_eq, hm₃, VG.Proof.AesGcmSiv.X86.postMem, Mem.readW_writeW_self32]
  · rw [esi₃, P.saved _ (by decide), esi₁, I.esi]
  · rw [rd₃, P.rd, rd₁, I.rd]
  · rw [wr₃, P.wr, wr₁, I.wr]
  · -- The frame.
    have mem : ∀ {r : Region}, r ∈ VG.Proof.AesGcmSiv.X86.derR p → ∃ r' ∈ VG.Proof.AesGcmSiv.X86.derR p, Region.Sub r r' := fun {r} h => ⟨r, h, fun _ h => h⟩
    refine ((I.frame.trans (f₁.sub fun r hr => ?_)).trans (fc.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact mem (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact mem (by simp)
      · simp only [Nat.mul_one]; exact mem (by simp)
      · exact mem (by simp)
      · exact mem (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub _ (by omega) (by omega)⟩
      · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · -- The bytes.
    have dW : ∀ {d k : Nat}, d + k ≤ 2816 → 16 + 8 * i ≤ d ∨ d + k ≤ 16 →
        (⟨w64 p.W + BitVec.ofNat 64 16, 8 * i⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ h₂ => Lay.w_w (by omega) (by omega) h₁
    have keep : bytesAt t₃.mem (w64 p.W + BitVec.ofNat 64 16) (8 * i) =
        bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) (8 * i) := by
      rw [Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact dW (by omega) (by omega)
          · exact dW (by decide) (by omega)) (by omega),
        Proof.AesGcm.X86.bytesAt_frame fc (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact dW (by decide) (by omega)
          · simp only [Nat.mul_one]; exact dW (by decide) (by omega)
          · exact dW (by decide) (by omega)
          · exact (L.bw' (by omega)).symm) (by omega),
        Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact dW (by decide) (by omega)) (by omega)]
    simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
    have last : bytesAt t₃.mem (w64 p.W + BitVec.ofNat 64 (16 + 8 * i)) 8 =
        (Spec.GcmSiv.ctxCiph σ.mem (w64 p.K) p.R
          (Spec.GcmSiv.le32 i ++ bytesAt σ.mem (w64 p.N) 12)).take 8 := by
      have e16 : bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 16 =
          bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 8 ++
            bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224 + BitVec.ofNat 64 8) 8 :=
        Proof.Cmac.bytesAt_add _ _ 8 8
      have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.K) p.R = Spec.GcmSiv.ctxCiph t.mem (w64 p.K) p.R := by
        unfold Spec.GcmSiv.ctxCiph
        rw [Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rounds_le))
          (by omega)]
      rw [hm₃, VG.Proof.AesGcmSiv.X86.postMem_bytes _ _ hi6,
        show bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 8 =
          (bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 16).take 8 by
          rw [e16, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)],
        Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt, hb₁,
        Proof.Cmac.aesWith_bytes _ _ (by rw [List.length_append, Proof.Cmac.bytesAt_length]; rfl),
        ← GcmSiv.aesWith_eq, show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (w64 p.K) (16 * (p.R + 1))) =
          Spec.GcmSiv.ctxCiph t₁.mem (w64 p.K) p.R from rfl, ek₁, eK, eN]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, Proof.Cmac.bytesAt_add, GcmSiv.halves_succ, ← I.out, keep,
      VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, last]

/-- The start of `derive`: `i = 0`. -/
theorem derive0_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {σ : State} (E : VG.Proof.AesGcmSiv.X86.Env p σ) :
    ∃ t₀, runBlock isa [.mov .eax (imm 0), .store (at_ .ebp iO) .eax] σ = some t₀ ∧ VG.Proof.AesGcmSiv.X86.DInv p σ 0 t₀ := by
  refine ⟨_, by grun [E.ebp, L.aW, E.perm.wW], ?_⟩
  have f : Frame [⟨w64 p.W + BitVec.ofNat 64 180, 4⟩] σ.mem
      (σ.mem.writeW (w64 p.W + BitVec.ofNat 64 180) (BitVec.ofNat 32 0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have f' : Frame (VG.Proof.AesGcmSiv.X86.derR p) σ.mem (σ.mem.writeW (w64 p.W + BitVec.ofNat 64 180) (BitVec.ofNat 32 0)) :=
    f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  refine ⟨E.mut L (by gregs [E.ebp]) (by gregs [E.esp]) (by gmems []) (by gmems [])
      (by gmems []; exact VG.Proof.AesGcmSiv.X86.frame_toMut f' (VG.Proof.AesGcmSiv.X86.inMut_derR p)),
    by gmems [slotv_eq], Nat.zero_le _, by gregs [], by gmems [], by gmems [], by gmems []; exact f', ?_⟩
  simp [GcmSiv.halves, bytesAt]

/-- `derive`: the halves of `derive_keys` at `W + 16`. -/
theorem derive_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {σ : State} (E : VG.Proof.AesGcmSiv.X86.Env p σ) :
    WP isa (derive v.callees) σ (VG.Proof.AesGcmSiv.X86.DInv p σ (p.R / 2 - 1)) := by
  have hR := L.rounds
  obtain ⟨t₀, run₀, I₀⟩ := VG.Proof.AesGcmSiv.X86.derive0_ok L E
  unfold derive
  refine WP.seq (WP.of_runBlock ⟨t₀, run₀, ?_⟩)
  refine WP.loop (M := isa) (fun m t => ∃ i, m = (p.R / 2 - 1) - i ∧ i < p.R / 2 - 1 ∧ VG.Proof.AesGcmSiv.X86.DInv p σ i t) ?_
    ((p.R / 2 - 1) - 0) _ ⟨0, rfl, by rcases hR with h | h <;> rw [h] <;> decide, I₀⟩
  rintro m t ⟨i, rfl, hi, I⟩
  refine WP.mono (VG.Proof.AesGcmSiv.X86.derStep_ok v L hi I) fun t' ⟨I', hz⟩ => ?_
  have ev := VG.Proof.AesGcmSiv.X86.eval_ne hz
  by_cases he : i + 1 = p.R / 2 - 1
  · left; exact ⟨ev.trans (by simp [he]), he ▸ I'⟩
  · right; exact ⟨ev.trans (by simp [he]), (p.R / 2 - 1) - (i + 1), by omega, i + 1, rfl, by omega, I'⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DInv.keys {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {σ t : State} (I : VG.Proof.AesGcmSiv.X86.DInv p σ (p.R / 2 - 1) t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (w64 p.K) p.R) (Spec.GcmSiv.keyLen p.R)
        (bytesAt σ.mem (w64 p.N) 12) =
      (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) 16,
        bytesAt t.mem (w64 p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R)) := by
  have hR := L.rounds
  have hk : Spec.GcmSiv.keyLen p.R / 8 + 2 = p.R / 2 - 1 := by unfold Spec.GcmSiv.keyLen; omega
  have hl : 8 * (p.R / 2 - 1) = 16 + Spec.GcmSiv.keyLen p.R := by unfold Spec.GcmSiv.keyLen; omega
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem _ p.R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Keys`. -/
section

/-!
# AES-GCM-SIV on x86: the encryption key's schedule and GHASH's key

Untrusted: everything here is checked by Lean. `expand` writes the schedule
of the encryption key at `W + 512` (`expand_ok`), and `hkey` GHASH's key,
`H · x` for the authentication key `H` (POLYVAL's field element), in
GHASH's order at `W + 64`, and zeroes its accumulator (`hkey_ok`).
`keys_ok`: the three together.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Proof.GcmSiv.Words (hkeyOf)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq zero4_fold GcmImpl readW_writeW_off)

/-! ## Blocks stored a word at a time -/

/-- A block of GHASH as the four words in memory, each byte-reversed. -/
theorem blockAt_bswap (m : Mem) (p : Addr) (d : Nat) :
    Spec.Gcm.blockAt m (p + BitVec.ofNat 64 d) = bswap (m.readW (p + BitVec.ofNat 64 d) 32) ++
      bswap (m.readW (p + BitVec.ofNat 64 (d + 4)) 32) ++ bswap (m.readW (p + BitVec.ofNat 64 (d + 8)) 32) ++
      bswap (m.readW (p + BitVec.ofNat 64 (d + 12)) 32) := by
  rw [Spec.Gcm.blockAt, VG.Proof.AesGcmSiv.X86.bytesAt_words, Proof.AesGcm.X86.ofBytes_le4]
  rfl

/-! ## `expand` -/

/-- What `expand` leaves: the schedule of the encryption key at `W + 512`. -/
structure ExpPost (p : VG.Proof.AesGcmSiv.X86.Prm) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  esi : t'.gpr .esi = t.gpr .esi
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 512, 240⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 512⟩, VG.Proof.AesGcmSiv.X86.stk p] t.mem t'.mem
  ciph : Spec.GcmSiv.ctxCiph t'.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
    Spec.GcmSiv.aes (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R))

/-- The arguments of `expand`'s call. -/
theorem expArgs_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) :
    ∃ t₁, runBlock isa expandArgs t = some t₁ ∧
      t₁.gpr .eax = p.W + BitVec.ofNat 32 32 ∧ t₁.gpr .ecx = BitVec.ofNat 32 (Spec.GcmSiv.keyLen p.R) ∧
      t₁.gpr .edx = p.W + BitVec.ofNat 32 512 ∧ t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧
      t₁.gpr .esi = t.gpr .esi ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧ t₁.mem = t.mem := by
  have hR := L.rounds
  have hRs := E.slots.rounds
  simp only [slotv_eq, roundsO] at hRs
  refine ⟨_, by simp only [expandArgs]; grun [E.ebp, L.aW, E.perm.wR, hRs], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gregs [E.ebp]
  · gregs [hRs, VG.Proof.AesGcmSiv.X86.keyLen_eq hR]
  · gregs [E.ebp]
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []
  all_goals gmems []

theorem expand_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) :
    WP isa (expand v.callees) t (VG.Proof.AesGcmSiv.X86.ExpPost p t) := by
  obtain ⟨t₁, run₁, eax, ecx, edx, ebp₁, esp₁, esi₁, rd₁, wr₁, hm₁⟩ := VG.Proof.AesGcmSiv.X86.expArgs_ok L E
  have E₁ : VG.Proof.AesGcmSiv.X86.Env p t₁ := E.keep (by rw [ebp₁, E.ebp]) (by rw [esp₁, E.esp]) rd₁ wr₁ hm₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (VG.Proof.AesGcmSiv.X86.callKey_ok v L E₁ eax ecx edx)
    fun t₂ P => ⟨P.env, by rw [P.rd, rd₁], by rw [P.wr, wr₁], by rw [P.saved _ (by decide), esi₁], ?_, ?_⟩
  · rw [← hm₁]; exact P.frame
  · have out := P.out
    have hr : Spec.Aes.rounds (Spec.GcmSiv.keyLen p.R / 4) = p.R := by
      unfold Spec.Aes.rounds Spec.GcmSiv.keyLen; rcases L.rounds with h | h <;> rw [h]
    rw [hr] at out
    rw [Spec.GcmSiv.ctxCiph, out, Spec.GcmSiv.aes, Proof.Cmac.bytesAt_length, hr, hm₁]

/-! ## `hkey` -/

/-- GHASH's key from the words `w₀`–`w₃` of the authentication key, as
`hkey` computes its four words, the most significant first. -/
abbrev hk3 (w₀ w₃ : BitVec 32) : BitVec 32 := (w₃ >>> 1) ^^^ ((0#32 - (w₀ &&& 1#32)) &&& 0xE1000000#32)
abbrev hkW (lo hi : BitVec 32) : BitVec 32 := (lo >>> 1) ||| (hi &&& 1#32).rotateRight 1

/-- The memory `hkey` leaves. -/
def hkeyMem (m : Mem) (W : Addr) : Mem :=
  let w₀ := m.readW (W + BitVec.ofNat 64 16) 32
  let w₁ := m.readW (W + BitVec.ofNat 64 20) 32
  let w₂ := m.readW (W + BitVec.ofNat 64 24) 32
  let w₃ := m.readW (W + BitVec.ofNat 64 28) 32
  Proof.Cmac.zero4 ((((m.writeW (W + BitVec.ofNat 64 76) (bswap (VG.Proof.AesGcmSiv.X86.hkW w₀ w₁))).writeW (W + BitVec.ofNat 64 72)
    (bswap (VG.Proof.AesGcmSiv.X86.hkW w₁ w₂))).writeW (W + BitVec.ofNat 64 68) (bswap (VG.Proof.AesGcmSiv.X86.hkW w₂ w₃))).writeW (W + BitVec.ofNat 64 64)
    (bswap (VG.Proof.AesGcmSiv.X86.hk3 w₀ w₃))) (W + BitVec.ofNat 64 80)

theorem hkeyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 64, 32⟩] m (VG.Proof.AesGcmSiv.X86.hkeyMem m W) := by
  have c : ∀ d, 64 ≤ d → d + 4 ≤ 96 → (⟨W + BitVec.ofNat 64 64, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d)
      (32 / 8) := fun d h₁ h₂ => Offset.contains W (by omega) (by omega) (by omega)
  have m₀ : (⟨W + BitVec.ofNat 64 64, 32⟩ : Region) ∈ [(⟨W + BitVec.ofNat 64 64, 32⟩ : Region)] :=
    List.mem_singleton_self _
  exact (((((Frame.refl _ _).writeW m₀ _ (c 76 (by decide) (by decide))).writeW m₀ _
    (c 72 (by decide) (by decide))).writeW m₀ _ (c 68 (by decide) (by decide))).writeW m₀ _
    (c 64 (by decide) (by decide))).trans ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩)

theorem bswap_bswap (a : BitVec 32) : bswap (bswap a) = a := Proof.Cmac.byteRev32_byteRev32 a

theorem hkeyMem_key (m : Mem) (W : Addr) :
    Spec.Gcm.blockAt (VG.Proof.AesGcmSiv.X86.hkeyMem m W) (W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt m (W + BitVec.ofNat 64 16) 16)) := by
  rw [VG.Proof.AesGcmSiv.X86.hkeyMem, Proof.Cmac.zero4, Proof.AesGcm.X86.blockAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)), VG.Proof.AesGcmSiv.X86.blockAt_bswap]
  simp (disch := decide) only [Nat.reduceAdd, Mem.readW_writeW_self32, readW_writeW_off, VG.Proof.AesGcmSiv.X86.bswap_bswap, VG.Proof.AesGcmSiv.X86.hkW, VG.Proof.AesGcmSiv.X86.hk3,
    VG.Proof.AesGcmSiv.X86.ror_and1]
  rw [GcmSiv.Words32.hkeyOf_words, GcmSiv.Words32.ofBytes_bytesAt, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc,
    VG.Proof.AesGcmSiv.X86.add_ofNat_assoc]

theorem hkeyMem_acc (m : Mem) (W : Addr) : Spec.Gcm.blockAt (VG.Proof.AesGcmSiv.X86.hkeyMem m W) (W + BitVec.ofNat 64 80) = 0 := by
  rw [VG.Proof.AesGcmSiv.X86.hkeyMem, Proof.Cmac.zero4, Spec.Gcm.blockAt, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_zero]
  decide

/-- `hkey`: GHASH's key at `W + 64` and its accumulator zeroed at `W + 80`. -/
theorem hkey_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) :
    ∃ t' : State, runBlock isa hkey t = some t' ∧ t'.mem = VG.Proof.AesGcmSiv.X86.hkeyMem t.mem (w64 p.W) ∧
      t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧ t'.gpr .esi = t.gpr .esi ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hz := zero4_fold ((((t.mem.writeW (w64 p.W + BitVec.ofNat 64 76)
      (bswap (VG.Proof.AesGcmSiv.X86.hkW (t.mem.readW (w64 p.W + BitVec.ofNat 64 16) 32) (t.mem.readW (w64 p.W + BitVec.ofNat 64 20) 32)))).writeW
      (w64 p.W + BitVec.ofNat 64 72)
      (bswap (VG.Proof.AesGcmSiv.X86.hkW (t.mem.readW (w64 p.W + BitVec.ofNat 64 20) 32) (t.mem.readW (w64 p.W + BitVec.ofNat 64 24) 32)))).writeW
      (w64 p.W + BitVec.ofNat 64 68)
      (bswap (VG.Proof.AesGcmSiv.X86.hkW (t.mem.readW (w64 p.W + BitVec.ofNat 64 24) 32) (t.mem.readW (w64 p.W + BitVec.ofNat 64 28) 32)))).writeW
      (w64 p.W + BitVec.ofNat 64 64)
      (bswap (VG.Proof.AesGcmSiv.X86.hk3 (t.mem.readW (w64 p.W + BitVec.ofNat 64 16) 32) (t.mem.readW (w64 p.W + BitVec.ofNat 64 28) 32))))
    p.W 80
  simp only [Nat.reduceAdd] at hz
  refine ⟨_, by simp only [hkey, hkeyW, zero4]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [VG.Proof.AesGcmSiv.X86.hkeyMem, hz]
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []
  all_goals rfl

/-! ## `keys` -/

/-- What `keys` writes: the keys, GHASH's key and accumulator, the blocks
the calls use and the index, the encryption key's schedule, the working
spaces and the stack below `SP`. -/
abbrev keyR (p : VG.Proof.AesGcmSiv.X86.Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 16, 112⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, ⟨w64 p.W + BitVec.ofNat 64 224, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 512, 2304⟩, VG.Proof.AesGcmSiv.X86.stk p]

theorem inMut_keyR (p : VG.Proof.AesGcmSiv.X86.Prm) : VG.Proof.AesGcmSiv.X86.InMut p (VG.Proof.AesGcmSiv.X86.keyR p) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide))
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact VG.Proof.AesGcmSiv.X86.inMut_stk p

/-- What `keys` leaves, from `σ`. -/
structure KeysPost (p : VG.Proof.AesGcmSiv.X86.Prm) (σ t : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  esi : t.gpr .esi = σ.gpr .esi
  frame : Frame (VG.Proof.AesGcmSiv.X86.keyR p) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (w64 p.K) p.R) (Spec.GcmSiv.keyLen p.R)
    (bytesAt σ.mem (w64 p.N) 12)).1 = bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) 16
  ciph : Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = Spec.GcmSiv.aes
    (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (w64 p.K) p.R) (Spec.GcmSiv.keyLen p.R)
      (bytesAt σ.mem (w64 p.N) 12)).2
  hkey : Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 64) =
    hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 80) = 0

theorem keys_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {σ : State} (E : VG.Proof.AesGcmSiv.X86.Env p σ) :
    WP isa (VG.Impl.AesGcmSiv.X86.keys v.callees) σ (VG.Proof.AesGcmSiv.X86.KeysPost p σ) := by
  have hR := L.rounds
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.derive_ok v L E) fun t₂ I => ?_)
  have k0 : (⟨w64 p.W + BitVec.ofNat 64 16, 112⟩ : Region) ∈ VG.Proof.AesGcmSiv.X86.keyR p := List.mem_cons_self
  have k1 : (⟨w64 p.W + BitVec.ofNat 64 176, 8⟩ : Region) ∈ VG.Proof.AesGcmSiv.X86.keyR p := by simp
  have k2 : (⟨w64 p.W + BitVec.ofNat 64 224, 16⟩ : Region) ∈ VG.Proof.AesGcmSiv.X86.keyR p := by simp
  have k3 : (⟨w64 p.W + BitVec.ofNat 64 512, 2304⟩ : Region) ∈ VG.Proof.AesGcmSiv.X86.keyR p := by simp
  have k4 : VG.Proof.AesGcmSiv.X86.stk p ∈ VG.Proof.AesGcmSiv.X86.keyR p := by simp
  have f₂ : Frame (VG.Proof.AesGcmSiv.X86.keyR p) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k1, fun _ h => h⟩
    · exact ⟨_, k2, fun _ h => h⟩
    · exact ⟨_, k3, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k4, fun _ h => h⟩
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.expand_ok v L I.env) fun t₃ X => ?_)
  obtain ⟨t₄, run₄, hm₄, ebp₄, esp₄, esi₄, rd₄, wr₄⟩ := VG.Proof.AesGcmSiv.X86.hkey_ok L X.env
  have dK : ∀ {d k : Nat}, d + k ≤ 64 → 16 ≤ d → ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 512, 240⟩ : Region),
      ⟨w64 p.W + BitVec.ofNat 64 768, 512⟩, VG.Proof.AesGcmSiv.X86.stk p],
      (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.bw' (by omega)).symm
  have f₃ : Frame (VG.Proof.AesGcmSiv.X86.keyR p) t₂.mem t₃.mem := X.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, k3, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k3, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k4, fun _ h => h⟩
  have f₄' : Frame [⟨w64 p.W + BitVec.ofNat 64 64, 32⟩] t₃.mem t₄.mem := by rw [hm₄]; exact VG.Proof.AesGcmSiv.X86.hkeyMem_frame _ _
  have f₄ : Frame (VG.Proof.AesGcmSiv.X86.keyR p) t₃.mem t₄.mem := f₄'.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
  have dH : ∀ {d k : Nat}, d + k ≤ 64 → ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl h) (by omega) (by decide)
  have dH' : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨w64 p.W + BitVec.ofNat 64 512, 240⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  have keys := I.keys L
  have a₃ : bytesAt t₃.mem (w64 p.W + BitVec.ofNat 64 16) 16 = bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86.bytesAt_frame X.frame (dK (by decide) (by decide)) (by decide)
  have a₄ : bytesAt t₄.mem (w64 p.W + BitVec.ofNat 64 16) 16 = bytesAt t₃.mem (w64 p.W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86.bytesAt_frame f₄' (dH (by decide)) (by decide)
  have E₄ : VG.Proof.AesGcmSiv.X86.Env p t₄ := X.env.mut L ebp₄ esp₄ rd₄ wr₄ (VG.Proof.AesGcmSiv.X86.frame_toMut f₄ (VG.Proof.AesGcmSiv.X86.inMut_keyR p))
  refine WP.of_runBlock ⟨t₄, run₄, E₄, by rw [rd₄, X.rd, I.rd], by rw [wr₄, X.wr, I.wr],
    by rw [esi₄, X.esi, I.esi], (f₂.trans f₃).trans f₄, ?_, ?_, ?_, ?_⟩
  · rw [keys, a₄, a₃]
  · have hk := keys
    rw [Prod.ext_iff] at hk
    rw [hk.2, ← X.ciph]
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame f₄' (fun r hr =>
      (dH' r hr).sub_left (Region.sub_prefix L.rounds_le)) (by omega)]
  · rw [hm₄, VG.Proof.AesGcmSiv.X86.hkeyMem_key, ← hm₄, a₄]
  · rw [hm₄]; exact VG.Proof.AesGcmSiv.X86.hkeyMem_acc _ _

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Absorb`. -/
section

/-!
# AES-GCM-SIV on x86: POLYVAL (`chunk`)

Untrusted: everything here is checked by Lean. POLYVAL is GHASH with the
key `H · x` on the same bits (`Proof.GcmSiv.Polyval`): `revLoop` copies up
to 64 blocks to `W + 768` with the bytes of each reversed, so that GHASH
reads each copy as POLYVAL reads the original (`revLoop_ok`), and `vg_ghash`
absorbs them (`chunk_ok`); chunks follow each other until fewer than 16
bytes are left (`chunks_ok`). The pointer is in `esi`, the number of bytes
left at `W + nO` and the number of blocks of the chunk at `W + iO`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add slotv slotv_eq GcmImpl readW_writeW_off covers_off
  in_off covers_cons covers_nil sub_beq32)

/-! ## Reversing blocks -/

/-- The body of `revLoop`. -/
abbrev revBody : List Instr :=
  [.mov .eax (.mem (at_ .esi 12)), .bswap .eax, .store (at_ .edx 0) .eax,
    .mov .eax (.mem (at_ .esi 8)), .bswap .eax, .store (at_ .edx 4) .eax, .mov .eax (.mem (at_ .esi 4)),
    .bswap .eax, .store (at_ .edx 8) .eax, .mov .eax (.mem (at_ .esi 0)), .bswap .eax, .store (at_ .edx 12) .eax,
    .alu .add .esi (imm 16), .alu .add .edx (imm 16), .alu .sub .ecx (imm 1)]

/-- What one step of `revLoop` stores: the words of the block at `S` in the
other order, each byte-reversed. -/
def revMem (m : Mem) (S P : Addr) : Mem :=
  Proof.Cmac.store4 m P (bswap (m.readW (S + BitVec.ofNat 64 12) 32)) (bswap (m.readW (S + BitVec.ofNat 64 8) 32))
    (bswap (m.readW (S + BitVec.ofNat 64 4) 32)) (bswap (m.readW (S + BitVec.ofNat 64 0) 32))

theorem ofNat_sub1 {j : Nat} (hj : j + 1 < 2 ^ 32) :
    BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 1 = BitVec.ofNat 32 j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat32 hj, toNat_ofNat32 (by decide), toNat_ofNat32 (by omega)]
  omega

theorem revStep_ok {t : State} {S P : BitVec 32} {j : Nat} (hj : j + 1 < 2 ^ 32)
    (fS : S.toNat + 16 ≤ 2 ^ 32) (fP : P.toNat + 16 ≤ 2 ^ 32)
    (hsp : (⟨w64 S, 16⟩ : Region).Disjoint ⟨w64 P, 16⟩)
    (hsi : t.gpr .esi = S) (hdx : t.gpr .edx = P) (hcx : t.gpr .ecx = BitVec.ofNat 32 (j + 1))
    (hr : Covers [⟨w64 S, 16⟩] (t.rd ++ t.wr)) (hw : Covers [⟨w64 P, 16⟩] t.wr) :
    ∃ t' : State, runBlock isa VG.Proof.AesGcmSiv.X86.revBody t = some t' ∧ t'.mem = VG.Proof.AesGcmSiv.X86.revMem t.mem (w64 S) (w64 P) ∧
      t'.gpr .esi = S + BitVec.ofNat 32 16 ∧ t'.gpr .edx = P + BitVec.ofNat 32 16 ∧
      t'.gpr .ecx = BitVec.ofNat 32 j ∧ t'.zf = some (decide (j = 0)) ∧ t'.gpr .ebp = t.gpr .ebp ∧
      t'.gpr .esp = t.gpr .esp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have aS : ∀ {o}, o < 16 → w64 (S + BitVec.ofNat 32 o) = w64 S + BitVec.ofNat 64 o := fun ho => w64_add (by omega)
  have aP : ∀ {o}, o < 16 → w64 (P + BitVec.ofNat 32 o) = w64 P + BitVec.ofNat 64 o := fun ho => w64_add (by omega)
  have rS : ∀ {o}, o + 4 ≤ 16 → InRegions (t.rd ++ t.wr) (w64 S + BitVec.ofNat 64 o) 4 :=
    fun ho => in_off hr ho (by decide)
  have wP : ∀ {o}, o + 4 ≤ 16 → InRegions t.wr (w64 P + BitVec.ofNat 64 o) 4 :=
    fun ho => in_off hw ho (by decide)
  have sep : ∀ (m : Mem) (v : BitVec 32) {a b : Nat}, a + 4 ≤ 16 → b + 4 ≤ 16 →
      (m.writeW (w64 P + BitVec.ofNat 64 a) v).readW (w64 S + BitVec.ofNat 64 b) 32 =
        m.readW (w64 S + BitVec.ofNat 64 b) 32 := fun m v a b ha hb =>
    Proof.Cmac.readW_writeW_disj _ (hsp.symm.sub_left (Offset.sub_base _ ha) |>.sub_right (Offset.sub_base _ hb))
  refine ⟨_, by grun [hsi, hdx, hcx, aS, aP, rS, wP, sep], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hsi, hdx, sep, VG.Proof.AesGcmSiv.X86.revMem, Proof.Cmac.store4, BitVec.add_zero]
  · gregs [hsi]
  · gregs [hdx]
  · gregs [hcx, VG.Proof.AesGcmSiv.X86.ofNat_sub1 hj]
  · gmems [hcx, VG.Proof.AesGcmSiv.X86.ofNat_sub1 hj]
    rw [show BitVec.ofNat 32 j = BitVec.ofNat 32 j - BitVec.ofNat 32 0 by simp, sub_beq32 (by omega) (by decide)]
  · gregs []
  · gregs []
  all_goals rfl

theorem blocksAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Gcm.blocksAt m p (j + 1) = Spec.Gcm.blocksAt m p j ++ [Spec.Gcm.blockAt m (p + BitVec.ofNat 64 (16 * j))] := by
  simp [Spec.Gcm.blocksAt, List.range_succ]

/-- The block `revMem` stores, as GHASH reads it: POLYVAL's field element of
the source. -/
theorem revMem_block (m : Mem) (S P : Addr) :
    Spec.Gcm.blockAt (VG.Proof.AesGcmSiv.X86.revMem m S P) P = Spec.GcmSiv.ofBytes (bytesAt m S 16) := by
  have b := VG.Proof.AesGcmSiv.X86.blockAt_bswap (VG.Proof.AesGcmSiv.X86.revMem m S P) P 0
  rw [BitVec.add_zero] at b
  rw [b, VG.Proof.AesGcmSiv.X86.revMem, Proof.Cmac.store4]
  simp (disch := decide) only [Nat.reduceAdd, BitVec.add_zero, Mem.readW_writeW_self32, readW_writeW_off,
    VG.Proof.AesGcmSiv.X86.bswap_bswap]
  have dj : ∀ {x y : Nat}, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 16 → y + 4 ≤ 16 →
      (⟨P + BitVec.ofNat 64 x, 4⟩ : Region).Disjoint ⟨P + BitVec.ofNat 64 y, 4⟩ :=
    fun h hx hy => Offset.disjoint P h (by omega) (by omega)
  have d₀ : ∀ y, 4 ≤ y → y + 4 ≤ 16 → (⟨P, 4⟩ : Region).Disjoint ⟨P + BitVec.ofNat 64 y, 4⟩ := fun y h₁ h₂ => by
    simpa using dj (x := 0) (y := y) (.inl h₁) (by decide) h₂
  simp only [Proof.Cmac.readW_writeW_disj _ (dj (x := 12) (y := 8) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ (dj (x := 12) (y := 4) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ (dj (x := 8) (y := 4) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ (d₀ 4 (by decide) (by decide)).symm,
    Proof.Cmac.readW_writeW_disj _ (d₀ 8 (by decide) (by decide)).symm,
    Proof.Cmac.readW_writeW_disj _ (d₀ 12 (by decide) (by decide)).symm, Mem.readW_writeW_self32, VG.Proof.AesGcmSiv.X86.bswap_bswap,
    BitVec.add_zero]
  rw [GcmSiv.Words32.ofBytes_bytesAt]

/-- POLYVAL's field elements of the `k` blocks at `Q`. -/
abbrev elemsAt (m : Mem) (Q : Addr) (k : Nat) : List Spec.GcmSiv.Elem :=
  (List.range k).map fun i => Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * i)) 16)

/-- What a chunk may read: `k` bytes at `Q` apart from what it writes. -/
structure Src (p : VG.Proof.AesGcmSiv.X86.Prm) (s : State) (Q : BitVec 32) (k : Nat) : Prop where
  rd : Covers [⟨w64 Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 32
  y : (⟨w64 Q, k⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 80, 16⟩
  v : (⟨w64 Q, k⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 176, 8⟩
  rev : (⟨w64 Q, k⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 768, 1280⟩
  stk : (VG.Proof.AesGcmSiv.X86.stk p).Disjoint ⟨w64 Q, k⟩

namespace Src

variable {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} {Q : BitVec 32} {n : Nat} (h : VG.Proof.AesGcmSiv.X86.Src p s Q n)
include h

theorem lt : n < 2 ^ 64 := by have := h.wrap; omega

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcmSiv.X86.Src p s' Q n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem addr {j : Nat} (hj : j < n) : w64 (Q + BitVec.ofNat 32 j) = w64 Q + BitVec.ofNat 64 j :=
  w64_add (by have := h.wrap; omega)

theorem toNat_add {j : Nat} (hj : j < n) : (Q + BitVec.ofNat 32 j).toNat = Q.toNat + j :=
  toNat_add32 (by have := h.wrap; omega)

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcmSiv.X86.Src p s Q k where
  rd := VG.Proof.AesGcmSiv.X86.covers_prefix h.rd hk
  wrap := by have := h.wrap; omega
  y := h.y.sub_left (Region.sub_prefix hk)
  v := h.v.sub_left (Region.sub_prefix hk)
  rev := h.rev.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`, for `a < n`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) (ha : a < n) : VG.Proof.AesGcmSiv.X86.Src p s (Q + BitVec.ofNat 32 a) k := by
  have e := h.addr ha
  have hs : Region.Sub ⟨w64 Q + BitVec.ofNat 64 a, k⟩ ⟨w64 Q, n⟩ := Offset.sub_base _ hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact covers_off h.rd hk h.lt
  · rw [h.toNat_add ha]; have := h.wrap; omega
  · rw [e]; exact h.y.sub_left hs
  · rw [e]; exact h.v.sub_left hs
  · rw [e]; exact h.rev.sub_left hs
  · rw [e]; exact h.stk.sub_right hs

end Src

/-- The block at `W + 224` as a chunk's source. -/
theorem srcB {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} (L : VG.Proof.AesGcmSiv.X86.Lay p) (P : VG.Proof.AesGcmSiv.X86.Perm p s) : VG.Proof.AesGcmSiv.X86.Src p s (p.W + BitVec.ofNat 32 224) 16 where
  rd := by rw [L.aW (by decide)]; exact P.wCR (by decide)
  wrap := by rw [L.nW (by decide)]; have := L.ww; omega
  y := by rw [L.aW (by decide)]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  v := by rw [L.aW (by decide)]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  rev := by rw [L.aW (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  stk := by rw [L.aW (by decide)]; exact L.bw' (by decide)

/-- A buffer apart from `W` and the stack as a chunk's source. -/
theorem srcBuf {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} {Q : BitVec 32} {k : Nat} (hr : Covers [⟨w64 Q, k⟩] (s.rd ++ s.wr))
    (hwrap : Q.toNat + k ≤ 2 ^ 32) (hw : (⟨w64 Q, k⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩)
    (hb : (VG.Proof.AesGcmSiv.X86.stk p).Disjoint ⟨w64 Q, k⟩) : VG.Proof.AesGcmSiv.X86.Src p s Q k :=
  ⟨hr, hwrap, hw.sub_right (Lay.wSub (by decide)), hw.sub_right (Lay.wSub (by decide)),
    hw.sub_right (Lay.wSub (by decide)), hb⟩

/-- What `revLoop` leaves after `j` blocks, from `t₀`. -/
structure RInv (p : VG.Proof.AesGcmSiv.X86.Prm) (Q : BitVec 32) (c j : Nat) (t₀ t : State) : Prop where
  esi : t.gpr .esi = Q + BitVec.ofNat 32 (16 * j)
  edx : t.gpr .edx = p.W + BitVec.ofNat 32 (768 + 16 * j)
  ecx : t.gpr .ecx = BitVec.ofNat 32 (c - j)
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 768, 16 * c⟩] t₀.mem t.mem
  out : Spec.Gcm.blocksAt t.mem (w64 p.W + BitVec.ofNat 64 768) j = VG.Proof.AesGcmSiv.X86.elemsAt t₀.mem (w64 Q) j
  ebp : t.gpr .ebp = t₀.gpr .ebp
  esp : t.gpr .esp = t₀.gpr .esp
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr

theorem add32_ofNat_assoc (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `revLoop`: `c` blocks at `Q` copied to `W + 768`, each reversed, so that
GHASH reads POLYVAL's field elements of them. -/
theorem revLoop_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t₀ : State} (E : VG.Proof.AesGcmSiv.X86.Env p t₀) {Q : BitVec 32} {c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 64) (hQ : VG.Proof.AesGcmSiv.X86.Src p t₀ Q (16 * c)) (hsi : t₀.gpr .esi = Q)
    (hdx : t₀.gpr .edx = p.W + BitVec.ofNat 32 768) (hcx : t₀.gpr .ecx = BitVec.ofNat 32 c) :
    WP isa revLoop t₀ fun t => Frame [⟨w64 p.W + BitVec.ofNat 64 768, 16 * c⟩] t₀.mem t.mem ∧
      Spec.Gcm.blocksAt t.mem (w64 p.W + BitVec.ofNat 64 768) c = VG.Proof.AesGcmSiv.X86.elemsAt t₀.mem (w64 Q) c ∧
      t.gpr .esi = Q + BitVec.ofNat 32 (16 * c) ∧ t.gpr .ebp = t₀.gpr .ebp ∧ t.gpr .esp = t₀.gpr .esp ∧
      t.rd = t₀.rd ∧ t.wr = t₀.wr := by
  have hw := L.ww
  have I₀ : VG.Proof.AesGcmSiv.X86.RInv p Q c 0 t₀ t₀ := ⟨by rw [hsi, Nat.mul_zero, BitVec.add_zero], by rw [hdx],
    by rw [hcx, Nat.sub_zero], Frame.refl _ _, by simp only [Spec.Gcm.blocksAt, VG.Proof.AesGcmSiv.X86.elemsAt, List.range_zero, List.map_nil],
    rfl, rfl, rfl, rfl⟩
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcmSiv.X86.revBody) (c := .ne)
    (fun (m : Nat) (t : State) => ∃ j, m = c - j ∧ j < c ∧ VG.Proof.AesGcmSiv.X86.RInv p Q c j t₀ t) ?_ (c - 0) t₀ ⟨0, rfl, hc1, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  have eS : w64 (Q + BitVec.ofNat 32 (16 * j)) = w64 Q + BitVec.ofNat 64 (16 * j) := hQ.addr (by omega)
  have eP : w64 (p.W + BitVec.ofNat 32 (768 + 16 * j)) = w64 p.W + BitVec.ofNat 64 (768 + 16 * j) :=
    L.aW (by omega)
  have hr : Covers [⟨w64 (Q + BitVec.ofNat 32 (16 * j)), 16⟩] (t.rd ++ t.wr) := by
    rw [I.rd, I.wr, eS]; exact covers_off hQ.rd (by omega) hQ.lt
  have hwr : Covers [⟨w64 (p.W + BitVec.ofNat 32 (768 + 16 * j)), 16⟩] t.wr := by
    rw [I.wr, eP]; exact E.perm.wC (by omega)
  have hsep : (⟨w64 (Q + BitVec.ofNat 32 (16 * j)), 16⟩ : Region).Disjoint
      ⟨w64 (p.W + BitVec.ofNat 32 (768 + 16 * j)), 16⟩ := by
    rw [eS, eP]
    exact (hQ.rev.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub _ (by omega) (by omega))
  obtain ⟨t', run', hm', si', dx', cx', z', bp', sp', rd', wr'⟩ :=
    VG.Proof.AesGcmSiv.X86.revStep_ok (j := c - j - 1) (by omega) (by rw [hQ.toNat_add (by omega)]; have := hQ.wrap; omega)
      (by rw [L.nW (by omega)]; omega) hsep I.esi I.edx (by rw [I.ecx]; congr 1; omega) hr hwr
  refine WP.of_runBlock ⟨t', run', ?_⟩
  rw [eS, eP] at hm'
  -- The source is outside the copies.
  have src : bytesAt t.mem (w64 Q + BitVec.ofNat 64 (16 * j)) 16 =
      bytesAt t₀.mem (w64 Q + BitVec.ofNat 64 (16 * j)) 16 :=
    Proof.AesGcm.X86.bytesAt_frame I.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hQ.rev.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub _ (by omega) (by omega)))
      (by decide)
  have fr : Frame [⟨w64 p.W + BitVec.ofNat 64 (768 + 16 * j), 16⟩] t.mem t'.mem := by
    rw [hm', VG.Proof.AesGcmSiv.X86.revMem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have I' : VG.Proof.AesGcmSiv.X86.RInv p Q c (j + 1) t₀ t' := by
    refine ⟨by rw [si', VG.Proof.AesGcmSiv.X86.add32_ofNat_assoc, Nat.mul_succ], by rw [dx', VG.Proof.AesGcmSiv.X86.add32_ofNat_assoc, Nat.mul_succ,
      Nat.add_assoc], by rw [cx', Nat.sub_sub], ?_, ?_, by rw [bp', I.ebp], by rw [sp', I.esp], by rw [rd', I.rd],
      by rw [wr', I.wr]⟩
    · exact I.frame.trans (fr.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩)
    · rw [VG.Proof.AesGcmSiv.X86.blocksAt_succ, Proof.AesGcm.X86.blocksAt_frame fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by omega), I.out]
      simp only [VG.Proof.AesGcmSiv.X86.elemsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, hm', VG.Proof.AesGcmSiv.X86.revMem_block, src]
  have ev := VG.Proof.AesGcmSiv.X86.eval_ne z'
  by_cases he : j + 1 = c
  · left
    refine ⟨ev.trans (by simp [show c - j - 1 = 0 by omega]), ?_⟩
    exact ⟨I'.frame, he ▸ I'.out, he ▸ I'.esi, I'.ebp, I'.esp, I'.rd, I'.wr⟩
  · right
    exact ⟨ev.trans (by simp; omega), c - (j + 1), by omega, j + 1, rfl, by omega, I'⟩


/-! ## A chunk -/

/-- What a chunk writes: GHASH's accumulator, the variables, the reversed
blocks and `vg_ghash`'s working space, and the stack below `SP`. -/
abbrev absR (p : VG.Proof.AesGcmSiv.X86.Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 80, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 1280⟩,
    VG.Proof.AesGcmSiv.X86.stk p]

theorem inMut_absR (p : VG.Proof.AesGcmSiv.X86.Prm) : VG.Proof.AesGcmSiv.X86.InMut p (VG.Proof.AesGcmSiv.X86.absR p) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide))
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact VG.Proof.AesGcmSiv.X86.inMut_stk p

/-- What a chunk leaves, from `t`, after absorbing `k` blocks of the `m`
bytes at `Q`. -/
structure ChunkPost (p : VG.Proof.AesGcmSiv.X86.Prm) (Q : BitVec 32) (m k : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  esi : t'.gpr .esi = Q + BitVec.ofNat 32 (16 * k)
  n : slotv t'.mem p.W nO = BitVec.ofNat 32 (m - 16 * k)
  z : t'.zf = some (decide ((m - 16 * k) / 16 = 0))
  frame : Frame (VG.Proof.AesGcmSiv.X86.absR p) t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (w64 p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 80)) (VG.Proof.AesGcmSiv.X86.elemsAt t.mem (w64 Q) k)

/-- `chunkLen`'s first block: `nO / 16` compared with 64. -/
theorem chunkLen1_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {m : Nat} (hm : m < 2 ^ 32)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    ∃ t₁, runBlock isa [.mov .ecx (slot nO), .shift .shr .ecx 4, .alu .cmp .ecx (imm 64)] t = some t₁ ∧
      t₁.gpr .ecx = BitVec.ofNat 32 (m / 16) ∧ t₁.cf = some (decide (m / 16 < 64)) ∧ t₁.gpr .ebp = p.W ∧
      t₁.gpr .esp = p.SP ∧ t₁.gpr .esi = t.gpr .esi ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧ t₁.mem = t.mem := by
  simp only [slotv_eq, nO] at hn
  refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gregs [hn, VG.Proof.AesGcmSiv.X86.ofNat_lsr32 hm]
  · gmems [hn, VG.Proof.AesGcmSiv.X86.ofNat_lsr32 hm]
    rw [toNat_ofNat32 (by omega), toNat_ofNat32 (by decide)]
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []
  all_goals gmems []

/-- `chunkLen`: the number of blocks of the chunk, in `ecx` and at `W + iO`. -/
theorem chunkLen_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {m : Nat} (hm : m < 2 ^ 32)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    WP isa chunkLen t fun t' => VG.Proof.AesGcmSiv.X86.Env p t' ∧ t'.gpr .ecx = BitVec.ofNat 32 (min (m / 16) 64) ∧
      slotv t'.mem p.W iO = BitVec.ofNat 32 (min (m / 16) 64) ∧ slotv t'.mem p.W nO = BitVec.ofNat 32 m ∧
      t'.gpr .esi = t.gpr .esi ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      Frame [⟨w64 p.W + BitVec.ofNat 64 180, 4⟩] t.mem t'.mem := by
  obtain ⟨t₁, run₁, cx₁, cf₁, bp₁, sp₁, si₁, rd₁, wr₁, m₁⟩ := VG.Proof.AesGcmSiv.X86.chunkLen1_ok L E hm hn
  simp only [slotv_eq, nO] at hn
  have E₁ : VG.Proof.AesGcmSiv.X86.Env p t₁ := E.keep (by rw [bp₁, E.ebp]) (by rw [sp₁, E.esp]) rd₁ wr₁ m₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- `ecx := min (m / 16, 64)`, by the branch.
  have hk : ∀ t₂ : State, t₂.gpr .ecx = BitVec.ofNat 32 (min (m / 16) 64) → VG.Proof.AesGcmSiv.X86.Env p t₂ → t₂.gpr .esi = t.gpr .esi →
      t₂.rd = t.rd → t₂.wr = t.wr → t₂.mem = t.mem →
      WP isa (.block [.store (at_ .ebp iO) .ecx]) t₂ fun t' => VG.Proof.AesGcmSiv.X86.Env p t' ∧
        t'.gpr .ecx = BitVec.ofNat 32 (min (m / 16) 64) ∧
        slotv t'.mem p.W iO = BitVec.ofNat 32 (min (m / 16) 64) ∧ slotv t'.mem p.W nO = BitVec.ofNat 32 m ∧
        t'.gpr .esi = t.gpr .esi ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
        Frame [⟨w64 p.W + BitVec.ofNat 64 180, 4⟩] t.mem t'.mem := by
    intro t₂ cx₂ E₂ si₂ rd₂ wr₂ m₂
    have f : Frame [⟨w64 p.W + BitVec.ofNat 64 180, 4⟩] t₂.mem
        (t₂.mem.writeW (w64 p.W + BitVec.ofNat 64 180) (BitVec.ofNat 32 (min (m / 16) 64))) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have fm := VG.Proof.AesGcmSiv.X86.frame_toMut f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
    refine WP.of_runBlock ⟨_, by grun [E₂.ebp, L.aW, E₂.perm.wW, cx₂], ?_⟩
    refine ⟨E₂.mut L (by gregs [E₂.ebp]) (by gregs [E₂.esp]) (by gmems []) (by gmems []) (by gmems []; exact fm),
      by gregs [cx₂], by gmems [slotv_eq], by gmems [slotv_eq, m₂, hn], by gregs [si₂], by gmems [rd₂],
      by gmems [wr₂], by gmems []; rw [← m₂]; exact f⟩
  refine WP.seq (WP.ite (decide (m / 16 < 64)) (VG.Proof.AesGcmSiv.X86.eval_b cf₁) (fun ht => ?_) (fun hf => ?_))
  · refine WP.of_runBlock ⟨t₁, rfl, ?_⟩
    have h : m / 16 < 64 := by simpa using ht
    exact hk t₁ (by rw [cx₁]; congr 1; omega) E₁ si₁ rd₁ wr₁ m₁
  · have h : ¬ m / 16 < 64 := by simpa using hf
    obtain ⟨t₂, run₂, cx₂, bp₂, sp₂, si₂, rd₂, wr₂, m₂⟩ : ∃ t₂, runBlock isa [.mov .ecx (imm 64)] t₁ = some t₂ ∧
        t₂.gpr .ecx = BitVec.ofNat 32 64 ∧ t₂.gpr .ebp = p.W ∧ t₂.gpr .esp = p.SP ∧ t₂.gpr .esi = t₁.gpr .esi ∧
        t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr ∧ t₂.mem = t₁.mem :=
      ⟨_, by grun [], by gregs [], by gregs [bp₁], by gregs [sp₁], by gregs [], by gmems [], by gmems [], by gmems []⟩
    refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
    exact hk t₂ (by rw [cx₂]; congr 1; omega) (E₁.keep (by rw [bp₂, bp₁]) (by rw [sp₂, sp₁]) rd₂ wr₂ m₂)
      (by rw [si₂, si₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [m₂, m₁])

/-- Four doublings. -/
theorem dbl4 (k : Nat) : BitVec.ofNat 32 k + BitVec.ofNat 32 k + (BitVec.ofNat 32 k + BitVec.ofNat 32 k) +
    (BitVec.ofNat 32 k + BitVec.ofNat 32 k + (BitVec.ofNat 32 k + BitVec.ofNat 32 k)) +
    (BitVec.ofNat 32 k + BitVec.ofNat 32 k + (BitVec.ofNat 32 k + BitVec.ofNat 32 k) +
    (BitVec.ofNat 32 k + BitVec.ofNat 32 k + (BitVec.ofNat 32 k + BitVec.ofNat 32 k))) = BitVec.ofNat 32 (16 * k) := by
  simp only [VG.Proof.AesGcmSiv.X86.ofNat_add32]; congr 1; omega

theorem ofNat_sub32 {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat32 ha, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]
  omega

/-- A chunk up to its call: up to 64 blocks reversed at `W + 768`, the
pointer and the count past them, and the arguments of `vg_ghash`. -/
structure ChunkPre (p : VG.Proof.AesGcmSiv.X86.Prm) (Q : BitVec 32) (m k : Nat) (t t₅ : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t₅
  rd : t₅.rd = t.rd
  wr : t₅.wr = t.wr
  eax : t₅.gpr .eax = p.W + BitVec.ofNat 32 64
  edx : t₅.gpr .edx = p.W + BitVec.ofNat 32 80
  ebx : t₅.gpr .ebx = p.W + BitVec.ofNat 32 768
  edi : t₅.gpr .edi = BitVec.ofNat 32 k
  esi : t₅.gpr .esi = Q + BitVec.ofNat 32 (16 * k)
  n : slotv t₅.mem p.W nO = BitVec.ofNat 32 (m - 16 * k)
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 16 * k⟩] t.mem t₅.mem
  out : Spec.Gcm.blocksAt t₅.mem (w64 p.W + BitVec.ofNat 64 768) k = VG.Proof.AesGcmSiv.X86.elemsAt t.mem (w64 Q) k

/-- The pieces of a chunk before its call. -/
theorem chunkPre_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32)
    (h16 : 16 ≤ m) (hQ : VG.Proof.AesGcmSiv.X86.Src p t Q (16 * (m / 16))) (hsi : t.gpr .esi = Q)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    WP isa chunkPre t (VG.Proof.AesGcmSiv.X86.ChunkPre p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.chunkLen_ok L E hm hn) fun t₁ ⟨E₁, cx₁, ix₁, n₁, si₁, rd₁, wr₁, f₁⟩ => ?_)
  obtain ⟨t₂, run₂, dx₂, cx₂, si₂, bp₂, sp₂, rd₂, wr₂, m₂⟩ : ∃ t₂, runBlock isa
      [.mov .edx (.reg .ebp), .alu .add .edx (imm revO)] t₁ = some t₂ ∧
      t₂.gpr .edx = p.W + BitVec.ofNat 32 768 ∧ t₂.gpr .ecx = BitVec.ofNat 32 (min (m / 16) 64) ∧
      t₂.gpr .esi = Q ∧ t₂.gpr .ebp = p.W ∧ t₂.gpr .esp = p.SP ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr ∧ t₂.mem = t₁.mem :=
    ⟨_, by grun [], by gregs [E₁.ebp], by gregs [cx₁], by gregs [si₁, hsi], by gregs [E₁.ebp], by gregs [E₁.esp],
      by gmems [], by gmems [], by gmems []⟩
  refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
  have E₂ : VG.Proof.AesGcmSiv.X86.Env p t₂ := E₁.keep (by rw [bp₂, E₁.ebp]) (by rw [sp₂, E₁.esp]) rd₂ wr₂ m₂
  have hk1 : 1 ≤ min (m / 16) 64 := by omega
  have hd₁ : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 180, 4⟩ : Region)],
      (⟨w64 Q, 16 * min (m / 16) 64⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hQ.v.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub _ (by decide) (by decide))
  have hQ₂ : VG.Proof.AesGcmSiv.X86.Src p t₂ Q (16 * min (m / 16) 64) :=
    (hQ.take (by omega)).of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.revLoop_ok L E₂ hk1 (by omega) hQ₂ si₂ dx₂ cx₂)
    fun t₃ ⟨fr₃, out₃, si₃, bp₃, sp₃, rd₃, wr₃⟩ => ?_)
  have dV : ∀ {d k : Nat}, 176 ≤ d → d + k ≤ 184 →
      ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 768, 16 * min (m / 16) 64⟩ : Region)],
      (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by omega)
  have E₃ : VG.Proof.AesGcmSiv.X86.Env p t₃ := E₂.mut L (by rw [bp₃, bp₂]) (by rw [sp₃, sp₂]) rd₃ wr₃ (VG.Proof.AesGcmSiv.X86.frame_toMut fr₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inr ⟨by decide, by omega⟩))))
  have ix₃ : slotv t₃.mem p.W iO = BitVec.ofNat 32 (min (m / 16) 64) := by
    rw [← ix₁, ← m₂]
    exact fr₃.readW (r := ⟨w64 p.W + BitVec.ofNat 64 180, 4⟩) (Region.contains_self _ _) (dV (by decide) (by decide))
      (by decide)
  have n₃ : slotv t₃.mem p.W nO = BitVec.ofNat 32 m := by
    rw [← n₁, ← m₂]
    exact fr₃.readW (r := ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩) (Region.contains_self _ _) (dV (by decide) (by decide))
      (by decide)
  simp only [slotv_eq, iO, nO] at ix₃ n₃
  rw [m₂] at fr₃ out₃
  have eQ : VG.Proof.AesGcmSiv.X86.elemsAt t₁.mem (w64 Q) (min (m / 16) 64) = VG.Proof.AesGcmSiv.X86.elemsAt t.mem (w64 Q) (min (m / 16) 64) := by
    unfold VG.Proof.AesGcmSiv.X86.elemsAt
    rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt, Proof.AesGcm.X86.bytesAt_frame f₁ hd₁ (by omega)]
  have f4 : Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t₃.mem
      (t₃.mem.writeW (w64 p.W + BitVec.ofNat 64 176) (BitVec.ofNat 32 (m - 16 * min (m / 16) 64))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨_, by simp only [chunkArgs]; grun [E₃.ebp, L.aW, E₃.perm.wW, E₃.perm.wR, ix₃, n₃], ?_⟩
  have fm4 := VG.Proof.AesGcmSiv.X86.frame_toMut f4 fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  refine ⟨E₃.mut L (by gregs [E₃.ebp]) (by gregs [E₃.esp]) (by gmems []) (by gmems [])
      (by gmems [VG.Proof.AesGcmSiv.X86.dbl4, VG.Proof.AesGcmSiv.X86.ofNat_sub32 (show 16 * min (m / 16) 64 ≤ m by omega) hm]; exact fm4),
    by gmems [rd₃, rd₂, rd₁], by gmems [wr₃, wr₂, wr₁], by gregs [E₃.ebp], by gregs [E₃.ebp], by gregs [E₃.ebp],
    by gregs [ix₃], by gregs [si₃], ?_, ?_, ?_⟩
  · gmems [slotv_eq, VG.Proof.AesGcmSiv.X86.dbl4, n₃, VG.Proof.AesGcmSiv.X86.ofNat_sub32 (show 16 * min (m / 16) 64 ≤ m by omega) hm]
  · gmems [VG.Proof.AesGcmSiv.X86.dbl4, n₃, VG.Proof.AesGcmSiv.X86.ofNat_sub32 (show 16 * min (m / 16) 64 ≤ m by omega) hm]
    refine ((f₁.sub fun r hr => ?_).trans (fr₃.sub fun r hr => ?_)).trans (f4.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
  · gmems [VG.Proof.AesGcmSiv.X86.dbl4, VG.Proof.AesGcmSiv.X86.ofNat_sub32 (show 16 * min (m / 16) 64 ≤ m by omega) hm]
    rw [Proof.AesGcm.X86.blocksAt_frame f4 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (a := 768) (n := 16 * min (m / 16) 64) (.inr (by decide)) (by omega) (by decide)) (by omega),
      out₃, eQ]

/-- `wholeLeft`: ZF set iff fewer than 16 of the `r` bytes are left. -/
theorem wholeLeft_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {r : Nat} (hr : r < 2 ^ 32)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 r) :
    ∃ t' : State, runBlock isa wholeLeft t = some t' ∧ t'.zf = some (decide (r / 16 = 0)) ∧ VG.Proof.AesGcmSiv.X86.Env p t' ∧
      t'.gpr .esi = t.gpr .esi ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  simp only [slotv_eq, nO] at hn
  refine ⟨_, by simp only [wholeLeft]; grun [E.ebp, L.aW, E.perm.wR, hn], ?_, ?_, by gregs [], by gmems [],
    by gmems [], by gmems []⟩
  · gmems [hn, VG.Proof.AesGcmSiv.X86.ofNat_lsr32 hr]
    rw [BitVec.and_self, show BitVec.ofNat 32 (r / 16) = BitVec.ofNat 32 (r / 16) - BitVec.ofNat 32 0 by simp,
      sub_beq32 (by omega) (by decide)]
  · exact E.keep (by gregs []) (by gregs []) (by gmems []) (by gmems []) (by gmems [])

theorem chunk_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ : VG.Proof.AesGcmSiv.X86.Src p t Q (16 * (m / 16))) (hsi : t.gpr .esi = Q)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    WP isa (chunk v.callees) t (VG.Proof.AesGcmSiv.X86.ChunkPost p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  have hk : min (m / 16) 64 ≤ 64 := by omega
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.chunkPre_ok L E hm h16 hQ hsi hn) fun t₅ Pr => ?_)
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.callGh_ok v L Pr.env hk Pr.eax Pr.edx Pr.ebx Pr.edi) fun t₆ P => ?_)
  have dH : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 8⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 768,
      16 * min (m / 16) 64⟩], (⟨w64 p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Lay.w_w (.inl (by omega)) (by decide) (by omega)
  have dY : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 8⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 768,
      16 * min (m / 16) 64⟩], (⟨w64 p.W + BitVec.ofNat 64 80, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Lay.w_w (.inl (by omega)) (by decide) (by omega)
  have out₆ := P.out
  rw [Proof.AesGcm.X86.blockAt_frame Pr.frame dH, Proof.AesGcm.X86.blockAt_frame Pr.frame dY, Pr.out] at out₆
  have n₆ : slotv t₆.mem p.W nO = BitVec.ofNat 32 (m - 16 * min (m / 16) 64) := by
    rw [← Pr.n]
    exact P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  obtain ⟨t₇, run₇, z₇, E₇, si₇, m₇, rd₇, wr₇⟩ := VG.Proof.AesGcmSiv.X86.wholeLeft_ok L P.env (by omega) n₆
  refine WP.of_runBlock ⟨t₇, run₇, E₇, by rw [rd₇, P.rd, Pr.rd], by rw [wr₇, P.wr, Pr.wr], ?_,
    by rw [slotv_eq, m₇]; exact n₆, z₇, ?_, by rw [m₇]; exact out₆⟩
  · rw [si₇, P.saved _ (by decide), Pr.esi]
  · rw [m₇]
    refine (Pr.frame.sub fun r hr => ?_).trans (P.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨w64 p.W + BitVec.ofNat 64 768, 1280⟩, by simp, Region.sub_prefix (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨w64 p.W + BitVec.ofNat 64 768, 1280⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-! ## Absorbing -/

theorem elemsAt_add (m : Mem) (Q : Addr) (d k : Nat) :
    VG.Proof.AesGcmSiv.X86.elemsAt m Q (d + k) = VG.Proof.AesGcmSiv.X86.elemsAt m Q d ++ VG.Proof.AesGcmSiv.X86.elemsAt m (Q + BitVec.ofNat 64 (16 * d)) k := by
  simp only [VG.Proof.AesGcmSiv.X86.elemsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, Nat.mul_add]

theorem elemsAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr} {k : Nat}
    (hd : ∀ r ∈ rs, (⟨Q, 16 * k⟩ : Region).Disjoint r) (hk : 16 * k ≤ 2 ^ 64) : VG.Proof.AesGcmSiv.X86.elemsAt m' Q k = VG.Proof.AesGcmSiv.X86.elemsAt m Q k := by
  unfold VG.Proof.AesGcmSiv.X86.elemsAt
  rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt, Proof.AesGcm.X86.bytesAt_frame hf hd hk]

/-- What absorbing writes: what a chunk writes, and the block at `W + 224`. -/
abbrev absorbR (p : VG.Proof.AesGcmSiv.X86.Prm) : List Region := ⟨w64 p.W + BitVec.ofNat 64 224, 16⟩ :: VG.Proof.AesGcmSiv.X86.absR p

theorem inMut_absorbR (p : VG.Proof.AesGcmSiv.X86.Prm) : VG.Proof.AesGcmSiv.X86.InMut p (VG.Proof.AesGcmSiv.X86.absorbR p) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact VG.Proof.AesGcmSiv.X86.inMut_absR p r hr

/-- What absorbing leaves, from `t`, having absorbed the elements `xs` and
written only `rs`. -/
structure Absorbed (p : VG.Proof.AesGcmSiv.X86.Prm) (rs : List Region) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame rs t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (w64 p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 80)) xs

/-- What absorbing a string leaves. -/
abbrev AbsPost (p : VG.Proof.AesGcmSiv.X86.Prm) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop := VG.Proof.AesGcmSiv.X86.Absorbed p (VG.Proof.AesGcmSiv.X86.absorbR p) xs t t'

theorem absorbR_H {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86.absorbR p, (⟨w64 p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.bw' (by decide)).symm

theorem absR_sub (p : VG.Proof.AesGcmSiv.X86.Prm) : ∀ r ∈ VG.Proof.AesGcmSiv.X86.absR p, ∃ r' ∈ VG.Proof.AesGcmSiv.X86.absorbR p, Region.Sub r r' :=
  fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩

theorem Absorbed.trans {p : VG.Proof.AesGcmSiv.X86.Prm} {rs : List Region} {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (hH : ∀ r ∈ rs, (⟨w64 p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r)
    (h₁ : VG.Proof.AesGcmSiv.X86.Absorbed p rs xs t t₁) (h₂ : VG.Proof.AesGcmSiv.X86.Absorbed p rs ys t₁ t₂) : VG.Proof.AesGcmSiv.X86.Absorbed p rs (xs ++ ys) t t₂ := by
  refine ⟨h₂.env, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.frame.trans h₂.frame, ?_⟩
  rw [h₂.out, h₁.out, Proof.AesGcm.X86.blockAt_frame h₁.frame hH, Proof.Gcm.ghashFrom_append]

theorem Absorbed.sub {p : VG.Proof.AesGcmSiv.X86.Prm} {rs rs' : List Region} {xs : List Spec.GcmSiv.Elem} {t t' : State}
    (h : VG.Proof.AesGcmSiv.X86.Absorbed p rs xs t t') (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : VG.Proof.AesGcmSiv.X86.Absorbed p rs' xs t t' :=
  ⟨h.env, h.rd, h.wr, h.frame.sub hs, h.out⟩

theorem Absorbed.of_chunk {p : VG.Proof.AesGcmSiv.X86.Prm} {Q : BitVec 32} {m k : Nat} {t t' : State}
    (h : VG.Proof.AesGcmSiv.X86.ChunkPost p Q m k t t') : VG.Proof.AesGcmSiv.X86.Absorbed p (VG.Proof.AesGcmSiv.X86.absR p) (VG.Proof.AesGcmSiv.X86.elemsAt t.mem (w64 Q) k) t t' :=
  ⟨h.env, h.rd, h.wr, h.frame, h.out⟩

theorem Absorbed.of_eq {p : VG.Proof.AesGcmSiv.X86.Prm} {rs : List Region} {xs : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h : VG.Proof.AesGcmSiv.X86.Absorbed p rs xs t₁ t₂) (hm : t₁.mem = t.mem) (hrd : t₁.rd = t.rd) (hwr : t₁.wr = t.wr) :
    VG.Proof.AesGcmSiv.X86.Absorbed p rs xs t t₂ :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, hm ▸ h.frame, by rw [h.out, hm]⟩

theorem absR_H {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86.absR p, (⟨w64 p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r :=
  fun r hr => VG.Proof.AesGcmSiv.X86.absorbR_H L r (List.mem_cons_of_mem _ hr)

theorem AbsPost.trans {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h₁ : VG.Proof.AesGcmSiv.X86.AbsPost p xs t t₁) (h₂ : VG.Proof.AesGcmSiv.X86.AbsPost p ys t₁ t₂) : VG.Proof.AesGcmSiv.X86.AbsPost p (xs ++ ys) t t₂ :=
  Absorbed.trans (VG.Proof.AesGcmSiv.X86.absorbR_H L) h₁ h₂

/-- The chunks of the `m` bytes at `Q`, from `σ`, after `d` blocks. -/
structure CInv (p : VG.Proof.AesGcmSiv.X86.Prm) (σ : State) (Q : BitVec 32) (m d : Nat) (t : State) : Prop where
  abs : VG.Proof.AesGcmSiv.X86.Absorbed p (VG.Proof.AesGcmSiv.X86.absR p) (VG.Proof.AesGcmSiv.X86.elemsAt σ.mem (w64 Q) d) σ t
  esi : t.gpr .esi = Q + BitVec.ofNat 32 (16 * d)
  n : slotv t.mem p.W nO = BitVec.ofNat 32 (m - 16 * d)

theorem CInv.src {p : VG.Proof.AesGcmSiv.X86.Prm} {σ t : State} {Q : BitVec 32} {m d : Nat} (I : VG.Proof.AesGcmSiv.X86.CInv p σ Q m d t)
    (hQ : VG.Proof.AesGcmSiv.X86.Src p σ Q (16 * (m / 16))) (hd : d < m / 16) :
    VG.Proof.AesGcmSiv.X86.Src p t (Q + BitVec.ofNat 32 (16 * d)) (16 * ((m - 16 * d) / 16)) :=
  (hQ.slice (by omega) (by omega)).of_eq I.abs.rd I.abs.wr

theorem CInv.zero {p : VG.Proof.AesGcmSiv.X86.Prm} {σ : State} (E : VG.Proof.AesGcmSiv.X86.Env p σ) {Q : BitVec 32} {m : Nat} (hsi : σ.gpr .esi = Q)
    (hn : slotv σ.mem p.W nO = BitVec.ofNat 32 m) : VG.Proof.AesGcmSiv.X86.CInv p σ Q m 0 σ :=
  ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [VG.Proof.AesGcmSiv.X86.elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
    by rw [hsi, Nat.mul_zero, BitVec.add_zero], by rw [hn, Nat.mul_zero, Nat.sub_zero]⟩

/-- A chunk, in the chunks. -/
theorem CInv.step {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {σ t t' : State} {Q : BitVec 32} {m d : Nat}
    (hQ : VG.Proof.AesGcmSiv.X86.Src p σ Q (16 * (m / 16))) (hd : d < m / 16) (I : VG.Proof.AesGcmSiv.X86.CInv p σ Q m d t)
    (C : VG.Proof.AesGcmSiv.X86.ChunkPost p (Q + BitVec.ofNat 32 (16 * d)) (m - 16 * d) (min ((m - 16 * d) / 16) 64) t t') :
    VG.Proof.AesGcmSiv.X86.CInv p σ Q m (d + min (m / 16 - d) 64) t' ∧
      t'.zf = some (decide (m / 16 - (d + min (m / 16 - d) 64) = 0)) := by
  have hk : min ((m - 16 * d) / 16) 64 = min (m / 16 - d) 64 := by congr 1; omega
  rw [hk] at C
  have hs := hQ.slice (a := 16 * d) (k := 16 * min (m / 16 - d) 64) (by omega) (by omega)
  have ea := hQ.addr (j := 16 * d) (by omega)
  have C' := Absorbed.of_chunk C
  rw [VG.Proof.AesGcmSiv.X86.elemsAt_frame I.abs.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hs.y
      · exact hs.v
      · exact hs.rev
      · exact hs.stk.symm) (by omega), ea] at C'
  refine ⟨⟨by rw [VG.Proof.AesGcmSiv.X86.elemsAt_add]; exact Absorbed.trans (VG.Proof.AesGcmSiv.X86.absR_H L) I.abs C', by rw [C.esi, VG.Proof.AesGcmSiv.X86.add32_ofNat_assoc, Nat.mul_add],
    by rw [C.n]; congr 1; omega⟩, by rw [C.z]; congr 2; apply propext; omega⟩

/-- The whole blocks: chunks until fewer than 16 bytes are left. -/
theorem chunks_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ : VG.Proof.AesGcmSiv.X86.Src p t Q (16 * (m / 16))) (hsi : t.gpr .esi = Q)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    WP isa (.loop (chunk v.callees) .ne) t fun t' =>
      VG.Proof.AesGcmSiv.X86.Absorbed p (VG.Proof.AesGcmSiv.X86.absR p) (VG.Proof.AesGcmSiv.X86.elemsAt t.mem (w64 Q) (m / 16)) t t' ∧
      t'.gpr .esi = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ slotv t'.mem p.W nO = BitVec.ofNat 32 (m % 16) := by
  refine WP.loop (M := isa) (body := chunk v.callees) (c := .ne)
    (fun (k : Nat) (t' : State) => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ VG.Proof.AesGcmSiv.X86.CInv p t Q m d t') ?_
    (m / 16 - 0) t ⟨0, rfl, by omega, CInv.zero E hsi hn⟩
  rintro k t' ⟨d, rfl, hd, I⟩
  refine WP.mono (VG.Proof.AesGcmSiv.X86.chunk_ok v L I.abs.env (by omega) (by omega) (I.src hQ hd) I.esi I.n) fun t'' C => ?_
  obtain ⟨I', z⟩ := I.step L hQ hd C
  have ev := VG.Proof.AesGcmSiv.X86.eval_ne z
  by_cases he : d + min (m / 16 - d) 64 = m / 16
  · left
    refine ⟨ev.trans (by simp; omega), he ▸ I'.abs, by rw [I'.esi, he], by rw [I'.n, he]; congr 1; omega⟩
  · right
    exact ⟨ev.trans (by simp; omega), m / 16 - (d + min (m / 16 - d) 64), by omega, d + min (m / 16 - d) 64, rfl,
      by omega, I'⟩

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Polyval`. -/
section

/-!
# AES-GCM-SIV on x86: POLYVAL and the tag input (`absorb`, `polyval`)

Untrusted: everything here is checked by Lean. `absorb` absorbs a string
padded with zeros (`absorb_ok`): its whole blocks by chunks, its last bytes
copied over a zero block at `W + 224` and absorbed as one more chunk
(`absTail_ok`); `lensBlock` puts the lengths block there for one more
(`lens_ok`), from the slots `alenO` and `lenO`; `tagIn` turns POLYVAL's
result into the tag input (`tagIn_ok`). `polyval_ok`: the tag input of
RFC 8452 §4, with POLYVAL as GHASH with the key `H · x`
(`Proof.GcmSiv.Words.tagInputG`), at `W + 96`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.Cmac (le4)
open VG.Proof.GcmSiv.Words (hkeyOf tagInputG)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 slotv slotv_eq GcmImpl readW_writeW_off covers_left covers_off
  zero4_fold LoopPre CopyPost copyLoop_ok length_bytesAt sub_beq32)

/-! ## The last bytes -/

/-- The last bytes copied over a zeroed block. -/
theorem pad_bytes (m : Mem) (c : Addr) (xs : List Byte) (hx : xs.length < 16) :
    bytesAt (writeBytes (Proof.Cmac.zero4 m c) c xs) c 16 = xs ++ Spec.GcmSiv.zeros (16 - xs.length) := by
  have hz := Proof.Cmac.zero4_bytes m c
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.X86.bytesAt_add] at hz
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.X86.bytesAt_add,
    Proof.AesGcm.X86.bytesAt_writeBytes_self _ _ _ (by omega),
    Proof.AesGcm.X86.bytesAt_frame (Proof.AesGcm.X86.writeBytes_frame' _ rfl) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base c (Nat.le_refl _) (by omega)) (by omega)]
  refine congrArg (xs ++ ·) ?_
  have := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at this
  rw [this, Nat.add_sub_cancel_left]
  simp [Spec.Cmac.zeros, Spec.GcmSiv.zeros, List.drop_replicate]

/-- One chunk of the 16 bytes at `W + 224`: their field element absorbed. -/
theorem chunkB_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t)
    (hsi : t.gpr .esi = p.W + BitVec.ofNat 32 224) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 16) :
    WP isa (chunk v.callees) t (VG.Proof.AesGcmSiv.X86.Absorbed p (VG.Proof.AesGcmSiv.X86.absR p)
      [Spec.GcmSiv.ofBytes (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 224) 16)] t) :=
  WP.mono (VG.Proof.AesGcmSiv.X86.chunk_ok v L E (m := 16) (by decide) (by decide) (VG.Proof.AesGcmSiv.X86.srcB L E.perm) hsi hn) fun t' C => by
    have A := Absorbed.of_chunk C
    simpa [VG.Proof.AesGcmSiv.X86.elemsAt, L.aW (show 224 < 2816 by decide)] using A

/-- What `absTailPre` leaves: the last bytes, padded, at `W + 224`, as the
bytes to absorb. -/
structure TailPre (p : VG.Proof.AesGcmSiv.X86.Prm) (P : Addr) (r : Nat) (t t₃ : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t₃
  rd : t₃.rd = t.rd
  wr : t₃.wr = t.wr
  esi : t₃.gpr .esi = p.W + BitVec.ofNat 32 224
  n : slotv t₃.mem p.W nO = BitVec.ofNat 32 16
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem t₃.mem
  bytes : bytesAt t₃.mem (w64 p.W + BitVec.ofNat 64 224) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r)

/-- `absTailPre`'s first block: the block zeroed, and the copy's arguments. -/
theorem absTail1_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {P : BitVec 32} {r : Nat}
    (hsi : t.gpr .esi = P) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 r) :
    ∃ t₁ : State, runBlock isa (zero4 bO ++ ([.mov .edi (.reg .esi), .mov .edx (.reg .ebp), .alu .add .edx (imm bO),
        .mov .ecx (slot nO)] : List Instr)) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero4 t.mem (w64 p.W + BitVec.ofNat 64 224) ∧ t₁.gpr .edi = P ∧
      t₁.gpr .edx = p.W + BitVec.ofNat 32 224 ∧ t₁.gpr .ecx = BitVec.ofNat 32 r ∧ t₁.gpr .ebp = p.W ∧
      t₁.gpr .esp = p.SP ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  simp only [slotv_eq, nO] at hn
  have hz := zero4_fold t.mem p.W 224
  simp only [Nat.reduceAdd] at hz
  have rn : (Proof.Cmac.zero4 t.mem (w64 p.W + BitVec.ofNat 64 224)).readW (w64 p.W + BitVec.ofNat 64 176) 32 =
      t.mem.readW (w64 p.W + BitVec.ofNat 64 176) 32 := by
    rw [← hz]; simp (disch := decide) only [readW_writeW_off]
  refine ⟨_, by simp only [zero4]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hn, hz, rn], ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · gmems [hz]
  · gregs [hsi]
  · gregs [E.ebp]
  · gmems [hz, rn, hn]
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals rfl

/-- `absTailPre`: the last `r` (1 to 15) bytes at `P`, padded with zeros. -/
theorem absTailPre_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {P : BitVec 32} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨w64 P, r⟩] (t.rd ++ t.wr)) (hf : P.toNat + r ≤ 2 ^ 32)
    (hd : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩) (hsi : t.gpr .esi = P)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 r) :
    WP isa absTailPre t (VG.Proof.AesGcmSiv.X86.TailPre p (w64 P) r t) := by
  have hw := L.ww
  obtain ⟨t₁, run₁, hm₁, di₁, dx₁, cx₁, bp₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.absTail1_ok L E hsi hn
  unfold absTailPre
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by
    rw [hm₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have E₁ : VG.Proof.AesGcmSiv.X86.Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (VG.Proof.AesGcmSiv.X86.frame_toMut f₁ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have dB : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 (p.W + BitVec.ofNat 32 224), r⟩ := by
    rw [L.aW (by decide)]
    exact (hd.sub_right (Lay.wSub (show 224 + 16 ≤ 2816 by decide))).sub_right (Region.sub_prefix (by omega))
  have lp : LoopPre t₁ P (p.W + BitVec.ofNat 32 224) r :=
    ⟨di₁, dx₁, cx₁, by omega, by omega, hf, by rw [L.nW (by decide)]; omega, by rw [rd₁, wr₁]; exact hc,
      by rw [L.aW (by decide)]; exact VG.Proof.AesGcmSiv.X86.covers_prefix (E₁.perm.wC (show 224 + 16 ≤ 2816 by decide)) (by omega), dB⟩
  refine WP.seq (WP.mono (copyLoop_ok t₁ lp) fun t₂ O => ?_)
  have hm₂ := O.mem
  rw [L.aW (by decide)] at hm₂
  -- The data is outside the zeroed block.
  have hd₁ : bytesAt t₁.mem (w64 P) r = bytesAt t.mem (w64 P) r :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by decide))) (by omega)
  have hb₂ : bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 16 =
      bytesAt t.mem (w64 P) r ++ Spec.GcmSiv.zeros (16 - r) := by
    have hl := length_bytesAt t.mem (w64 P) r
    rw [hm₂, hd₁, hm₁, VG.Proof.AesGcmSiv.X86.pad_bytes _ _ _ (by omega), hl]
  have f₂' : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t₁.mem t₂.mem := by
    rw [hm₂]
    exact (Proof.AesGcm.X86.writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₂.mem := f₁.trans f₂'
  have bp₂ : t₂.gpr .ebp = p.W := by rw [O.other _ (by decide) (by decide) (by decide) (by decide), bp₁]
  have sp₂ : t₂.gpr .esp = p.SP := by rw [O.other _ (by decide) (by decide) (by decide) (by decide), sp₁]
  have E₂ : VG.Proof.AesGcmSiv.X86.Env p t₂ := E₁.mut L bp₂ sp₂ O.rd O.wr (VG.Proof.AesGcmSiv.X86.frame_toMut f₂' fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t₂.mem
      (t₂.mem.writeW (w64 p.W + BitVec.ofNat 64 176) (BitVec.ofNat 32 16)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fm₃ := VG.Proof.AesGcmSiv.X86.frame_toMut f₃ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  refine WP.of_runBlock ⟨_, by grun [E₂.ebp, L.aW, E₂.perm.wW], ?_⟩
  refine ⟨E₂.mut L (by gregs [E₂.ebp]) (by gregs [E₂.esp]) (by gmems []) (by gmems []) (by gmems []; exact fm₃),
    by gmems [O.rd, rd₁], by gmems [O.wr, wr₁], by gregs [E₂.ebp], by gmems [slotv_eq], ?_, ?_⟩
  · gmems []
    exact (f₂.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (f₃.mono fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_of_mem _ List.mem_cons_self)
  · gmems []
    rw [Proof.AesGcm.X86.bytesAt_frame f₃ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide), hb₂]

/-- `absTail`: the last `r` (1 to 15) bytes at `P`, padded with zeros, absorbed. -/
theorem absTail_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {P : BitVec 32} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨w64 P, r⟩] (t.rd ++ t.wr)) (hf : P.toNat + r ≤ 2 ^ 32)
    (hd : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩) (hsi : t.gpr .esi = P)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 r) :
    WP isa (absTail v.callees) t
      (VG.Proof.AesGcmSiv.X86.AbsPost p [Spec.GcmSiv.ofBytes (bytesAt t.mem (w64 P) r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.absTailPre_ok L E hr1 hr hc hf hd hsi hn) fun t₃ T => ?_)
  refine WP.mono (VG.Proof.AesGcmSiv.X86.chunkB_ok v L T.env T.esi T.n) fun t₄ C => ?_
  rw [T.bytes] at C
  have dHY : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 224, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩], ∀ d,
      d + 16 ≤ 176 → (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun q hq d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  refine ⟨C.env, by rw [C.rd, T.rd], by rw [C.wr, T.wr],
    (T.frame.sub fun q hq => ?_).trans (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · rw [C.out, Proof.AesGcm.X86.blockAt_frame T.frame (fun q hq => dHY q hq 64 (by decide)),
      Proof.AesGcm.X86.blockAt_frame T.frame (fun q hq => dHY q hq 80 (by decide))]

/-! ## Absorbing a string -/

/-- The field elements of `n` bytes at `Q`, padded. -/
theorem elems_pad16_bytesAt (m : Mem) (Q : Addr) (n : Nat) :
    Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m Q n)) = VG.Proof.AesGcmSiv.X86.elemsAt m Q (n / 16) ++
      if n % 16 = 0 then [] else
        [Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++
          Spec.GcmSiv.zeros (16 - n % 16))] := by
  have hs := Proof.AesGcm.X86.bytesAt_add m Q (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega] at hs
  have hl := length_bytesAt m Q (16 * (n / 16))
  rw [GcmSiv.elems_pad16, length_bytesAt, hs, List.take_left' hl, List.drop_left' hl, GcmSiv.elems_bytesAt]

/-- The whole blocks of `absorb`, once ZF says whether there are any. -/
theorem absMid_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (hQ : VG.Proof.AesGcmSiv.X86.Src p t Q m) (hsi : t.gpr .esi = Q) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m)
    (hz : t.zf = some (decide (m / 16 = 0))) :
    WP isa (.ite .e (.block []) (.loop (chunk v.callees) .ne)) t fun t₂ =>
      VG.Proof.AesGcmSiv.X86.Absorbed p (VG.Proof.AesGcmSiv.X86.absR p) (VG.Proof.AesGcmSiv.X86.elemsAt t.mem (w64 Q) (m / 16)) t t₂ ∧
        t₂.gpr .esi = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ slotv t₂.mem p.W nO = BitVec.ofNat 32 (m % 16) := by
  refine WP.ite (decide (m / 16 = 0)) (VG.Proof.AesGcmSiv.X86.eval_e hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [h0, VG.Proof.AesGcmSiv.X86.elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [hsi, h0, Nat.mul_zero, BitVec.add_zero], by rw [hn]; congr 1; omega⟩
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact VG.Proof.AesGcmSiv.X86.chunks_ok v L E hm (by omega) (hQ.take (by omega)) hsi hn

/-- `anyLeft`: ZF set iff no byte is left. -/
theorem anyLeft_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {r : Nat} (hr : r < 2 ^ 32)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 r) :
    ∃ t' : State, runBlock isa anyLeft t = some t' ∧ t'.zf = some (decide (r = 0)) ∧ VG.Proof.AesGcmSiv.X86.Env p t' ∧
      t'.gpr .esi = t.gpr .esi ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  simp only [slotv_eq, nO] at hn
  refine ⟨_, by simp only [anyLeft]; grun [E.ebp, L.aW, E.perm.wR, hn], ?_, ?_, by gregs [], by gmems [],
    by gmems [], by gmems []⟩
  · gmems [hn]
    rw [BitVec.and_self, show BitVec.ofNat 32 r = BitVec.ofNat 32 r - BitVec.ofNat 32 0 by simp,
      sub_beq32 hr (by decide)]
  · exact E.keep (by gregs []) (by gregs []) (by gmems []) (by gmems []) (by gmems [])

theorem absorb_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (hQ : VG.Proof.AesGcmSiv.X86.Src p t Q m) (hd : (⟨w64 Q, m⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩)
    (hsi : t.gpr .esi = Q) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    WP isa (absorb v.callees) t (VG.Proof.AesGcmSiv.X86.AbsPost p (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem (w64 Q) m))) t) := by
  obtain ⟨t₁, run₁, z₁, E₁, si₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.wholeLeft_ok L E hm hn
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.absMid_ok v L E₁ hm (hQ.of_eq rd₁ wr₁) (by rw [si₁, hsi]) (by rw [slotv_eq, m₁]; exact hn)
    z₁) fun t₂ ⟨P₂, si₂, n₂⟩ => ?_)
  rw [m₁] at P₂
  have P₂' := P₂.of_eq m₁ rd₁ wr₁
  rw [VG.Proof.AesGcmSiv.X86.elems_pad16_bytesAt]
  obtain ⟨t₃, run₃, z₃, E₃, si₃, m₃, rd₃, wr₃⟩ := VG.Proof.AesGcmSiv.X86.anyLeft_ok L P₂'.env (by omega) n₂
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have P₃ : VG.Proof.AesGcmSiv.X86.Absorbed p (VG.Proof.AesGcmSiv.X86.absR p) (VG.Proof.AesGcmSiv.X86.elemsAt t.mem (w64 Q) (m / 16)) t t₃ :=
    ⟨E₃, rd₃.trans P₂'.rd, wr₃.trans P₂'.wr, m₃ ▸ P₂'.frame, by rw [m₃]; exact P₂'.out⟩
  refine WP.ite (decide (m % 16 = 0)) (VG.Proof.AesGcmSiv.X86.eval_e z₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil (P₃.sub (VG.Proof.AesGcmSiv.X86.absR_sub p))
  · have h0 : m % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    have hs := hQ.slice (a := 16 * (m / 16)) (k := m % 16) (by omega) (by omega)
    have ea := hQ.addr (j := 16 * (m / 16)) (by omega)
    have dT : (⟨w64 (Q + BitVec.ofNat 32 (16 * (m / 16))), m % 16⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ := by
      rw [ea]; exact hd.sub_left (Offset.sub_base _ (by omega))
    refine WP.mono (VG.Proof.AesGcmSiv.X86.absTail_ok v L P₃.env (by omega) (by omega) (by rw [P₃.rd, P₃.wr]; exact hs.rd) hs.wrap dT
      (by rw [si₃, si₂]) (by rw [slotv_eq, m₃]; exact n₂)) fun t₄ T => ?_
    have e := Proof.AesGcm.X86.bytesAt_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact hs.stk.symm) (by omega)
    rw [e, ea] at T
    exact AbsPost.trans L (P₃.sub (VG.Proof.AesGcmSiv.X86.absR_sub p)) T

/-! ## The lengths, and the tag input -/

/-- The memory `lensBlock` leaves. -/
def lensMem (m : Mem) (W : Addr) (al n : Nat) : Mem :=
  (Proof.Cmac.store4 m (W + BitVec.ofNat 64 224) (BitVec.ofNat 32 al <<< 3) (BitVec.ofNat 32 al >>> 29)
    (BitVec.ofNat 32 n <<< 3) (BitVec.ofNat 32 n >>> 29)).writeW (W + BitVec.ofNat 64 176) (BitVec.ofNat 32 16)

/-- `lensBlock`: the lengths block at `W + 224`, as the bytes to absorb. -/
theorem lensBlock_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) :
    ∃ t₁ : State, runBlock isa lensBlock t = some t₁ ∧
      t₁.mem = VG.Proof.AesGcmSiv.X86.lensMem t.mem (w64 p.W) p.al p.n ∧ t₁.gpr .esi = p.W + BitVec.ofNat 32 224 ∧
      t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have ha := E.slots.alen
  have hn := E.slots.len
  simp only [slotv_eq, alenO, lenO] at ha hn
  refine ⟨_, by simp only [lensBlock, le64At]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, ha, hn], ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · gmems [ha, hn, VG.Proof.AesGcmSiv.X86.add_self32_3, VG.Proof.AesGcmSiv.X86.lensMem, Proof.Cmac.store4, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc]
  · gregs [E.ebp]
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals rfl

/-- `lensBlock` and its chunk: the lengths block absorbed. -/
theorem lens_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) :
    WP isa (lens v.callees) t (VG.Proof.AesGcmSiv.X86.AbsPost p
      [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))] t) := by
  obtain ⟨t₁, run₁, hm₁, si₁, bp₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.lensBlock_ok L E
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem t₁.mem := by
    rw [hm₁, VG.Proof.AesGcmSiv.X86.lensMem]
    exact ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
  have E₁ : VG.Proof.AesGcmSiv.X86.Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (VG.Proof.AesGcmSiv.X86.frame_toMut f₁ fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩)))
  refine WP.mono (VG.Proof.AesGcmSiv.X86.chunkB_ok v L E₁ si₁ (by rw [slotv_eq, hm₁, VG.Proof.AesGcmSiv.X86.lensMem, Mem.readW_writeW_self32])) fun t₂ C => ?_
  have hb : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 224) 16 =
      Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n) := by
    have ea := GcmSiv.Words32.le64_words (BitVec.ofNat 32 p.al)
    have en := GcmSiv.Words32.le64_words (BitVec.ofNat 32 p.n)
    rw [toNat_ofNat32 L.al32] at ea
    rw [toNat_ofNat32 L.n32] at en
    rw [hm₁, VG.Proof.AesGcmSiv.X86.lensMem, Proof.AesGcm.X86.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _)) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide),
      Proof.Cmac.bytesAt_store4, ea, en, List.append_assoc]
  rw [hb] at C
  have dHY : ∀ d, d + 16 ≤ 176 → ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 224, 16⟩ : Region),
      ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩], (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  refine ⟨C.env, by rw [C.rd, rd₁], by rw [C.wr, wr₁], (f₁.sub fun q hq => ?_).trans
    (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · rw [C.out, Proof.AesGcm.X86.blockAt_frame f₁ (dHY 64 (by decide)),
      Proof.AesGcm.X86.blockAt_frame f₁ (dHY 80 (by decide))]

/-- The memory `tagIn` leaves. -/
def tagInMem (m : Mem) (W N : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 96)
    (bswap (m.readW (W + BitVec.ofNat 64 92) 32) ^^^ m.readW (N + BitVec.ofNat 64 0) 32)
    (bswap (m.readW (W + BitVec.ofNat 64 88) 32) ^^^ m.readW (N + BitVec.ofNat 64 4) 32)
    (bswap (m.readW (W + BitVec.ofNat 64 84) 32) ^^^ m.readW (N + BitVec.ofNat 64 8) 32)
    (bswap (m.readW (W + BitVec.ofNat 64 80) 32) &&& 0x7FFFFFFF#32)

theorem tagInMem_bytes (m : Mem) (W N : Addr) :
    bytesAt (VG.Proof.AesGcmSiv.X86.tagInMem m W N) (W + BitVec.ofNat 64 96) 16 =
      GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.blockAt m (W + BitVec.ofNat 64 80))) (bytesAt m N 12) := by
  have e := GcmSiv.Words32.tagOf_words (bswap (m.readW (W + BitVec.ofNat 64 92) 32))
    (bswap (m.readW (W + BitVec.ofNat 64 88) 32)) (bswap (m.readW (W + BitVec.ofNat 64 84) 32))
    (bswap (m.readW (W + BitVec.ofNat 64 80) 32)) (m.readW N 32) (m.readW (N + BitVec.ofNat 64 4) 32)
    (m.readW (N + BitVec.ofNat 64 8) 32)
  rw [GcmSiv.Words32.shl_shr_one] at e
  rw [VG.Proof.AesGcmSiv.X86.tagInMem, Proof.Cmac.bytesAt_store4, VG.Proof.AesGcmSiv.X86.blockAt_bswap, GcmSiv.Words32.toBytes_append4,
    show (12 : Nat) = 4 + 4 + 4 from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW]
  simp only [VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, Nat.reduceAdd, BitVec.add_zero]
  rw [e]

theorem tagIn_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) :
    ∃ t' : State, runBlock isa tagIn t = some t' ∧ t'.mem = VG.Proof.AesGcmSiv.X86.tagInMem t.mem (w64 p.W) (w64 p.N) ∧
      t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hN := E.slots.nonce
  simp only [slotv_eq, nonceO] at hN
  have n₀ := E.perm.nR (d := 0) (k := 4) (by decide)
  have n₄ := E.perm.nR (d := 4) (k := 4) (by decide)
  have n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  refine ⟨_, by simp only [tagIn, tagInW]; grun [E.ebp, L.aW, L.aN, E.perm.wW, E.perm.wR, hN, n₀, n₄, n₈], ?_, ?_,
    ?_, ?_, ?_⟩
  · gmems [hN, VG.Proof.AesGcmSiv.X86.tagInMem, Proof.Cmac.store4, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc]
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals rfl

theorem tagInMem_frame (m : Mem) (W N : Addr) : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m (VG.Proof.AesGcmSiv.X86.tagInMem m W N) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

/-! ## `polyval` -/

/-- What `polyval` writes: what absorbing writes, and the tag input at `W + 96`. -/
abbrev polyR (p : VG.Proof.AesGcmSiv.X86.Prm) : List Region := ⟨w64 p.W + BitVec.ofNat 64 96, 16⟩ :: VG.Proof.AesGcmSiv.X86.absorbR p

theorem inMut_polyR (p : VG.Proof.AesGcmSiv.X86.Prm) : VG.Proof.AesGcmSiv.X86.InMut p (VG.Proof.AesGcmSiv.X86.polyR p) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide))
  · exact VG.Proof.AesGcmSiv.X86.inMut_absorbR p r hr

/-- What `polyval` leaves, from `t`. -/
structure PolyPost (p : VG.Proof.AesGcmSiv.X86.Prm) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (VG.Proof.AesGcmSiv.X86.polyR p) t.mem t'.mem
  out : bytesAt t'.mem (w64 p.W + BitVec.ofNat 64 96) 16 =
    tagInputG (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) 16) (bytesAt t.mem (w64 p.N) 12)
      (bytesAt t.mem (w64 p.D) p.n) (bytesAt t.mem (w64 p.A) p.al)

/-- A buffer apart from `W` and the stack below `SP` misses what absorbing writes. -/
theorem absorbR_buf {p : VG.Proof.AesGcmSiv.X86.Prm} {P : Addr} {k : Nat} (hd : (⟨P, k⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩)
    (hb : (VG.Proof.AesGcmSiv.X86.stk p).Disjoint ⟨P, k⟩) : ∀ r ∈ VG.Proof.AesGcmSiv.X86.absorbR p, (⟨P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hb.symm

/-- `onStr s l`: the string at `W + s` (`W + l` bytes) to absorb. -/
theorem onStr_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {s l : Nat} {Q : BitVec 32} {k : Nat}
    (hs : s + 4 ≤ 176 ∧ 128 ≤ s) (hl : l + 4 ≤ 176 ∧ 128 ≤ l) (hQ : slotv t.mem p.W s = Q)
    (hk : slotv t.mem p.W l = BitVec.ofNat 32 k) :
    ∃ t₁ : State, runBlock isa (onStr s l) t = some t₁ ∧ VG.Proof.AesGcmSiv.X86.Env p t₁ ∧ t₁.gpr .esi = Q ∧
      slotv t₁.mem p.W nO = BitVec.ofNat 32 k ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧
      Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem t₁.mem := by
  simp only [slotv_eq] at hQ hk
  have f : Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem (t.mem.writeW (w64 p.W + BitVec.ofNat 64 176)
      (BitVec.ofNat 32 k)) := (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fm := VG.Proof.AesGcmSiv.X86.frame_toMut f fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  refine ⟨_, by simp only [onStr]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hQ, hk], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact E.mut L (by gregs [E.ebp]) (by gregs [E.esp]) (by gmems []) (by gmems []) (by gmems [hQ, hk]; exact fm)
  · gregs [hQ]
  · gmems [slotv_eq, hk]
  · gmems []
  · gmems []
  · gmems [hk]; exact f

theorem polyval_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t)
    (hG : Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 80) = 0) :
    WP isa (polyval v.callees) t (VG.Proof.AesGcmSiv.X86.PolyPost p t) := by
  have hw := L.ww
  -- The additional data.
  obtain ⟨t₁, run₁, E₁, si₁, n₁, rd₁, wr₁, f₁⟩ := VG.Proof.AesGcmSiv.X86.onStr_ok L E (s := aadO) (l := alenO) (by decide) (by decide)
    E.slots.aad E.slots.alen
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have d176 : ∀ {P : Addr} {k : Nat}, (⟨P, k⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 4⟩ : Region)], (⟨P, k⟩ : Region).Disjoint q := fun hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by decide))
  have eA₁ : bytesAt t₁.mem (w64 p.A) p.al = bytesAt t.mem (w64 p.A) p.al :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (d176 L.a_w) (by have := L.aw; omega)
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.absorb_ok v L E₁ (Q := p.A) (m := p.al) L.al32
    (VG.Proof.AesGcmSiv.X86.srcBuf E₁.perm.aad L.aw L.a_w L.ba) L.a_w si₁ n₁) fun t₂ P₂ => ?_)
  rw [eA₁] at P₂
  -- The data.
  obtain ⟨t₃, run₃, E₃, si₃, n₃, rd₃, wr₃, f₃⟩ := VG.Proof.AesGcmSiv.X86.onStr_ok L P₂.env (s := dataO) (l := lenO) (by decide) (by decide)
    P₂.env.slots.data P₂.env.slots.len
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have eD₃ : bytesAt t₃.mem (w64 p.D) p.n = bytesAt t.mem (w64 p.D) p.n := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₃ (d176 L.d_w) (by have := L.dw; omega),
      Proof.AesGcm.X86.bytesAt_frame P₂.frame (VG.Proof.AesGcmSiv.X86.absorbR_buf L.d_w L.bd) (by have := L.dw; omega),
      Proof.AesGcm.X86.bytesAt_frame f₁ (d176 L.d_w) (by have := L.dw; omega)]
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.absorb_ok v L E₃ (Q := p.D) (m := p.n) L.n32
    (VG.Proof.AesGcmSiv.X86.srcBuf (covers_left E₃.perm.d) L.dw L.d_w L.bd) L.d_w si₃ n₃) fun t₄ P₄ => ?_)
  rw [eD₃] at P₄
  -- From `t`: the writes of `onStr` are in `absorbR`, apart from GHASH's key and accumulator.
  have dHY : ∀ d, d + 16 ≤ 176 → ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 4⟩ : Region)],
      (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  have sub176 : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 4⟩ : Region)], ∃ q' ∈ VG.Proof.AesGcmSiv.X86.absorbR p, Region.Sub q q' :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  have pre : ∀ {xs : List Spec.GcmSiv.Elem} {u u₁ u₂ : State},
      Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] u.mem u₁.mem → u₁.rd = u.rd → u₁.wr = u.wr →
      VG.Proof.AesGcmSiv.X86.AbsPost p xs u₁ u₂ → VG.Proof.AesGcmSiv.X86.AbsPost p xs u u₂ := fun f hrd hwr P =>
    ⟨P.env, P.rd.trans hrd, P.wr.trans hwr, (f.sub sub176).trans P.frame, by
      rw [P.out, Proof.AesGcm.X86.blockAt_frame f (dHY 64 (by decide)),
        Proof.AesGcm.X86.blockAt_frame f (dHY 80 (by decide))]⟩
  have P₂₄ := AbsPost.trans L (pre f₁ rd₁ wr₁ P₂) (pre f₃ rd₃ wr₃ P₄)
  -- The lengths.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.lens_ok v L P₂₄.env) fun t₅ P₅ => ?_)
  have P₂₅ := AbsPost.trans L P₂₄ P₅
  -- The tag input.
  obtain ⟨t₆, run₆, hm₆, bp₆, sp₆, rd₆, wr₆⟩ := VG.Proof.AesGcmSiv.X86.tagIn_ok L P₂₅.env
  have f₆ : Frame [⟨w64 p.W + BitVec.ofNat 64 96, 16⟩] t₅.mem t₆.mem := by rw [hm₆]; exact VG.Proof.AesGcmSiv.X86.tagInMem_frame _ _ _
  refine WP.of_runBlock ⟨t₆, run₆, P₂₅.env.mut L bp₆ sp₆ rd₆ wr₆ (VG.Proof.AesGcmSiv.X86.frame_toMut f₆ fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide))),
    by rw [rd₆, P₂₅.rd], by rw [wr₆, P₂₅.wr], ?_, ?_⟩
  · refine (P₂₅.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans ?_
    exact f₆.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega
    have nN : bytesAt t₅.mem (w64 p.N) 12 = bytesAt t.mem (w64 p.N) 12 :=
      Proof.AesGcm.X86.bytesAt_frame P₂₅.frame (VG.Proof.AesGcmSiv.X86.absorbR_buf L.n_w L.bn) (by decide)
    rw [hm₆, VG.Proof.AesGcmSiv.X86.tagInMem_bytes, nN, P₂₅.out, hG, hY, tagInputG, length_bytesAt, length_bytesAt,
      GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))
        (by simp [Spec.GcmSiv.le64])]

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Tag`. -/
section

/-!
# AES-GCM-SIV on x86: a block encrypted with the encryption key (`tag`)

Untrusted: everything here is checked by Lean. `tag o` copies the block at
`W + 96` to `W + 112` (`copyMem`), zeroes the block at `W + o`, and calls
`vg_aes_ctr32` on that one block with the copy as the counter block: the
encryption of the block at `W + 96` with the encryption key's schedule at
`W + 512` (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq GcmImpl readW_writeW_off zero4_fold)

theorem blockAt_zero4 (m : Mem) (p : Addr) : Spec.Gcm.blockAt (Proof.Cmac.zero4 m p) p = 0 := by
  rw [Spec.Gcm.blockAt, Proof.Cmac.zero4_bytes]
  decide

/-- The memory after the copy of the counter block. -/
def copyMem (m : Mem) (W : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 112) (m.readW (W + BitVec.ofNat 64 96) 32)
    (m.readW (W + BitVec.ofNat 64 100) 32) (m.readW (W + BitVec.ofNat 64 104) 32)
    (m.readW (W + BitVec.ofNat 64 108) 32)

theorem copyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] m (VG.Proof.AesGcmSiv.X86.copyMem m W) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem copyMem_bytes (m : Mem) (W : Addr) :
    bytesAt (VG.Proof.AesGcmSiv.X86.copyMem m W) (W + BitVec.ofNat 64 112) 16 = bytesAt m (W + BitVec.ofNat 64 96) 16 := by
  rw [VG.Proof.AesGcmSiv.X86.copyMem, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.bytesAt_split4]
  simp only [VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, Nat.reduceAdd]

/-- The blocks a tag may be written to. -/
abbrev TagO (o : Nat) : Prop := o = 0 ∨ o = 224 ∨ o = 240

/-- What `tag o` writes. -/
abbrev tagWr (p : VG.Proof.AesGcmSiv.X86.Prm) (o : Nat) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩,
    VG.Proof.AesGcmSiv.X86.stk p]

theorem inMut_tagWr (p : VG.Proof.AesGcmSiv.X86.Prm) {o : Nat} (ho : VG.Proof.AesGcmSiv.X86.TagO o) : VG.Proof.AesGcmSiv.X86.InMut p (VG.Proof.AesGcmSiv.X86.tagWr p o) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide))
  · rcases ho with rfl | rfl | rfl
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide))
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact VG.Proof.AesGcmSiv.X86.inMut_stk p

/-- What `tag o` leaves, from `t`. -/
structure TagPost (p : VG.Proof.AesGcmSiv.X86.Prm) (o : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  esi : t'.gpr .esi = t.gpr .esi
  frame : Frame (VG.Proof.AesGcmSiv.X86.tagWr p o) t.mem t'.mem
  out : bytesAt t'.mem (w64 p.W + BitVec.ofNat 64 o) 16 =
    Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 96) 16)

/-- What `tag o`'s block leaves: the arguments of its call. -/
structure TagCall (p : VG.Proof.AesGcmSiv.X86.Prm) (o : Nat) (t t₁ : State) : Prop where
  mem : t₁.mem = Proof.Cmac.zero4 (VG.Proof.AesGcmSiv.X86.copyMem t.mem (w64 p.W)) (w64 p.W + BitVec.ofNat 64 o)
  eax : t₁.gpr .eax = p.W + BitVec.ofNat 32 512
  ecx : t₁.gpr .ecx = BitVec.ofNat 32 p.R
  edx : t₁.gpr .edx = p.W + BitVec.ofNat 32 112
  ebx : t₁.gpr .ebx = p.W + BitVec.ofNat 32 o
  edi : t₁.gpr .edi = BitVec.ofNat 32 1
  esi : t₁.gpr .esi = t.gpr .esi
  rd : t₁.rd = t.rd
  wr : t₁.wr = t.wr
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o, 16⟩] t.mem t₁.mem
  env : VG.Proof.AesGcmSiv.X86.Env p t₁
  dst : VG.Proof.AesGcmSiv.X86.Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.W + BitVec.ofNat 32 o) (16 * 1)

/-- `tag o`'s block. -/
theorem tagArgs_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {o : Nat} (ho : VG.Proof.AesGcmSiv.X86.TagO o) :
    ∃ t₁, runBlock isa (copy16 cbO ccO ++ zero4 o ++ ctrArgs o) t = some t₁ ∧ VG.Proof.AesGcmSiv.X86.TagCall p o t t₁ := by
  have hw := L.ww
  have o₁ : o + 16 ≤ 2816 := by omega
  have hR := E.slots.rounds
  simp only [slotv_eq, roundsO] at hR
  have hz := zero4_fold (VG.Proof.AesGcmSiv.X86.copyMem t.mem (w64 p.W)) p.W o
  have rR : (VG.Proof.AesGcmSiv.X86.copyMem t.mem (w64 p.W)).readW (w64 p.W + BitVec.ofNat 64 148) 32 = BitVec.ofNat 32 p.R := by
    rw [VG.Proof.AesGcmSiv.X86.copyMem, Proof.Cmac.store4]
    simp (disch := decide) only [VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, Nat.reduceAdd, readW_writeW_off]
    exact hR
  have rR' : (Proof.Cmac.zero4 (VG.Proof.AesGcmSiv.X86.copyMem t.mem (w64 p.W)) (w64 p.W + BitVec.ofNat 64 o)).readW
      (w64 p.W + BitVec.ofNat 64 148) 32 = BitVec.ofNat 32 p.R := by
    rw [← hz]
    rcases ho with rfl | rfl | rfl <;> simp (disch := decide) only [Nat.reduceAdd, readW_writeW_off] <;> exact rR
  obtain ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, bp₁, sp₁, si₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa
      (copy16 cbO ccO ++ zero4 o ++ ctrArgs o) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero4 (VG.Proof.AesGcmSiv.X86.copyMem t.mem (w64 p.W)) (w64 p.W + BitVec.ofNat 64 o) ∧
      t₁.gpr .eax = p.W + BitVec.ofNat 32 512 ∧ t₁.gpr .ecx = BitVec.ofNat 32 p.R ∧
      t₁.gpr .edx = p.W + BitVec.ofNat 32 112 ∧ t₁.gpr .ebx = p.W + BitVec.ofNat 32 o ∧
      t₁.gpr .edi = BitVec.ofNat 32 1 ∧ t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧ t₁.gpr .esi = t.gpr .esi ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    have hcp : ((((t.mem.writeW (w64 p.W + BitVec.ofNat 64 112) (t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32)).writeW
        (w64 p.W + BitVec.ofNat 64 116) (t.mem.readW (w64 p.W + BitVec.ofNat 64 100) 32)).writeW
        (w64 p.W + BitVec.ofNat 64 120) (t.mem.readW (w64 p.W + BitVec.ofNat 64 104) 32)).writeW
        (w64 p.W + BitVec.ofNat 64 124) (t.mem.readW (w64 p.W + BitVec.ofNat 64 108) 32)) =
        VG.Proof.AesGcmSiv.X86.copyMem t.mem (w64 p.W) := by
      simp only [VG.Proof.AesGcmSiv.X86.copyMem, Proof.Cmac.store4, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, Nat.reduceAdd]
    rcases ho with rfl | rfl | rfl <;>
    refine ⟨_, by simp only [copy16, zero4, ctrArgs]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hcp, hz, rR'],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | (gmems [hcp, hz]; done)
      | (gregs [E.ebp, rR']; done)
      | (gregs [E.ebp, E.esp]; done)
      | (gregs []; done)
      | rfl
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o, 16⟩] t.mem t₁.mem := by
    rw [hm₁, Proof.Cmac.zero4]
    exact ((VG.Proof.AesGcmSiv.X86.copyMem_frame _ _).mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; simp)
  have E₁ : VG.Proof.AesGcmSiv.X86.Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (VG.Proof.AesGcmSiv.X86.frame_toMut f₁ fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide))
    · exact VG.Proof.AesGcmSiv.X86.inMut_tagWr p ho _ (by simp))
  have hD : VG.Proof.AesGcmSiv.X86.Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.W + BitVec.ofNat 32 o) (16 * 1) :=
    VG.Proof.AesGcmSiv.X86.dstW L E₁.perm (q := o) (by rcases ho with rfl | rfl | rfl <;> decide)
      (by rw [L.aW (by decide)]; exact Lay.w_w (.inr (by omega)) (by decide) (by omega))
  exact ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, si₁, rd₁, wr₁, f₁, E₁, hD⟩

theorem tag_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {o : Nat} (ho : VG.Proof.AesGcmSiv.X86.TagO o) :
    WP isa (VG.Impl.AesGcmSiv.X86.tag v.callees o) t (VG.Proof.AesGcmSiv.X86.TagPost p o t) := by
  have hw := L.ww
  have o₁ : o + 16 ≤ 2816 := by omega
  obtain ⟨t₁, run₁, ⟨hm₁, eax, ecx, edx, ebx, edi, si₁, rd₁, wr₁, f₁, E₁, hD⟩⟩ := VG.Proof.AesGcmSiv.X86.tagArgs_ok L E ho
  have dO : (⟨w64 p.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 112, 16⟩ :=
    Lay.w_w (by omega) (by omega) (by decide)
  have hb₁ : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 112) 16 = bytesAt t.mem (w64 p.W + BitVec.ofNat 64 96) 16 := by
    rw [hm₁, Proof.Cmac.zero4, Proof.AesGcm.X86.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dO.symm) (by decide), VG.Proof.AesGcmSiv.X86.copyMem_bytes]
  have hz₁ : Spec.Gcm.blockAt t₁.mem (w64 p.W + BitVec.ofNat 64 o) = 0 := by rw [hm₁]; exact VG.Proof.AesGcmSiv.X86.blockAt_zero4 _ _
  have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
      Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (Lay.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le)
      · exact (Lay.w_w (.inr (by omega)) (by decide) (by omega)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (VG.Proof.AesGcmSiv.X86.callCtr_ok v L E₁ (VG.Proof.AesGcmSiv.X86.keyS L E₁.perm) hD
    (by rw [L.aW (by omega)]; exact VG.Proof.AesGcmSiv.X86.inMut_tagWr p ho _ (by simp)) eax ecx edx ebx edi) fun t₂ P => ?_
  have fc := P.frame
  have hout := P.out
  rw [L.aW (by omega)] at fc hout
  refine ⟨P.env, by rw [P.rd, rd₁], by rw [P.wr, wr₁], by rw [P.saved _ (by decide), si₁],
    (f₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp).trans (fc.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp), ?_⟩
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
  rw [L.aW (by decide)] at hout
  rw [Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
    show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 512) (16 * (p.R + 1))) =
      Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R from rfl, ek₁, hb₁]

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Crypt`. -/
section

/-!
# AES-GCM-SIV on x86: counter mode (`crypt`)

Untrusted: everything here is checked by Lean. The counter block at
`W + 96` starts as the tag with the top bit of its last byte set
(`cryptHead_ok`); each block of the data is encrypted in place by
`vg_aes_ctr32` from a copy of it at `W + 112`, after which its first word is
incremented (`cryptBlock_ok`); the last bytes are XORed with the keystream
block, computed at `W + 224` (`cryptTail_ok`). `crypt_ok`: the data becomes
`ctr` of it (RFC 8452 §4). The pointer is in `esi` and the number of bytes
left at `W + nO`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Impl.AesGcm.X86 (at_ imm slot xorLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add slotv slotv_eq GcmImpl readW_writeW_off covers_left
  covers_off XorPre XorPost xorLoop_ok xorBytes length_bytesAt sub_beq32)

theorem ctr32_single (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (icb x : Spec.Gcm.Block) :
    Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

theorem toBytes_xor (a b : Spec.Gcm.Block) :
    Spec.Gcm.toBytes (a ^^^ b) = Spec.Cmac.xor (Spec.Gcm.toBytes a) (Spec.Gcm.toBytes b) := by
  apply List.ext_getElem (by simp [Spec.Gcm.toBytes, Spec.Cmac.xor])
  intro i h₁ h₂
  simp [Spec.Gcm.toBytes, Spec.Cmac.xor, BitVec.extractLsb'_xor]

/-- What the counter block at `W + 96` holds before block `j`: the first
word of `icb` plus `j`, and the rest of `icb`. -/
structure CtrSt (W : Addr) (icb : List Byte) (j : Nat) (m : Mem) : Prop where
  word : m.readW (W + BitVec.ofNat 64 96) 32 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + j)
  rest : bytesAt m (W + BitVec.ofNat 64 100) 12 = icb.drop 4

theorem CtrSt.block {W : Addr} {icb : List Byte} {j : Nat} {m : Mem} (h : VG.Proof.AesGcmSiv.X86.CtrSt W icb j m) :
    bytesAt m (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.counterBlock icb j := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    h.word, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, h.rest]

/-- Bytes of a buffer outside the part a frame may also change. -/
theorem frame_outside {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {len a n : Nat}
    (hrs : ∀ r ∈ rs, r = ⟨P + BitVec.ofNat 64 a, n⟩ ∨ (⟨P, len⟩ : Region).Disjoint r) (hlen : len < 2 ^ 64)
    (han : a + n ≤ len) : ∀ p < len, (p < a ∨ a + n ≤ p) → m' (P + BitVec.ofNat 64 p) = m (P + BitVec.ofNat 64 p) :=
  fun p hp ho => hf _ fun r hr hc => by
    rcases hrs r hr with rfl | hd
    · exact Offset.disjoint P (d := p) (n := 1) (by omega) (by omega) (by omega) _ (Region.contains_self _ _) hc
    · exact hd _ (Offset.contains_base P (show p + 1 ≤ len by omega) (by omega)) hc

/-- What counter mode writes: the counter block and its copy, the bytes
left, the block at `W + 224`, `vg_aes_ctr32`'s working space, the data and
the stack below `SP`. -/
abbrev cryR (p : VG.Proof.AesGcmSiv.X86.Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, ⟨w64 p.W + BitVec.ofNat 64 224, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, ⟨w64 p.D, p.n⟩, VG.Proof.AesGcmSiv.X86.stk p]

theorem inMut_cryR (p : VG.Proof.AesGcmSiv.X86.Prm) : VG.Proof.AesGcmSiv.X86.InMut p (VG.Proof.AesGcmSiv.X86.cryR p) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide))
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact VG.Proof.AesGcmSiv.X86.inMut_d p
  · exact VG.Proof.AesGcmSiv.X86.inMut_stk p

/-- Byte `j` of the data, as a 64-bit address. -/
theorem Lay.dA {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {j : Nat} (hj : j < p.n) : w64 (p.D + BitVec.ofNat 32 j) = w64 p.D + BitVec.ofNat 64 j :=
  w64_add (by have := L.dw; omega)

theorem Lay.dN {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {j : Nat} (hj : j < p.n) : (p.D + BitVec.ofNat 32 j).toNat = p.D.toNat + j :=
  toNat_add32 (by have := L.dw; omega)

/-- What a block of counter mode leaves, from `t`. -/
structure BlockPost (p : VG.Proof.AesGcmSiv.X86.Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (j : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  esi : t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * (j + 1))
  n : slotv t'.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * (j + 1))
  z : t'.zf = some (decide ((p.n - 16 * (j + 1)) / 16 = 0))
  ctr : VG.Proof.AesGcmSiv.X86.CtrSt (w64 p.W) icb (j + 1) t'.mem
  data : bytesAt t'.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * (j + 1))
  frame : Frame (VG.Proof.AesGcmSiv.X86.cryR p) t.mem t'.mem

/-- The arguments of a block's call. -/
theorem blkArgs_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {j : Nat}
    (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)) :
    ∃ t₁ : State, runBlock isa blockArgs t = some t₁ ∧ t₁.mem = VG.Proof.AesGcmSiv.X86.copyMem t.mem (w64 p.W) ∧
      t₁.gpr .eax = p.W + BitVec.ofNat 32 512 ∧ t₁.gpr .ecx = BitVec.ofNat 32 p.R ∧
      t₁.gpr .edx = p.W + BitVec.ofNat 32 112 ∧ t₁.gpr .ebx = p.D + BitVec.ofNat 32 (16 * j) ∧
      t₁.gpr .edi = BitVec.ofNat 32 1 ∧ t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧ t₁.gpr .esi = t.gpr .esi ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have hR := E.slots.rounds
  simp only [slotv_eq, roundsO] at hR
  have hcp : ((((t.mem.writeW (w64 p.W + BitVec.ofNat 64 112) (t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 116) (t.mem.readW (w64 p.W + BitVec.ofNat 64 100) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 120) (t.mem.readW (w64 p.W + BitVec.ofNat 64 104) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 124) (t.mem.readW (w64 p.W + BitVec.ofNat 64 108) 32)) = VG.Proof.AesGcmSiv.X86.copyMem t.mem (w64 p.W) := by
    simp only [VG.Proof.AesGcmSiv.X86.copyMem, Proof.Cmac.store4, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, Nat.reduceAdd]
  have rR : (VG.Proof.AesGcmSiv.X86.copyMem t.mem (w64 p.W)).readW (w64 p.W + BitVec.ofNat 64 148) 32 = BitVec.ofNat 32 p.R := by
    rw [VG.Proof.AesGcmSiv.X86.copyMem, Proof.Cmac.store4]
    simp (disch := decide) only [VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, Nat.reduceAdd, readW_writeW_off]
    exact hR
  refine ⟨_, by simp only [blockArgs, copy16]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hcp, rR], ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hcp]
  · gregs [E.ebp]
  · gregs [rR]
  · gregs [E.ebp]
  · gregs [hsi]
  · gregs []
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []
  all_goals rfl

/-- The code after a block's call. -/
theorem blkPost_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * j)) :
    ∃ t' : State, runBlock isa blockNext t = some t' ∧
      t'.mem = (t.mem.writeW (w64 p.W + BitVec.ofNat 64 96)
        (t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 + BitVec.ofNat 32 1)).writeW (w64 p.W + BitVec.ofNat 64 176)
        (BitVec.ofNat 32 (p.n - 16 * (j + 1))) ∧
      t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * (j + 1)) ∧
      t'.zf = some (decide ((p.n - 16 * (j + 1)) / 16 = 0)) ∧ t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hn' := L.n32
  simp only [slotv_eq, nO] at hn
  have e5 : BitVec.ofNat 32 (p.n - 16 * j) - BitVec.ofNat 32 16 = BitVec.ofNat 32 (p.n - 16 * (j + 1)) := by
    rw [VG.Proof.AesGcmSiv.X86.ofNat_sub32 (by omega) (by omega), show p.n - 16 * j - 16 = p.n - 16 * (j + 1) by omega]
  have rn : (t.mem.writeW (w64 p.W + BitVec.ofNat 64 96) (t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 +
      BitVec.ofNat 32 1)).readW (w64 p.W + BitVec.ofNat 64 176) 32 = BitVec.ofNat 32 (p.n - 16 * j) := by
    rw [readW_writeW_off _ _ _ (by decide) (by decide) (by decide), hn]
  refine ⟨_, by simp only [blockNext, wholeLeft]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, rn, e5], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · gmems [rn, e5]
  · gregs [hsi, VG.Proof.AesGcmSiv.X86.add32_ofNat_assoc, Nat.mul_succ]
  · gmems [rn, e5, VG.Proof.AesGcmSiv.X86.ofNat_lsr32 (show p.n - 16 * (j + 1) < 2 ^ 32 by omega)]
    rw [BitVec.and_self, show BitVec.ofNat 32 ((p.n - 16 * (j + 1)) / 16) =
      BitVec.ofNat 32 ((p.n - 16 * (j + 1)) / 16) - BitVec.ofNat 32 0 by simp, sub_beq32 (by omega) (by decide)]
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals rfl

theorem cryptBlock_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {j : Nat}
    (hj : 16 * (j + 1) ≤ p.n) (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * j))
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * j)) (C : VG.Proof.AesGcmSiv.X86.CtrSt (w64 p.W) icb j t.mem)
    (hx : bytesAt t.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j))
    (hc : Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph) :
    WP isa (cryptBlock v.callees) t (VG.Proof.AesGcmSiv.X86.BlockPost p ciph icb x j t) := by
  have hw := L.ww
  have hn' := L.n32
  have hdw := L.dw
  obtain ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, bp₁, sp₁, si₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.blkArgs_ok L E hsi
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact VG.Proof.AesGcmSiv.X86.copyMem_frame _ _
  have E₁ : VG.Proof.AesGcmSiv.X86.Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (VG.Proof.AesGcmSiv.X86.frame_toMut f₁ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide)))
  have eQ : w64 (p.D + BitVec.ofNat 32 (16 * j)) = w64 p.D + BitVec.ofNat 64 (16 * j) := L.dA (by omega)
  have dQ : (⟨w64 p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  have hD : VG.Proof.AesGcmSiv.X86.Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.D + BitVec.ofNat 32 (16 * j)) (16 * 1) := by
    refine ⟨?_, by rw [L.dN (by omega)]; omega, ?_, ?_, ?_, ?_⟩ <;> rw [eQ]
    · exact covers_off E₁.perm.d (by omega) (by omega)
    · rw [L.aW (by decide)]; exact (dQ.sub_right (Lay.wSub (show 512 + 240 ≤ 2816 by decide))).symm
    · exact dQ.sub_right (Lay.wSub (by decide))
    · exact dQ.sub_right (Lay.wSub (by decide))
    · exact L.bd.sub_right (Offset.sub_base _ (by omega))
  -- What the copy changed.
  have dD : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 112, 16⟩ : Region)], (⟨w64 p.D, p.n⟩ : Region).Disjoint q :=
    fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hcb : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.counterBlock icb j := by
    rw [hm₁, VG.Proof.AesGcmSiv.X86.copyMem_bytes, C.block]
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph := by
    rw [← hc]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (Lay.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  have hx₁ : bytesAt t₁.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j) := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₁ dD (by omega), hx]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  refine WP.mono (VG.Proof.AesGcmSiv.X86.callCtr_ok v L E₁ (VG.Proof.AesGcmSiv.X86.keyS L E₁.perm) hD (by rw [eQ]; exact ⟨⟨w64 p.D, p.n⟩, by simp,
                                                  Offset.sub_base _ (by omega)⟩) eax ecx edx ebx edi) fun t₂ P => ?_
  have fc := P.frame
  have hout := P.out
  simp only [eQ, Nat.mul_one] at fc hout
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    VG.Proof.AesGcmSiv.X86.ctr32_single, List.cons.injEq, and_true] at hout
  rw [L.aW (by decide)] at hout
  have hb₂ : bytesAt t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * j)) 16 =
      Spec.Cmac.xor (bytesAt t₁.mem (w64 p.D + BitVec.ofNat 64 (16 * j)) 16) (GcmSiv.ksBlock ciph icb j) := by
    rw [Proof.Cmac.bytesAt_blockAt, hout, VG.Proof.AesGcmSiv.X86.toBytes_xor, ← Proof.Cmac.bytesAt_blockAt, Spec.Gcm.blockAt,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
      show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 512) (16 * (p.R + 1))) =
        Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R from rfl, hc₁, hcb]
  have hk : (GcmSiv.ksBlock ciph icb j).length = 16 := by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  have hx₂ : bytesAt t₂.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j + 16) := by
    rw [← hxl] at hx₁ ⊢
    refine GcmSiv.ctrPart_step ciph icb x _ (by decide) hk hx₁ ?_ (by rw [hb₂, List.take_of_length_le (by omega)])
    rw [hxl]
    refine VG.Proof.AesGcmSiv.X86.frame_outside fc (fun q hq => ?_) (by omega) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inl rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inr L.bd.symm
  -- What the first two pieces changed.
  have f₂' : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.D + BitVec.ofNat 64 (16 * j), 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, VG.Proof.AesGcmSiv.X86.stk p] t.mem t₂.mem :=
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans fc
  have dC : ∀ {d k : Nat}, (96 ≤ d ∧ d + k ≤ 112 ∨ 176 ≤ d ∧ d + k ≤ 184) →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨w64 p.D + BitVec.ofNat 64 (16 * j), 16⟩,
        ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, VG.Proof.AesGcmSiv.X86.stk p], (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (by omega) (by omega) (by decide)
      · exact (dQ.sub_right (Lay.wSub (by omega))).symm
      · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.bw' (by omega)).symm
  have w₂ : t₂.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 = t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 :=
    f₂'.readW (Region.contains_self _ _) (dC (k := 4) (.inl ⟨Nat.le_refl _, by decide⟩)) (by decide)
  have n₂ : slotv t₂.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * j) := by
    rw [← hn]; exact f₂'.readW (Region.contains_self _ _) (dC (k := 4) (.inr ⟨Nat.le_refl _, by decide⟩)) (by decide)
  have r₂ : bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 100) 12 = bytesAt t.mem (w64 p.W + BitVec.ofNat 64 100) 12 :=
    Proof.AesGcm.X86.bytesAt_frame f₂' (dC (.inl ⟨by decide, by decide⟩)) (by decide)
  have si₂ : t₂.gpr .esi = p.D + BitVec.ofNat 32 (16 * j) := by rw [P.saved _ (by decide), si₁, hsi]
  obtain ⟨t₃, run₃, hm₃, si₃, z₃, bp₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesGcmSiv.X86.blkPost_ok L P.env hj si₂ n₂
  have f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 96, 4⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t₂.mem t₃.mem := by
    rw [hm₃]
    have g : Frame [⟨w64 p.W + BitVec.ofNat 64 96, 4⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t₂.mem
        (t₂.mem.writeW (w64 p.W + BitVec.ofNat 64 96) (t₂.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 +
          BitVec.ofNat 32 1)) := (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
    exact g.writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
  have fm₃ : Frame (VG.Proof.AesGcmSiv.X86.cryR p) t₂.mem t₃.mem := f₃.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  have E₃ : VG.Proof.AesGcmSiv.X86.Env p t₃ := P.env.mut L bp₃ sp₃ rd₃ wr₃ (VG.Proof.AesGcmSiv.X86.frame_toMut fm₃ (VG.Proof.AesGcmSiv.X86.inMut_cryR p))
  have f₂ : Frame (VG.Proof.AesGcmSiv.X86.cryR p) t.mem t₂.mem := f₂'.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨w64 p.D, p.n⟩, by simp, Offset.sub_base _ (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine WP.of_runBlock ⟨t₃, run₃, E₃, by rw [rd₃, P.rd, rd₁], by rw [wr₃, P.wr, wr₁], si₃,
    by rw [slotv_eq, hm₃, Mem.readW_writeW_self32], z₃, ⟨?_, ?_⟩, ?_, f₂.trans fm₃⟩
  · rw [hm₃, readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, w₂, C.word]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [Proof.AesGcm.X86.bytesAt_frame f₃ (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), r₂, C.rest]
  · rw [Proof.AesGcm.X86.bytesAt_frame f₃ (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> exact L.d_w' (by decide)) (Nat.le_of_lt (by omega)), hx₂,
      show 16 * j + 16 = 16 * (j + 1) by omega]

/-- The encryption key's schedule misses what counter mode writes. -/
theorem key_cryR {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86.cryR p, (⟨w64 p.W + BitVec.ofNat 64 512, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm
  · exact (L.bw' (by decide)).symm

theorem ciph_cryR {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.X86.cryR p) m m') :
    Spec.GcmSiv.ctxCiph m' (w64 p.W + BitVec.ofNat 64 512) p.R =
      Spec.GcmSiv.ctxCiph m (w64 p.W + BitVec.ofNat 64 512) p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (VG.Proof.AesGcmSiv.X86.key_cryR L r hr).sub_left (Region.sub_prefix L.rounds_le))
    (by have := L.rounds_le; omega)]

/-- What the whole blocks of counter mode leave, from `t`. -/
structure BlocksPost (p : VG.Proof.AesGcmSiv.X86.Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (b : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  esi : t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * b)
  n : slotv t'.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * b)
  ctr : VG.Proof.AesGcmSiv.X86.CtrSt (w64 p.W) icb b t'.mem
  data : bytesAt t'.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b)
  frame : Frame (VG.Proof.AesGcmSiv.X86.cryR p) t.mem t'.mem

theorem blocks_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) (hb1 : 1 ≤ p.n / 16)
    (hsi : t.gpr .esi = p.D) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 p.n)
    (C : VG.Proof.AesGcmSiv.X86.CtrSt (w64 p.W) icb 0 t.mem) (hx : bytesAt t.mem (w64 p.D) p.n = x)
    (hc : Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph) :
    WP isa (.loop (cryptBlock v.callees) .ne) t (VG.Proof.AesGcmSiv.X86.BlocksPost p ciph icb x (p.n / 16) t) := by
  refine WP.loop (M := isa) (body := cryptBlock v.callees) (c := .ne)
    (fun (k : Nat) (t' : State) => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ VG.Proof.AesGcmSiv.X86.BlocksPost p ciph icb x j t t') ?_
    (p.n / 16 - 0) t
    ⟨0, rfl, hb1, ⟨E, rfl, rfl, by rw [hsi, Nat.mul_zero, BitVec.add_zero], by rw [hn, Nat.mul_zero, Nat.sub_zero],
      C, by rw [hx, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  rintro k t' ⟨j, rfl, hj, P⟩
  have hc' : Spec.GcmSiv.ctxCiph t'.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph := by
    rw [VG.Proof.AesGcmSiv.X86.ciph_cryR L P.frame, hc]
  refine WP.mono (VG.Proof.AesGcmSiv.X86.cryptBlock_ok v L P.env hxl (j := j) (by omega) P.esi P.n P.ctr P.data hc') fun t'' Q => ?_
  have P' : VG.Proof.AesGcmSiv.X86.BlocksPost p ciph icb x (j + 1) t t'' :=
    ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.esi, Q.n, Q.ctr, Q.data, P.frame.trans Q.frame⟩
  have ev := VG.Proof.AesGcmSiv.X86.eval_ne Q.z
  by_cases he : j + 1 = p.n / 16
  · left
    exact ⟨ev.trans (by simp; omega), he ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp; omega), p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, P'⟩

/-- What the last bytes of counter mode leave, from `t`. -/
structure TailPost (p : VG.Proof.AesGcmSiv.X86.Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  data : bytesAt t'.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x p.n
  frame : Frame (VG.Proof.AesGcmSiv.X86.cryR p) t.mem t'.mem

theorem cryptTail_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {b r : Nat}
    (hn : p.n = 16 * b + r) (hr1 : 1 ≤ r) (hr : r < 16) (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * b))
    (hnr : slotv t.mem p.W nO = BitVec.ofNat 32 r) (C : VG.Proof.AesGcmSiv.X86.CtrSt (w64 p.W) icb b t.mem)
    (hx : bytesAt t.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b))
    (hc : Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph) :
    WP isa (cryptTail v.callees) t (VG.Proof.AesGcmSiv.X86.TailPost p ciph icb x t) := by
  have hn' := L.n32
  have hdw := L.dw
  have hw := L.ww
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.tag_ok v L E (o := 224) (by decide)) fun t₂ T => ?_)
  have fT := T.frame
  have dT : ∀ q ∈ VG.Proof.AesGcmSiv.X86.tagWr p 224, (⟨w64 p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  have hx₂ : bytesAt t₂.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b) := by
    rw [Proof.AesGcm.X86.bytesAt_frame fT dT (by omega), hx]
  have hks : bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 16 = GcmSiv.ksBlock ciph icb b := by
    rw [T.out, hc, C.block]
  have hnr₂ : slotv t₂.mem p.W nO = BitVec.ofNat 32 r := by
    rw [← hnr]
    exact fT.readW (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  simp only [slotv_eq, nO] at hnr₂
  obtain ⟨t₃, run₃, dx₃, di₃, cx₃, m₃, bp₃, sp₃, rd₃, wr₃⟩ : ∃ t₃ : State, runBlock isa
      [.mov .edx (.reg .ebp), .alu .add .edx (imm bO), .mov .edi (.reg .esi), .mov .ecx (slot nO)] t₂ = some t₃ ∧
      t₃.gpr .edx = p.W + BitVec.ofNat 32 224 ∧ t₃.gpr .edi = p.D + BitVec.ofNat 32 (16 * b) ∧
      t₃.gpr .ecx = BitVec.ofNat 32 r ∧ t₃.mem = t₂.mem ∧ t₃.gpr .ebp = p.W ∧ t₃.gpr .esp = p.SP ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr :=
    ⟨_, by grun [T.env.ebp, L.aW, T.env.perm.wR, hnr₂], by gregs [T.env.ebp], by gregs [T.esi, hsi],
      by gregs [hnr₂], by gmems [], by gregs [T.env.ebp], by gregs [T.env.esp], by gmems [], by gmems []⟩
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have eD := L.dA (j := 16 * b) (by omega)
  have dQ : (⟨w64 p.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  have lp : XorPre t₃ (p.W + BitVec.ofNat 32 224) (p.D + BitVec.ofNat 32 (16 * b)) r := by
    refine ⟨dx₃, di₃, cx₃, by omega, by omega, by rw [L.nW (by decide)]; omega, by rw [L.dN (by omega)]; omega,
      ?_, ?_, ?_⟩
    · rw [rd₃, wr₃, L.aW (by decide)]
      exact VG.Proof.AesGcmSiv.X86.covers_prefix (T.env.perm.wCR (show 224 + 16 ≤ 2816 by decide)) (by omega)
    · rw [wr₃, eD]; exact covers_off T.env.perm.d (by omega) (by omega)
    · rw [eD, L.aW (by decide)]
      exact ((dQ.sub_right (Lay.wSub (show 224 + 16 ≤ 2816 by decide))).sub_right (Region.sub_prefix (by omega))).symm
  refine WP.mono (xorLoop_ok t₃ lp) fun t₄ O => ?_
  have hm₄ := O.mem
  rw [m₃, eD, L.aW (by decide)] at hm₄
  have hl : (xorBytes t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * b)) (w64 p.W + BitVec.ofNat 64 224) r).length = r := by
    simp [xorBytes, Proof.Cmac.bytesAt_length]
  have fw := Proof.AesGcm.X86.writeBytes_frame' t₂.mem (q := w64 p.D + BitVec.ofNat 64 (16 * b)) hl
  rw [← hm₄] at fw
  have hk : (GcmSiv.ksBlock ciph icb b).length = 16 := by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  have fwm : Frame (VG.Proof.AesGcmSiv.X86.mutR p) t₃.mem t₄.mem := by
    rw [m₃]
    exact VG.Proof.AesGcmSiv.X86.frame_toMut fw fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨w64 p.D, p.n⟩, by simp, Offset.sub_base _ (by omega)⟩
  have E₄ : VG.Proof.AesGcmSiv.X86.Env p t₄ := T.env.mut L
    (by rw [O.other _ (by decide) (by decide) (by decide) (by decide) (by decide), bp₃])
    (by rw [O.other _ (by decide) (by decide) (by decide) (by decide) (by decide), sp₃])
    (by rw [O.rd, rd₃]) (by rw [O.wr, wr₃]) (by rw [← m₃]; exact fwm)
  refine ⟨E₄, by rw [O.rd, rd₃, T.rd], by rw [O.wr, wr₃, T.wr], ?_, ?_⟩
  · have hb' : bytesAt t₄.mem (w64 p.D + BitVec.ofNat 64 (16 * b)) r = Spec.Cmac.xor
        (bytesAt t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * b)) r) ((GcmSiv.ksBlock ciph icb b).take r) := by
      have e := Proof.AesGcm.X86.bytesAt_writeBytes_self t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * b))
        (xorBytes t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * b)) (w64 p.W + BitVec.ofNat 64 224) r) (by omega)
      rw [hl] at e
      have hs := Proof.Cmac.bytesAt_add t₂.mem (w64 p.W + BitVec.ofNat 64 224) r (16 - r)
      rw [show r + (16 - r) = 16 by omega, hks] at hs
      rw [hm₄, e, xorBytes, hs, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rfl
    have := GcmSiv.ctrPart_step ciph icb x _ (i := b) (n := r) (by omega) hk (by rw [hxl]; exact hx₂)
      (VG.Proof.AesGcmSiv.X86.frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; omega) (by omega)) hb'
    rwa [hxl, ← hn] at this
  · refine (fT.sub fun q hq => ?_).trans (fw.sub fun q hq => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨w64 p.D, p.n⟩, by simp, Offset.sub_base _ (by omega)⟩

/-- What `crypt` leaves, from `t`. -/
structure CryptPost (p : VG.Proof.AesGcmSiv.X86.Prm) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (VG.Proof.AesGcmSiv.X86.cryR p) t.mem t'.mem
  data : bytesAt t'.mem (w64 p.D) p.n =
    Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) (bytesAt t.mem (w64 p.D) p.n)

/-- The memory `cryptHead` leaves: the counter block from the tag, and the
data's length as the bytes left. -/
def headMem (m : Mem) (W : Addr) (n : Nat) : Mem :=
  (Proof.Cmac.store4 m (W + BitVec.ofNat 64 96) (m.readW (W + BitVec.ofNat 64 0) 32)
    (m.readW (W + BitVec.ofNat 64 4) 32) (m.readW (W + BitVec.ofNat 64 8) 32)
    (m.readW (W + BitVec.ofNat 64 12) 32 ||| 0x80000000#32)).writeW (W + BitVec.ofNat 64 176) (BitVec.ofNat 32 n)

/-- The start of `crypt`: the counter block from the tag, and the data as
the bytes to encrypt. -/
theorem cryptHead_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) :
    ∃ t₁ : State, runBlock isa cryptHead t = some t₁ ∧ t₁.mem = VG.Proof.AesGcmSiv.X86.headMem t.mem (w64 p.W) p.n ∧
      t₁.gpr .esi = p.D ∧ t₁.zf = some (decide (p.n / 16 = 0)) ∧ t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have hD := E.slots.data
  have hn := E.slots.len
  simp only [slotv_eq, dataO, lenO] at hD hn
  refine ⟨_, by simp only [cryptHead, onStr, wholeLeft]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · gmems [VG.Proof.AesGcmSiv.X86.headMem, Proof.Cmac.store4, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, hD, hn]
  · gmems [hD, Proof.Cmac.store4, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc]
  · gmems [hD, hn, VG.Proof.AesGcmSiv.X86.ofNat_lsr32 L.n32, Proof.Cmac.store4, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc]
    rw [BitVec.and_self, show BitVec.ofNat 32 (p.n / 16) = BitVec.ofNat 32 (p.n / 16) - BitVec.ofNat 32 0 by simp,
      sub_beq32 (by have := L.n32; omega) (by decide)]
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals rfl

/-- What `cryptHead` leaves, from `t`. -/
structure CStart (p : VG.Proof.AesGcmSiv.X86.Prm) (t t₁ : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t₁
  rd : t₁.rd = t.rd
  wr : t₁.wr = t.wr
  esi : t₁.gpr .esi = p.D
  z : t₁.zf = some (decide (p.n / 16 = 0))
  n : slotv t₁.mem p.W nO = BitVec.ofNat 32 p.n
  ctr : VG.Proof.AesGcmSiv.X86.CtrSt (w64 p.W) (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) 0 t₁.mem
  data : bytesAt t₁.mem (w64 p.D) p.n = bytesAt t.mem (w64 p.D) p.n
  ciph : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
    Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R
  frame : Frame (VG.Proof.AesGcmSiv.X86.cryR p) t.mem t₁.mem

theorem cryptStart_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) :
    ∃ t₁, runBlock isa cryptHead t = some t₁ ∧ VG.Proof.AesGcmSiv.X86.CStart p t t₁ := by
  have hw := L.ww
  have hn := L.n32
  obtain ⟨t₁, run₁, hm₁, si₁, z₁, bp₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.cryptHead_ok L E
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem (w64 p.D) p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 96, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem t₁.mem := by
    rw [hm₁, VG.Proof.AesGcmSiv.X86.headMem]
    exact ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
  have dD : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩],
      (⟨w64 p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact L.d_w' (by decide)
  have hx₁ : bytesAt t₁.mem (w64 p.D) p.n = bytesAt t.mem (w64 p.D) p.n :=
    Proof.AesGcm.X86.bytesAt_frame f₁ dD (by omega)
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
      Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;>
        exact (Lay.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  have hcb : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 96) 16 =
      bytesAt (Proof.Cmac.store4 t.mem (w64 p.W + BitVec.ofNat 64 96) (t.mem.readW (w64 p.W + BitVec.ofNat 64 0) 32)
        (t.mem.readW (w64 p.W + BitVec.ofNat 64 4) 32) (t.mem.readW (w64 p.W + BitVec.ofNat 64 8) 32)
        (t.mem.readW (w64 p.W + BitVec.ofNat 64 12) 32 ||| 0x80000000#32)) (w64 p.W + BitVec.ofNat 64 96) 16 := by
    rw [hm₁, VG.Proof.AesGcmSiv.X86.headMem]
    exact Proof.AesGcm.X86.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)
  have hicb : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 96) 16 =
      Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16) := by
    rw [hcb, Proof.Cmac.bytesAt_store4, BitVec.add_zero, ← GcmSiv.Words32.initialCounter_words,
      Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
      ← Proof.Cmac.bytesAt_split4]
  have h4 := Proof.Cmac.bytesAt_add t₁.mem (w64 p.W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc] at h4
  have C₀ : VG.Proof.AesGcmSiv.X86.CtrSt (w64 p.W) (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) 0 t₁.mem := by
    refine ⟨?_, ?_⟩
    · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  have fm₁ : Frame (VG.Proof.AesGcmSiv.X86.cryR p) t.mem t₁.mem := f₁.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  have E₁ : VG.Proof.AesGcmSiv.X86.Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (VG.Proof.AesGcmSiv.X86.frame_toMut fm₁ (VG.Proof.AesGcmSiv.X86.inMut_cryR p))
  have n₁ : slotv t₁.mem p.W nO = BitVec.ofNat 32 p.n := by rw [slotv_eq, hm₁, VG.Proof.AesGcmSiv.X86.headMem, Mem.readW_writeW_self32]
  exact ⟨t₁, run₁, E₁, rd₁, wr₁, si₁, z₁, n₁, C₀, hx₁, hc₁, fm₁⟩

theorem crypt_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) :
    WP isa (crypt v.callees) t (VG.Proof.AesGcmSiv.X86.CryptPost p t) := by
  have hw := L.ww
  have hn := L.n32
  obtain ⟨t₁, run₁, ⟨E₁, rd₁, wr₁, si₁, z₁, n₁, C₀, hx₁, hc₁, fm₁⟩⟩ := VG.Proof.AesGcmSiv.X86.cryptStart_ok L E
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem (w64 p.D) p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The whole blocks.
  have hmid : WP isa (.ite .e (.block []) (.loop (cryptBlock v.callees) .ne)) t₁
      (VG.Proof.AesGcmSiv.X86.BlocksPost p (Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) (bytesAt t.mem (w64 p.D) p.n) (p.n / 16) t₁) := by
    refine WP.ite (decide (p.n / 16 = 0)) (VG.Proof.AesGcmSiv.X86.eval_e z₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : p.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨E₁, rfl, rfl, by rw [si₁, Nat.mul_zero, BitVec.add_zero], by rw [n₁, Nat.mul_zero, Nat.sub_zero], C₀,
        by rw [Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁], Frame.refl _ _⟩
    · have h0 : p.n / 16 ≠ 0 := by simpa using hf
      exact VG.Proof.AesGcmSiv.X86.blocks_ok v L E₁ hxl (by omega) si₁ n₁ C₀ hx₁ hc₁
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  have n₂ : slotv t₂.mem p.W nO = BitVec.ofNat 32 (p.n % 16) := by rw [B.n]; congr 1; omega
  obtain ⟨t₃, run₃, z₃, E₃, si₃, m₃, rd₃, wr₃⟩ := VG.Proof.AesGcmSiv.X86.anyLeft_ok L B.env (by omega) n₂
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  refine WP.ite (decide (p.n % 16 = 0)) (VG.Proof.AesGcmSiv.X86.eval_e z₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨E₃, by rw [rd₃, B.rd, rd₁], by rw [wr₃, B.wr, wr₁], by rw [m₃]; exact fm₁.trans B.frame, ?_⟩
    rw [m₃, B.data, show 16 * (p.n / 16) = p.n by omega, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : p.n % 16 ≠ 0 := by simpa using hf
    have hc₂ : Spec.GcmSiv.ctxCiph t₃.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
        Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R := by
      rw [m₃, VG.Proof.AesGcmSiv.X86.ciph_cryR L B.frame, hc₁]
    refine WP.mono (VG.Proof.AesGcmSiv.X86.cryptTail_ok v L E₃ hxl (b := p.n / 16) (r := p.n % 16) (by omega) (by omega) (by omega)
      (by rw [si₃, B.esi]) (by rw [slotv_eq, m₃]; exact n₂) (m₃ ▸ B.ctr) (by rw [m₃]; exact B.data) hc₂)
      fun t₄ T => ?_
    refine ⟨T.env, by rw [T.rd, rd₃, B.rd, rd₁], by rw [T.wr, wr₃, B.wr, wr₁],
      (fm₁.trans (m₃ ▸ B.frame)).trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Cmp`. -/
section

/-!
# AES-GCM-SIV on x86: comparing the tags and masking the data

Untrusted: everything here is checked by Lean. `cmp` sets `eax` to 1 if the
tags at `W` and `W + 240` are equal and 0 if not, without a branch, as
AES-GCM's `cmpTail` does (`cmp_ok`); `mask` ANDs every byte of the data with
`0 − eax`: it keeps the data if `eax` is 1 and zeroes it if `eax` is 0
(`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq bytes16_eq xor4_eq_zero w64_add in_of_covers succ_ofNat32 add_zero32
  pred_count pred_beq bytesAt_succ length_bytesAt and_self_beq32 readW_writeW_off covers_left)

/-- `cmp eax, 1` and `adc` of 0 after the OR of the XORs of two blocks' words:
1 if they are equal, else 0. -/
theorem cmpAdc (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 32) :
    0#32 + 0#32 + BitVec.setWidth 32 (BitVec.ofBool (decide
      ((a₀ ^^^ b₀ ||| a₁ ^^^ b₁ ||| a₂ ^^^ b₂ ||| a₃ ^^^ b₃).toNat < (1#32).toNat))) =
      BitVec.ofNat 32 (if a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ then 1 else 0) := by
  have e := xor4_eq_zero a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
  by_cases h : a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp only [and_self, ↓reduceIte, BitVec.xor_self, BitVec.or_self]
    decide
  · have h0 : (a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃) ≠ 0 := fun h' => h (e.mp h')
    have hne : ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat ≠ 0 := fun h' =>
      h0 (BitVec.eq_of_toNat_eq (by simpa using h'))
    have hlt : ¬ ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat < (1#32).toNat := by
      rw [BitVec.toNat_ofNat]; omega
    simp only [h, ↓reduceIte, decide_eq_false hlt]
    rfl

/-- Whether the tags at `W` and `W + 240` are equal, as a word. -/
abbrev okVal (m : Mem) (W : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (if bytesAt m (w64 W) 16 = bytesAt m (w64 W + BitVec.ofNat 64 240) 16 then 1 else 0)

theorem cmp_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) :
    ∃ t', runBlock isa cmp t = some t' ∧ t'.gpr .eax = VG.Proof.AesGcmSiv.X86.okVal t.mem p.W ∧ t'.mem = t.mem ∧
      t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [Impl.AesGcmSiv.X86.cmp, E.ebp, L.aW, E.perm.wR], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gregs []
    rw [VG.Proof.AesGcmSiv.X86.cmpAdc]
    simp only [VG.Proof.AesGcmSiv.X86.okVal, bytes16_eq, BitVec.add_zero, VG.Proof.AesGcmSiv.X86.add_ofNat_assoc, Nat.reduceAdd]
  · gmems []
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals gmems []

/-! ## `mask` -/

theorem mask_byte32 (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - BitVec.ofNat 32 (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show BitVec.ofNat 32 (if true = true then 1 else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.movzx8 .edx (at_ .edi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .edi 0) .dl, .alu .add .edi (imm 1),
    .alu .sub .ecx (imm 1)]

theorem maskStep_ok (s : State) {P : BitVec 32} {i n : Nat} {c : Bool} (hs : s.gpr .edi = P + BitVec.ofNat 32 i)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i)) (hb : s.gpr .ebx = 0 - BitVec.ofNat 32 (if c then 1 else 0))
    (eP : w64 (P + BitVec.ofNat 32 i) = w64 P + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 P + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa VG.Proof.AesGcmSiv.X86.maskBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 P + BitVec.ofNat 64 i) ((if c then s.mem (w64 P + BitVec.ofNat 64 i) else 0 : Byte)) ∧
      s'.gpr .edi = P + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by grun [VG.Proof.AesGcmSiv.X86.maskBody, add_zero32, hs, eP, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hb, VG.Proof.AesGcmSiv.X86.mask_byte32]
  · gregs [hs, succ_ofNat32]
  · gregs [hc]
  · gmems [hc]
  · intro r h₁ h₂ h₃; gregs [h₁, h₂, h₃]
  all_goals gmems []

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else Spec.GcmSiv.zeros j).length = j := by
  cases c <;> simp [Spec.GcmSiv.zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else Spec.GcmSiv.zeros (j + 1)) =
      (if c then bytesAt m P j else Spec.GcmSiv.zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [Spec.GcmSiv.zeros, bytesAt_succ, List.replicate_succ']

/-- What `mask` leaves, from `t`, for `eax` 1 (`c`) or 0. -/
structure MaskPost (p : VG.Proof.AesGcmSiv.X86.Prm) (c : Bool) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  eax : t'.gpr .eax = t.gpr .eax
  mem : t'.mem = writeBytes t.mem (w64 p.D) (if c then bytesAt t.mem (w64 p.D) p.n else Spec.GcmSiv.zeros p.n)

/-- The test of `mask`: `ebx := 0 − eax`, and ZF set iff there is no data. -/
theorem maskTest_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {s : State} (E : VG.Proof.AesGcmSiv.X86.Env p s) :
    ∃ s₁, runBlock isa
      [.mov .ebx (imm 0), .alu .sub .ebx (.reg .eax), .mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s =
        some s₁ ∧ s₁.mem = s.mem ∧ s₁.gpr .ebx = 0 - s.gpr .eax ∧
      s₁.gpr .ecx = BitVec.ofNat 32 p.n ∧ s₁.zf = some (decide (p.n = 0)) ∧ s₁.gpr .eax = s.gpr .eax ∧
      VG.Proof.AesGcmSiv.X86.Env p s₁ ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have hn32 := L.n32
  have hlen := E.slots.len
  simp only [slotv_eq, lenO] at hlen
  obtain ⟨s₁, run₁, m₁, bx₁, cx₁, zf₁, ax₁, bp₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .ebx (imm 0), .alu .sub .ebx (.reg .eax), .mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s =
        some s₁ ∧ s₁.mem = s.mem ∧ s₁.gpr .ebx = 0 - s.gpr .eax ∧
      s₁.gpr .ecx = BitVec.ofNat 32 p.n ∧ s₁.zf = some (decide (p.n = 0)) ∧ s₁.gpr .eax = s.gpr .eax ∧
      s₁.gpr .ebp = p.W ∧ s₁.gpr .esp = p.SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · gregs []; rfl
    · gregs [hlen]
    · gmems [hlen]; rw [and_self_beq32 hn32]
    · gregs []
    · gregs [E.ebp]
    · gregs [E.esp]
    all_goals gmems []
  exact ⟨s₁, run₁, m₁, bx₁, cx₁, zf₁, ax₁, E.keep (by rw [bp₁, E.ebp]) (by rw [sp₁, E.esp]) rd₁ wr₁ m₁, rd₁, wr₁⟩

/-- The data's address in `edi`. -/
theorem maskArgs_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {s₁ : State} (E₁ : VG.Proof.AesGcmSiv.X86.Env p s₁) :
    ∃ s₂, runBlock isa [.mov .edi (slot dataO)] s₁ = some s₂ ∧ s₂.mem = s₁.mem ∧ s₂.gpr .edi = p.D ∧
      (∀ r, r ≠ .edi → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
  have hd₁ := E₁.slots.data
  simp only [slotv_eq, dataO] at hd₁
  exact ⟨_, by grun [E₁.ebp, L.aW, E₁.perm.wR, hd₁], by gmems [], by gregs [hd₁], fun r h => by gregs [h],
    by gmems [], by gmems []⟩

/-- Every byte of the data ANDed with `0 − eax`, for `eax` 1 or 0. -/
theorem mask_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {s : State} (E : VG.Proof.AesGcmSiv.X86.Env p s) {c : Bool}
    (hok : s.gpr .eax = BitVec.ofNat 32 (if c then 1 else 0)) : WP isa mask s (VG.Proof.AesGcmSiv.X86.MaskPost p c s) := by
  have hn32 := L.n32
  obtain ⟨s₁, run₁, m₁, bx₁, cx₁, zf₁, ax₁, E₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.maskTest_ok L E
  rw [hok] at bx₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (p.n = 0)) (VG.Proof.AesGcmSiv.X86.eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : p.n = 0 := of_decide_eq_true hb
    refine ⟨E₁, rd₁, wr₁, ax₁, ?_⟩
    rw [m₁, hn0]
    cases c <;> simp [Spec.Aes.bytesAt, Spec.GcmSiv.zeros, writeBytes_nil]
  have hn0 : 0 < p.n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  obtain ⟨s₂, run₂, m₂, di₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesGcmSiv.X86.maskArgs_ok L E₁
  rw [m₁] at m₂
  rw [rd₁] at rd₂
  rw [wr₁] at wr₂
  have bp₁ := E₁.ebp
  have sp₁ := E₁.esp
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hfD := L.dw
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcmSiv.X86.maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = p.n - j ∧ j < p.n ∧ t.gpr .edi = p.D + BitVec.ofNat 32 j ∧
      t.gpr .ecx = BitVec.ofNat 32 (p.n - j) ∧
      t.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) j else Spec.GcmSiv.zeros j) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t.gpr r = s₂.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (p.n - 0) _
    ⟨0, rfl, hn0, by rw [di₂, add_zero32], by rw [g₂ _ (by decide), cx₁, Nat.sub_zero], by
      rw [m₂]; cases c <;> simp [Spec.Aes.bytesAt, Spec.GcmSiv.zeros, writeBytes_nil], fun r _ _ _ => rfl, rd₂, wr₂⟩
  rintro k t ⟨j, rfl, hj, di, cx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', di', cx', zf', g', rd', wr'⟩ := VG.Proof.AesGcmSiv.X86.maskStep_ok t (P := p.D) (i := j) (n := p.n) (c := c) di cx
    (by rw [g _ (by decide) (by decide) (by decide), g₂ _ (by decide), bx₁]) (w64_add (by omega))
    (by rw [rd, wr]; exact in_of_covers (covers_left E.perm.d) hj (by omega))
    (by rw [wr]; exact in_of_covers E.perm.d hj (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨w64 p.D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesGcmSiv.X86.length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (w64 p.D + BitVec.ofNat 64 j) = s.mem (w64 p.D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 p.D) (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem (w64 p.D)
      (if c then bytesAt s.mem (w64 p.D) (j + 1) else Spec.GcmSiv.zeros (j + 1)) := by
    rw [mem', hq, mem, VG.Proof.AesGcmSiv.X86.mask_succ, writeBytes_snoc _ _ _ _ (by rw [VG.Proof.AesGcmSiv.X86.length_mask]; omega), VG.Proof.AesGcmSiv.X86.length_mask]
  have hz : t'.zf = some (decide (j + 1 = p.n)) := by rw [zf', pred_beq hj hn32]
  have gg : ∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t'.gpr r = s₂.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  have fm : Frame (VG.Proof.AesGcmSiv.X86.mutR p) s.mem t'.mem := by
    rw [hmem]
    have f0 : Frame [⟨w64 p.D, j + 1⟩] s.mem (writeBytes s.mem (w64 p.D)
        (if c then bytesAt s.mem (w64 p.D) (j + 1) else Spec.GcmSiv.zeros (j + 1))) :=
      writeBytes_frame _ _ _ (by rw [VG.Proof.AesGcmSiv.X86.length_mask]; exact Region.contains_self _ _)
    exact VG.Proof.AesGcmSiv.X86.frame_toMut f0 fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨w64 p.D, p.n⟩, by simp, Region.sub_prefix (by omega)⟩
  have E' : VG.Proof.AesGcmSiv.X86.Env p t' := E.mut L (by rw [gg _ (by decide) (by decide) (by decide), g₂ _ (by decide), bp₁])
    (by rw [gg _ (by decide) (by decide) (by decide), g₂ _ (by decide), sp₁]) (by rw [rd', rd]) (by rw [wr', wr]) fm
  have ax' : t'.gpr .eax = s.gpr .eax := by
    rw [gg _ (by decide) (by decide) (by decide), g₂ _ (by decide), ax₁]
  by_cases he : j + 1 = p.n
  · left
    exact ⟨by simp [eval, hz, he], E', by rw [rd', rd], by rw [wr', wr], ax', by rw [hmem, he]⟩
  · right
    refine ⟨by simp [eval, hz, he], p.n - (j + 1), by omega, j + 1, rfl, by omega, di',
      by rw [cx', pred_count hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.TagIO`. -/
section

/-!
# AES-GCM-SIV on x86: the tag in and out

Untrusted: everything here is checked by Lean. `open` copies the received
tag from `tag` to `W` (`recvTag_ok`), and `seal` copies the tag it computed
at `W` out to `tag` (`tagOut_ok`): both load the pointer from its slot, then
all four words, then store them, so constant time from `ebp`, then from the
pointer (`recvTag_ct`, `tagOut_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq w64_add in_off in_left)

/-- The pointer to the tag, loaded. -/
theorem tagPtr_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) :
    ∃ t', runBlock isa [.mov .edi (slot tpO)] t = some t' ∧ t'.gpr .edi = p.T ∧ t'.mem = t.mem ∧
      (∀ r, r ≠ .edi → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hT := E.slots.tp
  simp only [slotv_eq, tpO] at hT
  exact ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hT], by gregs [hT], by gmems [], fun r h => by gregs [h], by gmems [],
    by gmems []⟩

theorem recvTag_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) :
    WP isa recvTag t fun t' => VG.Proof.AesGcmSiv.X86.Env p t' ∧ bytesAt t'.mem (w64 p.W) 16 = bytesAt t.mem (w64 p.T) 16 ∧
      Frame [⟨w64 p.W, 16⟩] t.mem t'.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, di₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.tagPtr_ok L E
  have aT : ∀ {k}, k < 16 → w64 (p.T + BitVec.ofNat 32 k) = w64 p.T + BitVec.ofNat 64 k := fun hk =>
    w64_add (by have := L.tw; omega)
  have tIn : ∀ {k}, k + 4 ≤ 16 → InRegions (t₁.rd ++ t₁.wr) (w64 p.T + BitVec.ofNat 64 k) 4 := fun hk => by
    rw [rd₁, wr₁]; exact in_off E.perm.t hk (by decide)
  have bp₁ : t₁.gpr .ebp = p.W := by rw [g₁ _ (by decide), E.ebp]
  have wIn : ∀ {d}, d + 4 ≤ 2816 → InRegions t₁.wr (w64 p.W + BitVec.ofNat 64 d) 4 := fun hd => by
    rw [wr₁]; exact E.perm.wW hd
  have hs := Proof.AesGcm.X86.store4_eq t₁.mem p.W 0
  simp only [Nat.reduceAdd] at hs
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain ⟨t₂, run₂, hm₂, bp₂, sp₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa
      [.mov .eax (.mem (at_ .edi 0)), .mov .ecx (.mem (at_ .edi 4)), .mov .edx (.mem (at_ .edi 8)),
        .mov .ebx (.mem (at_ .edi 12)), .store (at_ .ebp tagO) .eax, .store (at_ .ebp (tagO + 4)) .ecx,
        .store (at_ .ebp (tagO + 8)) .edx, .store (at_ .ebp (tagO + 12)) .ebx] t₁ = some t₂ ∧
      t₂.mem = Cmac.store4 t₁.mem (w64 p.W + BitVec.ofNat 64 0) (t₁.mem.readW (w64 p.T + BitVec.ofNat 64 0) 32)
        (t₁.mem.readW (w64 p.T + BitVec.ofNat 64 4) 32) (t₁.mem.readW (w64 p.T + BitVec.ofNat 64 8) 32)
        (t₁.mem.readW (w64 p.T + BitVec.ofNat 64 12) 32) ∧
      t₂.gpr .ebp = p.W ∧ t₂.gpr .esp = p.SP ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr :=
    ⟨_, by grun [di₁, aT, tIn, bp₁, L.aW, wIn], by gmems [di₁, bp₁, aT, L.aW, hs], by gregs [bp₁],
      by gregs [g₁ _ (by decide : Reg.esp ≠ .edi), E.esp], by gmems [rd₁], by gmems [wr₁]⟩
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  have f : Frame [⟨w64 p.W, 16⟩] t.mem t₂.mem := by
    rw [hm₂, m₁, BitVec.add_zero]; exact Cmac.frame_store4 _ _ _ _ _
  refine ⟨E.mut L bp₂ sp₂ rd₂ wr₂ (VG.Proof.AesGcmSiv.X86.frame_toMut f fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; simpa using VG.Proof.AesGcmSiv.X86.inMut_w p (d := 0) (k := 16) (.inl (by decide))),
    ?_, f, rd₂, wr₂⟩
  rw [hm₂, m₁, BitVec.add_zero, Cmac.bytesAt_store4, Cmac.bytesAt_split4, Cmac.le4_readW, Cmac.le4_readW,
    Cmac.le4_readW, Cmac.le4_readW, BitVec.add_zero]

theorem recvTag_ct {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) : CT (VG.Proof.AesGcmSiv.X86.Env p) recvTag :=
  CT.seq (J := fun s => s.gpr .ebp = p.W ∧ s.gpr .edi = p.T)
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h.ebp) (by taint_decide))
    (fun t E => let ⟨t₁, run₁, di₁, _, g₁, _⟩ := VG.Proof.AesGcmSiv.X86.tagPtr_ok L E
      WP.of_runBlock ⟨t₁, run₁, by rw [g₁ _ (by decide), E.ebp], di₁⟩)
    (CT.taint [.ebp, .edi] (VG.Proof.AesGcmSiv.X86.pin2 fun _ h => h) (by taint_decide))

theorem tagOut_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) (tW : Covers [⟨w64 p.T, 16⟩] t.wr) :
    WP isa tagOut t fun t' => bytesAt t'.mem (w64 p.T) 16 = bytesAt t.mem (w64 p.W) 16 ∧
      Frame [⟨w64 p.T, 16⟩] t.mem t'.mem ∧ t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧ t'.gpr .eax = t.mem.readW
        (w64 p.W) 32 ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hT := E.slots.tp
  simp only [slotv_eq, tpO] at hT
  have aT : ∀ {k}, k < 16 → w64 (p.T + BitVec.ofNat 32 k) = w64 p.T + BitVec.ofNat 64 k := fun hk =>
    w64_add (by have := L.tw; omega)
  have tIn : ∀ {k}, k + 4 ≤ 16 → InRegions t.wr (w64 p.T + BitVec.ofNat 64 k) 4 := fun hk => in_off tW hk (by decide)
  have hs := Proof.AesGcm.X86.store4_eq t.mem p.T 0
  simp only [Nat.reduceAdd] at hs
  refine WP.seq (WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hT], ?_⟩)
  refine WP.of_runBlock ⟨_, by grun [aT, tIn, hT], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hs, hT]
    rw [BitVec.add_zero, Cmac.bytesAt_store4, Cmac.bytesAt_split4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW,
      Cmac.le4_readW, BitVec.add_zero]
  · gmems [hs, hT]
    rw [BitVec.add_zero]
    exact Cmac.frame_store4 _ _ _ _ _
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []; rw [BitVec.add_zero]
  · gmems []
  · gmems []

theorem tagOut_ct {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) : CT (VG.Proof.AesGcmSiv.X86.Env p) tagOut :=
  CT.seq (J := fun s => s.gpr .edi = p.T) (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h.ebp) (by taint_decide))
    (fun t E => by
      have hT := E.slots.tp
      simp only [slotv_eq, tpO] at hT
      exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hT], by gregs [hT]⟩)
    (CT.taint [.edi] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide))

/-! ## Writes to the tag -/

/-- A part of `W` misses the tag. -/
theorem w_t {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {d k : Nat} (h : d + k ≤ 2816) :
    ∀ r ∈ [(⟨w64 p.T, 16⟩ : Region)], (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact (L.t_w.sub_right (Lay.wSub h)).symm

/-- An environment, after code that writes only the tag. -/
theorem Env.tag {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {s s' : State} (h : VG.Proof.AesGcmSiv.X86.Env p s) (hbp : s'.gpr .ebp = p.W)
    (hsp : s'.gpr .esp = p.SP) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame [⟨w64 p.T, 16⟩] s.mem s'.mem) : VG.Proof.AesGcmSiv.X86.Env p s' := by
  have k : ∀ o, o + 4 ≤ 2816 → slotv s'.mem p.W o = slotv s.mem p.W o := fun o ho =>
    hf.readW (r := ⟨w64 p.W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (VG.Proof.AesGcmSiv.X86.w_t L ho) (by decide)
  have S := h.slots
  exact ⟨hbp, hsp, h.perm.of_eq hrd hwr, by rw [k _ (by decide)]; exact S.ctx, by rw [k _ (by decide)]; exact S.rounds,
    by rw [k _ (by decide)]; exact S.nonce, by rw [k _ (by decide)]; exact S.aad,
    by rw [k _ (by decide)]; exact S.alen, by rw [k _ (by decide)]; exact S.data,
    by rw [k _ (by decide)]; exact S.len, by rw [k _ (by decide)]; exact S.tp⟩

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Seal`. -/
section

/-!
# AES-GCM-SIV on x86: `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, the tag
copied out to `tag` and the restore compute `encryptWith` (RFC 8452 §4) of
the arguments (`seal_wp`), given that the tag input computed with GHASH is
the RFC's (`Proof.GcmSiv.Words.tagInputG`, related to it by
`Proof.GcmSiv.Polyval.tagInput_eq_tagInputG`). Each
piece writes only `mutR`, which keeps the slots, our caller's registers,
the return address, the key schedule, the nonce and the additional data.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.X86 (w64 SavedAt GcmImpl covers_left)

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
abbrev TagInputEq : Prop := ∀ a n pt d : List Byte, Spec.GcmSiv.tagInput a n pt d = tagInputG a n pt d

/-- The end: our caller's registers restored. -/
theorem exit_ok {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {s₀ t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) (hsp : p.SP = s₀.gpr .esp)
    (hs : SavedAt t.mem p.W s₀) (hret : t.mem.readW (w64 p.SP) 32 = s₀.mem.readW (w64 p.SP) 32) :
    WP isa (.block Impl.AesGcm.X86.restore) t fun s' => abiPreserved s₀ s' ∧ s'.mem = t.mem ∧
      s'.gpr .eax = t.gpr .eax :=
  WP.mono (Proof.AesGcm.X86.exit_ok E.ebp (by rw [E.esp, hsp]) (covers_left E.perm.w2560)
    (by have := L.ww; omega) hs (by rw [← hsp]; exact hret)) fun _ ⟨a, m, r, _⟩ => ⟨a, m, r⟩

/-- What the entry wrote is in our caller's registers and the slots. -/
theorem entered_mut {s : State} {p : VG.Proof.AesGcmSiv.X86.Prm} {s₁ : State} (L : VG.Proof.AesGcmSiv.X86.Lay p) (En : VG.Proof.AesGcmSiv.X86.Entered s p s₁) :
    s₁.mem.readW (w64 p.SP) 32 = s.mem.readW (w64 p.SP) 32 ∧
      Spec.GcmSiv.ctxCiph s₁.mem (w64 p.K) p.R = Spec.GcmSiv.ctxCiph s.mem (w64 p.K) p.R ∧
      bytesAt s₁.mem (w64 p.N) 12 = bytesAt s.mem (w64 p.N) 12 ∧
      bytesAt s₁.mem (w64 p.A) p.al = bytesAt s.mem (w64 p.A) p.al ∧
      bytesAt s₁.mem (w64 p.D) p.n = bytesAt s.mem (w64 p.D) p.n ∧
      bytesAt s₁.mem (w64 p.W) 16 = bytesAt s.mem (w64 p.W) 16 := by
  have f := En.frame
  have d : ∀ {P : Addr} {k : Nat}, (⟨P, k⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ →
      ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 128, 48⟩ : Region)], (⟨P, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))
  refine ⟨Proof.AesGcm.X86.ret_kept f (d L.retW), ?_, Proof.AesGcm.X86.bytesAt_frame f (d L.n_w) (by decide),
    Proof.AesGcm.X86.bytesAt_frame f (d L.a_w) (by have := L.al32; omega),
    Proof.AesGcm.X86.bytesAt_frame f (d L.d_w) (by have := L.n32; omega),
    Proof.AesGcm.X86.bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using Lay.w_w (W := p.W) (a := 0) (n := 16) (d := 128) (k := 48) (.inl (by decide)) (by decide)
        (by decide)) (by decide)⟩
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.X86.bytesAt_frame f (d (L.k_w.sub_left (Region.sub_prefix L.rounds_le)))
    (by have := L.rounds_le; omega)]

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (v : GcmImpl) (hti : VG.Proof.AesGcmSiv.X86.TagInputEq) {s : State} (hs : VG.Proof.AesGcmSiv.X86.sealPre s) :
    WP isa («seal» v.callees) s fun s' => abiPreserved s s' ∧ sealX86.post s s' := by
  have h := VG.Proof.AesGcmSiv.X86.onePre_seal hs
  have tW : Covers [⟨w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T, 16⟩] s.wr := VG.Proof.AesGcmSiv.X86.covers_of_mem (by rw [hs.2.1]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have L := VG.Proof.AesGcmSiv.X86.lay_of h
  have hRb := L.rounds_le
  have hn := L.n32
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.entry_ok h) fun s₁ En => ?_)
  obtain ⟨ret₁, hK₁, n₁, a₁, d₁, -⟩ := VG.Proof.AesGcmSiv.X86.entered_mut L En
  -- The keys.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.keys_ok v L En.env) fun s₂ Ky => ?_)
  have f₂ := VG.Proof.AesGcmSiv.X86.frame_toMut Ky.frame (VG.Proof.AesGcmSiv.X86.inMut_keyR _)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.polyval_ok v L Ky.env Ky.hkey Ky.acc) fun s₃ Po => ?_)
  have f₃ := VG.Proof.AesGcmSiv.X86.frame_toMut Po.frame (VG.Proof.AesGcmSiv.X86.inMut_polyR _)
  -- The tag.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.tag_ok v L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  have f₄ := VG.Proof.AesGcmSiv.X86.frame_toMut Tg.frame (VG.Proof.AesGcmSiv.X86.inMut_tagWr _ (by decide))
  -- Counter mode.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.crypt_ok v L Tg.env) fun s₅ Cr => ?_)
  have f₅ := VG.Proof.AesGcmSiv.X86.frame_toMut Cr.frame (VG.Proof.AesGcmSiv.X86.inMut_cryR _)
  have f₂₅ := (f₂.trans f₃).trans (f₄.trans f₅)
  -- The tag copied out.
  have tW₅ : Covers [⟨w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T, 16⟩] s₅.wr := by rw [Cr.wr, Tg.wr, Po.wr, Ky.wr, En.wr]; exact tW
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.tagOut_ok L Cr.env tW₅) fun s₆ ⟨tg₆, f₆, bp₆, sp₆, _, rd₆, wr₆⟩ => ?_)
  have E₆ := Cr.env.tag L bp₆ sp₆ rd₆ wr₆ f₆
  have sv₆ : SavedAt s₆.mem (VG.Proof.AesGcmSiv.X86.prmOf s).W s :=
    (SavedAt.mut L f₂₅ En.saved).frame f₆ (VG.Proof.AesGcmSiv.X86.w_t L (d := 128) (k := 16) (by decide))
  have rT : ∀ q ∈ [(⟨w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T, 16⟩ : Region)], (⟨w64 (VG.Proof.AesGcmSiv.X86.prmOf s).SP, 4⟩ : Region).Disjoint q :=
    fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.retT
  have ret₆ : s₆.mem.readW (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).SP) 32 = s.mem.readW (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).SP) 32 := by
    rw [Proof.AesGcm.X86.ret_kept f₆ rT, VG.Proof.AesGcmSiv.X86.ret_mut L f₂₅, ret₁]
  have d₆ : bytesAt s₆.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n = bytesAt s₅.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n :=
    Proof.AesGcm.X86.bytesAt_frame f₆ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.t_d.symm) (by omega)
  -- `restore`.
  refine WP.mono (VG.Proof.AesGcmSiv.X86.exit_ok L E₆ rfl sv₆ ret₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).K) (VG.Proof.AesGcmSiv.X86.prmOf s).R)
      (Spec.GcmSiv.keyLen (VG.Proof.AesGcmSiv.X86.prmOf s).R) (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).N) 12)
      (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n) (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).A) (VG.Proof.AesGcmSiv.X86.prmOf s).al) =
    (bytesAt s'.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n, bytesAt s'.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T) 16)
  rw [hm, d₆, tg₆]
  -- What the pieces read.
  have n₂ : bytesAt s₂.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).N) 12 = bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).N) 12 := by
    rw [VG.Proof.AesGcmSiv.X86.nonce_mut L f₂, n₁]
  have a₂ : bytesAt s₂.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).A) (VG.Proof.AesGcmSiv.X86.prmOf s).al = bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).A) (VG.Proof.AesGcmSiv.X86.prmOf s).al := by
    rw [VG.Proof.AesGcmSiv.X86.aad_mut L f₂, a₁]
  have dk₂ : ∀ r ∈ VG.Proof.AesGcmSiv.X86.keyR (VG.Proof.AesGcmSiv.X86.prmOf s), (⟨w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D, (VG.Proof.AesGcmSiv.X86.prmOf s).n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  have d₂ : bytesAt s₂.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n = bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Ky.frame dk₂ (by omega), d₁]
  have d₄ : bytesAt s₄.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n = bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Tg.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.bd.symm) (by omega),
      Proof.AesGcm.X86.bytesAt_frame Po.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact L.d_w' (by decide)
        · exact VG.Proof.AesGcmSiv.X86.absorbR_buf L.d_w L.bd r hr) (by omega), d₂]
  have dS : ∀ {rs : List Region}, (∀ r ∈ rs, (⟨w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 512, 240⟩ : Region).Disjoint r) →
      ∀ {m m' : Mem}, Frame rs m m' → Spec.GcmSiv.ctxCiph m' (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 512) (VG.Proof.AesGcmSiv.X86.prmOf s).R =
        Spec.GcmSiv.ctxCiph m (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 512) (VG.Proof.AesGcmSiv.X86.prmOf s).R := fun hd m m' hf => by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega)]
  have key₃ : Spec.GcmSiv.ctxCiph s₃.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 512) (VG.Proof.AesGcmSiv.X86.prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 512) (VG.Proof.AesGcmSiv.X86.prmOf s).R := by
    refine dS (fun r hr => ?_) Po.frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  have key₄ : Spec.GcmSiv.ctxCiph s₄.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 512) (VG.Proof.AesGcmSiv.X86.prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 512) (VG.Proof.AesGcmSiv.X86.prmOf s).R := by
    refine (dS (fun r hr => ?_) Tg.frame).trans key₃
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  have t₅ : bytesAt s₅.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s₄.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 0) 16 := by
    refine Proof.AesGcm.X86.bytesAt_frame Cr.frame (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.d_w' (by decide)).symm
    · exact (L.bw' (by decide)).symm
  rw [BitVec.add_zero] at t₅
  have tg := Tg.out
  rw [BitVec.add_zero] at tg
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have po := Po.out
  rw [n₂, a₂, d₂] at po
  rw [Cr.data, t₅, d₄, key₄, ci, tg, key₃, ci, po, ← au]
  unfold Spec.GcmSiv.encryptWith
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).K) (VG.Proof.AesGcmSiv.X86.prmOf s).R)
    (Spec.GcmSiv.keyLen (VG.Proof.AesGcmSiv.X86.prmOf s).R) (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).N) 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Open`. -/
section

/-!
# AES-GCM-SIV on x86: `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the received tag
copied to `W`, the keys, counter mode on the data from it, POLYVAL of the
result and the tag input, its tag at `W + 240`, the comparison, the mask and
the restore compute `decryptWith` (RFC 8452 §5) of the arguments (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.X86 (w64 SavedAt GcmImpl covers_left length_bytesAt)

theorem decrypt_eq (hti : VG.Proof.AesGcmSiv.X86.TagInputEq) (ciph : Spec.GcmSiv.Cipher) (kl : Nat) (nonce ct aad tag : List Byte) :
    Spec.GcmSiv.decryptWith ciph kl nonce ct aad tag =
      let dk := Spec.GcmSiv.deriveKeys ciph kl nonce
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 nonce
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct) aad) = tag then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct)
      else none := by
  unfold Spec.GcmSiv.decryptWith
  generalize Spec.GcmSiv.deriveKeys ciph kl nonce = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

/-- Counter mode after the keys keeps what POLYVAL starts from. -/
theorem keys_crypt {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {σ s₂ s₃ : State} (Ky : VG.Proof.AesGcmSiv.X86.KeysPost p σ s₂) (Cr : VG.Proof.AesGcmSiv.X86.CryptPost p s₂ s₃) :
    Spec.Gcm.blockAt s₃.mem (w64 p.W + BitVec.ofNat 64 64) =
      GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 16) 16)) ∧
    Spec.Gcm.blockAt s₃.mem (w64 p.W + BitVec.ofNat 64 80) = 0 ∧
    bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (w64 p.W + BitVec.ofNat 64 16) 16 := by
  have dCr : ∀ {d : Nat}, 16 ≤ d → d + 16 ≤ 96 → ∀ r ∈ VG.Proof.AesGcmSiv.X86.cryR p,
      (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.d_w' (by omega)).symm
    · exact (L.bw' (by omega)).symm
  have a₃ : bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (w64 p.W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86.bytesAt_frame Cr.frame (dCr (by decide) (by decide)) (by decide)
  refine ⟨?_, ?_, a₃⟩
  · rw [Proof.AesGcm.X86.blockAt_frame Cr.frame (dCr (by decide) (by decide)), Ky.hkey, a₃]
  · rw [Proof.AesGcm.X86.blockAt_frame Cr.frame (dCr (by decide) (by decide)), Ky.acc]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (v : GcmImpl) (hti : VG.Proof.AesGcmSiv.X86.TagInputEq) {s : State} (hs : VG.Proof.AesGcmSiv.X86.openPre s) :
    WP isa («open» v.callees) s fun s' => abiPreserved s s' ∧ openX86.post s s' := by
  have h := VG.Proof.AesGcmSiv.X86.onePre_open hs
  have L := VG.Proof.AesGcmSiv.X86.lay_of h
  have hRb := L.rounds_le
  have hn := L.n32
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.entry_ok h) fun s₀ En => ?_)
  obtain ⟨ret₀, hK₀, n₀, a₀, d₀, -⟩ := VG.Proof.AesGcmSiv.X86.entered_mut L En
  -- The received tag.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.recvTag_ok L En.env) fun s₁ ⟨E₁, tg₁, fr₁, _, _⟩ => ?_)
  have fr₁' : Frame (VG.Proof.AesGcmSiv.X86.mutR (VG.Proof.AesGcmSiv.X86.prmOf s)) s₀.mem s₁.mem := VG.Proof.AesGcmSiv.X86.frame_toMut fr₁ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    simpa using VG.Proof.AesGcmSiv.X86.inMut_w (VG.Proof.AesGcmSiv.X86.prmOf s) (d := 0) (k := 16) (.inl (by decide))
  have ret₁ : s₁.mem.readW (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).SP) 32 = s.mem.readW (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).SP) 32 := by
    rw [VG.Proof.AesGcmSiv.X86.ret_mut L fr₁', ret₀]
  have hK₁ := (VG.Proof.AesGcmSiv.X86.ciph_mut L fr₁').trans hK₀
  have n₁ := (VG.Proof.AesGcmSiv.X86.nonce_mut L fr₁').trans n₀
  have a₁ := (VG.Proof.AesGcmSiv.X86.aad_mut L fr₁').trans a₀
  have d₁ : bytesAt s₁.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n = bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n :=
    (Proof.AesGcm.X86.bytesAt_frame fr₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.d_w.sub_right (Region.sub_prefix (by decide)))
      (by omega)).trans d₀
  have tag₁ : bytesAt s₁.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W) 16 = bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T) 16 := by
    rw [tg₁]
    exact Proof.AesGcm.X86.bytesAt_frame En.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.t_w.sub_right (Lay.wSub (by decide))) (by decide)
  have sv₁ := SavedAt.mut L fr₁' En.saved
  -- The keys.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.keys_ok v L E₁) fun s₂ Ky => ?_)
  have f₂ := VG.Proof.AesGcmSiv.X86.frame_toMut Ky.frame (VG.Proof.AesGcmSiv.X86.inMut_keyR _)
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.crypt_ok v L Ky.env) fun s₃ Cr => ?_)
  have f₃ := VG.Proof.AesGcmSiv.X86.frame_toMut Cr.frame (VG.Proof.AesGcmSiv.X86.inMut_cryR _)
  obtain ⟨hG₃, hY₃, a₃⟩ := VG.Proof.AesGcmSiv.X86.keys_crypt L Ky Cr
  -- POLYVAL of the plaintext and the tag input.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.polyval_ok v L Cr.env hG₃ hY₃) fun s₄ Po => ?_)
  have f₄ := VG.Proof.AesGcmSiv.X86.frame_toMut Po.frame (VG.Proof.AesGcmSiv.X86.inMut_polyR _)
  -- Its tag at `W + 240`.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.tag_ok v L Po.env (o := 240) (by decide)) fun s₅ Tg => ?_)
  have f₅ := VG.Proof.AesGcmSiv.X86.frame_toMut Tg.frame (VG.Proof.AesGcmSiv.X86.inMut_tagWr _ (by decide))
  -- The comparison.
  obtain ⟨s₆, run₆, ax₆, hm₆, bp₆, sp₆, rd₆, wr₆⟩ := VG.Proof.AesGcmSiv.X86.cmp_ok L Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : VG.Proof.AesGcmSiv.X86.Env (VG.Proof.AesGcmSiv.X86.prmOf s) s₆ := Tg.env.keep (by rw [bp₆, Tg.env.ebp]) (by rw [sp₆, Tg.env.esp]) rd₆ wr₆ hm₆
  have ax₆' : s₆.gpr .eax = BitVec.ofNat 32 (if decide (bytesAt s₅.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W) 16 =
      bytesAt s₅.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 240) 16) then 1 else 0) := by
    rw [ax₆]; simp only [VG.Proof.AesGcmSiv.X86.okVal, decide_eq_true_eq]
  -- The mask.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86.mask_ok L E₆ ax₆') fun s₇ Mk => ?_)
  have fM : Frame (VG.Proof.AesGcmSiv.X86.mutR (VG.Proof.AesGcmSiv.X86.prmOf s)) s₆.mem s₇.mem := by
    rw [Mk.mem]
    exact VG.Proof.AesGcmSiv.X86.frame_toMut (writeBytes_frame _ _ _ (by
      split <;> simp only [length_bytesAt, Spec.GcmSiv.zeros, List.length_replicate] <;>
        exact Region.contains_self _ _) : Frame [⟨w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D, (VG.Proof.AesGcmSiv.X86.prmOf s).n⟩] _ _) fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact VG.Proof.AesGcmSiv.X86.inMut_d _
  have f₂₇ : Frame (VG.Proof.AesGcmSiv.X86.mutR (VG.Proof.AesGcmSiv.X86.prmOf s)) s₁.mem s₇.mem := ((f₂.trans f₃).trans (f₄.trans f₅)).trans (hm₆ ▸ fM)
  -- The restore.
  refine WP.mono (VG.Proof.AesGcmSiv.X86.exit_ok L Mk.env rfl (SavedAt.mut L f₂₇ sv₁) (by rw [VG.Proof.AesGcmSiv.X86.ret_mut L f₂₇, ret₁]))
    fun s' ⟨ga, hm, hax⟩ => ⟨ga, ?_⟩
  -- What the pieces read.
  have n₃ : bytesAt s₃.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).N) 12 = bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).N) 12 := by
    rw [VG.Proof.AesGcmSiv.X86.nonce_mut L (f₂.trans f₃), n₁]
  have a₃' : bytesAt s₃.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).A) (VG.Proof.AesGcmSiv.X86.prmOf s).al = bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).A) (VG.Proof.AesGcmSiv.X86.prmOf s).al := by
    rw [VG.Proof.AesGcmSiv.X86.aad_mut L (f₂.trans f₃), a₁]
  have dK : ∀ r ∈ VG.Proof.AesGcmSiv.X86.keyR (VG.Proof.AesGcmSiv.X86.prmOf s), (⟨w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D, (VG.Proof.AesGcmSiv.X86.prmOf s).n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  have d₂ : bytesAt s₂.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n = bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Ky.frame dK (by omega), d₁]
  have tK : ∀ r ∈ VG.Proof.AesGcmSiv.X86.keyR (VG.Proof.AesGcmSiv.X86.prmOf s), (⟨w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  have tag₂ : bytesAt s₂.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T) 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame Ky.frame tK (by decide), BitVec.add_zero, tag₁]
  have tag₅ : bytesAt s₅.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T) 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame Tg.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm) (by decide),
      Proof.AesGcm.X86.bytesAt_frame Po.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm) (by decide),
      Proof.AesGcm.X86.bytesAt_frame Cr.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.d_w' (by decide)).symm
        · exact (L.bw' (by decide)).symm) (by decide), tag₂]
  rw [BitVec.add_zero] at tag₂ tag₅
  have dS : ∀ {rs : List Region}, (∀ r ∈ rs, (⟨w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 512, 240⟩ : Region).Disjoint r) →
      ∀ {m m' : Mem}, Frame rs m m' → Spec.GcmSiv.ctxCiph m' (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 512) (VG.Proof.AesGcmSiv.X86.prmOf s).R =
        Spec.GcmSiv.ctxCiph m (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 512) (VG.Proof.AesGcmSiv.X86.prmOf s).R := fun hd m m' hf => by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega)]
  have ci₄ : Spec.GcmSiv.ctxCiph s₄.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 512) (VG.Proof.AesGcmSiv.X86.prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).W + BitVec.ofNat 64 512) (VG.Proof.AesGcmSiv.X86.prmOf s).R := by
    rw [dS (fun r hr => ?_) Po.frame, VG.Proof.AesGcmSiv.X86.ciph_cryR L Cr.frame]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  have d₅ : bytesAt s₅.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n = bytesAt s₃.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Tg.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.bd.symm) (by omega),
      Proof.AesGcm.X86.bytesAt_frame Po.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact L.d_w' (by decide)
        · exact VG.Proof.AesGcmSiv.X86.absorbR_buf L.d_w L.bd r hr) (by omega)]
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have pt₃ := Cr.data
  rw [tag₂, d₂, ci] at pt₃
  have po := Po.out
  rw [a₃, ← au, n₃, a₃', pt₃] at po
  have tg := Tg.out
  rw [ci₄, ci, po] at tg
  have md := Mk.mem
  rw [hm₆, tg, tag₅] at md
  have ax : s'.gpr .eax = s₆.gpr .eax := by rw [hax, Mk.eax]
  rw [ax₆', tg, tag₅] at ax
  show VG.Proof.AesGcmSiv.X86.openPost (VG.Proof.AesGcmSiv.X86.openResult s) s' (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n
  have hdec : VG.Proof.AesGcmSiv.X86.openResult s =
      let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).K) (VG.Proof.AesGcmSiv.X86.prmOf s).R)
        (Spec.GcmSiv.keyLen (VG.Proof.AesGcmSiv.X86.prmOf s).R) (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).N) 12)
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).N) 12)
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T) 16))
            (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n)) (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).A) (VG.Proof.AesGcmSiv.X86.prmOf s).al)) =
          bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T) 16 then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T) 16))
          (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n))
      else none := VG.Proof.AesGcmSiv.X86.decrypt_eq hti _ _ _ _ _ _
  simp only at hdec
  have hD₅ : bytesAt s₅.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n = Spec.GcmSiv.ctr
      (Spec.GcmSiv.aes (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).K) (VG.Proof.AesGcmSiv.X86.prmOf s).R)
        (Spec.GcmSiv.keyLen (VG.Proof.AesGcmSiv.X86.prmOf s).R) (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).N) 12)).2)
      (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T) 16)) (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n) := by
    rw [d₅, pt₃]
  have hl : ∀ c : Bool, (if c then bytesAt s₅.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n
      else Spec.GcmSiv.zeros (VG.Proof.AesGcmSiv.X86.prmOf s).n).length = (VG.Proof.AesGcmSiv.X86.prmOf s).n := fun c => by
    cases c <;> simp [length_bytesAt, Spec.GcmSiv.zeros]
  have mD : ∀ c : Bool, bytesAt (writeBytes s₅.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (if c then bytesAt s₅.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n
      else Spec.GcmSiv.zeros (VG.Proof.AesGcmSiv.X86.prmOf s).n)) (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n =
      if c then bytesAt s₅.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n else Spec.GcmSiv.zeros (VG.Proof.AesGcmSiv.X86.prmOf s).n := fun c => by
    have e := Proof.AesGcm.X86.bytesAt_writeBytes_self s₅.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D)
      (if c then bytesAt s₅.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n else Spec.GcmSiv.zeros (VG.Proof.AesGcmSiv.X86.prmOf s).n)
      (by rw [hl]; omega)
    rwa [hl] at e
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).K) (VG.Proof.AesGcmSiv.X86.prmOf s).R)
    (Spec.GcmSiv.keyLen (VG.Proof.AesGcmSiv.X86.prmOf s).R) (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).N) 12) = dk at ax hdec md hD₅
  rw [hdec]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).N) 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T) 16))
        (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n)) (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).A) (VG.Proof.AesGcmSiv.X86.prmOf s).al)) =
      bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T) 16
  · refine VG.Proof.AesGcmSiv.X86.openPost_some (ite_eq_left_of_eq_true _ _ (eq_true hc)) ?_ ?_
    · rw [ax, ite_eq_left (decide_eq_true hc.symm)]; rfl
    · rw [hm, md, mD, hD₅, ite_eq_left (decide_eq_true hc.symm)]
  · have hc' : ¬bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T) 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1
        (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).N) 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).T) 16))
          (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).D) (VG.Proof.AesGcmSiv.X86.prmOf s).n)) (bytesAt s.mem (w64 (VG.Proof.AesGcmSiv.X86.prmOf s).A) (VG.Proof.AesGcmSiv.X86.prmOf s).al)) :=
      Ne.symm hc
    refine VG.Proof.AesGcmSiv.X86.openPost_none (ite_eq_right_of_eq_false _ _ (eq_false hc)) ?_ ?_
    · rw [ax, ite_eq_right (fun h => hc' (of_decide_eq_true h))]; rfl
    · rw [hm, md, mD, ite_eq_right (fun h => hc' (of_decide_eq_true h))]

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.KeysCT`. -/
section

/-!
# AES-GCM-SIV on x86: the keys are constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments (`Env p`) leak the same trace: the code between calls
by the taint analysis, from `ebp` and the registers holding pointers or
counts that the correctness proofs pin to public values (a pointer loaded
from a slot in the block that uses it is pinned after its load: `ldPin`);
each call by its callee's proof (`callCtr_ct`, `callKey_ct`); and a loop
with calls by its iterations, each from the public number of iterations
left (`CT.loopN`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq GcmImpl)

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

theorem CT.of_empty {I : State → Prop} {c : Prog isa} (h : ∀ s, ¬ I s) : CT I c :=
  RelCT.of_false fun s₁ _ hp => h s₁ hp.1

/-- A block that loads a register `r` from the slot `o` first, then uses it
(as an address): the rest is constant time from `ebp` and `r`, which holds
the public value `x` the slot holds. -/
theorem ldPin {I : State → Prop} {r : Reg} {o : Nat} {x : BitVec 32} {is : List Instr} {W : BitVec 32}
    (hW : ∀ s, I s → s.gpr .ebp = W ∧ slotv s.mem W o = x ∧ InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4)
    (hwW : W.toNat + o + 4 ≤ 2 ^ 32) (hr : r ≠ .ebp)
    {hc₁ : Taint.Hint VG.X86.taint.T}
    (h₁ : (VG.X86.taint.check (τr [.ebp]) (.block [.mov r (slot o)]) hc₁).isSome = true)
    {hc : Taint.Hint VG.X86.taint.T}
    (h : (VG.X86.taint.check (τr [.ebp, r]) (.block is) hc).isSome = true) :
    CT I (.block (.mov r (slot o) :: is)) := by
  have e : (.mov r (slot o) :: is : List Instr) = [.mov r (slot o)] ++ is := rfl
  rw [e]
  refine RelCT.block_append (CT.seq (J := fun s => s.gpr .ebp = W ∧ s.gpr r = x)
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun s h => (hW s h).1) h₁) (fun s hs => ?_)
    (CT.taint [.ebp, r] (VG.Proof.AesGcmSiv.X86.pin2 fun _ h => h) h))
  obtain ⟨bp, sl, ir⟩ := hW s hs
  have aW : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := Proof.AesGcm.X86.w64_add (by omega)
  simp only [slotv_eq] at sl
  have hr' : Reg.ebp ≠ r := fun h => hr h.symm
  refine WP.of_runBlock ⟨_, by grun [bp, aW, ir], ?_, ?_⟩
  · rw [VG.X86.RegUpd.gpr_setReg_of_ne _ _ hr', bp]
  · gregs [sl]

/-! ## `derive` -/

theorem deriveBlock_ct {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {I : State → Prop} (hI : ∀ s, I s → VG.Proof.AesGcmSiv.X86.Env p s) :
    CT I (.block deriveBlock) :=
  VG.Proof.AesGcmSiv.X86.ldPin (r := .eax) (o := nonceO) (x := p.N) (W := p.W)
    (fun s h => ⟨(hI s h).ebp, (hI s h).slots.nonce, (hI s h).perm.wR (by decide)⟩) (by have := L.ww; unfold nonceO; omega)
    (by decide) (by taint_decide) (by taint_decide)

theorem derivePost_ct {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {I : State → Prop} {i : Nat}
    (hI : ∀ s, I s → VG.Proof.AesGcmSiv.X86.Env p s ∧ slotv s.mem p.W iO = BitVec.ofNat 32 i) : CT I (.block derivePost) :=
  VG.Proof.AesGcmSiv.X86.ldPin (r := .edx) (o := iO) (x := BitVec.ofNat 32 i) (W := p.W)
    (fun s h => ⟨(hI s h).1.ebp, (hI s h).2, (hI s h).1.perm.wR (by decide)⟩) (by have := L.ww; unfold iO; omega)
    (by decide) (by taint_decide) (by taint_decide)

/-- The state of a step of `derive` before its call. -/
structure DerCall (p : VG.Proof.AesGcmSiv.X86.Prm) (i : Nat) (t₁ : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t₁
  key : VG.Proof.AesGcmSiv.X86.KeyOk p t₁ p.K
  dst : VG.Proof.AesGcmSiv.X86.Dst p t₁ p.K (p.W + BitVec.ofNat 32 224) (16 * 1)
  eax : t₁.gpr .eax = p.K
  ecx : t₁.gpr .ecx = BitVec.ofNat 32 p.R
  edx : t₁.gpr .edx = p.W + BitVec.ofNat 32 112
  ebx : t₁.gpr .ebx = p.W + BitVec.ofNat 32 224
  edi : t₁.gpr .edi = BitVec.ofNat 32 1
  ix : slotv t₁.mem p.W iO = BitVec.ofNat 32 i

theorem derCall_of {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {σ t t₁ : State} {i : Nat} (I : VG.Proof.AesGcmSiv.X86.DInv p σ i t)
    (run : runBlock isa deriveBlock t = some t₁) : VG.Proof.AesGcmSiv.X86.DerCall p i t₁ := by
  obtain ⟨u₁, run₁, hm₁, eax, ecx, edx, ebx, edi, bp₁, sp₁, -, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.derArgs_ok L I.env I.ix
  have e : u₁ = t₁ := Option.some.inj (run₁.symm.trans run)
  subst e
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t.mem u₁.mem := by
    rw [hm₁]; exact VG.Proof.AesGcmSiv.X86.derMem_frame _ _ _ _
  have E₁ : VG.Proof.AesGcmSiv.X86.Env p u₁ := I.env.mut L bp₁ sp₁ rd₁ wr₁ (VG.Proof.AesGcmSiv.X86.frame_toMut f₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide))
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  refine ⟨E₁, VG.Proof.AesGcmSiv.X86.keyK L E₁.perm, VG.Proof.AesGcmSiv.X86.dstW L E₁.perm (q := 224) (.inr ⟨by decide, by decide⟩) (L.k_w' (by decide)), eax,
    ecx, edx, ebx, edi, ?_⟩
  rw [← I.ix]
  exact f₁.readW (r := ⟨w64 p.W + BitVec.ofNat 64 180, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)

/-- A step of `derive`. -/
theorem derStep_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {i : Nat} :
    CT (fun s => ∃ σ, VG.Proof.AesGcmSiv.X86.DInv p σ i s) (.seq (.block deriveBlock) (.seq (callCtr v.callees) (.block derivePost))) := by
  refine CT.seq (J := VG.Proof.AesGcmSiv.X86.DerCall p i) (VG.Proof.AesGcmSiv.X86.deriveBlock_ct L fun s ⟨_, I⟩ => I.env) (fun t ⟨σ, I⟩ => by
      obtain ⟨t₁, run₁, -⟩ := VG.Proof.AesGcmSiv.X86.derArgs_ok L I.env I.ix
      exact WP.of_runBlock ⟨t₁, run₁, VG.Proof.AesGcmSiv.X86.derCall_of L I run₁⟩) ?_
  refine CT.seq (J := fun s => VG.Proof.AesGcmSiv.X86.Env p s ∧ slotv s.mem p.W iO = BitVec.ofNat 32 i)
    (VG.Proof.AesGcmSiv.X86.callCtr_ct v L (Q := p.K) (D := p.W + BitVec.ofNat 32 224) (n := 1) fun t₁ C =>
      ⟨C.env, C.key, C.dst, C.eax, C.ecx, C.edx, C.ebx, C.edi⟩)
    (fun t₁ C => WP.mono (VG.Proof.AesGcmSiv.X86.callCtr_ok v L C.env C.key C.dst
      (by rw [L.aW (by decide)]; exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))) C.eax C.ecx C.edx C.ebx
      C.edi) fun s P => ⟨P.env, ?_⟩) (VG.Proof.AesGcmSiv.X86.derivePost_ct L fun _ h => h)
  rw [← C.ix]
  exact P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 180, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · rw [L.aW (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm) (by decide)

theorem derive_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) : CT (VG.Proof.AesGcmSiv.X86.Env p) (derive v.callees) := by
  have hR := L.rounds
  have hk : 1 ≤ p.R / 2 - 1 := by rcases hR with h | h <;> rw [h] <;> decide
  refine CT.seq (J := fun s => ∃ σ, VG.Proof.AesGcmSiv.X86.DInv p σ 0 s) (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun s h => h.ebp) (by taint_decide))
    (fun σ E => by obtain ⟨t₀, run₀, I₀⟩ := VG.Proof.AesGcmSiv.X86.derive0_ok L E; exact WP.of_runBlock ⟨t₀, run₀, σ, I₀⟩) ?_
  refine (CT.loopN (fun k s => ∃ σ i, k = p.R / 2 - 1 - i ∧ i < p.R / 2 - 1 ∧ VG.Proof.AesGcmSiv.X86.DInv p σ i s) (fun k => ?_)
    (fun k s ⟨σ, i, hk', hi, I⟩ => ?_) (p.R / 2 - 1)).mono fun s ⟨σ, I⟩ => ⟨σ, 0, by omega, by omega, I⟩
  · by_cases hkk : 0 < k ∧ k ≤ p.R / 2 - 1
    · exact (VG.Proof.AesGcmSiv.X86.derStep_ct v L (i := p.R / 2 - 1 - k)).mono fun s ⟨σ, i, hk', hi, I⟩ => ⟨σ, by
        rw [show p.R / 2 - 1 - k = i by omega]; exact I⟩
    · exact CT.of_empty fun s ⟨σ, i, hk', hi, _⟩ => hkk ⟨by omega, by omega⟩
  · refine WP.mono (VG.Proof.AesGcmSiv.X86.derStep_ok v L hi I) fun s' ⟨I', hz⟩ => ⟨by omega, by rw [VG.Proof.AesGcmSiv.X86.eval_ne hz]; simp; omega,
      fun hk1 => ⟨σ, i + 1, by omega, by omega, I'⟩⟩

/-! ## `expand` and `hkey` -/

theorem expand_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) : CT (VG.Proof.AesGcmSiv.X86.Env p) (expand v.callees) := by
  refine CT.seq (J := fun t₁ => VG.Proof.AesGcmSiv.X86.Env p t₁ ∧ t₁.gpr .eax = p.W + BitVec.ofNat 32 32 ∧
      t₁.gpr .ecx = BitVec.ofNat 32 (Spec.GcmSiv.keyLen p.R) ∧ t₁.gpr .edx = p.W + BitVec.ofNat 32 512)
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun s h => h.ebp) (by taint_decide)) (fun s E => ?_) (VG.Proof.AesGcmSiv.X86.callKey_ct v L fun _ h => h)
  obtain ⟨t₁, run₁, eax, ecx, edx, bp, sp, _, rd, wr, hm⟩ := VG.Proof.AesGcmSiv.X86.expArgs_ok L E
  exact WP.of_runBlock ⟨t₁, run₁, E.keep (by rw [bp, E.ebp]) (by rw [sp, E.esp]) rd wr hm, eax, ecx, edx⟩

theorem keys_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) : CT (VG.Proof.AesGcmSiv.X86.Env p) (VG.Impl.AesGcmSiv.X86.keys v.callees) :=
  CT.seq (VG.Proof.AesGcmSiv.X86.derive_ct v L) (fun s E => WP.mono (VG.Proof.AesGcmSiv.X86.derive_ok v L E) fun _ I => I.env)
    (CT.seq (VG.Proof.AesGcmSiv.X86.expand_ct v L) (fun s E => WP.mono (VG.Proof.AesGcmSiv.X86.expand_ok v L E) fun _ X => X.env)
      (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun s h => h.ebp) (by taint_decide)))

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.PolyvalCT`. -/
section

/-!
# AES-GCM-SIV on x86: POLYVAL is constant time

Untrusted: everything here is checked by Lean. A chunk branches on the
number of bytes left, its loop copies the blocks from the pointer in `esi`,
and `vg_ghash` absorbs as many blocks as the number left says: all public
(`chunk_ct`); the chunks of a string, its last bytes and the lengths
(`absorb_ct`, `lens_ct`), and the tag input (`tagIn_ct`), from the public
arguments (`polyval_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq GcmImpl copyLoop_ct LoopPre copyLoop_ok covers_left covers_off
  length_bytesAt)

/-! ## A chunk -/

theorem chunkLen_ct {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {m : Nat} (hm : m < 2 ^ 32) {I : State → Prop}
    (hI : ∀ s, I s → VG.Proof.AesGcmSiv.X86.Env p s ∧ slotv s.mem p.W nO = BitVec.ofNat 32 m) : CT I chunkLen := by
  refine CT.seq (J := fun t₁ => t₁.gpr .ebp = p.W ∧ t₁.cf = some (decide (m / 16 < 64)))
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun s h => (hI s h).1.ebp) (by taint_decide)) (fun s h => ?_) ?_
  · obtain ⟨t₁, run₁, _, cf₁, bp₁, _⟩ := VG.Proof.AesGcmSiv.X86.chunkLen1_ok L (hI s h).1 hm (hI s h).2
    exact WP.of_runBlock ⟨t₁, run₁, bp₁, cf₁⟩
  have hmov : CT (fun t₁ => t₁.gpr .ebp = p.W ∧ t₁.cf = some (decide (m / 16 < 64))) (.block [.mov .ecx (imm 64)]) :=
    CT.taint [] (fun _ _ _ _ r hr => by simp at hr) (by taint_decide)
  refine CT.seq (J := fun s => s.gpr .ebp = p.W)
    (CT.ite (decide (m / 16 < 64)) (fun s h => VG.Proof.AesGcmSiv.X86.eval_b h.2) (fun _ => CT.nil) (fun _ => hmov))
    (fun s h => WP.ite (decide (m / 16 < 64)) (VG.Proof.AesGcmSiv.X86.eval_b h.2) (fun _ => WP.block_nil h.1)
      (fun _ => WP.of_runBlock ⟨_, by grun [], by gregs [h.1]⟩))
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h) (by taint_decide))

/-- What a chunk of the `m` bytes at `Q` starts from. -/
structure ChunkI (p : VG.Proof.AesGcmSiv.X86.Prm) (Q : BitVec 32) (m : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p s
  src : VG.Proof.AesGcmSiv.X86.Src p s Q (16 * (m / 16))
  esi : s.gpr .esi = Q
  n : slotv s.mem p.W nO = BitVec.ofNat 32 m

/-- Before `revLoop`. -/
structure RevI (p : VG.Proof.AesGcmSiv.X86.Prm) (Q : BitVec 32) (k : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p s
  src : VG.Proof.AesGcmSiv.X86.Src p s Q (16 * k)
  esi : s.gpr .esi = Q
  edx : s.gpr .edx = p.W + BitVec.ofNat 32 768
  ecx : s.gpr .ecx = BitVec.ofNat 32 k

theorem chunkPre_ct {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32) (h16 : 16 ≤ m) :
    CT (VG.Proof.AesGcmSiv.X86.ChunkI p Q m) chunkPre := by
  have hk1 : 1 ≤ min (m / 16) 64 := by omega
  refine CT.seq (J := fun s => VG.Proof.AesGcmSiv.X86.Env p s ∧ VG.Proof.AesGcmSiv.X86.Src p s Q (16 * min (m / 16) 64) ∧ s.gpr .esi = Q ∧
      s.gpr .ecx = BitVec.ofNat 32 (min (m / 16) 64))
    (VG.Proof.AesGcmSiv.X86.chunkLen_ct L hm fun s h => ⟨h.env, h.n⟩)
    (fun s h => WP.mono (VG.Proof.AesGcmSiv.X86.chunkLen_ok L h.env hm h.n) fun s₁ ⟨E₁, cx₁, _, _, si₁, rd₁, wr₁, _⟩ =>
      ⟨E₁, (h.src.take (by omega)).of_eq rd₁ wr₁, by rw [si₁, h.esi], cx₁⟩) ?_
  refine CT.seq (J := VG.Proof.AesGcmSiv.X86.RevI p Q (min (m / 16) 64))
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun s h => h.1.ebp) (by taint_decide))
    (fun s ⟨E, hQ, si, cx⟩ => WP.of_runBlock ⟨_, by grun [],
      ⟨E.keep (by gregs []) (by gregs []) (by gmems []) (by gmems []) (by gmems []), hQ.of_eq (by gmems []) (by gmems []),
        by gregs [si], by gregs [E.ebp], by gregs [cx]⟩⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W)
    (CT.taint [.esi, .edx, .ecx] (VG.Proof.AesGcmSiv.X86.pin3 fun s h => ⟨h.esi, h.edx, h.ecx⟩) (by taint_decide))
    (fun s h => WP.mono (VG.Proof.AesGcmSiv.X86.revLoop_ok L h.env hk1 (by omega) h.src h.esi h.edx h.ecx) fun _ ⟨_, _, _, bp, _⟩ => by
      rw [bp, h.env.ebp]) (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h) (by taint_decide))

theorem chunk_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32) (h16 : 16 ≤ m) :
    CT (VG.Proof.AesGcmSiv.X86.ChunkI p Q m) (chunk v.callees) := by
  have hk : min (m / 16) 64 ≤ 64 := by omega
  refine CT.seq (J := fun t₅ => ∃ t, VG.Proof.AesGcmSiv.X86.ChunkI p Q m t ∧ VG.Proof.AesGcmSiv.X86.ChunkPre p Q m (min (m / 16) 64) t t₅)
    (VG.Proof.AesGcmSiv.X86.chunkPre_ct L hm h16) (fun t h => WP.mono (VG.Proof.AesGcmSiv.X86.chunkPre_ok L h.env hm h16 h.src h.esi h.n) fun t₅ Pr => ⟨t, h, Pr⟩)
    (CT.seq (J := fun s => s.gpr .ebp = p.W)
      (VG.Proof.AesGcmSiv.X86.callGh_ct v L hk fun s ⟨_, _, Pr⟩ => ⟨Pr.env, Pr.eax, Pr.edx, Pr.ebx, Pr.edi⟩)
      (fun s ⟨_, _, Pr⟩ => WP.mono (VG.Proof.AesGcmSiv.X86.callGh_ok v L Pr.env hk Pr.eax Pr.edx Pr.ebx Pr.edi) fun _ P => P.env.ebp)
      (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h) (by taint_decide)))

/-! ## The chunks of a string -/

/-- The chunks of the `m` bytes at `Q`, from some `σ`, after `d` blocks. -/
def ChunksI (p : VG.Proof.AesGcmSiv.X86.Prm) (Q : BitVec 32) (m d : Nat) (s : State) : Prop :=
  ∃ σ, VG.Proof.AesGcmSiv.X86.CInv p σ Q m d s ∧ VG.Proof.AesGcmSiv.X86.Src p σ Q (16 * (m / 16))

/-- The number of chunks of `b` whole blocks. -/
abbrev nChunks (b : Nat) : Nat := (b + 63) / 64

theorem chunks_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32)
    (h16 : 16 ≤ m) : CT (VG.Proof.AesGcmSiv.X86.ChunksI p Q m 0) (.loop (chunk v.callees) .ne) := by
  have hN1 : 0 < VG.Proof.AesGcmSiv.X86.nChunks (m / 16) := by unfold VG.Proof.AesGcmSiv.X86.nChunks; omega
  have hN2 : 64 * (VG.Proof.AesGcmSiv.X86.nChunks (m / 16) - 1) < m / 16 := by unfold VG.Proof.AesGcmSiv.X86.nChunks; omega
  have hN3 : m / 16 ≤ 64 * VG.Proof.AesGcmSiv.X86.nChunks (m / 16) := by unfold VG.Proof.AesGcmSiv.X86.nChunks; omega
  refine (CT.loopN (fun k s => 0 < k ∧ k ≤ VG.Proof.AesGcmSiv.X86.nChunks (m / 16) ∧ VG.Proof.AesGcmSiv.X86.ChunksI p Q m (64 * (VG.Proof.AesGcmSiv.X86.nChunks (m / 16) - k)) s)
    (fun k => ?_) (fun k s ⟨hk0, hk, σ, I, hQ⟩ => ?_) (VG.Proof.AesGcmSiv.X86.nChunks (m / 16))).mono
    fun s h => ⟨by omega, Nat.le_refl _, by rw [Nat.sub_self, Nat.mul_zero]; exact h⟩
  · by_cases hkk : 0 < k ∧ k ≤ VG.Proof.AesGcmSiv.X86.nChunks (m / 16)
    · have hd : 64 * (VG.Proof.AesGcmSiv.X86.nChunks (m / 16) - k) < m / 16 := by omega
      exact (VG.Proof.AesGcmSiv.X86.chunk_ct v L (Q := Q + BitVec.ofNat 32 (16 * (64 * (VG.Proof.AesGcmSiv.X86.nChunks (m / 16) - k))))
        (m := m - 16 * (64 * (VG.Proof.AesGcmSiv.X86.nChunks (m / 16) - k))) (by omega) (by omega)).mono fun s ⟨_, _, σ, I, hQ⟩ =>
          ⟨I.abs.env, I.src hQ hd, I.esi, I.n⟩
    · exact CT.of_empty fun s ⟨hk0, hk, _⟩ => hkk ⟨hk0, hk⟩
  · have hd : 64 * (VG.Proof.AesGcmSiv.X86.nChunks (m / 16) - k) < m / 16 := by omega
    refine WP.mono (VG.Proof.AesGcmSiv.X86.chunk_ok v L I.abs.env (by omega) (by omega) (I.src hQ hd) I.esi I.n) fun s' C => ?_
    obtain ⟨I', z⟩ := I.step L hQ hd C
    refine ⟨hk0, by rw [VG.Proof.AesGcmSiv.X86.eval_ne z]; simp; omega, fun hk1 => ⟨by omega, by omega, σ, ?_, hQ⟩⟩
    have e : 64 * (VG.Proof.AesGcmSiv.X86.nChunks (m / 16) - k) + min (m / 16 - 64 * (VG.Proof.AesGcmSiv.X86.nChunks (m / 16) - k)) 64 =
        64 * (VG.Proof.AesGcmSiv.X86.nChunks (m / 16) - (k - 1)) := by omega
    rw [e] at I'
    exact I'

/-! ## The last bytes -/

/-- What the last `r` bytes at `P` start from. -/
structure TailI (p : VG.Proof.AesGcmSiv.X86.Prm) (P : BitVec 32) (r : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p s
  esi : s.gpr .esi = P
  n : slotv s.mem p.W nO = BitVec.ofNat 32 r
  r1 : 1 ≤ r
  r16 : r < 16
  rd : Covers [⟨w64 P, r⟩] (s.rd ++ s.wr)
  wrap : P.toNat + r ≤ 2 ^ 32
  w : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩

theorem absTailPre_ct {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {P : BitVec 32} {r : Nat} : CT (VG.Proof.AesGcmSiv.X86.TailI p P r) absTailPre := by
  have hw := L.ww
  refine CT.seq (J := fun t₁ => LoopPre t₁ P (p.W + BitVec.ofNat 32 224) r ∧ t₁.gpr .ebp = p.W)
    (CT.taint [.ebp, .esi] (VG.Proof.AesGcmSiv.X86.pin2 fun s h => ⟨h.env.ebp, h.esi⟩) (by taint_decide)) (fun t T => ?_) ?_
  · obtain ⟨t₁, run₁, hm₁, di₁, dx₁, cx₁, bp₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.absTail1_ok L T.env T.esi T.n
    have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by
      rw [hm₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
    have E₁ : VG.Proof.AesGcmSiv.X86.Env p t₁ := T.env.mut L bp₁ sp₁ rd₁ wr₁ (VG.Proof.AesGcmSiv.X86.frame_toMut f₁ fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
    have dB : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 (p.W + BitVec.ofNat 32 224), r⟩ := by
      rw [L.aW (by decide)]
      exact (T.w.sub_right (Lay.wSub (show 224 + 16 ≤ 2816 by decide))).sub_right
        (Region.sub_prefix (by have := T.r16; omega))
    have lp : LoopPre t₁ P (p.W + BitVec.ofNat 32 224) r := by
      refine ⟨di₁, dx₁, cx₁, T.r1, by have := T.r16; omega, T.wrap, ?_, by rw [rd₁, wr₁]; exact T.rd, ?_, dB⟩
      · rw [L.nW (by decide)]; have := T.r16; omega
      · rw [L.aW (by decide)]
        exact VG.Proof.AesGcmSiv.X86.covers_prefix (E₁.perm.wC (show 224 + 16 ≤ 2816 by decide)) (by have := T.r16; omega)
    exact WP.of_runBlock ⟨t₁, run₁, lp, bp₁⟩
  refine CT.seq (J := fun s => s.gpr .ebp = p.W)
    (copyLoop_ct (VG.Proof.AesGcmSiv.X86.pin3 fun s h => ⟨h.1.edi, h.1.edx, h.1.ecx⟩))
    (fun s h => WP.mono (copyLoop_ok s h.1) fun _ O => by
      rw [O.other _ (by decide) (by decide) (by decide) (by decide), h.2])
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h) (by taint_decide))

theorem absTail_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {P : BitVec 32} {r : Nat} :
    CT (VG.Proof.AesGcmSiv.X86.TailI p P r) (absTail v.callees) :=
  CT.seq (J := fun t₃ => ∃ t, VG.Proof.AesGcmSiv.X86.TailI p P r t ∧ VG.Proof.AesGcmSiv.X86.TailPre p (w64 P) r t t₃) (VG.Proof.AesGcmSiv.X86.absTailPre_ct L)
    (fun t T => WP.mono (VG.Proof.AesGcmSiv.X86.absTailPre_ok L T.env T.r1 T.r16 T.rd T.wrap T.w T.esi T.n) fun t₃ h => ⟨t, T, h⟩)
    ((VG.Proof.AesGcmSiv.X86.chunk_ct v L (Q := p.W + BitVec.ofNat 32 224) (m := 16) (by decide) (by decide)).mono
      fun s ⟨_, _, h⟩ => ⟨h.env, VG.Proof.AesGcmSiv.X86.srcB L h.env.perm, h.esi, h.n⟩)

/-! ## Absorbing a string -/

/-- What absorbing the `m` bytes at `Q` starts from. -/
structure AbsI (p : VG.Proof.AesGcmSiv.X86.Prm) (Q : BitVec 32) (m : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p s
  src : VG.Proof.AesGcmSiv.X86.Src p s Q m
  w : (⟨w64 Q, m⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩
  esi : s.gpr .esi = Q
  n : slotv s.mem p.W nO = BitVec.ofNat 32 m

theorem AbsI.keep {p : VG.Proof.AesGcmSiv.X86.Prm} {Q : BitVec 32} {m : Nat} {s s' : State} (h : VG.Proof.AesGcmSiv.X86.AbsI p Q m s) (E : VG.Proof.AesGcmSiv.X86.Env p s')
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hm : s'.mem = s.mem) (hsi : s'.gpr .esi = s.gpr .esi) :
    VG.Proof.AesGcmSiv.X86.AbsI p Q m s' :=
  ⟨E, h.src.of_eq hrd hwr, h.w, by rw [hsi, h.esi], by rw [slotv_eq, hm]; exact h.n⟩

theorem absorb_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32) :
    CT (VG.Proof.AesGcmSiv.X86.AbsI p Q m) (absorb v.callees) := by
  refine CT.seq (J := fun s => VG.Proof.AesGcmSiv.X86.AbsI p Q m s ∧ s.zf = some (decide (m / 16 = 0)))
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun s h => h.env.ebp) (by taint_decide)) (fun t A => ?_) ?_
  · obtain ⟨t₁, run₁, z₁, E₁, si₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.wholeLeft_ok L A.env hm A.n
    exact WP.of_runBlock ⟨t₁, run₁, A.keep E₁ rd₁ wr₁ m₁ si₁, z₁⟩
  refine CT.seq (J := fun s => ∃ t, VG.Proof.AesGcmSiv.X86.AbsI p Q m t ∧ VG.Proof.AesGcmSiv.X86.Env p s ∧ s.rd = t.rd ∧ s.wr = t.wr ∧
      s.gpr .esi = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ slotv s.mem p.W nO = BitVec.ofNat 32 (m % 16))
    (CT.ite (decide (m / 16 = 0)) (fun s h => VG.Proof.AesGcmSiv.X86.eval_e h.2) (fun _ => CT.nil) fun hf => ?_)
    (fun t ⟨A, z⟩ => WP.mono (VG.Proof.AesGcmSiv.X86.absMid_ok v L A.env hm A.src A.esi A.n z) fun s ⟨P, si, n⟩ =>
      ⟨t, A, P.env, P.rd, P.wr, si, n⟩) ?_
  · have h0 : m / 16 ≠ 0 := of_decide_eq_false hf
    exact (VG.Proof.AesGcmSiv.X86.chunks_ct v L (Q := Q) hm (by omega)).mono fun s ⟨A, _⟩ =>
      ⟨s, CInv.zero A.env A.esi A.n, A.src.take (by omega)⟩
  refine CT.seq (J := fun s => (∃ t, VG.Proof.AesGcmSiv.X86.AbsI p Q m t ∧ VG.Proof.AesGcmSiv.X86.Env p s ∧ s.rd = t.rd ∧ s.wr = t.wr ∧
      s.gpr .esi = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ slotv s.mem p.W nO = BitVec.ofNat 32 (m % 16)) ∧
      s.zf = some (decide (m % 16 = 0)))
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun s ⟨_, _, E, _⟩ => E.ebp) (by taint_decide)) (fun s ⟨t, A, E, rd, wr, si, n⟩ => ?_) ?_
  · obtain ⟨s₁, run₁, z₁, E₁, si₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.anyLeft_ok L E (by omega) n
    exact WP.of_runBlock ⟨s₁, run₁, ⟨t, A, E₁, by rw [rd₁, rd], by rw [wr₁, wr], by rw [si₁, si],
      by rw [slotv_eq, m₁]; exact n⟩, z₁⟩
  refine CT.ite (decide (m % 16 = 0)) (fun s h => VG.Proof.AesGcmSiv.X86.eval_e h.2) (fun _ => CT.nil) fun hf => ?_
  have h0 : m % 16 ≠ 0 := of_decide_eq_false hf
  refine (VG.Proof.AesGcmSiv.X86.absTail_ct v L (P := Q + BitVec.ofNat 32 (16 * (m / 16))) (r := m % 16)).mono
    fun s ⟨⟨t, A, E, rd, wr, si, n⟩, _⟩ => ?_
  have hs := A.src.slice (a := 16 * (m / 16)) (k := m % 16) (by omega) (by omega)
  have ea := A.src.addr (j := 16 * (m / 16)) (by omega)
  exact ⟨E, si, n, by omega, by omega, by rw [rd, wr]; exact hs.rd, hs.wrap,
    by rw [ea]; exact A.w.sub_left (Offset.sub_base _ (by omega))⟩

/-! ## The lengths, the tag input, and `polyval` -/

theorem lens_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) : CT (VG.Proof.AesGcmSiv.X86.Env p) (lens v.callees) := by
  refine CT.seq (J := VG.Proof.AesGcmSiv.X86.ChunkI p (p.W + BitVec.ofNat 32 224) 16)
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun s h => h.ebp) (by taint_decide)) (fun t E => ?_) (VG.Proof.AesGcmSiv.X86.chunk_ct v L (by decide) (by decide))
  obtain ⟨t₁, run₁, hm₁, si₁, bp₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.lensBlock_ok L E
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem t₁.mem := by
    rw [hm₁, VG.Proof.AesGcmSiv.X86.lensMem]
    exact ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
  have E₁ : VG.Proof.AesGcmSiv.X86.Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (VG.Proof.AesGcmSiv.X86.frame_toMut f₁ fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inr (.inl ⟨by decide, by decide⟩)))
  exact WP.of_runBlock ⟨t₁, run₁, E₁, VG.Proof.AesGcmSiv.X86.srcB L E₁.perm, si₁, by rw [slotv_eq, hm₁, VG.Proof.AesGcmSiv.X86.lensMem, Mem.readW_writeW_self32]⟩

theorem tagIn_ct {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) : CT (VG.Proof.AesGcmSiv.X86.Env p) (.block tagIn) :=
  VG.Proof.AesGcmSiv.X86.ldPin (r := .ecx) (o := nonceO) (x := p.N) (W := p.W)
    (fun s h => ⟨h.ebp, h.slots.nonce, h.perm.wR (by decide)⟩) (by have := L.ww; unfold nonceO; omega)
    (by decide) (by taint_decide) (by taint_decide)

theorem polyval_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) : CT (VG.Proof.AesGcmSiv.X86.Env p) (polyval v.callees) := by
  refine CT.seq (J := VG.Proof.AesGcmSiv.X86.AbsI p p.A p.al) (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_)
    (CT.seq (J := VG.Proof.AesGcmSiv.X86.Env p) (VG.Proof.AesGcmSiv.X86.absorb_ct v L L.al32)
      (fun t A => WP.mono (VG.Proof.AesGcmSiv.X86.absorb_ok v L A.env L.al32 A.src A.w A.esi A.n) fun _ P => P.env)
      (CT.seq (J := VG.Proof.AesGcmSiv.X86.AbsI p p.D p.n) (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_)
        (CT.seq (J := VG.Proof.AesGcmSiv.X86.Env p) (VG.Proof.AesGcmSiv.X86.absorb_ct v L L.n32)
          (fun t A => WP.mono (VG.Proof.AesGcmSiv.X86.absorb_ok v L A.env L.n32 A.src A.w A.esi A.n) fun _ P => P.env)
          (CT.seq (J := VG.Proof.AesGcmSiv.X86.Env p) (VG.Proof.AesGcmSiv.X86.lens_ct v L) (fun t E => WP.mono (VG.Proof.AesGcmSiv.X86.lens_ok v L E) fun _ P => P.env) (VG.Proof.AesGcmSiv.X86.tagIn_ct L)))))
  · obtain ⟨t₁, run₁, E₁, si₁, n₁, _, _, _⟩ := VG.Proof.AesGcmSiv.X86.onStr_ok L E (s := aadO) (l := alenO) (by decide) (by decide)
      E.slots.aad E.slots.alen
    exact WP.of_runBlock ⟨t₁, run₁, E₁, VG.Proof.AesGcmSiv.X86.srcBuf E₁.perm.aad L.aw L.a_w L.ba, L.a_w, si₁, n₁⟩
  · obtain ⟨t₁, run₁, E₁, si₁, n₁, _, _, _⟩ := VG.Proof.AesGcmSiv.X86.onStr_ok L E (s := dataO) (l := lenO) (by decide) (by decide)
      E.slots.data E.slots.len
    exact WP.of_runBlock ⟨t₁, run₁, E₁, VG.Proof.AesGcmSiv.X86.srcBuf (covers_left E₁.perm.d) L.dw L.d_w L.bd, L.d_w, si₁, n₁⟩

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.CryptCT`. -/
section

/-!
# AES-GCM-SIV on x86: the tag and counter mode are constant time

Untrusted: everything here is checked by Lean. `tag o` calls `vg_aes_ctr32`
on public pointers (`tag_ct`); counter mode encrypts block after block of
the data, through the pointer in `esi`, as many as its public length says
(`crypt_ct`), and XORs the last bytes in a loop from public pointers and
counts (`cryptTail_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq GcmImpl xorLoop_ct XorPre xorLoop_ok covers_off covers_left)

theorem tag_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {o : Nat} (ho : VG.Proof.AesGcmSiv.X86.TagO o) : CT (VG.Proof.AesGcmSiv.X86.Env p) (VG.Impl.AesGcmSiv.X86.tag v.callees o) := by
  have hc : CT (VG.Proof.AesGcmSiv.X86.Env p) (.block (copy16 cbO ccO ++ zero4 o ++ ctrArgs o)) := by
    rcases ho with rfl | rfl | rfl <;> exact CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h.ebp) (by taint_decide)
  refine CT.seq (J := fun t₁ => ∃ t, VG.Proof.AesGcmSiv.X86.TagCall p o t t₁) hc
    (fun t E => by obtain ⟨t₁, run₁, C⟩ := VG.Proof.AesGcmSiv.X86.tagArgs_ok L E ho; exact WP.of_runBlock ⟨t₁, run₁, t, C⟩)
    (VG.Proof.AesGcmSiv.X86.callCtr_ct v L fun t₁ ⟨_, C⟩ => ⟨C.env, VG.Proof.AesGcmSiv.X86.keyS L C.env.perm, C.dst, C.eax, C.ecx, C.edx, C.ebx, C.edi⟩)

/-! ## A block -/

/-- What a block's call starts from. -/
structure BlkCall (p : VG.Proof.AesGcmSiv.X86.Prm) (j : Nat) (t₁ : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86.Env p t₁
  dst : VG.Proof.AesGcmSiv.X86.Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.D + BitVec.ofNat 32 (16 * j)) (16 * 1)
  eax : t₁.gpr .eax = p.W + BitVec.ofNat 32 512
  ecx : t₁.gpr .ecx = BitVec.ofNat 32 p.R
  edx : t₁.gpr .edx = p.W + BitVec.ofNat 32 112
  ebx : t₁.gpr .ebx = p.D + BitVec.ofNat 32 (16 * j)
  edi : t₁.gpr .edi = BitVec.ofNat 32 1
  esi : t₁.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)

theorem blkCall_of {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.X86.Env p t) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)) :
    ∃ t₁, runBlock isa blockArgs t = some t₁ ∧ VG.Proof.AesGcmSiv.X86.BlkCall p j t₁ := by
  have hw := L.ww
  have hn' := L.n32
  have hdw := L.dw
  obtain ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, bp₁, sp₁, si₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86.blkArgs_ok L E hsi
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact VG.Proof.AesGcmSiv.X86.copyMem_frame _ _
  have E₁ : VG.Proof.AesGcmSiv.X86.Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (VG.Proof.AesGcmSiv.X86.frame_toMut f₁ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact VG.Proof.AesGcmSiv.X86.inMut_w p (.inl (by decide)))
  have eQ : w64 (p.D + BitVec.ofNat 32 (16 * j)) = w64 p.D + BitVec.ofNat 64 (16 * j) := L.dA (by omega)
  have dQ : (⟨w64 p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  have hD : VG.Proof.AesGcmSiv.X86.Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.D + BitVec.ofNat 32 (16 * j)) (16 * 1) := by
    refine ⟨?_, by rw [L.dN (by omega)]; omega, ?_, ?_, ?_, ?_⟩ <;> rw [eQ]
    · exact covers_off E₁.perm.d (by omega) (by omega)
    · rw [L.aW (by decide)]; exact (dQ.sub_right (Lay.wSub (show 512 + 240 ≤ 2816 by decide))).symm
    · exact dQ.sub_right (Lay.wSub (by decide))
    · exact dQ.sub_right (Lay.wSub (by decide))
    · exact L.bd.sub_right (Offset.sub_base _ (by omega))
  exact ⟨t₁, run₁, E₁, hD, eax, ecx, edx, ebx, edi, by rw [si₁, hsi]⟩

theorem cryptBlock_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {j : Nat} (hj : 16 * (j + 1) ≤ p.n) :
    CT (fun s => VG.Proof.AesGcmSiv.X86.Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)) (cryptBlock v.callees) := by
  have hdw := L.dw
  refine CT.seq (J := VG.Proof.AesGcmSiv.X86.BlkCall p j)
    (CT.taint [.ebp, .esi] (VG.Proof.AesGcmSiv.X86.pin2 fun _ h => ⟨h.1.ebp, h.2⟩) (by taint_decide))
    (fun t ⟨E, si⟩ => by obtain ⟨t₁, run₁, C⟩ := VG.Proof.AesGcmSiv.X86.blkCall_of L E hj si; exact WP.of_runBlock ⟨t₁, run₁, C⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * j))
    (VG.Proof.AesGcmSiv.X86.callCtr_ct v L fun t₁ C => ⟨C.env, VG.Proof.AesGcmSiv.X86.keyS L C.env.perm, C.dst, C.eax, C.ecx, C.edx, C.ebx, C.edi⟩)
    (fun t₁ C => WP.mono (VG.Proof.AesGcmSiv.X86.callCtr_ok v L C.env (VG.Proof.AesGcmSiv.X86.keyS L C.env.perm) C.dst
      (by rw [L.dA (by omega)]; exact ⟨⟨w64 p.D, p.n⟩, by simp, Offset.sub_base _ (by omega)⟩) C.eax C.ecx C.edx
      C.ebx C.edi) fun s P => ⟨P.env.ebp, by rw [P.saved _ (by decide), C.esi]⟩)
    (CT.taint [.ebp, .esi] (VG.Proof.AesGcmSiv.X86.pin2 fun _ h => h) (by taint_decide))

/-- The whole blocks of the data, from `t`. -/
def BlocksI (p : VG.Proof.AesGcmSiv.X86.Prm) (j : Nat) (s : State) : Prop :=
  ∃ t ciph icb x, x.length = p.n ∧ Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph ∧
    VG.Proof.AesGcmSiv.X86.BlocksPost p ciph icb x j t s

theorem blocks_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) (hb1 : 1 ≤ p.n / 16) :
    CT (VG.Proof.AesGcmSiv.X86.BlocksI p 0) (.loop (cryptBlock v.callees) .ne) := by
  refine (CT.loopN (fun k s => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ VG.Proof.AesGcmSiv.X86.BlocksI p j s) (fun k => ?_)
    (fun k s ⟨j, hk, hj, t, ciph, icb, x, hxl, hc, P⟩ => ?_) (p.n / 16)).mono
    fun s h => ⟨0, by omega, by omega, h⟩
  · by_cases hkk : 0 < k ∧ k ≤ p.n / 16
    · exact (VG.Proof.AesGcmSiv.X86.cryptBlock_ct v L (j := p.n / 16 - k) (by omega)).mono fun s ⟨j, hk', hj, _, _, _, _, _, _, P⟩ => by
        rw [show p.n / 16 - k = j by omega]; exact ⟨P.env, P.esi⟩
    · exact CT.of_empty fun s ⟨j, hk', hj, _⟩ => hkk ⟨by omega, by omega⟩
  · have hc' : Spec.GcmSiv.ctxCiph s.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph := by
      rw [VG.Proof.AesGcmSiv.X86.ciph_cryR L P.frame, hc]
    refine WP.mono (VG.Proof.AesGcmSiv.X86.cryptBlock_ok v L P.env hxl (j := j) (by omega) P.esi P.n P.ctr P.data hc') fun t'' Q => ?_
    refine ⟨by omega, by rw [VG.Proof.AesGcmSiv.X86.eval_ne Q.z]; simp; omega, fun hk1 => ⟨j + 1, by omega, by omega, t, ciph, icb, x, hxl, hc,
      ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.esi, Q.n, Q.ctr, Q.data, P.frame.trans Q.frame⟩⟩⟩

/-! ## The last bytes -/

theorem cryptTail_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) {b r : Nat} (hn : p.n = 16 * b + r) (hr1 : 1 ≤ r)
    (hr : r < 16) :
    CT (fun s => VG.Proof.AesGcmSiv.X86.Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * b) ∧ slotv s.mem p.W nO = BitVec.ofNat 32 r)
      (cryptTail v.callees) := by
  have hn' := L.n32
  have hdw := L.dw
  have hw := L.ww
  refine CT.seq (J := fun s => VG.Proof.AesGcmSiv.X86.Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * b) ∧
      slotv s.mem p.W nO = BitVec.ofNat 32 r) ((VG.Proof.AesGcmSiv.X86.tag_ct v L (o := 224) (by decide)).mono fun _ h => h.1)
    (fun t ⟨E, si, n⟩ => WP.mono (VG.Proof.AesGcmSiv.X86.tag_ok v L E (o := 224) (by decide)) fun t₂ T => ⟨T.env, by rw [T.esi, si], ?_⟩) ?_
  · rw [← n]
    exact T.frame.readW (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  refine CT.seq (J := fun s => XorPre s (p.W + BitVec.ofNat 32 224) (p.D + BitVec.ofNat 32 (16 * b)) r)
    (CT.taint [.ebp, .esi] (VG.Proof.AesGcmSiv.X86.pin2 fun _ h => ⟨h.1.ebp, h.2.1⟩) (by taint_decide)) (fun t₂ ⟨E, si, n⟩ => ?_)
    (xorLoop_ct (VG.Proof.AesGcmSiv.X86.pin3 fun _ h => ⟨h.edi, h.edx, h.ecx⟩))
  simp only [slotv_eq, nO] at n
  obtain ⟨t₃, run₃, dx₃, di₃, cx₃, m₃, rd₃, wr₃⟩ : ∃ t₃ : State, runBlock isa
      [.mov .edx (.reg .ebp), .alu .add .edx (imm bO), .mov .edi (.reg .esi), .mov .ecx (slot nO)] t₂ = some t₃ ∧
      t₃.gpr .edx = p.W + BitVec.ofNat 32 224 ∧ t₃.gpr .edi = p.D + BitVec.ofNat 32 (16 * b) ∧
      t₃.gpr .ecx = BitVec.ofNat 32 r ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, n], by gregs [E.ebp], by gregs [si], by gregs [n], by gmems [], by gmems [],
      by gmems []⟩
  have eD := L.dA (j := 16 * b) (by omega)
  have dQ : (⟨w64 p.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  refine WP.of_runBlock ⟨t₃, run₃, dx₃, di₃, cx₃, by omega, by omega, by rw [L.nW (by decide)]; omega,
    by rw [L.dN (by omega)]; omega, ?_, ?_, ?_⟩
  · rw [rd₃, wr₃, L.aW (by decide)]
    exact VG.Proof.AesGcmSiv.X86.covers_prefix (E.perm.wCR (show 224 + 16 ≤ 2816 by decide)) (by omega)
  · rw [wr₃, eD]; exact covers_off E.perm.d (by omega) (by omega)
  · rw [eD, L.aW (by decide)]
    exact ((dQ.sub_right (Lay.wSub (show 224 + 16 ≤ 2816 by decide))).sub_right (Region.sub_prefix (by omega))).symm

/-! ## `crypt` -/

theorem crypt_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) : CT (VG.Proof.AesGcmSiv.X86.Env p) (crypt v.callees) := by
  have hn := L.n32
  refine CT.seq (J := fun s => ∃ t, VG.Proof.AesGcmSiv.X86.CStart p t s) (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h.ebp) (by taint_decide))
    (fun t E => by obtain ⟨t₁, run₁, S⟩ := VG.Proof.AesGcmSiv.X86.cryptStart_ok L E; exact WP.of_runBlock ⟨t₁, run₁, t, S⟩) ?_
  refine CT.seq (J := fun s => VG.Proof.AesGcmSiv.X86.Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧
      slotv s.mem p.W nO = BitVec.ofNat 32 (p.n % 16))
    (CT.ite (decide (p.n / 16 = 0)) (fun s ⟨_, S⟩ => VG.Proof.AesGcmSiv.X86.eval_e S.z) (fun _ => CT.nil) fun hf => ?_)
    (fun t₁ ⟨t, S⟩ => ?_) ?_
  · have h0 : p.n / 16 ≠ 0 := of_decide_eq_false hf
    refine (VG.Proof.AesGcmSiv.X86.blocks_ct v L (by omega)).mono fun s ⟨t, S⟩ => ⟨s, _, _, bytesAt s.mem (w64 p.D) p.n,
      Proof.Cmac.bytesAt_length _ _ _, rfl, ⟨S.env, rfl, rfl, by rw [S.esi, Nat.mul_zero, BitVec.add_zero],
        by rw [S.n, Nat.mul_zero, Nat.sub_zero], S.ctr, by rw [Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  · have hxl : (bytesAt t₁.mem (w64 p.D) p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
    refine WP.mono (Q := VG.Proof.AesGcmSiv.X86.BlocksPost p (Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) (bytesAt t₁.mem (w64 p.D) p.n) (p.n / 16) t₁)
      ?_ fun t₂ B => ⟨B.env, B.esi, by rw [B.n]; congr 1; omega⟩
    refine WP.ite (decide (p.n / 16 = 0)) (VG.Proof.AesGcmSiv.X86.eval_e S.z) (fun ht => ?_) (fun hf => ?_)
    · have h0 : p.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨S.env, rfl, rfl, by rw [S.esi, Nat.mul_zero, BitVec.add_zero], by rw [S.n, Nat.mul_zero, Nat.sub_zero],
        S.ctr, by rw [Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩
    · have h0 : p.n / 16 ≠ 0 := by simpa using hf
      exact VG.Proof.AesGcmSiv.X86.blocks_ok v L S.env hxl (by omega) S.esi S.n S.ctr rfl rfl
  refine CT.seq (J := fun s => (VG.Proof.AesGcmSiv.X86.Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧
      slotv s.mem p.W nO = BitVec.ofNat 32 (p.n % 16)) ∧ s.zf = some (decide (p.n % 16 = 0)))
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h.1.ebp) (by taint_decide)) (fun s ⟨E, si, n⟩ => ?_) ?_
  · obtain ⟨s₁, run₁, z₁, E₁, si₁, m₁, -, -⟩ := VG.Proof.AesGcmSiv.X86.anyLeft_ok L E (by omega) n
    exact WP.of_runBlock ⟨s₁, run₁, ⟨E₁, by rw [si₁, si], by rw [slotv_eq, m₁]; exact n⟩, z₁⟩
  refine CT.ite (decide (p.n % 16 = 0)) (fun s h => VG.Proof.AesGcmSiv.X86.eval_e h.2) (fun _ => CT.nil) fun hf => ?_
  have h0 : p.n % 16 ≠ 0 := of_decide_eq_false hf
  exact (VG.Proof.AesGcmSiv.X86.cryptTail_ct v L (b := p.n / 16) (r := p.n % 16) (by omega) (by omega) (by omega)).mono
    fun s ⟨h, _⟩ => h

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.FnCT`. -/
section

/-!
# AES-GCM-SIV on x86: `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` are constant time

Untrusted: everything here is checked by Lean. The arguments and `esp` are
public, and so is everything the pieces' preconditions say (`prmOf`). The
entry loads `work` from the stack, at `esp`, and saves our caller's registers
and the arguments through it (`entry_ct`); `cmp` computes the result without
a branch, and `mask` loops over the data's length alone (`mask_ct`); the
other pieces are constant time from `Env` (`keys_ct`, `polyval_ct`,
`tag_ct`, `crypt_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot argOp)
open VG.Proof.AesGcm.X86 (CT w64 GcmImpl argA argA_contains)

/-- The public arguments are a function of what `onePub` says is public. -/
theorem prmOf_pub {s₁ s₂ : State} (h : VG.Proof.AesGcmSiv.X86.onePub s₁ s₂) : VG.Proof.AesGcmSiv.X86.prmOf s₁ = VG.Proof.AesGcmSiv.X86.prmOf s₂ := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [VG.Proof.AesGcmSiv.X86.prmOf, h₁, h₂ 0 (by decide), h₂ 1 (by decide), h₂ 2 (by decide), h₂ 3 (by decide), h₂ 4 (by decide),
    h₂ 5 (by decide), h₂ 6 (by decide), h₂ 7 (by decide), h₂ 8 (by decide)]

theorem entryLoad_ok {p : VG.Proof.AesGcmSiv.X86.Prm} {s : State} (h : VG.Proof.AesGcmSiv.X86.onePre s) (hp : VG.Proof.AesGcmSiv.X86.prmOf s = p) :
    ∃ s', runBlock isa [.mov .eax (argOp 8)] s = some s' ∧ s'.gpr .eax = p.W ∧ s'.gpr .esp = p.SP := by
  have Ao := VG.Proof.AesGcmSiv.X86.argsOk_of h
  have hw : p.W = arg s 8 := hp ▸ rfl
  have hsp : p.SP = s.gpr .esp := hp ▸ rfl
  have rA := Ao.rA
  have fa := Ao.fa
  generalize hSP : s.gpr .esp = SP at rA fa hsp
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 8) 4 :=
    rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine ⟨_, by grun [hSP, i₀], ?_, ?_⟩
  · rw [gpr_setReg_self, hw, ← hSP]; rfl
  · rw [gpr_setReg_of_ne _ _ (by decide), hSP, hsp]

theorem entrySave_ct {p : VG.Proof.AesGcmSiv.X86.Prm} :
    CT (fun s => s.gpr .eax = p.W ∧ s.gpr .esp = p.SP)
      (.block (Impl.AesGcm.X86.saveAt ++ entryPs.flatMap (fun q => Impl.AesGcm.X86.keep q.1 q.2))) :=
  CT.taint [.eax, .esp] (VG.Proof.AesGcmSiv.X86.pin2 fun _ h => h) (by taint_decide)

theorem entry_ct {p : VG.Proof.AesGcmSiv.X86.Prm} : CT (fun s => VG.Proof.AesGcmSiv.X86.onePre s ∧ VG.Proof.AesGcmSiv.X86.prmOf s = p) sivEntry := by
  have e : ∀ s, VG.Proof.AesGcmSiv.X86.prmOf s = p → s.gpr .esp = p.SP := fun s h => h ▸ rfl
  rw [VG.Proof.AesGcmSiv.X86.sivEntry_eq]
  refine CT.seq (J := fun s => s.gpr .eax = p.W ∧ s.gpr .esp = p.SP)
    (CT.taint [.esp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e _ h₁.2, e _ h₂.2]) (by taint_decide))
    (fun s ⟨h, hp⟩ => let ⟨s', run, ax, sp⟩ := VG.Proof.AesGcmSiv.X86.entryLoad_ok h hp; WP.of_runBlock ⟨s', run, ax, sp⟩) VG.Proof.AesGcmSiv.X86.entrySave_ct

/-! ## The mask -/

theorem mask_ct {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) : CT (VG.Proof.AesGcmSiv.X86.Env p) mask := by
  refine CT.block_seq (F := fun _ s₁ => s₁.zf = some (decide (p.n = 0)) ∧ VG.Proof.AesGcmSiv.X86.Env p s₁ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 p.n) [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun s h => h.ebp) (by taint_decide)
    (fun s E => let ⟨s₁, run, _, _, cx, zf, _, E₁, _⟩ := VG.Proof.AesGcmSiv.X86.maskTest_ok L E; ⟨s₁, run, zf, E₁, cx⟩) ?_
  refine CT.ite (decide (p.n = 0)) (fun _ ⟨_, _, zf, _⟩ => VG.Proof.AesGcmSiv.X86.eval_e zf) (fun _ => CT.nil) fun _ => ?_
  refine CT.block_seq (F := fun _ s₂ => s₂.gpr .edi = p.D ∧ s₂.gpr .ecx = BitVec.ofNat 32 p.n) [.ebp]
    (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ ⟨_, _, _, E, _⟩ => E.ebp) (by taint_decide)
    (fun s₁ ⟨_, _, _, E₁, cx⟩ => let ⟨s₂, run, _, di, g, _⟩ := VG.Proof.AesGcmSiv.X86.maskArgs_ok L E₁;
      ⟨s₂, run, di, by rw [g _ (by decide), cx]⟩) ?_
  exact CT.taint [.edi, .ecx] (VG.Proof.AesGcmSiv.X86.pin2 fun _ ⟨_, _, di, cx⟩ => ⟨di, cx⟩) (by taint_decide)

/-! ## `seal` -/

theorem seal_top_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) :
    CT (fun s => VG.Proof.AesGcmSiv.X86.sealPre s ∧ VG.Proof.AesGcmSiv.X86.prmOf s = p) («seal» v.callees) := by
  have tw : ∀ s, VG.Proof.AesGcmSiv.X86.sealPre s → VG.Proof.AesGcmSiv.X86.prmOf s = p → Covers [⟨w64 p.T, 16⟩] s.wr := fun s h hp => by
    subst hp; exact VG.Proof.AesGcmSiv.X86.covers_of_mem (by rw [h.2.1]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  refine CT.seq (J := fun s₁ => ∃ s, (VG.Proof.AesGcmSiv.X86.sealPre s ∧ VG.Proof.AesGcmSiv.X86.prmOf s = p) ∧ VG.Proof.AesGcmSiv.X86.Entered s p s₁)
    (entry_ct.mono fun s h => ⟨VG.Proof.AesGcmSiv.X86.onePre_seal h.1, h.2⟩)
    (fun s ⟨h, hp⟩ => WP.mono (VG.Proof.AesGcmSiv.X86.entry_ok (VG.Proof.AesGcmSiv.X86.onePre_seal h)) fun s₁ En => ⟨s, ⟨h, hp⟩, hp ▸ En⟩) ?_
  refine CT.seq (J := fun s => ∃ σ, VG.Proof.AesGcmSiv.X86.KeysPost p σ s ∧ Covers [⟨w64 p.T, 16⟩] σ.wr)
    ((VG.Proof.AesGcmSiv.X86.keys_ct v L).mono fun _ ⟨_, _, En⟩ => En.env)
    (fun _ ⟨s, ⟨h, hp⟩, En⟩ => WP.mono (VG.Proof.AesGcmSiv.X86.keys_ok v L En.env) fun _ Ky => ⟨_, Ky, by rw [En.wr]; exact tw s h hp⟩) ?_
  refine CT.seq (J := fun s => VG.Proof.AesGcmSiv.X86.Env p s ∧ Covers [⟨w64 p.T, 16⟩] s.wr) ((VG.Proof.AesGcmSiv.X86.polyval_ct v L).mono fun _ ⟨_, Ky, _⟩ => Ky.env)
    (fun _ ⟨_, Ky, t⟩ => WP.mono (VG.Proof.AesGcmSiv.X86.polyval_ok v L Ky.env Ky.hkey Ky.acc) fun _ Po =>
      ⟨Po.env, by rw [Po.wr, Ky.wr]; exact t⟩) ?_
  refine CT.seq (J := fun s => VG.Proof.AesGcmSiv.X86.Env p s ∧ Covers [⟨w64 p.T, 16⟩] s.wr)
    ((VG.Proof.AesGcmSiv.X86.tag_ct v L (o := 0) (by decide)).mono fun _ h => h.1)
    (fun _ ⟨E, t⟩ => WP.mono (VG.Proof.AesGcmSiv.X86.tag_ok v L E (o := 0) (by decide)) fun _ Tg => ⟨Tg.env, by rw [Tg.wr]; exact t⟩) ?_
  refine CT.seq (J := fun s => VG.Proof.AesGcmSiv.X86.Env p s ∧ Covers [⟨w64 p.T, 16⟩] s.wr) ((VG.Proof.AesGcmSiv.X86.crypt_ct v L).mono fun _ h => h.1)
    (fun _ ⟨E, t⟩ => WP.mono (VG.Proof.AesGcmSiv.X86.crypt_ok v L E) fun _ Cr => ⟨Cr.env, by rw [Cr.wr]; exact t⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W) ((VG.Proof.AesGcmSiv.X86.tagOut_ct L).mono fun _ h => h.1)
    (fun _ ⟨E, t⟩ => WP.mono (VG.Proof.AesGcmSiv.X86.tagOut_ok L E t) fun _ ⟨_, _, bp, _⟩ => bp) ?_
  exact CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h) (by taint_decide)

theorem seal_ct (v : GcmImpl) : ConstantTime isa sealX86.pre sealX86.pub («seal» v.callees) :=
  CT.constantTime VG.Proof.AesGcmSiv.X86.prmOf (fun _ _ _ _ h => VG.Proof.AesGcmSiv.X86.prmOf_pub h) fun p => by
    by_cases hex : ∃ s, VG.Proof.AesGcmSiv.X86.sealPre s ∧ VG.Proof.AesGcmSiv.X86.prmOf s = p
    · obtain ⟨z, hz, rfl⟩ := hex
      exact VG.Proof.AesGcmSiv.X86.seal_top_ct v (VG.Proof.AesGcmSiv.X86.lay_of (VG.Proof.AesGcmSiv.X86.onePre_seal hz))
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

/-! ## `open` -/

theorem open_top_ct (v : GcmImpl) {p : VG.Proof.AesGcmSiv.X86.Prm} (L : VG.Proof.AesGcmSiv.X86.Lay p) :
    CT (fun s => VG.Proof.AesGcmSiv.X86.openPre s ∧ VG.Proof.AesGcmSiv.X86.prmOf s = p) («open» v.callees) := by
  refine CT.seq (J := fun s₁ => ∃ s, (VG.Proof.AesGcmSiv.X86.openPre s ∧ VG.Proof.AesGcmSiv.X86.prmOf s = p) ∧ VG.Proof.AesGcmSiv.X86.Entered s p s₁)
    (entry_ct.mono fun s h => ⟨VG.Proof.AesGcmSiv.X86.onePre_open h.1, h.2⟩)
    (fun s ⟨h, hp⟩ => WP.mono (VG.Proof.AesGcmSiv.X86.entry_ok (VG.Proof.AesGcmSiv.X86.onePre_open h)) fun s₁ En => ⟨s, ⟨h, hp⟩, hp ▸ En⟩) ?_
  refine CT.seq (J := VG.Proof.AesGcmSiv.X86.Env p) ((VG.Proof.AesGcmSiv.X86.recvTag_ct L).mono fun _ ⟨_, _, En⟩ => En.env)
    (fun _ ⟨_, _, En⟩ => WP.mono (VG.Proof.AesGcmSiv.X86.recvTag_ok L En.env) fun _ h => h.1) ?_
  refine CT.seq (J := fun s => ∃ σ, VG.Proof.AesGcmSiv.X86.KeysPost p σ s) (VG.Proof.AesGcmSiv.X86.keys_ct v L)
    (fun _ E => WP.mono (VG.Proof.AesGcmSiv.X86.keys_ok v L E) fun s Ky => ⟨_, Ky⟩) ?_
  refine CT.seq (J := fun s => VG.Proof.AesGcmSiv.X86.Env p s ∧
      Spec.Gcm.blockAt s.mem (w64 p.W + BitVec.ofNat 64 64) =
        GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s.mem (w64 p.W + BitVec.ofNat 64 16) 16)) ∧
      Spec.Gcm.blockAt s.mem (w64 p.W + BitVec.ofNat 64 80) = 0)
    ((VG.Proof.AesGcmSiv.X86.crypt_ct v L).mono fun _ ⟨_, Ky⟩ => Ky.env)
    (fun _ ⟨_, Ky⟩ => WP.mono (VG.Proof.AesGcmSiv.X86.crypt_ok v L Ky.env) fun _ Cr => ⟨Cr.env, (VG.Proof.AesGcmSiv.X86.keys_crypt L Ky Cr).1, (VG.Proof.AesGcmSiv.X86.keys_crypt L Ky Cr).2.1⟩) ?_
  refine CT.seq (J := VG.Proof.AesGcmSiv.X86.Env p) ((VG.Proof.AesGcmSiv.X86.polyval_ct v L).mono fun _ h => h.1)
    (fun _ h => WP.mono (VG.Proof.AesGcmSiv.X86.polyval_ok v L h.1 h.2.1 h.2.2) fun _ Po => Po.env) ?_
  refine CT.seq (J := VG.Proof.AesGcmSiv.X86.Env p) (VG.Proof.AesGcmSiv.X86.tag_ct v L (o := 240) (by decide))
    (fun _ E => WP.mono (VG.Proof.AesGcmSiv.X86.tag_ok v L E (o := 240) (by decide)) fun _ Tg => Tg.env) ?_
  refine CT.seq (J := fun s => VG.Proof.AesGcmSiv.X86.Env p s ∧ ∃ c : Bool, s.gpr .eax = BitVec.ofNat 32 (if c then 1 else 0))
    (CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun s E => ?_) ?_
  · obtain ⟨s₆, run₆, ax₆, hm₆, bp₆, sp₆, rd₆, wr₆⟩ := VG.Proof.AesGcmSiv.X86.cmp_ok L E
    refine WP.of_runBlock ⟨s₆, run₆, E.keep (by rw [bp₆, E.ebp]) (by rw [sp₆, E.esp]) rd₆ wr₆ hm₆,
      decide (bytesAt s.mem (w64 p.W) 16 = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 240) 16), ?_⟩
    rw [ax₆]; simp only [VG.Proof.AesGcmSiv.X86.okVal, decide_eq_true_eq]
  refine CT.seq (J := VG.Proof.AesGcmSiv.X86.Env p) ((VG.Proof.AesGcmSiv.X86.mask_ct L).mono fun _ h => h.1)
    (fun _ ⟨E, _, hc⟩ => WP.mono (VG.Proof.AesGcmSiv.X86.mask_ok L E hc) fun _ Mk => Mk.env) ?_
  exact CT.taint [.ebp] (VG.Proof.AesGcmSiv.X86.pin_ebp fun _ h => h.ebp) (by taint_decide)

theorem open_ct (v : GcmImpl) : ConstantTime isa openX86.pre openX86.pub («open» v.callees) :=
  CT.constantTime VG.Proof.AesGcmSiv.X86.prmOf (fun _ _ _ _ h => VG.Proof.AesGcmSiv.X86.prmOf_pub h) fun p => by
    by_cases hex : ∃ s, VG.Proof.AesGcmSiv.X86.openPre s ∧ VG.Proof.AesGcmSiv.X86.prmOf s = p
    · obtain ⟨z, hz, rfl⟩ := hex
      exact VG.Proof.AesGcmSiv.X86.open_top_ct v (VG.Proof.AesGcmSiv.X86.lay_of (VG.Proof.AesGcmSiv.X86.onePre_open hz))
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

end VG.Proof.AesGcmSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86.Verified`. -/
section

/-!
# AES-GCM-SIV on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`), given that the tag input computed with GHASH is the RFC's
(`TagInputEq`, which the registration file has from
`Proof.GcmSiv.Polyval.tagInput_eq_tagInputG`, so that no proof here imports
its algebra), a state satisfying each
precondition, and the shared contracts with the working space as a last
argument (`Proof/AesGcmSiv/Scratch.lean`), with 28 bytes of stack: a call of
`vg_aes_ctr32` (its six arguments and return address), which makes no
calls.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86
open VG.Proof.AesGcm.X86 (GcmImpl)

/-- The return value: the low word of `edx:eax`. -/
theorem setWidth_ret (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := b.isLt
  rw [Nat.shiftLeft_eq, Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.zero_or, Nat.mod_eq_of_lt this]

section
variable (v : GcmImpl)

theorem seal_spSafe : («seal» v.callees).all (fun i => !isa.writesSp i) = true := by
  simp only [«seal», sivEntry, tagOut, Impl.AesGcm.X86.entry, VG.Impl.AesGcmSiv.X86.keys, derive, deriveBlock, derivePost, expand, hkey, polyval,
    absorb, chunk, absTail, absTailPre, lens, onStr, VG.Impl.AesGcmSiv.X86.tag, crypt, cryptBlock, cryptTail, callCtr, callKey, callGh,
    Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees, Code.all, v.ctr.spSafe, v.ctr.expandSpSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem open_spSafe : («open» v.callees).all (fun i => !isa.writesSp i) = true := by
  simp only [«open», sivEntry, recvTag, Impl.AesGcm.X86.entry, VG.Impl.AesGcmSiv.X86.keys, derive, deriveBlock, derivePost, expand, hkey, polyval,
    absorb, chunk, absTail, absTailPre, lens, onStr, VG.Impl.AesGcmSiv.X86.tag, crypt, cryptBlock, cryptTail, mask, callCtr, callKey,
    callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees, Code.all,
    v.ctr.spSafe, v.ctr.expandSpSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

end

/-- A state satisfying the precondition of `vg_aes_gcm_siv_seal`: the key
schedule at `0x1000`, 10 rounds, the nonce at `0x2000`, no additional data
(at `0x2100`), no data (at `0x3000`), the tag at `0x4000` and `work` at
`0x5000`, as stack arguments at `0x8004`. -/
def sealSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8011 then 0x21 else if a = 0x8019 then 0x30 else if a = 0x8021 then 0x40
    else if a = 0x8025 then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 16⟩, ⟨0x5000, 2816⟩, ⟨0x8004, 36⟩]

/-- As `sealSat`, with the tag read only. -/
def openSat : State :=
  { VG.Proof.AesGcmSiv.X86.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x4000, 16⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x5000, 2816⟩, ⟨0x8004, 36⟩] }

theorem sealSat_args : arg VG.Proof.AesGcmSiv.X86.sealSat 0 = 0x1000 ∧ arg VG.Proof.AesGcmSiv.X86.sealSat 1 = 10 ∧ arg VG.Proof.AesGcmSiv.X86.sealSat 2 = 0x2000 ∧
    arg VG.Proof.AesGcmSiv.X86.sealSat 3 = 0x2100 ∧ arg VG.Proof.AesGcmSiv.X86.sealSat 4 = 0 ∧ arg VG.Proof.AesGcmSiv.X86.sealSat 5 = 0x3000 ∧ arg VG.Proof.AesGcmSiv.X86.sealSat 6 = 0 ∧
    arg VG.Proof.AesGcmSiv.X86.sealSat 7 = 0x4000 ∧ arg VG.Proof.AesGcmSiv.X86.sealSat 8 = 0x5000 ∧ argAddr VG.Proof.AesGcmSiv.X86.sealSat 0 = 0x8004 := by
  decide

theorem openSat_args : arg VG.Proof.AesGcmSiv.X86.openSat 0 = 0x1000 ∧ arg VG.Proof.AesGcmSiv.X86.openSat 1 = 10 ∧ arg VG.Proof.AesGcmSiv.X86.openSat 2 = 0x2000 ∧
    arg VG.Proof.AesGcmSiv.X86.openSat 3 = 0x2100 ∧ arg VG.Proof.AesGcmSiv.X86.openSat 4 = 0 ∧ arg VG.Proof.AesGcmSiv.X86.openSat 5 = 0x3000 ∧ arg VG.Proof.AesGcmSiv.X86.openSat 6 = 0 ∧
    arg VG.Proof.AesGcmSiv.X86.openSat 7 = 0x4000 ∧ arg VG.Proof.AesGcmSiv.X86.openSat 8 = 0x5000 ∧ argAddr VG.Proof.AesGcmSiv.X86.openSat 0 = 0x8004 :=
  VG.Proof.AesGcmSiv.X86.sealSat_args

theorem seal_verified (v : GcmImpl) (hti : VG.Proof.AesGcmSiv.X86.TagInputEq) :
    Verified X86.target («seal» v.callees) (Proof.AesGcmSiv.sealScratchContract X86.abi 352 28) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesGcmSiv.X86.seal_wp v hti hs) (VG.Proof.AesGcmSiv.X86.seal_ct v) (by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, e⟩ := VG.Proof.AesGcmSiv.X86.sealSat_args
    have esp : sealSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Spec.GcmSiv.sealPost, VG.Proof.AesGcmSiv.X86.sealX86, VG.Proof.AesGcmSiv.X86.sealPre, VG.Proof.AesGcmSiv.X86.oneLay, VG.Proof.AesGcmSiv.X86.onePub, VG.Proof.AesGcmSiv.X86.schR, VG.Proof.AesGcmSiv.X86.nonceR, VG.Proof.AesGcmSiv.X86.aadR, VG.Proof.AesGcmSiv.X86.dataR, VG.Proof.AesGcmSiv.X86.tagR, VG.Proof.AesGcmSiv.X86.workR, VG.Proof.AesGcmSiv.X86.argsR', VG.Proof.AesGcmSiv.X86.retR,
      VG.Proof.AesGcmSiv.X86.stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using VG.Proof.AesGcmSiv.X86.sealSat)

theorem open_verified (v : GcmImpl) (hti : VG.Proof.AesGcmSiv.X86.TagInputEq) :
    Verified X86.target («open» v.callees) (Proof.AesGcmSiv.openScratchContract X86.abi 352 28) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesGcmSiv.X86.open_wp v hti hs) (VG.Proof.AesGcmSiv.X86.open_ct v)
    { pre := by
        sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.X86.openX86, VG.Proof.AesGcmSiv.X86.openResult, VG.Proof.AesGcmSiv.X86.openPost, VG.Proof.AesGcmSiv.X86.openPre, VG.Proof.AesGcmSiv.X86.oneLay, VG.Proof.AesGcmSiv.X86.onePub,
          VG.Proof.AesGcmSiv.X86.schR, VG.Proof.AesGcmSiv.X86.nonceR, VG.Proof.AesGcmSiv.X86.aadR, VG.Proof.AesGcmSiv.X86.dataR, VG.Proof.AesGcmSiv.X86.tagR, VG.Proof.AesGcmSiv.X86.workR, VG.Proof.AesGcmSiv.X86.argsR', VG.Proof.AesGcmSiv.X86.retR, VG.Proof.AesGcmSiv.X86.stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes]
      post := by
        intro s s' _ h
        sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.X86.openX86, VG.Proof.AesGcmSiv.X86.openResult, VG.Proof.AesGcmSiv.X86.openPost, VG.Proof.AesGcmSiv.X86.openPre, VG.Proof.AesGcmSiv.X86.oneLay, VG.Proof.AesGcmSiv.X86.onePub,
          VG.Proof.AesGcmSiv.X86.schR, VG.Proof.AesGcmSiv.X86.nonceR, VG.Proof.AesGcmSiv.X86.aadR, VG.Proof.AesGcmSiv.X86.dataR, VG.Proof.AesGcmSiv.X86.tagR, VG.Proof.AesGcmSiv.X86.workR, VG.Proof.AesGcmSiv.X86.argsR', VG.Proof.AesGcmSiv.X86.retR, VG.Proof.AesGcmSiv.X86.stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, VG.Proof.AesGcmSiv.X86.setWidth_ret]
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.X86.openX86, VG.Proof.AesGcmSiv.X86.openResult, VG.Proof.AesGcmSiv.X86.openPost, VG.Proof.AesGcmSiv.X86.openPre, VG.Proof.AesGcmSiv.X86.oneLay, VG.Proof.AesGcmSiv.X86.onePub,
          VG.Proof.AesGcmSiv.X86.schR, VG.Proof.AesGcmSiv.X86.nonceR, VG.Proof.AesGcmSiv.X86.aadR, VG.Proof.AesGcmSiv.X86.dataR, VG.Proof.AesGcmSiv.X86.tagR, VG.Proof.AesGcmSiv.X86.workR, VG.Proof.AesGcmSiv.X86.argsR', VG.Proof.AesGcmSiv.X86.retR, VG.Proof.AesGcmSiv.X86.stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, VG.Proof.AesGcmSiv.X86.setWidth_ret] at h
        sig_simp [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.X86.openX86, VG.Proof.AesGcmSiv.X86.openResult, VG.Proof.AesGcmSiv.X86.openPost, VG.Proof.AesGcmSiv.X86.openPre, VG.Proof.AesGcmSiv.X86.oneLay, VG.Proof.AesGcmSiv.X86.onePub,
          VG.Proof.AesGcmSiv.X86.schR, VG.Proof.AesGcmSiv.X86.nonceR, VG.Proof.AesGcmSiv.X86.aadR, VG.Proof.AesGcmSiv.X86.dataR, VG.Proof.AesGcmSiv.X86.tagR, VG.Proof.AesGcmSiv.X86.workR, VG.Proof.AesGcmSiv.X86.argsR', VG.Proof.AesGcmSiv.X86.retR, VG.Proof.AesGcmSiv.X86.stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, VG.Proof.AesGcmSiv.X86.setWidth_ret] [] at h
        intro _
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.X86.openX86, VG.Proof.AesGcmSiv.X86.openResult, VG.Proof.AesGcmSiv.X86.openPost, VG.Proof.AesGcmSiv.X86.openPre, VG.Proof.AesGcmSiv.X86.oneLay, VG.Proof.AesGcmSiv.X86.onePub,
          VG.Proof.AesGcmSiv.X86.schR, VG.Proof.AesGcmSiv.X86.nonceR, VG.Proof.AesGcmSiv.X86.aadR, VG.Proof.AesGcmSiv.X86.dataR, VG.Proof.AesGcmSiv.X86.tagR, VG.Proof.AesGcmSiv.X86.workR, VG.Proof.AesGcmSiv.X86.argsR', VG.Proof.AesGcmSiv.X86.retR, VG.Proof.AesGcmSiv.X86.stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes] at h
        sig_split h
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.X86.openX86, VG.Proof.AesGcmSiv.X86.openResult, VG.Proof.AesGcmSiv.X86.openPost, VG.Proof.AesGcmSiv.X86.openPre, VG.Proof.AesGcmSiv.X86.oneLay, VG.Proof.AesGcmSiv.X86.onePub,
          VG.Proof.AesGcmSiv.X86.schR, VG.Proof.AesGcmSiv.X86.nonceR, VG.Proof.AesGcmSiv.X86.aadR, VG.Proof.AesGcmSiv.X86.dataR, VG.Proof.AesGcmSiv.X86.tagR, VG.Proof.AesGcmSiv.X86.workR, VG.Proof.AesGcmSiv.X86.argsR', VG.Proof.AesGcmSiv.X86.retR, VG.Proof.AesGcmSiv.X86.stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes]
        sig_simp [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig, Spec.GcmSiv.openPre,
          Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.X86.openX86, VG.Proof.AesGcmSiv.X86.openResult, VG.Proof.AesGcmSiv.X86.openPost, VG.Proof.AesGcmSiv.X86.openPre, VG.Proof.AesGcmSiv.X86.oneLay, VG.Proof.AesGcmSiv.X86.onePub,
          VG.Proof.AesGcmSiv.X86.schR, VG.Proof.AesGcmSiv.X86.nonceR, VG.Proof.AesGcmSiv.X86.aadR, VG.Proof.AesGcmSiv.X86.dataR, VG.Proof.AesGcmSiv.X86.tagR, VG.Proof.AesGcmSiv.X86.workR, VG.Proof.AesGcmSiv.X86.argsR', VG.Proof.AesGcmSiv.X86.retR, VG.Proof.AesGcmSiv.X86.stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
      sat := by
        obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, e⟩ := VG.Proof.AesGcmSiv.X86.openSat_args
        have esp : openSat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.X86.openX86, VG.Proof.AesGcmSiv.X86.openResult, VG.Proof.AesGcmSiv.X86.openPost, VG.Proof.AesGcmSiv.X86.openPre,
          VG.Proof.AesGcmSiv.X86.oneLay, VG.Proof.AesGcmSiv.X86.onePub, VG.Proof.AesGcmSiv.X86.schR, VG.Proof.AesGcmSiv.X86.nonceR, VG.Proof.AesGcmSiv.X86.aadR, VG.Proof.AesGcmSiv.X86.dataR, VG.Proof.AesGcmSiv.X86.tagR, VG.Proof.AesGcmSiv.X86.workR, VG.Proof.AesGcmSiv.X86.argsR', VG.Proof.AesGcmSiv.X86.retR, VG.Proof.AesGcmSiv.X86.stackR, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using VG.Proof.AesGcmSiv.X86.openSat }

end VG.Proof.AesGcmSiv.X86

end
