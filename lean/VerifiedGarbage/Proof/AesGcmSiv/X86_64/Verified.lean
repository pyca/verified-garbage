import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerifyCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.AesGcmSiv.X86_64
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.GcmSiv.Words32
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Narrow
import Mathlib.Data.List.Dedup
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcmSiv.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86_64.Env`. -/
section

/-!
# AES-GCM-SIV on x86-64: the contracts, where everything is and running blocks

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
  let data : Region := ⟨s.gpr .r9, (VG.Proof.AesGcmSiv.arg s 0).toNat⟩
  let tag : Region := ⟨VG.Proof.AesGcmSiv.arg s 1, 16⟩
  let work : Region := ⟨VG.Proof.AesGcmSiv.arg s 2, 3816⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (VG.Proof.AesGcmSiv.args s 3) ∧ work.Disjoint (VG.Proof.AesGcmSiv.args s 3) ∧
    (VG.Proof.AesGcmSiv.ret s).Disjoint data ∧ (VG.Proof.AesGcmSiv.ret s).Disjoint work ∧
    (VG.Proof.AesGcmSiv.stk8 s).Disjoint sch ∧ (VG.Proof.AesGcmSiv.stk8 s).Disjoint nonce ∧ (VG.Proof.AesGcmSiv.stk8 s).Disjoint aad ∧ (VG.Proof.AesGcmSiv.stk8 s).Disjoint data ∧
    (VG.Proof.AesGcmSiv.stk8 s).Disjoint tag ∧ (VG.Proof.AesGcmSiv.stk8 s).Disjoint work ∧
    (s.gpr .rdi).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (VG.Proof.AesGcmSiv.arg s 0).toNat ≤ 2 ^ 64 ∧
    (VG.Proof.AesGcmSiv.arg s 1).toNat + 16 ≤ 2 ^ 64 ∧ (VG.Proof.AesGcmSiv.arg s 2).toNat + 3816 ≤ 2 ^ 64 ∧ 8 ≤ (s.gpr .rsp).toNat ∧
    (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧ VG.Proof.AesGcmSiv.rounds s

/-- What `vg_aes_gcm_siv_seal` needs: `oneLay`, with `tag` the 16 bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, 12⟩
  let aad : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (VG.Proof.AesGcmSiv.arg s 0).toNat⟩
  let tag : Region := ⟨VG.Proof.AesGcmSiv.arg s 1, 16⟩
  let work : Region := ⟨VG.Proof.AesGcmSiv.arg s 2, 3816⟩
  s.rd = [sch, nonce, aad, VG.Proof.AesGcmSiv.args s 3] ∧ s.wr = [data, tag, work] ∧ VG.Proof.AesGcmSiv.oneLay s ∧ (VG.Proof.AesGcmSiv.ret s).Disjoint tag

/-- What `vg_aes_gcm_siv_open` needs: `oneLay`, with the received tag the 16
bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, 12⟩
  let aad : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (VG.Proof.AesGcmSiv.arg s 0).toNat⟩
  let tag : Region := ⟨VG.Proof.AesGcmSiv.arg s 1, 16⟩
  let work : Region := ⟨VG.Proof.AesGcmSiv.arg s 2, 3816⟩
  s.rd = [sch, nonce, aad, tag, VG.Proof.AesGcmSiv.args s 3] ∧ s.wr = [data, work] ∧ VG.Proof.AesGcmSiv.oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < 3, VG.Proof.AesGcmSiv.arg s₁ i = VG.Proof.AesGcmSiv.arg s₂ i

/-- `vg_aes_gcm_siv_seal`. -/
def sealX86_64 : Contract isa where
  pre := VG.Proof.AesGcmSiv.sealPre
  post s s' :=
    VG.Spec.GcmSiv.encryptWith (VG.Spec.GcmSiv.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (keyLen (s.gpr .rsi).toNat)
        (bytesAt s.mem (s.gpr .rdx) 12) (bytesAt s.mem (s.gpr .r9) (VG.Proof.AesGcmSiv.arg s 0).toNat)
        (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) =
      (bytesAt s'.mem (s.gpr .r9) (VG.Proof.AesGcmSiv.arg s 0).toNat, bytesAt s'.mem (VG.Proof.AesGcmSiv.arg s 1) 16)
  pub := VG.Proof.AesGcmSiv.onePub

/-- What `vg_aes_gcm_siv_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  VG.Spec.GcmSiv.decryptWith (VG.Spec.GcmSiv.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (keyLen (s.gpr .rsi).toNat)
    (bytesAt s.mem (s.gpr .rdx) 12) (bytesAt s.mem (s.gpr .r9) (VG.Proof.AesGcmSiv.arg s 0).toNat)
    (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (bytesAt s.mem (VG.Proof.AesGcmSiv.arg s 1) 16)

/-- What `vg_aes_gcm_siv_open` leaves in `rax` and in the `n` bytes of data
at `D`, for the result `r`. Irreducible, so that checking a state against
it never evaluates `r`. -/
@[irreducible] def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
  | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem D n = VG.Spec.GcmSiv.zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : (s'.gpr .rax).setWidth 32 = 1) (hd : bytesAt s'.mem D n = pt) : VG.Proof.AesGcmSiv.openPost r s' D n := by
  subst hr; unfold VG.Proof.AesGcmSiv.openPost; exact ⟨hax, hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : (s'.gpr .rax).setWidth 32 = 0) (hd : bytesAt s'.mem D n = VG.Spec.GcmSiv.zeros n) : VG.Proof.AesGcmSiv.openPost r s' D n := by
  subst hr; unfold VG.Proof.AesGcmSiv.openPost; exact ⟨hax, hd⟩

/-- What `vg_aes_gcm_siv_open` may leak (`Spec.GcmSiv.openLeak`): whether it
succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬VG.Proof.AesGcmSiv.rounds s then [] else [if (VG.Proof.AesGcmSiv.openResult s).isSome then 1 else 0]

/-- `vg_aes_gcm_siv_open`. -/
def openX86_64 : Contract isa where
  pre := VG.Proof.AesGcmSiv.openPre
  post s s' := VG.Proof.AesGcmSiv.openPost (VG.Proof.AesGcmSiv.openResult s) s' (s.gpr .r9) (VG.Proof.AesGcmSiv.arg s 0).toNat
  pub s₁ s₂ := VG.Proof.AesGcmSiv.onePub s₁ s₂ ∧ VG.Proof.AesGcmSiv.openLeak s₁ = VG.Proof.AesGcmSiv.openLeak s₂

end VG.Proof.AesGcmSiv

/-!
## Where everything is

Untrusted: everything here is checked by Lean. The key schedule of the
key-generating key (240 bytes at `K`), the working space (3816 bytes at
`W`) and the 8 bytes of stack below `SP` that the calls use (`Lay`); what a
state may access (`Perm`); the registers holding `K` and `W` and the stack
pointer (`Env`); and the public values the entry keeps in `W` (`Slots`).
The pieces write the parts of `W` in `mutR` (and the data, and the stack
below `SP`), so the slots and our caller's registers saved in `W` stay as
the entry left them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (covers_off in_off in_left covers_left)

/-! ## The regions -/

/-- The key schedule, `W` and the stack below `SP` used by the calls. -/
structure Lay (K W SP : Addr) : Prop where
  kw : K.toNat + 240 ≤ 2 ^ 64
  ww : W.toNat + 3816 ≤ 2 ^ 64
  k_w : (⟨K, 240⟩ : Region).Disjoint ⟨W, 3816⟩
  stk_k : (below SP 8).Disjoint ⟨K, 240⟩
  stk_w : (below SP 8).Disjoint ⟨W, 3816⟩
  sp : 8 ≤ SP.toNat

/-- What a state may access. -/
structure Perm (K W : Addr) (s : State) : Prop where
  k : Covers [⟨K, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨W, 3816⟩] s.wr

/-- The registers holding the key schedule, `W` and the stack pointer, and
what the state may access. -/
structure Env (K W SP : Addr) (s : State) : Prop where
  r13 : s.gpr .r13 = K
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = SP
  perm : VG.Proof.AesGcmSiv.X86_64.Perm K W s

theorem Perm.of_eq {K W : Addr} {s s' : State} (h : VG.Proof.AesGcmSiv.X86_64.Perm K W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesGcmSiv.X86_64.Perm K W s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `r13`, `r15`, `rsp` and the permissions. -/
theorem Env.keep {K W SP : Addr} {s s' : State} (h : VG.Proof.AesGcmSiv.X86_64.Env K W SP s)
    (hg : ∀ r ∈ [Reg.r13, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesGcmSiv.X86_64.Env K W SP s' :=
  ⟨by rw [hg _ (by simp), h.r13], by rw [hg _ (by simp), h.r15], by rw [hg _ (by simp), h.rsp],
    h.perm.of_eq hrd hwr⟩

theorem Env.of_saved {K W SP : Addr} {s s' : State} (h : VG.Proof.AesGcmSiv.X86_64.Env K W SP s)
    (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcmSiv.X86_64.Env K W SP s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg _ (by decide)) hrd hwr

namespace Lay

theorem kSub {K : Addr} {d n : Nat} (h : d + n ≤ 240) : Region.Sub ⟨K + BitVec.ofNat 64 d, n⟩ ⟨K, 240⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 3816) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 3816⟩ :=
  Offset.sub_base _ h

variable {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 3816) (hd : d + k ≤ 3816) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem k_w' {d k : Nat} (hd : d + k ≤ 3816) : (⟨K, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (VG.Proof.AesGcmSiv.X86_64.Lay.wSub hd)

theorem stk_w' {a n : Nat} (ha : a + n ≤ 3816) : (below SP 8).Disjoint ⟨W + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (VG.Proof.AesGcmSiv.X86_64.Lay.wSub ha)

end Lay

namespace Perm

variable {K W : Addr} {s : State} (P : VG.Proof.AesGcmSiv.X86_64.Perm K W s)
include P

theorem kR {d n : Nat} (h : d + n ≤ 240) : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 d) n :=
  in_off P.k h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 3816) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 3816) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 3816) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 3816) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_left (P.wC h)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W`, the
key schedule and the stack below `SP`. -/
structure Buf (K W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩
  stk : (below SP 8).Disjoint ⟨D, n⟩

namespace Buf

variable {K W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s (D + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega
  w := h.w.sub_left (Offset.sub_base D (by omega))
  stk := h.stk.sub_right (Offset.sub_base D (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s (D + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega)).take (by omega)

end Buf

/-! ## The slots -/

/-- The public values the entry keeps in `W`: the rounds, the nonce, the
additional data and its length, and the data and its length. -/
structure Slots (W : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (m : Mem) : Prop where
  rounds : m.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 R
  nonce : m.readW (W + BitVec.ofNat 64 208) 64 = N
  aad : m.readW (W + BitVec.ofNat 64 216) 64 = A
  alen : m.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al
  data : m.readW (W + BitVec.ofNat 64 232) 64 = D
  len : m.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n

/-- The parts of `W` the pieces write: the blocks at `[0, 144)`, `ok` at
`[192, 200)` and `[248, 3816)`. -/
abbrev wA (W : Addr) : Region := ⟨W, 144⟩
abbrev wO (W : Addr) : Region := ⟨W + BitVec.ofNat 64 192, 8⟩
abbrev wC (W : Addr) : Region := ⟨W + BitVec.ofNat 64 248, 3568⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (W SP D : Addr) (n : Nat) : List Region := [VG.Proof.AesGcmSiv.X86_64.wA W, VG.Proof.AesGcmSiv.X86_64.wO W, VG.Proof.AesGcmSiv.X86_64.wC W, below SP 8, ⟨D, n⟩]

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {K W SP D : Addr} {n : Nat} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    {d k : Nat} (hd : 144 ≤ d ∧ d + k ≤ 192 ∨ 200 ≤ d ∧ d + k ≤ 248) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.mutR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 144) (.inr (by omega)) (by omega) (by decide)
  · rcases hd with hd | hd
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm
  · exact (hD.sub_right (Lay.wSub (by omega))).symm

end VG.Proof.AesGcmSiv.X86_64

/-!
## Running blocks

Untrusted: everything here is checked by Lean. `srun [facts]` runs a block
of the instructions the AES-GCM-SIV code uses from a state in which the
`facts` (register values and accessible memory) hold; and the reading of
conditions and sequences of programs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Proof.AesGcm.X86_64 (offset_nat imm_eq setWidth_imm ofNat_add_ofNat toNat_ofNat_of_lt)

/-- A part of `W` read after a write to another part. -/
theorem readW_writeW_W {m : Mem} {W : Addr} {d e w w' : Nat} (v : BitVec w') (h : d + w / 8 ≤ e ∨ e + w' / 8 ≤ d)
    (hd : d + w / 8 ≤ 2 ^ 64) (he : e + w' / 8 ≤ 2 ^ 64) (hw : w / 8 < 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 e) v).readW (W + BitVec.ofNat 64 d) w = m.readW (W + BitVec.ofNat 64 d) w :=
  Mem.readW_writeW_sep (Offset.sep W h hd he) hw

/-- Runs a block of the instructions the AES-GCM-SIV code uses. -/
macro "srun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [imm_eq, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, execAlu, execAlu32, execShift, State.load64, State.store64, State.load32, State.store32,
    State.load8, State.store8, State.ea, State.setReg32, offset_nat, at_, imm, ptr, tagO, akO, ekO, hO, yO, cmO,
    ccO, bO, okO, roundsO, nonceO, aadO, alenO, dataO, lenO, skO, revO, ghO, scrO, List.cons_append,
    List.nil_append, List.append_assoc, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
    gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags,
    wr_setReg, wr_arithFlags, wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, setWidth_imm, and_self, and_true, true_and, BitVec.add_zero,
    readW_writeW_W, $ts,*]) <;> try rfl)

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ofNat_add_ofNat]

theorem eval_e {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .e s = some b := h
theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some !b := by
  show s.zf.map _ = _; rw [h]; rfl
theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := h

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

theorem seq_assoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => WP.assoc h)

theorem seq_assoc4 {a b c d e : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b (.seq c d))) e) s Q) : WP isa (.seq a (.seq b (.seq c (.seq d e)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => VG.Proof.AesGcmSiv.X86_64.seq_assoc3 h)

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

end VG.Proof.AesGcmSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86_64.Entry`. -/
section

/-!
# AES-GCM-SIV on x86-64: the entry, the exit and the arguments

Untrusted: everything here is checked by Lean. `entry` reads the stack
arguments, saves our caller's registers at `W + 144` and keeps the arguments
but `tag` in `W` (`entry_ok`); `restore` reads the registers back (`restore_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Proof.AesGcm.X86_64 (in_off)
open VG.Spec.Aes (bytesAt)

/-- Our caller's registers, saved at `W + 144`. -/
def Saved (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Prop :=
  ∀ p ∈ saved, m.readW (W + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The save area and the slots, which `entry` writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 144, 104⟩

theorem readW_writeW_off {m : Mem} {W : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 e) v).readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep W h hd he) (by decide)

/-- `entry`. -/
theorem entry_ok {K W SP : Addr} {s : State} (P : VG.Proof.AesGcmSiv.X86_64.Perm K W s) {R : Nat} {N A D : Addr} {al n : Nat}
    (hsp : s.gpr .rsp = SP) (hargs : Covers [⟨SP + BitVec.ofNat 64 8, 24⟩] (s.rd ++ s.wr))
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    ∃ s₁, runBlock isa entry s = some s₁ ∧ VG.Proof.AesGcmSiv.X86_64.Env K W SP s₁ ∧ VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n s₁.mem ∧
      VG.Proof.AesGcmSiv.X86_64.Saved s₁.mem W s.gpr ∧ Frame [VG.Proof.AesGcmSiv.X86_64.entryR W] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have a₈ := in_off (d := 0) (n := 8) hargs (by decide) (by decide)
  have a₂₄ := in_off (d := 16) (n := 8) hargs (by decide) (by decide)
  rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, show 8 + 0 = 8 from rfl] at a₈
  rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc] at a₂₄
  simp only [Nat.reduceAdd] at a₂₄
  have w₁ := P.wW (show 144 + 8 ≤ 3816 by decide)
  have w₂ := P.wW (show 152 + 8 ≤ 3816 by decide)
  have w₃ := P.wW (show 160 + 8 ≤ 3816 by decide)
  have w₄ := P.wW (show 168 + 8 ≤ 3816 by decide)
  have w₅ := P.wW (show 176 + 8 ≤ 3816 by decide)
  have w₆ := P.wW (show 184 + 8 ≤ 3816 by decide)
  have w₇ := P.wW (show 200 + 8 ≤ 3816 by decide)
  have w₈ := P.wW (show 208 + 8 ≤ 3816 by decide)
  have w₉ := P.wW (show 216 + 8 ≤ 3816 by decide)
  have w₁₀ := P.wW (show 224 + 8 ≤ 3816 by decide)
  have w₁₁ := P.wW (show 232 + 8 ≤ 3816 by decide)
  have w₁₂ := P.wW (show 240 + 8 ≤ 3816 by decide)
  have cE : ∀ d, 144 ≤ d → d + 8 ≤ 248 → (VG.Proof.AesGcmSiv.X86_64.entryR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
  refine ⟨_, by srun [entry, save, saved, List.map_cons, List.map_nil, hW, hsp, hn, a₈, a₂₄, w₁, w₂, w₃, w₄,
      w₅, w₆, w₇, w₈, w₉, w₁₀, w₁₁, w₁₂], ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hdi]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hsp]
  · exact P.of_eq rfl rfl
  iterate 6
    · simp (disch := decide) only [mem_setReg, VG.Proof.AesGcmSiv.X86_64.readW_writeW_off, Mem.readW_writeW_self64, gpr_setReg,
        ite_true, ite_false, reduceCtorEq, hsi, hdx, hcx, hr8, hr9, hn]
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [mem_setReg, VG.Proof.AesGcmSiv.X86_64.readW_writeW_off, Mem.readW_writeW_self64]
  · simp only [mem_setReg]
    repeat (first | exact Frame.refl _ _ |
      refine Frame.writeW ?_ (List.mem_singleton_self _) _ (cE _ (by decide) (by decide)))
  all_goals rfl

/-- `restore`: our caller's registers back. -/
theorem restore_ok {K W SP : Addr} {s : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP s) {g : Reg → BitVec 64} (hs : VG.Proof.AesGcmSiv.X86_64.Saved s.mem W g) :
    ∃ s', runBlock isa VG.Impl.AesGcmSiv.X86_64.restore s = some s' ∧ (∀ p ∈ saved, s'.gpr p.1 = g p.1) ∧ s'.mem = s.mem ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rax = s.gpr .rax := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 144 + 8 ≤ 3816 by decide)
  have r₂ := E.perm.wR (show 152 + 8 ≤ 3816 by decide)
  have r₃ := E.perm.wR (show 160 + 8 ≤ 3816 by decide)
  have r₄ := E.perm.wR (show 168 + 8 ≤ 3816 by decide)
  have r₅ := E.perm.wR (show 176 + 8 ≤ 3816 by decide)
  have r₆ := E.perm.wR (show 184 + 8 ≤ 3816 by decide)
  have v₁ := hs (.rbx, 144) (by decide)
  have v₂ := hs (.rbp, 152) (by decide)
  have v₃ := hs (.r12, 160) (by decide)
  have v₄ := hs (.r13, 168) (by decide)
  have v₅ := hs (.r14, 176) (by decide)
  have v₆ := hs (.r15, 184) (by decide)
  refine ⟨_, by srun [VG.Impl.AesGcmSiv.X86_64.restore, saved, List.map_cons, List.map_nil, h15, r₁, r₂, r₃, r₄, r₅, r₆], ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, v₁, v₂, v₃, v₄, v₅, v₆]
  · rfl
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]

end VG.Proof.AesGcmSiv.X86_64

/-!
## The arguments

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`TagBuf`, `args_of_seal`, `args_of_open`). Between `entry` and `restore`, the
pieces only write the parts of `W` below 144, from 192 to 200 and from 248
on, the stack below `SP` and the data (`mutR`), so they keep the slots, the
saved registers, the key schedule, the nonce, the additional data and the
tag's address on the stack (`argT_kept`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64
open VG.Impl.AesGcmSiv.X86_64 (saved)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (covers_left covers_of_mem bytesAt_frame)

/-- What `seal` and `open` are given: the key schedule at `K` for `R`
rounds, the nonce (12 bytes at `N`), the additional data (`al` bytes at
`A`), the data (`n` bytes at `D`), the working space at `W` and the stack
pointer `SP`. -/
structure Args (s : State) (K W SP N A D : Addr) (R al n : Nat) : Prop where
  lay : VG.Proof.AesGcmSiv.X86_64.Lay K W SP
  perm : VG.Proof.AesGcmSiv.X86_64.Perm K W s
  rounds : R = 10 ∨ R = 14
  nonce : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s N 12
  aad : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s A al
  data : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s D n
  dw : Covers [⟨D, n⟩] s.wr
  dk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩
  nd : (⟨N, 12⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  retW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 3816⟩
  retD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  args : Covers [⟨SP + BitVec.ofNat 64 8, 24⟩] (s.rd ++ s.wr)
  argsW : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨W, 3816⟩
  argsD : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨D, n⟩

/-- The tag, the 16 bytes at `T`: apart from the data, `W` and the stack
below `SP`. -/
structure TagBuf (W SP D : Addr) (n : Nat) (T : Addr) : Prop where
  d : (⟨T, 16⟩ : Region).Disjoint ⟨D, n⟩
  w : (⟨T, 16⟩ : Region).Disjoint ⟨W, 3816⟩
  stk : (below SP 8).Disjoint ⟨T, 16⟩
  wrap : T.toNat + 16 ≤ 2 ^ 64

theorem arg_eq (s : State) (i : Nat) : VG.Proof.AesGcmSiv.arg s i = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 64 := rfl

/-- `Args` from the layout, with the buffers covered as each function's
permissions say. -/
theorem args_of_lay {s : State} (h : VG.Proof.AesGcmSiv.oneLay s)
    (hk : Covers [⟨s.gpr .rdi, 240⟩] (s.rd ++ s.wr)) (hN : Covers [⟨s.gpr .rdx, 12⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩] (s.rd ++ s.wr)) (ha : Covers [VG.Proof.AesGcmSiv.args s 3] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .r9, (VG.Proof.AesGcmSiv.arg s 0).toNat⟩] s.wr) (hW : Covers [⟨VG.Proof.AesGcmSiv.arg s 2, 3816⟩] s.wr) :
    VG.Proof.AesGcmSiv.X86_64.Args s (s.gpr .rdi) (VG.Proof.AesGcmSiv.arg s 2) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r9) (s.gpr .rsi).toNat
        (s.gpr .r8).toNat (VG.Proof.AesGcmSiv.arg s 0).toNat ∧
      VG.Proof.AesGcmSiv.X86_64.TagBuf (VG.Proof.AesGcmSiv.arg s 2) (s.gpr .rsp) (s.gpr .r9) (VG.Proof.AesGcmSiv.arg s 0).toNat (VG.Proof.AesGcmSiv.arg s 1) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, b20, b21, b22, b23,
    b24, b25, b26, _, hR⟩ := h
  exact ⟨{
    lay := ⟨b20, b25, d2, d14, d19, b26⟩
    perm := ⟨hk, hW⟩
    rounds := hR
    nonce := ⟨hN, by decide, b21, d4, d15⟩
    aad := ⟨hA, BitVec.isLt _, b22, d6, d16⟩
    data := ⟨covers_left hD, BitVec.isLt _, b23, d9, d17⟩
    dw := hD
    dk := d1
    nd := d3
    ad := d5
    retW := d13
    retD := d12
    args := ha
    argsW := d11.symm
    argsD := d10.symm }, ⟨d7, d8, d18, b24⟩⟩

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : VG.Proof.AesGcmSiv.sealPre s) :
    (VG.Proof.AesGcmSiv.X86_64.Args s (s.gpr .rdi) (VG.Proof.AesGcmSiv.arg s 2) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r9) (s.gpr .rsi).toNat
        (s.gpr .r8).toNat (VG.Proof.AesGcmSiv.arg s 0).toNat ∧
      VG.Proof.AesGcmSiv.X86_64.TagBuf (VG.Proof.AesGcmSiv.arg s 2) (s.gpr .rsp) (s.gpr .r9) (VG.Proof.AesGcmSiv.arg s 0).toNat (VG.Proof.AesGcmSiv.arg s 1)) ∧
      Covers [⟨VG.Proof.AesGcmSiv.arg s 1, 16⟩] s.wr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨VG.Proof.AesGcmSiv.arg s 1, 16⟩ := by
  obtain ⟨hrd, hwr, hl, hrt⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .rdi, 240⟩ : Region), ⟨s.gpr .rdx, 12⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩,
      VG.Proof.AesGcmSiv.args s 3], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .r9, (VG.Proof.AesGcmSiv.arg s 0).toNat⟩ : Region), ⟨VG.Proof.AesGcmSiv.arg s 1, 16⟩, ⟨VG.Proof.AesGcmSiv.arg s 2, 3816⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨VG.Proof.AesGcmSiv.X86_64.args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)), mwr _ (by simp), hrt⟩

/-- `open`'s arguments, and its received tag, to read. -/
theorem args_of_open {s : State} (h : VG.Proof.AesGcmSiv.openPre s) :
    (VG.Proof.AesGcmSiv.X86_64.Args s (s.gpr .rdi) (VG.Proof.AesGcmSiv.arg s 2) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r9) (s.gpr .rsi).toNat
        (s.gpr .r8).toNat (VG.Proof.AesGcmSiv.arg s 0).toNat ∧
      VG.Proof.AesGcmSiv.X86_64.TagBuf (VG.Proof.AesGcmSiv.arg s 2) (s.gpr .rsp) (s.gpr .r9) (VG.Proof.AesGcmSiv.arg s 0).toNat (VG.Proof.AesGcmSiv.arg s 1)) ∧
      Covers [⟨VG.Proof.AesGcmSiv.arg s 1, 16⟩] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .rdi, 240⟩ : Region), ⟨s.gpr .rdx, 12⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩,
      ⟨VG.Proof.AesGcmSiv.arg s 1, 16⟩, VG.Proof.AesGcmSiv.args s 3], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .r9, (VG.Proof.AesGcmSiv.arg s 0).toNat⟩ : Region), ⟨VG.Proof.AesGcmSiv.arg s 2, 3816⟩], Covers [r] s.wr := fun r hr =>
    covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨VG.Proof.AesGcmSiv.X86_64.args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)), mrd _ (by simp)⟩

/-- The tag as a buffer to read. -/
theorem TagBuf.buf {K W SP D T : Addr} {n : Nat} {s : State} (h : VG.Proof.AesGcmSiv.X86_64.TagBuf W SP D n T)
    (hr : Covers [⟨T, 16⟩] (s.rd ++ s.wr)) : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s T 16 :=
  ⟨hr, by decide, h.wrap, h.w, h.stk⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- The cipher of a key schedule outside a frame's regions. -/
theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [VG.Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

section
variable {K W SP N A D : Addr} {R al n : Nat} {m m' : Mem}

/-- The tag's address, at `SP + 16`, misses what the entry and the pieces
write. -/
theorem argT_disj (hW : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hD : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.entryR W :: VG.Proof.AesGcmSiv.X86_64.mutR W SP D n, (⟨SP + BitVec.ofNat 64 16, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨SP + BitVec.ofNat 64 16, 8⟩ ⟨SP + BitVec.ofNat 64 8, 24⟩ := by
    rw [show SP + BitVec.ofNat 64 16 = SP + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 by rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc]]
    exact Offset.sub_base _ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hW.sub_left hs).sub_right (Region.sub_prefix (by decide))
  · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact Offset.disjoint_below SP (by decide)
  · exact hD.sub_left hs

/-- The tag's address, at `SP + 16`, through the entry and the pieces. -/
theorem argT_kept (hf : Frame (VG.Proof.AesGcmSiv.X86_64.entryR W :: VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) m m')
    (hW : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hD : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨D, n⟩) :
    m'.readW (SP + BitVec.ofNat 64 16) 64 = m.readW (SP + BitVec.ofNat 64 16) 64 :=
  hf.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (VG.Proof.AesGcmSiv.X86_64.argT_disj hW hD) (by decide)

/-- The tag, through the entry and the pieces. -/
theorem tag_kept {T : Addr} (hT : VG.Proof.AesGcmSiv.X86_64.TagBuf W SP D n T) (hf : Frame (VG.Proof.AesGcmSiv.X86_64.entryR W :: VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) m m') :
    bytesAt m' T 16 = bytesAt m T 16 :=
  VG.Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.w.sub_right (Region.sub_prefix (by decide))
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.stk.symm
    · exact hT.d) (by decide)

theorem slots_mut (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hf : Frame (VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) m m') (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n m) : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n m' := by
  have k : ∀ d, (144 ≤ d ∧ d + 8 ≤ 192 ∨ 200 ≤ d ∧ d + 8 ≤ 248) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _) (VG.Proof.AesGcmSiv.X86_64.kept_mut L hD hd) (by decide)
  exact ⟨by rw [k 200 (by decide)]; exact S.rounds, by rw [k 208 (by decide)]; exact S.nonce,
    by rw [k 216 (by decide)]; exact S.aad, by rw [k 224 (by decide)]; exact S.alen,
    by rw [k 232 (by decide)]; exact S.data, by rw [k 240 (by decide)]; exact S.len⟩

theorem saved_mut (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hf : Frame (VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) m m') {g : Reg → BitVec 64} (S : VG.Proof.AesGcmSiv.X86_64.Saved m W g) : VG.Proof.AesGcmSiv.X86_64.Saved m' W g := by
  intro p hp
  rw [← S p hp]
  have hd : 144 ≤ p.2 ∧ p.2 + 8 ≤ 192 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact hf.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (w := 64) (Region.contains_self _ _) (VG.Proof.AesGcmSiv.X86_64.kept_mut L hD (.inl hd))
    (by decide)

theorem ciph_mut (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) (hR : R = 10 ∨ R = 14)
    (hf : Frame (VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) m m') : Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R :=
  VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.k_w.sub_right (Region.sub_prefix (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.stk_k.symm
    · exact hdk) (by rcases hR with h | h <;> subst h <;> decide)

theorem buf_mut {s : State} {P : Addr} {len : Nat} (hP : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s P len)
    (hPD : (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩) (hf : Frame (VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) m m') :
    bytesAt m' P len = bytesAt m P len :=
  VG.Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
    · exact hPD) (by have := hP.lt; omega)

end

end VG.Proof.AesGcmSiv.X86_64

/-!
## The arguments of the functions called

Untrusted: everything here is checked by Lean. The calls are those of
AES-GCM (`Proof.AesGcm.X86_64.ctr_call`, `gh_call`, `key_call`); `cargs`,
`gargs` and `kargs` build their arguments from the environment: the key
schedule of the key-generating key (`keyK`) or of the encryption key at
`W + 248` (`keyS`), blocks of `W` as counter blocks, states and data, the
data itself, and the working spaces at `W + 1512` and `W + 1768`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (CtrCall GhCall KeyCall covers_left covers_cons covers_nil covers_append)

theorem toNat_W {W : Addr} (hw : W.toNat + 3816 ≤ 2 ^ 64) {d : Nat} (hd : d < 3816) :
    (W + BitVec.ofNat 64 d).toNat = W.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Data for a call: `k` bytes at `Q`, which the code may read, apart from
the working spaces at `W + 1512` and the stack below `SP`. -/
structure Src (W SP : Addr) (s : State) (Q : Addr) (k : Nat) : Prop where
  rd : Covers [⟨Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 64
  qs : (⟨Q, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 1512, 2304⟩
  stk : (below SP 8).Disjoint ⟨Q, k⟩

/-- Bytes of `W` below 1512 as data. -/
theorem srcW {K W SP : Addr} {s : State} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) (P : VG.Proof.AesGcmSiv.X86_64.Perm K W s) {t k : Nat} (hk : t + k ≤ 1512) :
    VG.Proof.AesGcmSiv.X86_64.Src W SP s (W + BitVec.ofNat 64 t) k where
  rd := P.wCR (by omega)
  wrap := by rw [VG.Proof.AesGcmSiv.X86_64.toNat_W L.ww (by omega)]; have := L.ww; omega
  qs := L.w_w (.inl (by omega)) (by omega) (by decide)
  stk := L.stk_w' (by omega)

/-- A buffer as data. -/
theorem srcBuf {K W SP : Addr} {s : State} {Q : Addr} {k : Nat} (h : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s Q k) : VG.Proof.AesGcmSiv.X86_64.Src W SP s Q k :=
  ⟨h.rd, h.wrap, h.w.sub_right (Lay.wSub (by decide)), h.stk⟩

/-- A key schedule for `vg_aes_ctr32`, apart from the blocks of `W` below
248 and the working space at `W + 1768`. -/
structure Key (W SP : Addr) (s : State) (Kc : Addr) : Prop where
  rd : Covers [⟨Kc, 240⟩] (s.rd ++ s.wr)
  stk : (below SP 8).Disjoint ⟨Kc, 240⟩
  lo : (⟨Kc, 240⟩ : Region).Disjoint ⟨W, 248⟩
  hi : (⟨Kc, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 1768, 2048⟩

/-- The key-generating key's schedule. -/
theorem keyK {K W SP : Addr} {s : State} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) (P : VG.Proof.AesGcmSiv.X86_64.Perm K W s) : VG.Proof.AesGcmSiv.X86_64.Key W SP s K :=
  ⟨P.k, L.stk_k, L.k_w.sub_right (Region.sub_prefix (by decide)), L.k_w' (by decide)⟩

/-- The encryption key's schedule, at `W + 248`. -/
theorem keyS {K W SP : Addr} {s : State} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) (P : VG.Proof.AesGcmSiv.X86_64.Perm K W s) : VG.Proof.AesGcmSiv.X86_64.Key W SP s (W + BitVec.ofNat 64 248) :=
  ⟨P.wCR (by decide), L.stk_w' (by decide),
    by simpa using L.w_w (a := 248) (n := 240) (d := 0) (k := 248) (.inr (by decide)) (by decide) (by decide),
    L.w_w (.inl (by decide)) (by decide) (by decide)⟩

/-- The arguments of `vg_aes_ctr32`: the key schedule at `Kc`, the counter
block at `W + c`, `n` blocks at `Q`, which it may write, and the working
space at `W + 1768`. -/
theorem cargs {K W SP : Addr} {s : State} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 14) {Kc : Addr} (hk : VG.Proof.AesGcmSiv.X86_64.Key W SP s Kc) {c : Nat} (hc : c + 16 ≤ 248) {Q : Addr} {n : Nat}
    (hq : VG.Proof.AesGcmSiv.X86_64.Src W SP s Q (16 * n)) (hqc : (⟨Q, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 c, 16⟩)
    (hqk : (⟨Kc, 240⟩ : Region).Disjoint ⟨Q, 16 * n⟩) (hqw : Covers [⟨Q, 16 * n⟩] s.wr)
    (rdi : s.gpr .rdi = Kc) (rsi : s.gpr .rsi = BitVec.ofNat 64 R) (rdx : s.gpr .rdx = W + BitVec.ofNat 64 c)
    (rcx : s.gpr .rcx = Q) (r8 : s.gpr .r8 = BitVec.ofNat 64 n) (r9 : s.gpr .r9 = W + BitVec.ofNat 64 1768) :
    CtrCall s Kc (W + BitVec.ofNat 64 c) Q (W + BitVec.ofNat 64 1768) R n where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := by omega
  wrap := hq.wrap
  kc := hk.lo.sub_right (Offset.sub_base W hc)
  kd := hqk
  ks := hk.hi
  cd := hqc.symm
  cs := L.w_w (.inl (by omega)) (by omega) (by decide)
  ds := hq.qs.sub_right (Offset.sub W (by decide) (by decide))
  stkK := by rw [E.rsp]; exact hk.stk
  stkC := by rw [E.rsp]; exact L.stk_w' (by omega)
  stkD := by rw [E.rsp]; exact hq.stk
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  reads := covers_append (covers_cons hk.rd covers_nil)
    (covers_cons (E.perm.wCR (by omega)) (covers_cons hq.rd (covers_cons (E.perm.wCR (by decide)) covers_nil)))
  writes := covers_cons (E.perm.wC (by omega)) (covers_cons hqw (covers_cons (E.perm.wC (by decide)) covers_nil))

/-- The arguments of `vg_ghash`: GHASH's key at `W + 64`, its accumulator at
`W + 80`, `n` blocks at `W + d` and the working space at `W + 1512`. -/
theorem gargs {K W SP : Addr} {s : State} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP s) {d n : Nat} (hd : 96 ≤ d)
    (hdn : d + 16 * n ≤ 1512) (rdi : s.gpr .rdi = W + BitVec.ofNat 64 64) (rsi : s.gpr .rsi = W + BitVec.ofNat 64 80)
    (rdx : s.gpr .rdx = W + BitVec.ofNat 64 d) (rcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (r8 : s.gpr .r8 = W + BitVec.ofNat 64 1512) :
    GhCall s (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 d) (W + BitVec.ofNat 64 1512) n where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  n_lt := by omega
  hy := L.w_w (.inl (by decide)) (by decide) (by decide)
  hs := L.w_w (.inl (by decide)) (by decide) (by decide)
  yd := L.w_w (.inl (by omega)) (by decide) (by omega)
  ys := L.w_w (.inl (by decide)) (by decide) (by decide)
  ds := L.w_w (.inl (by omega)) (by omega) (by decide)
  stkH := by rw [E.rsp]; exact L.stk_w' (by decide)
  stkY := by rw [E.rsp]; exact L.stk_w' (by decide)
  stkD := by rw [E.rsp]; exact L.stk_w' (by omega)
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  reads := covers_append (covers_cons (E.perm.wCR (by decide)) (covers_cons (E.perm.wCR (by omega)) covers_nil))
    (covers_cons (E.perm.wCR (by decide)) (covers_cons (E.perm.wCR (by decide)) covers_nil))
  writes := covers_cons (E.perm.wC (by decide)) (covers_cons (E.perm.wC (by decide)) covers_nil)

/-- The arguments of `vg_aes_expand_key`: the `l`-byte encryption key at
`W + 32`, its schedule at `W + 248` and the working space at `W + 1768`. -/
theorem kargs {K W SP : Addr} {s : State} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP s) {l : Nat} (hl : l = 16 ∨ l = 32)
    (rdi : s.gpr .rdi = W + BitVec.ofNat 64 32) (rsi : s.gpr .rsi = BitVec.ofNat 64 l)
    (rdx : s.gpr .rdx = W + BitVec.ofNat 64 248) (rcx : s.gpr .rcx = W + BitVec.ofNat 64 1768) :
    KeyCall s (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 1768) l where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  len := by omega
  kc := L.w_w (.inl (by omega)) (by omega) (by decide)
  ks := L.w_w (.inl (by omega)) (by omega) (by decide)
  cs := L.w_w (.inl (by decide)) (by decide) (by decide)
  stkK := by rw [E.rsp]; exact L.stk_w' (by omega)
  stkC := by rw [E.rsp]; exact L.stk_w' (by decide)
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  reads := covers_append (covers_cons (E.perm.wCR (by omega)) covers_nil)
    (covers_cons (E.perm.wCR (by decide)) (covers_cons (E.perm.wCR (by decide)) covers_nil))
  writes := covers_cons (E.perm.wC (by decide)) (covers_cons (E.perm.wC (by decide)) covers_nil)

end VG.Proof.AesGcmSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86_64.Derive`. -/
section

/-!
# AES-GCM-SIV on x86-64: the message keys (`derive`)

Untrusted: everything here is checked by Lean. Each step of `derive` writes
`little_endian_uint32(i) ‖ nonce` at `W + 112` and a zero block at
`W + 128` (`derArgs_ok`), on which `vg_aes_ctr32` leaves
`CIPH_K(little_endian_uint32(i) ‖ nonce)`, of which the first 8 bytes are
kept at `W + 16 + 8 i`: after the loop, the halves of `derive_keys`
(`derive_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (CtrCall CtrPost ctr_call GcmImpl in_off ofNat_add_ofNat)

/-- The arguments of a step: the counter block and a zero block. -/
theorem derArgs_ok {K W SP : Addr} {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
    (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n t.mem) (hN : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t N 12) {i : Nat} (hbx : t.gpr .rbx = BitVec.ofNat 64 i) :
    ∃ t₁ : State, runBlock isa (deriveBlock ++ ([.mov .rdi (.reg .r13)] : List Instr) ++ ctrArgs ++ ptr .rcx .r15 bO) t = some t₁ ∧
      t₁.mem = ((Proof.Cmac.store4 t.mem (W + BitVec.ofNat 64 112) ((BitVec.ofNat 64 i).setWidth 32)
          (t.mem.readW N 32) (t.mem.readW (N + BitVec.ofNat 64 4) 32) (t.mem.readW (N + BitVec.ofNat 64 8) 32)).writeW
          (W + BitVec.ofNat 64 128) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 136) (0 : BitVec 64) ∧
      t₁.gpr .rdi = K ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧ t₁.gpr .rdx = W + BitVec.ofNat 64 112 ∧
      t₁.gpr .rcx = W + BitVec.ofNat 64 128 ∧ t₁.gpr .r8 = BitVec.ofNat 64 1 ∧ t₁.gpr .r9 = W + BitVec.ofNat 64 1768 ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r15, .rsp], t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have rN := S.nonce
  have rR := S.rounds
  have n₀ := in_off (d := 0) (n := 4) hN.rd (by decide) (by decide)
  have n₄ := in_off (d := 4) (n := 4) hN.rd (by decide) (by decide)
  have n₈ := in_off (d := 8) (n := 4) hN.rd (by decide) (by decide)
  simp only [BitVec.add_zero] at n₀
  have rS := E.perm.wR (show 208 + 8 ≤ 3816 by decide)
  have rR' := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  have w₁ := E.perm.wW (show 112 + 4 ≤ 3816 by decide)
  have w₂ := E.perm.wW (show 116 + 4 ≤ 3816 by decide)
  have w₃ := E.perm.wW (show 120 + 4 ≤ 3816 by decide)
  have w₄ := E.perm.wW (show 124 + 4 ≤ 3816 by decide)
  have w₅ := E.perm.wW (show 128 + 8 ≤ 3816 by decide)
  have w₆ := E.perm.wW (show 136 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [deriveBlock, zero16, ctrArgs, h15, rN, rR, n₀, n₄, n₈, rS, rR', w₁, w₂, w₃, w₄, w₅, w₆, hbx], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, E.r13]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · rfl
  · rfl
  simp only [mem_setReg, mem_arithFlags, Proof.Cmac.store4, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx]
  rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc]
  simp only [Nat.reduceAdd, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq]
  rfl

/-- The counter block of a step: `little_endian_uint32(i) ‖ nonce`. -/
theorem derBlock_bytes {W : Addr} (_hw : W.toNat + 3816 ≤ 2 ^ 64) (m : Mem) (N : Addr) (i : Nat) :
    bytesAt (((Proof.Cmac.store4 m (W + BitVec.ofNat 64 112) ((BitVec.ofNat 64 i).setWidth 32)
          (m.readW N 32) (m.readW (N + BitVec.ofNat 64 4) 32) (m.readW (N + BitVec.ofNat 64 8) 32)).writeW
          (W + BitVec.ofNat 64 128) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 136) (0 : BitVec 64))
        (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt m N 12 := by
  have c₁ : (⟨W + BitVec.ofNat 64 128, 16⟩ : Region).Contains (W + BitVec.ofNat 64 128) (64 / 8) :=
    Offset.contains W (d := 128) (n := 8) (e := 128) (k := 16) (by decide) (by decide) (by omega)
  have c₂ : (⟨W + BitVec.ofNat 64 128, 16⟩ : Region).Contains (W + BitVec.ofNat 64 136) (64 / 8) :=
    Offset.contains W (d := 136) (n := 8) (e := 128) (k := 16) (by decide) (by decide) (by omega)
  rw [Proof.AesGcm.X86_64.bytesAt_frame
      (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by omega) (by omega)) (by decide),
    Proof.Cmac.bytesAt_store4, GcmSiv.le4_le32, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    show (12 : Nat) = 4 + (4 + 4) from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc]
  simp only [List.append_assoc]

/-- The zero block of a step. -/
theorem derZero_block {W : Addr} (X : Mem) :
    Spec.Gcm.blockAt ((X.writeW (W + BitVec.ofNat 64 128) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 136)
      (0 : BitVec 64)) (W + BitVec.ofNat 64 128) = 0 := by
  rw [Spec.Gcm.blockAt, show W + BitVec.ofNat 64 136 = W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8 by
    rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc], Proof.Cmac.bytesAt_store2]
  decide

/-- What `derive` writes. -/
abbrev derR (W SP : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 48⟩, ⟨W + BitVec.ofNat 64 112, 32⟩, ⟨W + BitVec.ofNat 64 1768, 2048⟩, below SP 8]

theorem derR_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.derR W SP, ∃ r' ∈ VG.Proof.AesGcmSiv.X86_64.mutR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨VG.Proof.AesGcmSiv.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨VG.Proof.AesGcmSiv.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨VG.Proof.AesGcmSiv.X86_64.wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- After `i` steps of `derive` from `σ`: the first `8 i` bytes of the halves
at `W + 16`. -/
structure DInv (K W SP : Addr) (σ : State) (R : Nat) (N : Addr) (cnt i : Nat) (t : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  rbx : t.gpr .rbx = BitVec.ofNat 64 i
  rbp : t.gpr .rbp = BitVec.ofNat 64 cnt
  r12 : t.gpr .r12 = W + BitVec.ofNat 64 (16 + 8 * i)
  le : i ≤ cnt
  frame : Frame (VG.Proof.AesGcmSiv.X86_64.derR W SP) σ.mem t.mem
  out : bytesAt t.mem (W + BitVec.ofNat 64 16) (8 * i) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem K R) (bytesAt σ.mem N 12) i

/-- The code after the call of a step. -/
abbrev derPost : List Instr :=
  [.mov .rax (.mem (at_ .r15 bO)), .store (at_ .r12 0) .rax, .alu .add .r12 (imm 8), .alu .add .rbx (imm 1),
    .alu .cmp .rbx (.reg .rbp)]

theorem derPost_ok {K W SP : Addr} {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {i cnt : Nat} (hi : i < cnt) (hc : cnt ≤ 6)
    (hbx : t.gpr .rbx = BitVec.ofNat 64 i) (hbp : t.gpr .rbp = BitVec.ofNat 64 cnt)
    (h12 : t.gpr .r12 = W + BitVec.ofNat 64 (16 + 8 * i)) :
    ∃ t' : State, runBlock isa VG.Proof.AesGcmSiv.X86_64.derPost t = some t' ∧
      t'.mem = t.mem.writeW (W + BitVec.ofNat 64 (16 + 8 * i)) (t.mem.readW (W + BitVec.ofNat 64 128) 64) ∧
      t'.gpr .rbx = BitVec.ofNat 64 (i + 1) ∧ t'.gpr .rbp = BitVec.ofNat 64 cnt ∧
      t'.gpr .r12 = W + BitVec.ofNat 64 (16 + 8 * (i + 1)) ∧ t'.zf = some (decide (i + 1 = cnt)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have rb := E.perm.wR (show 128 + 8 ≤ 3816 by decide)
  have wo := E.perm.wW (d := 16 + 8 * i) (n := 8) (by omega)
  refine ⟨_, by srun [VG.Proof.AesGcmSiv.X86_64.derPost, h15, h12, rb, wo], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx, ofNat_add_ofNat]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h12, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc]
    rw [show 16 + 8 * i + 8 = 16 + 8 * (i + 1) by omega]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx, hbp,
      ofNat_add_ofNat, Proof.AesGcm.X86_64.sub_beq (show i + 1 < 2 ^ 64 by omega) (show cnt < 2 ^ 64 by omega)]
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- Buffers outside `W` and the stack below `SP` are kept by `derive`. -/
theorem buf_derR {K W SP : Addr} {s : State} {P : Addr} {len : Nat} (hP : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s P len) {m m' : Mem}
    (hf : Frame (VG.Proof.AesGcmSiv.X86_64.derR W SP) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

/-- The key schedule is kept by `derive`. -/
theorem ciph_derR {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {m m' : Mem}
    (hf : Frame (VG.Proof.AesGcmSiv.X86_64.derR W SP) m m') : Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R :=
  VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.k_w' (by decide)
    · exact L.k_w' (by decide)
    · exact L.k_w' (by decide)
    · exact L.stk_k.symm) (by rcases hR with h | h <;> subst h <;> decide)

/-- A step of `derive`. -/
theorem derStep_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} {σ : State} (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n σ.mem) (hN : VG.Proof.AesGcmSiv.X86_64.Buf K W SP σ N 12)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) {cnt i : Nat} (hc : cnt ≤ 6) (hi : i < cnt) {t : State}
    (I : VG.Proof.AesGcmSiv.X86_64.DInv K W SP σ R N cnt i t) :
    WP isa (.seq (.block (deriveBlock ++ ([.mov .rdi (.reg .r13)] : List Instr) ++ ctrArgs ++ ptr .rcx .r15 bO))
      (.seq (callCtr v.callees) (.block VG.Proof.AesGcmSiv.X86_64.derPost))) t fun t' =>
      VG.Proof.AesGcmSiv.X86_64.DInv K W SP σ R N cnt (i + 1) t' ∧ t'.zf = some (decide (i + 1 = cnt)) := by
  have St := VG.Proof.AesGcmSiv.X86_64.slots_mut L hDW (I.frame.sub (VG.Proof.AesGcmSiv.X86_64.derR_mut W SP D n)) S
  have eN : bytesAt t.mem N 12 = bytesAt σ.mem N 12 := VG.Proof.AesGcmSiv.X86_64.buf_derR hN I.frame
  have eK : Spec.GcmSiv.ctxCiph t.mem K R = Spec.GcmSiv.ctxCiph σ.mem K R := VG.Proof.AesGcmSiv.X86_64.ciph_derR L hR I.frame
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ :=
    VG.Proof.AesGcmSiv.X86_64.derArgs_ok I.env St (hN.of_eq I.rd I.wr) I.rbx
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := I.env.keep (fun r hr => hg₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
    hrd₁ hwr₁
  have cc : CtrCall t₁ K (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 128) (W + BitVec.ofNat 64 1768) R 1 :=
    VG.Proof.AesGcmSiv.X86_64.cargs L E₁ hR (VG.Proof.AesGcmSiv.X86_64.keyK L E₁.perm) (c := 112) (by decide) (VG.Proof.AesGcmSiv.X86_64.srcW L E₁.perm (t := 128) (k := 16 * 1) (by decide))
      (L.w_w (.inr (by decide)) (by decide) (by decide)) (L.k_w' (by decide)) (E₁.perm.wC (by decide))
      rdi rsi rdx rcx r8 r9
  -- The bytes the call is given.
  have hb₁ : bytesAt t₁.mem (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt t.mem N 12 := by
    rw [hm₁]; exact VG.Proof.AesGcmSiv.X86_64.derBlock_bytes L.ww _ _ _
  have hz₁ : Spec.Gcm.blockAt t₁.mem (W + BitVec.ofNat 64 128) = 0 := by rw [hm₁]; exact VG.Proof.AesGcmSiv.X86_64.derZero_block _
  have f₁ : Frame [⟨W + BitVec.ofNat 64 112, 32⟩] t.mem t₁.mem := by
    rw [hm₁]
    exact ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 128) (n := 8) (e := 112) (k := 32) (by decide)
        (by decide) (by have := L.ww; omega)) |>.writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 136) (n := 8) (e := 112) (k := 32) (by decide)
        (by decide) (by have := L.ww; omega))
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_)
  have E₂ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₂ := E₁.of_saved P.saved P.rd P.wr
  have g₂ : ∀ r ∈ [Reg.rbx, .rbp, .r12], t₂.gpr r = t.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [P.saved _ (by decide), hg₁ _ (by simp)]
  obtain ⟨t₃, run₃, hm₃, bx₃, bp₃, r12₃, zf₃, hg₃, hrd₃, hwr₃⟩ :=
    VG.Proof.AesGcmSiv.X86_64.derPost_ok E₂ hi hc (by rw [g₂ _ (by simp), I.rbx]) (by rw [g₂ _ (by simp), I.rbp])
      (by rw [g₂ _ (by simp), I.r12])
  refine WP.of_runBlock ⟨t₃, run₃, ⟨E₂.keep hg₃ hrd₃ hwr₃, by rw [hrd₃, P.rd, hrd₁, I.rd],
    by rw [hwr₃, P.wr, hwr₁, I.wr], bx₃, bp₃, r12₃, by omega, ?_, ?_⟩, zf₃⟩
  · -- The frame.
    have fc := P.frame
    rw [E₁.rsp] at fc
    refine (I.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self), by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)).trans
      ((fc.sub fun r hr => ?_).trans (by
        rw [hm₃]
        exact (Frame.refl _ _).writeW (List.mem_cons_self) _ (Offset.contains W (d := 16 + 8 * i) (n := 8)
          (e := 16) (k := 48) (by omega) (by omega) (by have := L.ww; omega))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · -- The bytes.
    have fc := P.frame
    rw [E₁.rsp] at fc
    have dW : ∀ {d k : Nat}, d + k ≤ 3816 → 16 + 8 * i ≤ d →
        (⟨W + BitVec.ofNat 64 16, 8 * i⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ h₂ => L.w_w (.inl (by omega)) (by omega) h₁
    have keep : bytesAt t₃.mem (W + BitVec.ofNat 64 16) (8 * i) = bytesAt t.mem (W + BitVec.ofNat 64 16) (8 * i) := by
      rw [hm₃, Proof.AesGcm.X86_64.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Region.contains_self (W + BitVec.ofNat 64 (16 + 8 * i)) 8))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW (by omega) (by omega)) (by omega),
        Proof.AesGcm.X86_64.bytesAt_frame fc (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact dW (by decide) (by omega)
          · exact dW (by decide) (by omega)
          · exact dW (by decide) (by omega)
          · exact (L.stk_w' (by omega)).symm) (by omega),
        Proof.AesGcm.X86_64.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dW (by decide) (by omega)) (by omega)]
    have hout := P.out
    simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
    have last : bytesAt t₃.mem (W + BitVec.ofNat 64 (16 + 8 * i)) 8 =
        (Spec.GcmSiv.ctxCiph σ.mem K R (Spec.GcmSiv.le32 i ++ bytesAt σ.mem N 12)).take 8 := by
      have e16 : bytesAt t₂.mem (W + BitVec.ofNat 64 128) 16 =
          bytesAt t₂.mem (W + BitVec.ofNat 64 128) 8 ++ bytesAt t₂.mem (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8) 8 :=
        Proof.Cmac.bytesAt_add _ _ 8 8
      have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem K R = Spec.GcmSiv.ctxCiph t.mem K R :=
        VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.k_w' (by decide))
          (by rcases hR with h | h <;> subst h <;> decide)
      rw [hm₃, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_readW,
        show bytesAt t₂.mem (W + BitVec.ofNat 64 128) 8 = (bytesAt t₂.mem (W + BitVec.ofNat 64 128) 16).take 8 by
          rw [e16, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)],
        Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt, hb₁,
        Proof.Cmac.aesWith_bytes _ _ (by rw [List.length_append, Proof.Cmac.bytesAt_length]; rfl),
        ← GcmSiv.aesWith_eq, show Spec.GcmSiv.aesWith R (bytesAt t₁.mem K (16 * (R + 1))) =
          Spec.GcmSiv.ctxCiph t₁.mem K R from rfl, ek₁, eK, eN]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, Proof.Cmac.bytesAt_add, GcmSiv.halves_succ, ← I.out, keep,
      VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, last]

theorem shr1 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 1 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- The start of `derive`: no block yet, and the number of blocks,
`rounds / 2 − 1`. -/
theorem derInit_ok {K W SP : Addr} {σ : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP σ) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n σ.mem) :
    WP isa (.block (([.mov32 .rbx (imm 0)] : List Instr) ++ ptr .r12 .r15 akO ++
      ([.mov .rbp (.mem (at_ .r15 roundsO)), .shift .shr .rbp 1, .alu .sub .rbp (imm 1)] : List Instr))) σ
      (VG.Proof.AesGcmSiv.X86_64.DInv K W SP σ R N (R / 2 - 1) 0) := by
  have h15 := E.r15
  have rR := S.rounds
  have rr := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  obtain ⟨t, run, hm, bx, bp, h12, hg, hrd, hwr⟩ : ∃ t : State, runBlock isa ([.mov32 .rbx (imm 0)] ++ ptr .r12 .r15 akO ++
      [.mov .rbp (.mem (at_ .r15 roundsO)), .shift .shr .rbp 1, .alu .sub .rbp (imm 1)]) σ = some t ∧
      t.mem = σ.mem ∧ t.gpr .rbx = BitVec.ofNat 64 0 ∧ t.gpr .rbp = BitVec.ofNat 64 (R / 2 - 1) ∧
      t.gpr .r12 = W + BitVec.ofNat 64 16 ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], t.gpr r = σ.gpr r) ∧
      t.rd = σ.rd ∧ t.wr = σ.wr := by
    refine ⟨_, by srun [h15, rR, rr], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, execShift]
      rw [VG.Proof.AesGcmSiv.X86_64.shr1 R (by omega), Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h15]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  exact WP.of_runBlock ⟨t, run, E.keep hg hrd hwr, hrd, hwr, bx, bp, by rw [h12], Nat.zero_le _,
    by rw [hm]; exact Frame.refl _ _, rfl⟩

/-- `derive`: the halves of `derive_keys` at `W + 16`. -/
theorem derive_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} {σ : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP σ) (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n σ.mem)
    (hN : VG.Proof.AesGcmSiv.X86_64.Buf K W SP σ N 12) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) :
    WP isa (derive v.callees) σ (VG.Proof.AesGcmSiv.X86_64.DInv K W SP σ R N (R / 2 - 1) (R / 2 - 1)) := by
  have hc : R / 2 - 1 ≤ 6 := by omega
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.derInit_ok E hR S) fun t I₀ => ?_)
  refine WP.loop (M := isa) (fun m t => ∃ i, m = (R / 2 - 1) - i ∧ i < R / 2 - 1 ∧
    VG.Proof.AesGcmSiv.X86_64.DInv K W SP σ R N (R / 2 - 1) i t) ?_ ((R / 2 - 1) - 0) t ⟨0, rfl, by omega, I₀⟩
  rintro m t ⟨i, rfl, hi, I⟩
  refine WP.mono (VG.Proof.AesGcmSiv.X86_64.derStep_ok v L hR S hN hDW hc hi I) fun t' ⟨I', hz⟩ => ?_
  by_cases he : i + 1 = R / 2 - 1
  · left; exact ⟨(VG.Proof.AesGcmSiv.X86_64.eval_ne hz).trans (by simp [he]), he ▸ I'⟩
  · right; exact ⟨(VG.Proof.AesGcmSiv.X86_64.eval_ne hz).trans (by simp [he]), (R / 2 - 1) - (i + 1), by omega, i + 1, rfl, by omega, I'⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DInv.keys {K W SP : Addr} {σ : State} {R : Nat} (hR : R = 10 ∨ R = 14) {N : Addr} {t : State}
    (I : VG.Proof.AesGcmSiv.X86_64.DInv K W SP σ R N (R / 2 - 1) (R / 2 - 1) t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12) =
      (bytesAt t.mem (W + BitVec.ofNat 64 16) 16, bytesAt t.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R)) := by
  have hk : Spec.GcmSiv.keyLen R / 8 + 2 = R / 2 - 1 := by unfold Spec.GcmSiv.keyLen; omega
  have hl : 8 * (R / 2 - 1) = 16 + Spec.GcmSiv.keyLen R := by unfold Spec.GcmSiv.keyLen; omega
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem K R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesGcmSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys`. -/
section

/-!
# AES-GCM-SIV on x86-64: the encryption key's schedule and GHASH's key

Untrusted: everything here is checked by Lean. `expand` writes the schedule
of the encryption key at `W + 248` (`expand_ok`), and `hkey` GHASH's key,
`H · x` for the authentication key `H` (POLYVAL's field element), in
GHASH's order at `W + 64`, and zeroes its accumulator (`hkey_ok`): the
shift of `hi ++ lo` by one bit to the right, and `R` added when the bit
shifted out is set (`mulXG_words`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Polyval (mulXG)
open VG.Proof.AesGcm.X86_64 (GcmImpl key_call ofNat_add_ofNat)

theorem and1 (x : BitVec 64) : x &&& 1#64 = if x.getLsbD 0 then 1#64 else 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod]
  cases h : x.getLsbD 0
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_zero]
    simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two] at h
    revert h; cases Nat.mod_two_eq_zero_or_one x.toNat <;> simp_all
  · simp only [↓reduceIte, show (1#64).toNat = 1 from rfl]
    simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two] at h
    revert h; cases Nat.mod_two_eq_zero_or_one x.toNat <;> simp_all

theorem appLo (a b : BitVec 64) {j : Nat} (h : j < 64) : (a ++ b).getLsbD j = b.getLsbD j := by
  rw [BitVec.getLsbD_append]; simp [h]

theorem appHi (a b : BitVec 64) {j : Nat} (h : 64 ≤ j) : (a ++ b).getLsbD j = a.getLsbD (j - 64) := by
  rw [BitVec.getLsbD_append]; simp [show ¬ j < 64 by omega]

/-- `mulXG` on the halves of a block, for any words `M` and `C` with the bits
of the carry into the low half and of `R` in the high half. -/
theorem mulXG_core (hi lo : BitVec 64) (M C : BitVec 64)
    (hM : ∀ i < 64, M.getLsbD i = (decide (i = 63) && hi.getLsbD 0))
    (hC : ∀ i < 64, C.getLsbD i = (Spec.Gcm.R.getLsbD (i + 64) && lo.getLsbD 0))
    (hR : ∀ i < 64, Spec.Gcm.R.getLsbD i = false) :
    ((hi >>> 1) ^^^ C) ++ ((lo >>> 1) ||| M) = mulXG (hi ++ lo) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi128
  unfold mulXG; rw [VG.Proof.AesGcmSiv.X86_64.appLo hi lo (by decide)]
  by_cases h64 : i < 64
  · rw [VG.Proof.AesGcmSiv.X86_64.appLo _ _ h64, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, hM i h64]
    by_cases h63 : i = 63
    · subst h63
      have e : lo.getLsbD (1 + 63) = false := BitVec.getLsbD_of_ge lo _ (by decide)
      rw [e]
      cases hl : lo.getLsbD 0 <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.getLsbD_xor,
        BitVec.getLsbD_ushiftRight, VG.Proof.AesGcmSiv.X86_64.appHi hi lo (show 64 ≤ 1 + 63 by decide), hR 63 (by decide)] <;> simp
    · have e : (hi ++ lo).getLsbD (1 + i) = lo.getLsbD (1 + i) := VG.Proof.AesGcmSiv.X86_64.appLo hi lo (by omega)
      cases hl : lo.getLsbD 0 <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.getLsbD_xor,
        BitVec.getLsbD_ushiftRight, e, hR i h64, decide_eq_false h63] <;> simp
  · rw [VG.Proof.AesGcmSiv.X86_64.appHi _ _ (by omega), BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, hC (i - 64) (by omega),
      show i - 64 + 64 = i by omega]
    have e : (hi ++ lo).getLsbD (1 + i) = hi.getLsbD (1 + (i - 64)) := by
      rw [VG.Proof.AesGcmSiv.X86_64.appHi hi lo (by omega)]; congr 1; omega
    cases hl : lo.getLsbD 0 <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.getLsbD_xor,
      BitVec.getLsbD_ushiftRight, e] <;> simp

/-- GHASH's product with `x`, as `hkey` computes it on the halves of a block. -/
theorem mulXG_words (hi lo : BitVec 64) :
    ((hi >>> 1) ^^^ (0xE100000000000000#64 &&& (0#64 - (lo &&& 1#64)))) ++
      ((lo >>> 1) ||| (hi &&& 1#64).rotateRight 1) = mulXG (hi ++ lo) := by
  have hR : ∀ i < 64, Spec.Gcm.R.getLsbD i = false := by decide +kernel
  have hR' : ∀ i < 64, (0xE100000000000000#64 : BitVec 64).getLsbD i = Spec.Gcm.R.getLsbD (i + 64) := by
    decide +kernel
  have h1 : ∀ i < 64, (0x8000000000000000#64 : BitVec 64).getLsbD i = decide (i = 63) := by decide +kernel
  refine VG.Proof.AesGcmSiv.X86_64.mulXG_core hi lo _ _ (fun i hi64 => ?_) (fun i hi64 => ?_) hR
  · rw [VG.Proof.AesGcmSiv.X86_64.and1 hi]; cases h : hi.getLsbD 0 <;> simp [h1 i hi64]
  · rw [VG.Proof.AesGcmSiv.X86_64.and1 lo]; cases h : lo.getLsbD 0 <;> simp [hR' i hi64]

/-- Two words stored at `p` and `p + 8`, read as a block in GHASH's order. -/
theorem blockAt_two (m : Mem) (p : Addr) (x y : BitVec 64) :
    Spec.Gcm.blockAt ((m.writeW p (bswap64 x)).writeW (p + BitVec.ofNat 64 8) (bswap64 y)) p = x ++ y := by
  have hs : Mem.Sep p (64 / 8) (p + BitVec.ofNat 64 8) (64 / 8) := by
    simpa using Offset.sep p (d := 0) (n := 8) (e := 8) (k := 8) (.inl (by decide)) (by decide) (by decide)
  rw [← Proof.Gcm.X86_64.blockAt_bswap, Mem.readW_writeW_self64, BitVec.add_zero, Mem.readW_writeW_sep hs (by decide),
    Mem.readW_writeW_self64, Proof.Gcm.X86_64.bswap64_bswap64, Proof.Gcm.X86_64.bswap64_bswap64]

/-- The block at `W + 64`, after the accumulator at `W + 80` is zeroed. -/
theorem blockAt_zero_after (W : Addr) (m : Mem) :
    Spec.Gcm.blockAt ((m.writeW (W + BitVec.ofNat 64 80) (0#64)).writeW (W + BitVec.ofNat 64 88) (0#64))
      (W + BitVec.ofNat 64 64) = Spec.Gcm.blockAt m (W + BitVec.ofNat 64 64) := by
  have c₁ : (⟨W + BitVec.ofNat 64 80, 16⟩ : Region).Contains (W + BitVec.ofNat 64 80) (64 / 8) :=
    Offset.contains W (d := 80) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide)
  have c₂ : (⟨W + BitVec.ofNat 64 80, 16⟩ : Region).Contains (W + BitVec.ofNat 64 88) (64 / 8) :=
    Offset.contains W (d := 88) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide)
  exact Proof.AesGcm.X86_64.blockAt_frame
    (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide))

/-- Four words written at `W + 64`, …, `W + 88`. -/
theorem frame4 (W : Addr) (m : Mem) (a b c d : BitVec 64) :
    Frame [⟨W + BitVec.ofNat 64 64, 32⟩] m ((((m.writeW (W + BitVec.ofNat 64 64) a).writeW (W + BitVec.ofNat 64 72) b).writeW
      (W + BitVec.ofNat 64 80) c).writeW (W + BitVec.ofNat 64 88) d) := by
  have ct : ∀ e, 64 ≤ e → e + 8 ≤ 96 → (⟨W + BitVec.ofNat 64 64, 32⟩ : Region).Contains (W + BitVec.ofNat 64 e) (64 / 8) :=
    fun e h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 64 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (ct 72 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (ct 80 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (ct 88 (by decide) (by decide))

/-- `hkey`: GHASH's key at `W + 64` and its accumulator zeroed at `W + 80`. -/
theorem hkey_ok {K W SP : Addr} {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) :
    ∃ t' : State, runBlock isa hkey t = some t' ∧
      Spec.Gcm.blockAt t'.mem (W + BitVec.ofNat 64 64) =
        mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)) ∧
      Spec.Gcm.blockAt t'.mem (W + BitVec.ofNat 64 80) = 0 ∧
      Frame [⟨W + BitVec.ofNat 64 64, 32⟩] t.mem t'.mem ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 16 + 8 ≤ 3816 by decide)
  have r₂ := E.perm.wR (show 24 + 8 ≤ 3816 by decide)
  have w₁ := E.perm.wW (show 64 + 8 ≤ 3816 by decide)
  have w₂ := E.perm.wW (show 72 + 8 ≤ 3816 by decide)
  have w₃ := E.perm.wW (show 80 + 8 ≤ 3816 by decide)
  have w₄ := E.perm.wW (show 88 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [hkey, zero16, h15, r₁, r₂, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      ite_false, reduceCtorEq]
    rw [VG.Proof.AesGcmSiv.X86_64.blockAt_zero_after W, show W + BitVec.ofNat 64 72 = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 by
      rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc], VG.Proof.AesGcmSiv.X86_64.blockAt_two, GcmSiv.ofBytes_bytesAt, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, ← VG.Proof.AesGcmSiv.X86_64.mulXG_words]
    rfl
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    rw [show W + BitVec.ofNat 64 88 = W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8 by rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc],
      Spec.Gcm.blockAt, Proof.Cmac.bytesAt_store2]
    decide
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    exact VG.Proof.AesGcmSiv.X86_64.frame4 W _ _ _ _ _
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- What `expand` leaves: the schedule of the encryption key at `W + 248`. -/
structure ExpPost (K W SP : Addr) (R : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  saved : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r
  frame : Frame [⟨W + BitVec.ofNat 64 248, 240⟩, ⟨W + BitVec.ofNat 64 1768, 512⟩, below SP 8] t.mem t'.mem
  ciph : Spec.GcmSiv.ctxCiph t'.mem (W + BitVec.ofNat 64 248) R =
    Spec.GcmSiv.aes (bytesAt t.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R))

/-- The arguments of `expand`'s call. -/
theorem expArgs_ok {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat} {t : State}
    (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n t.mem) :
    ∃ t₁ : State, runBlock isa
      (ptr .rdi .r15 ekO ++ ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6), .alu .add .rsi (.reg .rsi),
        .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO ++ ptr .rcx .r15 scrO) t = some t₁ ∧
      t₁.mem = t.mem ∧ t₁.gpr .rdi = W + BitVec.ofNat 64 32 ∧
      t₁.gpr .rsi = BitVec.ofNat 64 (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rdx = W + BitVec.ofNat 64 248 ∧
      t₁.gpr .rcx = W + BitVec.ofNat 64 1768 ∧ (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have rR := S.rounds
  have rr := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [h15, rR, rr], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    rw [Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega), ofNat_add_ofNat, ofNat_add_ofNat]
    congr 1; unfold Spec.GcmSiv.keyLen; omega
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

theorem expand_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n t.mem) :
    WP isa (expand v.callees) t (VG.Proof.AesGcmSiv.X86_64.ExpPost K W SP R t) := by
  have h15 := E.r15
  have rR := S.rounds
  have rr := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  have hl : Spec.GcmSiv.keyLen R = 16 ∨ Spec.GcmSiv.keyLen R = 32 := by unfold Spec.GcmSiv.keyLen; omega
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, rcx, hg₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcmSiv.X86_64.expArgs_ok hR E S
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := E.of_saved hg₁ hrd₁ hwr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (key_call v.key (VG.Proof.AesGcmSiv.X86_64.kargs L E₁ hl rdi rsi rdx rcx)) fun t₂ P => ?_
  have fc := P.frame
  rw [E₁.rsp] at fc
  refine ⟨E₁.of_saved P.saved P.rd P.wr, by rw [P.rd, hrd₁], by rw [P.wr, hwr₁],
    fun r hr => by rw [P.saved r hr, hg₁ r hr], by rw [← hm₁]; exact fc, ?_⟩
  have hr : Spec.Aes.rounds (Spec.GcmSiv.keyLen R / 4) = R := by
    unfold Spec.Aes.rounds Spec.GcmSiv.keyLen; omega
  have out := P.out
  rw [hr] at out
  rw [Spec.GcmSiv.ctxCiph, out, Spec.GcmSiv.aes, Proof.Cmac.bytesAt_length, hr, hm₁]

end VG.Proof.AesGcmSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86_64.Absorb`. -/
section

/-!
# AES-GCM-SIV on x86-64: POLYVAL (`absorb`)

Untrusted: everything here is checked by Lean. POLYVAL is GHASH with the
key `H · x` on the same bits (`Proof.GcmSiv.Polyval`): `revLoop` copies up to
64 blocks to `W + 488` with the bytes of each reversed, so that GHASH reads
each copy as POLYVAL reads the original (`revLoop_ok`), and `vg_ghash`
absorbs them; `absorb` absorbs the padded string so (`absorb_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.AesGcm.X86_64 (GcmImpl GhCall GhPost gh_call ofNat_add_ofNat in_off toNat_ofNat_of_lt)

/-- The body of `revLoop`. -/
abbrev revBody : List Instr :=
  [.mov .rax (.mem (at_ .rsi 0)), .mov .rdx (.mem (at_ .rsi 8)), .bswap .rax, .bswap .rdx,
    .store (at_ .rdi 0) .rdx, .store (at_ .rdi 8) .rax, .alu .add .rsi (imm 16), .alu .add .rdi (imm 16),
    .alu .sub .rcx (imm 1)]

theorem revStep_ok {t : State} {S P : Addr} {j : Nat} (hj : j < 2 ^ 63)
    (hsi : t.gpr .rsi = S) (hdi : t.gpr .rdi = P) (hcx : t.gpr .rcx = BitVec.ofNat 64 (j + 1))
    (hr₀ : InRegions (t.rd ++ t.wr) S 8) (hr₈ : InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 8) 8)
    (hw₀ : InRegions t.wr P 8) (hw₈ : InRegions t.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ t' : State, runBlock isa VG.Proof.AesGcmSiv.X86_64.revBody t = some t' ∧
      t'.mem = (t.mem.writeW P (bswap64 (t.mem.readW (S + BitVec.ofNat 64 8) 64))).writeW (P + BitVec.ofNat 64 8)
        (bswap64 (t.mem.readW S 64)) ∧
      t'.gpr .rsi = S + BitVec.ofNat 64 16 ∧ t'.gpr .rdi = P + BitVec.ofNat 64 16 ∧
      t'.gpr .rcx = BitVec.ofNat 64 j ∧ t'.zf = some (decide (j = 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → t'.gpr r = t.gpr r) ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by srun [hsi, hdi, hr₀, hr₈, hw₀, hw₈], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hdi]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hsi]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hdi]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hcx]
    rw [Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]; rfl
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hcx,
      Proof.AesGcm.X86_64.sub_beq (show j + 1 < 2 ^ 64 by omega) (show 1 < 2 ^ 64 by decide)]
    simp
  · intro r h₁ h₂ h₃ h₄ h₅; simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, h₄, h₅, ite_false]
  all_goals rfl

theorem blocksAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Gcm.blocksAt m p (j + 1) = Spec.Gcm.blocksAt m p j ++ [Spec.Gcm.blockAt m (p + BitVec.ofNat 64 (16 * j))] := by
  simp [Spec.Gcm.blocksAt, List.range_succ]

/-- What `revLoop` leaves after `j` blocks, from `t₀`. -/
structure RInv (W : Addr) (Q : Addr) (c j : Nat) (t₀ t : State) : Prop where
  rsi : t.gpr .rsi = Q + BitVec.ofNat 64 (16 * j)
  rdi : t.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * j)
  rcx : t.gpr .rcx = BitVec.ofNat 64 (c - j)
  frame : Frame [⟨W + BitVec.ofNat 64 488, 16 * c⟩] t₀.mem t.mem
  out : Spec.Gcm.blocksAt t.mem (W + BitVec.ofNat 64 488) j =
    (List.range j).map fun k => Spec.GcmSiv.ofBytes (bytesAt t₀.mem (Q + BitVec.ofNat 64 (16 * k)) 16)
  regs : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → t.gpr r = t₀.gpr r
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr

/-- `revLoop`: `c` blocks at `Q` copied to `W + 488`, each reversed, so that
GHASH reads POLYVAL's field elements of them. -/
theorem revLoop_ok {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {t₀ : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₀) {Q : Addr} {c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 64) (hQ : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t₀ Q (16 * c)) (h14 : t₀.gpr .r14 = BitVec.ofNat 64 c)
    (hsi : t₀.gpr .rsi = Q) (hdi : t₀.gpr .rdi = W + BitVec.ofNat 64 488) :
    WP isa revLoop t₀ fun t => Frame [⟨W + BitVec.ofNat 64 488, 16 * c⟩] t₀.mem t.mem ∧
      Spec.Gcm.blocksAt t.mem (W + BitVec.ofNat 64 488) c =
        (List.range c).map (fun k => Spec.GcmSiv.ofBytes (bytesAt t₀.mem (Q + BitVec.ofNat 64 (16 * k)) 16)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → t.gpr r = t₀.gpr r) ∧
      t.rd = t₀.rd ∧ t.wr = t₀.wr := by
  obtain ⟨t₁, run₁, hcx₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa [.mov .rcx (.reg .r14)] t₀ = some t₁ ∧
      t₁.gpr .rcx = BitVec.ofNat 64 c ∧ (∀ r, r ≠ .rcx → t₁.gpr r = t₀.gpr r) ∧ t₁.mem = t₀.mem ∧
      t₁.rd = t₀.rd ∧ t₁.wr = t₀.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, h14]
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have I₀ : VG.Proof.AesGcmSiv.X86_64.RInv W Q c 0 t₀ t₁ := ⟨by rw [hg₁ _ (by decide), hsi, Nat.mul_zero, BitVec.add_zero],
    by rw [hg₁ _ (by decide), hdi], by rw [hcx₁, Nat.sub_zero], by rw [hm₁]; exact Frame.refl _ _,
    by simp only [Spec.Gcm.blocksAt, List.range_zero, List.map_nil],
    fun r _ _ _ _ h => hg₁ r h, hrd₁, hwr₁⟩
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcmSiv.X86_64.revBody) (c := .ne)
    (fun (m : Nat) (t : State) => ∃ j, m = c - j ∧ j < c ∧ VG.Proof.AesGcmSiv.X86_64.RInv W Q c j t₀ t) ?_ (c - 0) t₁ ⟨0, rfl, hc1, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  have hw := L.ww
  have rq₀ := in_off (d := 16 * j) (n := 8) hQ.rd (by omega) hQ.lt
  have rq₈ := in_off (d := 16 * j + 8) (n := 8) hQ.rd (by omega) hQ.lt
  rw [← VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc] at rq₈
  have ww₀ := E.perm.wW (d := 488 + 16 * j) (n := 8) (by omega)
  have ww₈ := E.perm.wW (d := 488 + 16 * j + 8) (n := 8) (by omega)
  rw [← VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc] at ww₈
  rw [← I.rd, ← I.wr] at rq₀ rq₈
  rw [← I.wr] at ww₀ ww₈
  obtain ⟨t', run', hm', si', di', cx', zf', hg', hrd', hwr'⟩ :=
    VG.Proof.AesGcmSiv.X86_64.revStep_ok (j := c - j - 1) (by omega) I.rsi I.rdi (by rw [I.rcx]; congr 1; omega) rq₀ rq₈ ww₀ ww₈
  refine WP.of_runBlock ⟨t', run', ?_⟩
  -- The source is outside the copies.
  have src : ∀ d, d + 8 ≤ 16 * c → t.mem.readW (Q + BitVec.ofNat 64 d) 64 = t₀.mem.readW (Q + BitVec.ofNat 64 d) 64 :=
    fun d hd => I.frame.readW (r := ⟨Q + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hQ.w.sub_left (Offset.sub_base Q (by omega))).sub_right (Lay.wSub (by omega))) (by decide)
  have c₁ : (⟨W + BitVec.ofNat 64 488, 16 * c⟩ : Region).Contains (W + BitVec.ofNat 64 (488 + 16 * j)) (64 / 8) :=
    Offset.contains W (by omega) (by omega) (by omega)
  have c₂ : (⟨W + BitVec.ofNat 64 488, 16 * c⟩ : Region).Contains
      (W + BitVec.ofNat 64 (488 + 16 * j) + BitVec.ofNat 64 8) (64 / 8) := by
    rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc]; exact Offset.contains W (by omega) (by omega) (by omega)
  have I' : VG.Proof.AesGcmSiv.X86_64.RInv W Q c (j + 1) t₀ t' := by
    refine ⟨by rw [si', VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc]; congr 2, by rw [di', VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc]; congr 2, by rw [cx']; congr 1, ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ => by rw [hg' r h₁ h₂ h₃ h₄ h₅, I.regs r h₁ h₂ h₃ h₄ h₅],
      by rw [hrd', I.rd], by rw [hwr', I.wr]⟩
    · rw [hm']
      exact (I.frame.writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂
    · have fr : Frame [⟨W + BitVec.ofNat 64 (488 + 16 * j), 16⟩] t.mem t'.mem := by
        rw [hm']
        have cP0 : (⟨W + BitVec.ofNat 64 (488 + 16 * j), 16⟩ : Region).Contains (W + BitVec.ofNat 64 (488 + 16 * j))
            (64 / 8) := Offset.contains W (Nat.le_refl _) (by omega) (by omega)
        have cP8 : (⟨W + BitVec.ofNat 64 (488 + 16 * j), 16⟩ : Region).Contains
            (W + BitVec.ofNat 64 (488 + 16 * j) + BitVec.ofNat 64 8) (64 / 8) :=
          Offset.contains_base (W + BitVec.ofNat 64 (488 + 16 * j)) (show 8 + 8 ≤ 16 by decide) (by decide)
        exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ cP0).writeW (List.mem_singleton_self _) _ cP8
      have s₈ := src (16 * j + 8) (by omega)
      rw [← VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc] at s₈
      rw [VG.Proof.AesGcmSiv.X86_64.blocksAt_succ, Proof.AesGcm.X86_64.blocksAt_frame fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint W (.inl (by omega)) (by omega) (by omega)) (by omega), I.out, List.range_succ,
        List.map_append, List.map_cons, List.map_nil, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, hm', VG.Proof.AesGcmSiv.X86_64.blockAt_two, GcmSiv.ofBytes_bytesAt,
        src (16 * j) (by omega), s₈]
  by_cases he : j + 1 = c
  · left
    refine ⟨(VG.Proof.AesGcmSiv.X86_64.eval_ne zf').trans (by simp [show c - j - 1 = 0 by omega]), ?_⟩
    exact ⟨I'.frame, he ▸ I'.out, I'.regs, I'.rd, I'.wr⟩
  · right
    exact ⟨(VG.Proof.AesGcmSiv.X86_64.eval_ne zf').trans (by simp [show c - j - 1 ≠ 0 by omega]), c - (j + 1), by omega, j + 1, rfl,
      by omega, I'⟩

/-- What absorbing writes: GHASH's accumulator, the block at `W + 128`, the
reversed blocks, `vg_ghash`'s working space and the stack below `SP`. -/
abbrev absR (W SP : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩,
    ⟨W + BitVec.ofNat 64 1512, 256⟩, below SP 8]

/-- POLYVAL's field elements of the `k` blocks at `Q`. -/
abbrev elemsAt (m : Mem) (Q : Addr) (k : Nat) : List Spec.GcmSiv.Elem :=
  (List.range k).map fun i => Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * i)) 16)

/-- What `absorbChunk` leaves, from `t`, after absorbing `k` of the `b`
blocks at `Q`. -/
structure ChunkPost (K W SP : Addr) (Q : Addr) (b k : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  rbp : t'.gpr .rbp = t.gpr .rbp
  r12 : t'.gpr .r12 = Q + BitVec.ofNat 64 (16 * k)
  rbx : t'.gpr .rbx = BitVec.ofNat 64 (b - k)
  zf : t'.zf = some (decide (b - k = 0))
  frame : Frame (VG.Proof.AesGcmSiv.X86_64.absR W SP) t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80)) (VG.Proof.AesGcmSiv.X86_64.elemsAt t.mem Q k)

/-- `(a; (b; (c; (d; e)))); g`, run as `a; (b; (c; (d; (e; g))))`. -/
theorem WP.assoc5 {a b c d e g : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b (.seq c (.seq d e)))) g) s Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d (.seq e g))))) s Q := by
  obtain ⟨t, s', ex, hq⟩ := h
  cases ex with | seq x y => cases x with | seq xa x => cases x with | seq xb x => cases x with | seq xc x =>
  cases x with | seq xd xe =>
  exact ⟨_, _, .seq xa (.seq xb (.seq xc (.seq xd (.seq xe y)))), hq⟩

/-- A chunk up to its call: up to 64 blocks reversed at `W + 488`, and the
arguments of `vg_ghash`. -/
structure ChunkPre (K W SP : Addr) (Q : Addr) (k : Nat) (t t₅ : State) : Prop where
  call : GhCall t₅ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
    (W + BitVec.ofNat 64 1512) k
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₅
  regs : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r15, .rsp], t₅.gpr r = t.gpr r
  r14 : t₅.gpr .r14 = BitVec.ofNat 64 k
  rd : t₅.rd = t.rd
  wr : t₅.wr = t.wr
  frame : Frame [⟨W + BitVec.ofNat 64 488, 16 * k⟩] t.mem t₅.mem
  out : Spec.Gcm.blocksAt t₅.mem (W + BitVec.ofNat 64 488) k = VG.Proof.AesGcmSiv.X86_64.elemsAt t.mem Q k

theorem chunkPre_ok {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t)
    {Q : Addr} {b : Nat} (hb : 1 ≤ b) (hQ : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t Q (16 * b))
    (h12 : t.gpr .r12 = Q) (hbx : t.gpr .rbx = BitVec.ofNat 64 b) :
    WP isa (.seq (.block [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)])
      (.seq (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block []))
      (.seq (.block (([.mov .rsi (.reg .r12)] : List Instr) ++ ptr .rdi .r15 revO))
      (.seq revLoop (.block (ghArgs ++ ptr .rdx .r15 revO ++ ([.mov .rcx (.reg .r14)] : List Instr))))))) t
      (VG.Proof.AesGcmSiv.X86_64.ChunkPre K W SP Q (min b 64) t) := by
  have hbl : b < 2 ^ 60 := by have := hQ.lt; omega
  have h15 := E.r15
  -- `r14 := min b 64`.
  obtain ⟨t₁, run₁, h14₁, hcf₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State,
      runBlock isa [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)] t = some t₁ ∧
      t₁.gpr .r14 = BitVec.ofNat 64 64 ∧ t₁.cf = some (decide (b < 64)) ∧
      (∀ r, r ≠ .r14 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_arithFlags, gpr_setReg, ite_true]
    · simp only [cf_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbx,
        toNat_ofNat_of_lt (show b < 2 ^ 64 by omega)]
      rfl
    · intro r hr; simp only [gpr_arithFlags, gpr_setReg, hr, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have hite : WP isa (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block [])) t₁ fun t₂ =>
      t₂.gpr .r14 = BitVec.ofNat 64 (min b 64) ∧ (∀ r, r ≠ .r14 → t₂.gpr r = t.gpr r) ∧ t₂.mem = t.mem ∧
      t₂.rd = t.rd ∧ t₂.wr = t.wr := by
    refine WP.ite (decide (b < 64)) (VG.Proof.AesGcmSiv.X86_64.eval_b hcf₁) (fun ht => ?_) (fun hf => ?_)
    · refine WP.of_runBlock ⟨_, by srun [], ?_, fun r hr => ?_, ?_, ?_, ?_⟩
      · simp only [gpr_setReg, ite_true, hg₁ _ (by decide : Reg.rbx ≠ .r14), hbx]
        simp at ht; rw [Nat.min_eq_left (by omega)]
      · simp only [gpr_setReg, hr, ite_false]; exact hg₁ r hr
      · exact hm₁
      · exact hrd₁
      · exact hwr₁
    · refine WP.block_nil ⟨?_, hg₁, hm₁, hrd₁, hwr₁⟩
      simp at hf; rw [h14₁, Nat.min_eq_right (by omega)]
  refine WP.seq (WP.mono hite fun t₂ ⟨h14₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_)
  -- The source and the destination of the copies.
  have h15₂ : t₂.gpr .r15 = W := by rw [hg₂ _ (by decide), h15]
  obtain ⟨t₃, run₃, hsi₃, hdi₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃ : State,
      runBlock isa ([.mov .rsi (.reg .r12)] ++ ptr .rdi .r15 revO) t₂ = some t₃ ∧
      t₃.gpr .rsi = Q ∧ t₃.gpr .rdi = W + BitVec.ofNat 64 488 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdi → t₃.gpr r = t₂.gpr r) ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hg₂ _ (by decide : Reg.r12 ≠ .r14), h12]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₂]
    · intro r h₁ h₂; simp only [gpr_arithFlags, gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have kE₃ : ∀ r ∈ [Reg.r13, .r15, .rsp], t₃.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [hg₃ _ (by decide) (by decide), hg₂ _ (by decide)]
  have E₃ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₃ := E.keep kE₃ (by rw [hrd₃, hrd₂]) (by rw [hwr₃, hwr₂])
  have hQ₃ : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t₃ Q (16 * min b 64) :=
    (hQ.take (by omega)).of_eq (by rw [hrd₃, hrd₂]) (by rw [hwr₃, hwr₂])
  have h14₃ : t₃.gpr .r14 = BitVec.ofNat 64 (min b 64) := by rw [hg₃ _ (by decide) (by decide), h14₂]
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.revLoop_ok L E₃ (by omega) (by omega) hQ₃ h14₃ hsi₃ hdi₃)
    fun t₄ ⟨fr₄, out₄, hg₄, hrd₄, hwr₄⟩ => ?_)
  have h15₄ : t₄.gpr .r15 = W := by rw [hg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), E₃.r15]
  have h14₄ : t₄.gpr .r14 = BitVec.ofNat 64 (min b 64) := by
    rw [hg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), h14₃]
  -- `vg_ghash`'s arguments.
  obtain ⟨t₅, run₅, rdi₅, rsi₅, r8₅, rdx₅, rcx₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ t₅ : State,
      runBlock isa (ghArgs ++ ptr .rdx .r15 revO ++ [.mov .rcx (.reg .r14)]) t₄ = some t₅ ∧
      t₅.gpr .rdi = W + BitVec.ofNat 64 64 ∧ t₅.gpr .rsi = W + BitVec.ofNat 64 80 ∧
      t₅.gpr .r8 = W + BitVec.ofNat 64 1512 ∧ t₅.gpr .rdx = W + BitVec.ofNat 64 488 ∧
      t₅.gpr .rcx = BitVec.ofNat 64 (min b 64) ∧ (∀ r ∈ calleeSaved, t₅.gpr r = t₄.gpr r) ∧
      t₅.mem = t₄.mem ∧ t₅.rd = t₄.rd ∧ t₅.wr = t₄.wr := by
    refine ⟨_, by srun [ghArgs], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₄]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₄]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₄]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₄]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h14₄]
    · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₅ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₅ := E₃.of_saved (fun r hr => by
      rw [hg₅ r hr]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hrd₅, hrd₄]) (by rw [hwr₅, hwr₄])
  refine WP.of_runBlock ⟨t₅, run₅, VG.Proof.AesGcmSiv.X86_64.gargs L E₅ (d := 488) (n := min b 64) (by decide) (by omega) rdi₅ rsi₅ rdx₅
    rcx₅ r8₅, E₅, fun r hr => ?_, by rw [hg₅ _ (by decide), h14₄], by rw [hrd₅, hrd₄, hrd₃, hrd₂],
    by rw [hwr₅, hwr₄, hwr₃, hwr₂], by rw [hm₅, ← hm₃.trans hm₂]; exact fr₄, by rw [hm₅, out₄, hm₃, hm₂]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [hg₅ _ (by decide), hg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hg₃ _ (by decide) (by decide), hg₂ _ (by decide)]

theorem chunk_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t)
    {Q : Addr} {b : Nat} (hb : 1 ≤ b) (hQ : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t Q (16 * b))
    (h12 : t.gpr .r12 = Q) (hbx : t.gpr .rbx = BitVec.ofNat 64 b) :
    WP isa (absorbChunk v.callees) t (VG.Proof.AesGcmSiv.X86_64.ChunkPost K W SP Q b (min b 64) t) := by
  have hbl : b < 2 ^ 60 := by have := hQ.lt; omega
  refine WP.assoc5 (WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.chunkPre_ok L E hb hQ h12 hbx) fun t₅ Pr => ?_))
  refine WP.seq (WP.mono (gh_call v.gh Pr.call) fun t₆ P => ?_)
  have h12₆ : t₆.gpr .r12 = Q := by rw [P.saved _ (by decide), Pr.regs _ (by simp), h12]
  have hbx₆ : t₆.gpr .rbx = BitVec.ofNat 64 b := by rw [P.saved _ (by decide), Pr.regs _ (by simp), hbx]
  have h14₆ : t₆.gpr .r14 = BitVec.ofNat 64 (min b 64) := by rw [P.saved _ (by decide), Pr.r14]
  have E₆ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₆ := Pr.env.of_saved P.saved P.rd P.wr
  have dH : ∀ r ∈ [(⟨W + BitVec.ofNat 64 488, 16 * min b 64⟩ : Region)], (⟨W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  have dY : ∀ r ∈ [(⟨W + BitVec.ofNat 64 488, 16 * min b 64⟩ : Region)], (⟨W + BitVec.ofNat 64 80, 16⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  have fr₆ := P.frame
  rw [Pr.env.rsp] at fr₆
  have out₆ := P.out
  rw [Proof.AesGcm.X86_64.blockAt_frame Pr.frame dH, Proof.AesGcm.X86_64.blockAt_frame Pr.frame dY, Pr.out] at out₆
  refine WP.of_runBlock ⟨_, by srun [], ?_⟩
  refine ⟨E₆.keep (fun r hr => ?_) rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [rd_arithFlags, rd_setReg]; rw [P.rd, Pr.rd]
  · simp only [wr_arithFlags, wr_setReg]; rw [P.wr, Pr.wr]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    rw [P.saved _ (by decide), Pr.regs _ (by simp)]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h12₆, h14₆,
      Proof.AesGcm.X86_64.times16_val]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbx₆, h14₆]
    exact Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)
  · simp only [zf_setReg, zf_arithFlags, gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbx₆, h14₆,
      Proof.AesGcm.X86_64.sub_beq (show b < 2 ^ 64 by omega) (show min b 64 < 2 ^ 64 by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · simp only [mem_arithFlags, mem_setReg]
    refine (Pr.frame.sub fun r hr => ?_).trans (fr₆.mono fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W + BitVec.ofNat 64 488, 1024⟩, by simp, Region.sub_prefix (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp
  · simp only [mem_arithFlags, mem_setReg]; rw [out₆]

theorem elemsAt_add (m : Mem) (Q : Addr) (d k : Nat) :
    VG.Proof.AesGcmSiv.X86_64.elemsAt m Q (d + k) = VG.Proof.AesGcmSiv.X86_64.elemsAt m Q d ++ VG.Proof.AesGcmSiv.X86_64.elemsAt m (Q + BitVec.ofNat 64 (16 * d)) k := by
  simp only [VG.Proof.AesGcmSiv.X86_64.elemsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, Nat.mul_add]

/-- A buffer misses what absorbing writes. -/
theorem buf_absR {K W SP : Addr} {s : State} {Q : Addr} {k : Nat} (h : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s Q k) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.absR W SP, (⟨Q, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.w.sub_right (Lay.wSub (by decide))
  · exact h.w.sub_right (Lay.wSub (by decide))
  · exact h.w.sub_right (Lay.wSub (by decide))
  · exact h.w.sub_right (Lay.wSub (by decide))
  · exact h.stk.symm

/-- So do the other parts of `W`. -/
theorem w_absR {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {d k : Nat}
    (hd : d + k ≤ 80 ∨ 96 ≤ d ∧ d + k ≤ 128 ∨ 144 ≤ d ∧ d + k ≤ 488) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.absR W SP, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rcases hd with hd | hd | hd
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · rcases hd with hd | hd | hd
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm

theorem elemsAt_frame {K W SP : Addr} {s : State} {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.X86_64.absR W SP) m m') {Q : Addr} {k : Nat}
    (h : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s Q (16 * k)) : VG.Proof.AesGcmSiv.X86_64.elemsAt m' Q k = VG.Proof.AesGcmSiv.X86_64.elemsAt m Q k := by
  unfold VG.Proof.AesGcmSiv.X86_64.elemsAt
  rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt,
    Proof.AesGcm.X86_64.bytesAt_frame hf (VG.Proof.AesGcmSiv.X86_64.buf_absR h) (by have := h.lt; omega)]

/-- What absorbing leaves, from `t`, having absorbed the elements `xs`. -/
structure AbsPost (K W SP : Addr) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (VG.Proof.AesGcmSiv.X86_64.absR W SP) t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80)) xs

theorem chunks_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t)
    {Q : Addr} {b : Nat} (hb : 1 ≤ b) (hQ : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t Q (16 * b))
    (h12 : t.gpr .r12 = Q) (hbx : t.gpr .rbx = BitVec.ofNat 64 b) :
    WP isa (.loop (absorbChunk v.callees) .ne) t fun t' => VG.Proof.AesGcmSiv.X86_64.AbsPost K W SP (VG.Proof.AesGcmSiv.X86_64.elemsAt t.mem Q b) t t' ∧
      t'.gpr .r12 = Q + BitVec.ofNat 64 (16 * b) ∧ t'.gpr .rbp = t.gpr .rbp := by
  refine WP.loop (M := isa) (body := absorbChunk v.callees) (c := .ne)
    (fun (m : Nat) (t' : State) => ∃ d, m = b - d ∧ d < b ∧ VG.Proof.AesGcmSiv.X86_64.AbsPost K W SP (VG.Proof.AesGcmSiv.X86_64.elemsAt t.mem Q d) t t' ∧
      t'.gpr .r12 = Q + BitVec.ofNat 64 (16 * d) ∧ t'.gpr .rbx = BitVec.ofNat 64 (b - d) ∧
      t'.gpr .rbp = t.gpr .rbp) ?_ (b - 0) t
    ⟨0, rfl, hb, ⟨E, rfl, rfl, Frame.refl _ _, by simp [VG.Proof.AesGcmSiv.X86_64.elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [h12, Nat.mul_zero, BitVec.add_zero], by rw [hbx, Nat.sub_zero], rfl⟩
  rintro m t' ⟨d, rfl, hd, P, h12', hbx', hbp'⟩
  have hQ' : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t' (Q + BitVec.ofNat 64 (16 * d)) (16 * (b - d)) :=
    (hQ.slice (by omega)).of_eq P.rd P.wr
  refine WP.mono (VG.Proof.AesGcmSiv.X86_64.chunk_ok v L P.env (by omega) hQ' h12' hbx') fun t'' C => ?_
  have hk : 1 ≤ min (b - d) 64 := by omega
  have P' : VG.Proof.AesGcmSiv.X86_64.AbsPost K W SP (VG.Proof.AesGcmSiv.X86_64.elemsAt t.mem Q (d + min (b - d) 64)) t t'' := by
    refine ⟨C.env, C.rd.trans P.rd, C.wr.trans P.wr, P.frame.trans C.frame, ?_⟩
    rw [C.out, P.out, Proof.AesGcm.X86_64.blockAt_frame P.frame (VG.Proof.AesGcmSiv.X86_64.w_absR L (.inl (by decide))),
      VG.Proof.AesGcmSiv.X86_64.elemsAt_frame P.frame ((hQ.slice (k := 16 * min (b - d) 64) (by omega))), VG.Proof.AesGcmSiv.X86_64.elemsAt_add,
      Proof.Gcm.ghashFrom_append]
  have r12'' : t''.gpr .r12 = Q + BitVec.ofNat 64 (16 * (d + min (b - d) 64)) := by
    rw [C.r12, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, Nat.mul_add]
  have rbp'' : t''.gpr .rbp = t.gpr .rbp := C.rbp.trans hbp'
  by_cases he : b - d - min (b - d) 64 = 0
  · left
    have hdb : d + min (b - d) 64 = b := by omega
    refine ⟨(VG.Proof.AesGcmSiv.X86_64.eval_ne C.zf).trans (by simp [he]), hdb ▸ P', hdb ▸ r12'', rbp''⟩
  · right
    refine ⟨(VG.Proof.AesGcmSiv.X86_64.eval_ne C.zf).trans (by simp [he]), b - (d + min (b - d) 64), by omega, d + min (b - d) 64, rfl,
      by omega, P', r12'', by rw [C.rbx]; congr 1; omega, rbp''⟩

/-- The last bytes copied over a zeroed block. -/
theorem pad_bytes (m : Mem) (c : Addr) (xs : List Byte) (hx : xs.length < 16) :
    bytesAt (writeBytes (Proof.Cmac.zero2 m c) c xs) c 16 = xs ++ Spec.GcmSiv.zeros (16 - xs.length) := by
  have hz := Proof.Cmac.zero2_bytes m c
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.X86_64.bytesAt_add] at hz
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.X86_64.bytesAt_add,
    Proof.AesGcm.X86_64.bytesAt_writeBytes_self _ _ _ (by omega),
    Proof.AesGcm.X86_64.bytesAt_frame (Proof.AesGcm.X86_64.writeBytes_frame' _ rfl) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base c (Nat.le_refl _) (by omega)) (by omega)]
  refine congrArg (xs ++ ·) ?_
  have := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (Proof.AesGcm.X86_64.length_bytesAt _ _ _)] at this
  rw [this, Nat.add_sub_cancel_left]
  simp [Spec.Cmac.zeros, Spec.GcmSiv.zeros, List.drop_replicate]

/-- The last bytes up to their call: the padded block reversed at `W + 488`,
and the arguments of `vg_ghash`. -/
structure TailPre (K W SP : Addr) (P : Addr) (r : Nat) (t t₃ : State) : Prop where
  call : GhCall t₃ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
    (W + BitVec.ofNat 64 1512) 1
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₃
  regs : ∀ q ∈ [Reg.rbx, .rbp, .r12, .r13, .r15, .rsp], t₃.gpr q = t.gpr q
  rd : t₃.rd = t.rd
  wr : t₃.wr = t.wr
  frame : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩] t.mem t₃.mem
  block : Spec.Gcm.blockAt t₃.mem (W + BitVec.ofNat 64 488) =
    Spec.GcmSiv.ofBytes (bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r))

theorem tailPre_ok {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t)
    {P : Addr} {r : Nat} (hr1 : 1 ≤ r) (hr : r < 16) (hP : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t P r)
    (h12 : t.gpr .r12 = P) (hbp : t.gpr .rbp = BitVec.ofNat 64 r) :
    WP isa (.seq (.block (zero16 bO ++ ptr .rdi .r15 bO ++ ([.mov .rsi (.reg .r12), .mov .rcx (.reg .rbp)] : List Instr)))
      (.seq Impl.AesGcm.X86_64.copyLoop (.block (([.mov .rax (.mem (at_ .r15 bO)), .mov .rdx (.mem (at_ .r15 (bO + 8))), .bswap .rax,
        .bswap .rdx, .store (at_ .r15 revO) .rdx, .store (at_ .r15 (revO + 8)) .rax] : List Instr) ++ ghArgs ++
        ptr .rdx .r15 revO ++ ([.mov32 .rcx (imm 1)] : List Instr))))) t (VG.Proof.AesGcmSiv.X86_64.TailPre K W SP P r t) := by
  have h15 := E.r15
  have hw := L.ww
  have w₀ := E.perm.wW (show 128 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 136 + 8 ≤ 3816 by decide)
  -- The block zeroed, and the copy's arguments.
  obtain ⟨t₁, run₁, hm₁, hdi₁, hsi₁, hcx₁, hg₁, hrd₁, hwr₁⟩ : ∃ t₁ : State,
      runBlock isa (zero16 bO ++ ptr .rdi .r15 bO ++ [.mov .rsi (.reg .r12), .mov .rcx (.reg .rbp)]) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero2 t.mem (W + BitVec.ofNat 64 128) ∧ t₁.gpr .rdi = W + BitVec.ofNat 64 128 ∧
      t₁.gpr .rsi = P ∧ t₁.gpr .rcx = BitVec.ofNat 64 r ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [zero16, h15, w₀, w₈], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, Proof.Cmac.zero2, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc]
      rfl
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h12]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbp]
    · intro r h₁ h₂ h₃ h₄; simp only [gpr_arithFlags, gpr_setReg, h₁, h₂, h₃, h₄, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have lp : Proof.AesGcm.X86_64.LoopPre t₁ P (W + BitVec.ofNat 64 128) r :=
    ⟨hsi₁, hdi₁, hcx₁, hr1, by omega, by rw [hrd₁, hwr₁]; exact hP.rd, by rw [hwr₁]; exact E.perm.wC (by omega),
      hP.w.sub_right (Lay.wSub (by omega))⟩
  refine WP.seq (WP.mono (Proof.AesGcm.X86_64.copyLoop_ok t₁ lp) fun t₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_)
  -- The data is outside the zeroed block.
  have hd₁ : bytesAt t₁.mem P r = bytesAt t.mem P r := by
    rw [hm₁, Proof.Cmac.zero2]
    exact Proof.AesGcm.X86_64.bytesAt_frame
      (((Frame.refl [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region)] _).writeW (List.mem_singleton_self _) _
        (Offset.contains W (Nat.le_refl _) (by decide) (by omega))).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide)))
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by omega)
  have hb₂ : bytesAt t₂.mem (W + BitVec.ofNat 64 128) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r) := by
    have hl := Proof.AesGcm.X86_64.length_bytesAt t.mem P r
    rw [hm₂, hd₁, hm₁, VG.Proof.AesGcmSiv.X86_64.pad_bytes _ _ _ (by omega), hl]
  have h15₂ : t₂.gpr .r15 = W := by
    rw [hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide) (by decide), h15]
  have r₀ := E.perm.wR (show 128 + 8 ≤ 3816 by decide)
  have r₈ := E.perm.wR (show 136 + 8 ≤ 3816 by decide)
  have v₀ := E.perm.wW (show 488 + 8 ≤ 3816 by decide)
  have v₈ := E.perm.wW (show 496 + 8 ≤ 3816 by decide)
  rw [← hrd₁, ← hwr₁, ← hrd₂, ← hwr₂] at r₀ r₈
  rw [← hwr₁, ← hwr₂] at v₀ v₈
  -- The block reversed at `W + 488`, and `vg_ghash`'s arguments.
  obtain ⟨t₃, run₃, hm₃, rdi₃, rsi₃, r8₃, rdx₃, rcx₃, hg₃, hrd₃, hwr₃⟩ : ∃ t₃ : State,
      runBlock isa (([.mov .rax (.mem (at_ .r15 bO)), .mov .rdx (.mem (at_ .r15 (bO + 8))), .bswap .rax, .bswap .rdx,
        .store (at_ .r15 revO) .rdx, .store (at_ .r15 (revO + 8)) .rax] : List Instr) ++ ghArgs ++
        ptr .rdx .r15 revO ++ ([.mov32 .rcx (imm 1)] : List Instr)) t₂ = some t₃ ∧
      t₃.mem = (t₂.mem.writeW (W + BitVec.ofNat 64 488) (bswap64 (t₂.mem.readW (W + BitVec.ofNat 64 136) 64))).writeW
        (W + BitVec.ofNat 64 488 + BitVec.ofNat 64 8) (bswap64 (t₂.mem.readW (W + BitVec.ofNat 64 128) 64)) ∧
      t₃.gpr .rdi = W + BitVec.ofNat 64 64 ∧ t₃.gpr .rsi = W + BitVec.ofNat 64 80 ∧
      t₃.gpr .r8 = W + BitVec.ofNat 64 1512 ∧ t₃.gpr .rdx = W + BitVec.ofNat 64 488 ∧
      t₃.gpr .rcx = BitVec.ofNat 64 1 ∧ (∀ r ∈ calleeSaved, t₃.gpr r = t₂.gpr r) ∧
      t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [ghArgs, h15₂, r₀, r₈, v₀, v₈], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₂]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₂]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₂]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₂]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₃ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₃ := E.keep (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;>
        rw [hg₃ _ (by decide), hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide) (by decide)])
    (by rw [hrd₃, hrd₂, hrd₁]) (by rw [hwr₃, hwr₂, hwr₁])
  -- What the pieces wrote so far.
  have fr₃' : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩] t.mem t₃.mem := by
    have mB : (⟨W + BitVec.ofNat 64 128, 16⟩ : Region) ∈
        [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩] := by simp
    have mR : (⟨W + BitVec.ofNat 64 488, 1024⟩ : Region) ∈
        [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩] := by simp
    have f₁ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩] t.mem t₁.mem := by
      rw [hm₁, Proof.Cmac.zero2]
      exact ((Frame.refl _ _).writeW mB _ (Offset.contains W (Nat.le_refl _) (by decide) (by omega))).writeW mB _
        (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide))
    have f₂ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩] t₁.mem t₂.mem := by
      rw [hm₂]
      exact (Proof.AesGcm.X86_64.writeBytes_frame' _ (Proof.AesGcm.X86_64.length_bytesAt _ _ _)).sub
        fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, mB, Region.sub_prefix (by omega)⟩
    have f₃ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩] t₂.mem t₃.mem := by
      rw [hm₃]
      exact ((Frame.refl _ _).writeW mR _ (Offset.contains W (Nat.le_refl _) (by decide) (by omega))).writeW mR _
        (Offset.contains_base _ (show 8 + 8 ≤ 1024 by decide) (by decide))
    exact (f₁.trans f₂).trans f₃
  have fr₃ : Frame (VG.Proof.AesGcmSiv.X86_64.absR W SP) t.mem t₃.mem := fr₃'.mono fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp
  have hb₃ : Spec.Gcm.blockAt t₃.mem (W + BitVec.ofNat 64 488) =
      Spec.GcmSiv.ofBytes (bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r)) := by
    rw [hm₃, VG.Proof.AesGcmSiv.X86_64.blockAt_two, ← hb₂, GcmSiv.ofBytes_bytesAt, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc]
  refine WP.of_runBlock ⟨t₃, run₃, VG.Proof.AesGcmSiv.X86_64.gargs L E₃ (d := 488) (n := 1) (by decide) (by decide) rdi₃ rsi₃ rdx₃ rcx₃ r8₃,
    E₃, fun q hq => ?_, by rw [hrd₃, hrd₂, hrd₁], by rw [hwr₃, hwr₂, hwr₁], fr₃', hb₃⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [hg₃ _ (by decide), hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide) (by decide)]

theorem tail_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t)
    {P : Addr} {r : Nat} (hr1 : 1 ≤ r) (hr : r < 16) (hP : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t P r)
    (h12 : t.gpr .r12 = P) (hbp : t.gpr .rbp = BitVec.ofNat 64 r) :
    WP isa (absorbTail v.callees) t
      (VG.Proof.AesGcmSiv.X86_64.AbsPost K W SP [Spec.GcmSiv.ofBytes (bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  refine VG.Proof.AesGcmSiv.X86_64.seq_assoc3 (WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.tailPre_ok L E hr1 hr hP h12 hbp) fun t₃ Tp => ?_))
  have fr₃ : Frame (VG.Proof.AesGcmSiv.X86_64.absR W SP) t.mem t₃.mem := Tp.frame.mono fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp
  refine WP.mono (gh_call v.gh Tp.call) fun t₄ Q => ?_
  have fr₄ := Q.frame
  rw [Tp.env.rsp] at fr₄
  refine ⟨Tp.env.of_saved Q.saved Q.rd Q.wr, by rw [Q.rd, Tp.rd], by rw [Q.wr, Tp.wr],
    fr₃.trans (fr₄.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp), ?_⟩
  rw [Q.out, Proof.AesGcm.X86_64.blockAt_frame fr₃ (VG.Proof.AesGcmSiv.X86_64.w_absR L (.inl (by decide))),
    Proof.AesGcm.X86_64.blockAt_frame Tp.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)),
    show Spec.Gcm.blocksAt t₃.mem (W + BitVec.ofNat 64 488) 1 = [Spec.Gcm.blockAt t₃.mem (W + BitVec.ofNat 64 488)] by
      simp [Spec.Gcm.blocksAt], Tp.block]

theorem AbsPost.trans {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h₁ : VG.Proof.AesGcmSiv.X86_64.AbsPost K W SP xs t t₁) (h₂ : VG.Proof.AesGcmSiv.X86_64.AbsPost K W SP ys t₁ t₂) : VG.Proof.AesGcmSiv.X86_64.AbsPost K W SP (xs ++ ys) t t₂ := by
  refine ⟨h₂.env, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.frame.trans h₂.frame, ?_⟩
  rw [h₂.out, h₁.out, Proof.AesGcm.X86_64.blockAt_frame h₁.frame (VG.Proof.AesGcmSiv.X86_64.w_absR L (.inl (by decide))),
    Proof.Gcm.ghashFrom_append]

/-- The field elements of `n` bytes at `Q`, padded. -/
theorem elems_pad16_bytesAt (m : Mem) (Q : Addr) (n : Nat) :
    Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m Q n)) = VG.Proof.AesGcmSiv.X86_64.elemsAt m Q (n / 16) ++
      if n % 16 = 0 then [] else
        [Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++ Spec.GcmSiv.zeros (16 - n % 16))] := by
  have hs := Proof.AesGcm.X86_64.bytesAt_add m Q (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega] at hs
  have hl := Proof.AesGcm.X86_64.length_bytesAt m Q (16 * (n / 16))
  rw [GcmSiv.elems_pad16, Proof.AesGcm.X86_64.length_bytesAt, hs, List.take_left' hl, List.drop_left' hl,
    GcmSiv.elems_bytesAt]

theorem AbsPost.of_eq {K W SP : Addr} {xs : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h : VG.Proof.AesGcmSiv.X86_64.AbsPost K W SP xs t₁ t₂) (hm : t₁.mem = t.mem) (hrd : t₁.rd = t.rd) (hwr : t₁.wr = t.wr) :
    VG.Proof.AesGcmSiv.X86_64.AbsPost K W SP xs t t₂ :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, hm ▸ h.frame, by rw [h.out, hm]⟩

theorem absorb_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t)
    {Q : Addr} {n : Nat} (hQ : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t Q n) (h12 : t.gpr .r12 = Q) (hbp : t.gpr .rbp = BitVec.ofNat 64 n) :
    WP isa (absorb v.callees) t
      (VG.Proof.AesGcmSiv.X86_64.AbsPost K W SP (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem Q n))) t) := by
  have hn := hQ.lt
  have hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 n)
  rw [toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  obtain ⟨t₁, run₁, hbx₁, hbp₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State,
      runBlock isa [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)] t =
        some t₁ ∧
      t₁.gpr .rbx = BitVec.ofNat 64 (n / 16) ∧ t₁.gpr .rbp = BitVec.ofNat 64 (n % 16) ∧
      t₁.zf = some (decide (n / 16 = 0)) ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbp,
        Proof.AesGcm.X86_64.shr4 _ hn]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbp, hand]
    · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
        reduceCtorEq, hbp, Proof.AesGcm.X86_64.shr4 _ hn]
      rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]
    · intro r h₁ h₂; simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  have hQ₁ := hQ.of_eq hrd₁ hwr₁
  have h12₁ : t₁.gpr .r12 = Q := by rw [hg₁ _ (by decide) (by decide), h12]
  -- The whole blocks.
  have hmid : WP isa (.ite .e (.block []) (.loop (absorbChunk v.callees) .ne)) t₁ fun t₂ =>
      VG.Proof.AesGcmSiv.X86_64.AbsPost K W SP (VG.Proof.AesGcmSiv.X86_64.elemsAt t.mem Q (n / 16)) t₁ t₂ ∧ t₂.gpr .r12 = Q + BitVec.ofNat 64 (16 * (n / 16)) ∧
      t₂.gpr .rbp = BitVec.ofNat 64 (n % 16) := by
    refine WP.ite (decide (n / 16 = 0)) (VG.Proof.AesGcmSiv.X86_64.eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : n / 16 = 0 := by simpa using ht
      refine WP.block_nil ⟨⟨E₁, rfl, rfl, Frame.refl _ _, by simp [h0, VG.Proof.AesGcmSiv.X86_64.elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
        by rw [h12₁, h0, Nat.mul_zero, BitVec.add_zero], hbp₁⟩
    · have h0 : n / 16 ≠ 0 := by simpa using hf
      refine WP.mono (VG.Proof.AesGcmSiv.X86_64.chunks_ok v L E₁ (by omega) (hQ₁.take (by omega)) h12₁ hbx₁) fun t₂ ⟨P, r12, rbp⟩ => ?_
      rw [hm₁] at P
      exact ⟨P, r12, rbp.trans hbp₁⟩
  refine WP.seq (WP.mono hmid fun t₂ ⟨P₂, r12₂, rbp₂⟩ => ?_)
  have P₂' := P₂.of_eq hm₁ hrd₁ hwr₁
  obtain ⟨t₃, run₃, hzf₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃ : State, runBlock isa [.alu .test .rbp (.reg .rbp)] t₂ = some t₃ ∧
      t₃.zf = some (decide (n % 16 = 0)) ∧ (∀ r, t₃.gpr r = t₂.gpr r) ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, rbp₂]
      rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]
    · intro r; rfl
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have P₃ : VG.Proof.AesGcmSiv.X86_64.AbsPost K W SP (VG.Proof.AesGcmSiv.X86_64.elemsAt t.mem Q (n / 16)) t t₃ :=
    ⟨P₂'.env.keep (fun r _ => hg₃ r) hrd₃ hwr₃, hrd₃.trans P₂'.rd, hwr₃.trans P₂'.wr, hm₃ ▸ P₂'.frame,
      by rw [hm₃, P₂'.out]⟩
  rw [VG.Proof.AesGcmSiv.X86_64.elems_pad16_bytesAt]
  refine WP.ite (decide (n % 16 = 0)) (VG.Proof.AesGcmSiv.X86_64.eval_e hzf₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil P₃
  · have h0 : n % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    have hP : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t₃ (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hQ.slice (by omega)).of_eq P₃.rd P₃.wr
    refine WP.mono (VG.Proof.AesGcmSiv.X86_64.tail_ok v L P₃.env (by omega) (by omega) hP (by rw [hg₃, r12₂]) (by rw [hg₃, rbp₂]))
      fun t₄ T => ?_
    have e := Proof.AesGcm.X86_64.bytesAt_frame P₃.frame (VG.Proof.AesGcmSiv.X86_64.buf_absR (hQ.slice (a := 16 * (n / 16)) (k := n % 16)
      (by omega))) (by omega)
    rw [e] at T
    exact P₃.trans L T

end VG.Proof.AesGcmSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86_64.Polyval`. -/
section

/-!
# AES-GCM-SIV on x86-64: POLYVAL and the tag input (`polyval`)

Untrusted: everything here is checked by Lean. `lens` absorbs the lengths
block (`lens_ok`), `tagIn` turns POLYVAL's result into the tag input
(`tagIn_ok`), and `polyval` absorbs the padded additional data, the padded
data and the lengths block from the zero accumulator, leaving the tag input
of RFC 8452 §4 at `W + 96` (`polyval_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl GhCall GhPost gh_call ofNat_add_ofNat in_off toNat_ofNat_of_lt)

/-- The arguments of `lens`'s call. -/
theorem lensArgs_ok {K W SP : Addr} {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {al n : Nat}
    (hal : t.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (hn : t.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) (hal' : al < 2 ^ 64) (hn' : n < 2 ^ 64) :
    ∃ t₁ : State,
      runBlock isa (([.mov .rax (.mem (at_ .r15 lenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 bO) .rax,
        .mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 (bO + 8)) .rax] :
          List Instr) ++ ghArgs ++ ptr .rdx .r15 bO ++ ([.mov32 .rcx (imm 1)] : List Instr)) t = some t₁ ∧
      t₁.mem = (t.mem.writeW (W + BitVec.ofNat 64 128) (bswap64 (BitVec.ofNat 64 (8 * n)))).writeW
        (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8) (bswap64 (BitVec.ofNat 64 (8 * al))) ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 64 ∧ t₁.gpr .rsi = W + BitVec.ofNat 64 80 ∧
      t₁.gpr .r8 = W + BitVec.ofNat 64 1512 ∧ t₁.gpr .rdx = W + BitVec.ofNat 64 128 ∧
      t₁.gpr .rcx = BitVec.ofNat 64 1 ∧ (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have r₂ := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (show 128 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 136 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [ghArgs, h15, r₁, r₂, w₀, w₈, hal, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, Proof.AesGcm.X86_64.times8_val,
      toNat_ofNat_of_lt hal', toNat_ofNat_of_lt hn']
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

theorem lens_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {al n : Nat}
    (hal : t.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (hn : t.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) (hal' : al < 2 ^ 64) (hn' : n < 2 ^ 64) :
    WP isa (lens v.callees) t
      (VG.Proof.AesGcmSiv.X86_64.AbsPost K W SP [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n))] t) := by
  obtain ⟨t₁, run₁, hm₁, rdi₁, rsi₁, r8₁, rdx₁, rcx₁, hg₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcmSiv.X86_64.lensArgs_ok E hal hn hal' hn'
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := E.of_saved hg₁ hrd₁ hwr₁
  have fB : Frame [⟨W + BitVec.ofNat 64 128, 16⟩] t.mem t₁.mem := by
    rw [hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains W (Nat.le_refl _) (by decide) (by have := L.ww; omega))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide))
  have dB : ∀ d, d + 16 ≤ 128 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region)],
      (⟨W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun d hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl hd) (by omega) (by decide)
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (gh_call v.gh (VG.Proof.AesGcmSiv.X86_64.gargs L E₁ (d := 128) (n := 1) (by decide) (by decide) rdi₁ rsi₁ rdx₁ rcx₁ r8₁))
    fun t₂ Q => ?_
  have fr₂ := Q.frame
  rw [E₁.rsp] at fr₂
  refine ⟨E₁.of_saved Q.saved Q.rd Q.wr, by rw [Q.rd, hrd₁], by rw [Q.wr, hwr₁],
    (fB.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans (fr₂.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp), ?_⟩
  rw [Q.out, Proof.AesGcm.X86_64.blockAt_frame fB (dB 64 (by decide)),
    Proof.AesGcm.X86_64.blockAt_frame fB (dB 80 (by decide)),
    show Spec.Gcm.blocksAt t₁.mem (W + BitVec.ofNat 64 128) 1 = [Spec.Gcm.blockAt t₁.mem (W + BitVec.ofNat 64 128)] by
      simp [Spec.Gcm.blocksAt], hm₁, VG.Proof.AesGcmSiv.X86_64.blockAt_two, GcmSiv.le64_le8, GcmSiv.le64_le8, GcmSiv.ofBytes_le8]

theorem tagIn_ok {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {N : Addr}
    (hN : t.mem.readW (W + BitVec.ofNat 64 208) 64 = N) (hNb : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t N 12) :
    ∃ t' : State, runBlock isa VG.Impl.AesGcmSiv.X86_64.tagIn t = some t' ∧ Frame [⟨W + BitVec.ofNat 64 96, 16⟩] t.mem t'.mem ∧
      bytesAt t'.mem (W + BitVec.ofNat 64 96) 16 =
        GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80))) (bytesAt t.mem N 12) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have hw := L.ww
  have r₀ := E.perm.wR (show 80 + 8 ≤ 3816 by decide)
  have r₈ := E.perm.wR (show 88 + 8 ≤ 3816 by decide)
  have rn := E.perm.wR (show 208 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (show 96 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 104 + 8 ≤ 3816 by decide)
  have n₀ : InRegions (t.rd ++ t.wr) N 8 := by
    simpa using in_off (d := 0) (n := 8) hNb.rd (by decide) (by decide)
  have n₈ := in_off (d := 8) (n := 4) hNb.rd (by decide) (by decide)
  refine ⟨_, by srun [VG.Impl.AesGcmSiv.X86_64.tagIn, h15, r₀, r₈, rn, w₀, w₈, hN, n₀, n₈], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains W (Nat.le_refl _) (by decide) (by omega))).writeW (List.mem_singleton_self _) _
      (Offset.contains W (by decide) (by decide) (by omega))
  · simp only [mem_setReg, mem_arithFlags]
    rw [show W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc],
      Proof.Cmac.bytesAt_store2, ← Proof.Gcm.X86_64.blockAt_bswap, BitVec.add_zero, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc,
      GcmSiv.toBytes_append, show (12 : Nat) = 8 + 4 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le8_readW,
      ← Proof.Cmac.le4_readW, GcmSiv.tagOf_words]
    rfl
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- The slots, after code that writes only what absorbing writes. -/
theorem Slots.absR {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat} {m m' : Mem}
    (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n m) (hf : Frame (VG.Proof.AesGcmSiv.X86_64.absR W SP) m m') : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n m' := by
  have k (d : Nat) (hd : 200 ≤ d ∧ d + 8 ≤ 248) : m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
    hf.readW (Region.contains_self _ _) (VG.Proof.AesGcmSiv.X86_64.w_absR L (.inr (.inr ⟨by omega, by omega⟩))) (by decide)
  exact ⟨by rw [k 200 (by decide)]; exact S.rounds, by rw [k 208 (by decide)]; exact S.nonce,
    by rw [k 216 (by decide)]; exact S.aad, by rw [k 224 (by decide)]; exact S.alen,
    by rw [k 232 (by decide)]; exact S.data, by rw [k 240 (by decide)]; exact S.len⟩

/-- What `polyval` writes: what absorbing writes, and the tag input at `W + 96`. -/
abbrev polyR (W SP : Addr) : List Region := ⟨W + BitVec.ofNat 64 96, 16⟩ :: VG.Proof.AesGcmSiv.X86_64.absR W SP

/-- What `polyval` leaves, from `t`. -/
structure PolyPost (K W SP : Addr) (N A D : Addr) (al n : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (VG.Proof.AesGcmSiv.X86_64.polyR W SP) t.mem t'.mem
  /-- Given that POLYVAL is GHASH with `mulXG` of the key (`PolyvalEq`, proved
  in `Verified.lean` so that these proofs need not import its algebra). -/
  out : GcmSiv.Polyval.PolyvalEq → bytesAt t'.mem (W + BitVec.ofNat 64 96) 16 =
    Spec.GcmSiv.tagInput (bytesAt t.mem (W + BitVec.ofNat 64 16) 16) (bytesAt t.mem N 12) (bytesAt t.mem D n)
      (bytesAt t.mem A al)

theorem polyval_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {R : Nat}
    {N A D : Addr} {al n : Nat} (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n t.mem) (hA : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t A al) (hD : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t D n)
    (hN : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t N 12)
    (hG : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0) :
    WP isa (polyval v.callees) t (VG.Proof.AesGcmSiv.X86_64.PolyPost K W SP N A D al n t) := by
  have h15 := E.r15
  have rA := E.perm.wR (show 216 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  have sA := S.aad
  have sL := S.alen
  obtain ⟨t₁, run₁, h12₁, hbp₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa
      [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] t = some t₁ ∧
      t₁.gpr .r12 = A ∧ t₁.gpr .rbp = BitVec.ofNat 64 al ∧ (∀ r, r ≠ .r12 → r ≠ .rbp → t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h15, rA, rL], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sA]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sL]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  refine WP.mono (VG.Proof.AesGcmSiv.X86_64.absorb_ok v L E₁ (hA.of_eq hrd₁ hwr₁) h12₁ hbp₁) fun t₂ P₂ => ?_
  have P₂' := P₂.of_eq hm₁ hrd₁ hwr₁
  rw [hm₁] at P₂'
  have S₂ := S.absR L P₂'.frame
  have h15₂ := P₂'.env.r15
  have rD := P₂'.env.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rN := P₂'.env.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have sD := S₂.data
  have sN := S₂.len
  obtain ⟨t₃, run₃, h12₃, hbp₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃ : State, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))] t₂ = some t₃ ∧
      t₃.gpr .r12 = D ∧ t₃.gpr .rbp = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .r12 → r ≠ .rbp → t₃.gpr r = t₂.gpr r) ∧
      t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [h15₂, rD, rN], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sD]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sN]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, WP.seq ?_⟩)
  have E₃ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₃ := P₂'.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  have hD₃ : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t₃ D n := hD.of_eq (hrd₃.trans P₂'.rd) (hwr₃.trans P₂'.wr)
  refine WP.mono (VG.Proof.AesGcmSiv.X86_64.absorb_ok v L E₃ hD₃ h12₃ hbp₃) fun t₄ P₄ => ?_
  have P₄' := P₄.of_eq hm₃ hrd₃ hwr₃
  rw [hm₃, Proof.AesGcm.X86_64.bytesAt_frame P₂'.frame (VG.Proof.AesGcmSiv.X86_64.buf_absR hD) (Nat.le_of_lt hD.lt)] at P₄'
  have P₂₄ := P₂'.trans L P₄'
  have S₄ := S.absR L P₂₄.frame
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.lens_ok v L P₂₄.env S₄.alen S₄.len hA.lt hD.lt) fun t₅ P₅ => ?_)
  have P₂₅ := P₂₄.trans L P₅
  have S₅ := S.absR L P₂₅.frame
  obtain ⟨t₆, run₆, fr₆, out₆, hg₆, hrd₆, hwr₆⟩ := VG.Proof.AesGcmSiv.X86_64.tagIn_ok L P₂₅.env S₅.nonce (hN.of_eq P₂₅.rd P₂₅.wr)
  refine WP.of_runBlock ⟨t₆, run₆, P₂₅.env.of_saved hg₆ hrd₆ hwr₆, hrd₆.trans P₂₅.rd, hwr₆.trans P₂₅.wr,
    (P₂₅.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans
      (fr₆.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self ..), fun hpv => ?_⟩
  have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
    rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega
  rw [out₆, Proof.AesGcm.X86_64.bytesAt_frame P₂₅.frame (VG.Proof.AesGcmSiv.X86_64.buf_absR hN) (by decide), GcmSiv.tagInput_eq,
    Proof.AesGcm.X86_64.length_bytesAt, Proof.AesGcm.X86_64.length_bytesAt, P₂₅.out, hG, hY, Spec.GcmSiv.polyval,
    hpv, GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
    GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n)) (by simp [Spec.GcmSiv.le64])]

end VG.Proof.AesGcmSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86_64.Tag`. -/
section

/-!
# AES-GCM-SIV on x86-64: the tag (`tag`)

Untrusted: everything here is checked by Lean. `tag o` encrypts the tag
input at `W + 96` with the encryption key's schedule at `W + 248` into the
block at `W + o`, by `vg_aes_ctr32` of one zero block from a copy of it at
`W + 112` (`tag_ok`); counter mode's last block uses the same code for the
keystream block at `W + 128`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl CtrCall CtrPost ctr_call toNat_ofNat_of_lt)

theorem blockAt_zero2 (m : Mem) (p : Addr) : Spec.Gcm.blockAt (Proof.Cmac.zero2 m p) p = 0 := by
  rw [Spec.Gcm.blockAt, Proof.Cmac.zero2_bytes]
  decide

/-- A part of `W` read after a write to its start. -/
theorem readW_writeW_W0 {m : Mem} {W : Addr} {d w w' : Nat} (v : BitVec w') (h : w' / 8 ≤ d)
    (hd : d + w / 8 ≤ 2 ^ 64) (hw : w / 8 < 2 ^ 64) (hw' : w' / 8 ≤ 2 ^ 64) :
    (m.writeW W v).readW (W + BitVec.ofNat 64 d) w = m.readW (W + BitVec.ofNat 64 d) w := by
  simpa using VG.Proof.AesGcmSiv.X86_64.readW_writeW_W (m := m) (W := W) (e := 0) (d := d) (w := w) v (.inr (by omega)) hd (by omega) hw

/-- What `tag o` writes. -/
abbrev tagR (W SP : Addr) (o : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩, ⟨W + BitVec.ofNat 64 1768, 2048⟩, below SP 8]

/-- What `tag o` leaves, from `t`. -/
structure TagPost (K W SP : Addr) (R o : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  saved : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r
  frame : Frame (VG.Proof.AesGcmSiv.X86_64.tagR W SP o) t.mem t'.mem
  out : bytesAt t'.mem (W + BitVec.ofNat 64 o) 16 =
    Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R (bytesAt t.mem (W + BitVec.ofNat 64 96) 16)

/-- The arguments of `tag o`'s call. -/
theorem tagArgs_ok {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {t : State}
    (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {N A D : Addr} {al n : Nat} (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n t.mem) {o : Nat}
    (ho : o = 0 ∨ o = 128) :
    ∃ t₁ : State, runBlock isa
    (copy16 cmO ccO ++ zero16 o ++ ptr .rdi .r15 skO ++ ctrArgs ++ ptr .rcx .r15 o) t = some t₁ ∧
    t₁.mem = Proof.Cmac.zero2 ((t.mem.writeW (W + BitVec.ofNat 64 112) (t.mem.readW (W + BitVec.ofNat 64 96) 64)).writeW
      (W + BitVec.ofNat 64 112 + BitVec.ofNat 64 8) (t.mem.readW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 64))
      (W + BitVec.ofNat 64 o) ∧
    t₁.gpr .rdi = W + BitVec.ofNat 64 248 ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧
    t₁.gpr .rdx = W + BitVec.ofNat 64 112 ∧ t₁.gpr .rcx = W + BitVec.ofNat 64 o ∧
    t₁.gpr .r8 = BitVec.ofNat 64 1 ∧ t₁.gpr .r9 = W + BitVec.ofNat 64 1768 ∧
    (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have hw := L.ww
  have rR := S.rounds
  have rR' := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  have r₀ := E.perm.wR (show 96 + 8 ≤ 3816 by decide)
  have r₈ := E.perm.wR (show 104 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (show 112 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 120 + 8 ≤ 3816 by decide)
  have z₀ := E.perm.wW (show o + 8 ≤ 3816 by omega)
  have z₈ := E.perm.wW (show o + 8 + 8 ≤ 3816 by omega)
  rcases ho with rfl | rfl
  all_goals
    simp only [Nat.reduceAdd, BitVec.add_zero] at z₀ z₈
    refine ⟨_, by srun [copy16, zero16, ctrArgs, h15, rR, rR', r₀, r₈, w₀, w₈, z₀, z₈, VG.Proof.AesGcmSiv.X86_64.readW_writeW_W0], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, Proof.Cmac.zero2, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, BitVec.add_zero, Nat.reduceAdd]; rfl
    all_goals try (simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15, rR,
      BitVec.add_zero]; done)
    · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    all_goals rfl

theorem tag_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State}
    (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {N A D : Addr} {al n : Nat} (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n t.mem) {o : Nat}
    (ho : o = 0 ∨ o = 128) :
    WP isa (tag v.callees o) t (VG.Proof.AesGcmSiv.X86_64.TagPost K W SP R o t) := by
  have hw := L.ww
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcmSiv.X86_64.tagArgs_ok L E S ho
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := E.of_saved hg₁ hrd₁ hwr₁
  have dO : (⟨W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 112, 16⟩ :=
    L.w_w (by omega) (by omega) (by decide)
  have cc : CtrCall t₁ (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 o)
      (W + BitVec.ofNat 64 1768) R 1 :=
    VG.Proof.AesGcmSiv.X86_64.cargs L E₁ hR (VG.Proof.AesGcmSiv.X86_64.keyS L E₁.perm) (c := 112) (by decide) (VG.Proof.AesGcmSiv.X86_64.srcW L E₁.perm (t := o) (k := 16 * 1) (by omega))
      dO (L.w_w (.inr (by omega)) (by decide) (by omega)) (E₁.perm.wC (by omega)) rdi rsi rdx rcx r8 r9
  have fZ := Proof.Cmac.frame_store2 (m := (t.mem.writeW (W + BitVec.ofNat 64 112)
    (t.mem.readW (W + BitVec.ofNat 64 96) 64)).writeW (W + BitVec.ofNat 64 112 + BitVec.ofNat 64 8)
    (t.mem.readW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 64)) (W + BitVec.ofNat 64 o) 0 0
  have fC := Proof.Cmac.frame_store2 (m := t.mem) (W + BitVec.ofNat 64 112)
    (t.mem.readW (W + BitVec.ofNat 64 96) 64) (t.mem.readW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 64)
  have f₁ : Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩] t.mem t₁.mem := by
    rw [hm₁, Proof.Cmac.zero2]
    exact (fC.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans
      (fZ.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp)
  have hb₁ : bytesAt t₁.mem (W + BitVec.ofNat 64 112) 16 = bytesAt t.mem (W + BitVec.ofNat 64 96) 16 := by
    rw [hm₁, Proof.Cmac.zero2, Proof.AesGcm.X86_64.bytesAt_frame fZ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dO.symm) (by decide),
      Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]
  have hz₁ : Spec.Gcm.blockAt t₁.mem (W + BitVec.ofNat 64 o) = 0 := by rw [hm₁]; exact VG.Proof.AesGcmSiv.X86_64.blockAt_zero2 _ _
  have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (W + BitVec.ofNat 64 248) R =
      Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R :=
    VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by omega)) (by decide) (by omega))
      (by rcases hR with h | h <;> subst h <;> decide)
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_
  have fc := P.frame
  rw [E₁.rsp, Nat.mul_one] at fc
  refine ⟨E₁.of_saved P.saved P.rd P.wr, by rw [P.rd, hrd₁], by rw [P.wr, hwr₁],
    fun r hr => by rw [P.saved r hr, hg₁ r hr],
    (f₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp).trans (fc.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp), ?_⟩
  have hout := P.out
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
  rw [Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
    show Spec.GcmSiv.aesWith R (bytesAt t₁.mem (W + BitVec.ofNat 64 248) (16 * (R + 1))) =
      Spec.GcmSiv.ctxCiph t₁.mem (W + BitVec.ofNat 64 248) R from rfl, ek₁, hb₁]

end VG.Proof.AesGcmSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86_64.Crypt`. -/
section

/-!
# AES-GCM-SIV on x86-64: counter mode (`crypt`)

Untrusted: everything here is checked by Lean. The counter block at
`W + 96` starts as the tag with the top bit of its last byte set; each block
of the data is encrypted in place by `vg_aes_ctr32` from a copy of it at
`W + 112`, after which its first word is incremented (`cryptBlock_ok`); the
last bytes are XORed with the keystream block, computed at `W + 128`
(`cryptTail_ok`). `crypt_ok`: the data becomes `ctr` of it (RFC 8452 §4).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.AesGcm.X86_64 (GcmImpl CtrCall CtrPost ctr_call toNat_ofNat_of_lt)

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

theorem CtrSt.block {W : Addr} {icb : List Byte} {j : Nat} {m : Mem} (h : VG.Proof.AesGcmSiv.X86_64.CtrSt W icb j m) :
    bytesAt m (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.counterBlock icb j := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    h.word, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, h.rest]

/-- Bytes of a buffer outside the part a frame may also change. -/
theorem frame_outside {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {len a n : Nat}
    (hrs : ∀ r ∈ rs, r = ⟨P + BitVec.ofNat 64 a, n⟩ ∨ (⟨P, len⟩ : Region).Disjoint r) (hlen : len < 2 ^ 64)
    (han : a + n ≤ len) : ∀ p < len, (p < a ∨ a + n ≤ p) → m' (P + BitVec.ofNat 64 p) = m (P + BitVec.ofNat 64 p) :=
  fun p hp ho => hf _ fun r hr hc => by
    rcases hrs r hr with rfl | hd
    · exact Offset.disjoint P (d := p) (n := 1) (by omega) (by omega) (by omega) _ (Region.contains_self _ _) hc
    · exact hd _ (Offset.contains_base P (show p + 1 ≤ len by omega) (by omega)) hc

/-- What counter mode writes: the counter block, its copy and the block at
`W + 128`, `vg_aes_ctr32`'s working space, the stack below `SP` and the data. -/
abbrev cryR (W SP D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 96, 48⟩, ⟨W + BitVec.ofNat 64 1768, 2048⟩, below SP 8, ⟨D, n⟩]

/-- What a block of counter mode leaves, from `t`. -/
structure BlockPost (K W SP : Addr) (D : Addr) (n : Nat) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte)
    (b j : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  rbp : t'.gpr .rbp = t.gpr .rbp
  r12 : t'.gpr .r12 = D + BitVec.ofNat 64 (16 * (j + 1))
  rbx : t'.gpr .rbx = BitVec.ofNat 64 (b - (j + 1))
  zf : t'.zf = some (decide (b - (j + 1) = 0))
  ctr : VG.Proof.AesGcmSiv.X86_64.CtrSt W icb (j + 1) t'.mem
  data : bytesAt t'.mem D n = GcmSiv.ctrPart ciph icb x (16 * (j + 1))
  frame : Frame (VG.Proof.AesGcmSiv.X86_64.cryR W SP D n) t.mem t'.mem

/-- The arguments of a block's call. -/
theorem blkArgs_ok {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n t.mem) {j : Nat} (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j)) :
    ∃ t₁ : State, runBlock isa
      (copy16 cmO ccO ++ ptr .rdi .r15 skO ++ ctrArgs ++ ([.mov .rcx (.reg .r12)] : List Instr)) t = some t₁ ∧
      t₁.mem = (t.mem.writeW (W + BitVec.ofNat 64 112) (t.mem.readW (W + BitVec.ofNat 64 96) 64)).writeW
        (W + BitVec.ofNat 64 112 + BitVec.ofNat 64 8) (t.mem.readW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 64) ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 248 ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧
      t₁.gpr .rdx = W + BitVec.ofNat 64 112 ∧ t₁.gpr .rcx = D + BitVec.ofNat 64 (16 * j) ∧
      t₁.gpr .r8 = BitVec.ofNat 64 1 ∧ t₁.gpr .r9 = W + BitVec.ofNat 64 1768 ∧
      (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have hw := L.ww
  have rR := S.rounds
  have rR' := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  have r₀ := E.perm.wR (show 96 + 8 ≤ 3816 by decide)
  have r₈ := E.perm.wR (show 104 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (show 112 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 120 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [copy16, ctrArgs, h15, rR, rR', r₀, r₈, w₀, w₈], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc]
  all_goals try (simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15, rR, h12]; done)
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

theorem cryptBlock_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State}
    (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {N A D : Addr} {al n : Nat} (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n t.mem) (hD : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t D n)
    (hDw : Covers [⟨D, n⟩] t.wr) {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = n) {b j : Nat}
    (hb : 16 * b ≤ n) (hj : j < b) (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j))
    (hbx : t.gpr .rbx = BitVec.ofNat 64 (b - j)) (C : VG.Proof.AesGcmSiv.X86_64.CtrSt W icb j t.mem)
    (hx : bytesAt t.mem D n = GcmSiv.ctrPart ciph icb x (16 * j))
    (hc : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R = ciph) :
    WP isa (cryptBlock v.callees) t (VG.Proof.AesGcmSiv.X86_64.BlockPost K W SP D n ciph icb x b j t) := by
  have h15 := E.r15
  have hw := L.ww
  have hn := hD.lt
  have rR := S.rounds
  have rR' := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  have r₀ := E.perm.wR (show 96 + 8 ≤ 3816 by decide)
  have r₈ := E.perm.wR (show 104 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (show 112 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 120 + 8 ≤ 3816 by decide)
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcmSiv.X86_64.blkArgs_ok L E S h12
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := E.of_saved hg₁ hrd₁ hwr₁
  have hQ : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t₁ (D + BitVec.ofNat 64 (16 * j)) (16 * 1) := (hD.slice (by omega)).of_eq hrd₁ hwr₁
  have cc : CtrCall t₁ (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 112) (D + BitVec.ofNat 64 (16 * j))
      (W + BitVec.ofNat 64 1768) R 1 :=
    VG.Proof.AesGcmSiv.X86_64.cargs L E₁ hR (VG.Proof.AesGcmSiv.X86_64.keyS L E₁.perm) (c := 112) (by decide) (VG.Proof.AesGcmSiv.X86_64.srcBuf hQ) (hQ.w.sub_right (Lay.wSub (by decide)))
      (hQ.w.sub_right (Lay.wSub (show 248 + 240 ≤ 3816 by decide))).symm
      (by rw [hwr₁]; exact Proof.AesGcm.X86_64.covers_off hDw (by omega) hn) rdi rsi rdx rcx r8 r9
  -- What the copy changed.
  have f₁ : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have dD : ∀ q ∈ [(⟨W + BitVec.ofNat 64 112, 16⟩ : Region)], (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact hD.w.sub_right (Lay.wSub (by decide))
  have hcb : bytesAt t₁.mem (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.counterBlock icb j := by
    rw [hm₁, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split,
      C.block]
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (W + BitVec.ofNat 64 248) R = ciph := by
    rw [VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by rcases hR with h | h <;> subst h <;> decide), hc]
  have hx₁ : bytesAt t₁.mem D n = GcmSiv.ctrPart ciph icb x (16 * j) := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame f₁ dD (Nat.le_of_lt hn), hx]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  refine WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_
  have fc := P.frame
  rw [E₁.rsp, Nat.mul_one] at fc
  have hout := P.out
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    VG.Proof.AesGcmSiv.X86_64.ctr32_single, List.cons.injEq, and_true] at hout
  have hb₂ : bytesAt t₂.mem (D + BitVec.ofNat 64 (16 * j)) 16 =
      Spec.Cmac.xor (bytesAt t₁.mem (D + BitVec.ofNat 64 (16 * j)) 16) (GcmSiv.ksBlock ciph icb j) := by
    rw [Proof.Cmac.bytesAt_blockAt, hout, VG.Proof.AesGcmSiv.X86_64.toBytes_xor, ← Proof.Cmac.bytesAt_blockAt, Spec.Gcm.blockAt,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
      show Spec.GcmSiv.aesWith R (bytesAt t₁.mem (W + BitVec.ofNat 64 248) (16 * (R + 1))) =
        Spec.GcmSiv.ctxCiph t₁.mem (W + BitVec.ofNat 64 248) R from rfl, hc₁, hcb]
  have hk : (GcmSiv.ksBlock ciph icb j).length = 16 := by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  have hx₂ : bytesAt t₂.mem D n = GcmSiv.ctrPart ciph icb x (16 * j + 16) := by
    rw [← hxl] at hx₁ ⊢
    refine GcmSiv.ctrPart_step ciph icb x D (by decide) hk hx₁ ?_ (by rw [hb₂, List.take_of_length_le (by omega)])
    rw [hxl]
    refine VG.Proof.AesGcmSiv.X86_64.frame_outside fc (fun q hq => ?_) hn (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))
    · exact .inl rfl
    · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))
    · exact .inr hD.stk.symm
  have E₂ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₂ := E₁.of_saved P.saved P.rd P.wr
  have h15₂ := E₂.r15
  have c₀ := E₂.perm.wR (show 96 + 4 ≤ 3816 by decide)
  have c₁ := E₂.perm.wW (show 96 + 4 ≤ 3816 by decide)
  have h12₂ : t₂.gpr .r12 = D + BitVec.ofNat 64 (16 * j) := by rw [P.saved _ (by decide), hg₁ _ (by decide), h12]
  have hbx₂ : t₂.gpr .rbx = BitVec.ofNat 64 (b - j) := by rw [P.saved _ (by decide), hg₁ _ (by decide), hbx]
  have sw : ∀ y : BitVec 32, (BitVec.setWidth 32 (BitVec.setWidth 64 y) : BitVec 32) = y := fun y => by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  -- What the first two pieces changed.
  have f₂' : Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨D + BitVec.ofNat 64 (16 * j), 16⟩, ⟨W + BitVec.ofNat 64 1768, 2048⟩,
      below SP 8] t.mem t₂.mem :=
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans fc
  have f₂ : Frame (VG.Proof.AesGcmSiv.X86_64.cryR W SP D n) t.mem t₂.mem := f₂'.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 96, 48⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have dC : ∀ {d k : Nat}, 96 ≤ d → d + k ≤ 112 →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨D + BitVec.ofNat 64 (16 * j), 16⟩,
        ⟨W + BitVec.ofNat 64 1768, 2048⟩, below SP 8], (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact ((hD.w.sub_left (Offset.sub_base D (show 16 * j + 16 ≤ n by omega))).sub_right
          (Lay.wSub (by omega))).symm
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm
  have w₂ : t₂.mem.readW (W + BitVec.ofNat 64 96) 32 = t.mem.readW (W + BitVec.ofNat 64 96) 32 :=
    f₂'.readW (Region.contains_self _ _) (dC (k := 4) (Nat.le_refl _) (by decide)) (by decide)
  have r₂ : bytesAt t₂.mem (W + BitVec.ofNat 64 100) 12 = bytesAt t.mem (W + BitVec.ofNat 64 100) 12 :=
    Proof.AesGcm.X86_64.bytesAt_frame f₂' (dC (by decide) (by decide)) (by decide)
  have fw : ∀ v : BitVec 32, Frame [⟨W + BitVec.ofNat 64 96, 4⟩] t₂.mem (t₂.mem.writeW (W + BitVec.ofNat 64 96) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨_, by srun [h15₂, c₀, c₁, h12₂, hbx₂], ?_⟩
  refine ⟨E₂.keep (fun r hr => ?_) rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [gpr_arithFlags, gpr_setReg, mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg,
    wr_arithFlags, wr_setReg, zf_arithFlags, zf_setReg, ite_true, ite_false, reduceCtorEq, sw]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp
  · rw [P.rd, hrd₁]
  · rw [P.wr, hwr₁]
  · rw [P.saved _ (by decide), hg₁ _ (by decide)]
  · rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, show 16 * j + 16 = 16 * (j + 1) by omega]
  · rw [Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega), Nat.sub_sub]
  · rw [Proof.AesGcm.X86_64.sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · refine ⟨?_, ?_⟩
    · rw [Mem.readW_writeW_self32, w₂, C.word]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · rw [Proof.AesGcm.X86_64.bytesAt_frame (fw _) (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
          (by decide), r₂, C.rest]
  · rw [Proof.AesGcm.X86_64.bytesAt_frame (fw _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hD.w.sub_right (Lay.wSub (by decide))) (Nat.le_of_lt hn), hx₂,
      show 16 * j + 16 = 16 * (j + 1) by omega]
  · exact f₂.writeW (List.mem_cons_self ..) _ (Offset.contains W (Nat.le_refl _) (by decide) (by omega))

/-- The slots, after code that writes only parts of `W` apart from them, the
stack below `SP` and a buffer apart from `W`. -/
theorem Slots.of_frame {W : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {m m' : Mem}
    {rs : List Region} (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint r) : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n m' := by
  have k (d : Nat) (hd' : 200 ≤ d ∧ d + 8 ≤ 248) :
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
    hf.readW (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub W (by omega) (by omega))) (by decide)
  exact ⟨by rw [k 200 (by decide)]; exact S.rounds, by rw [k 208 (by decide)]; exact S.nonce,
    by rw [k 216 (by decide)]; exact S.aad, by rw [k 224 (by decide)]; exact S.alen,
    by rw [k 232 (by decide)]; exact S.data, by rw [k 240 (by decide)]; exact S.len⟩

theorem slots_cryR {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {s : State} {D : Addr} {n : Nat} (hD : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s D n) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.cryR W SP D n, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm
  · exact (hD.w.sub_right (Lay.wSub (by decide))).symm

/-- The encryption key's schedule misses what counter mode writes. -/
theorem key_cryR {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {s : State} {D : Addr} {n : Nat} (hD : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s D n) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.cryR W SP D n, (⟨W + BitVec.ofNat 64 248, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm
  · exact (hD.w.sub_right (Lay.wSub (by decide))).symm

/-- What the whole blocks of counter mode leave, from `t`. -/
structure BlocksPost (K W SP : Addr) (D : Addr) (n : Nat) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte)
    (b : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  rbp : t'.gpr .rbp = t.gpr .rbp
  r12 : t'.gpr .r12 = D + BitVec.ofNat 64 (16 * b)
  ctr : VG.Proof.AesGcmSiv.X86_64.CtrSt W icb b t'.mem
  data : bytesAt t'.mem D n = GcmSiv.ctrPart ciph icb x (16 * b)
  frame : Frame (VG.Proof.AesGcmSiv.X86_64.cryR W SP D n) t.mem t'.mem

theorem blocks_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State}
    (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {N A D : Addr} {al n : Nat} (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n t.mem) (hD : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t D n)
    (hDw : Covers [⟨D, n⟩] t.wr) {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = n) {b : Nat}
    (hb : 16 * b ≤ n) (hb1 : 1 ≤ b) (h12 : t.gpr .r12 = D) (hbx : t.gpr .rbx = BitVec.ofNat 64 b)
    (C : VG.Proof.AesGcmSiv.X86_64.CtrSt W icb 0 t.mem) (hx : bytesAt t.mem D n = x)
    (hc : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R = ciph) :
    WP isa (.loop (cryptBlock v.callees) .ne) t (VG.Proof.AesGcmSiv.X86_64.BlocksPost K W SP D n ciph icb x b t) := by
  refine WP.loop (M := isa) (body := cryptBlock v.callees) (c := .ne)
    (fun (m : Nat) (t' : State) => ∃ j, m = b - j ∧ j < b ∧ VG.Proof.AesGcmSiv.X86_64.BlocksPost K W SP D n ciph icb x j t t' ∧
      t'.gpr .rbx = BitVec.ofNat 64 (b - j)) ?_ (b - 0) t
    ⟨0, rfl, hb1, ⟨E, rfl, rfl, rfl, by rw [h12, Nat.mul_zero, BitVec.add_zero], C,
      by rw [hx, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩, by rw [hbx, Nat.sub_zero]⟩
  rintro m t' ⟨j, rfl, hj, P, hbx'⟩
  have hc' : Spec.GcmSiv.ctxCiph t'.mem (W + BitVec.ofNat 64 248) R = ciph := by
    rw [VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame P.frame (VG.Proof.AesGcmSiv.X86_64.key_cryR L hD) (by rcases hR with h | h <;> subst h <;> decide), hc]
  refine WP.mono (VG.Proof.AesGcmSiv.X86_64.cryptBlock_ok v L hR P.env (S.of_frame P.frame (VG.Proof.AesGcmSiv.X86_64.slots_cryR L hD)) (hD.of_eq P.rd P.wr)
    (by rw [P.wr]; exact hDw) hxl hb hj P.r12 hbx' P.ctr P.data hc') fun t'' Q => ?_
  have P' : VG.Proof.AesGcmSiv.X86_64.BlocksPost K W SP D n ciph icb x (j + 1) t t'' :=
    ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.rbp.trans P.rbp, Q.r12, Q.ctr, Q.data, P.frame.trans Q.frame⟩
  by_cases he : b - (j + 1) = 0
  · left
    have hjb : j + 1 = b := by omega
    exact ⟨(VG.Proof.AesGcmSiv.X86_64.eval_ne Q.zf).trans (by simp [he]), hjb ▸ P'⟩
  · right
    exact ⟨(VG.Proof.AesGcmSiv.X86_64.eval_ne Q.zf).trans (by simp [he]), b - (j + 1), by omega, j + 1, rfl, by omega, P', Q.rbx⟩

/-- What the last bytes of counter mode leave, from `t`. -/
structure TailPost (K W SP : Addr) (D : Addr) (n : Nat) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte)
    (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  data : bytesAt t'.mem D n = GcmSiv.ctrPart ciph icb x n
  frame : Frame (VG.Proof.AesGcmSiv.X86_64.cryR W SP D n) t.mem t'.mem

theorem cryptTail_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State}
    (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {N A D : Addr} {al n : Nat} (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n t.mem) (hD : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t D n)
    (hDw : Covers [⟨D, n⟩] t.wr) {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = n) {b r : Nat}
    (hn : n = 16 * b + r) (hr1 : 1 ≤ r) (hr : r < 16) (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * b))
    (hbp : t.gpr .rbp = BitVec.ofNat 64 r) (C : VG.Proof.AesGcmSiv.X86_64.CtrSt W icb b t.mem)
    (hx : bytesAt t.mem D n = GcmSiv.ctrPart ciph icb x (16 * b))
    (hc : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R = ciph) :
    WP isa (cryptTail v.callees) t (VG.Proof.AesGcmSiv.X86_64.TailPost K W SP D n ciph icb x t) := by
  have hn' := hD.lt
  refine VG.Proof.AesGcmSiv.X86_64.seq_assoc ?_
  show WP isa (.seq (tag v.callees 128) _) t _
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.tag_ok v L hR E S (o := 128) (by decide)) fun t₂ T => ?_)
  have fT := T.frame
  have dT : ∀ q ∈ VG.Proof.AesGcmSiv.X86_64.tagR W SP 128, (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hD.w.sub_right (Lay.wSub (by decide))
    · exact hD.w.sub_right (Lay.wSub (by decide))
    · exact hD.w.sub_right (Lay.wSub (by decide))
    · exact hD.stk.symm
  have hx₂ : bytesAt t₂.mem D n = GcmSiv.ctrPart ciph icb x (16 * b) := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame fT dT (Nat.le_of_lt hn'), hx]
  have hks : bytesAt t₂.mem (W + BitVec.ofNat 64 128) 16 = GcmSiv.ksBlock ciph icb b := by
    rw [T.out, hc, C.block]
  have h15₂ := T.env.r15
  have h12₂ : t₂.gpr .r12 = D + BitVec.ofNat 64 (16 * b) := by rw [T.saved _ (by decide), h12]
  have hbp₂ : t₂.gpr .rbp = BitVec.ofNat 64 r := by rw [T.saved _ (by decide), hbp]
  obtain ⟨t₃, run₃, rdi₃, rsi₃, rcx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃ : State, runBlock isa
      (([.mov .rdi (.reg .r12)] : List Instr) ++ ptr .rsi .r15 bO ++ ([.mov .rcx (.reg .rbp)] : List Instr)) t₂ =
        some t₃ ∧
      t₃.gpr .rdi = D + BitVec.ofNat 64 (16 * b) ∧ t₃.gpr .rsi = W + BitVec.ofNat 64 128 ∧
      t₃.gpr .rcx = BitVec.ofNat 64 r ∧ (∀ q, q ≠ .rdi → q ≠ .rsi → q ≠ .rcx → t₃.gpr q = t₂.gpr q) ∧
      t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₂, h12₂, hbp₂]; done)
    · intro q h₁ h₂ h₃; simp only [gpr_arithFlags, gpr_setReg, h₁, h₂, h₃, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have lp : Proof.AesGcm.X86_64.LoopPre t₃ (W + BitVec.ofNat 64 128) (D + BitVec.ofNat 64 (16 * b)) r :=
    ⟨rsi₃, rdi₃, rcx₃, hr1, by omega, by rw [hrd₃, hwr₃]; exact T.env.perm.wCR (by omega),
      by rw [hwr₃, T.wr]; exact Proof.AesGcm.X86_64.covers_off hDw (by omega) hn',
      ((hD.w.sub_left (Offset.sub_base D (show 16 * b + r ≤ n by omega))).sub_right (Lay.wSub (by omega))).symm⟩
  refine WP.mono (Proof.AesGcm.X86_64.xorLoop_ok t₃ lp) fun t₄ ⟨hm₄, hg₄, hrd₄, hwr₄⟩ => ?_
  rw [hm₃] at hm₄
  have hl : (Proof.AesGcm.X86_64.xorBytes t₂.mem (D + BitVec.ofNat 64 (16 * b)) (W + BitVec.ofNat 64 128) r).length = r := by
    simp [Proof.AesGcm.X86_64.xorBytes, Proof.Cmac.bytesAt_length]
  have fw := Proof.AesGcm.X86_64.writeBytes_frame' t₂.mem (q := D + BitVec.ofNat 64 (16 * b)) hl
  rw [← hm₄] at fw
  have hk : (GcmSiv.ksBlock ciph icb b).length = 16 := by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  refine ⟨T.env.keep (fun q hq => ?_) (by rw [hrd₄, hrd₃]) (by rw [hwr₄, hwr₃]),
    by rw [hrd₄, hrd₃, T.rd], by rw [hwr₄, hwr₃, T.wr], ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;>
      rw [hg₄ _ (by decide) (by decide) (by decide), hg₃ _ (by decide) (by decide) (by decide)]
  · have hb' : bytesAt t₄.mem (D + BitVec.ofNat 64 (16 * b)) r = Spec.Cmac.xor
        (bytesAt t₂.mem (D + BitVec.ofNat 64 (16 * b)) r) ((GcmSiv.ksBlock ciph icb b).take r) := by
      have e := Proof.AesGcm.X86_64.bytesAt_writeBytes_self t₂.mem (D + BitVec.ofNat 64 (16 * b))
        (Proof.AesGcm.X86_64.xorBytes t₂.mem (D + BitVec.ofNat 64 (16 * b)) (W + BitVec.ofNat 64 128) r) (by omega)
      rw [hl] at e
      have hs := Proof.Cmac.bytesAt_add t₂.mem (W + BitVec.ofNat 64 128) r (16 - r)
      rw [show r + (16 - r) = 16 by omega, hks] at hs
      rw [hm₄, e, Proof.AesGcm.X86_64.xorBytes, hs, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rfl
    have := GcmSiv.ctrPart_step ciph icb x D (i := b) (n := r) (by omega) hk (by rw [hxl]; exact hx₂)
      (VG.Proof.AesGcmSiv.X86_64.frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; exact hn') (by omega)) hb'
    rwa [hxl, ← hn] at this
  · refine (fT.sub fun q hq => ?_).trans (fw.sub fun q hq => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 96, 48⟩, by simp, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 96, 48⟩, by simp, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega)⟩

/-- What `crypt` leaves, from `t`. -/
structure CryptPost (K W SP : Addr) (R : Nat) (D : Addr) (n : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (VG.Proof.AesGcmSiv.X86_64.cryR W SP D n) t.mem t'.mem
  data : bytesAt t'.mem D n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
    (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n)

/-- The start of `crypt`: the counter block from the tag, and the data's
whole blocks and last bytes. -/
theorem cryptHead_ok {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n t.mem) (hD : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t D n) :
    ∃ t₁ : State, runBlock isa
      [.mov .rax (.mem (at_ .r15 tagO)), .store (at_ .r15 cmO) .rax, .mov .rax (.mem (at_ .r15 (tagO + 8))),
        .movImm64 .rcx 0x8000000000000000, .alu .or .rax (.reg .rcx), .store (at_ .r15 (cmO + 8)) .rax,
        .mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov .rbx (.reg .rbp),
        .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)] t = some t₁ ∧
      t₁.mem = (t.mem.writeW (W + BitVec.ofNat 64 96) (t.mem.readW W 64)).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8)
        (t.mem.readW (W + BitVec.ofNat 64 8) 64 ||| 0x8000000000000000#64) ∧
      t₁.gpr .r12 = D ∧ t₁.gpr .rbp = BitVec.ofNat 64 (n % 16) ∧ t₁.gpr .rbx = BitVec.ofNat 64 (n / 16) ∧
      t₁.zf = some (decide (n / 16 = 0)) ∧ (∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → t₁.gpr r = t.gpr r) ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have hw := L.ww
  have hn := hD.lt
  have rT₀ : InRegions (t.rd ++ t.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3816 by decide)
  have rT₈ := E.perm.wR (show 8 + 8 ≤ 3816 by decide)
  have rD := E.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (show 96 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 104 + 8 ≤ 3816 by decide)
  have sD := S.data
  have sL := S.len
  have hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 n)
  rw [toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  refine ⟨_, by srun [h15, rT₀, rT₈, rD, rL, w₀, w₈], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc]; rfl
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sD]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sL, hand]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sL,
      Proof.AesGcm.X86_64.shr4 _ hn]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
      reduceCtorEq, sL, Proof.AesGcm.X86_64.shr4 _ hn]
    rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]
  · intro r hr h₁ h₂ h₃; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    any_goals exact absurd rfl h₁
    any_goals exact absurd rfl h₂
    any_goals exact absurd rfl h₃
    all_goals simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

theorem crypt_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State}
    (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {N A D : Addr} {al n : Nat} (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n t.mem) (hD : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t D n)
    (hDw : Covers [⟨D, n⟩] t.wr) :
    WP isa (crypt v.callees) t (VG.Proof.AesGcmSiv.X86_64.CryptPost K W SP R D n t) := by
  have h15 := E.r15
  have hw := L.ww
  have hn := hD.lt
  have rT₀ : InRegions (t.rd ++ t.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3816 by decide)
  have rT₈ := E.perm.wR (show 8 + 8 ≤ 3816 by decide)
  have rD := E.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (show 96 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 104 + 8 ≤ 3816 by decide)
  have sD := S.data
  have sL := S.len
  have hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 n)
  rw [toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  obtain ⟨t₁, run₁, hm₁, h12₁, hbp₁, hbx₁, hzf₁, hg₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcmSiv.X86_64.cryptHead_ok L E S hD
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem D n).length = n := Proof.Cmac.bytesAt_length _ _ _
  have f₁ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have dD : ∀ q ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact hD.w.sub_right (Lay.wSub (by decide))
  have hx₁ : bytesAt t₁.mem D n = bytesAt t.mem D n := Proof.AesGcm.X86_64.bytesAt_frame f₁ dD (Nat.le_of_lt hn)
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (W + BitVec.ofNat 64 248) R =
      Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R :=
    VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by rcases hR with h | h <;> subst h <;> decide)
  have hicb : bytesAt t₁.mem (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.initialCounter (bytesAt t.mem W 16) := by
    rw [hm₁, Proof.Cmac.bytesAt_store2, ← GcmSiv.initialCounter_words, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
      ← Proof.Cmac.bytesAt_split]
  have h4 := Proof.Cmac.bytesAt_add t₁.mem (W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc] at h4
  have C₀ : VG.Proof.AesGcmSiv.X86_64.CtrSt W (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) 0 t₁.mem := by
    refine ⟨?_, ?_⟩
    · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have S₁ := S.of_frame f₁ (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
  have fC : ∀ q ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)], ∃ q' ∈ VG.Proof.AesGcmSiv.X86_64.cryR W SP D n, Region.Sub q q' := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨⟨W + BitVec.ofNat 64 96, 48⟩, by simp, Offset.sub W (by decide) (by decide)⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The whole blocks.
  have hmid : WP isa (.ite .e (.block []) (.loop (cryptBlock v.callees) .ne)) t₁
      (VG.Proof.AesGcmSiv.X86_64.BlocksPost K W SP D n (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n) (n / 16) t₁) := by
    refine WP.ite (decide (n / 16 = 0)) (VG.Proof.AesGcmSiv.X86_64.eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨E₁, rfl, rfl, rfl, by rw [h12₁, Nat.mul_zero, BitVec.add_zero], C₀,
        by rw [Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁], Frame.refl _ _⟩
    · have h0 : n / 16 ≠ 0 := by simpa using hf
      exact VG.Proof.AesGcmSiv.X86_64.blocks_ok v L hR E₁ S₁ (hD.of_eq hrd₁ hwr₁) (by rw [hwr₁]; exact hDw) hxl (by omega) (by omega) h12₁
        hbx₁ C₀ hx₁ hc₁
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  have hbp₂ : t₂.gpr .rbp = BitVec.ofNat 64 (n % 16) := B.rbp.trans hbp₁
  obtain ⟨t₃, run₃, hzf₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃ : State, runBlock isa [.alu .test .rbp (.reg .rbp)] t₂ = some t₃ ∧
      t₃.zf = some (decide (n % 16 = 0)) ∧ (∀ r, t₃.gpr r = t₂.gpr r) ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, hbp₂]
      rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]
    · intro r; rfl
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have E₃ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₃ := B.env.keep (fun r _ => hg₃ r) hrd₃ hwr₃
  refine WP.ite (decide (n % 16 = 0)) (VG.Proof.AesGcmSiv.X86_64.eval_e hzf₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨E₃, by rw [hrd₃, B.rd, hrd₁], by rw [hwr₃, B.wr, hwr₁],
      by rw [hm₃]; exact (f₁.sub fC).trans B.frame, ?_⟩
    rw [hm₃, B.data, show 16 * (n / 16) = n by omega, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : n % 16 ≠ 0 := by simpa using hf
    have F₃ : Frame (VG.Proof.AesGcmSiv.X86_64.cryR W SP D n) t₁.mem t₃.mem := by rw [hm₃]; exact B.frame
    have hc₃ : Spec.GcmSiv.ctxCiph t₃.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R := by
      rw [VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame F₃ (VG.Proof.AesGcmSiv.X86_64.key_cryR L hD) (by rcases hR with h | h <;> subst h <;> decide), hc₁]
    refine WP.mono (VG.Proof.AesGcmSiv.X86_64.cryptTail_ok v L hR E₃ (S₁.of_frame F₃ (VG.Proof.AesGcmSiv.X86_64.slots_cryR L hD))
      (hD.of_eq (by rw [hrd₃, B.rd, hrd₁]) (by rw [hwr₃, B.wr, hwr₁])) (by rw [hwr₃, B.wr, hwr₁]; exact hDw) hxl
      (b := n / 16) (r := n % 16) (by omega) (by omega) (by omega) (by rw [hg₃, B.r12]) (by rw [hg₃, hbp₂])
      (by rw [hm₃]; exact B.ctr) (by rw [hm₃]; exact B.data) hc₃) fun t₄ T => ?_
    refine ⟨T.env, by rw [T.rd, hrd₃, B.rd, hrd₁], by rw [T.wr, hwr₃, B.wr, hwr₁],
      ((f₁.sub fC).trans F₃).trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn`. -/
section

/-!
# AES-GCM-SIV on x86-64: comparing the tags, and `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`

Untrusted: everything here is checked by Lean. `cmp` stores at `W + 192`
whether the received tag at `W` equals the computed one at `W + 128`,
without a branch (`cmp_ok`); `mask` ANDs every byte of the data with
`0 − ok`, leaving it if the tags are equal and zeroing it if not
(`mask_ok`). `recv` copies the received tag to `W` (`recv_ok`), and
`tagOut` the computed one from `W` to `tag` (`tagOut_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc)
open VG.Proof.AesGcm.X86_64 (toNat_ofNat_of_lt in_off)

/-- `ok` from the XOR of the tags' words: 1 if both are equal, 0 if not. -/
theorem ok_val (a b c d : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 32 0#64 + BitVec.setWidth 32
      (BitVec.ofBool (decide ((a ^^^ b ||| c ^^^ d).toNat < (1#64).toNat)))) =
      if a = b ∧ c = d then 1#64 else 0#64 := by
  by_cases h : a = b ∧ c = d
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
    have : decide ((a ^^^ b ||| c ^^^ d).toNat < (1#64).toNat) = false := decide_eq_false fun hl => h (by
      have e : (a ^^^ b ||| c ^^^ d) = 0#64 := BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_ofNat]; rw [BitVec.toNat_ofNat] at hl; omega)
      rw [BitVec.or_eq_zero_iff] at e
      exact ⟨BitVec.xor_eq_zero_iff.mp e.1, BitVec.xor_eq_zero_iff.mp e.2⟩)
    rw [this]
    decide

theorem le8_inj {a b : BitVec 64} (h : Proof.Cmac.le8 a = Proof.Cmac.le8 b) : a = b :=
  BitVec.eq_of_toNat_eq (by rw [← GcmSiv.leNat_le8, h, GcmSiv.leNat_le8])

/-- Two blocks in memory are equal when their words are. -/
theorem bytes16_eq (m : Mem) (p q : Addr) :
    bytesAt m p 16 = bytesAt m q 16 ↔
      m.readW p 64 = m.readW q 64 ∧ m.readW (p + BitVec.ofNat 64 8) 64 = m.readW (q + BitVec.ofNat 64 8) 64 := by
  rw [Proof.Cmac.bytesAt_split m p, Proof.Cmac.bytesAt_split m q, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW]
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [Proof.Cmac.length_le8, Proof.Cmac.length_le8])
    exact ⟨VG.Proof.AesGcmSiv.X86_64.le8_inj h₁, VG.Proof.AesGcmSiv.X86_64.le8_inj h₂⟩
  · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]

theorem cmp_ok {K W SP : Addr} {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) :
    ∃ t' : State, runBlock isa cmp t = some t' ∧
      t'.mem = t.mem.writeW (W + BitVec.ofNat 64 192)
        (if bytesAt t.mem W 16 = bytesAt t.mem (W + BitVec.ofNat 64 128) 16 then 1#64 else 0#64) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have r₀ : InRegions (t.rd ++ t.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3816 by decide)
  have r₈ := E.perm.wR (show 8 + 8 ≤ 3816 by decide)
  have u₀ := E.perm.wR (show 128 + 8 ≤ 3816 by decide)
  have u₈ := E.perm.wR (show 136 + 8 ≤ 3816 by decide)
  have wo := E.perm.wW (show 192 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [Impl.AesGcmSiv.X86_64.cmp, h15, r₀, r₈, u₀, u₈, wo], ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, gpr_setReg, gpr_arithFlags, cf_arithFlags, cf_setReg,
      ite_true, ite_false, reduceCtorEq]
    have hb := VG.Proof.AesGcmSiv.X86_64.bytes16_eq t.mem W (W + BitVec.ofNat 64 128)
    rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc] at hb
    simp only [VG.Proof.AesGcmSiv.X86_64.ok_val, hb]
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

abbrev maskBody : List Instr :=
  [.movzx8 .rax maskByte, .alu .and .rax (.reg .r11), .store8 maskByte .rax, .alu .add .r10 (imm 1),
    .alu .cmp .r10 (.reg .rbp)]

theorem setWidth8_and (a : Byte) (k : BitVec 64) : ((a.setWidth 64 &&& k : BitVec 64)).setWidth 8 = a &&& k.setWidth 8 := by
  ext j hj; simp

theorem maskStep_ok (s : State) {D : Addr} {i n : Nat} (hd : s.gpr .r12 = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr .rbp = BitVec.ofNat 64 n)
    (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa VG.Proof.AesGcmSiv.X86_64.maskBody s = some s' ∧
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i) (s.mem (D + BitVec.ofNat 64 i) &&& (s.gpr .r11).setWidth 8) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₁ := Proof.AesGcm.X86_64.ea_idx s .r12 hd hi
  have wr' : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨x, hx, hc⟩ := w; exact ⟨x, List.mem_append_right _ hx, hc⟩
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, BitVec.reduceSignExtend,
      VG.Proof.AesGcmSiv.X86_64.maskBody, maskByte, imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8,
      State.store8, State.ea, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg,
      mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, e₁, w, wr']
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
      VG.Proof.AesGcmSiv.X86_64.setWidth8_and]
  · simp [gpr_setReg, hi]
  · simp [hi, hn]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

/-- Byte `i` at `D`, not yet written. -/
theorem dst_kept {m : Mem} {D : Addr} {i : Nat} (hi : i < 2 ^ 64) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.lt_irrefl,
    ite_false]

/-- The first `i` bytes at `D`, each ANDed with `k`. -/
abbrev maskBytes (m : Mem) (D : Addr) (k : Byte) (i : Nat) : List Byte := (bytesAt m D i).map (· &&& k)

theorem maskLoop_ok (s : State) {D : Addr} {n : Nat} (hd : s.gpr .r12 = D) (hn : s.gpr .rbp = BitVec.ofNat 64 n)
    (hi : s.gpr .r10 = BitVec.ofNat 64 0) (hn1 : 1 ≤ n) (hnl : n < 2 ^ 64) (hw : Covers [⟨D, n⟩] s.wr) :
    WP isa (.loop (.block VG.Proof.AesGcmSiv.X86_64.maskBody) .ne) s fun s' =>
      s'.mem = writeBytes s.mem D (VG.Proof.AesGcmSiv.X86_64.maskBytes s.mem D ((s.gpr .r11).setWidth 8) n) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcmSiv.X86_64.maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (VG.Proof.AesGcmSiv.X86_64.maskBytes s.mem D ((s.gpr .r11).setWidth 8) i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn1, hi, by simp [VG.Proof.AesGcmSiv.X86_64.maskBytes, bytesAt, writeBytes_nil], fun _ _ _ => rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi', r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := VG.Proof.AesGcmSiv.X86_64.maskStep_ok t
    (by rw [g _ (by decide) (by decide), hd]) r10 (by rw [g _ (by decide) (by decide), hn])
    (by rw [wr]; exact Proof.AesGcm.X86_64.in_of_covers hw hi' (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (VG.Proof.AesGcmSiv.X86_64.maskBytes s.mem D ((s.gpr .r11).setWidth 8) i).length = i := by
    simp [VG.Proof.AesGcmSiv.X86_64.maskBytes, Proof.Cmac.bytesAt_length]
  have hmem : t'.mem = writeBytes s.mem D (VG.Proof.AesGcmSiv.X86_64.maskBytes s.mem D ((s.gpr .r11).setWidth 8) (i + 1)) := by
    rw [mem', mem, VG.Proof.AesGcmSiv.X86_64.dst_kept (by omega) _ hlen, g _ (by decide) (by decide)]
    simp only [VG.Proof.AesGcmSiv.X86_64.maskBytes]
    rw [Proof.AesGcm.X86_64.bytesAt_succ, List.map_append, List.map_cons, List.map_nil,
      writeBytes_snoc s.mem D _ _ (by rw [List.length_map, Proof.Cmac.bytesAt_length]; omega),
      List.length_map, Proof.Cmac.bytesAt_length]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', Proof.AesGcm.X86_64.succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [r10', Proof.AesGcm.X86_64.succ_ofNat], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

theorem map_and_ff (xs : List Byte) : xs.map (· &&& (0#64 - 1#64 : BitVec 64).setWidth 8) = xs := by
  rw [show (0#64 - 1#64 : BitVec 64).setWidth 8 = BitVec.allOnes 8 by decide,
    show (fun x : Byte => x &&& BitVec.allOnes 8) = id from funext fun x => BitVec.and_allOnes, List.map_id]

theorem map_and_zero (xs : List Byte) : xs.map (· &&& (0#64 - 0#64 : BitVec 64).setWidth 8) =
    Spec.GcmSiv.zeros xs.length := by
  rw [show (0#64 - 0#64 : BitVec 64).setWidth 8 = 0#8 by decide]
  simp [Spec.GcmSiv.zeros, List.map_const']

/-- What `mask` leaves, from `t`, when `ok` is whether `c` holds. -/
structure MaskPost (K W SP : Addr) (D : Addr) (n : Nat) (c : Prop) [Decidable c] (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame [⟨D, n⟩] t.mem t'.mem
  data : bytesAt t'.mem D n = if c then bytesAt t.mem D n else Spec.GcmSiv.zeros n

theorem mask_ok {K W SP : Addr} {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
    (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n t.mem) (hD : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) {c : Prop} [Decidable c]
    (hok : t.mem.readW (W + BitVec.ofNat 64 192) 64 = if c then 1#64 else 0#64) :
    WP isa mask t (VG.Proof.AesGcmSiv.X86_64.MaskPost K W SP D n c t) := by
  have h15 := E.r15
  have hn := hD.lt
  have rD := E.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have rO := E.perm.wR (show 192 + 8 ≤ 3816 by decide)
  have sD := S.data
  have sL := S.len
  obtain ⟨t₁, run₁, h12₁, hbp₁, h11₁, h10₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .r11 (imm 0),
        .alu .sub .r11 (.mem (at_ .r15 okO)), .mov32 .r10 (imm 0), .alu .test .rbp (.reg .rbp)] t = some t₁ ∧
      t₁.gpr .r12 = D ∧ t₁.gpr .rbp = BitVec.ofNat 64 n ∧
      t₁.gpr .r11 = 0#64 - t.mem.readW (W + BitVec.ofNat 64 192) 64 ∧ t₁.gpr .r10 = BitVec.ofNat 64 0 ∧
      t₁.zf = some (decide (n = 0)) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h15, rD, rL, rO], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, sD]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, sL]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, sL]
      rw [Proof.AesGcm.X86_64.and_self_beq hn]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := E.keep hg₁ hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (VG.Proof.AesGcmSiv.X86_64.eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨E₁, hrd₁, hwr₁, by rw [hm₁]; exact Frame.refl _ _, ?_⟩
    simp [bytesAt, Spec.GcmSiv.zeros]
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.mono (VG.Proof.AesGcmSiv.X86_64.maskLoop_ok t₁ h12₁ hbp₁ h10₁ (by omega) (by omega) (by rw [hwr₁]; exact hDw))
      fun t₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_
    have hl : (VG.Proof.AesGcmSiv.X86_64.maskBytes t₁.mem D ((t₁.gpr .r11).setWidth 8) n).length = n := by
      simp [VG.Proof.AesGcmSiv.X86_64.maskBytes, Proof.Cmac.bytesAt_length]
    refine ⟨E₁.keep (fun r hr => ?_) hrd₂ hwr₂, hrd₂.trans hrd₁, hwr₂.trans hwr₁,
      by rw [hm₂, hm₁] at *; exact Proof.AesGcm.X86_64.writeBytes_frame' _ hl, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)
    · have e := Proof.AesGcm.X86_64.bytesAt_writeBytes_self t₁.mem D
        (VG.Proof.AesGcmSiv.X86_64.maskBytes t₁.mem D ((t₁.gpr .r11).setWidth 8) n) (by omega)
      rw [hl] at e
      rw [hm₂, e, h11₁, hok, hm₁]
      simp only [VG.Proof.AesGcmSiv.X86_64.maskBytes]
      split
      · exact VG.Proof.AesGcmSiv.X86_64.map_and_ff _
      · rw [VG.Proof.AesGcmSiv.X86_64.map_and_zero, Proof.Cmac.bytesAt_length]

/-! ## The tag's copies -/

/-- A 16-byte block copied from `S` to `T`, by words. -/
theorem bytesAt_copy2 (m : Mem) (S T : Addr) (hs : Mem.Sep (S + BitVec.ofNat 64 8) (64 / 8) T (64 / 8)) :
    bytesAt ((m.writeW T (m.readW S 64)).writeW (T + BitVec.ofNat 64 8)
      ((m.writeW T (m.readW S 64)).readW (S + BitVec.ofNat 64 8) 64)) T 16 = bytesAt m S 16 := by
  rw [Mem.readW_writeW_sep hs (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
    ← Proof.Cmac.bytesAt_split]

/-- `recv`: the received tag, at `T`, whose address is at `SP + 16`, copied
to `W`. -/
theorem recv_ok {K W SP T : Addr} {s : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP s)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T) (hTa : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8)
    (hB : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s T 16) :
    ∃ s', runBlock isa recv s = some s' ∧ Frame [⟨W, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem W 16 = bytesAt s.mem T 16 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h15 := E.r15
  have hsp := E.rsp
  have t₀ : InRegions (s.rd ++ s.wr) T 8 := by simpa using in_off (d := 0) (n := 8) hB.rd (by decide) (by decide)
  have t₈ := in_off (d := 8) (n := 8) hB.rd (by decide) (by decide)
  have w₀ : InRegions s.wr W 8 := by simpa using E.perm.wW (show 0 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 8 + 8 ≤ 3816 by decide)
  have hs : Mem.Sep (T + BitVec.ofNat 64 8) (64 / 8) W (64 / 8) :=
    hB.w.sep (Offset.contains_base T (d := 8) (n := 8) (k := 16) (by decide) (by decide))
      (by simpa using Offset.contains_base W (d := 0) (n := 8) (k := 3816) (by decide) (by decide))
  refine ⟨_, by srun [recv, h15, hsp, hT, hTa, t₀, t₈, w₀, w₈], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg]; exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_setReg]; exact VG.Proof.AesGcmSiv.X86_64.bytesAt_copy2 _ _ _ hs
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- `tagOut`: the tag at `W` copied to `T`, whose address is at `SP + 16`. -/
theorem tagOut_ok {K W SP T : Addr} {s : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP s)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T) (hTa : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8)
    (hTw : Covers [⟨T, 16⟩] s.wr) (hTW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 3816⟩) :
    ∃ s', runBlock isa tagOut s = some s' ∧ Frame [⟨T, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem T 16 = bytesAt s.mem W 16 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h15 := E.r15
  have hsp := E.rsp
  have t₀ : InRegions s.wr T 8 := by simpa using in_off (d := 0) (n := 8) hTw (by decide) (by decide)
  have t₈ := in_off (d := 8) (n := 8) hTw (by decide) (by decide)
  have w₀ : InRegions (s.rd ++ s.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wR (show 8 + 8 ≤ 3816 by decide)
  have hs : Mem.Sep (W + BitVec.ofNat 64 8) (64 / 8) T (64 / 8) :=
    hTW.symm.sep (Offset.contains_base W (d := 8) (n := 8) (k := 3816) (by decide) (by decide))
      (by simpa using Offset.contains_base T (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  refine ⟨_, by srun [tagOut, h15, hsp, hT, hTa, t₀, t₈, w₀, w₈], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg]; exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_setReg]; exact VG.Proof.AesGcmSiv.X86_64.bytesAt_copy2 _ _ _ hs
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

end VG.Proof.AesGcmSiv.X86_64

/-!
## The keys, and what the pieces write

Untrusted: everything here is checked by Lean. `keys` derives the message
keys, expands the encryption key and sets up GHASH's key and accumulator
(`keys_ok`). Every piece but counter mode and the mask writes only parts of
`W` and the stack below `SP` (`mutW`), which miss the buffers, the key
schedule and what the entry keeps in `W`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

/-- What the pieces before counter mode write. -/
abbrev mutW (W SP : Addr) : List Region := [VG.Proof.AesGcmSiv.X86_64.wA W, VG.Proof.AesGcmSiv.X86_64.wO W, VG.Proof.AesGcmSiv.X86_64.wC W, below SP 8]

theorem mutW_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.mutW W SP, ∃ r' ∈ VG.Proof.AesGcmSiv.X86_64.mutR W SP D n, Region.Sub r r' :=
  fun r hr => ⟨r, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp, fun _ h => h⟩

/-- `⟨W + d, k⟩` within `[0, 144)` of `W`. -/
theorem sub_wA {W SP : Addr} {d k : Nat} (h : d + k ≤ 144) :
    ∃ r' ∈ VG.Proof.AesGcmSiv.X86_64.mutW W SP, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨VG.Proof.AesGcmSiv.X86_64.wA W, by simp, Offset.sub_base W h⟩

/-- `⟨W + d, k⟩` within `[248, 3816)` of `W`. -/
theorem sub_wC {W SP : Addr} {d k : Nat} (h₁ : 248 ≤ d) (h₂ : d + k ≤ 3816) :
    ∃ r' ∈ VG.Proof.AesGcmSiv.X86_64.mutW W SP, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨VG.Proof.AesGcmSiv.X86_64.wC W, by simp, Offset.sub W h₁ (by omega)⟩

theorem sub_stk {W SP : Addr} : ∃ r' ∈ VG.Proof.AesGcmSiv.X86_64.mutW W SP, Region.Sub (below SP 8) r' := ⟨_, by simp, fun _ h => h⟩

theorem buf_mutW {K W SP : Addr} {s : State} {P : Addr} {len : Nat} (hP : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s P len) {m m' : Mem}
    (hf : Frame (VG.Proof.AesGcmSiv.X86_64.mutW W SP) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

theorem mutW_frame {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {d k : Nat}
    (hd : 144 ≤ d ∧ d + k ≤ 192 ∨ 200 ≤ d ∧ d + k ≤ 248) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.mutW W SP, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 144) (.inr (by omega)) (by omega) (by decide)
  · rcases hd with hd | hd
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm

/-- What `keys` writes: the keys, GHASH's key and accumulator, the blocks
the calls use, the encryption key's schedule and the working spaces. -/
abbrev keyR (W SP : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 128⟩, VG.Proof.AesGcmSiv.X86_64.wC W, below SP 8]

theorem keyR_mutW (W SP : Addr) : ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.keyR W SP, ∃ r' ∈ VG.Proof.AesGcmSiv.X86_64.mutW W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.AesGcmSiv.X86_64.sub_wA (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact VG.Proof.AesGcmSiv.X86_64.sub_stk

/-- What `keys` leaves, from `σ`. -/
structure KeysPost (K W SP : Addr) (R : Nat) (N : Addr) (σ t : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  frame : Frame (VG.Proof.AesGcmSiv.X86_64.keyR W SP) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12)).1 =
    bytesAt t.mem (W + BitVec.ofNat 64 16) 16
  ciph : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R = Spec.GcmSiv.aes
    (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12)).2
  hkey : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
    GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0

theorem keys_ok (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} {σ : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP σ) (S : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n σ.mem)
    (hN : VG.Proof.AesGcmSiv.X86_64.Buf K W SP σ N 12) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) :
    WP isa (VG.Impl.AesGcmSiv.X86_64.keys v.callees) σ (VG.Proof.AesGcmSiv.X86_64.KeysPost K W SP R N σ) := by
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.derive_ok v L hR E S hN hDW) fun t₂ I => ?_)
  have f₂ : Frame (VG.Proof.AesGcmSiv.X86_64.keyR W SP) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 16, 128⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 16, 128⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨VG.Proof.AesGcmSiv.X86_64.wC W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have S₂ := VG.Proof.AesGcmSiv.X86_64.slots_mut L hDW ((f₂.sub (VG.Proof.AesGcmSiv.X86_64.keyR_mutW W SP)).sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n)) S
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.expand_ok v L hR I.env S₂) fun t₃ X => ?_)
  obtain ⟨t₄, run₄, hG, hY, f₄, hg₄, hrd₄, hwr₄⟩ := VG.Proof.AesGcmSiv.X86_64.hkey_ok X.env
  refine WP.of_runBlock ⟨t₄, run₄, ?_⟩
  have fX := X.frame
  have f₃ : Frame (VG.Proof.AesGcmSiv.X86_64.keyR W SP) t₂.mem t₃.mem := fX.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.AesGcmSiv.X86_64.wC W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨VG.Proof.AesGcmSiv.X86_64.wC W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have dA : ∀ q ∈ [(⟨W + BitVec.ofNat 64 248, 240⟩ : Region), ⟨W + BitVec.ofNat 64 1768, 512⟩, below SP 8],
      (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
  have d64 : ∀ q ∈ [(⟨W + BitVec.ofNat 64 64, 32⟩ : Region)], (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint q :=
    fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have hA₄ : bytesAt t₄.mem (W + BitVec.ofNat 64 16) 16 = bytesAt t₂.mem (W + BitVec.ofNat 64 16) 16 := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame f₄ d64 (by decide), Proof.AesGcm.X86_64.bytesAt_frame fX dA (by decide)]
  have hK := I.keys hR
  refine ⟨X.env.keep (fun r hr => ?_) hrd₄ hwr₄, by rw [hrd₄, X.rd, I.rd], by rw [hwr₄, X.wr, I.wr],
    (f₂.trans f₃).trans (f₄.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨W + BitVec.ofNat 64 16, 128⟩, by simp, Offset.sub W (by decide) (by decide)⟩),
    ?_, ?_,
    by rw [hG, hA₄, ← Proof.AesGcm.X86_64.bytesAt_frame fX dA (by decide)], hY⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₄ _ (by simp)
  · rw [hK, hA₄]
  · rw [VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame f₄ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by rcases hR with h | h <;> subst h <;> decide), X.ciph, hK]

end VG.Proof.AesGcmSiv.X86_64

/-!
## `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, the
copy of the tag to `tag` and the restore compute `encryptWith` (RFC 8452
§4) of the arguments (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

/-- The return address misses everything the code writes. -/
theorem ret_disj {K W SP D : Addr} {n : Nat} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) (hW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) : ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.entryR W :: VG.Proof.AesGcmSiv.X86_64.mutR W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Region.sub_prefix (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below SP (by have := L.sp; omega)
  · exact hD

theorem cryR_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.cryR W SP D n, ∃ r' ∈ VG.Proof.AesGcmSiv.X86_64.mutR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨VG.Proof.AesGcmSiv.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨VG.Proof.AesGcmSiv.X86_64.wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem polyR_mutW (W SP : Addr) : ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.polyR W SP, ∃ r' ∈ VG.Proof.AesGcmSiv.X86_64.mutW W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcmSiv.X86_64.sub_wA (by decide)
  · exact VG.Proof.AesGcmSiv.X86_64.sub_wA (by decide)
  · exact VG.Proof.AesGcmSiv.X86_64.sub_wA (by decide)
  · exact VG.Proof.AesGcmSiv.X86_64.sub_wC (by decide) (by decide)
  · exact VG.Proof.AesGcmSiv.X86_64.sub_wC (by decide) (by decide)
  · exact VG.Proof.AesGcmSiv.X86_64.sub_stk

theorem tagR_mutW (W SP : Addr) {o : Nat} (ho : o + 16 ≤ 144) : ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.tagR W SP o, ∃ r' ∈ VG.Proof.AesGcmSiv.X86_64.mutW W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcmSiv.X86_64.sub_wA (by decide)
  · exact VG.Proof.AesGcmSiv.X86_64.sub_wA ho
  · exact VG.Proof.AesGcmSiv.X86_64.sub_wC (by decide) (by decide)
  · exact VG.Proof.AesGcmSiv.X86_64.sub_stk

theorem key_polyR {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.polyR W SP, (⟨W + BitVec.ofNat 64 248, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

theorem key_tagR {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {o : Nat} (ho : o + 16 ≤ 248) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.tagR W SP o, (⟨W + BitVec.ofNat 64 248, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr ho) (by decide) (by omega)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- `vg_aes_gcm_siv_seal`, for its arguments. -/
theorem seal_wp' (v : GcmImpl) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : VG.Proof.AesGcmSiv.X86_64.Args s K W SP N A D R al n) (Tb : VG.Proof.AesGcmSiv.X86_64.TagBuf W SP D n T) (hTw : Covers [⟨T, 16⟩] s.wr)
    (hrT : (⟨SP, 8⟩ : Region).Disjoint ⟨T, 16⟩) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa («seal» v.callees) s fun s' => gprPreserved s s' ∧
      Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) = (bytesAt s'.mem D n, bytesAt s'.mem T 16) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h <;> subst h <;> decide
  obtain ⟨s₁, run₁, E₁, S₁, sv₁, f₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86_64.entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hent : ∀ {P : Addr} {len : Nat}, VG.Proof.AesGcmSiv.X86_64.Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => Proof.AesGcm.X86_64.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem K R = Spec.GcmSiv.ctxCiph s.mem K R :=
    VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  have bN₁ := Ar.nonce.of_eq rd₁ wr₁
  have bA₁ := Ar.aad.of_eq rd₁ wr₁
  have bD₁ := Ar.data.of_eq rd₁ wr₁
  -- The keys.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.keys_ok v L Ar.rounds E₁ S₁ bN₁ Ar.data.w) fun s₂ Ky => ?_)
  have fK : Frame (VG.Proof.AesGcmSiv.X86_64.mutW W SP) s₁.mem s₂.mem := Ky.frame.sub (VG.Proof.AesGcmSiv.X86_64.keyR_mutW W SP)
  have S₂ := VG.Proof.AesGcmSiv.X86_64.slots_mut L Ar.data.w (fK.sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n)) S₁
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.polyval_ok v L Ky.env S₂ (bA₁.of_eq Ky.rd Ky.wr) (bD₁.of_eq Ky.rd Ky.wr)
    (bN₁.of_eq Ky.rd Ky.wr) Ky.hkey Ky.acc) fun s₃ Po => ?_)
  have f₃ : Frame (VG.Proof.AesGcmSiv.X86_64.mutW W SP) s₂.mem s₃.mem := Po.frame.sub (VG.Proof.AesGcmSiv.X86_64.polyR_mutW W SP)
  have S₃ := VG.Proof.AesGcmSiv.X86_64.slots_mut L Ar.data.w (f₃.sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n)) S₂
  -- The tag.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.tag_ok v L Ar.rounds Po.env S₃ (o := 0) (by decide)) fun s₄ Tg => ?_)
  have f₄ : Frame (VG.Proof.AesGcmSiv.X86_64.mutW W SP) s₃.mem s₄.mem := Tg.frame.sub (VG.Proof.AesGcmSiv.X86_64.tagR_mutW W SP (by decide))
  have S₄ := VG.Proof.AesGcmSiv.X86_64.slots_mut L Ar.data.w (f₄.sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n)) S₃
  have f₁₄ : Frame (VG.Proof.AesGcmSiv.X86_64.mutW W SP) s₁.mem s₄.mem := (fK.trans f₃).trans f₄
  -- Counter mode.
  have bD₄ : VG.Proof.AesGcmSiv.X86_64.Buf K W SP s₄ D n := bD₁.of_eq (by rw [Tg.rd, Po.rd, Ky.rd]) (by rw [Tg.wr, Po.wr, Ky.wr])
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.crypt_ok v L Ar.rounds Tg.env S₄ bD₄
    (by rw [Tg.wr, Po.wr, Ky.wr, wr₁]; exact Ar.dw)) fun s₅ Cr => ?_)
  have f₁₅ : Frame (VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) s₁.mem s₅.mem := (f₁₄.sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n)).trans (Cr.frame.sub (VG.Proof.AesGcmSiv.X86_64.cryR_mut W SP D n))
  have fall : Frame (VG.Proof.AesGcmSiv.X86_64.entryR W :: VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) s.mem s₅.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (f₁₅.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  have r₅ : s₅.rd = s.rd := by rw [Cr.rd, Tg.rd, Po.rd, Ky.rd, rd₁]
  have w₅ : s₅.wr = s.wr := by rw [Cr.wr, Tg.wr, Po.wr, Ky.wr, wr₁]
  -- The copy of the tag, and `restore`.
  have hTa : InRegions (s₅.rd ++ s₅.wr) (SP + BitVec.ofNat 64 16) 8 := by
    have h := Proof.AesGcm.X86_64.in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc] at h
    rw [r₅, w₅]; exact h
  obtain ⟨s₆, run₆, fT, hT₆, hg₆, rd₆, wr₆⟩ := VG.Proof.AesGcmSiv.X86_64.tagOut_ok Cr.env (by rw [VG.Proof.AesGcmSiv.X86_64.argT_kept fall Ar.argsW Ar.argsD, hT]) hTa
    (by rw [w₅]; exact hTw) Tb.w
  have E₆ : VG.Proof.AesGcmSiv.X86_64.Env K W SP s₆ := Cr.env.of_saved hg₆ rd₆ wr₆
  have dT : ∀ q ∈ [(⟨T, 16⟩ : Region)], ∀ p ∈ saved, (⟨W + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint q := by
    intro q hq p hp
    simp only [List.mem_singleton] at hq; subst hq
    have hd : 144 ≤ p.2 ∧ p.2 + 8 ≤ 192 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (Tb.w.sub_right (Lay.wSub (by omega))).symm
  have sv₆ : VG.Proof.AesGcmSiv.X86_64.Saved s₆.mem W s.gpr := fun p hp => by
    rw [← VG.Proof.AesGcmSiv.X86_64.saved_mut L Ar.data.w f₁₅ sv₁ p hp]
    exact fT.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
      (fun q hq => dT q hq p hp) (by decide)
  obtain ⟨s₇, run₇, hg₇, hm₇, hsp₇, _⟩ := VG.Proof.AesGcmSiv.X86_64.restore_ok E₆ sv₆
  refine WP.of_runBlock ⟨s₇, by rw [VG.Proof.AesGcmSiv.X86_64.runBlock_append, run₆]; exact run₇, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₇ (.rbx, 144) (by decide)
    · exact hg₇ (.rbp, 152) (by decide)
    · rw [hsp₇, E₆.rsp, hsp]
    · exact hg₇ (.r12, 160) (by decide)
    · exact hg₇ (.r13, 168) (by decide)
    · exact hg₇ (.r14, 176) (by decide)
    · exact hg₇ (.r15, 184) (by decide)
  · rw [hm₇, hsp, fT.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hrT) (by decide)]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (VG.Proof.AesGcmSiv.X86_64.ret_disj L Ar.retW Ar.retD) (by decide)
  · have key₃ : Spec.GcmSiv.ctxCiph s₃.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₂.mem (W + BitVec.ofNat 64 248) R := VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame Po.frame (VG.Proof.AesGcmSiv.X86_64.key_polyR L) hRb
    have key₄ : Spec.GcmSiv.ctxCiph s₄.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₃.mem (W + BitVec.ofNat 64 248) R := VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame Tg.frame (VG.Proof.AesGcmSiv.X86_64.key_tagR L (by decide)) hRb
    have n₂ : bytesAt s₂.mem N 12 = bytesAt s.mem N 12 := by rw [VG.Proof.AesGcmSiv.X86_64.buf_mutW bN₁ fK, hent Ar.nonce]
    have a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := by rw [VG.Proof.AesGcmSiv.X86_64.buf_mutW bA₁ fK, hent Ar.aad]
    have d₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [VG.Proof.AesGcmSiv.X86_64.buf_mutW bD₁ fK, hent Ar.data]
    have d₄ : bytesAt s₄.mem D n = bytesAt s.mem D n := by rw [VG.Proof.AesGcmSiv.X86_64.buf_mutW bD₁ f₁₄, hent Ar.data]
    have t₅ : bytesAt s₅.mem W 16 = bytesAt s₄.mem W 16 := Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · simpa using L.w_w (a := 0) (n := 16) (d := 96) (k := 48) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (d := 1768) (k := 2048) (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
      · exact (Ar.data.w.sub_right (Region.sub_prefix (by decide))).symm) (by decide)
    have d₇ : bytesAt s₇.mem D n = bytesAt s₅.mem D n := by
      rw [hm₇]; exact Proof.AesGcm.X86_64.bytesAt_frame fT (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact Tb.d.symm) (by have := Ar.data.lt; omega)
    have tg := Tg.out
    rw [BitVec.add_zero] at tg
    have au := Ky.auth
    have ci := Ky.ciph
    rw [hK₁, hent Ar.nonce] at au ci
    have po := Po.out hpv
    rw [n₂, a₂, d₂] at po
    rw [d₇, hm₇, hT₆, Cr.data, t₅, d₄, key₄, key₃, ci, tg, key₃, ci, po, ← au]
    unfold Spec.GcmSiv.encryptWith
    generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12) = dk
    obtain ⟨a, e⟩ := dk
    rfl

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (v : GcmImpl) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} (h : VG.Proof.AesGcmSiv.sealPre s) :
    WP isa («seal» v.callees) s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨⟨Ar, Tb⟩, hTw, hrT⟩ := VG.Proof.AesGcmSiv.X86_64.args_of_seal h
  exact VG.Proof.AesGcmSiv.X86_64.seal_wp' v hpv Ar Tb hTw hrT rfl (VG.Proof.AesGcmSiv.X86_64.ofNat_toNat64 _).symm rfl rfl rfl (VG.Proof.AesGcmSiv.X86_64.ofNat_toNat64 _).symm rfl rfl
    (VG.Proof.AesGcmSiv.X86_64.ofNat_toNat64 _).symm rfl

end VG.Proof.AesGcmSiv.X86_64

/-!
## `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the copy of the
received tag to `W`, the keys, counter mode on the data from it, POLYVAL of
the result and the tag input, its tag at `W + 128`, the comparison, the mask
and the restore compute `decryptWith` (RFC 8452 §5) of the arguments
(`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

theorem w0_keyR {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) : ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.keyR W SP, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 16) (k := 128) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 248) (k := 3568) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm

theorem w0_cryR {K W SP D : Addr} {n : Nat} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) :
    ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.cryR W SP D n, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 96) (k := 48) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 1768) (k := 2048) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
  · exact (hD.sub_right (Region.sub_prefix (by decide))).symm

theorem w0_polyR {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) : ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.polyR W SP, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 96) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 80) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 128) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 488) (k := 1024) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 1512) (k := 256) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm

theorem w0_tagR {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) : ∀ r ∈ VG.Proof.AesGcmSiv.X86_64.tagR W SP 128, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 112) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 128) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 1768) (k := 2048) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm

/-- `vg_aes_gcm_siv_open`, for its arguments. -/
theorem open_wp' (v : GcmImpl) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : VG.Proof.AesGcmSiv.X86_64.Args s K W SP N A D R al n) (Tb : VG.Proof.AesGcmSiv.X86_64.TagBuf W SP D n T) (hTr : Covers [⟨T, 16⟩] (s.rd ++ s.wr))
    (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa («open» v.callees) s fun s' => gprPreserved s s' ∧
      VG.Proof.AesGcmSiv.openPost (Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T 16)) s' D n := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h <;> subst h <;> decide
  obtain ⟨s₀, run₀, E₀, S₀, sv₀, f₀, rd₀, wr₀⟩ := VG.Proof.AesGcmSiv.X86_64.entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  have f₀' : Frame (VG.Proof.AesGcmSiv.X86_64.entryR W :: VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) s.mem s₀.mem :=
    f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  -- The received tag, copied to `W`.
  have hTa : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 16) 8 := by
    have h := Proof.AesGcm.X86_64.in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc] at h
    rw [rd₀, wr₀]; exact h
  obtain ⟨s₁, run₁, fR, hR₁, hgR, rdR, wrR⟩ := VG.Proof.AesGcmSiv.X86_64.recv_ok E₀ (by rw [VG.Proof.AesGcmSiv.X86_64.argT_kept f₀' Ar.argsW Ar.argsD, hT]) hTa
    ((Tb.buf (s := s) hTr).of_eq rd₀ wr₀)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP s₁ := E₀.of_saved hgR rdR wrR
  have fR' : Frame (VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) s₀.mem s₁.mem := fR.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨VG.Proof.AesGcmSiv.X86_64.wA W, by simp, Region.sub_prefix (by decide)⟩
  have S₁ := VG.Proof.AesGcmSiv.X86_64.slots_mut L Ar.data.w fR' S₀
  have rd₁ : s₁.rd = s.rd := by rw [rdR, rd₀]
  have wr₁ : s₁.wr = s.wr := by rw [wrR, wr₀]
  have f₁ : Frame (VG.Proof.AesGcmSiv.X86_64.entryR W :: VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) s.mem s₁.mem :=
    f₀'.trans (fR'.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  have f₀₁ : Frame [VG.Proof.AesGcmSiv.X86_64.entryR W, ⟨W, 16⟩] s.mem s₁.mem :=
    (f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨W, 16⟩, by simp, fun _ h => h⟩)
  have hent : ∀ {P : Addr} {len : Nat}, VG.Proof.AesGcmSiv.X86_64.Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => Proof.AesGcm.X86_64.bytesAt_frame f₀₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hP.w.sub_right (Lay.wSub (by decide))
      · exact hP.w.sub_right (Region.sub_prefix (by decide)))
      (by have := hP.lt; omega)
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem K R = Spec.GcmSiv.ctxCiph s.mem K R :=
    VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame f₀₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w.sub_right (Lay.wSub (by decide))
      · exact L.k_w.sub_right (Region.sub_prefix (by decide))) hRb
  have hT₁ : bytesAt s₁.mem W 16 = bytesAt s.mem T 16 := by
    rw [hR₁]; exact VG.Proof.AesGcmSiv.X86_64.tag_kept Tb f₀'
  have bN₁ := Ar.nonce.of_eq rd₁ wr₁
  have bA₁ := Ar.aad.of_eq rd₁ wr₁
  have bD₁ := Ar.data.of_eq rd₁ wr₁
  -- The keys.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.keys_ok v L Ar.rounds E₁ S₁ bN₁ Ar.data.w) fun s₂ Ky => ?_)
  have fK : Frame (VG.Proof.AesGcmSiv.X86_64.mutW W SP) s₁.mem s₂.mem := Ky.frame.sub (VG.Proof.AesGcmSiv.X86_64.keyR_mutW W SP)
  have S₂ := VG.Proof.AesGcmSiv.X86_64.slots_mut L Ar.data.w (fK.sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n)) S₁
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.crypt_ok v L Ar.rounds Ky.env S₂ (bD₁.of_eq Ky.rd Ky.wr)
    (by rw [Ky.wr, wr₁]; exact Ar.dw)) fun s₃ Cr => ?_)
  have S₃ := S₂.of_frame Cr.frame (VG.Proof.AesGcmSiv.X86_64.slots_cryR L Ar.data)
  have dK : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 96 → ∀ q ∈ VG.Proof.AesGcmSiv.X86_64.cryR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm
      · exact (Ar.data.w.sub_right (Lay.wSub (by omega))).symm
  have hA₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (dK (by decide) (by decide)) (by decide)
  have hG₃ : Spec.Gcm.blockAt s₃.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt s₃.mem (W + BitVec.ofNat 64 16) 16)) := by
    rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), Ky.hkey, hA₃]
  have hY₃ : Spec.Gcm.blockAt s₃.mem (W + BitVec.ofNat 64 80) = 0 := by
    rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), Ky.acc]
  have nA : ∀ {P : Addr} {len : Nat}, VG.Proof.AesGcmSiv.X86_64.Buf K W SP s P len → (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩ →
      bytesAt s₃.mem P len = bytesAt s.mem P len := fun hP hPD => by
    rw [Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.stk.symm
        · exact hPD) (by have := hP.lt; omega),
      VG.Proof.AesGcmSiv.X86_64.buf_mutW (hP.of_eq rd₁ wr₁) fK, hent hP]
  -- POLYVAL of the plaintext and the tag input.
  have r₃ : s₃.rd = s₁.rd := by rw [Cr.rd, Ky.rd]
  have w₃ : s₃.wr = s₁.wr := by rw [Cr.wr, Ky.wr]
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.polyval_ok v L Cr.env S₃ (bA₁.of_eq r₃ w₃) (bD₁.of_eq r₃ w₃) (bN₁.of_eq r₃ w₃) hG₃ hY₃)
    fun s₄ Po => ?_)
  have S₄ := VG.Proof.AesGcmSiv.X86_64.slots_mut L Ar.data.w ((Po.frame.sub (VG.Proof.AesGcmSiv.X86_64.polyR_mutW W SP)).sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n)) S₃
  -- Its tag at `W + 128`.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.tag_ok v L Ar.rounds Po.env S₄ (o := 128) (by decide)) fun s₅ Tg => ?_)
  -- The comparison.
  obtain ⟨s₆, run₆, hm₆, hg₆, hrd₆, hwr₆⟩ := VG.Proof.AesGcmSiv.X86_64.cmp_ok Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : VG.Proof.AesGcmSiv.X86_64.Env K W SP s₆ := Tg.env.of_saved hg₆ hrd₆ hwr₆
  have fO : Frame [VG.Proof.AesGcmSiv.X86_64.wO W] s₅.mem s₆.mem := by
    rw [hm₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have S₅ := VG.Proof.AesGcmSiv.X86_64.slots_mut L Ar.data.w ((Tg.frame.sub (VG.Proof.AesGcmSiv.X86_64.tagR_mutW W SP (by decide))).sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n)) S₄
  have S₆ := S₅.of_frame fO (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
  have r₅ : s₅.rd = s₁.rd := by rw [Tg.rd, Po.rd, r₃]
  have w₅ : s₅.wr = s₁.wr := by rw [Tg.wr, Po.wr, w₃]
  have hok : s₆.mem.readW (W + BitVec.ofNat 64 192) 64 =
      if bytesAt s₅.mem (W + BitVec.ofNat 64 128) 16 = bytesAt s₅.mem W 16 then 1#64 else 0#64 := by
    rw [hm₆, Mem.readW_writeW_self64]
    by_cases hc : bytesAt s₅.mem W 16 = bytesAt s₅.mem (W + BitVec.ofNat 64 128) 16
    · simp only [hc, ↓reduceIte]
    · simp only [hc, Ne.symm hc, ↓reduceIte]
  -- The mask.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.mask_ok E₆ S₆ (bD₁.of_eq (by rw [hrd₆, r₅]) (by rw [hwr₆, w₅]))
    (by rw [hwr₆, w₅, wr₁]; exact Ar.dw) hok) fun s₇ Mk => ?_)
  -- `ok` and the restore.
  have h15₇ := Mk.env.r15
  have rO := Mk.env.perm.wR (show 192 + 8 ≤ 3816 by decide)
  obtain ⟨s₈, run₈, hax₈, hm₈, hg₈, hrd₈, hwr₈⟩ : ∃ s₈ : State, runBlock isa [.mov .rax (.mem (at_ .r15 okO))] s₇ =
      some s₈ ∧ s₈.gpr .rax = s₇.mem.readW (W + BitVec.ofNat 64 192) 64 ∧ s₈.mem = s₇.mem ∧
      (∀ r, r ≠ .rax → s₈.gpr r = s₇.gpr r) ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by srun [h15₇, rO], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true]
    · rfl
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  have E₈ : VG.Proof.AesGcmSiv.X86_64.Env K W SP s₈ := Mk.env.keep (fun r hr => hg₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd₈ hwr₈
  have fall : Frame (VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) s₁.mem s₇.mem :=
    ((((fK.sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n)).trans (Cr.frame.sub (VG.Proof.AesGcmSiv.X86_64.cryR_mut W SP D n))).trans
      ((Po.frame.sub (VG.Proof.AesGcmSiv.X86_64.polyR_mutW W SP)).sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n))).trans
      (((Tg.frame.sub (VG.Proof.AesGcmSiv.X86_64.tagR_mutW W SP (by decide))).sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n)).trans
        (fO.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩))).trans
      (Mk.frame.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩)
  obtain ⟨s₉, run₉, hg₉, hm₉, hsp₉, hax₉⟩ :=
    VG.Proof.AesGcmSiv.X86_64.restore_ok E₈ (by rw [hm₈]; exact VG.Proof.AesGcmSiv.X86_64.saved_mut L Ar.data.w (fR'.trans fall) sv₀)
  refine WP.of_runBlock ⟨s₉, by rw [VG.Proof.AesGcmSiv.X86_64.runBlock_append, run₈]; exact run₉, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₉ (.rbx, 144) (by decide)
    · exact hg₉ (.rbp, 152) (by decide)
    · rw [hsp₉, E₈.rsp, hsp]
    · exact hg₉ (.r12, 160) (by decide)
    · exact hg₉ (.r13, 168) (by decide)
    · exact hg₉ (.r14, 176) (by decide)
    · exact hg₉ (.r15, 184) (by decide)
  · have fall' : Frame (VG.Proof.AesGcmSiv.X86_64.entryR W :: VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) s.mem s₇.mem :=
      f₁.trans (fall.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
    rw [hm₉, hm₈, hsp]
    exact fall'.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (VG.Proof.AesGcmSiv.X86_64.ret_disj L Ar.retW Ar.retD) (by decide)
  · have au := Ky.auth
    have ci := Ky.ciph
    rw [hK₁, hent Ar.nonce] at au ci
    have tag₂ : bytesAt s₂.mem W 16 = bytesAt s.mem T 16 := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame Ky.frame (VG.Proof.AesGcmSiv.X86_64.w0_keyR L) (by decide), hT₁]
    have tag₅ : bytesAt s₅.mem W 16 = bytesAt s.mem T 16 := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame Tg.frame (VG.Proof.AesGcmSiv.X86_64.w0_tagR L) (by decide),
        Proof.AesGcm.X86_64.bytesAt_frame Po.frame (VG.Proof.AesGcmSiv.X86_64.w0_polyR L) (by decide),
        Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (VG.Proof.AesGcmSiv.X86_64.w0_cryR L Ar.data.w) (by decide), tag₂]
    have ct₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [VG.Proof.AesGcmSiv.X86_64.buf_mutW bD₁ fK, hent Ar.data]
    have ci₄ : Spec.GcmSiv.ctxCiph s₄.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₂.mem (W + BitVec.ofNat 64 248) R := by
      rw [VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame Po.frame (VG.Proof.AesGcmSiv.X86_64.key_polyR L) hRb, VG.Proof.AesGcmSiv.X86_64.ctxCiph_frame Cr.frame (VG.Proof.AesGcmSiv.X86_64.key_cryR L Ar.data) hRb]
    have pt₃ := Cr.data
    rw [tag₂, ct₂, ci] at pt₃
    have po := Po.out hpv
    rw [hA₃, ← au, nA Ar.nonce Ar.nd, nA Ar.aad Ar.ad, pt₃] at po
    have tg := Tg.out
    rw [ci₄, ci, po] at tg
    have dD : ∀ q ∈ VG.Proof.AesGcmSiv.X86_64.tagR W SP 128, (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.stk.symm
    have dP : ∀ q ∈ VG.Proof.AesGcmSiv.X86_64.polyR W SP, (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.stk.symm
    have d₆ : bytesAt s₆.mem D n = bytesAt s₃.mem D n := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame fO (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
          (by have := Ar.data.lt; omega),
        Proof.AesGcm.X86_64.bytesAt_frame Tg.frame dD (by have := Ar.data.lt; omega),
        Proof.AesGcm.X86_64.bytesAt_frame Po.frame dP (by have := Ar.data.lt; omega)]
    have ax : s₉.gpr .rax = s₆.mem.readW (W + BitVec.ofNat 64 192) 64 := by
      rw [hax₉, hax₈, Mk.frame.readW (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm)
        (by decide)]
    have md := Mk.data
    have ax' := ax.trans hok
    rw [tg, tag₅] at ax'
    rw [tg, tag₅, d₆, pt₃] at md
    have hdec : Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T 16) =
        let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        if Spec.GcmSiv.aes dk.2 (Spec.GcmSiv.tagInput dk.1 (bytesAt s.mem N 12)
            (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
            (bytesAt s.mem A al)) = bytesAt s.mem T 16 then
          some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
        else none := by
      unfold Spec.GcmSiv.decryptWith
      rw [← Prod.eta (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R)
        (bytesAt s.mem N 12))]
    simp only at hdec
    generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12) = dk
      at md ax' hdec
    rw [hdec]
    refine Or.elim (Classical.em (Spec.GcmSiv.aes dk.2 (Spec.GcmSiv.tagInput dk.1 (bytesAt s.mem N 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
      (bytesAt s.mem A al)) = bytesAt s.mem T 16)) (fun hc => ?_) (fun hc => ?_)
    · refine VG.Proof.AesGcmSiv.openPost_some (by rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]) ?_ ?_
      · rw [ax']; simp only [hc, ↓reduceIte]; decide
      · rw [hm₉, hm₈, md]; simp only [hc, ↓reduceIte]
    · refine VG.Proof.AesGcmSiv.openPost_none (by rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]) ?_ ?_
      · rw [ax']; simp only [hc, ↓reduceIte]; decide
      · rw [hm₉, hm₈, md]; simp only [hc, ↓reduceIte]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (v : GcmImpl) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} (h : VG.Proof.AesGcmSiv.openPre s) :
    WP isa («open» v.callees) s fun s' => gprPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨⟨Ar, Tb⟩, hTr⟩ := VG.Proof.AesGcmSiv.X86_64.args_of_open h
  exact VG.Proof.AesGcmSiv.X86_64.open_wp' v hpv Ar Tb hTr rfl (VG.Proof.AesGcmSiv.X86_64.ofNat_toNat64 _).symm rfl rfl rfl (VG.Proof.AesGcmSiv.X86_64.ofNat_toNat64 _).symm rfl rfl
    (VG.Proof.AesGcmSiv.X86_64.ofNat_toNat64 _).symm rfl

end VG.Proof.AesGcmSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86_64.CryptCT`. -/
section

/-!
# AES-GCM-SIV on x86-64: relating two runs, the tag and counter mode

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs piece by piece (`RelCT`). Both runs have the same public
arguments, kept in the slots of `W` (`Slots`), so the taint analysis starts
from the registers that agree and those slots, public (`sivT`, `both_agree`);
what correctness says about each run is added with `RelCT.wp`.
-/

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)

/-- The taint: the registers `rs`, `r13`, `r15` and `rsp` public, `r15` the
base of the working space (the second writable region) and the slots of the
public arguments `[200, 248)` public. -/
def sivT (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r13, .r15, .rsp]), flags := false, lens := [0, 3816], bases := [(.r15, 1, 0)],
    slots := [(1, 200, 48)] }

/-- One run with the public arguments. -/
structure One (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcmSiv.X86_64.Env K W SP s
  sl : VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n s.mem
  wr : s.wr = [⟨D, n⟩, ⟨W, 3816⟩]

/-- Two runs with the same public arguments, agreeing on the registers `rs`. -/
structure Both (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (rs : List Reg) (s₁ s₂ : State) :
    Prop where
  o₁ : VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n s₁
  o₂ : VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n s₂
  agree : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

/-- Bytes of a word that both memories hold. -/
theorem word_byte {m₁ m₂ : Mem} {a : Addr} {v : BitVec 64} (h₁ : m₁.readW a 64 = v) (h₂ : m₂.readW a 64 = v)
    {j : Nat} (hj : j < 8) : m₁ (a + BitVec.ofNat 64 j) = m₂ (a + BitVec.ofNat 64 j) := by
  have e : bytesAt m₁ a 8 = bytesAt m₂ a 8 := by rw [← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, h₁, h₂]
  have := congrArg (fun l => l.getD j 0) e
  simpa only [Proof.Cmac.getD_bytesAt _ _ hj] using this

theorem both_agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {rs : List Reg} {s₁ s₂ : State}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64)
    (h : VG.Proof.AesGcmSiv.X86_64.Both K W SP R N A D al n rs s₁ s₂) : X86_64.Taint.Agree (VG.Proof.AesGcmSiv.X86_64.sivT rs) s₁ s₂ := by
  have wf : ∀ {s : State}, VG.Proof.AesGcmSiv.X86_64.Env K W SP s → s.wr = [⟨D, n⟩, ⟨W, 3816⟩] → X86_64.Taint.Wf (VG.Proof.AesGcmSiv.X86_64.sivT rs) s := fun E hw => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
    · rw [hw]; exact List.pairwise_pair.mpr hDW
    · rw [hw]; intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hn
      · show 3816 ≤ 2 ^ 64; decide
    · simp only [VG.Proof.AesGcmSiv.X86_64.sivT, List.mem_singleton] at hp; subst hp
      simp only [X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [E.r15, BitVec.add_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h.o₁.wr, h.o₂.wr], wf h.o₁.env h.o₁.wr,
    wf h.o₂.env h.o₂.wr, fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, X86_64.Taint.noLo⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact h.agree r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.o₁.env.r13, h.o₂.env.r13]
      · rw [h.o₁.env.r15, h.o₂.env.r15]
      · rw [h.o₁.env.rsp, h.o₂.env.rsp]
  · simp only [VG.Proof.AesGcmSiv.X86_64.sivT, List.mem_singleton] at hsl; subst hsl; simp [VG.Proof.AesGcmSiv.X86_64.sivT]
  · have hb : ∀ s : State, s.wr = [⟨D, n⟩, ⟨W, 3816⟩] → X86_64.Taint.byteAddr s 1 k = W + BitVec.ofNat 64 k :=
      fun s hw => by
        simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
    have hw : ∀ d, k = d + (k - d) → W + BitVec.ofNat 64 k = W + BitVec.ofNat 64 d + BitVec.ofNat 64 (k - d) :=
      fun d e => by rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, ← e]
    simp only [VG.Proof.AesGcmSiv.X86_64.sivT, List.mem_singleton] at hsl; subst hsl
    rw [hb s₁ h.o₁.wr, hb s₂ h.o₂.wr]
    simp only at hk₁ hk₂
    have S₁ := h.o₁.sl
    have S₂ := h.o₂.sl
    have key : ∀ d, d ∈ [200, 208, 216, 224, 232, 240] → d ≤ k → k < d + 8 →
        s₁.mem (W + BitVec.ofNat 64 k) = s₂.mem (W + BitVec.ofNat 64 k) := fun d hd h₁ h₂ => by
      rw [hw d (by omega)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact VG.Proof.AesGcmSiv.X86_64.word_byte S₁.rounds S₂.rounds (by omega)
      · exact VG.Proof.AesGcmSiv.X86_64.word_byte S₁.nonce S₂.nonce (by omega)
      · exact VG.Proof.AesGcmSiv.X86_64.word_byte S₁.aad S₂.aad (by omega)
      · exact VG.Proof.AesGcmSiv.X86_64.word_byte S₁.alen S₂.alen (by omega)
      · exact VG.Proof.AesGcmSiv.X86_64.word_byte S₁.data S₂.data (by omega)
      · exact VG.Proof.AesGcmSiv.X86_64.word_byte S₁.len S₂.len (by omega)
    have hq : (k - 200) / 8 = 0 ∨ (k - 200) / 8 = 1 ∨ (k - 200) / 8 = 2 ∨ (k - 200) / 8 = 3 ∨
        (k - 200) / 8 = 4 ∨ (k - 200) / 8 = 5 := by omega
    exact key (200 + 8 * ((k - 200) / 8)) (by
      rcases hq with h | h | h | h | h | h <;> rw [h] <;> decide) (by omega) (by omega)

/-- Code the taint analysis checks from `sivT rs`. -/
theorem rel_taintC {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesGcmSiv.X86_64.Both K W SP R N A D al n rs s₁ s₂)
    (hc : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (VG.Proof.AesGcmSiv.X86_64.sivT rs) (fun s₁ s₂ h => VG.Proof.AesGcmSiv.X86_64.both_agree hDW hn (hP _ _ h)) hc

/-- Code the taint analysis checks from `sivT rs`, leaving the flags public. -/
theorem rel_flagsC {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesGcmSiv.X86_64.Both K W SP R N A D al n rs s₁ s₂)
    (hc : ∃ hc, ((taint.check (VG.Proof.AesGcmSiv.X86_64.sivT rs) c hc).map (·.flags)) = some true) :
    RelCT isa P c fun s₁ s₂ => s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf := by
  obtain ⟨_, h⟩ := hc
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (VG.Proof.AesGcmSiv.X86_64.both_agree hDW hn (hP _ _ hp)) e₁ e₂
  obtain ⟨hcf, hzf, -, -⟩ := ha.rf.2 hs
  exact ⟨ht, hcf, hzf⟩

theorem eval_e_eq {s₁ s₂ : State} (h : s₁.zf = s₂.zf) : isa.eval .e s₁ = isa.eval .e s₂ := h
theorem eval_ne_eq {s₁ s₂ : State} (h : s₁.zf = s₂.zf) : isa.eval .ne s₁ = isa.eval .ne s₂ := by
  show s₁.zf.map _ = s₂.zf.map _; rw [h]
theorem eval_b_eq {s₁ s₂ : State} (h : s₁.cf = s₂.cf) : isa.eval .b s₁ = isa.eval .b s₂ := h

/-- Runs related from each pair of states. -/
theorem rel_of_pt {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (fun t₁ t₂ => t₁ = σ₁ ∧ t₂ = σ₂) c Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.AesGcmSiv.X86_64

/-!
## The tag and counter mode are constant time

Untrusted: everything here is checked by Lean. The code around each call of
`vg_aes_ctr32` passes the taint analysis from the public slots and the
registers both runs agree on (`rel_taintC`); each call has the same
arguments in both runs, by correctness.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr xorLoop)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl CtrCall ctr_rel ctr_call)

/-! ## The tag -/

theorem tagCall_wp {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    {t : State} (O : VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t) {o : Nat} (ho : o = 0 ∨ o = 128) :
    WP isa (.block (copy16 cmO ccO ++ zero16 o ++ ptr .rdi .r15 skO ++ ctrArgs ++ ptr .rcx .r15 o)) t fun t₁ =>
      CtrCall t₁ (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 o)
        (W + BitVec.ofNat 64 1768) R 1 ∧ t₁.gpr .rsp = SP := by
  obtain ⟨t₁, run₁, -, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcmSiv.X86_64.tagArgs_ok L O.env O.sl ho
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := O.env.of_saved hg₁ hrd₁ hwr₁
  have dO : (⟨W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 112, 16⟩ :=
    L.w_w (by omega) (by omega) (by decide)
  exact WP.of_runBlock ⟨t₁, run₁, VG.Proof.AesGcmSiv.X86_64.cargs L E₁ hR (VG.Proof.AesGcmSiv.X86_64.keyS L E₁.perm) (c := 112) (by decide)
    (VG.Proof.AesGcmSiv.X86_64.srcW L E₁.perm (t := o) (k := 16 * 1) (by omega)) dO (L.w_w (.inr (by omega)) (by decide) (by omega))
    (E₁.perm.wC (by omega)) rdi rsi rdx rcx r8 r9, E₁.rsp⟩

theorem tagArgs_check {o : Nat} (ho : o = 0 ∨ o = 128) :
    ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT []) (.block (copy16 cmO ccO ++ zero16 o ++ ptr .rdi .r15 skO ++ ctrArgs ++
      ptr .rcx .r15 o)) hc).isSome = true := by
  rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `tag o`, in two runs with the same public arguments. -/
theorem tag_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {o : Nat}
    (ho : o = 0 ∨ o = 128) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → VG.Proof.AesGcmSiv.X86_64.Both K W SP R N A D al n [] t₁ t₂) :
    RelCT isa P (tag v.callees o) fun _ _ => True := by
  have a := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [] hDW hn hP (VG.Proof.AesGcmSiv.X86_64.tagArgs_check ho)).wp
    (F₁ := fun (t₁ : State) => CtrCall t₁ (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 o)
        (W + BitVec.ofNat 64 1768) R 1 ∧ t₁.gpr .rsp = SP)
    (F₂ := fun (t₁ : State) => CtrCall t₁ (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 o)
        (W + BitVec.ofNat 64 1768) R 1 ∧ t₁.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.tagCall_wp L hR (hP _ _ h).o₁ ho, VG.Proof.AesGcmSiv.X86_64.tagCall_wp L hR (hP _ _ h).o₂ ho⟩
  exact RelCT.seq a (ctr_rel v.ctr fun t₁ t₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)

/-! ## Counter mode's whole blocks -/

/-- The end of a block: the counter incremented, the pointer and the count. -/
theorem blkEnd_ok {K W SP : Addr} {t : State} (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t) {D : Addr} {b j : Nat} (hj : j < b)
    (hb : b < 2 ^ 60) (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j)) (hbx : t.gpr .rbx = BitVec.ofNat 64 (b - j)) :
    ∃ t' : State, runBlock isa [.mov32 .rax (.mem (at_ .r15 cmO)), .alu32 .add .rax (imm 1), .store32 (at_ .r15 cmO) .rax,
        .alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)] t = some t' ∧
      Frame [⟨W + BitVec.ofNat 64 96, 4⟩] t.mem t'.mem ∧ t'.gpr .r12 = D + BitVec.ofNat 64 (16 * (j + 1)) ∧
      t'.gpr .rbx = BitVec.ofNat 64 (b - (j + 1)) ∧ t'.zf = some (decide (b - (j + 1) = 0)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbp], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have c₀ := E.perm.wR (show 96 + 4 ≤ 3816 by decide)
  have c₁ := E.perm.wW (show 96 + 4 ≤ 3816 by decide)
  refine ⟨_, by srun [h15, c₀, c₁, h12, hbx], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [gpr_arithFlags, gpr_setReg, mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg,
    wr_arithFlags, wr_setReg, zf_arithFlags, zf_setReg, ite_true, ite_false, reduceCtorEq]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, show 16 * j + 16 = 16 * (j + 1) by omega]
  · rw [Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega), Nat.sub_sub]
  · rw [Proof.AesGcm.X86_64.sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp

/-- A run of counter mode before block `j`. -/
structure CInv (K W SP : Addr) (R : Nat) (N A D : Addr) (al n b : Nat) (j : Nat) (t : State) : Prop where
  one : VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t
  buf : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t D n
  r12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j)
  rbx : t.gpr .rbx = BitVec.ofNat 64 (b - j)
  rbp : t.gpr .rbp = BitVec.ofNat 64 (n % 16)

theorem CInv.agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n b : Nat} {j : Nat} {t₁ t₂ : State}
    (h₁ : VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₁) (h₂ : VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₂) :
    VG.Proof.AesGcmSiv.X86_64.Both K W SP R N A D al n [.r12, .rbx, .rbp] t₁ t₂ :=
  ⟨h₁.one, h₂.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r12, h₂.r12]
    · rw [h₁.rbx, h₂.rbx]
    · rw [h₁.rbp, h₂.rbp]⟩

/-- A block, after its arguments: the call's, and the run's. -/
def BlkArgs (K W SP : Addr) (R : Nat) (N A D : Addr) (al n b : Nat) (j : Nat) (t : State) : Prop :=
  CtrCall t (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 112) (D + BitVec.ofNat 64 (16 * j))
    (W + BitVec.ofNat 64 1768) R 1 ∧ t.gpr .rsp = SP ∧ VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t

theorem blkArgs_wp {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n b : Nat}
    (hb : 16 * b ≤ n) {j : Nat} (hj : j < b) {t : State} (I : VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t) :
    WP isa (.block (copy16 cmO ccO ++ ptr .rdi .r15 skO ++ ctrArgs ++ ([.mov .rcx (.reg .r12)] : List Instr))) t
      (VG.Proof.AesGcmSiv.X86_64.BlkArgs K W SP R N A D al n b j) := by
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcmSiv.X86_64.blkArgs_ok L I.one.env I.one.sl I.r12
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := I.one.env.of_saved hg₁ hrd₁ hwr₁
  have hn := I.buf.lt
  have hD₁ := I.buf.of_eq hrd₁ hwr₁
  have hQ : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t₁ (D + BitVec.ofNat 64 (16 * j)) (16 * 1) := hD₁.slice (by omega)
  have hDw : Covers [⟨D, n⟩] t₁.wr := by rw [hwr₁, I.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp)
  refine WP.of_runBlock ⟨t₁, run₁, VG.Proof.AesGcmSiv.X86_64.cargs L E₁ hR (VG.Proof.AesGcmSiv.X86_64.keyS L E₁.perm) (c := 112) (by decide) (VG.Proof.AesGcmSiv.X86_64.srcBuf hQ)
    (hQ.w.sub_right (Lay.wSub (by decide))) (hQ.w.sub_right (Lay.wSub (show 248 + 240 ≤ 3816 by decide))).symm
    (Proof.AesGcm.X86_64.covers_off hDw (by omega) hn) rdi rsi rdx rcx r8 r9, E₁.rsp,
    ⟨⟨E₁, by rw [hm₁]; exact I.one.sl.of_frame (Proof.Cmac.frame_store2 _ _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      hwr₁.trans I.one.wr⟩, hD₁, by rw [hg₁ _ (by decide), I.r12], by rw [hg₁ _ (by decide), I.rbx],
      by rw [hg₁ _ (by decide), I.rbp]⟩⟩

theorem blkCalled_wp (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n b : Nat}
    (hb : 16 * b ≤ n) {j : Nat} (hj : j < b) {t : State} (h : VG.Proof.AesGcmSiv.X86_64.BlkArgs K W SP R N A D al n b j t) :
    WP isa (.call v.ctr.callee.name v.ctr.callee.code) t (VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j) := by
  obtain ⟨cc, hsp, I⟩ := h
  refine WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_
  have fc := P.frame
  rw [hsp] at fc
  refine ⟨⟨I.one.env.of_saved P.saved P.rd P.wr, I.one.sl.of_frame fc (fun q hq => ?_), P.wr.trans I.one.wr⟩,
    I.buf.of_eq P.rd P.wr, by rw [P.saved _ (by decide), I.r12], by rw [P.saved _ (by decide), I.rbx],
    by rw [P.saved _ (by decide), I.rbp]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact ((I.buf.w.sub_left (Offset.sub_base D (show 16 * j + 16 * 1 ≤ n by omega))).sub_right
      (Lay.wSub (by decide))).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

theorem blkEnd_wp {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n b : Nat} (hb : 16 * b ≤ n)
    {j : Nat} (hj : j < b) {t : State} (I : VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t) :
    WP isa (.block [.mov32 .rax (.mem (at_ .r15 cmO)), .alu32 .add .rax (imm 1), .store32 (at_ .r15 cmO) .rax,
        .alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)]) t fun t' =>
      VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b (j + 1) t' ∧ t'.zf = some (decide (b - (j + 1) = 0)) := by
  have hn := I.buf.lt
  obtain ⟨t', run', f', r12', rbx', zf', hg', hrd', hwr'⟩ := VG.Proof.AesGcmSiv.X86_64.blkEnd_ok I.one.env hj (by omega) I.r12 I.rbx
  exact WP.of_runBlock ⟨t', run', ⟨⟨I.one.env.keep (fun r hr => hg' r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd' hwr',
    I.one.sl.of_frame f' (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
    hwr'.trans I.one.wr⟩, I.buf.of_eq hrd' hwr', r12', rbx', by rw [hg' _ (by simp), I.rbp]⟩, zf'⟩

theorem blkArgs_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [.r12, .rbx, .rbp])
    (.block (copy16 cmO ccO ++ ptr .rdi .r15 skO ++ ctrArgs ++ ([.mov .rcx (.reg .r12)] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem blkEnd_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [.r12, .rbx, .rbp])
    (.block [.mov32 .rax (.mem (at_ .r15 cmO)), .alu32 .add .rax (imm 1), .store32 (at_ .r15 cmO) .rax,
      .alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)]) hc).isSome = true := ⟨_, by taint_decide⟩

/-- A block of counter mode, in two runs before the same block. -/
theorem blk_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n b : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hb : 16 * b ≤ n) {j : Nat}
    (hj : j < b) :
    RelCT isa (fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₁ ∧ VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₂) (cryptBlock v.callees)
      fun t₁ t₂ => (VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b (j + 1) t₁ ∧ t₁.zf = some (decide (b - (j + 1) = 0))) ∧
        (VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b (j + 1) t₂ ∧ t₂.zf = some (decide (b - (j + 1) = 0))) := by
  have r₁ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2) VG.Proof.AesGcmSiv.X86_64.blkArgs_check).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.BlkArgs K W SP R N A D al n b j) (F₂ := VG.Proof.AesGcmSiv.X86_64.BlkArgs K W SP R N A D al n b j)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.blkArgs_wp L hR hb hj h.1, VG.Proof.AesGcmSiv.X86_64.blkArgs_wp L hR hb hj h.2⟩
  have r₂ := (ctr_rel v.ctr (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.BlkArgs K W SP R N A D al n b j t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.BlkArgs K W SP R N A D al n b j t₂)
    fun t₁ t₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1]⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j) (F₂ := VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.blkCalled_wp v L hb hj h.2.1, VG.Proof.AesGcmSiv.X86_64.blkCalled_wp v L hb hj h.2.2⟩
  have r₃ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₂) hDW hn (fun t₁ t₂ h => h.2.1.agree h.2.2) VG.Proof.AesGcmSiv.X86_64.blkEnd_check).wp
    (F₁ := fun (t' : State) => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b (j + 1) t' ∧ t'.zf = some (decide (b - (j + 1) = 0)))
    (F₂ := fun (t' : State) => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b (j + 1) t' ∧ t'.zf = some (decide (b - (j + 1) = 0)))
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.blkEnd_wp L hb hj h.2.1, VG.Proof.AesGcmSiv.X86_64.blkEnd_wp L hb hj h.2.2⟩
  exact (RelCT.seq r₁ (RelCT.seq r₂ r₃)).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

/-- The whole blocks of counter mode, in two runs. -/
theorem blks_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n b : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hb : 16 * b ≤ n) (hb1 : 1 ≤ b) :
    RelCT isa (fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b 0 t₁ ∧ VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b 0 t₂)
      (.loop (cryptBlock v.callees) .ne)
      fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b b t₁ ∧ VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b b t₂ := by
  refine (RelCT.loop (fun m t₁ t₂ => ∃ j, m = b - j ∧ j < b ∧ VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₂) (fun m => ?_) (b - 0)).mono (fun t₁ t₂ h => ⟨0, rfl, hb1, h⟩) fun _ _ h => h
  refine RelCT.exists_ fun j => ?_
  by_cases hj : j < b
  · by_cases hm : m = b - j
    · subst hm
      refine (VG.Proof.AesGcmSiv.X86_64.blk_rel v L hR hDW hn hb hj).mono (fun t₁ t₂ h => ⟨h.2.2.1, h.2.2.2⟩)
        fun t₁ t₂ ⟨⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ => ⟨by rw [VG.Proof.AesGcmSiv.X86_64.eval_ne z₁, VG.Proof.AesGcmSiv.X86_64.eval_ne z₂], fun hc => ?_, fun hc => ?_⟩
      · rw [VG.Proof.AesGcmSiv.X86_64.eval_ne z₁] at hc
        have he : j + 1 = b := by simp at hc; omega
        rw [he] at I₁ I₂
        exact ⟨I₁, I₂⟩
      · rw [VG.Proof.AesGcmSiv.X86_64.eval_ne z₁] at hc
        have he : b - (j + 1) ≠ 0 := by simpa using hc
        exact ⟨b - (j + 1), by omega, j + 1, rfl, by omega, I₁, I₂⟩
    · exact RelCT.of_false fun _ _ h => hm h.1
  · exact RelCT.of_false fun _ _ h => hj h.2.1

/-! ## The last bytes, and the whole of counter mode -/

theorem tail2_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [.r12, .rbx, .rbp])
    (.seq (.block (([.mov .rdi (.reg .r12)] : List Instr) ++ ptr .rsi .r15 bO ++ ([.mov .rcx (.reg .rbp)] : List Instr)))
      xorLoop) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The tag's code leaves a run with the public arguments, and the registers. -/
theorem tag_cinv (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n b j : Nat} {t : State} (I : VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t) :
    WP isa (tag v.callees 128) t (VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j) :=
  WP.mono (VG.Proof.AesGcmSiv.X86_64.tag_ok v L hR I.one.env I.one.sl (o := 128) (by decide)) fun t' T =>
    ⟨⟨T.env, I.one.sl.of_frame T.frame (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w' (by decide)).symm), T.wr.trans I.one.wr⟩,
      I.buf.of_eq T.rd T.wr, by rw [T.saved _ (by decide), I.r12], by rw [T.saved _ (by decide), I.rbx],
      by rw [T.saved _ (by decide), I.rbp]⟩

/-- The last bytes, in two runs. -/
theorem tail_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n b j : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) :
    RelCT isa (fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₁ ∧ VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₂) (cryptTail v.callees)
      fun _ _ => True := by
  refine RelCT.assoc ?_
  show RelCT isa _ (.seq (tag v.callees 128) _) _
  have r₁ := (VG.Proof.AesGcmSiv.X86_64.tag_rel v L hR hDW hn (o := 128) (by decide)
    (P := fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₁ ∧ VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t₂)
    fun t₁ t₂ h => ⟨h.1.one, h.2.one, fun _ h => nomatch h⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j) (F₂ := VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.tag_cinv v L hR h.1, VG.Proof.AesGcmSiv.X86_64.tag_cinv v L hR h.2⟩
  exact RelCT.seq r₁ (VG.Proof.AesGcmSiv.X86_64.rel_taintC [.r12, .rbx, .rbp] hDW hn (fun t₁ t₂ h => h.2.1.agree h.2.2) VG.Proof.AesGcmSiv.X86_64.tail2_check)

/-- The start of `crypt`, in a run. -/
theorem head_cinv {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (O : VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t) (hD : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t D n) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 tagO)), .store (at_ .r15 cmO) .rax, .mov .rax (.mem (at_ .r15 (tagO + 8))),
        .movImm64 .rcx 0x8000000000000000, .alu .or .rax (.reg .rcx), .store (at_ .r15 (cmO + 8)) .rax,
        .mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov .rbx (.reg .rbp),
        .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)]) t fun t₁ =>
      VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n (n / 16) 0 t₁ ∧ t₁.zf = some (decide (n / 16 = 0)) := by
  obtain ⟨t₁, run₁, hm₁, h12₁, hbp₁, hbx₁, hzf₁, hg₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcmSiv.X86_64.cryptHead_ok L O.env O.sl hD
  refine WP.of_runBlock ⟨t₁, run₁, ⟨⟨O.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁,
    by rw [hm₁]; exact O.sl.of_frame (Proof.Cmac.frame_store2 _ _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
    hwr₁.trans O.wr⟩, hD.of_eq hrd₁ hwr₁, by rw [h12₁, Nat.mul_zero, BitVec.add_zero], by rw [hbx₁, Nat.sub_zero],
    hbp₁⟩, hzf₁⟩

theorem head_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [])
    (.block [.mov .rax (.mem (at_ .r15 tagO)), .store (at_ .r15 cmO) .rax, .mov .rax (.mem (at_ .r15 (tagO + 8))),
        .movImm64 .rcx 0x8000000000000000, .alu .or .rax (.reg .rcx), .store (at_ .r15 (cmO + 8)) .rax,
        .mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov .rbx (.reg .rbp),
        .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem test_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [.r12, .rbx, .rbp]) (.block [.alu .test .rbp (.reg .rbp)]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem test_cinv {K W SP : Addr} {R : Nat} {N A D : Addr} {al n b j : Nat} {t : State}
    (I : VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t) :
    WP isa (.block [.alu .test .rbp (.reg .rbp)]) t fun t' =>
      VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n b j t' ∧ t'.zf = some (decide (n % 16 = 0)) := by
  have hn := I.buf.lt
  refine WP.of_runBlock ⟨_, by srun [], ?_, ?_⟩
  · exact ⟨⟨I.one.env.keep (fun _ _ => by simp only [gpr_arithFlags]) rfl rfl, I.one.sl, I.one.wr⟩, I.buf.of_eq rfl rfl,
      by simp only [gpr_arithFlags, I.r12], by simp only [gpr_arithFlags, I.rbx], by simp only [gpr_arithFlags, I.rbp]⟩
  · simp only [zf_arithFlags, I.rbp]
    rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]

/-- `crypt`, in two runs with the same public arguments. -/
theorem crypt_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → (VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t₁ ∧ VG.Proof.AesGcmSiv.X86_64.Buf K W SP t₁ D n) ∧
      (VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t₂ ∧ VG.Proof.AesGcmSiv.X86_64.Buf K W SP t₂ D n)) :
    RelCT isa P (crypt v.callees) fun _ _ => True := by
  have r₁ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.1, (hP _ _ h).2.1, fun _ h => nomatch h⟩)
    VG.Proof.AesGcmSiv.X86_64.head_check).wp
    (F₁ := fun (t₁ : State) => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n (n / 16) 0 t₁ ∧ t₁.zf = some (decide (n / 16 = 0)))
    (F₂ := fun (t₁ : State) => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n (n / 16) 0 t₁ ∧ t₁.zf = some (decide (n / 16 = 0)))
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.head_cinv L (hP _ _ h).1.1 (hP _ _ h).1.2, VG.Proof.AesGcmSiv.X86_64.head_cinv L (hP _ _ h).2.1 (hP _ _ h).2.2⟩
  have r₂ : RelCT isa (fun t₁ t₂ => True ∧ (VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n (n / 16) 0 t₁ ∧
        t₁.zf = some (decide (n / 16 = 0))) ∧ (VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n (n / 16) 0 t₂ ∧
        t₂.zf = some (decide (n / 16 = 0))))
      (.ite .e (.block []) (.loop (cryptBlock v.callees) .ne))
      fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n (n / 16) (n / 16) t₁ ∧ VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n (n / 16) (n / 16) t₂ := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [VG.Proof.AesGcmSiv.X86_64.eval_e h.2.1.2, VG.Proof.AesGcmSiv.X86_64.eval_e h.2.2.2]) ?_ ?_
    · refine RelCT.block_nil fun t₁ t₂ h => ?_
      have h0 : n / 16 = 0 := by have := h.2; rw [VG.Proof.AesGcmSiv.X86_64.eval_e h.1.2.1.2] at this; simpa using this
      have a := h.1.2.1.1
      have b := h.1.2.2.1
      rw [h0] at a b ⊢
      exact ⟨a, b⟩
    · by_cases h0 : n / 16 = 0
      · refine RelCT.of_false fun t₁ t₂ h => ?_
        have := h.2
        rw [VG.Proof.AesGcmSiv.X86_64.eval_e h.1.2.1.2] at this
        simp [h0] at this
      · exact (VG.Proof.AesGcmSiv.X86_64.blks_rel v L hR hDW hn (b := n / 16) (by omega) (by omega)).mono
          (fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h
  have r₃ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n (n / 16) (n / 16) t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n (n / 16) (n / 16) t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2) VG.Proof.AesGcmSiv.X86_64.test_check).wp
    (F₁ := fun (t : State) => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n (n / 16) (n / 16) t ∧ t.zf = some (decide (n % 16 = 0)))
    (F₂ := fun (t : State) => VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n (n / 16) (n / 16) t ∧ t.zf = some (decide (n % 16 = 0)))
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.test_cinv h.1, VG.Proof.AesGcmSiv.X86_64.test_cinv h.2⟩
  have r₄ : RelCT isa (fun t₁ t₂ => True ∧ (VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n (n / 16) (n / 16) t₁ ∧
        t₁.zf = some (decide (n % 16 = 0))) ∧ (VG.Proof.AesGcmSiv.X86_64.CInv K W SP R N A D al n (n / 16) (n / 16) t₂ ∧
        t₂.zf = some (decide (n % 16 = 0))))
      (.ite .e (.block []) (cryptTail v.callees)) fun _ _ => True :=
    RelCT.ite (fun t₁ t₂ h => by rw [VG.Proof.AesGcmSiv.X86_64.eval_e h.2.1.2, VG.Proof.AesGcmSiv.X86_64.eval_e h.2.2.2]) (RelCT.block_nil fun _ _ _ => trivial)
      ((VG.Proof.AesGcmSiv.X86_64.tail_rel v L hR hDW hn).mono (fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ _ => trivial)
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ r₄))

end VG.Proof.AesGcmSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86_64.PolyvalCT`. -/
section

/-!
# AES-GCM-SIV on x86-64: the keys and POLYVAL are constant time

Untrusted: everything here is checked by Lean. Both runs derive the same
number of blocks (`rounds / 2 − 1`), from a slot; the code around the calls
passes the taint analysis, and each call has the same arguments in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl CtrCall ctr_rel ctr_call KeyCall key_rel key_call)

/-- A run of `derive` before block `i`. -/
structure DCInv (K W SP : Addr) (R : Nat) (N A D : Addr) (al n i : Nat) (t : State) : Prop where
  one : VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t
  nonce : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t N 12
  rbx : t.gpr .rbx = BitVec.ofNat 64 i
  rbp : t.gpr .rbp = BitVec.ofNat 64 (R / 2 - 1)
  r12 : t.gpr .r12 = W + BitVec.ofNat 64 (16 + 8 * i)

theorem DCInv.agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n i : Nat} {t₁ t₂ : State}
    (h₁ : VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i t₁) (h₂ : VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i t₂) :
    VG.Proof.AesGcmSiv.X86_64.Both K W SP R N A D al n [.rbx, .rbp, .r12] t₁ t₂ :=
  ⟨h₁.one, h₂.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.rbx, h₂.rbx]
    · rw [h₁.rbp, h₂.rbp]
    · rw [h₁.r12, h₂.r12]⟩

/-- A step of `derive`, after its arguments. -/
def DArgs (K W SP : Addr) (R : Nat) (N A D : Addr) (al n i : Nat) (t : State) : Prop :=
  CtrCall t K (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 128) (W + BitVec.ofNat 64 1768) R 1 ∧
    t.gpr .rsp = SP ∧ VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i t

theorem dArgs_wp {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n i : Nat}
    {t : State} (I : VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i t) :
    WP isa (.block (deriveBlock ++ ([.mov .rdi (.reg .r13)] : List Instr) ++ ctrArgs ++ ptr .rcx .r15 bO)) t
      (VG.Proof.AesGcmSiv.X86_64.DArgs K W SP R N A D al n i) := by
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ :=
    VG.Proof.AesGcmSiv.X86_64.derArgs_ok I.one.env I.one.sl I.nonce I.rbx
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := I.one.env.keep (fun r hr => hg₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
    hrd₁ hwr₁
  have f₁ : Frame [⟨W + BitVec.ofNat 64 112, 32⟩] t.mem t₁.mem := by
    rw [hm₁]
    exact ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 128) (n := 8) (e := 112) (k := 32) (by decide)
        (by decide) (by have := L.ww; omega)) |>.writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 136) (n := 8) (e := 112) (k := 32) (by decide)
        (by decide) (by have := L.ww; omega))
  exact WP.of_runBlock ⟨t₁, run₁, VG.Proof.AesGcmSiv.X86_64.cargs L E₁ hR (VG.Proof.AesGcmSiv.X86_64.keyK L E₁.perm) (c := 112) (by decide)
    (VG.Proof.AesGcmSiv.X86_64.srcW L E₁.perm (t := 128) (k := 16 * 1) (by decide)) (L.w_w (.inr (by decide)) (by decide) (by decide))
    (L.k_w' (by decide)) (E₁.perm.wC (by decide)) rdi rsi rdx rcx r8 r9, E₁.rsp,
    ⟨E₁, I.one.sl.of_frame f₁ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      hwr₁.trans I.one.wr⟩, I.nonce.of_eq hrd₁ hwr₁, by rw [hg₁ _ (by simp), I.rbx], by rw [hg₁ _ (by simp), I.rbp],
    by rw [hg₁ _ (by simp), I.r12]⟩

theorem dCalled_wp (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n i : Nat}
    {t : State} (h : VG.Proof.AesGcmSiv.X86_64.DArgs K W SP R N A D al n i t) :
    WP isa (.call v.ctr.callee.name v.ctr.callee.code) t (VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i) := by
  obtain ⟨cc, hsp, I⟩ := h
  refine WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_
  have fc := P.frame
  rw [hsp] at fc
  refine ⟨⟨I.one.env.of_saved P.saved P.rd P.wr, I.one.sl.of_frame fc (fun q hq => ?_), P.wr.trans I.one.wr⟩,
    I.nonce.of_eq P.rd P.wr, by rw [P.saved _ (by decide), I.rbx], by rw [P.saved _ (by decide), I.rbp],
    by rw [P.saved _ (by decide), I.r12]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

theorem dPost_wp {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n i : Nat}
    (hi : i < R / 2 - 1) {t : State} (I : VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i t) :
    WP isa (.block VG.Proof.AesGcmSiv.X86_64.derPost) t fun t' =>
      VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n (i + 1) t' ∧ t'.zf = some (decide (i + 1 = R / 2 - 1)) := by
  obtain ⟨t', run', hm', bx', bp', r12', zf', hg', hrd', hwr'⟩ :=
    VG.Proof.AesGcmSiv.X86_64.derPost_ok I.one.env hi (by omega) I.rbx I.rbp I.r12
  have f' : Frame [⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩] t.mem t'.mem := by
    rw [hm']; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact WP.of_runBlock ⟨t', run', ⟨⟨I.one.env.keep hg' hrd' hwr', I.one.sl.of_frame f' (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by omega)) (by decide) (by omega)),
    hwr'.trans I.one.wr⟩, I.nonce.of_eq hrd' hwr', bx', bp', r12'⟩, zf'⟩

theorem dArgs_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [.rbx, .rbp, .r12])
    (.block (deriveBlock ++ ([.mov .rdi (.reg .r13)] : List Instr) ++ ctrArgs ++ ptr .rcx .r15 bO)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dPost_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [.rbx, .rbp, .r12]) (.block VG.Proof.AesGcmSiv.X86_64.derPost) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A step of `derive`, in two runs before the same block. -/
theorem dStep_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {i : Nat} (hi : i < R / 2 - 1) :
    RelCT isa (fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i t₁ ∧ VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i t₂)
      (.seq (.block (deriveBlock ++ ([.mov .rdi (.reg .r13)] : List Instr) ++ ctrArgs ++ ptr .rcx .r15 bO))
        (.seq (callCtr v.callees) (.block VG.Proof.AesGcmSiv.X86_64.derPost)))
      fun t₁ t₂ => (VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n (i + 1) t₁ ∧ t₁.zf = some (decide (i + 1 = R / 2 - 1))) ∧
        (VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n (i + 1) t₂ ∧ t₂.zf = some (decide (i + 1 = R / 2 - 1))) := by
  have r₁ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [.rbx, .rbp, .r12] (P := fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2) VG.Proof.AesGcmSiv.X86_64.dArgs_check).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.DArgs K W SP R N A D al n i) (F₂ := VG.Proof.AesGcmSiv.X86_64.DArgs K W SP R N A D al n i)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.dArgs_wp L hR h.1, VG.Proof.AesGcmSiv.X86_64.dArgs_wp L hR h.2⟩
  have r₂ := (ctr_rel v.ctr (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.DArgs K W SP R N A D al n i t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.DArgs K W SP R N A D al n i t₂)
    fun t₁ t₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1]⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i) (F₂ := VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.dCalled_wp v L h.2.1, VG.Proof.AesGcmSiv.X86_64.dCalled_wp v L h.2.2⟩
  have r₃ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [.rbx, .rbp, .r12] (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i t₂) hDW hn (fun t₁ t₂ h => h.2.1.agree h.2.2) VG.Proof.AesGcmSiv.X86_64.dPost_check).wp
    (F₁ := fun (t' : State) => VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n (i + 1) t' ∧ t'.zf = some (decide (i + 1 = R / 2 - 1)))
    (F₂ := fun (t' : State) => VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n (i + 1) t' ∧ t'.zf = some (decide (i + 1 = R / 2 - 1)))
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.dPost_wp L hR hi h.2.1, VG.Proof.AesGcmSiv.X86_64.dPost_wp L hR hi h.2.2⟩
  exact (RelCT.seq r₁ (RelCT.seq r₂ r₃)).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

theorem dInit_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT []) (.block (([.mov32 .rbx (imm 0)] : List Instr) ++ ptr .r12 .r15 akO ++
    ([.mov .rbp (.mem (at_ .r15 roundsO)), .shift .shr .rbp 1, .alu .sub .rbp (imm 1)] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem slots_derR {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) : ∀ q ∈ VG.Proof.AesGcmSiv.X86_64.derR W SP, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint q := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

theorem dInit_wp {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    {σ : State} (O : VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n σ) (hN : VG.Proof.AesGcmSiv.X86_64.Buf K W SP σ N 12) :
    WP isa (.block (([.mov32 .rbx (imm 0)] : List Instr) ++ ptr .r12 .r15 akO ++
      ([.mov .rbp (.mem (at_ .r15 roundsO)), .shift .shr .rbp 1, .alu .sub .rbp (imm 1)] : List Instr))) σ
      (VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n 0) :=
  WP.mono (VG.Proof.AesGcmSiv.X86_64.derInit_ok O.env hR O.sl) fun t I =>
    ⟨⟨I.env, O.sl.of_frame I.frame (VG.Proof.AesGcmSiv.X86_64.slots_derR L), I.wr.trans O.wr⟩, hN.of_eq I.rd I.wr, I.rbx, I.rbp,
      by rw [I.r12]⟩

/-- `derive`, in two runs with the same public arguments. -/
theorem derive_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → (VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t₁ ∧ VG.Proof.AesGcmSiv.X86_64.Buf K W SP t₁ N 12) ∧
      (VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t₂ ∧ VG.Proof.AesGcmSiv.X86_64.Buf K W SP t₂ N 12)) :
    RelCT isa P (derive v.callees) fun t₁ t₂ =>
      VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n (R / 2 - 1) t₁ ∧ VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n (R / 2 - 1) t₂ := by
  have r₁ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.1, (hP _ _ h).2.1, fun _ h => nomatch h⟩)
    VG.Proof.AesGcmSiv.X86_64.dInit_check).wp (F₁ := VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n 0) (F₂ := VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n 0)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.dInit_wp L hR (hP _ _ h).1.1 (hP _ _ h).1.2, VG.Proof.AesGcmSiv.X86_64.dInit_wp L hR (hP _ _ h).2.1 (hP _ _ h).2.2⟩
  refine RelCT.seq r₁ ?_
  refine (RelCT.loop (fun m t₁ t₂ => ∃ i, m = (R / 2 - 1) - i ∧ i < R / 2 - 1 ∧ VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n i t₂) (fun m => ?_) ((R / 2 - 1) - 0)).mono
    (fun t₁ t₂ h => ⟨0, rfl, by omega, h.2.1, h.2.2⟩) fun _ _ h => h
  refine RelCT.exists_ fun i => ?_
  by_cases hi : i < R / 2 - 1
  · by_cases hm : m = (R / 2 - 1) - i
    · subst hm
      refine (VG.Proof.AesGcmSiv.X86_64.dStep_rel v L hR hDW hn hi).mono (fun t₁ t₂ h => ⟨h.2.2.1, h.2.2.2⟩)
        fun t₁ t₂ ⟨⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ => ⟨by rw [VG.Proof.AesGcmSiv.X86_64.eval_ne z₁, VG.Proof.AesGcmSiv.X86_64.eval_ne z₂], fun hc => ?_, fun hc => ?_⟩
      · rw [VG.Proof.AesGcmSiv.X86_64.eval_ne z₁] at hc
        have he : i + 1 = R / 2 - 1 := by simpa using hc
        rw [he] at I₁ I₂
        exact ⟨I₁, I₂⟩
      · rw [VG.Proof.AesGcmSiv.X86_64.eval_ne z₁] at hc
        have he : i + 1 ≠ R / 2 - 1 := by simpa using hc
        exact ⟨(R / 2 - 1) - (i + 1), by omega, i + 1, rfl, by omega, I₁, I₂⟩
    · exact RelCT.of_false fun _ _ h => hm h.1
  · exact RelCT.of_false fun _ _ h => hi h.2.1

theorem expArgs_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT []) (.block (ptr .rdi .r15 ekO ++
    ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6), .alu .add .rsi (.reg .rsi),
      .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO ++ ptr .rcx .r15 scrO)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem hkey_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT []) (.block hkey) hc).isSome = true := ⟨_, by taint_decide⟩

theorem expArgs_wp {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    {t : State} (O : VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t) :
    WP isa (.block (ptr .rdi .r15 ekO ++ ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6),
      .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO ++
      ptr .rcx .r15 scrO)) t fun t₁ =>
      KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 1768)
        (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP := by
  obtain ⟨t₁, run₁, -, rdi, rsi, rdx, rcx, hg₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcmSiv.X86_64.expArgs_ok hR O.env O.sl
  have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := O.env.of_saved hg₁ hrd₁ hwr₁
  have hl : Spec.GcmSiv.keyLen R = 16 ∨ Spec.GcmSiv.keyLen R = 32 := by unfold Spec.GcmSiv.keyLen; omega
  exact WP.of_runBlock ⟨t₁, run₁, VG.Proof.AesGcmSiv.X86_64.kargs L E₁ hl rdi rsi rdx rcx, E₁.rsp⟩

/-- `keys`, in two runs with the same public arguments. -/
theorem keys_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → (VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t₁ ∧ VG.Proof.AesGcmSiv.X86_64.Buf K W SP t₁ N 12) ∧
      (VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t₂ ∧ VG.Proof.AesGcmSiv.X86_64.Buf K W SP t₂ N 12)) :
    RelCT isa P (VG.Impl.AesGcmSiv.X86_64.keys v.callees) fun _ _ => True := by
  refine RelCT.seq (VG.Proof.AesGcmSiv.X86_64.derive_rel v L hR hDW hn hP) ?_
  have one_exp : ∀ {t : State}, VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t → WP isa (.seq (.block (ptr .rdi .r15 ekO ++
      ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6), .alu .add .rsi (.reg .rsi),
        .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO ++ ptr .rcx .r15 scrO))
      (.call v.key.fn.name v.key.fn.code)) t (VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n) :=
    fun O => WP.mono (VG.Proof.AesGcmSiv.X86_64.expand_ok v L hR O.env O.sl) fun t' X => ⟨X.env, O.sl.of_frame X.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm), X.wr.trans O.wr⟩
  have r₁ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [] (P := fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n (R / 2 - 1) t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.DCInv K W SP R N A D al n (R / 2 - 1) t₂) hDW hn (fun t₁ t₂ h => ⟨h.1.one, h.2.one, fun _ h => nomatch h⟩)
    VG.Proof.AesGcmSiv.X86_64.expArgs_check).wp
    (F₁ := fun (t₁ : State) => KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248)
      (W + BitVec.ofNat 64 1768) (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP)
    (F₂ := fun (t₁ : State) => KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248)
      (W + BitVec.ofNat 64 1768) (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.expArgs_wp L hR h.1.one, VG.Proof.AesGcmSiv.X86_64.expArgs_wp L hR h.2.one⟩
  have r₂ := (RelCT.seq r₁ (key_rel v.key fun t₁ t₂ h =>
    ⟨_, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n) (F₂ := VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n)
    fun t₁ t₂ h => ⟨one_exp h.1.one, one_exp h.2.one⟩
  exact RelCT.seq r₂ (VG.Proof.AesGcmSiv.X86_64.rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨h.2.1, h.2.2, fun _ h => nomatch h⟩) VG.Proof.AesGcmSiv.X86_64.hkey_check)

end VG.Proof.AesGcmSiv.X86_64

/-!
## POLYVAL is constant time

Untrusted: everything here is checked by Lean. Both runs absorb the same
chunks of blocks: their number depends only on the lengths, which are
public; the code around each call of `vg_ghash` passes the taint analysis,
and each call has the same arguments in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl GhCall gh_rel gh_call toNat_ofNat_of_lt)

/-- `(a; (b; c)); d`, related as `a; (b; (c; d))`. -/
theorem rel_assoc3 {P Q : State → State → Prop} {a b c d : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b c)) d) Q) : RelCT isa P (.seq a (.seq b (.seq c d))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ d₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ d₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ c₁)) d₁) (.seq (.seq a₂ (.seq b₂ c₂)) d₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- `(a; (b; (c; (d; e)))); g`, related as `a; (b; (c; (d; (e; g))))`. -/
theorem rel_assoc5 {P Q : State → State → Prop} {a b c d e g : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c (.seq d e)))) g) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d (.seq e g))))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
  | seq d₁ e₁ => cases e₁ with | seq e₁' g₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
  | seq d₂ e₂ => cases e₂ with | seq e₂' g₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ e₁')))) g₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ e₂')))) g₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-! ## The chunks -/

/-- A run of the chunks of `b` blocks at `Q`, after `d` of them, with
`nr` bytes left after them. -/
structure AInv (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (Q : Addr) (b nr d : Nat) (t : State) :
    Prop where
  one : VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t
  buf : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t Q (16 * b)
  res : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t (Q + BitVec.ofNat 64 (16 * b)) nr
  r12 : t.gpr .r12 = Q + BitVec.ofNat 64 (16 * d)
  rbx : t.gpr .rbx = BitVec.ofNat 64 (b - d)
  rbp : t.gpr .rbp = BitVec.ofNat 64 nr

theorem AInv.agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d : Nat} {t₁ t₂ : State}
    (h₁ : VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr d t₁) (h₂ : VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr d t₂) :
    VG.Proof.AesGcmSiv.X86_64.Both K W SP R N A D al n [.r12, .rbx, .rbp] t₁ t₂ :=
  ⟨h₁.one, h₂.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r12, h₂.r12]
    · rw [h₁.rbx, h₂.rbx]
    · rw [h₁.rbp, h₂.rbp]⟩

/-- A chunk after its call, or up to it: the run, `k`, and the call's arguments. -/
structure AMid (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (Q : Addr) (b nr d k : Nat) (t : State) :
    Prop where
  inv : VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr d t
  r14 : t.gpr .r14 = BitVec.ofNat 64 k

theorem AMid.agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d k : Nat} {t₁ t₂ : State}
    (h₁ : VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d k t₁) (h₂ : VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d k t₂) :
    VG.Proof.AesGcmSiv.X86_64.Both K W SP R N A D al n [.r12, .rbx, .rbp, .r14] t₁ t₂ :=
  ⟨h₁.inv.one, h₂.inv.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.inv.r12, h₂.inv.r12]
    · rw [h₁.inv.rbx, h₂.inv.rbx]
    · rw [h₁.inv.rbp, h₂.inv.rbp]
    · rw [h₁.r14, h₂.r14]⟩

theorem chunkPre_wp {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d : Nat}
    (hd : d < b) {t : State} (I : VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr d t) :
    WP isa (.seq (.block [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)])
      (.seq (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block []))
      (.seq (.block (([.mov .rsi (.reg .r12)] : List Instr) ++ ptr .rdi .r15 revO))
      (.seq revLoop (.block (ghArgs ++ ptr .rdx .r15 revO ++ ([.mov .rcx (.reg .r14)] : List Instr))))))) t
      fun t₅ => GhCall t₅ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₅.gpr .rsp = SP ∧
        VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₅ := by
  have hQ : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t (Q + BitVec.ofNat 64 (16 * d)) (16 * (b - d)) := I.buf.slice (by omega)
  refine WP.mono (VG.Proof.AesGcmSiv.X86_64.chunkPre_ok L I.one.env (by omega) hQ I.r12 I.rbx) fun t₅ Pr => ⟨Pr.call, Pr.env.rsp, ?_, Pr.r14⟩
  refine ⟨⟨Pr.env, I.one.sl.of_frame Pr.frame (fun q hq => ?_), Pr.wr.trans I.one.wr⟩, I.buf.of_eq Pr.rd Pr.wr,
    I.res.of_eq Pr.rd Pr.wr, by rw [Pr.regs _ (by simp), I.r12], by rw [Pr.regs _ (by simp), I.rbx], by rw [Pr.regs _ (by simp), I.rbp]⟩
  simp only [List.mem_singleton] at hq; subst hq
  exact L.w_w (.inl (by decide)) (by decide) (by omega)

theorem chunkCalled_wp (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    {Q : Addr} {b nr d k : Nat} {t : State} (h : GhCall t (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80)
      (W + BitVec.ofNat 64 488) (W + BitVec.ofNat 64 1512) k ∧ t.gpr .rsp = SP ∧
      VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d k t) :
    WP isa (.call v.gh.fn.name v.gh.fn.code) t (VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d k) := by
  obtain ⟨gc, hsp, M⟩ := h
  refine WP.mono (gh_call v.gh gc) fun t₆ P => ?_
  have fc := P.frame
  rw [hsp] at fc
  refine ⟨⟨⟨M.inv.one.env.of_saved P.saved P.rd P.wr, M.inv.one.sl.of_frame fc (fun q hq => ?_),
    P.wr.trans M.inv.one.wr⟩, M.inv.buf.of_eq P.rd P.wr, M.inv.res.of_eq P.rd P.wr, by rw [P.saved _ (by decide), M.inv.r12],
    by rw [P.saved _ (by decide), M.inv.rbx], by rw [P.saved _ (by decide), M.inv.rbp]⟩,
    by rw [P.saved _ (by decide), M.r14]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- The end of a chunk: the pointer and the count past it. -/
theorem chunkEnd_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d : Nat} (hd : d < b)
    {t : State} (M : VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t) :
    WP isa (.block [.mov .rax (.reg .r14), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .r12 (.reg .rax), .alu .sub .rbx (.reg .r14)]) t
      fun t' => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t' ∧
        t'.zf = some (decide (b - (d + min (b - d) 64) = 0)) := by
  have hbl : b < 2 ^ 60 := by have := M.inv.buf.lt; omega
  refine WP.of_runBlock ⟨_, by srun [], ?_, ?_⟩
  · refine ⟨⟨M.inv.one.env.keep (fun r hr => ?_) rfl rfl, M.inv.one.sl, M.inv.one.wr⟩, M.inv.buf.of_eq rfl rfl,
      M.inv.res.of_eq rfl rfl, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, M.inv.r12, M.r14,
        Proof.AesGcm.X86_64.times16_val, VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc, Nat.mul_add]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, M.inv.rbx, M.r14]
      rw [Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega), Nat.sub_sub]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, M.inv.rbp]
  · simp only [zf_setReg, zf_arithFlags, gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, M.inv.rbx,
      M.r14, Proof.AesGcm.X86_64.sub_beq (show b - d < 2 ^ 64 by omega) (show min (b - d) 64 < 2 ^ 64 by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

theorem chunkPre_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [.r12, .rbx, .rbp])
    (.seq (.block [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)])
      (.seq (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block []))
      (.seq (.block (([.mov .rsi (.reg .r12)] : List Instr) ++ ptr .rdi .r15 revO))
      (.seq revLoop (.block (ghArgs ++ ptr .rdx .r15 revO ++ ([.mov .rcx (.reg .r14)] : List Instr))))))) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem chunkEnd_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [.r12, .rbx, .rbp, .r14])
    (.block [.mov .rax (.reg .r14), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .r12 (.reg .rax), .alu .sub .rbx (.reg .r14)])
    hc).isSome = true := ⟨_, by taint_decide⟩

/-- A chunk, in two runs after the same blocks. -/
theorem chunk_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {Q : Addr} {b nr d : Nat} (hd : d < b) :
    RelCT isa (fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr d t₁ ∧ VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr d t₂)
      (absorbChunk v.callees)
      fun t₁ t₂ => (VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t₁ ∧
          t₁.zf = some (decide (b - (d + min (b - d) 64) = 0))) ∧
        (VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t₂ ∧
          t₂.zf = some (decide (b - (d + min (b - d) 64) = 0))) := by
  refine VG.Proof.AesGcmSiv.X86_64.rel_assoc5 ?_
  have r₁ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr d t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr d t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2) VG.Proof.AesGcmSiv.X86_64.chunkPre_check).wp
    (F₁ := fun (t₅ : State) => GhCall t₅ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₅.gpr .rsp = SP ∧
        VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₅)
    (F₂ := fun (t₅ : State) => GhCall t₅ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₅.gpr .rsp = SP ∧
        VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₅)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.chunkPre_wp L hd h.1, VG.Proof.AesGcmSiv.X86_64.chunkPre_wp L hd h.2⟩
  have r₂ := (gh_rel v.gh (P := fun t₁ t₂ => True ∧ (GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80)
        (W + BitVec.ofNat 64 488) (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₁.gpr .rsp = SP ∧
        VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₁) ∧
      (GhCall t₂ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₂.gpr .rsp = SP ∧
        VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₂))
    fun t₁ t₂ h => ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1]⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d (min (b - d) 64))
    (F₂ := VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d (min (b - d) 64))
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.chunkCalled_wp v L h.2.1, VG.Proof.AesGcmSiv.X86_64.chunkCalled_wp v L h.2.2⟩
  have r₃ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [.r12, .rbx, .rbp, .r14] (P := fun t₁ t₂ => True ∧
      VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₁ ∧ VG.Proof.AesGcmSiv.X86_64.AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₂)
      hDW hn (fun t₁ t₂ h => h.2.1.agree h.2.2) VG.Proof.AesGcmSiv.X86_64.chunkEnd_check).wp
    (F₁ := fun (t' : State) => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t' ∧
      t'.zf = some (decide (b - (d + min (b - d) 64) = 0)))
    (F₂ := fun (t' : State) => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t' ∧
      t'.zf = some (decide (b - (d + min (b - d) 64) = 0)))
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.chunkEnd_wp hd h.2.1, VG.Proof.AesGcmSiv.X86_64.chunkEnd_wp hd h.2.2⟩
  exact (RelCT.seq r₁ (RelCT.seq r₂ r₃)).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

/-- The chunks, in two runs. -/
theorem chunks_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {Q : Addr} {b nr : Nat} (hb : 1 ≤ b) :
    RelCT isa (fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr 0 t₁ ∧ VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr 0 t₂)
      (.loop (absorbChunk v.callees) .ne)
      fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr b t₁ ∧ VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr b t₂ := by
  refine (RelCT.loop (fun m t₁ t₂ => ∃ d, m = b - d ∧ d < b ∧ VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr d t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr d t₂) (fun m => ?_) (b - 0)).mono
    (fun t₁ t₂ h => ⟨0, rfl, hb, h⟩) fun _ _ h => h
  refine RelCT.exists_ fun d => ?_
  by_cases hd : d < b
  · by_cases hm : m = b - d
    · subst hm
      refine (VG.Proof.AesGcmSiv.X86_64.chunk_rel v L hDW hn hd).mono (fun t₁ t₂ h => ⟨h.2.2.1, h.2.2.2⟩)
        fun t₁ t₂ ⟨⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ => ⟨by rw [VG.Proof.AesGcmSiv.X86_64.eval_ne z₁, VG.Proof.AesGcmSiv.X86_64.eval_ne z₂], fun hc => ?_, fun hc => ?_⟩
      · rw [VG.Proof.AesGcmSiv.X86_64.eval_ne z₁] at hc
        have he : d + min (b - d) 64 = b := by simp at hc; omega
        rw [he] at I₁ I₂
        exact ⟨I₁, I₂⟩
      · rw [VG.Proof.AesGcmSiv.X86_64.eval_ne z₁] at hc
        have he : b - (d + min (b - d) 64) ≠ 0 := by simpa using hc
        exact ⟨b - (d + min (b - d) 64), by omega, d + min (b - d) 64, rfl, by omega, I₁, I₂⟩
    · exact RelCT.of_false fun _ _ h => hm h.1
  · exact RelCT.of_false fun _ _ h => hd h.2.1

/-! ## The last bytes and `absorb` -/

theorem tailPre_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [.r12, .rbx, .rbp])
    (.seq (.block (zero16 bO ++ ptr .rdi .r15 bO ++ ([.mov .rsi (.reg .r12), .mov .rcx (.reg .rbp)] : List Instr)))
      (.seq copyLoop (.block (([.mov .rax (.mem (at_ .r15 bO)), .mov .rdx (.mem (at_ .r15 (bO + 8))), .bswap .rax,
        .bswap .rdx, .store (at_ .r15 revO) .rdx, .store (at_ .r15 (revO + 8)) .rax] : List Instr) ++ ghArgs ++
        ptr .rdx .r15 revO ++ ([.mov32 .rcx (imm 1)] : List Instr))))) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The last bytes, in two runs. -/
theorem absTail_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {Q : Addr} {b nr : Nat} (hr1 : 1 ≤ nr)
    (hr : nr < 16) :
    RelCT isa (fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr b t₁ ∧ VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr b t₂)
      (absorbTail v.callees) fun _ _ => True := by
  have pre : ∀ {t : State}, VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr b t → WP isa _ t fun t₃ =>
      GhCall t₃ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₃.gpr .rsp = SP := fun I =>
    WP.mono (VG.Proof.AesGcmSiv.X86_64.tailPre_ok L I.one.env hr1 hr I.res I.r12 I.rbp) fun _ Tp => ⟨Tp.call, Tp.env.rsp⟩
  refine VG.Proof.AesGcmSiv.X86_64.rel_assoc3 (RelCT.seq ((VG.Proof.AesGcmSiv.X86_64.rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ =>
      VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr b t₁ ∧ VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr b t₂) hDW hn
      (fun t₁ t₂ h => h.1.agree h.2) VG.Proof.AesGcmSiv.X86_64.tailPre_check).wp
    (F₁ := fun (t₃ : State) => GhCall t₃ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₃.gpr .rsp = SP)
    (F₂ := fun (t₃ : State) => GhCall t₃ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₃.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨pre h.1, pre h.2⟩) ?_)
  exact gh_rel v.gh fun t₁ t₂ h => ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩

/-- What `absorb` is given: `nb` bytes at `Q`. -/
structure AbsIn (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (Q : Addr) (nb : Nat) (t : State) : Prop where
  one : VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t
  buf : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t Q nb
  r12 : t.gpr .r12 = Q
  rbp : t.gpr .rbp = BitVec.ofNat 64 nb

theorem absHead_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {nb : Nat} {t : State}
    (h : VG.Proof.AesGcmSiv.X86_64.AbsIn K W SP R N A D al n Q nb t) :
    WP isa (.block [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)]) t
      fun t₁ => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₁ ∧ t₁.zf = some (decide (nb / 16 = 0)) := by
  have hn := h.buf.lt
  have hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 nb)
  rw [toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  refine WP.of_runBlock ⟨_, by srun [], ?_, ?_⟩
  · refine ⟨⟨h.one.env.keep (fun r hr => ?_) rfl rfl, h.one.sl, h.one.wr⟩, (h.buf.take (by omega)).of_eq rfl rfl,
      (h.buf.slice (by omega)).of_eq rfl rfl, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h.r12, Nat.mul_zero,
        BitVec.add_zero]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h.rbp,
        Proof.AesGcm.X86_64.shr4 _ hn, Nat.sub_zero]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h.rbp, hand]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
      reduceCtorEq, h.rbp, Proof.AesGcm.X86_64.shr4 _ hn]
    rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]

theorem absHead_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [.r12, .rbp])
    (.block [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem absTest_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d : Nat} (hnr : nr < 16)
    {t : State} (I : VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr d t) :
    WP isa (.block [.alu .test .rbp (.reg .rbp)]) t fun t' =>
      VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q b nr d t' ∧ t'.zf = some (decide (nr = 0)) := by
  refine WP.of_runBlock ⟨_, by srun [], ?_, ?_⟩
  · exact ⟨⟨I.one.env.keep (fun _ _ => by simp only [gpr_arithFlags]) rfl rfl, I.one.sl, I.one.wr⟩,
      I.buf.of_eq rfl rfl, I.res.of_eq rfl rfl, by simp only [gpr_arithFlags, I.r12], by simp only [gpr_arithFlags, I.rbx],
      by simp only [gpr_arithFlags, I.rbp]⟩
  · simp only [zf_arithFlags, I.rbp]
    rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]

/-- `absorb`, in two runs with the same public arguments. -/
theorem absorb_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {Q : Addr} {nb : Nat} {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → VG.Proof.AesGcmSiv.X86_64.AbsIn K W SP R N A D al n Q nb t₁ ∧ VG.Proof.AesGcmSiv.X86_64.AbsIn K W SP R N A D al n Q nb t₂) :
    RelCT isa P (absorb v.callees) fun _ _ => True := by
  have r₁ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [.r12, .rbp] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.one, (hP _ _ h).2.one, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [(hP _ _ h).1.r12, (hP _ _ h).2.r12]
      · rw [(hP _ _ h).1.rbp, (hP _ _ h).2.rbp]⟩) VG.Proof.AesGcmSiv.X86_64.absHead_check).wp
    (F₁ := fun (t₁ : State) => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₁ ∧ t₁.zf = some (decide (nb / 16 = 0)))
    (F₂ := fun (t₁ : State) => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₁ ∧ t₁.zf = some (decide (nb / 16 = 0)))
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.absHead_wp (hP _ _ h).1, VG.Proof.AesGcmSiv.X86_64.absHead_wp (hP _ _ h).2⟩
  have r₂ : RelCT isa (fun t₁ t₂ => True ∧ (VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₁ ∧
        t₁.zf = some (decide (nb / 16 = 0))) ∧ (VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₂ ∧
        t₂.zf = some (decide (nb / 16 = 0))))
      (.ite .e (.block []) (.loop (absorbChunk v.callees) .ne))
      fun t₁ t₂ => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₁ ∧
        VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₂ := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [VG.Proof.AesGcmSiv.X86_64.eval_e h.2.1.2, VG.Proof.AesGcmSiv.X86_64.eval_e h.2.2.2]) ?_ ?_
    · refine RelCT.block_nil fun t₁ t₂ h => ?_
      have h0 : nb / 16 = 0 := by have := h.2; rw [VG.Proof.AesGcmSiv.X86_64.eval_e h.1.2.1.2] at this; simpa using this
      have a := h.1.2.1.1
      have b := h.1.2.2.1
      rw [h0] at a b ⊢
      exact ⟨a, b⟩
    · by_cases h0 : nb / 16 = 0
      · refine RelCT.of_false fun t₁ t₂ h => ?_
        have := h.2
        rw [VG.Proof.AesGcmSiv.X86_64.eval_e h.1.2.1.2] at this
        simp [h0] at this
      · exact (VG.Proof.AesGcmSiv.X86_64.chunks_rel v L hDW hn (b := nb / 16) (by omega)).mono (fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩)
          fun _ _ h => h
  have r₃ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ =>
      VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2)
      VG.Proof.AesGcmSiv.X86_64.test_check).wp
    (F₁ := fun (t : State) => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t ∧
      t.zf = some (decide (nb % 16 = 0)))
    (F₂ := fun (t : State) => VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t ∧
      t.zf = some (decide (nb % 16 = 0)))
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.absTest_wp (by omega) h.1, VG.Proof.AesGcmSiv.X86_64.absTest_wp (by omega) h.2⟩
  have r₄ : RelCT isa (fun t₁ t₂ => True ∧ (VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₁ ∧
        t₁.zf = some (decide (nb % 16 = 0))) ∧ (VG.Proof.AesGcmSiv.X86_64.AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₂ ∧
        t₂.zf = some (decide (nb % 16 = 0))))
      (.ite .e (.block []) (absorbTail v.callees)) fun _ _ => True := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [VG.Proof.AesGcmSiv.X86_64.eval_e h.2.1.2, VG.Proof.AesGcmSiv.X86_64.eval_e h.2.2.2]) (RelCT.block_nil fun _ _ _ => trivial) ?_
    by_cases h0 : nb % 16 = 0
    · refine RelCT.of_false fun t₁ t₂ h => ?_
      have := h.2
      rw [VG.Proof.AesGcmSiv.X86_64.eval_e h.1.2.1.2] at this
      simp [h0] at this
    · exact (VG.Proof.AesGcmSiv.X86_64.absTail_rel v L hDW hn (by omega) (by omega)).mono (fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩)
        fun _ _ _ => trivial
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ r₄))

/-! ## The lengths, and `polyval` -/

theorem lensArgs_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT []) (.block (([.mov .rax (.mem (at_ .r15 lenO)),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax,
    .store (at_ .r15 bO) .rax, .mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 (bO + 8)) .rax] :
      List Instr) ++ ghArgs ++ ptr .rdx .r15 bO ++ ([.mov32 .rcx (imm 1)] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `lens`, in two runs with the same public arguments. -/
theorem lens_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t₁ ∧ VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t₂) :
    RelCT isa P (lens v.callees) fun _ _ => True := by
  have pre : ∀ {t : State}, VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t → WP isa (.block (([.mov .rax (.mem (at_ .r15 lenO)),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax,
      .store (at_ .r15 bO) .rax, .mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 (bO + 8)) .rax] :
        List Instr) ++ ghArgs ++ ptr .rdx .r15 bO ++ ([.mov32 .rcx (imm 1)] : List Instr))) t fun t₁ =>
      GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 128)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₁.gpr .rsp = SP := fun O => by
    obtain ⟨t₁, run₁, -, rdi₁, rsi₁, r8₁, rdx₁, rcx₁, hg₁, hrd₁, hwr₁⟩ := VG.Proof.AesGcmSiv.X86_64.lensArgs_ok O.env O.sl.alen O.sl.len hal hn'
    have E₁ : VG.Proof.AesGcmSiv.X86_64.Env K W SP t₁ := O.env.of_saved hg₁ hrd₁ hwr₁
    exact WP.of_runBlock ⟨t₁, run₁, VG.Proof.AesGcmSiv.X86_64.gargs L E₁ (d := 128) (n := 1) (by decide) (by decide) rdi₁ rsi₁ rdx₁ rcx₁ r8₁,
      E₁.rsp⟩
  refine RelCT.seq ((VG.Proof.AesGcmSiv.X86_64.rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1, (hP _ _ h).2, fun _ h => nomatch h⟩)
    VG.Proof.AesGcmSiv.X86_64.lensArgs_check).wp
    (F₁ := fun (t₁ : State) => GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 128)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₁.gpr .rsp = SP)
    (F₂ := fun (t₁ : State) => GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 128)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₁.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨pre (hP _ _ h).1, pre (hP _ _ h).2⟩) ?_
  exact gh_rel v.gh fun t₁ t₂ h => ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩

theorem tagIn_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT []) (.block VG.Impl.AesGcmSiv.X86_64.tagIn) hc).isSome = true := ⟨_, by taint_decide⟩

theorem polyA_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [])
    (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem polyD_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [])
    (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A run with the public arguments and the buffers of the additional data
and the data. -/
structure Bufs (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (t : State) : Prop where
  one : VG.Proof.AesGcmSiv.X86_64.One K W SP R N A D al n t
  aad : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t A al
  data : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t D n

theorem Bufs.of_eq {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t t' : State}
    (h : VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t) (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t') (hf : Frame (VG.Proof.AesGcmSiv.X86_64.absR W SP) t.mem t'.mem) (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) : VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t' :=
  ⟨⟨E, Slots.absR L h.one.sl hf, hwr.trans h.one.wr⟩, h.aad.of_eq hrd hwr, h.data.of_eq hrd hwr⟩

theorem polyBlk_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (h : VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t) {o₁ o₂ : Nat} {Q : Addr} {nb : Nat} (hQ : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t Q nb)
    (h₁ : t.mem.readW (W + BitVec.ofNat 64 o₁) 64 = Q) (h₂ : t.mem.readW (W + BitVec.ofNat 64 o₂) 64 = BitVec.ofNat 64 nb)
    (ho₁ : o₁ + 8 ≤ 3816) (ho₂ : o₂ + 8 ≤ 3816) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 o₁)), .mov .rbp (.mem (at_ .r15 o₂))]) t
      fun t' => VG.Proof.AesGcmSiv.X86_64.AbsIn K W SP R N A D al n Q nb t' ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t' := by
  have h15 := h.one.env.r15
  have r₁ := h.one.env.perm.wR ho₁
  have r₂ := h.one.env.perm.wR ho₂
  refine WP.of_runBlock ⟨_, by srun [h15, r₁, r₂], ?_⟩
  have E' : VG.Proof.AesGcmSiv.X86_64.Env K W SP ((t.setReg .r12 (t.mem.readW (W + BitVec.ofNat 64 o₁) 64)).setReg .rbp
      (t.mem.readW (W + BitVec.ofNat 64 o₂) 64)) :=
    h.one.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]) rfl rfl
  exact ⟨⟨⟨E', h.one.sl, h.one.wr⟩, hQ.of_eq rfl rfl, by simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h₁],
    by simp only [gpr_setReg, ite_true, h₂]⟩, ⟨E', h.one.sl, h.one.wr⟩, h.aad.of_eq rfl rfl, h.data.of_eq rfl rfl⟩

theorem absorb_bufs (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    {Q : Addr} {nb : Nat} {t : State} (h : VG.Proof.AesGcmSiv.X86_64.AbsIn K W SP R N A D al n Q nb t ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t) :
    WP isa (absorb v.callees) t (VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n) :=
  WP.mono (VG.Proof.AesGcmSiv.X86_64.absorb_ok v L h.1.one.env h.1.buf h.1.r12 h.1.rbp) fun _ P => h.2.of_eq P.env P.frame L P.rd P.wr

/-- `polyval`, in two runs with the same public arguments. -/
theorem polyval_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t₁ ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t₂) :
    RelCT isa P (polyval v.callees) fun _ _ => True := by
  have r₁ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.one, (hP _ _ h).2.one, fun _ h => nomatch h⟩)
    VG.Proof.AesGcmSiv.X86_64.polyA_check).wp
    (F₁ := fun (t : State) => VG.Proof.AesGcmSiv.X86_64.AbsIn K W SP R N A D al n A al t ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t)
    (F₂ := fun (t : State) => VG.Proof.AesGcmSiv.X86_64.AbsIn K W SP R N A D al n A al t ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.polyBlk_wp (o₁ := aadO) (o₂ := alenO) (hP _ _ h).1 (hP _ _ h).1.aad (hP _ _ h).1.one.sl.aad
        (hP _ _ h).1.one.sl.alen (by decide) (by decide),
      VG.Proof.AesGcmSiv.X86_64.polyBlk_wp (o₁ := aadO) (o₂ := alenO) (hP _ _ h).2 (hP _ _ h).2.aad (hP _ _ h).2.one.sl.aad
        (hP _ _ h).2.one.sl.alen (by decide) (by decide)⟩
  have r₂ := (VG.Proof.AesGcmSiv.X86_64.absorb_rel v L hDW hn (Q := A) (nb := al) (P := fun t₁ t₂ => True ∧
      (VG.Proof.AesGcmSiv.X86_64.AbsIn K W SP R N A D al n A al t₁ ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t₁) ∧
      (VG.Proof.AesGcmSiv.X86_64.AbsIn K W SP R N A D al n A al t₂ ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t₂))
    fun t₁ t₂ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n) (F₂ := VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.absorb_bufs v L h.2.1, VG.Proof.AesGcmSiv.X86_64.absorb_bufs v L h.2.2⟩
  have r₃ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [] (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t₁ ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) VG.Proof.AesGcmSiv.X86_64.polyD_check).wp
    (F₁ := fun (t : State) => VG.Proof.AesGcmSiv.X86_64.AbsIn K W SP R N A D al n D n t ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t)
    (F₂ := fun (t : State) => VG.Proof.AesGcmSiv.X86_64.AbsIn K W SP R N A D al n D n t ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.polyBlk_wp (o₁ := dataO) (o₂ := lenO) h.2.1 h.2.1.data h.2.1.one.sl.data h.2.1.one.sl.len
        (by decide) (by decide),
      VG.Proof.AesGcmSiv.X86_64.polyBlk_wp (o₁ := dataO) (o₂ := lenO) h.2.2 h.2.2.data h.2.2.one.sl.data h.2.2.one.sl.len (by decide)
        (by decide)⟩
  have r₄ := (VG.Proof.AesGcmSiv.X86_64.absorb_rel v L hDW hn (Q := D) (nb := n) (P := fun t₁ t₂ => True ∧
      (VG.Proof.AesGcmSiv.X86_64.AbsIn K W SP R N A D al n D n t₁ ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t₁) ∧
      (VG.Proof.AesGcmSiv.X86_64.AbsIn K W SP R N A D al n D n t₂ ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t₂))
    fun t₁ t₂ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n) (F₂ := VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.absorb_bufs v L h.2.1, VG.Proof.AesGcmSiv.X86_64.absorb_bufs v L h.2.2⟩
  have lens_bufs : ∀ {t : State}, VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t → WP isa (lens v.callees) t (VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n) :=
    fun h => WP.mono (VG.Proof.AesGcmSiv.X86_64.lens_ok v L h.one.env h.one.sl.alen h.one.sl.len hal hn') fun _ P =>
      h.of_eq P.env P.frame L P.rd P.wr
  have r₅ := (VG.Proof.AesGcmSiv.X86_64.lens_rel v L hDW hn hal hn' (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t₂) fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n) (F₂ := VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨lens_bufs h.2.1, lens_bufs h.2.2⟩
  have r₆ := VG.Proof.AesGcmSiv.X86_64.rel_taintC [] (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t₁ ∧ VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) VG.Proof.AesGcmSiv.X86_64.tagIn_check
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (RelCT.seq r₅ r₆))))

end VG.Proof.AesGcmSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86_64.FnCT`. -/
section

/-!
# AES-GCM-SIV on x86-64: `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` are constant time

Untrusted: everything here is checked by Lean. The entry, which loads `W`
from the stack first, passes the taint analysis from the public arguments
(`entry_rel`); between the pieces each run has the public arguments, its
buffers and the tag's address on the stack (`St`), which every piece keeps
(by correctness), and the pieces are related from it (`keys_rel`,
`polyval_rel`, `tag_rel`, `crypt_rel`, and the taint analysis for the
comparison, the mask and the restore). The copies of the tag load its
address from the stack first, the same in both runs, and the taint analysis
checks the rest (`rel_loadT`).

The taint analysis knows `W` as the second writable region, as it is for
`open`; `seal` may write `tag` too, before `W`, but its pieces before the copy
of the tag do not, and run the same from its states with `tag` only readable
(`rel_narrow`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl in_off)

/-- The address of the tag `T`, at `SP + 16`, where the run may read it,
apart from what the pieces write, and the tag, which it may read. -/
structure ArgT (W SP D : Addr) (n : Nat) (T : Addr) (s : State) : Prop where
  val : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T
  rd : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8
  w : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨W, 3816⟩
  d : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨D, n⟩
  tb : VG.Proof.AesGcmSiv.X86_64.TagBuf W SP D n T
  trd : Covers [⟨T, 16⟩] (s.rd ++ s.wr)

theorem ArgT.mut {W SP D T : Addr} {n : Nat} {s s' : State} (h : VG.Proof.AesGcmSiv.X86_64.ArgT W SP D n T s)
    (hf : Frame (VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcmSiv.X86_64.ArgT W SP D n T s' :=
  ⟨by rw [VG.Proof.AesGcmSiv.X86_64.argT_kept (hf.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩) h.w h.d, h.val],
    by rw [hrd, hwr]; exact h.rd, h.w, h.d, h.tb, by rw [hrd, hwr]; exact h.trd⟩

/-- A run between the pieces: the public arguments, the buffers and the
tag's address. -/
structure St (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (t : State) : Prop where
  bufs : VG.Proof.AesGcmSiv.X86_64.Bufs K W SP R N A D al n t
  nonce : VG.Proof.AesGcmSiv.X86_64.Buf K W SP t N 12
  argT : VG.Proof.AesGcmSiv.X86_64.ArgT W SP D n T t

theorem St.frame {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {t t' : State}
    (h : VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t) (E : VG.Proof.AesGcmSiv.X86_64.Env K W SP t') {rs : List Region} (hf : Frame rs t.mem t'.mem)
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint r) (hm : Frame (VG.Proof.AesGcmSiv.X86_64.mutR W SP D n) t.mem t'.mem)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t' :=
  ⟨⟨⟨E, h.bufs.one.sl.of_frame hf hd, hwr.trans h.bufs.one.wr⟩, h.bufs.aad.of_eq hrd hwr, h.bufs.data.of_eq hrd hwr⟩,
    h.nonce.of_eq hrd hwr, h.argT.mut hm hrd hwr⟩

/-- `St`, and the keys' results that POLYVAL needs. -/
def StK (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (t : State) : Prop :=
  VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t ∧
    Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)) ∧
    Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0

theorem keys_st (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} {t : State} (h : VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t) : WP isa (VG.Impl.AesGcmSiv.X86_64.keys v.callees) t (VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T) :=
  WP.mono (VG.Proof.AesGcmSiv.X86_64.keys_ok v L hR h.bufs.one.env h.bufs.one.sl h.nonce h.bufs.data.w) fun _ Ky =>
    ⟨h.frame Ky.env Ky.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) ((Ky.frame.sub (VG.Proof.AesGcmSiv.X86_64.keyR_mutW W SP)).sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n)) Ky.rd Ky.wr,
      Ky.hkey, Ky.acc⟩

theorem polyval_st (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T t) : WP isa (polyval v.callees) t (VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) :=
  WP.mono (VG.Proof.AesGcmSiv.X86_64.polyval_ok v L h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.aad h.1.bufs.data h.1.nonce h.2.1 h.2.2)
    fun _ Po => h.1.frame Po.env Po.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) ((Po.frame.sub (VG.Proof.AesGcmSiv.X86_64.polyR_mutW W SP)).sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n)) Po.rd Po.wr

theorem tag_st (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} {o : Nat} (ho : o = 0 ∨ o = 128) {t : State} (h : VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t) :
    WP isa (tag v.callees o) t (VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) :=
  WP.mono (VG.Proof.AesGcmSiv.X86_64.tag_ok v L hR h.bufs.one.env h.bufs.one.sl ho) fun _ Tg => h.frame Tg.env Tg.frame (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by omega)) (by decide) (by omega)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) ((Tg.frame.sub (VG.Proof.AesGcmSiv.X86_64.tagR_mutW W SP (by omega))).sub (VG.Proof.AesGcmSiv.X86_64.mutW_mut W SP D n))
    Tg.rd Tg.wr

theorem crypt_st0 (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} {t : State} (h : VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t) : WP isa (crypt v.callees) t (VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) :=
  WP.mono (VG.Proof.AesGcmSiv.X86_64.crypt_ok v L hR h.bufs.one.env h.bufs.one.sl h.bufs.data
    (by rw [h.bufs.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp))) fun _ Cr =>
    h.frame Cr.env Cr.frame (VG.Proof.AesGcmSiv.X86_64.slots_cryR L h.bufs.data) (Cr.frame.sub (VG.Proof.AesGcmSiv.X86_64.cryR_mut W SP D n)) Cr.rd Cr.wr

theorem crypt_st (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} {t : State} (h : VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T t) : WP isa (crypt v.callees) t (VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T) := by
  refine WP.mono (VG.Proof.AesGcmSiv.X86_64.crypt_ok v L hR h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.data
    (by rw [h.1.bufs.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp))) fun _ Cr => ?_
  have dK : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 96 → ∀ q ∈ VG.Proof.AesGcmSiv.X86_64.cryR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm
      · exact (h.1.bufs.data.w.sub_right (Lay.wSub (by omega))).symm
  refine ⟨h.1.frame Cr.env Cr.frame (VG.Proof.AesGcmSiv.X86_64.slots_cryR L h.1.bufs.data) (Cr.frame.sub (VG.Proof.AesGcmSiv.X86_64.cryR_mut W SP D n)) Cr.rd Cr.wr,
    ?_, ?_⟩
  · rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), h.2.1,
      Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (dK (by decide) (by decide)) (by decide)]
  · rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), h.2.2]

/-! ## The entry -/

theorem loadW_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp 24))]) s fun s' =>
      s'.gpr .rax = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by srun [hr], ?_, ?_⟩
  · simp only [gpr_setReg, ite_true]
  · intro r a; simp only [gpr_setReg, a, ite_false]

theorem entryW_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp 24))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem entryRest_check :
    ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (.block entry.tail) hc).isSome =
      true := ⟨_, by taint_decide⟩

/-- Code the taint analysis checks from the registers `rs`, public. -/
theorem rel_taintR {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s₁ s₂ h => Taint.agree_ofRegs (hag _ _ h)) hc

/-- The entry, in two runs with the same arguments in registers and the same
`W`. -/
theorem entry_rel {s₀ s₀' : State} {F₁ F₂ : State → Prop}
    (hag : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r)
    (hw : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64)
    (hr₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 24) 8)
    (hr₂ : InRegions (s₀'.rd ++ s₀'.wr) (s₀'.gpr .rsp + BitVec.ofNat 64 24) 8)
    (hE₁ : WP isa (.block entry) s₀ F₁) (hE₂ : WP isa (.block entry) s₀' F₂) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ => True ∧ F₁ s₁ ∧ F₂ s₂ := by
  have l := (VG.Proof.AesGcmSiv.X86_64.rel_taintR (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') [.rsp] (fun _ _ h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact hag _ (by simp))
      VG.Proof.AesGcmSiv.X86_64.entryW_check).wp
    (F₁ := fun (s' : State) => s'.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r)
    (F₂ := fun (s' : State) => s'.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀'.gpr r)
    fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.AesGcmSiv.X86_64.loadW_ok hr₁, VG.Proof.AesGcmSiv.X86_64.loadW_ok hr₂⟩
  have e : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun _ _ => True :=
    RelCT.block_append (M := isa) (l₁ := [.mov .rax (.mem (at_ .rsp 24))]) (l₂ := entry.tail) (RelCT.seq l
      (VG.Proof.AesGcmSiv.X86_64.rel_taintR (P := fun (s₁ s₂ : State) => True ∧
          (s₁.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧
          (s₂.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .rax → s₂.gpr r = s₀'.gpr r))
        (.rax :: [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (fun _ _ h r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [h.2.1.1, h.2.2.1, hw]
        · have hx : r ≠ .rax := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          rw [h.2.1.2 r hx, h.2.2.2 r hx, hag r hr]) VG.Proof.AesGcmSiv.X86_64.entryRest_check))
  exact e.wp fun _ _ h => by rw [h.1, h.2]; exact ⟨hE₁, hE₂⟩

/-- What the entry leaves, for the arguments: the environment, the slots, the
same permissions, and the address of the tag still at `SP + 16`. -/
theorem entry_post {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : VG.Proof.AesGcmSiv.X86_64.Args s K W SP N A D R al n) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (.block entry) s fun s₁ => VG.Proof.AesGcmSiv.X86_64.Env K W SP s₁ ∧ VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n s₁.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ s₁.mem.readW (SP + BitVec.ofNat 64 16) 64 = T ∧
      InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 16) 8 := by
  obtain ⟨s₁, run₁, E₁, S₁, _, f₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.X86_64.entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  have hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8 := by
    have h := in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc] at h
    exact h
  refine WP.of_runBlock ⟨s₁, run₁, E₁, S₁, rd₁, wr₁, ?_, by rw [rd₁, wr₁]; exact hTr⟩
  rw [f₁.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.AesGcmSiv.X86_64.argT_disj (n := n) Ar.argsW Ar.argsD _ List.mem_cons_self) (by decide), hT]

theorem argW_in {s : State} {K W SP N A D : Addr} {R al n : Nat} (Ar : VG.Proof.AesGcmSiv.X86_64.Args s K W SP N A D R al n)
    (hsp : s.gpr .rsp = SP) : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8 := by
  have h := in_off (d := 16) (n := 8) Ar.args (by decide) (by decide)
  rw [VG.Proof.AesGcmSiv.X86_64.add_ofNat_assoc] at h
  rw [hsp]; exact h

theorem pub_regs {s₀ s₀' : State} (hq : VG.Proof.AesGcmSiv.onePub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q1, q2, q3, q4, q5, q6, q7]

/-! ## The tag's address -/

/-- What the copies of the tag need of a run: `r15` and `rsp` hold `W` and
`SP`, and the address of the tag `T` is at `SP + 16`, where the run may read
it. -/
def TagIn (W SP T : Addr) (s : State) : Prop :=
  s.gpr .r15 = W ∧ s.gpr .rsp = SP ∧ s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T ∧
    InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8

theorem St.tagIn {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {σ s : State}
    (h : VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T σ) (hg : σ.gpr = s.gpr) (hm : σ.mem = s.mem)
    (hc : Covers (σ.rd ++ σ.wr) (s.rd ++ s.wr)) : VG.Proof.AesGcmSiv.X86_64.TagIn W SP T s :=
  ⟨by rw [← hg]; exact h.bufs.one.env.r15, by rw [← hg]; exact h.bufs.one.env.rsp, by rw [← hm]; exact h.argT.val,
    hc _ _ h.argT.rd⟩

/-- `mov rcx, [rsp + 16]`: the tag's address in `rcx`. -/
theorem loadT_ok {W SP T : Addr} {s : State} (h : VG.Proof.AesGcmSiv.X86_64.TagIn W SP T s) :
    WP isa (.block [.mov .rcx (.mem (at_ .rsp 16))]) s fun s' =>
      s'.gpr .rcx = T ∧ s'.gpr .r15 = W ∧ ∀ r, r ≠ .rcx → s'.gpr r = s.gpr r := by
  obtain ⟨h15, hsp, hT, hr⟩ := h
  refine WP.of_runBlock ⟨_, by srun [hsp, hr], ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, hT]
  · simp only [gpr_setReg, ite_false, reduceCtorEq, h15]
  · intro r a; simp only [gpr_setReg, a, ite_false]

theorem loadT_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rcx (.mem (at_ .rsp 16))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

/-- `mov rcx, [rsp + 16]` and then `c`, which the taint analysis checks with
`rcx` and `r15` public, in two runs with the same `W`, `SP` and tag
address. -/
theorem rel_loadT {W SP T : Addr} {P : State → State → Prop} {l : List Instr}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesGcmSiv.X86_64.TagIn W SP T s₁ ∧ VG.Proof.AesGcmSiv.X86_64.TagIn W SP T s₂)
    (hc : ∃ hc, (taint.check (Taint.ofRegs [.rcx, .r15]) (.block l) hc).isSome = true) :
    RelCT isa P (.block (([.mov .rcx (.mem (at_ .rsp 16))] : List Instr) ++ l)) fun _ _ => True := by
  have a := (VG.Proof.AesGcmSiv.X86_64.rel_taintR (P := P) [.rsp] (fun s₁ s₂ h r hr => by
      obtain ⟨⟨-, a₁, -⟩, ⟨-, a₂, -⟩⟩ := hP _ _ h
      simp only [List.mem_singleton] at hr; subst hr; rw [a₁, a₂]) VG.Proof.AesGcmSiv.X86_64.loadT_check).wp
    (F₁ := fun (s : State) => s.gpr .rcx = T ∧ s.gpr .r15 = W ∧ ∀ r, r ≠ .rcx → s.gpr r = s.gpr r)
    (F₂ := fun (s : State) => s.gpr .rcx = T ∧ s.gpr .r15 = W ∧ ∀ r, r ≠ .rcx → s.gpr r = s.gpr r)
    fun _ _ h => ⟨WP.mono (VG.Proof.AesGcmSiv.X86_64.loadT_ok (hP _ _ h).1) fun _ h => ⟨h.1, h.2.1, fun _ _ => rfl⟩,
      WP.mono (VG.Proof.AesGcmSiv.X86_64.loadT_ok (hP _ _ h).2) fun _ h => ⟨h.1, h.2.1, fun _ _ => rfl⟩⟩
  exact RelCT.block_append (M := isa) (RelCT.seq a (VG.Proof.AesGcmSiv.X86_64.rel_taintR [.rcx, .r15] (fun _ _ h r hr => by
    obtain ⟨-, ⟨c₁, w₁, -⟩, ⟨c₂, w₂, -⟩⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [c₁, c₂]
    · rw [w₁, w₂]) hc))

/-! ## `seal` -/

/-- `s` with the tag read only, and the data and `W` its writable regions. -/
abbrev narrowT (D : Addr) (n : Nat) (T W : Addr) (s : State) : State :=
  s.withRegions (s.rd ++ [⟨T, 16⟩]) [⟨D, n⟩, ⟨W, 3816⟩]

theorem covers_narrowT (rd : List Region) (d t w : Region) :
    Covers (rd ++ [d, t, w]) ((rd ++ [t]) ++ [d, w]) :=
  Covers.of_mem fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]

/-- What the entry of `seal` leaves: with the tag read only, a run after the
entry. -/
def SealIn (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (s : State) : Prop :=
  s.wr = [⟨D, n⟩, ⟨T, 16⟩, ⟨W, 3816⟩] ∧ VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T (VG.Proof.AesGcmSiv.X86_64.narrowT D n T W s)

theorem sealIn_of {s s₁ : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : VG.Proof.AesGcmSiv.X86_64.Args s K W SP N A D R al n) (Tb : VG.Proof.AesGcmSiv.X86_64.TagBuf W SP D n T) (hwr : s.wr = [⟨D, n⟩, ⟨T, 16⟩, ⟨W, 3816⟩])
    (h : VG.Proof.AesGcmSiv.X86_64.Env K W SP s₁ ∧ VG.Proof.AesGcmSiv.X86_64.Slots W R N A D al n s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      s₁.mem.readW (SP + BitVec.ofNat 64 16) 64 = T ∧ InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 16) 8) :
    VG.Proof.AesGcmSiv.X86_64.SealIn K W SP R N A D al n T s₁ := by
  obtain ⟨E, S, rd, wr, hT, hTr⟩ := h
  have hwr₁ : s₁.wr = [⟨D, n⟩, ⟨T, 16⟩, ⟨W, 3816⟩] := by rw [wr]; exact hwr
  have hc : Covers (s₁.rd ++ s₁.wr) ((VG.Proof.AesGcmSiv.X86_64.narrowT D n T W s₁).rd ++ (VG.Proof.AesGcmSiv.X86_64.narrowT D n T W s₁).wr) := by
    rw [hwr₁]; exact VG.Proof.AesGcmSiv.X86_64.covers_narrowT _ _ _ _
  have hb : ∀ {P : Addr} {len : Nat}, VG.Proof.AesGcmSiv.X86_64.Buf K W SP s P len → VG.Proof.AesGcmSiv.X86_64.Buf K W SP (VG.Proof.AesGcmSiv.X86_64.narrowT D n T W s₁) P len := fun hP =>
    { hP.of_eq rd wr with rd := (hP.of_eq rd wr).rd.trans hc }
  exact ⟨hwr₁, ⟨⟨⟨E.r13, E.r15, E.rsp, E.perm.k.trans hc, Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp⟩, S, rfl⟩, hb Ar.aad, hb Ar.data⟩, hb Ar.nonce,
    ⟨hT, hc _ _ hTr, Ar.argsW, Ar.argsD, Tb, Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp⟩⟩

theorem entry_seal {s : State} (hp : VG.Proof.AesGcmSiv.sealPre s) :
    WP isa (.block entry) s (VG.Proof.AesGcmSiv.X86_64.SealIn (s.gpr .rdi) (VG.Proof.AesGcmSiv.arg s 2) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .rcx)
      (s.gpr .r9) (s.gpr .r8).toNat (VG.Proof.AesGcmSiv.arg s 0).toNat (VG.Proof.AesGcmSiv.arg s 1)) :=
  WP.mono (VG.Proof.AesGcmSiv.X86_64.entry_post (VG.Proof.AesGcmSiv.X86_64.args_of_seal hp).1.1 rfl (VG.Proof.AesGcmSiv.X86_64.ofNat_toNat64 _).symm rfl rfl rfl
      (VG.Proof.AesGcmSiv.X86_64.ofNat_toNat64 _).symm rfl rfl (VG.Proof.AesGcmSiv.X86_64.ofNat_toNat64 _).symm rfl)
    fun _ h => VG.Proof.AesGcmSiv.X86_64.sealIn_of (VG.Proof.AesGcmSiv.X86_64.args_of_seal hp).1.1 (VG.Proof.AesGcmSiv.X86_64.args_of_seal hp).1.2 hp.2.1 h

/-- The second run, with the first's public arguments. -/
theorem entry_seal_pub {s₀ s₀' : State} (hp' : VG.Proof.AesGcmSiv.sealPre s₀') (hq : VG.Proof.AesGcmSiv.onePub s₀ s₀') :
    WP isa (.block entry) s₀' (VG.Proof.AesGcmSiv.X86_64.SealIn (s₀.gpr .rdi) (VG.Proof.AesGcmSiv.arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx)
      (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (VG.Proof.AesGcmSiv.arg s₀ 0).toNat (VG.Proof.AesGcmSiv.arg s₀ 1)) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), q1, q2, q3, q4, q5, q6, q7]
  exact VG.Proof.AesGcmSiv.X86_64.entry_seal hp'

/-- `seal` after its entry, up to the copy of the tag. -/
abbrev sealFront (v : GcmImpl) : Prog isa :=
  .seq (.seq (.seq (VG.Impl.AesGcmSiv.X86_64.keys v.callees) (polyval v.callees)) (tag v.callees tagO)) (crypt v.callees)

theorem sealFront_st (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D T : Addr} {al n : Nat} {t : State} (h : VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t) :
    WP isa (VG.Proof.AesGcmSiv.X86_64.sealFront v) t (VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) :=
  WP.seq (WP.mono (WP.seq (WP.mono (WP.seq (WP.mono (VG.Proof.AesGcmSiv.X86_64.keys_st v L hR h) fun _ h => VG.Proof.AesGcmSiv.X86_64.polyval_st v L h))
    fun _ h => VG.Proof.AesGcmSiv.X86_64.tag_st v L hR (by decide) h)) fun _ h => VG.Proof.AesGcmSiv.X86_64.crypt_st0 v L hR h)

/-- `sealFront`, in two runs. -/
theorem sealFront_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D T : Addr} {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64)
    (hn' : n < 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₁ ∧ VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₂) :
    RelCT isa P (VG.Proof.AesGcmSiv.X86_64.sealFront v) fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₁ ∧ VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₂ := by
  have r₁ := (VG.Proof.AesGcmSiv.X86_64.keys_rel v L hR hDW hn fun t₁ t₂ h => ⟨⟨(hP _ _ h).1.bufs.one, (hP _ _ h).1.nonce⟩,
      ⟨(hP _ _ h).2.bufs.one, (hP _ _ h).2.nonce⟩⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T) (F₂ := VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.keys_st v L hR (hP _ _ h).1, VG.Proof.AesGcmSiv.X86_64.keys_st v L hR (hP _ _ h).2⟩
  have r₂ := (VG.Proof.AesGcmSiv.X86_64.polyval_rel v L hDW hn hal hn' (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.1.bufs, h.2.2.1.bufs⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) (F₂ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.polyval_st v L h.2.1, VG.Proof.AesGcmSiv.X86_64.polyval_st v L h.2.2⟩
  have r₃ := (VG.Proof.AesGcmSiv.X86_64.tag_rel v L hR hDW hn (o := tagO) (by decide) (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) (F₂ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.tag_st v L hR (by decide) h.2.1, VG.Proof.AesGcmSiv.X86_64.tag_st v L hR (by decide) h.2.2⟩
  have r₄ := (VG.Proof.AesGcmSiv.X86_64.crypt_rel v L hR hDW hn (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨⟨h.2.1.bufs.one, h.2.1.bufs.data⟩, ⟨h.2.2.bufs.one, h.2.2.bufs.data⟩⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) (F₂ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.crypt_st0 v L hR h.2.1, VG.Proof.AesGcmSiv.X86_64.crypt_st0 v L hR h.2.2⟩
  exact (RelCT.seq (RelCT.seq (RelCT.seq r₁ r₂) r₃) r₄).mono (fun _ _ h => h) fun _ _ h => ⟨trivial, h.2⟩

theorem tagOut_check : ∃ hc, (taint.check (Taint.ofRegs [.rcx, .r15]) (.block (tagOut.tail ++ VG.Impl.AesGcmSiv.X86_64.restore)) hc).isSome =
    true := ⟨_, by taint_decide⟩

/-- `vg_aes_gcm_siv_seal`, in two runs with the same public arguments. -/
theorem seal_rel (v : GcmImpl) {s₀ s₀' : State} (hp : VG.Proof.AesGcmSiv.sealPre s₀) (hp' : VG.Proof.AesGcmSiv.sealPre s₀') (hq : VG.Proof.AesGcmSiv.onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callees) fun _ _ => True := by
  have Ar := (VG.Proof.AesGcmSiv.X86_64.args_of_seal hp).1.1
  have L := Ar.lay
  refine RelCT.seq (VG.Proof.AesGcmSiv.X86_64.entry_rel (VG.Proof.AesGcmSiv.X86_64.pub_regs hq) (hq.2.2.2.2.2.2.2 2 (by decide)) (VG.Proof.AesGcmSiv.X86_64.argW_in Ar rfl)
    (VG.Proof.AesGcmSiv.X86_64.argW_in (VG.Proof.AesGcmSiv.X86_64.args_of_seal hp').1.1 rfl) (VG.Proof.AesGcmSiv.X86_64.entry_seal hp) (VG.Proof.AesGcmSiv.X86_64.entry_seal_pub hp' hq)) ?_
  refine RelCT.assoc (RelCT.assoc (RelCT.assoc ?_))
  have hn := Nat.le_of_lt Ar.data.lt
  have front := rel_narrow (c := VG.Proof.AesGcmSiv.X86_64.sealFront v)
    (P := fun s₁ s₂ => True ∧
      VG.Proof.AesGcmSiv.X86_64.SealIn (s₀.gpr .rdi) (VG.Proof.AesGcmSiv.arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9)
        (s₀.gpr .r8).toNat (VG.Proof.AesGcmSiv.arg s₀ 0).toNat (VG.Proof.AesGcmSiv.arg s₀ 1) s₁ ∧
      VG.Proof.AesGcmSiv.X86_64.SealIn (s₀.gpr .rdi) (VG.Proof.AesGcmSiv.arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9)
        (s₀.gpr .r8).toNat (VG.Proof.AesGcmSiv.arg s₀ 0).toNat (VG.Proof.AesGcmSiv.arg s₀ 1) s₂)
    [⟨VG.Proof.AesGcmSiv.arg s₀ 1, 16⟩] [⟨s₀.gpr .r9, (VG.Proof.AesGcmSiv.arg s₀ 0).toNat⟩, ⟨VG.Proof.AesGcmSiv.arg s₀ 2, 3816⟩]
    (VG.Proof.AesGcmSiv.X86_64.sealFront_rel v L Ar.rounds Ar.data.w hn Ar.aad.lt Ar.data.lt
      fun _ _ h => by obtain ⟨_, _, hp, rfl, rfl⟩ := h; exact ⟨hp.2.1.2, hp.2.2.2⟩)
    fun s₁ s₂ h => by
      have hc : ∀ {s : State}, s.wr = [⟨s₀.gpr .r9, (VG.Proof.AesGcmSiv.arg s₀ 0).toNat⟩, ⟨VG.Proof.AesGcmSiv.arg s₀ 1, 16⟩, ⟨VG.Proof.AesGcmSiv.arg s₀ 2, 3816⟩] →
          Covers ([⟨VG.Proof.AesGcmSiv.arg s₀ 1, 16⟩] ++ [⟨s₀.gpr .r9, (VG.Proof.AesGcmSiv.arg s₀ 0).toNat⟩, ⟨VG.Proof.AesGcmSiv.arg s₀ 2, 3816⟩]) s.wr ∧
          Covers [⟨s₀.gpr .r9, (VG.Proof.AesGcmSiv.arg s₀ 0).toNat⟩, ⟨VG.Proof.AesGcmSiv.arg s₀ 2, 3816⟩] s.wr := fun hw => by
        rw [hw]
        refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩ <;>
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢ <;>
          rcases hr with h | h | h <;> simp [h]
      obtain ⟨_, ⟨hw₁, p₁⟩, ⟨hw₂, p₂⟩⟩ := h
      obtain ⟨t₁, u₁, e₁, -⟩ := VG.Proof.AesGcmSiv.X86_64.sealFront_st v L Ar.rounds p₁
      obtain ⟨t₂, u₂, e₂, -⟩ := VG.Proof.AesGcmSiv.X86_64.sealFront_st v L Ar.rounds p₂
      exact ⟨⟨(hc hw₁).1, (hc hw₁).2, t₁, u₁, e₁⟩, ⟨(hc hw₂).1, (hc hw₂).2, t₂, u₂, e₂⟩⟩
  exact RelCT.seq front (VG.Proof.AesGcmSiv.X86_64.rel_loadT (l := tagOut.tail ++ VG.Impl.AesGcmSiv.X86_64.restore) (fun _ _ h => by
    obtain ⟨_, _, ⟨-, m₁, m₂⟩, ⟨g₁, h₁, c₁⟩, ⟨g₂, h₂, c₂⟩⟩ := h
    exact ⟨m₁.tagIn g₁ h₁ c₁, m₂.tagIn g₂ h₂ c₂⟩) VG.Proof.AesGcmSiv.X86_64.tagOut_check)

/-! ## `open` -/

theorem entry_st {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : VG.Proof.AesGcmSiv.X86_64.Args s K W SP N A D R al n) (Tb : VG.Proof.AesGcmSiv.X86_64.TagBuf W SP D n T) (hTr : Covers [⟨T, 16⟩] (s.rd ++ s.wr))
    (hwr : s.wr = [⟨D, n⟩, ⟨W, 3816⟩]) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (.block entry) s (VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) :=
  WP.mono (VG.Proof.AesGcmSiv.X86_64.entry_post Ar hsp hn hT hW hdi hsi hdx hcx hr8 hr9) fun _ ⟨E₁, S₁, rd₁, wr₁, hT₁, hTa₁⟩ =>
    ⟨⟨⟨E₁, S₁, wr₁.trans hwr⟩, Ar.aad.of_eq rd₁ wr₁, Ar.data.of_eq rd₁ wr₁⟩, Ar.nonce.of_eq rd₁ wr₁,
      ⟨hT₁, hTa₁, Ar.argsW, Ar.argsD, Tb, by rw [rd₁, wr₁]; exact hTr⟩⟩

theorem entry_open {s : State} (hp : VG.Proof.AesGcmSiv.openPre s) :
    WP isa (.block entry) s (VG.Proof.AesGcmSiv.X86_64.St (s.gpr .rdi) (VG.Proof.AesGcmSiv.arg s 2) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .rcx)
      (s.gpr .r9) (s.gpr .r8).toNat (VG.Proof.AesGcmSiv.arg s 0).toNat (VG.Proof.AesGcmSiv.arg s 1)) :=
  VG.Proof.AesGcmSiv.X86_64.entry_st (VG.Proof.AesGcmSiv.X86_64.args_of_open hp).1.1 (VG.Proof.AesGcmSiv.X86_64.args_of_open hp).1.2 (VG.Proof.AesGcmSiv.X86_64.args_of_open hp).2 hp.2.1 rfl (VG.Proof.AesGcmSiv.X86_64.ofNat_toNat64 _).symm rfl rfl
    rfl (VG.Proof.AesGcmSiv.X86_64.ofNat_toNat64 _).symm rfl rfl (VG.Proof.AesGcmSiv.X86_64.ofNat_toNat64 _).symm rfl

/-- The second run, with the first's public arguments. -/
theorem entry_open_pub {s₀ s₀' : State} (hp' : VG.Proof.AesGcmSiv.openPre s₀') (hq : VG.Proof.AesGcmSiv.onePub s₀ s₀') :
    WP isa (.block entry) s₀' (VG.Proof.AesGcmSiv.X86_64.St (s₀.gpr .rdi) (VG.Proof.AesGcmSiv.arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx)
      (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (VG.Proof.AesGcmSiv.arg s₀ 0).toNat (VG.Proof.AesGcmSiv.arg s₀ 1)) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), q1, q2, q3, q4, q5, q6, q7]
  exact VG.Proof.AesGcmSiv.X86_64.entry_open hp'

theorem recv_st {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t) : WP isa (.block recv) t (VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) := by
  obtain ⟨t', run', fR, -, hg', hrd', hwr'⟩ := VG.Proof.AesGcmSiv.X86_64.recv_ok h.bufs.one.env h.argT.val h.argT.rd
    (h.argT.tb.buf h.argT.trd)
  refine WP.of_runBlock ⟨t', run', h.frame (h.bufs.one.env.of_saved hg' hrd' hwr') fR (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    simpa using L.w_w (a := 200) (n := 48) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide))
    (fR.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨VG.Proof.AesGcmSiv.X86_64.wA W, by simp, Region.sub_prefix (by decide)⟩)
    hrd' hwr'⟩

theorem recv_split : recv = ([.mov .rcx (.mem (at_ .rsp 16))] : List Instr) ++ recv.tail := rfl

theorem recv_check : ∃ hc, (taint.check (Taint.ofRegs [.rcx, .r15]) (.block recv.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT []) (.block Impl.AesGcmSiv.X86_64.cmp) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mask_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT []) mask hc).isSome = true := ⟨_, by taint_decide⟩

theorem fin_check : ∃ hc, (taint.check (VG.Proof.AesGcmSiv.X86_64.sivT [])
    (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ VG.Impl.AesGcmSiv.X86_64.restore)) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `St`, with `ok` at `W + 192` either 1 or 0. -/
def StO (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (t : State) : Prop :=
  VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t ∧
    (t.mem.readW (W + BitVec.ofNat 64 192) 64 = 1#64 ∨ t.mem.readW (W + BitVec.ofNat 64 192) 64 = 0#64)

theorem cmp_st {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t) : WP isa (.block Impl.AesGcmSiv.X86_64.cmp) t (VG.Proof.AesGcmSiv.X86_64.StO K W SP R N A D al n T) := by
  obtain ⟨t', run', hm', hg', hrd', hwr'⟩ := VG.Proof.AesGcmSiv.X86_64.cmp_ok h.bufs.one.env
  have fO : Frame [VG.Proof.AesGcmSiv.X86_64.wO W] t.mem t'.mem := by
    rw [hm']; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨t', run', h.frame (h.bufs.one.env.of_saved hg' hrd' hwr') fO (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
    (fO.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩) hrd' hwr', ?_⟩
  rw [hm', Mem.readW_writeW_self64]
  split
  · exact .inl rfl
  · exact .inr rfl

theorem mask_st {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : VG.Proof.AesGcmSiv.X86_64.StO K W SP R N A D al n T t) : WP isa mask t (VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) := by
  have hok : t.mem.readW (W + BitVec.ofNat 64 192) 64 =
      if t.mem.readW (W + BitVec.ofNat 64 192) 64 = 1#64 then 1#64 else 0#64 := by
    rcases h.2 with h' | h' <;> rw [h'] <;> decide
  refine WP.mono (VG.Proof.AesGcmSiv.X86_64.mask_ok h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.data
    (by rw [h.1.bufs.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp)) hok) fun _ Mk =>
    h.1.frame Mk.env Mk.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact (h.1.bufs.data.w.sub_right (Lay.wSub (by decide))).symm)
      (Mk.frame.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩)
      Mk.rd Mk.wr

/-- `open` after its entry, in two runs. -/
theorem openBody_rel (v : GcmImpl) {K W SP : Addr} (L : VG.Proof.AesGcmSiv.X86_64.Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₁ ∧ VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₂) :
    RelCT isa P (.seq (.block recv) (.seq (VG.Impl.AesGcmSiv.X86_64.keys v.callees) (.seq (crypt v.callees) (.seq (polyval v.callees)
      (.seq (tag v.callees bO) (.seq (.block Impl.AesGcmSiv.X86_64.cmp) (.seq mask
        (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ VG.Impl.AesGcmSiv.X86_64.restore)))))))))
      fun _ _ => True := by
  have r₀ := (VG.Proof.AesGcmSiv.X86_64.rel_loadT (l := recv.tail) (fun t₁ t₂ h =>
      ⟨(hP _ _ h).1.tagIn rfl rfl (Covers.refl _), (hP _ _ h).2.tagIn rfl rfl (Covers.refl _)⟩) VG.Proof.AesGcmSiv.X86_64.recv_check).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) (F₂ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨by rw [← VG.Proof.AesGcmSiv.X86_64.recv_split]; exact VG.Proof.AesGcmSiv.X86_64.recv_st L (hP _ _ h).1, by rw [← VG.Proof.AesGcmSiv.X86_64.recv_split]; exact VG.Proof.AesGcmSiv.X86_64.recv_st L (hP _ _ h).2⟩
  have r₁ := (VG.Proof.AesGcmSiv.X86_64.keys_rel v L hR hDW hn (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨⟨h.2.1.bufs.one, h.2.1.nonce⟩, ⟨h.2.2.bufs.one, h.2.2.nonce⟩⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T) (F₂ := VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.keys_st v L hR h.2.1, VG.Proof.AesGcmSiv.X86_64.keys_st v L hR h.2.2⟩
  have r₂ := (VG.Proof.AesGcmSiv.X86_64.crypt_rel v L hR hDW hn (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T t₂) fun t₁ t₂ h =>
      ⟨⟨h.2.1.1.bufs.one, h.2.1.1.bufs.data⟩, ⟨h.2.2.1.bufs.one, h.2.2.1.bufs.data⟩⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T) (F₂ := VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.crypt_st v L hR h.2.1, VG.Proof.AesGcmSiv.X86_64.crypt_st v L hR h.2.2⟩
  have r₃ := (VG.Proof.AesGcmSiv.X86_64.polyval_rel v L hDW hn hal hn' (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.StK K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.1.bufs, h.2.2.1.bufs⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) (F₂ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.polyval_st v L h.2.1, VG.Proof.AesGcmSiv.X86_64.polyval_st v L h.2.2⟩
  have r₄ := (VG.Proof.AesGcmSiv.X86_64.tag_rel v L hR hDW hn (o := bO) (by decide) (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₁ ∧
      VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) (F₂ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.tag_st v L hR (by decide) h.2.1, VG.Proof.AesGcmSiv.X86_64.tag_st v L hR (by decide) h.2.2⟩
  have r₅ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [] (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₁ ∧ VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) VG.Proof.AesGcmSiv.X86_64.cmp_check).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.StO K W SP R N A D al n T) (F₂ := VG.Proof.AesGcmSiv.X86_64.StO K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.cmp_st L h.2.1, VG.Proof.AesGcmSiv.X86_64.cmp_st L h.2.2⟩
  have r₆ := (VG.Proof.AesGcmSiv.X86_64.rel_taintC [] (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.StO K W SP R N A D al n T t₁ ∧ VG.Proof.AesGcmSiv.X86_64.StO K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.bufs.one, h.2.2.1.bufs.one, fun _ h => nomatch h⟩) VG.Proof.AesGcmSiv.X86_64.mask_check).wp
    (F₁ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T) (F₂ := VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨VG.Proof.AesGcmSiv.X86_64.mask_st h.2.1, VG.Proof.AesGcmSiv.X86_64.mask_st h.2.2⟩
  have r₇ := VG.Proof.AesGcmSiv.X86_64.rel_taintC [] (P := fun t₁ t₂ => True ∧ VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₁ ∧ VG.Proof.AesGcmSiv.X86_64.St K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) VG.Proof.AesGcmSiv.X86_64.fin_check
  rw [VG.Proof.AesGcmSiv.X86_64.recv_split]
  exact RelCT.seq r₀ (RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (RelCT.seq r₅ (RelCT.seq r₆ r₇))))))

/-- `vg_aes_gcm_siv_open`, in two runs with the same public arguments. -/
theorem open_rel (v : GcmImpl) {s₀ s₀' : State} (hp : VG.Proof.AesGcmSiv.openPre s₀) (hp' : VG.Proof.AesGcmSiv.openPre s₀') (hq : VG.Proof.AesGcmSiv.onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callees) fun _ _ => True := by
  have Ar := (VG.Proof.AesGcmSiv.X86_64.args_of_open hp).1.1
  refine RelCT.seq (VG.Proof.AesGcmSiv.X86_64.entry_rel (VG.Proof.AesGcmSiv.X86_64.pub_regs hq) (hq.2.2.2.2.2.2.2 2 (by decide)) (VG.Proof.AesGcmSiv.X86_64.argW_in Ar rfl)
    (VG.Proof.AesGcmSiv.X86_64.argW_in (VG.Proof.AesGcmSiv.X86_64.args_of_open hp').1.1 rfl) (VG.Proof.AesGcmSiv.X86_64.entry_open hp) (VG.Proof.AesGcmSiv.X86_64.entry_open_pub hp' hq)) ?_
  exact VG.Proof.AesGcmSiv.X86_64.openBody_rel v Ar.lay Ar.rounds Ar.data.w (Nat.le_of_lt Ar.data.lt) Ar.aad.lt Ar.data.lt
    fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.AesGcmSiv.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.X86_64.Verified`. -/
section

/-!
# AES-GCM-SIV on x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`), states satisfying the preconditions, and the shared contracts
of `Spec/GcmSiv/Contract.lean` with the working space as a last argument
(`Proof/AesGcmSiv/Scratch.lean`, 477 words), with 8 bytes of stack: the
return address of a call of one of them, which make no calls. The last section
allocates the working space.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.Impl.AesGcmSiv.X86_64
open VG.Proof.AesGcm.X86_64 (GcmImpl)

/-- The CPU features of `seal` and `open`: those of the three functions they
call (here, to keep `List.dedup`'s imports out of the proofs). -/
def features (v : GcmImpl) : List String :=
  (v.ctr.features ++ v.key.features ++ v.gh.features).dedup

section
variable (v : GcmImpl)

theorem seal_mx : («seal» v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«seal», «open», entry, VG.Impl.AesGcmSiv.X86_64.keys, derive, deriveBlock, expand, hkey, polyval, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, VG.Impl.AesGcmSiv.X86_64.tagIn, tagOut, recv, crypt, cryptBlock, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.allInstrs, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem open_mx : («open» v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«seal», «open», entry, VG.Impl.AesGcmSiv.X86_64.keys, derive, deriveBlock, expand, hkey, polyval, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, VG.Impl.AesGcmSiv.X86_64.tagIn, tagOut, recv, crypt, cryptBlock, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.allInstrs, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_spSafe : («seal» v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«seal», «open», entry, VG.Impl.AesGcmSiv.X86_64.keys, derive, deriveBlock, expand, hkey, polyval, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, VG.Impl.AesGcmSiv.X86_64.tagIn, tagOut, recv, crypt, cryptBlock, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.all, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem open_spSafe : («open» v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«seal», «open», entry, VG.Impl.AesGcmSiv.X86_64.keys, derive, deriveBlock, expand, hkey, polyval, absorb, absorbChunk, revLoop, absorbTail, lens,
    tag, VG.Impl.AesGcmSiv.X86_64.tagIn, tagOut, recv, crypt, cryptBlock, cryptTail, mask, callCtr, callKey, callGh, GcmImpl.callees, Code.all, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_correct (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.AesGcmSiv.X86_64.seal_wp v GcmSiv.Polyval.polyvalFrom_eq hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesGcmSiv.X86_64.seal_mx v) he hg, hp⟩

theorem open_correct (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.AesGcmSiv.X86_64.open_wp v GcmSiv.Polyval.polyvalFrom_eq hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesGcmSiv.X86_64.open_mx v) he hg, hp⟩

theorem seal_ct : ConstantTime isa sealX86_64.pre sealX86_64.pub («seal» v.callees) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesGcmSiv.X86_64.seal_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem open_ct : ConstantTime isa openX86_64.pre openX86_64.pub («open» v.callees) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesGcmSiv.X86_64.open_rel v h₁ h₂ hq.1 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end

/-- A state satisfying the precondition of `vg_aes_gcm_siv_seal`: no
additional data, no data, the tag at `0x3000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0, 3816⟩]

theorem seal_verified (v : GcmImpl) :
    Verified X86_64.target («seal» v.callees) (Proof.AesGcmSiv.sealScratchContract X86_64.abi 477 8) :=
  Verified.of_correct (VG.Proof.AesGcmSiv.X86_64.seal_correct v) (VG.Proof.AesGcmSiv.X86_64.seal_ct v) (by
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Spec.GcmSiv.sealPost, Proof.AesGcmSiv.sealX86_64, Proof.AesGcmSiv.sealPre, Proof.AesGcmSiv.oneLay,
      Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args, Proof.AesGcmSiv.stk8,
      Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [sealSat] using VG.Proof.AesGcmSiv.X86_64.sealSat)

/-- A state satisfying the precondition of `vg_aes_gcm_siv_open`: as
`sealSat`, with the tag read only. -/
def openSat : State := { VG.Proof.AesGcmSiv.X86_64.sealSat with
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x8008, 24⟩]
  wr := [⟨0, 0⟩, ⟨0, 3816⟩] }

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : GcmImpl) :
    Verified X86_64.target («open» v.callees) (Proof.AesGcmSiv.openScratchContract X86_64.abi 477 8) :=
  Verified.of_correct (VG.Proof.AesGcmSiv.X86_64.open_correct v) (VG.Proof.AesGcmSiv.X86_64.open_ct v)
    { pre := by sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      -- `h` and the goal match on the same outcome of `decryptWith` with
      -- different matchers (`openPost`'s and `openPost`'s of the contract):
      -- split on it rather than have `exact h` unfold both to unify them.
      post := by
        intro s s' hs h
        sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] at h
        sig_simp [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [] at h
        intro _
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        sig_simp [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, Proof.AesGcmSiv.openX86_64,
        Proof.AesGcmSiv.openLeak, Proof.AesGcmSiv.openResult, Proof.AesGcmSiv.openPost, Proof.AesGcmSiv.openPre,
        Proof.AesGcmSiv.oneLay, Proof.AesGcmSiv.onePub, X86_64.abi, Proof.AesGcmSiv.arg, Proof.AesGcmSiv.args,
        Proof.AesGcmSiv.stk8, Proof.AesGcmSiv.ret, Proof.AesGcmSiv.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [openSat, sealSat] using VG.Proof.AesGcmSiv.X86_64.openSat }

/-! ## With the working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (above), in a frame that allocates it
(`Verified.stackArgScratch`): their working space is passed on the stack
after the six argument registers and two other stack arguments (`len` and
`tag`), so the frame of 3848 bytes holds the 3816 bytes of working space, a
copy of those two, the word that stands for the return address and the
address of the working space. The code's own calls use 8 bytes below it:
the return address of a call of `vg_aes_ctr32`, `vg_aes_expand_key` or
`vg_ghash`, which use no stack (`Ctr32Impl.noStack`, `KeyImpl.noStack`,
`GhashImpl.noStack`). `open`'s leak, whether it succeeds, reads only its
buffers (`openLeak_local`).
-/

variable (v : GcmImpl)

theorem seal_xdepth : («seal» v.callees).x86_64Depth ≤ 8 := by
  simp only [«seal», VG.Impl.AesGcmSiv.X86_64.keys, derive, expand, polyval, absorb, absorbChunk, absorbTail, lens, tag, crypt, cryptBlock,
    cryptTail, callCtr, callKey, callGh, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack, v.key.noStack,
    v.gh.noStack]
  decide +kernel

theorem open_xdepth : («open» v.callees).x86_64Depth ≤ 8 := by
  simp only [«open», VG.Impl.AesGcmSiv.X86_64.keys, derive, expand, polyval, absorb, absorbChunk, absorbTail, lens, tag, crypt, cryptBlock,
    cryptTail, callCtr, callKey, callGh, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack, v.key.noStack,
    v.gh.noStack]
  decide +kernel

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space. -/
def sealFrameSat : State :=
  { VG.Proof.AesGcmSiv.X86_64.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x8008, 16⟩], wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.GcmSiv.sealContract X86_64.abi 3856).pre s := by
  implies_sat [Spec.GcmSiv.sealContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using VG.Proof.AesGcmSiv.X86_64.sealFrameSat

theorem seal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 («seal» v.callees))
      (Spec.GcmSiv.sealContract X86_64.abi 3856) :=
  X86_64.Verified.stackArgScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 477) (pre := Spec.GcmSiv.sealPre X86_64.abi.ptrBits)
    (post := Spec.GcmSiv.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3848) (VG.Proof.AesGcmSiv.X86_64.seal_verified v) (by decide) (by decide) (by decide)
    (VG.Proof.AesGcmSiv.X86_64.seal_spSafe v) (VG.Proof.AesGcmSiv.X86_64.seal_xdepth v) (sealPre_local _) (sealPost_local _) VG.Proof.AesGcmSiv.X86_64.sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space. -/
def openFrameSat : State :=
  { VG.Proof.AesGcmSiv.X86_64.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x8008, 16⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.GcmSiv.openContract X86_64.abi 3856).pre s := by
  implies_sat [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Spec.GcmSiv.openPost,
    Spec.GcmSiv.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, sealSat] using VG.Proof.AesGcmSiv.X86_64.openFrameSat

theorem open_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 («open» v.callees))
      (Spec.GcmSiv.openContract X86_64.abi 3856) :=
  X86_64.Verified.stackArgScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 477) (pre := Spec.GcmSiv.openPre X86_64.abi.ptrBits)
    (post := Spec.GcmSiv.openPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.GcmSiv.openLeak X86_64.abi.ptrBits)) (bytes := 3848)
    (Proof.AesGcmSiv.Verified.of_openScratch (VG.Proof.AesGcmSiv.X86_64.open_verified v))
    (by decide) (by decide) (by decide) (VG.Proof.AesGcmSiv.X86_64.open_spSafe v) (VG.Proof.AesGcmSiv.X86_64.open_xdepth v) (openPre_local _)
    (openPost_local _) VG.Proof.AesGcmSiv.X86_64.openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.AesGcmSiv.X86_64

end
