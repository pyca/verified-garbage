import VerifiedGarbage.Proof.AesGcm.Arm.Frame
import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Impl.AesGcmSiv.Arm
import VerifiedGarbage.Proof.GcmSiv.Words32
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Gcm.Arm.Ghash
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.AesGcmSiv.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.Arm.Env`. -/
section

/-!
# AES-GCM-SIV on ARMv7: the contracts, and where everything is

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
    s.sp.toNat + 20 ≤ 2 ^ 32 ∧ VG.Proof.AesGcmSiv.Arm.rounds (s.gpr .r1)

/-- What `vg_aes_gcm_siv_seal` needs: `oneLay`, with `tag` the 16 bytes to
write, apart from the stack arguments. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨State.addr (s.gpr .r0), 240⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), 12⟩
  let aad : Region := ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩
  let data : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
  let tag : Region := ⟨State.addr (arg s 3), 16⟩
  let work : Region := ⟨State.addr (arg s 4), 3760⟩
  s.rd = [sch, nonce, aad, args s 5] ∧ s.wr = [data, tag, work] ∧ tag.Disjoint (args s 5) ∧ VG.Proof.AesGcmSiv.Arm.oneLay s

/-- What `vg_aes_gcm_siv_open` needs: `oneLay`, with the received tag the 16
bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨State.addr (s.gpr .r0), 240⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), 12⟩
  let aad : Region := ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩
  let data : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
  let tag : Region := ⟨State.addr (arg s 3), 16⟩
  let work : Region := ⟨State.addr (arg s 4), 3760⟩
  s.rd = [sch, nonce, aad, tag, args s 5] ∧ s.wr = [data, work] ∧ VG.Proof.AesGcmSiv.Arm.oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_siv_seal`. -/
def sealArm : Contract isa where
  pre := VG.Proof.AesGcmSiv.Arm.sealPre
  post s s' :=
    VG.Spec.GcmSiv.encryptWith (VG.Spec.GcmSiv.ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (keyLen (s.gpr .r1).toNat)
        (bytesAt s.mem (State.addr (s.gpr .r2)) 12) (bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)
        (bytesAt s.mem (State.addr (s.gpr .r3)) (arg s 0).toNat) =
      (bytesAt s'.mem (State.addr (arg s 1)) (arg s 2).toNat, bytesAt s'.mem (State.addr (arg s 3)) 16)
  pub := VG.Proof.AesGcmSiv.Arm.onePub

/-- What `vg_aes_gcm_siv_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  VG.Spec.GcmSiv.decryptWith (VG.Spec.GcmSiv.ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (keyLen (s.gpr .r1).toNat)
    (bytesAt s.mem (State.addr (s.gpr .r2)) 12) (bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)
    (bytesAt s.mem (State.addr (s.gpr .r3)) (arg s 0).toNat) (bytesAt s.mem (State.addr (arg s 3)) 16)

/-- What `vg_aes_gcm_siv_open` leaves in `r0` and in the `n` bytes of data
at `D`, for the result `r`. Irreducible, so that checking a state against
it never evaluates `r`. -/
@[irreducible] def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem D n = pt
  | none => s'.gpr .r0 = 0 ∧ bytesAt s'.mem D n = VG.Spec.GcmSiv.zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : s'.gpr .r0 = 1) (hd : bytesAt s'.mem D n = pt) : VG.Proof.AesGcmSiv.Arm.openPost r s' D n := by
  subst hr; unfold VG.Proof.AesGcmSiv.Arm.openPost; exact ⟨hax, hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : s'.gpr .r0 = 0) (hd : bytesAt s'.mem D n = VG.Spec.GcmSiv.zeros n) : VG.Proof.AesGcmSiv.Arm.openPost r s' D n := by
  subst hr; unfold VG.Proof.AesGcmSiv.Arm.openPost; exact ⟨hax, hd⟩

/-- `vg_aes_gcm_siv_open`. It does not branch on whether the tag is right,
so its runs are related without the leak the shared contract allows. -/
def openArm : Contract isa where
  pre := VG.Proof.AesGcmSiv.Arm.openPre
  post s s' := VG.Proof.AesGcmSiv.Arm.openPost (VG.Proof.AesGcmSiv.Arm.openResult s) s' (State.addr (arg s 1)) (arg s 2).toNat
  pub := VG.Proof.AesGcmSiv.Arm.onePub

end VG.Proof.AesGcmSiv.Arm

/-!
## Where everything is

Untrusted: everything here is checked by Lean. The public arguments
(`Prm`): the key schedule of the key-generating key (240 bytes at `K`), the
working space (3760 bytes at `W`), the nonce (12 bytes at `N`), the
additional data (`al` bytes at `A`), the data (`n` bytes at `D`), the tag
(16 bytes at `T`), the stack pointer and the number of rounds, all 32-bit;
how their regions lie, apart from each other, from the stack arguments (20
bytes at `SP`) and from the 8 bytes below `SP` that the calls' frames use
(`Lay`); what a state may access (`Perm`); the registers that hold some of
them throughout (`Env`), which the functions called preserve; and the stack
arguments `aad_len`, `data`, `len` and `tag` (`Args`), which nothing
writes. `srun` runs a block symbolically.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (below covers_off in_off in_left covers_left covers_prefix)

/-- Runs a block of the instructions the AES-GCM-SIV code uses. -/
macro "srun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  arun [Impl.AesGcmSiv.Arm.tagO, Impl.AesGcmSiv.Arm.akO, Impl.AesGcmSiv.Arm.ekO, Impl.AesGcmSiv.Arm.hO,
    Impl.AesGcmSiv.Arm.yO, Impl.AesGcmSiv.Arm.cbO, Impl.AesGcmSiv.Arm.ccO, Impl.AesGcmSiv.Arm.bO,
    Impl.AesGcmSiv.Arm.skO, Impl.AesGcmSiv.Arm.revO, Impl.AesGcmSiv.Arm.ghO,
    Impl.AesGcmSiv.Arm.scrO, $ts,*])

/-- The registers apart from `rs` are kept. -/
abbrev Others (rs : List Reg) (s s' : State) : Prop := ∀ r, r ∉ rs → s'.gpr r = s.gpr r

/-- Proves `Others` of a state `srun` computed. -/
macro "others_tac" : tactic => `(tactic| (
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [gpr_setReg, hr]))

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

/-- The stack arguments. -/
abbrev argR (SP : BitVec 32) : Region := ⟨State.addr SP, 20⟩

/-- How the regions lie. -/
structure Lay (p : VG.Proof.AesGcmSiv.Arm.Prm) : Prop where
  kw : p.K.toNat + 240 ≤ 2 ^ 32
  ww : p.W.toNat + 3760 ≤ 2 ^ 32
  nw : p.N.toNat + 12 ≤ 2 ^ 32
  aw : p.A.toNat + p.al ≤ 2 ^ 32
  dw : p.D.toNat + p.n ≤ 2 ^ 32
  al_lt : p.al < 2 ^ 32
  n_lt : p.n < 2 ^ 32
  sp8 : 8 ≤ p.SP.toNat
  spf : p.SP.toNat + 20 ≤ 2 ^ 32
  tw : p.T.toNat + 16 ≤ 2 ^ 32
  k_w : (⟨State.addr p.K, 240⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩
  k_d : (⟨State.addr p.K, 240⟩ : Region).Disjoint ⟨State.addr p.D, p.n⟩
  n_w : (⟨State.addr p.N, 12⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩
  n_d : (⟨State.addr p.N, 12⟩ : Region).Disjoint ⟨State.addr p.D, p.n⟩
  a_w : (⟨State.addr p.A, p.al⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩
  a_d : (⟨State.addr p.A, p.al⟩ : Region).Disjoint ⟨State.addr p.D, p.n⟩
  d_w : (⟨State.addr p.D, p.n⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩
  t_w : (⟨State.addr p.T, 16⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩
  t_d : (⟨State.addr p.T, 16⟩ : Region).Disjoint ⟨State.addr p.D, p.n⟩
  d_args : (⟨State.addr p.D, p.n⟩ : Region).Disjoint (VG.Proof.AesGcmSiv.Arm.argR p.SP)
  w_args : (⟨State.addr p.W, 3760⟩ : Region).Disjoint (VG.Proof.AesGcmSiv.Arm.argR p.SP)
  bk : (below p.SP).Disjoint ⟨State.addr p.K, 240⟩
  bn : (below p.SP).Disjoint ⟨State.addr p.N, 12⟩
  ba : (below p.SP).Disjoint ⟨State.addr p.A, p.al⟩
  bd : (below p.SP).Disjoint ⟨State.addr p.D, p.n⟩
  bw : (below p.SP).Disjoint ⟨State.addr p.W, 3760⟩
  rounds : p.R = 10 ∨ p.R = 14

/-- What a state may access. -/
structure Perm (p : VG.Proof.AesGcmSiv.Arm.Prm) (s : State) : Prop where
  k : Covers [⟨State.addr p.K, 240⟩] (s.rd ++ s.wr)
  non : Covers [⟨State.addr p.N, 12⟩] (s.rd ++ s.wr)
  aad : Covers [⟨State.addr p.A, p.al⟩] (s.rd ++ s.wr)
  d : Covers [⟨State.addr p.D, p.n⟩] s.wr
  w : Covers [⟨State.addr p.W, 3760⟩] s.wr
  args : Covers [VG.Proof.AesGcmSiv.Arm.argR p.SP] (s.rd ++ s.wr)
  /-- Nothing the state may write overlaps the stack arguments. -/
  argw : ∀ r ∈ s.wr, (VG.Proof.AesGcmSiv.Arm.argR p.SP).Disjoint r
  t : Covers [⟨State.addr p.T, 16⟩] (s.rd ++ s.wr)

theorem Perm.of_eq {p : VG.Proof.AesGcmSiv.Arm.Prm} {s s' : State} (h : VG.Proof.AesGcmSiv.Arm.Perm p s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesGcmSiv.Arm.Perm p s' := by
  obtain ⟨a, b, c, d, e, f, g, t⟩ := h
  exact ⟨by rw [hrd, hwr]; exact a, by rw [hrd, hwr]; exact b, by rw [hrd, hwr]; exact c, by rw [hwr]; exact d,
    by rw [hwr]; exact e, by rw [hrd, hwr]; exact f, by rw [hwr]; exact g, by rw [hrd, hwr]; exact t⟩

/-- The registers holding some of the public arguments, the stack pointer,
and what the state may access. -/
structure Env (p : VG.Proof.AesGcmSiv.Arm.Prm) (s : State) : Prop where
  r7 : s.gpr .r7 = p.A
  r8 : s.gpr .r8 = BitVec.ofNat 32 p.R
  r9 : s.gpr .r9 = p.K
  r10 : s.gpr .r10 = p.N
  r11 : s.gpr .r11 = p.W
  sp : s.sp = p.SP
  perm : VG.Proof.AesGcmSiv.Arm.Perm p s

/-- The registers `Env` pins. -/
abbrev envRegs : List Reg := [.r7, .r8, .r9, .r10, .r11]

/-- An environment, after code that keeps `r7`–`r11`, the stack pointer and
the permissions. -/
theorem Env.keep {p : VG.Proof.AesGcmSiv.Arm.Prm} {s s' : State} (h : VG.Proof.AesGcmSiv.Arm.Env p s) (hg : ∀ r ∈ VG.Proof.AesGcmSiv.Arm.envRegs, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcmSiv.Arm.Env p s' :=
  ⟨by rw [hg _ (by simp), h.r7], by rw [hg _ (by simp), h.r8], by rw [hg _ (by simp), h.r9],
    by rw [hg _ (by simp), h.r10], by rw [hg _ (by simp), h.r11], by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after a call. -/
theorem Env.of_saved {p : VG.Proof.AesGcmSiv.Arm.Prm} {s s' : State} (h : VG.Proof.AesGcmSiv.Arm.Env p s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcmSiv.Arm.Env p s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

/-- An environment, after code that writes only the registers `rs`. -/
theorem Env.of_others {p : VG.Proof.AesGcmSiv.Arm.Prm} {s s' : State} {rs : List Reg} (h : VG.Proof.AesGcmSiv.Arm.Env p s) (ho : VG.Proof.AesGcmSiv.Arm.Others rs s s')
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hd : ∀ r ∈ VG.Proof.AesGcmSiv.Arm.envRegs, r ∉ rs := by decide) :
    VG.Proof.AesGcmSiv.Arm.Env p s' :=
  h.keep (fun r h' => ho r (hd r h')) hsp hrd hwr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 3760) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 3760⟩ :=
  Offset.sub_base _ h

variable {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p)
include L

/-- An offset into `W`, as a 64-bit address. -/
theorem wA {d : Nat} (hd : d < 3760) : State.addr (p.W + BitVec.ofNat 32 d) = State.addr p.W + BitVec.ofNat 64 d :=
  addr_add (by have := L.ww; omega)

theorem wN {d : Nat} (hd : d < 3760) : (p.W + BitVec.ofNat 32 d).toNat = p.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 3760) (hd : d + k ≤ 3760) :
    (⟨State.addr p.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem k_w' {d k : Nat} (hd : d + k ≤ 3760) :
    (⟨State.addr p.K, 240⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (VG.Proof.AesGcmSiv.Arm.Lay.wSub hd)

theorem n_w' {d k : Nat} (hd : d + k ≤ 3760) :
    (⟨State.addr p.N, 12⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.n_w.sub_right (VG.Proof.AesGcmSiv.Arm.Lay.wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 3760) :
    (⟨State.addr p.A, p.al⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (VG.Proof.AesGcmSiv.Arm.Lay.wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 3760) :
    (⟨State.addr p.D, p.n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (VG.Proof.AesGcmSiv.Arm.Lay.wSub hd)

theorem t_w' {d k : Nat} (hd : d + k ≤ 3760) :
    (⟨State.addr p.T, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.t_w.sub_right (VG.Proof.AesGcmSiv.Arm.Lay.wSub hd)

theorem bw' {d k : Nat} (hd : d + k ≤ 3760) : (below p.SP).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.bw.sub_right (VG.Proof.AesGcmSiv.Arm.Lay.wSub hd)

theorem args_w' {d k : Nat} (hd : d + k ≤ 3760) : (VG.Proof.AesGcmSiv.Arm.argR p.SP).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.w_args.symm.sub_right (VG.Proof.AesGcmSiv.Arm.Lay.wSub hd)

/-- The stack arguments lie above the stack below `SP`. -/
theorem args_below : (VG.Proof.AesGcmSiv.Arm.argR p.SP).Disjoint (below p.SP) :=
  Offset.base_disjoint_below (State.addr p.SP) (n := 8) (k := 20) (by have := L.spf; omega)

theorem rounds_le : 16 * (p.R + 1) ≤ 240 := by rcases L.rounds with h | h <;> omega

theorem rounds3 : p.R = 10 ∨ p.R = 12 ∨ p.R = 14 := by rcases L.rounds with h | h <;> simp [h]

theorem toNat_R : (BitVec.ofNat 32 p.R).toNat = p.R := by
  rcases L.rounds with h | h <;> rw [h] <;> rfl

theorem ofNat_R_lt : p.R < 2 ^ 32 := by rcases L.rounds with h | h <;> omega

end Lay

namespace Perm

variable {p : VG.Proof.AesGcmSiv.Arm.Prm} {s : State} (P : VG.Proof.AesGcmSiv.Arm.Perm p s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 3760) : InRegions s.wr (State.addr p.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 3760) : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 3760) : Covers [⟨State.addr p.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 3760) : Covers [⟨State.addr p.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_left (P.wC h)

/-- The first 2560 bytes of `W`, where AES-GCM's save area is. -/
theorem w2560 : Covers [⟨State.addr p.W, 2560⟩] s.wr := covers_prefix P.w (by decide)

theorem nR {d k : Nat} (h : d + k ≤ 12) : InRegions (s.rd ++ s.wr) (State.addr p.N + BitVec.ofNat 64 d) k :=
  in_off P.non h (by decide)

end Perm

/-! ## The stack arguments -/

/-- The stack arguments `aad_len`, `data`, `len` and `tag` in the memory `m`. -/
structure Args (p : VG.Proof.AesGcmSiv.Arm.Prm) (m : Mem) : Prop where
  a0 : m.readW (State.addr (p.SP + BitVec.ofNat 32 0)) 32 = BitVec.ofNat 32 p.al
  a4 : m.readW (State.addr (p.SP + BitVec.ofNat 32 4)) 32 = p.D
  a8 : m.readW (State.addr (p.SP + BitVec.ofNat 32 8)) 32 = BitVec.ofNat 32 p.n
  a12 : m.readW (State.addr (p.SP + BitVec.ofNat 32 12)) 32 = p.T

theorem argA {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {k : Nat} (hk : k < 20) :
    State.addr (p.SP + BitVec.ofNat 32 k) = State.addr p.SP + BitVec.ofNat 64 k :=
  addr_add (by have := L.spf; omega)

/-- The stack arguments, after writes apart from them. -/
theorem Args.frame {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {m m' : Mem} (h : VG.Proof.AesGcmSiv.Arm.Args p m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.AesGcmSiv.Arm.argR p.SP).Disjoint r) : VG.Proof.AesGcmSiv.Arm.Args p m' := by
  have e : ∀ k, k + 4 ≤ 20 → m'.readW (State.addr (p.SP + BitVec.ofNat 32 k)) 32 =
      m.readW (State.addr (p.SP + BitVec.ofNat 32 k)) 32 := fun k hk => by
    rw [VG.Proof.AesGcmSiv.Arm.argA L (by omega)]
    exact hf.readW (r := ⟨State.addr p.SP + BitVec.ofNat 64 k, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)
  exact ⟨by rw [e 0 (by decide), h.a0], by rw [e 4 (by decide), h.a4], by rw [e 8 (by decide), h.a8],
    by rw [e 12 (by decide), h.a12]⟩

/-- A stack argument may be read. -/
theorem Perm.argR' {p : VG.Proof.AesGcmSiv.Arm.Prm} {s : State} (P : VG.Proof.AesGcmSiv.Arm.Perm p s) (L : VG.Proof.AesGcmSiv.Arm.Lay p) {k : Nat} (hk : k + 4 ≤ 20) :
    InRegions (s.rd ++ s.wr) (State.addr (p.SP + BitVec.ofNat 32 k)) 4 := by
  rw [VG.Proof.AesGcmSiv.Arm.argA L (by omega)]; exact in_off P.args hk (by decide)

/-! ## Arithmetic -/

theorem ofNat_lsl32 (a k : Nat) : BitVec.ofNat 32 a <<< k = BitVec.ofNat 32 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]

theorem ofNat_lsr32 {a : Nat} (ha : a < 2 ^ 32) (k : Nat) : BitVec.ofNat 32 a >>> k = BitVec.ofNat 32 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by have := Nat.div_le_self a (2 ^ k); omega)]

/-- The `n` bytes at `p + d` within the `k` bytes at `p`. -/
theorem contains_at (p : Addr) {d n k : Nat} (h : d + n ≤ k) (hk : k < 2 ^ 64) :
    (⟨p, k⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := Offset.contains_base p h (by omega)

theorem contains_at0 (p : Addr) {n k : Nat} (h : n ≤ k) (hk : k < 2 ^ 64) :
    (⟨p, k⟩ : Region).Contains p n := by
  simpa using VG.Proof.AesGcmSiv.Arm.contains_at p (d := 0) (by omega : 0 + n ≤ k) hk

end VG.Proof.AesGcmSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.Arm.Derive`. -/
section

/-!
# AES-GCM-SIV on ARMv7: the message keys (`derive`)

Untrusted: everything here is checked by Lean. Each step of `derive` writes
`little_endian_uint32(i) ‖ nonce` at `W + 112` and a zero block at
`W + 176` (`derArgs_ok`), on which `vg_aes_ctr32` leaves
`CIPH_K(little_endian_uint32(i) ‖ nonce)`, of which the first 8 bytes are
kept at `W + 16 + 8 i` (`derPost_ok`): after the loop, the halves of
`derive_keys` (`derive_ok`, `DInv.keys`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (CtrCall CtrPost ctr_call below add_ofNat_zero add_ofNat_assoc add32_ofNat_assoc
  covers_cons covers_nil covers_append' eval_ne' z_cmp ofNat_sub32 ofNat_add32 toNat32 mem_store gpr_store sp_store
  rd_store wr_store z_store mem_subFlags z_subFlags gpr_subFlags sp_subFlags rd_subFlags wr_subFlags)

/-- An offset into the nonce, as a 64-bit address. -/
theorem Lay.nA {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {d : Nat} (hd : d < 12) :
    State.addr (p.N + BitVec.ofNat 32 d) = State.addr p.N + BitVec.ofNat 64 d :=
  addr_add (by have := L.nw; omega)

/-- The memory after a step's block: the counter block and a zero block. -/
def derMem (m : Mem) (W N : Addr) (i : Nat) : Mem :=
  Proof.Cmac.zero4 (Proof.Cmac.store4 m (W + BitVec.ofNat 64 112) (BitVec.ofNat 32 i)
    (m.readW N 32) (m.readW (N + BitVec.ofNat 64 4) 32) (m.readW (N + BitVec.ofNat 64 8) 32)) (W + BitVec.ofNat 64 176)

/-- The arguments of a step: the counter block and a zero block. -/
theorem derArgs_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) {i : Nat} (h4 : t.gpr .r4 = BitVec.ofNat 32 i) :
    ∃ t₁ : State, runBlock isa deriveBlock t = some t₁ ∧ t₁.mem = VG.Proof.AesGcmSiv.Arm.derMem t.mem (State.addr p.W) (State.addr p.N) i ∧
      t₁.gpr .r0 = p.K ∧ t₁.gpr .r1 = BitVec.ofNat 32 p.R ∧ t₁.gpr .r2 = p.W + BitVec.ofNat 32 112 ∧
      t₁.gpr .r3 = p.W + BitVec.ofNat 32 176 ∧ t₁.gpr .r12 = BitVec.ofNat 32 1 ∧
      t₁.gpr .lr = p.W + BitVec.ofNat 32 1712 ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r0, .r1, .r2, .r3, .r12, .lr] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have n₀ : InRegions (t.rd ++ t.wr) (State.addr p.N) 4 := by simpa using E.perm.nR (d := 0) (k := 4) (by decide)
  have n₄ := E.perm.nR (d := 4) (k := 4) (by decide)
  have n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  have w₁ := E.perm.wW (show 112 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 116 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 120 + 4 ≤ 3760 by decide)
  have w₄ := E.perm.wW (show 124 + 4 ≤ 3760 by decide)
  have w₅ := E.perm.wW (show 176 + 4 ≤ 3760 by decide)
  have w₆ := E.perm.wW (show 180 + 4 ≤ 3760 by decide)
  have w₇ := E.perm.wW (show 184 + 4 ≤ 3760 by decide)
  have w₈ := E.perm.wW (show 188 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [deriveBlock, Impl.AesGcm.Arm.zero16]; srun [E.r10, E.r11, add_ofNat_zero, L.nA, L.wA,
    n₀, n₄, n₈, w₁, w₂, w₃, w₄, w₅, w₆, w₇, w₈], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
  · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, VG.Proof.AesGcmSiv.Arm.derMem, Proof.Cmac.zero4,
      Proof.Cmac.store4, h4, add_ofNat_assoc, Nat.reduceAdd]
    rfl
  · simp [gpr_setReg, E.r9]
  · simp [gpr_setReg, E.r8]
  · simp [gpr_setReg, E.r11]
  · simp [gpr_setReg, E.r11]
  · simp [gpr_setReg]
  · simp [gpr_setReg, E.r11]


/-- What the code after a step's call writes: the 8 bytes kept. -/
def postMem (m : Mem) (W : Addr) (i : Nat) : Mem :=
  (m.writeW (W + BitVec.ofNat 64 (16 + 8 * i)) (m.readW (W + BitVec.ofNat 64 176) 32)).writeW
    (W + BitVec.ofNat 64 (20 + 8 * i)) (m.readW (W + BitVec.ofNat 64 180) 32)

theorem ofNat_lsl3 {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {i k : Nat} (hi : 8 * i + k < 3760) :
    State.addr (p.W + BitVec.ofNat 32 i <<< 3 + BitVec.ofNat 32 k) = State.addr p.W + BitVec.ofNat 64 (k + 8 * i) := by
  rw [VG.Proof.AesGcmSiv.Arm.ofNat_lsl32, add32_ofNat_assoc, L.wA (by omega)]
  congr 2; omega

/-- The code after the call of a step. -/
theorem derPost_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) {i : Nat} (hi : i < p.R / 2 - 1)
    (h4 : t.gpr .r4 = BitVec.ofNat 32 i) :
    ∃ t' : State, runBlock isa derivePost t = some t' ∧ t'.mem = VG.Proof.AesGcmSiv.Arm.postMem t.mem (State.addr p.W) i ∧
      t'.gpr .r4 = BitVec.ofNat 32 (i + 1) ∧ t'.z = decide (i + 1 = p.R / 2 - 1) ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r0, .r1, .r2, .r4, .r12] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR := L.rounds
  have r₀ := E.perm.wR (show 176 + 4 ≤ 3760 by decide)
  have r₁ := E.perm.wR (show 180 + 4 ≤ 3760 by decide)
  have wo₀ := E.perm.wW (d := 16 + 8 * i) (n := 4) (by omega)
  have wo₁ := E.perm.wW (d := 20 + 8 * i) (n := 4) (by omega)
  have ea₀ := VG.Proof.AesGcmSiv.Arm.ofNat_lsl3 L (i := i) (k := 16) (by omega)
  have ea₁ := VG.Proof.AesGcmSiv.Arm.ofNat_lsl3 L (i := i) (k := 20) (by omega)
  refine ⟨_, by simp only [derivePost]; srun [E.r8, E.r11, h4, L.wA, ea₀, ea₁, r₀, r₁, wo₀, wo₁], ?_⟩
  refine ⟨?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
  · simp only [mem_setReg, mem_store, mem_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, VG.Proof.AesGcmSiv.Arm.postMem]
  · simp [gpr_setReg, h4, ofNat_add32]
  · simp only [z_setReg, z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, z_store, gpr_store, h4, E.r8,
      VG.Proof.AesGcmSiv.Arm.ofNat_lsr32 L.ofNat_R_lt, ofNat_add32]
    rw [ofNat_sub32 (by rcases hR with h | h <;> rw [h] <;> decide) (by have := L.ofNat_R_lt; omega),
      z_cmp (by have := L.ofNat_R_lt; omega) (by have := L.ofNat_R_lt; omega), Nat.pow_one]
    congr 1; apply propext; omega

theorem postMem_frame (m : Mem) (W : Addr) (i : Nat) (hi : 8 * i + 24 < 2 ^ 64) :
    Frame [⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩] m (VG.Proof.AesGcmSiv.Arm.postMem m W i) := by
  have c₀ : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩ : Region).Contains (W + BitVec.ofNat 64 (16 + 8 * i)) (32 / 8) :=
    Offset.contains W (by omega) (by omega) (by omega)
  have c₁ : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩ : Region).Contains (W + BitVec.ofNat 64 (20 + 8 * i)) (32 / 8) :=
    Offset.contains W (by omega) (by omega) (by omega)
  unfold VG.Proof.AesGcmSiv.Arm.postMem
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₀).writeW (List.mem_singleton_self _) _ c₁

/-- The counter block of a step: `little_endian_uint32(i) ‖ nonce`. -/
theorem derBlock_bytes (m : Mem) (W N : Addr) (i : Nat) :
    bytesAt (VG.Proof.AesGcmSiv.Arm.derMem m W N i) (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt m N 12 := by
  rw [VG.Proof.AesGcmSiv.Arm.derMem, Proof.Cmac.zero4, Proof.AesGcm.Arm.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide),
    Proof.Cmac.bytesAt_store4, GcmSiv.le4_ofNat, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, show (12 : Nat) = 4 + (4 + 4) from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add,
    add_ofNat_assoc]
  simp only [List.append_assoc]


/-- The zero block of a step. -/
theorem derZero_block (W N : Addr) (m : Mem) (i : Nat) :
    Spec.Gcm.blockAt (VG.Proof.AesGcmSiv.Arm.derMem m W N i) (W + BitVec.ofNat 64 176) = 0 := by
  rw [VG.Proof.AesGcmSiv.Arm.derMem, Spec.Gcm.blockAt, Proof.Cmac.zero4_bytes]
  decide

theorem derMem_frame (m : Mem) (W N : Addr) (i : Nat) :
    Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 176, 16⟩] m (VG.Proof.AesGcmSiv.Arm.derMem m W N i) :=
  ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self).trans
    ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self)

/-- What `derive` writes. -/
abbrev derR (W : Addr) (SP : BitVec 32) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 48⟩, ⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 176, 16⟩,
    ⟨W + BitVec.ofNat 64 1712, 2048⟩, below SP]

/-- After `i` steps of `derive` from `σ`: the first `8 i` bytes of the halves
at `W + 16`. -/
structure DInv (p : VG.Proof.AesGcmSiv.Arm.Prm) (σ : State) (i : Nat) (t : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t
  r4 : t.gpr .r4 = BitVec.ofNat 32 i
  le : i ≤ p.R / 2 - 1
  frame : Frame (VG.Proof.AesGcmSiv.Arm.derR (State.addr p.W) p.SP) σ.mem t.mem
  out : bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) (8 * i) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem (State.addr p.K) p.R) (bytesAt σ.mem (State.addr p.N) 12) i

/-- Buffers apart from `W` and the stack below `SP` are kept by `derive`. -/
theorem bytesAt_derR {p : VG.Proof.AesGcmSiv.Arm.Prm} {P : Addr} {len : Nat}
    (hP : (⟨P, len⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩) (hb : (below p.SP).Disjoint ⟨P, len⟩)
    (hl : len ≤ 2 ^ 64) {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.Arm.derR (State.addr p.W) p.SP) m m') :
    bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.Arm.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hP.sub_right (Lay.wSub (by decide))
    · exact hP.sub_right (Lay.wSub (by decide))
    · exact hP.sub_right (Lay.wSub (by decide))
    · exact hP.sub_right (Lay.wSub (by decide))
    · exact hb.symm) hl

/-- The key schedule is kept by `derive`. -/
theorem ciph_derR {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.Arm.derR (State.addr p.W) p.SP) m m') :
    Spec.GcmSiv.ctxCiph m' (State.addr p.K) p.R = Spec.GcmSiv.ctxCiph m (State.addr p.K) p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [VG.Proof.AesGcmSiv.Arm.bytesAt_derR (L.k_w.sub_left (Region.sub_prefix L.rounds_le))
    (L.bk.sub_right (Region.sub_prefix L.rounds_le)) (by have := L.rounds_le; omega) hf]

/-- The arguments of a step's call. -/
theorem derCall {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t₁ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p t₁) (r0 : t₁.gpr .r0 = p.K)
    (r1 : t₁.gpr .r1 = BitVec.ofNat 32 p.R) (r2 : t₁.gpr .r2 = p.W + BitVec.ofNat 32 112)
    (r3 : t₁.gpr .r3 = p.W + BitVec.ofNat 32 176) (r12 : t₁.gpr .r12 = BitVec.ofNat 32 1)
    (lr : t₁.gpr .lr = p.W + BitVec.ofNat 32 1712) :
    CtrCall t₁ p.K (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 176) (p.W + BitVec.ofNat 32 1712) p.R 1 := by
  have ww := L.ww
  refine ⟨r0, r1, r2, r3, r12, lr, L.rounds3, by rw [E₁.sp]; exact L.sp8, L.kw,
    by rw [L.wN (by decide)]; omega, by rw [L.wN (by decide)]; omega, by rw [L.wN (by decide)]; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [L.wA (show 112 < 3760 by decide), L.wA (show 176 < 3760 by decide),
      L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one]
  · exact L.k_w' (by decide)
  · exact L.k_w' (by decide)
  · exact L.k_w' (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.bk
  · exact L.bw' (by decide)
  · exact L.bw' (by decide)
  · exact L.bw' (by decide)
  · exact E₁.perm.k
  · exact covers_cons (E₁.perm.wC (by decide)) (covers_cons (E₁.perm.wC (by decide))
      (covers_cons (E₁.perm.wC (by decide)) covers_nil))


/-- The 8 bytes a step keeps: the first 8 of the block at `W + 176`. -/
theorem postMem_bytes (m : Mem) (W : Addr) (i : Nat) (hi : 8 * i + 24 < 2 ^ 64) :
    bytesAt (VG.Proof.AesGcmSiv.Arm.postMem m W i) (W + BitVec.ofNat 64 (16 + 8 * i)) 8 = bytesAt m (W + BitVec.ofNat 64 176) 8 := by
  have e : W + BitVec.ofNat 64 (20 + 8 * i) = W + BitVec.ofNat 64 (16 + 8 * i) + BitVec.ofNat 64 4 := by
    rw [add_ofNat_assoc]; congr 2; omega
  have d : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 4⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (20 + 8 * i), 4⟩ :=
    Offset.disjoint W (.inl (by omega)) (by omega) (by omega)
  rw [show (8 : Nat) = 4 + 4 from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, ← e,
    ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, VG.Proof.AesGcmSiv.Arm.postMem,
    Proof.Cmac.readW_writeW_disj _ d.symm, Mem.readW_writeW_self32, Mem.readW_writeW_self32, add_ofNat_assoc]

/-- A step of `derive`. -/
theorem derStep_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {σ : State} {i : Nat} (hi : i < p.R / 2 - 1) {t : State}
    (I : VG.Proof.AesGcmSiv.Arm.DInv p σ i t) :
    WP isa (.seq (.block deriveBlock) (.seq Impl.AesGcm.Arm.ctrFrame (.block derivePost))) t fun t' =>
      VG.Proof.AesGcmSiv.Arm.DInv p σ (i + 1) t' ∧ t'.z = decide (i + 1 = p.R / 2 - 1) := by
  have hR := L.rounds
  have hw := L.ww
  have hi6 : i ≤ 5 := by rcases hR with h | h <;> rw [h] at hi <;> omega
  have eN : bytesAt t.mem (State.addr p.N) 12 = bytesAt σ.mem (State.addr p.N) 12 :=
    VG.Proof.AesGcmSiv.Arm.bytesAt_derR L.n_w L.bn (by decide) I.frame
  have eK := VG.Proof.AesGcmSiv.Arm.ciph_derR L I.frame
  obtain ⟨t₁, run₁, hm₁, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.Arm.derArgs_ok L I.env I.r4
  have E₁ : VG.Proof.AesGcmSiv.Arm.Env p t₁ := I.env.of_others ho₁ sp₁ rd₁ wr₁
  have cc := VG.Proof.AesGcmSiv.Arm.derCall L E₁ r0 r1 r2 r3 r12 lr
  have hb₁ : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 112) 16 =
      Spec.GcmSiv.le32 i ++ bytesAt t.mem (State.addr p.N) 12 := by
    rw [hm₁]; exact VG.Proof.AesGcmSiv.Arm.derBlock_bytes _ _ _ _
  have hz₁ : Spec.Gcm.blockAt t₁.mem (State.addr p.W + BitVec.ofNat 64 176) = 0 := by
    rw [hm₁]; exact VG.Proof.AesGcmSiv.Arm.derZero_block _ _ _ _
  have f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩]
      t.mem t₁.mem := by rw [hm₁]; exact VG.Proof.AesGcmSiv.Arm.derMem_frame _ _ _ _
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (ctr_call cc) fun t₂ P => ?_)
  have E₂ : VG.Proof.AesGcmSiv.Arm.Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have h4₂ : t₂.gpr .r4 = BitVec.ofNat 32 i := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), I.r4]
  have fc := P.frame
  have hout := P.out
  simp only [L.wA (show 112 < 3760 by decide), L.wA (show 176 < 3760 by decide),
    L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one] at fc hout
  obtain ⟨t₃, run₃, hm₃, r4₃, z₃, ho₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesGcmSiv.Arm.derPost_ok L E₂ hi h4₂
  refine WP.of_runBlock ⟨t₃, run₃, ⟨E₂.of_others ho₃ sp₃ rd₃ wr₃, r4₃, by omega, ?_, ?_⟩, z₃⟩
  · -- The frame.
    have mem : ∀ {r : Region}, r ∈ VG.Proof.AesGcmSiv.Arm.derR (State.addr p.W) p.SP → ∃ r' ∈ VG.Proof.AesGcmSiv.Arm.derR (State.addr p.W) p.SP, Region.Sub r r' :=
      fun {r} h => ⟨r, h, fun _ h => h⟩
    refine ((I.frame.trans (f₁.sub fun r hr => ?_)).trans (fc.sub fun r hr => ?_)).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact mem (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact mem (by simp)
    · rw [hm₃]
      exact (VG.Proof.AesGcmSiv.Arm.postMem_frame _ _ _ (by omega)).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, Offset.sub _ (by omega) (by omega)⟩
  · -- The bytes.
    have dW : ∀ {d k : Nat}, d + k ≤ 3760 → 16 + 8 * i ≤ d ∨ d + k ≤ 16 →
        (⟨State.addr p.W + BitVec.ofNat 64 16, 8 * i⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ h₂ => L.w_w (by omega) (by omega) h₁
    have keep : bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 16) (8 * i) =
        bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) (8 * i) := by
      rw [hm₃, Proof.AesGcm.Arm.bytesAt_frame (VG.Proof.AesGcmSiv.Arm.postMem_frame _ _ _ (by omega))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW (by omega) (by omega)) (by omega),
        Proof.AesGcm.Arm.bytesAt_frame fc (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact dW (by decide) (by omega)
          · exact dW (by decide) (by omega)
          · exact dW (by decide) (by omega)
          · exact (L.bw' (by omega)).symm) (by omega),
        Proof.AesGcm.Arm.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact dW (by decide) (by omega)) (by omega)]
    simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
    have last : bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 (16 + 8 * i)) 8 =
        (Spec.GcmSiv.ctxCiph σ.mem (State.addr p.K) p.R
          (Spec.GcmSiv.le32 i ++ bytesAt σ.mem (State.addr p.N) 12)).take 8 := by
      have e16 : bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 16 =
          bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 8 ++
            bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176 + BitVec.ofNat 64 8) 8 :=
        Proof.Cmac.bytesAt_add _ _ 8 8
      have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.K) p.R = Spec.GcmSiv.ctxCiph t.mem (State.addr p.K) p.R := by
        unfold Spec.GcmSiv.ctxCiph
        rw [Proof.AesGcm.Arm.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rounds_le))
          (by omega)]
      rw [hm₃, VG.Proof.AesGcmSiv.Arm.postMem_bytes _ _ _ (by omega),
        show bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 8 =
          (bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 16).take 8 by
          rw [e16, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)],
        Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt, hb₁,
        Proof.Cmac.aesWith_bytes _ _ (by rw [List.length_append, Proof.Cmac.bytesAt_length]; rfl),
        ← GcmSiv.aesWith_eq, show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (State.addr p.K) (16 * (p.R + 1))) =
          Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.K) p.R from rfl, ek₁, eK, eN]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, Proof.Cmac.bytesAt_add, GcmSiv.halves_succ, ← I.out, keep,
      add_ofNat_assoc, last]

/-- `derive`: the halves of `derive_keys` at `W + 16`. -/
theorem derive_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {σ : State} (E : VG.Proof.AesGcmSiv.Arm.Env p σ) :
    WP isa derive σ (VG.Proof.AesGcmSiv.Arm.DInv p σ (p.R / 2 - 1)) := by
  have hR := L.rounds
  refine WP.seq (Proof.AesGcm.Arm.WP.run (Q := fun t => VG.Proof.AesGcmSiv.Arm.DInv p σ 0 t) ⟨_, by srun [], ?_⟩ fun t I₀ => ?_)
  · exact ⟨E.keep (fun r hr => by
        simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      by simp [gpr_setReg], Nat.zero_le _, by rw [mem_setReg]; exact Frame.refl _ _, rfl⟩
  refine WP.loop (M := isa) (fun m t => ∃ i, m = (p.R / 2 - 1) - i ∧ i < p.R / 2 - 1 ∧ VG.Proof.AesGcmSiv.Arm.DInv p σ i t) ?_
    ((p.R / 2 - 1) - 0) _ ⟨0, rfl, by rcases hR with h | h <;> rw [h] <;> decide, I₀⟩
  rintro m t ⟨i, rfl, hi, I⟩
  refine WP.mono (VG.Proof.AesGcmSiv.Arm.derStep_ok L hi I) fun t' ⟨I', hz⟩ => ?_
  have ev := eval_ne' hz
  by_cases he : i + 1 = p.R / 2 - 1
  · left; exact ⟨ev.trans (by simp [he]), he ▸ I'⟩
  · right; exact ⟨ev.trans (by simp [he]), (p.R / 2 - 1) - (i + 1), by omega, i + 1, rfl, by omega, I'⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DInv.keys {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {σ t : State} (I : VG.Proof.AesGcmSiv.Arm.DInv p σ (p.R / 2 - 1) t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (State.addr p.K) p.R) (Spec.GcmSiv.keyLen p.R)
        (bytesAt σ.mem (State.addr p.N) 12) =
      (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16,
        bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R)) := by
  have hR := L.rounds
  have hk : Spec.GcmSiv.keyLen p.R / 8 + 2 = p.R / 2 - 1 := by unfold Spec.GcmSiv.keyLen; omega
  have hl : 8 * (p.R / 2 - 1) = 16 + Spec.GcmSiv.keyLen p.R := by unfold Spec.GcmSiv.keyLen; omega
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, add_ofNat_assoc] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem _ p.R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesGcmSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.Arm.Keys`. -/
section

/-!
# AES-GCM-SIV on ARMv7: the encryption key's schedule and GHASH's key

Untrusted: everything here is checked by Lean. `expand` writes the schedule
of the encryption key at `W + 192` (`expand_ok`), and `hkey` GHASH's key,
`H · x` for the authentication key `H` (POLYVAL's field element), in
GHASH's order at `W + 64`, and zeroes its accumulator (`hkey_ok`).
`keys_ok`: the three together.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (hkeyOf)
open VG.Proof.AesGcm.Arm (KeyCall KeyPost key_call below add_ofNat_zero add_ofNat_assoc covers_cons covers_nil
  covers_append' ofNat_sub32 mem_store gpr_store sp_store rd_store wr_store z_store)

/-! ## Blocks stored a word at a time -/

/-- A block stored as four words, read by GHASH. -/
theorem blockAt_store4 (m : Mem) (p : Addr) (a b c d : BitVec 32) :
    Spec.Gcm.blockAt (Proof.Cmac.store4 m p a b c d) p = Proof.Gcm.Arm.w4 (rev a) (rev b) (rev c) (rev d) := by
  have dj : ∀ {x y : Nat}, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 16 → y + 4 ≤ 16 →
      (⟨p + BitVec.ofNat 64 x, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 y, 4⟩ :=
    fun h hx hy => Offset.disjoint p h (by omega) (by omega)
  have d₀ : (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 4, 4⟩ := by
    simpa using dj (x := 0) (y := 4) (.inl (by decide)) (by decide) (by decide)
  have d₀' : (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 8, 4⟩ := by
    simpa using dj (x := 0) (y := 8) (.inl (by decide)) (by decide) (by decide)
  have d₀'' : (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 12, 4⟩ := by
    simpa using dj (x := 0) (y := 12) (.inl (by decide)) (by decide) (by decide)
  rw [Proof.Gcm.Arm.blockAt_rev, Proof.Cmac.store4]
  simp only [Proof.Cmac.readW_writeW_disj _ (dj (x := 12) (y := 8) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ (dj (x := 12) (y := 4) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ (dj (x := 8) (y := 4) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ d₀.symm, Proof.Cmac.readW_writeW_disj _ d₀'.symm,
    Proof.Cmac.readW_writeW_disj _ d₀''.symm, Mem.readW_writeW_self32]

/-! ## `expand` -/

/-- What `expand` leaves: the schedule of the encryption key at `W + 192`. -/
structure ExpPost (p : VG.Proof.AesGcmSiv.Arm.Prm) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t'
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 192, 240⟩, ⟨State.addr p.W + BitVec.ofNat 64 1712, 512⟩]
    t.mem t'.mem
  ciph : Spec.GcmSiv.ctxCiph t'.mem (State.addr p.W + BitVec.ofNat 64 192) p.R =
    Spec.GcmSiv.aes (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R))

theorem keyLen_lsl {R : Nat} (hR : R = 10 ∨ R = 14) :
    (BitVec.ofNat 32 R - BitVec.ofNat 32 6) <<< 2 = BitVec.ofNat 32 (Spec.GcmSiv.keyLen R) := by
  rw [ofNat_sub32 (by omega) (by omega), VG.Proof.AesGcmSiv.Arm.ofNat_lsl32]
  congr 1; unfold Spec.GcmSiv.keyLen; omega

/-- The arguments of `expand`'s call. -/
theorem expArgs_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) :
    ∃ t₁ : State, runBlock isa expandArgs t = some t₁ ∧
      KeyCall t₁ (p.W + BitVec.ofNat 32 32) (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 1712)
        (Spec.GcmSiv.keyLen p.R) ∧ VG.Proof.AesGcmSiv.Arm.Env p t₁ ∧ t₁.mem = t.mem := by
  have hl : Spec.GcmSiv.keyLen p.R = 16 ∨ Spec.GcmSiv.keyLen p.R = 32 := by
    unfold Spec.GcmSiv.keyLen; rcases L.rounds with h | h <;> omega
  have hR := L.rounds
  have ww := L.ww
  refine ⟨_, by simp only [expandArgs]; srun [E.r8, E.r11], ⟨?r0, ?r1, ?r2, ?r3, ?len, ?fK, ?fC, ?fS, ?kc, ?ks, ?cs,
    ?rd, ?wr⟩, E.keep (fun r hr => ?regs) (by rfl) (by rfl) (by rfl), by rfl⟩
  case regs =>
    simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  case r0 => simp [gpr_setReg, E.r11]
  case r1 => simp [gpr_setReg, E.r8, VG.Proof.AesGcmSiv.Arm.keyLen_lsl hR]
  case r2 => simp [gpr_setReg, E.r11]
  case r3 => simp [gpr_setReg, E.r11]
  case len => omega
  case fK => rw [L.wN (by decide)]; omega
  case fC => rw [L.wN (by decide)]; omega
  case fS => rw [L.wN (by decide)]; omega
  case kc => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by omega)) (by omega) (by decide)
  case ks => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by omega)) (by omega) (by decide)
  case cs => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case rd => rw [L.wA (by decide)]; exact E.perm.wCR (by omega)
  case wr =>
    rw [L.wA (by decide), L.wA (by decide)]
    exact covers_cons (E.perm.wC (by decide)) (covers_cons (E.perm.wC (by decide)) covers_nil)

theorem expand_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) : WP isa expand t (VG.Proof.AesGcmSiv.Arm.ExpPost p t) := by
  obtain ⟨t₁, run₁, kc, E₁, hm₁⟩ := VG.Proof.AesGcmSiv.Arm.expArgs_ok L E
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (key_call kc) fun t₂ P => ?_
  have fr := P.frame
  have out := P.out
  simp only [L.wA (show 32 < 3760 by decide), L.wA (show 192 < 3760 by decide),
    L.wA (show 1712 < 3760 by decide)] at fr out
  refine ⟨E₁.of_saved P.saved P.sp P.rd P.wr, by rw [← hm₁]; exact fr, ?_⟩
  have hr : Spec.Aes.rounds (Spec.GcmSiv.keyLen p.R / 4) = p.R := by
    unfold Spec.Aes.rounds Spec.GcmSiv.keyLen; rcases L.rounds with h | h <;> rw [h]
  rw [hr] at out
  rw [Spec.GcmSiv.ctxCiph, out, Spec.GcmSiv.aes, Proof.Cmac.bytesAt_length, hr, hm₁]

/-! ## `hkey` -/

/-- GHASH's key from the words `w₀`–`w₃` of the authentication key, as
`hkey` computes it: its four words, the most significant first. -/
abbrev hk3 (w₀ w₃ : BitVec 32) : BitVec 32 := (w₃ >>> 1) ^^^ ((0#32 - (w₀ &&& 1#32)) &&& 0xE1000000#32)
abbrev hkW (lo hi : BitVec 32) : BitVec 32 := (lo >>> 1) ||| (hi <<< 31)

/-- The memory `hkey` leaves. -/
def hkeyMem (m : Mem) (W : Addr) : Mem :=
  let w₀ := m.readW (W + BitVec.ofNat 64 16) 32
  let w₁ := m.readW (W + BitVec.ofNat 64 20) 32
  let w₂ := m.readW (W + BitVec.ofNat 64 24) 32
  let w₃ := m.readW (W + BitVec.ofNat 64 28) 32
  Proof.Cmac.zero4 (Proof.Cmac.store4 m (W + BitVec.ofNat 64 64) (rev (VG.Proof.AesGcmSiv.Arm.hk3 w₀ w₃)) (rev (VG.Proof.AesGcmSiv.Arm.hkW w₂ w₃))
    (rev (VG.Proof.AesGcmSiv.Arm.hkW w₁ w₂)) (rev (VG.Proof.AesGcmSiv.Arm.hkW w₀ w₁))) (W + BitVec.ofNat 64 80)

theorem hkeyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 64, 32⟩] m (VG.Proof.AesGcmSiv.Arm.hkeyMem m W) :=
  ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩).trans
    ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩)

theorem hkeyMem_key (m : Mem) (W : Addr) :
    Spec.Gcm.blockAt (VG.Proof.AesGcmSiv.Arm.hkeyMem m W) (W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt m (W + BitVec.ofNat 64 16) 16)) := by
  rw [VG.Proof.AesGcmSiv.Arm.hkeyMem, Proof.Cmac.zero4, Proof.AesGcm.Arm.blockAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)),
    VG.Proof.AesGcmSiv.Arm.blockAt_store4, rev_rev, rev_rev, rev_rev, rev_rev, Proof.Gcm.Arm.w4, GcmSiv.Words32.hkeyOf_words,
    GcmSiv.Words32.ofBytes_bytesAt, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]

theorem hkeyMem_acc (m : Mem) (W : Addr) : Spec.Gcm.blockAt (VG.Proof.AesGcmSiv.Arm.hkeyMem m W) (W + BitVec.ofNat 64 80) = 0 := by
  rw [VG.Proof.AesGcmSiv.Arm.hkeyMem, Proof.Cmac.zero4, Spec.Gcm.blockAt, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_zero]
  decide

/-- `hkey`: GHASH's key at `W + 64` and its accumulator zeroed at `W + 80`. -/
theorem hkey_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) :
    ∃ t' : State, runBlock isa hkey t = some t' ∧ t'.mem = VG.Proof.AesGcmSiv.Arm.hkeyMem t.mem (State.addr p.W) ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r0, .r1, .r2, .r3, .r12, .lr] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₀ := E.perm.wR (show 16 + 4 ≤ 3760 by decide)
  have r₁ := E.perm.wR (show 20 + 4 ≤ 3760 by decide)
  have r₂ := E.perm.wR (show 24 + 4 ≤ 3760 by decide)
  have r₃ := E.perm.wR (show 28 + 4 ≤ 3760 by decide)
  have w₀ := E.perm.wW (show 64 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 68 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 72 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 76 + 4 ≤ 3760 by decide)
  have w₄ := E.perm.wW (show 80 + 4 ≤ 3760 by decide)
  have w₅ := E.perm.wW (show 84 + 4 ≤ 3760 by decide)
  have w₆ := E.perm.wW (show 88 + 4 ≤ 3760 by decide)
  have w₇ := E.perm.wW (show 92 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [hkey, Impl.AesGcm.Arm.zero16]; srun [E.r11, L.wA, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, w₄,
    w₅, w₆, w₇], ?_, by others_tac, by rfl, by rfl, by rfl⟩
  simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, VG.Proof.AesGcmSiv.Arm.hkeyMem, Proof.Cmac.zero4,
    Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd]
  rfl

/-! ## `keys` -/

/-- What `keys` writes: the keys, GHASH's key and accumulator, the blocks
the calls use, the encryption key's schedule, the working spaces and the
stack below `SP`. -/
abbrev keyR (W : Addr) (SP : BitVec 32) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 112⟩, ⟨W + BitVec.ofNat 64 176, 16⟩, ⟨W + BitVec.ofNat 64 192, 3568⟩, below SP]

/-- What `keys` leaves, from `σ`. -/
structure KeysPost (p : VG.Proof.AesGcmSiv.Arm.Prm) (σ t : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t
  frame : Frame (VG.Proof.AesGcmSiv.Arm.keyR (State.addr p.W) p.SP) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (State.addr p.K) p.R) (Spec.GcmSiv.keyLen p.R)
    (bytesAt σ.mem (State.addr p.N) 12)).1 = bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16
  ciph : Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = Spec.GcmSiv.aes
    (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (State.addr p.K) p.R) (Spec.GcmSiv.keyLen p.R)
      (bytesAt σ.mem (State.addr p.N) 12)).2
  hkey : Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 64) =
    hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 80) = 0

theorem keys_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {σ : State} (E : VG.Proof.AesGcmSiv.Arm.Env p σ) : WP isa VG.Impl.AesGcmSiv.Arm.keys σ (VG.Proof.AesGcmSiv.Arm.KeysPost p σ) := by
  have hR := L.rounds
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.derive_ok L E) fun t₂ I => ?_)
  have k0 : (⟨State.addr p.W + BitVec.ofNat 64 16, 112⟩ : Region) ∈ VG.Proof.AesGcmSiv.Arm.keyR (State.addr p.W) p.SP := List.mem_cons_self
  have k1 : (⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩ : Region) ∈ VG.Proof.AesGcmSiv.Arm.keyR (State.addr p.W) p.SP :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have k2 : (⟨State.addr p.W + BitVec.ofNat 64 192, 3568⟩ : Region) ∈ VG.Proof.AesGcmSiv.Arm.keyR (State.addr p.W) p.SP :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have k3 : below p.SP ∈ VG.Proof.AesGcmSiv.Arm.keyR (State.addr p.W) p.SP := by simp
  have f₂ : Frame (VG.Proof.AesGcmSiv.Arm.keyR (State.addr p.W) p.SP) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k1, fun _ h => h⟩
    · exact ⟨_, k2, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k3, fun _ h => h⟩
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.expand_ok L I.env) fun t₃ X => ?_)
  obtain ⟨t₄, run₄, hm₄, ho₄, sp₄, rd₄, wr₄⟩ := VG.Proof.AesGcmSiv.Arm.hkey_ok L X.env
  have dK : ∀ {d k : Nat}, d + k ≤ 64 → 16 ≤ d → ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 192, 240⟩ : Region),
      ⟨State.addr p.W + BitVec.ofNat 64 1712, 512⟩],
      (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have f₃ : Frame (VG.Proof.AesGcmSiv.Arm.keyR (State.addr p.W) p.SP) t₂.mem t₃.mem := X.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, k2, Offset.sub _ (by decide) (by decide)⟩
  have f₄ : Frame (VG.Proof.AesGcmSiv.Arm.keyR (State.addr p.W) p.SP) t₃.mem t₄.mem := by
    rw [hm₄]; exact (VG.Proof.AesGcmSiv.Arm.hkeyMem_frame _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
  have dH : ∀ {d k : Nat}, d + k ≤ 64 → ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl h) (by omega) (by decide)
  have dH' : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 192, 240⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have keys := I.keys L
  have a₃ : bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 16) 16 =
      bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.Arm.bytesAt_frame X.frame (dK (by decide) (by decide)) (by decide)
  have a₄ : bytesAt t₄.mem (State.addr p.W + BitVec.ofNat 64 16) 16 =
      bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 16) 16 := by
    rw [hm₄]; exact Proof.AesGcm.Arm.bytesAt_frame (VG.Proof.AesGcmSiv.Arm.hkeyMem_frame _ _) (dH (by decide)) (by decide)
  refine WP.of_runBlock ⟨t₄, run₄, X.env.of_others ho₄ sp₄ rd₄ wr₄, (f₂.trans f₃).trans f₄, ?_, ?_, ?_, ?_⟩
  · rw [keys, a₄, a₃]
  · have hk := keys
    rw [Prod.ext_iff] at hk
    rw [hk.2, ← X.ciph]
    unfold Spec.GcmSiv.ctxCiph
    rw [hm₄, Proof.AesGcm.Arm.bytesAt_frame (VG.Proof.AesGcmSiv.Arm.hkeyMem_frame _ _) (fun r hr =>
      (dH' r hr).sub_left (Region.sub_prefix L.rounds_le)) (by omega)]
  · rw [hm₄, VG.Proof.AesGcmSiv.Arm.hkeyMem_key, ← hm₄, a₄]
  · rw [hm₄]; exact VG.Proof.AesGcmSiv.Arm.hkeyMem_acc _ _

end VG.Proof.AesGcmSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.Arm.Absorb`. -/
section

/-!
# AES-GCM-SIV on ARMv7: POLYVAL (`chunk`)

Untrusted: everything here is checked by Lean. POLYVAL is GHASH with the
key `H · x` on the same bits (`Proof.GcmSiv.Polyval`): `revLoop` copies up
to 64 blocks to `W + 432` with the bytes of each reversed, so that GHASH
reads each copy as POLYVAL reads the original (`revLoop_ok`), and `vg_ghash`
absorbs them (`chunk_ok`); chunks follow each other until fewer than 16
bytes are left (`chunks_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (GhCall GhPost gh_call below add_ofNat_zero add_ofNat_assoc add32_ofNat_assoc covers_cons
  covers_nil covers_append' covers_off covers_prefix eval_ne' eval_eq' z_cmp ofNat_sub32 ofNat_add32 toNat32
  mem_store gpr_store sp_store rd_store wr_store z_store mem_subFlags z_subFlags gpr_subFlags sp_subFlags
  rd_subFlags wr_subFlags)

/-! ## Reversing blocks -/

/-- The body of `revLoop`. -/
abbrev revBody : List Instr :=
  [.ldr .r0 .r4 12, .ldr .r1 .r4 8, .ldr .r12 .r4 4, .ldr .lr .r4 0, .rev .r0 .r0, .rev .r1 .r1,
    .rev .r12 .r12, .rev .lr .lr, .str .r0 .r2 0, .str .r1 .r2 4, .str .r12 .r2 8, .str .lr .r2 12,
    Impl.AesGcm.Arm.addI .r4 .r4 16, Impl.AesGcm.Arm.addI .r2 .r2 16, .subs .r3 .r3 (Impl.AesGcm.Arm.imm 1)]

/-- The registers `revLoop` writes. -/
abbrev revRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r12, .lr]

/-- What one step of `revLoop` stores: the words of the block at `S` in the
other order, each reversed. -/
def revMem (m : Mem) (S P : Addr) : Mem :=
  Proof.Cmac.store4 m P (rev (m.readW (S + BitVec.ofNat 64 12) 32)) (rev (m.readW (S + BitVec.ofNat 64 8) 32))
    (rev (m.readW (S + BitVec.ofNat 64 4) 32)) (rev (m.readW S 32))

theorem revStep_ok {t : State} {S P : BitVec 32} {j : Nat} (hj : j + 1 < 2 ^ 32)
    (hS : ∀ o, o < 16 → State.addr (S + BitVec.ofNat 32 o) = State.addr S + BitVec.ofNat 64 o)
    (hP : ∀ o, o < 16 → State.addr (P + BitVec.ofNat 32 o) = State.addr P + BitVec.ofNat 64 o)
    (h4 : t.gpr .r4 = S) (h2 : t.gpr .r2 = P) (h3 : t.gpr .r3 = BitVec.ofNat 32 (j + 1))
    (hr : Covers [⟨State.addr S, 16⟩] (t.rd ++ t.wr)) (hw : Covers [⟨State.addr P, 16⟩] t.wr) :
    ∃ t' : State, runBlock isa VG.Proof.AesGcmSiv.Arm.revBody t = some t' ∧ t'.mem = VG.Proof.AesGcmSiv.Arm.revMem t.mem (State.addr S) (State.addr P) ∧
      t'.gpr .r4 = S + BitVec.ofNat 32 16 ∧ t'.gpr .r2 = P + BitVec.ofNat 32 16 ∧
      t'.gpr .r3 = BitVec.ofNat 32 j ∧ t'.z = decide (j = 0) ∧ VG.Proof.AesGcmSiv.Arm.Others VG.Proof.AesGcmSiv.Arm.revRegs t t' ∧ t'.sp = t.sp ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₀ : InRegions (t.rd ++ t.wr) (State.addr S) 4 := by simpa using in_off hr (d := 0) (n := 4) (by decide) (by decide)
  have r₄ := in_off hr (d := 4) (n := 4) (by decide) (by decide)
  have r₈ := in_off hr (d := 8) (n := 4) (by decide) (by decide)
  have r₁₂ := in_off hr (d := 12) (n := 4) (by decide) (by decide)
  have w₀ : InRegions t.wr (State.addr P) 4 := by simpa using in_off hw (d := 0) (n := 4) (by decide) (by decide)
  have w₄ := in_off hw (d := 4) (n := 4) (by decide) (by decide)
  have w₈ := in_off hw (d := 8) (n := 4) (by decide) (by decide)
  have w₁₂ := in_off hw (d := 12) (n := 4) (by decide) (by decide)
  refine ⟨_, by srun [h4, h2, h3, add_ofNat_zero, hS, hP, r₀, r₄, r₈, r₁₂, w₀, w₄, w₈, w₁₂], ?_⟩
  refine ⟨?_, by simp [gpr_setReg, h4], by simp [gpr_setReg, h2], ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, mem_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, VG.Proof.AesGcmSiv.Arm.revMem,
      Proof.Cmac.store4]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h3]
    rw [ofNat_sub32 (by omega) (by omega)]; rfl
  · simp only [z_setReg, z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h3]
    rw [z_cmp (by omega) (by decide)]
    congr 1; apply propext; omega
where
  in_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k) (hk : k < 2 ^ 64) :
      InRegions rs (p + BitVec.ofNat 64 d) n := Proof.AesGcm.Arm.in_off h hd hk

theorem blocksAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Gcm.blocksAt m p (j + 1) = Spec.Gcm.blocksAt m p j ++ [Spec.Gcm.blockAt m (p + BitVec.ofNat 64 (16 * j))] := by
  simp [Spec.Gcm.blocksAt, List.range_succ]

/-- The block `revMem` stores, as GHASH reads it: POLYVAL's field element of
the source. -/
theorem revMem_block (m : Mem) (S P : Addr) :
    Spec.Gcm.blockAt (VG.Proof.AesGcmSiv.Arm.revMem m S P) P = Spec.GcmSiv.ofBytes (bytesAt m S 16) := by
  rw [VG.Proof.AesGcmSiv.Arm.revMem, VG.Proof.AesGcmSiv.Arm.blockAt_store4, rev_rev, rev_rev, rev_rev, rev_rev, Proof.Gcm.Arm.w4, GcmSiv.Words32.ofBytes_bytesAt]

/-- POLYVAL's field elements of the `k` blocks at `Q`. -/
abbrev elemsAt (m : Mem) (Q : Addr) (k : Nat) : List Spec.GcmSiv.Elem :=
  (List.range k).map fun i => Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * i)) 16)

/-- What a chunk may read: `k` bytes at `Q` apart from what it writes. -/
structure Src (p : VG.Proof.AesGcmSiv.Arm.Prm) (s : State) (Q : BitVec 32) (k : Nat) : Prop where
  rd : Covers [⟨State.addr Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 32
  y : (⟨State.addr Q, k⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 80, 16⟩
  rev : (⟨State.addr Q, k⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 432, 1280⟩
  stk : (below p.SP).Disjoint ⟨State.addr Q, k⟩

namespace Src

variable {p : VG.Proof.AesGcmSiv.Arm.Prm} {s : State} {Q : BitVec 32} {n : Nat} (h : VG.Proof.AesGcmSiv.Arm.Src p s Q n)
include h

theorem lt : n < 2 ^ 64 := by have := h.wrap; omega

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcmSiv.Arm.Src p s' Q n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem addr {j : Nat} (hj : j < n) : State.addr (Q + BitVec.ofNat 32 j) = State.addr Q + BitVec.ofNat 64 j :=
  addr_add (by have := h.wrap; omega)

theorem toNat_add {j : Nat} (hj : j < n) : (Q + BitVec.ofNat 32 j).toNat = Q.toNat + j := by
  have := h.wrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcmSiv.Arm.Src p s Q k where
  rd := covers_prefix h.rd hk
  wrap := by have := h.wrap; omega
  y := h.y.sub_left (Region.sub_prefix hk)
  rev := h.rev.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`, for `a < n`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) (ha : a < n) : VG.Proof.AesGcmSiv.Arm.Src p s (Q + BitVec.ofNat 32 a) k := by
  have e := h.addr ha
  have hs : Region.Sub ⟨State.addr Q + BitVec.ofNat 64 a, k⟩ ⟨State.addr Q, n⟩ := Offset.sub_base _ hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact covers_off h.rd hk h.lt
  · rw [h.toNat_add ha]; have := h.wrap; omega
  · rw [e]; exact h.y.sub_left hs
  · rw [e]; exact h.rev.sub_left hs
  · rw [e]; exact h.stk.sub_right hs

end Src

/-- What `revLoop` leaves after `j` blocks, from `t₀`. -/
structure RInv (p : VG.Proof.AesGcmSiv.Arm.Prm) (Q : BitVec 32) (c j : Nat) (t₀ t : State) : Prop where
  r4 : t.gpr .r4 = Q + BitVec.ofNat 32 (16 * j)
  r2 : t.gpr .r2 = p.W + BitVec.ofNat 32 (432 + 16 * j)
  r3 : t.gpr .r3 = BitVec.ofNat 32 (c - j)
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 432, 16 * c⟩] t₀.mem t.mem
  out : Spec.Gcm.blocksAt t.mem (State.addr p.W + BitVec.ofNat 64 432) j = VG.Proof.AesGcmSiv.Arm.elemsAt t₀.mem (State.addr Q) j
  others : VG.Proof.AesGcmSiv.Arm.Others VG.Proof.AesGcmSiv.Arm.revRegs t₀ t
  sp : t.sp = t₀.sp
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr

/-- `revLoop`: `c` blocks at `Q` copied to `W + 432`, each reversed, so that
GHASH reads POLYVAL's field elements of them. -/
theorem revLoop_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t₀ : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t₀) {Q : BitVec 32} {c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 64) (hQ : VG.Proof.AesGcmSiv.Arm.Src p t₀ Q (16 * c)) (h4 : t₀.gpr .r4 = Q)
    (h2 : t₀.gpr .r2 = p.W + BitVec.ofNat 32 432) (h3 : t₀.gpr .r3 = BitVec.ofNat 32 c) :
    WP isa revLoop t₀ fun t => Frame [⟨State.addr p.W + BitVec.ofNat 64 432, 16 * c⟩] t₀.mem t.mem ∧
      Spec.Gcm.blocksAt t.mem (State.addr p.W + BitVec.ofNat 64 432) c = VG.Proof.AesGcmSiv.Arm.elemsAt t₀.mem (State.addr Q) c ∧
      t.gpr .r4 = Q + BitVec.ofNat 32 (16 * c) ∧
      VG.Proof.AesGcmSiv.Arm.Others VG.Proof.AesGcmSiv.Arm.revRegs t₀ t ∧ t.sp = t₀.sp ∧ t.rd = t₀.rd ∧ t.wr = t₀.wr := by
  have hw := L.ww
  have I₀ : VG.Proof.AesGcmSiv.Arm.RInv p Q c 0 t₀ t₀ := ⟨by rw [h4, Nat.mul_zero, add_ofNat_zero], by rw [h2],
    by rw [h3, Nat.sub_zero], Frame.refl _ _, by simp only [Spec.Gcm.blocksAt, VG.Proof.AesGcmSiv.Arm.elemsAt, List.range_zero, List.map_nil],
    fun _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcmSiv.Arm.revBody) (c := .ne)
    (fun (m : Nat) (t : State) => ∃ j, m = c - j ∧ j < c ∧ VG.Proof.AesGcmSiv.Arm.RInv p Q c j t₀ t) ?_ (c - 0) t₀ ⟨0, rfl, hc1, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  have eS : State.addr (Q + BitVec.ofNat 32 (16 * j)) = State.addr Q + BitVec.ofNat 64 (16 * j) :=
    hQ.addr (by omega)
  have hS : ∀ o, o < 16 → State.addr (Q + BitVec.ofNat 32 (16 * j) + BitVec.ofNat 32 o) =
      State.addr (Q + BitVec.ofNat 32 (16 * j)) + BitVec.ofNat 64 o := fun o ho => by
    rw [add32_ofNat_assoc, hQ.addr (by omega), eS, add_ofNat_assoc]
  have hP : ∀ o, o < 16 → State.addr (p.W + BitVec.ofNat 32 (432 + 16 * j) + BitVec.ofNat 32 o) =
      State.addr (p.W + BitVec.ofNat 32 (432 + 16 * j)) + BitVec.ofNat 64 o := fun o ho => by
    rw [add32_ofNat_assoc, L.wA (by omega), L.wA (by omega), add_ofNat_assoc]
  have hr : Covers [⟨State.addr (Q + BitVec.ofNat 32 (16 * j)), 16⟩] (t.rd ++ t.wr) := by
    rw [I.rd, I.wr, eS]; exact covers_off hQ.rd (by omega) hQ.lt
  have hwr : Covers [⟨State.addr (p.W + BitVec.ofNat 32 (432 + 16 * j)), 16⟩] t.wr := by
    rw [I.wr, L.wA (by omega)]; exact E.perm.wC (by omega)
  obtain ⟨t', run', hm', r4', r2', r3', z', ho', sp', rd', wr'⟩ :=
    VG.Proof.AesGcmSiv.Arm.revStep_ok (j := c - j - 1) (by omega) hS hP I.r4 I.r2 (by rw [I.r3]; congr 1; omega) hr hwr
  refine WP.of_runBlock ⟨t', run', ?_⟩
  rw [eS, L.wA (by omega)] at hm'
  -- The source is outside the copies.
  have src : bytesAt t.mem (State.addr Q + BitVec.ofNat 64 (16 * j)) 16 =
      bytesAt t₀.mem (State.addr Q + BitVec.ofNat 64 (16 * j)) 16 :=
    Proof.AesGcm.Arm.bytesAt_frame I.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hQ.rev.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub _ (by omega) (by omega)))
      (by decide)
  have fr : Frame [⟨State.addr p.W + BitVec.ofNat 64 (432 + 16 * j), 16⟩] t.mem t'.mem := by
    rw [hm', VG.Proof.AesGcmSiv.Arm.revMem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have I' : VG.Proof.AesGcmSiv.Arm.RInv p Q c (j + 1) t₀ t' := by
    refine ⟨by rw [r4', add32_ofNat_assoc, Nat.mul_succ], by rw [r2', add32_ofNat_assoc, Nat.mul_succ, Nat.add_assoc],
      by rw [r3', Nat.sub_sub], ?_, ?_, fun r hr => by rw [ho' r hr, I.others r hr],
      by rw [sp', I.sp], by rw [rd', I.rd], by rw [wr', I.wr]⟩
    · exact I.frame.trans (fr.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩)
    · rw [VG.Proof.AesGcmSiv.Arm.blocksAt_succ, Proof.AesGcm.Arm.blocksAt_frame fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by omega), I.out]
      simp only [VG.Proof.AesGcmSiv.Arm.elemsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [add_ofNat_assoc, hm', VG.Proof.AesGcmSiv.Arm.revMem_block, src]
  have ev := eval_ne' z'
  by_cases he : j + 1 = c
  · left
    refine ⟨ev.trans (by simp [show c - j - 1 = 0 by omega]), ?_⟩
    exact ⟨I'.frame, he ▸ I'.out, he ▸ I'.r4, I'.others, I'.sp, I'.rd, I'.wr⟩
  · right
    exact ⟨ev.trans (by simp; omega), c - (j + 1), by omega, j + 1, rfl, by omega, I'⟩


/-! ## A chunk -/

/-- What a chunk writes: GHASH's accumulator, the reversed blocks,
`vg_ghash`'s working space and the stack below `SP`. -/
abbrev absR (W : Addr) (SP : BitVec 32) : List Region :=
  [⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 432, 1280⟩, below SP]

/-- What a chunk leaves, from `t`, after absorbing `k` blocks of the `m`
bytes at `Q`. -/
structure ChunkPost (p : VG.Proof.AesGcmSiv.Arm.Prm) (Q : BitVec 32) (m k : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  r4 : t'.gpr .r4 = Q + BitVec.ofNat 32 (16 * k)
  r5 : t'.gpr .r5 = BitVec.ofNat 32 (m - 16 * k)
  z : t'.z = decide ((m - 16 * k) / 16 = 0)
  frame : Frame (VG.Proof.AesGcmSiv.Arm.absR (State.addr p.W) p.SP) t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (State.addr p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 80)) (VG.Proof.AesGcmSiv.Arm.elemsAt t.mem (State.addr Q) k)

/-- `chunkLen`: the number of blocks of the chunk. -/
theorem chunkLen_ok {t : State} {m : Nat} (hm : m < 2 ^ 32) (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa chunkLen t fun t' => t'.gpr .r6 = BitVec.ofNat 32 (min (m / 16) 64) ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r6] t t' ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, r6₁, z₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa
      [.mov .r6 (.shifted .r5 .lsr 10), .cmp .r6 (Impl.AesGcm.Arm.imm 0)] t = some t₁ ∧
      t₁.gpr .r6 = BitVec.ofNat 32 (m / 1024) ∧ t₁.z = decide (m / 1024 = 0) ∧ VG.Proof.AesGcmSiv.Arm.Others [.r6] t t₁ ∧
      t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h5], ?_, ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
    · simp [gpr_setReg, VG.Proof.AesGcmSiv.Arm.ofNat_lsr32 hm]
    · simp only [z_subFlags, gpr_setReg, ite_true, VG.Proof.AesGcmSiv.Arm.ofNat_lsr32 hm]
      rw [z_cmp (by omega) (by decide)]
      rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (m / 1024 = 0)) (eval_eq' z₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 1024 = 0 := by simpa using ht
    refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_setReg, ite_true, ho₁ .r5 (by decide), h5, VG.Proof.AesGcmSiv.Arm.ofNat_lsr32 hm]
      congr 1; omega
    · simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false]; exact ho₁ r (by simpa using hr)
  · have h0 : m / 1024 ≠ 0 := by simpa using hf
    refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_setReg, ite_true]
      congr 1; omega
    · simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false]; exact ho₁ r (by simpa using hr)

/-- A chunk up to its call: up to 64 blocks reversed at `W + 432`, the
pointer and the count past them, and the arguments of `vg_ghash`. -/
structure ChunkPre (p : VG.Proof.AesGcmSiv.Arm.Prm) (Q : BitVec 32) (m k : Nat) (t t₅ : State) : Prop where
  call : GhCall t₅ (p.W + BitVec.ofNat 32 64) (p.W + BitVec.ofNat 32 80) (p.W + BitVec.ofNat 32 432)
    (p.W + BitVec.ofNat 32 1456) k
  env : VG.Proof.AesGcmSiv.Arm.Env p t₅
  rd : t₅.rd = t.rd
  wr : t₅.wr = t.wr
  r4 : t₅.gpr .r4 = Q + BitVec.ofNat 32 (16 * k)
  r5 : t₅.gpr .r5 = BitVec.ofNat 32 (m - 16 * k)
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 432, 16 * k⟩] t.mem t₅.mem
  out : Spec.Gcm.blocksAt t₅.mem (State.addr p.W + BitVec.ofNat 64 432) k = VG.Proof.AesGcmSiv.Arm.elemsAt t.mem (State.addr Q) k

/-- The pieces of a chunk before its call. -/
theorem chunkPre_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32)
    (h16 : 16 ≤ m) (hQ : VG.Proof.AesGcmSiv.Arm.Src p t Q (16 * (m / 16))) (h4 : t.gpr .r4 = Q) (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa chunkPre t (VG.Proof.AesGcmSiv.Arm.ChunkPre p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.chunkLen_ok hm h5) fun t₁ ⟨r6₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ => ?_)
  obtain ⟨t₂, run₂, r2₂, r3₂, ho₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa
      [Impl.AesGcm.Arm.addI .r2 .r11 revO, .mov .r3 (.reg .r6)] t₁ = some t₂ ∧
      t₂.gpr .r2 = p.W + BitVec.ofNat 32 432 ∧ t₂.gpr .r3 = BitVec.ofNat 32 (min (m / 16) 64) ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r2, .r3] t₁ t₂ ∧ t₂.mem = t₁.mem ∧ t₂.sp = t₁.sp ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    refine ⟨_, by srun [], ?_, ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
    · simp [gpr_setReg, ho₁ .r11 (by decide), E.r11]
    · simp [gpr_setReg, r6₁]
  refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
  have E₂ : VG.Proof.AesGcmSiv.Arm.Env p t₂ := (E.of_others ho₁ sp₁ rd₁ wr₁).of_others ho₂ sp₂ rd₂ wr₂
  have hk1 : 1 ≤ min (m / 16) 64 := by omega
  have hQ₂ : VG.Proof.AesGcmSiv.Arm.Src p t₂ Q (16 * min (m / 16) 64) :=
    (hQ.take (by omega)).of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have h4₂ : t₂.gpr .r4 = Q := by rw [ho₂ _ (by decide), ho₁ _ (by decide), h4]
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.revLoop_ok L E₂ hk1 (by omega) hQ₂ h4₂ r2₂ r3₂)
    fun t₃ ⟨fr₃, out₃, r4₃, ho₃, sp₃, rd₃, wr₃⟩ => ?_)
  have E₃ : VG.Proof.AesGcmSiv.Arm.Env p t₃ := E₂.of_others ho₃ sp₃ rd₃ wr₃
  have r6₃ : t₃.gpr .r6 = BitVec.ofNat 32 (min (m / 16) 64) := by
    rw [ho₃ _ (by decide), ho₂ _ (by decide), r6₁]
  have r5₃ : t₃.gpr .r5 = BitVec.ofNat 32 m := by
    rw [ho₃ _ (by decide), ho₂ _ (by decide), ho₁ _ (by decide), h5]
  have m₂₁ : t₂.mem = t.mem := by rw [m₂, m₁]
  rw [m₂₁] at fr₃ out₃
  refine Proof.AesGcm.Arm.WP.run ⟨_, by simp only [chunkArgs]; srun [], rfl⟩ fun t₄ ht₄ => ?_
  subst ht₄
  refine ⟨⟨?r0, ?r1, ?r2, ?r3, ?r12, ?hsp, ?fH, ?fY, ?fD, ?fS, ?hy, ?hs, ?yd, ?ys, ?ds, ?bh, ?bY, ?bd, ?bs,
      ?reads, ?writes⟩,
    E₃.keep (fun r hr => ?regs) (by rfl) (by rfl) (by rfl), by simp only [rd_setReg]; rw [rd₃, rd₂, rd₁],
    by simp only [wr_setReg]; rw [wr₃, wr₂, wr₁], ?_, ?_, by simp only [mem_setReg]; exact fr₃,
    by simp only [mem_setReg]; exact out₃⟩
  case regs =>
    simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  case r0 => simp [gpr_setReg, E₃.r11]
  case r1 => simp [gpr_setReg, E₃.r11]
  case r2 => simp [gpr_setReg, E₃.r11]
  case r3 => simp [gpr_setReg, r6₃]
  case r12 => simp [gpr_setReg, E₃.r11]
  case hsp => simp only [sp_setReg]; rw [E₃.sp]; exact L.sp8
  case fH => rw [L.wN (by decide)]; omega
  case fY => rw [L.wN (by decide)]; omega
  case fD => rw [L.wN (by decide)]; omega
  case fS => rw [L.wN (by decide)]; omega
  case hy => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case hs => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case yd => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  case ys => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case ds => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by omega)) (by omega) (by decide)
  case bh => simp only [sp_setReg]; rw [E₃.sp, L.wA (by decide)]; exact L.bw' (by decide)
  case bY => simp only [sp_setReg]; rw [E₃.sp, L.wA (by decide)]; exact L.bw' (by decide)
  case bd => simp only [sp_setReg]; rw [E₃.sp, L.wA (by decide)]; exact L.bw' (by omega)
  case bs => simp only [sp_setReg]; rw [E₃.sp, L.wA (by decide)]; exact L.bw' (by decide)
  case reads =>
    simp only [rd_setReg, wr_setReg]
    rw [L.wA (by decide), L.wA (by decide)]
    exact covers_append' (covers_cons (E₃.perm.wCR (by decide)) covers_nil)
      (covers_cons (E₃.perm.wCR (by omega)) covers_nil)
  case writes =>
    simp only [wr_setReg]
    rw [L.wA (by decide), L.wA (by decide)]
    exact covers_cons (E₃.perm.wC (by decide)) (covers_cons (E₃.perm.wC (by decide)) covers_nil)
  · simp [gpr_setReg, r4₃]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, r5₃, r6₃, VG.Proof.AesGcmSiv.Arm.ofNat_lsl32]
    rw [ofNat_sub32 (by omega) hm]; congr 2; omega


/-- `wholeLeft`: `Z` set iff fewer than 16 of the `r` bytes are left. -/
theorem wholeLeft_ok {t : State} {r : Nat} (hr : r < 2 ^ 32) (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    ∃ t' : State, runBlock isa wholeLeft t = some t' ∧ t'.z = decide (r / 16 = 0) ∧ VG.Proof.AesGcmSiv.Arm.Others [.r12] t t' ∧
      t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by simp only [wholeLeft]; srun [h5], ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
  simp only [z_subFlags, gpr_setReg, ite_true, VG.Proof.AesGcmSiv.Arm.ofNat_lsr32 hr]
  rw [z_cmp (by omega) (by decide)]
  rfl

theorem chunk_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ : VG.Proof.AesGcmSiv.Arm.Src p t Q (16 * (m / 16))) (h4 : t.gpr .r4 = Q)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa chunk t (VG.Proof.AesGcmSiv.Arm.ChunkPost p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  have hk : 16 * min (m / 16) 64 ≤ 1024 := by omega
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.chunkPre_ok L E hm h16 hQ h4 h5) fun t₅ Pr => ?_)
  refine WP.seq (WP.mono (gh_call Pr.call) fun t₆ P => ?_)
  have E₆ : VG.Proof.AesGcmSiv.Arm.Env p t₆ := Pr.env.of_saved P.saved P.sp P.rd P.wr
  have r5₆ : t₆.gpr .r5 = BitVec.ofNat 32 (m - 16 * min (m / 16) 64) := by
    rw [P.saved _ (by decide) (by decide), Pr.r5]
  have fr := P.frame
  have out₆ := P.out
  simp only [L.wA (show 64 < 3760 by decide), L.wA (show 80 < 3760 by decide),
    L.wA (show 432 < 3760 by decide), L.wA (show 1456 < 3760 by decide), Pr.env.sp] at fr out₆
  have dH : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 432, 16 * min (m / 16) 64⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  have dY : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 432, 16 * min (m / 16) 64⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 80, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  rw [Proof.AesGcm.Arm.blockAt_frame Pr.frame dH, Proof.AesGcm.Arm.blockAt_frame Pr.frame dY, Pr.out] at out₆
  obtain ⟨t₇, run₇, z₇, ho₇, m₇, sp₇, rd₇, wr₇⟩ := VG.Proof.AesGcmSiv.Arm.wholeLeft_ok (by omega) r5₆
  refine WP.of_runBlock ⟨t₇, run₇, E₆.of_others ho₇ sp₇ rd₇ wr₇, by rw [rd₇, P.rd, Pr.rd],
    by rw [wr₇, P.wr, Pr.wr], ?_, by rw [ho₇ _ (by decide), r5₆], z₇, ?_, by rw [m₇]; exact out₆⟩
  · rw [ho₇ _ (by decide), P.saved _ (by decide) (by decide), Pr.r4]
  · rw [m₇]
    refine (Pr.frame.sub fun r hr => ?_).trans (fr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-! ## Absorbing -/

theorem elemsAt_add (m : Mem) (Q : Addr) (d k : Nat) :
    VG.Proof.AesGcmSiv.Arm.elemsAt m Q (d + k) = VG.Proof.AesGcmSiv.Arm.elemsAt m Q d ++ VG.Proof.AesGcmSiv.Arm.elemsAt m (Q + BitVec.ofNat 64 (16 * d)) k := by
  simp only [VG.Proof.AesGcmSiv.Arm.elemsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, add_ofNat_assoc, Nat.mul_add]

theorem elemsAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr} {k : Nat}
    (hd : ∀ r ∈ rs, (⟨Q, 16 * k⟩ : Region).Disjoint r) (hk : 16 * k ≤ 2 ^ 64) : VG.Proof.AesGcmSiv.Arm.elemsAt m' Q k = VG.Proof.AesGcmSiv.Arm.elemsAt m Q k := by
  unfold VG.Proof.AesGcmSiv.Arm.elemsAt
  rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt, Proof.AesGcm.Arm.bytesAt_frame hf hd hk]

/-- What absorbing writes: what a chunk writes, and the block at `W + 176`. -/
abbrev absorbR (W : Addr) (SP : BitVec 32) : List Region := ⟨W + BitVec.ofNat 64 176, 16⟩ :: VG.Proof.AesGcmSiv.Arm.absR W SP

/-- What absorbing leaves, from `t`, having absorbed the elements `xs` and
written only `rs`. -/
structure Absorbed (p : VG.Proof.AesGcmSiv.Arm.Prm) (rs : List Region) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame rs t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (State.addr p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 80)) xs

/-- What absorbing a string leaves. -/
abbrev AbsPost (p : VG.Proof.AesGcmSiv.Arm.Prm) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop :=
  VG.Proof.AesGcmSiv.Arm.Absorbed p (VG.Proof.AesGcmSiv.Arm.absorbR (State.addr p.W) p.SP) xs t t'

theorem absorbR_H {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) :
    ∀ r ∈ VG.Proof.AesGcmSiv.Arm.absorbR (State.addr p.W) p.SP, (⟨State.addr p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.bw' (by decide)).symm

/-- A buffer apart from `W` and the stack below `SP` misses what absorbing writes. -/
theorem absorbR_buf {p : VG.Proof.AesGcmSiv.Arm.Prm} {P : Addr} {k : Nat} (hd : (⟨P, k⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩)
    (hb : (below p.SP).Disjoint ⟨P, k⟩) : ∀ r ∈ VG.Proof.AesGcmSiv.Arm.absorbR (State.addr p.W) p.SP, (⟨P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hb.symm

theorem absR_sub (W : Addr) (SP : BitVec 32) : ∀ r ∈ VG.Proof.AesGcmSiv.Arm.absR W SP, ∃ r' ∈ VG.Proof.AesGcmSiv.Arm.absorbR W SP, Region.Sub r r' :=
  fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩

theorem Absorbed.trans {p : VG.Proof.AesGcmSiv.Arm.Prm} {rs : List Region} {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (hH : ∀ r ∈ rs, (⟨State.addr p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r)
    (h₁ : VG.Proof.AesGcmSiv.Arm.Absorbed p rs xs t t₁) (h₂ : VG.Proof.AesGcmSiv.Arm.Absorbed p rs ys t₁ t₂) : VG.Proof.AesGcmSiv.Arm.Absorbed p rs (xs ++ ys) t t₂ := by
  refine ⟨h₂.env, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.frame.trans h₂.frame, ?_⟩
  rw [h₂.out, h₁.out, Proof.AesGcm.Arm.blockAt_frame h₁.frame hH, Proof.Gcm.ghashFrom_append]

theorem Absorbed.sub {p : VG.Proof.AesGcmSiv.Arm.Prm} {rs rs' : List Region} {xs : List Spec.GcmSiv.Elem} {t t' : State}
    (h : VG.Proof.AesGcmSiv.Arm.Absorbed p rs xs t t') (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : VG.Proof.AesGcmSiv.Arm.Absorbed p rs' xs t t' :=
  ⟨h.env, h.rd, h.wr, h.frame.sub hs, h.out⟩

theorem AbsPost.trans {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h₁ : VG.Proof.AesGcmSiv.Arm.AbsPost p xs t t₁) (h₂ : VG.Proof.AesGcmSiv.Arm.AbsPost p ys t₁ t₂) : VG.Proof.AesGcmSiv.Arm.AbsPost p (xs ++ ys) t t₂ :=
  Absorbed.trans (VG.Proof.AesGcmSiv.Arm.absorbR_H L) h₁ h₂

theorem Absorbed.of_chunk {p : VG.Proof.AesGcmSiv.Arm.Prm} {Q : BitVec 32} {m k : Nat} {t t' : State}
    (h : VG.Proof.AesGcmSiv.Arm.ChunkPost p Q m k t t') : VG.Proof.AesGcmSiv.Arm.Absorbed p (VG.Proof.AesGcmSiv.Arm.absR (State.addr p.W) p.SP) (VG.Proof.AesGcmSiv.Arm.elemsAt t.mem (State.addr Q) k) t t' :=
  ⟨h.env, h.rd, h.wr, h.frame, h.out⟩

theorem Absorbed.of_eq {p : VG.Proof.AesGcmSiv.Arm.Prm} {rs : List Region} {xs : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h : VG.Proof.AesGcmSiv.Arm.Absorbed p rs xs t₁ t₂) (hm : t₁.mem = t.mem) (hrd : t₁.rd = t.rd) (hwr : t₁.wr = t.wr) :
    VG.Proof.AesGcmSiv.Arm.Absorbed p rs xs t t₂ :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, hm ▸ h.frame, by rw [h.out, hm]⟩

theorem absR_H {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) :
    ∀ r ∈ VG.Proof.AesGcmSiv.Arm.absR (State.addr p.W) p.SP, (⟨State.addr p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r :=
  fun r hr => VG.Proof.AesGcmSiv.Arm.absorbR_H L r (List.mem_cons_of_mem _ hr)

/-- The chunks of the `m` bytes at `Q`, from `σ`, after `d` blocks. -/
structure CInv (p : VG.Proof.AesGcmSiv.Arm.Prm) (σ : State) (Q : BitVec 32) (m d : Nat) (t : State) : Prop where
  abs : VG.Proof.AesGcmSiv.Arm.Absorbed p (VG.Proof.AesGcmSiv.Arm.absR (State.addr p.W) p.SP) (VG.Proof.AesGcmSiv.Arm.elemsAt σ.mem (State.addr Q) d) σ t
  r4 : t.gpr .r4 = Q + BitVec.ofNat 32 (16 * d)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (m - 16 * d)

theorem CInv.src {p : VG.Proof.AesGcmSiv.Arm.Prm} {σ t : State} {Q : BitVec 32} {m d : Nat} (I : VG.Proof.AesGcmSiv.Arm.CInv p σ Q m d t)
    (hQ : VG.Proof.AesGcmSiv.Arm.Src p σ Q (16 * (m / 16))) (hd : d < m / 16) :
    VG.Proof.AesGcmSiv.Arm.Src p t (Q + BitVec.ofNat 32 (16 * d)) (16 * ((m - 16 * d) / 16)) :=
  (hQ.slice (by omega) (by omega)).of_eq I.abs.rd I.abs.wr

theorem CInv.zero {p : VG.Proof.AesGcmSiv.Arm.Prm} {σ : State} (E : VG.Proof.AesGcmSiv.Arm.Env p σ) {Q : BitVec 32} {m : Nat} (h4 : σ.gpr .r4 = Q)
    (h5 : σ.gpr .r5 = BitVec.ofNat 32 m) : VG.Proof.AesGcmSiv.Arm.CInv p σ Q m 0 σ :=
  ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [VG.Proof.AesGcmSiv.Arm.elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
    by rw [h4, Nat.mul_zero, add_ofNat_zero], by rw [h5, Nat.mul_zero, Nat.sub_zero]⟩

/-- A chunk, in the chunks. -/
theorem CInv.step {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {σ t t' : State} {Q : BitVec 32} {m d : Nat}
    (hQ : VG.Proof.AesGcmSiv.Arm.Src p σ Q (16 * (m / 16))) (hd : d < m / 16) (I : VG.Proof.AesGcmSiv.Arm.CInv p σ Q m d t)
    (C : VG.Proof.AesGcmSiv.Arm.ChunkPost p (Q + BitVec.ofNat 32 (16 * d)) (m - 16 * d) (min ((m - 16 * d) / 16) 64) t t') :
    VG.Proof.AesGcmSiv.Arm.CInv p σ Q m (d + min (m / 16 - d) 64) t' ∧
      t'.z = decide (m / 16 - (d + min (m / 16 - d) 64) = 0) := by
  have hk : min ((m - 16 * d) / 16) 64 = min (m / 16 - d) 64 := by congr 1; omega
  rw [hk] at C
  have hs := hQ.slice (a := 16 * d) (k := 16 * min (m / 16 - d) 64) (by omega) (by omega)
  have ea := hQ.addr (j := 16 * d) (by omega)
  have C' := Absorbed.of_chunk C
  rw [VG.Proof.AesGcmSiv.Arm.elemsAt_frame I.abs.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.y
      · exact hs.rev
      · exact hs.stk.symm) (by omega), ea] at C'
  refine ⟨⟨by rw [VG.Proof.AesGcmSiv.Arm.elemsAt_add]; exact Absorbed.trans (VG.Proof.AesGcmSiv.Arm.absR_H L) I.abs C', by rw [C.r4, add32_ofNat_assoc, Nat.mul_add],
    by rw [C.r5]; congr 1; omega⟩, by rw [C.z]; congr 1; apply propext; omega⟩

/-- The whole blocks: chunks until fewer than 16 bytes are left. -/
theorem chunks_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ : VG.Proof.AesGcmSiv.Arm.Src p t Q (16 * (m / 16))) (h4 : t.gpr .r4 = Q)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa (.loop chunk .ne) t fun t' =>
      VG.Proof.AesGcmSiv.Arm.Absorbed p (VG.Proof.AesGcmSiv.Arm.absR (State.addr p.W) p.SP) (VG.Proof.AesGcmSiv.Arm.elemsAt t.mem (State.addr Q) (m / 16)) t t' ∧
      t'.gpr .r4 = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ t'.gpr .r5 = BitVec.ofNat 32 (m % 16) := by
  refine WP.loop (M := isa) (body := chunk) (c := .ne)
    (fun (k : Nat) (t' : State) => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ VG.Proof.AesGcmSiv.Arm.CInv p t Q m d t') ?_
    (m / 16 - 0) t ⟨0, rfl, by omega, CInv.zero E h4 h5⟩
  rintro k t' ⟨d, rfl, hd, I⟩
  refine WP.mono (VG.Proof.AesGcmSiv.Arm.chunk_ok L I.abs.env (by omega) (by omega) (I.src hQ hd) I.r4 I.r5) fun t'' C => ?_
  obtain ⟨I', z⟩ := I.step L hQ hd C
  have ev := eval_ne' z
  by_cases he : d + min (m / 16 - d) 64 = m / 16
  · left
    refine ⟨ev.trans (by simp; omega), he ▸ I'.abs, by rw [I'.r4, he], by rw [I'.r5, he]; congr 1; omega⟩
  · right
    exact ⟨ev.trans (by simp; omega), m / 16 - (d + min (m / 16 - d) 64), by omega, d + min (m / 16 - d) 64, rfl,
      by omega, I'⟩

end VG.Proof.AesGcmSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.Arm.Polyval`. -/
section

/-!
# AES-GCM-SIV on ARMv7: POLYVAL and the tag input (`absorb`, `polyval`)

Untrusted: everything here is checked by Lean. `absorb` absorbs a string
padded with zeros (`absorb_ok`): its whole blocks by chunks, its last bytes
copied over a zero block at `W + 176` and absorbed as one more chunk
(`absTail_ok`); `lensBlock` puts the lengths block there for one more
(`lens_ok`), from the stack arguments `aad_len` and `len`; `tagIn` turns
POLYVAL's result into the tag input (`tagIn_ok`). `polyval_ok`: the tag
input of RFC 8452 §4, with POLYVAL as GHASH with the key `H · x`
(`Proof.GcmSiv.Words.tagInputG`), at `W + 96`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.GcmSiv.Words (hkeyOf tagInputG)
open VG.Proof.AesGcm.Arm (below add_ofNat_zero add_ofNat_assoc add32_ofNat_assoc covers_left covers_prefix
  covers_off eval_eq' z_cmp ofNat_sub32 ofNat_add32 toNat32 mem_store gpr_store sp_store rd_store wr_store z_store
  mem_subFlags z_subFlags gpr_subFlags sp_subFlags rd_subFlags wr_subFlags LoopPre LoopOut copyLoop_ok
  length_bytesAt)

/-! ## The last bytes -/

/-- The last bytes copied over a zeroed block. -/
theorem pad_bytes (m : Mem) (c : Addr) (xs : List Byte) (hx : xs.length < 16) :
    bytesAt (VG.WriteBytes.writeBytes (Proof.Cmac.zero4 m c) c xs) c 16 = xs ++ Spec.GcmSiv.zeros (16 - xs.length) := by
  have hz := Proof.Cmac.zero4_bytes m c
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.Arm.bytesAt_add] at hz
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.Arm.bytesAt_add,
    Proof.AesGcm.Arm.bytesAt_writeBytes_self _ _ _ (by omega),
    Proof.AesGcm.Arm.bytesAt_frame (Proof.AesGcm.Arm.writeBytes_frame' _ rfl) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base c (Nat.le_refl _) (by omega)) (by omega)]
  refine congrArg (xs ++ ·) ?_
  have := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at this
  rw [this, Nat.add_sub_cancel_left]
  simp [Spec.Cmac.zeros, Spec.GcmSiv.zeros, List.drop_replicate]

/-- The block at `W + 176` as a chunk's source. -/
theorem srcB {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {s : State} (P : VG.Proof.AesGcmSiv.Arm.Perm p s) : VG.Proof.AesGcmSiv.Arm.Src p s (p.W + BitVec.ofNat 32 176) 16 := by
  have ww := L.ww
  refine ⟨?_, by rw [L.wN (by decide)]; omega, ?_, ?_, ?_⟩ <;> rw [L.wA (by decide)]
  · exact P.wCR (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.bw' (by decide)

/-- One chunk of the 16 bytes at `W + 176`: their field element absorbed. -/
theorem chunkB_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t)
    (h4 : t.gpr .r4 = p.W + BitVec.ofNat 32 176) (h5 : t.gpr .r5 = BitVec.ofNat 32 16) :
    WP isa chunk t (VG.Proof.AesGcmSiv.Arm.Absorbed p (VG.Proof.AesGcmSiv.Arm.absR (State.addr p.W) p.SP)
      [Spec.GcmSiv.ofBytes (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 176) 16)] t) :=
  WP.mono (VG.Proof.AesGcmSiv.Arm.chunk_ok L E (m := 16) (by decide) (by decide) (VG.Proof.AesGcmSiv.Arm.srcB L E.perm) h4 h5) fun t' C => by
    have A := Absorbed.of_chunk C
    simpa [VG.Proof.AesGcmSiv.Arm.elemsAt, L.wA (show 176 < 3760 by decide)] using A

/-- What `absTailPre` leaves: the last bytes, padded, at `W + 176`, as the
bytes to absorb. -/
structure TailPre (p : VG.Proof.AesGcmSiv.Arm.Prm) (P : Addr) (r : Nat) (t t₃ : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t₃
  rd : t₃.rd = t.rd
  wr : t₃.wr = t.wr
  r4 : t₃.gpr .r4 = p.W + BitVec.ofNat 32 176
  r5 : t₃.gpr .r5 = BitVec.ofNat 32 16
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩] t.mem t₃.mem
  bytes : bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 176) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r)

/-- `absTailPre`: the last `r` (1 to 15) bytes at `P`, padded with zeros. -/
theorem absTailPre_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) {P : BitVec 32} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨State.addr P, r⟩] (t.rd ++ t.wr)) (hf : P.toNat + r ≤ 2 ^ 32)
    (hd : (⟨State.addr P, r⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩) (h4 : t.gpr .r4 = P)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa absTailPre t (VG.Proof.AesGcmSiv.Arm.TailPre p (State.addr P) r t) := by
  have hw := L.ww
  have w₀ := E.perm.wW (show 176 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 180 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 184 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 188 + 4 ≤ 3760 by decide)
  -- The block zeroed, and the copy's arguments.
  obtain ⟨t₁, run₁, hm₁, r1₁, r2₁, r3₁, ho₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State,
      runBlock isa (Impl.AesGcm.Arm.zero16 bO ++ ([.mov .r1 (.reg .r4), Impl.AesGcm.Arm.addI .r2 .r11 bO,
        .mov .r3 (.reg .r5)] : List Instr)) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero4 t.mem (State.addr p.W + BitVec.ofNat 64 176) ∧ t₁.gpr .r1 = P ∧
      t₁.gpr .r2 = p.W + BitVec.ofNat 32 176 ∧ t₁.gpr .r3 = BitVec.ofNat 32 r ∧ VG.Proof.AesGcmSiv.Arm.Others [.r0, .r1, .r2, .r3] t t₁ ∧
      t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [Impl.AesGcm.Arm.zero16]; srun [E.r11, L.wA, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_,
      by others_tac, by rfl, by rfl, by rfl⟩
    · simp only [mem_setReg, mem_store, Proof.Cmac.zero4, Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd]; rfl
    · simp [gpr_setReg, h4]
    · simp [gpr_setReg, E.r11]
    · simp [gpr_setReg, h5]
  unfold absTailPre
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesGcmSiv.Arm.Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  have dB : (⟨State.addr P, r⟩ : Region).Disjoint ⟨State.addr (p.W + BitVec.ofNat 32 176), r⟩ := by
    rw [L.wA (by decide)]
    exact (hd.sub_right (Lay.wSub (show 176 + 16 ≤ 3760 by decide))).sub_right (Region.sub_prefix (by omega))
  have lp : LoopPre t₁ P (p.W + BitVec.ofNat 32 176) r :=
    ⟨r1₁, r2₁, r3₁, by omega, by omega, hf, by rw [L.wN (by decide)]; omega, by rw [rd₁, wr₁]; exact hc,
      by rw [L.wA (by decide)]; exact covers_prefix (E₁.perm.wC (show 176 + 16 ≤ 3760 by decide)) (by omega), dB⟩
  refine WP.seq (WP.mono (copyLoop_ok t₁ lp) fun t₂ ⟨hm₂, O⟩ => ?_)
  have E₂ : VG.Proof.AesGcmSiv.Arm.Env p t₂ := E₁.keep (fun q hq => O.other q (by
    simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide)) O.sp O.rd O.wr
  rw [L.wA (by decide)] at hm₂
  -- The data is outside the zeroed block.
  have hd₁ : bytesAt t₁.mem (State.addr P) r = bytesAt t.mem (State.addr P) r := by
    rw [hm₁]
    exact Proof.AesGcm.Arm.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by decide)))
      (by omega)
  have hb₂ : bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 16 =
      bytesAt t.mem (State.addr P) r ++ Spec.GcmSiv.zeros (16 - r) := by
    have hl := length_bytesAt t.mem (State.addr P) r
    rw [hm₂, hd₁, hm₁, VG.Proof.AesGcmSiv.Arm.pad_bytes _ _ _ (by omega), hl]
  have f₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩] t.mem t₂.mem := by
    rw [hm₂, hm₁]
    exact (Proof.Cmac.frame_store4 _ _ _ _ _).trans
      ((Proof.AesGcm.Arm.writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun t₃ ht₃ => ?_
  subst ht₃
  exact ⟨E₂.keep (fun q hq => by
      simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    by simp only [rd_setReg]; rw [O.rd, rd₁], by simp only [wr_setReg]; rw [O.wr, wr₁],
    by simp [gpr_setReg, E₂.r11], by simp [gpr_setReg],
    by simp only [mem_setReg]; exact f₂, by simp only [mem_setReg]; exact hb₂⟩

/-- `absTail`: the last `r` (1 to 15) bytes at `P`, padded with zeros, absorbed. -/
theorem absTail_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) {P : BitVec 32} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨State.addr P, r⟩] (t.rd ++ t.wr)) (hf : P.toNat + r ≤ 2 ^ 32)
    (hd : (⟨State.addr P, r⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩) (h4 : t.gpr .r4 = P)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa absTail t
      (VG.Proof.AesGcmSiv.Arm.AbsPost p [Spec.GcmSiv.ofBytes (bytesAt t.mem (State.addr P) r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.absTailPre_ok L E hr1 hr hc hf hd h4 h5) fun t₃ T => ?_)
  refine WP.mono (VG.Proof.AesGcmSiv.Arm.chunkB_ok L T.env T.r4 T.r5) fun t₄ C => ?_
  rw [T.bytes] at C
  have dHY : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩ : Region)], ∀ d, d + 16 ≤ 176 →
      (⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun q hq d hd => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega) (by decide)
  refine ⟨C.env, by rw [C.rd, T.rd], by rw [C.wr, T.wr],
    (T.frame.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  rw [C.out, Proof.AesGcm.Arm.blockAt_frame T.frame (fun q hq => dHY q hq 64 (by decide)),
    Proof.AesGcm.Arm.blockAt_frame T.frame (fun q hq => dHY q hq 80 (by decide))]


/-! ## Absorbing a string -/

/-- The field elements of `n` bytes at `Q`, padded. -/
theorem elems_pad16_bytesAt (m : Mem) (Q : Addr) (n : Nat) :
    Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m Q n)) = VG.Proof.AesGcmSiv.Arm.elemsAt m Q (n / 16) ++
      if n % 16 = 0 then [] else
        [Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++
          Spec.GcmSiv.zeros (16 - n % 16))] := by
  have hs := Proof.AesGcm.Arm.bytesAt_add m Q (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega] at hs
  have hl := length_bytesAt m Q (16 * (n / 16))
  rw [GcmSiv.elems_pad16, length_bytesAt, hs, List.take_left' hl, List.drop_left' hl, GcmSiv.elems_bytesAt]

/-- The whole blocks of `absorb`, once `Z` says whether there are any. -/
theorem absMid_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (hQ : VG.Proof.AesGcmSiv.Arm.Src p t Q m) (h4 : t.gpr .r4 = Q) (h5 : t.gpr .r5 = BitVec.ofNat 32 m)
    (hz : t.z = decide (m / 16 = 0)) :
    WP isa (.ite .eq (.block []) (.loop chunk .ne)) t fun t₂ =>
      VG.Proof.AesGcmSiv.Arm.Absorbed p (VG.Proof.AesGcmSiv.Arm.absR (State.addr p.W) p.SP) (VG.Proof.AesGcmSiv.Arm.elemsAt t.mem (State.addr Q) (m / 16)) t t₂ ∧
        t₂.gpr .r4 = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ t₂.gpr .r5 = BitVec.ofNat 32 (m % 16) := by
  refine WP.ite (decide (m / 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [h0, VG.Proof.AesGcmSiv.Arm.elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [h4, h0, Nat.mul_zero, add_ofNat_zero], by rw [h5]; congr 1; omega⟩
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact VG.Proof.AesGcmSiv.Arm.chunks_ok L E hm (by omega) (hQ.take (by omega)) h4 h5

theorem absorb_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32)
    (hQ : VG.Proof.AesGcmSiv.Arm.Src p t Q m) (hd : (⟨State.addr Q, m⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩) (h4 : t.gpr .r4 = Q)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa absorb t (VG.Proof.AesGcmSiv.Arm.AbsPost p (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem (State.addr Q) m))) t) := by
  obtain ⟨t₁, run₁, z₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.Arm.wholeLeft_ok hm h5
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesGcmSiv.Arm.Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.absMid_ok L E₁ hm (hQ.of_eq rd₁ wr₁) (by rw [ho₁ _ (by decide), h4])
    (by rw [ho₁ _ (by decide), h5]) z₁) fun t₂ ⟨P₂, r4₂, r5₂⟩ => ?_)
  rw [m₁] at P₂
  have P₂' := P₂.of_eq m₁ rd₁ wr₁
  rw [VG.Proof.AesGcmSiv.Arm.elems_pad16_bytesAt]
  obtain ⟨t₃, run₃, z₃, ho₃, m₃, sp₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa [.cmp .r5 (Impl.AesGcm.Arm.imm 0)] t₂ = some t₃ ∧
      t₃.z = decide (m % 16 = 0) ∧ VG.Proof.AesGcmSiv.Arm.Others [] t₂ t₃ ∧ t₃.mem = t₂.mem ∧ t₃.sp = t₂.sp ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr := by
    refine ⟨_, by srun [r5₂], ?_, fun r _ => by rfl, by rfl, by rfl, by rfl, by rfl⟩
    simp only [z_subFlags]
    rw [z_cmp (by omega) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have P₃ : VG.Proof.AesGcmSiv.Arm.Absorbed p (VG.Proof.AesGcmSiv.Arm.absR (State.addr p.W) p.SP) (VG.Proof.AesGcmSiv.Arm.elemsAt t.mem (State.addr Q) (m / 16)) t t₃ :=
    ⟨P₂'.env.of_others ho₃ sp₃ rd₃ wr₃, rd₃.trans P₂'.rd, wr₃.trans P₂'.wr, m₃ ▸ P₂'.frame, by rw [m₃]; exact P₂'.out⟩
  refine WP.ite (decide (m % 16 = 0)) (eval_eq' z₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil (P₃.sub (VG.Proof.AesGcmSiv.Arm.absR_sub _ _))
  · have h0 : m % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    have hs := hQ.slice (a := 16 * (m / 16)) (k := m % 16) (by omega) (by omega)
    have ea := hQ.addr (j := 16 * (m / 16)) (by omega)
    have dT : (⟨State.addr (Q + BitVec.ofNat 32 (16 * (m / 16))), m % 16⟩ : Region).Disjoint
        ⟨State.addr p.W, 3760⟩ := by
      rw [ea]; exact hd.sub_left (Offset.sub_base _ (by omega))
    refine WP.mono (VG.Proof.AesGcmSiv.Arm.absTail_ok L P₃.env (by omega) (by omega) (by rw [P₃.rd, P₃.wr]; exact hs.rd) hs.wrap dT
      (by rw [ho₃ _ (by simp), r4₂]) (by rw [ho₃ _ (by simp), r5₂])) fun t₄ T => ?_
    have e := Proof.AesGcm.Arm.bytesAt_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact hs.stk.symm) (by omega)
    rw [e, ea] at T
    exact AbsPost.trans L (P₃.sub (VG.Proof.AesGcmSiv.Arm.absR_sub _ _)) T


/-! ## The lengths, and the tag input -/

/-- The stack arguments are apart from what absorbing writes. -/
theorem absorbR_args {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) : ∀ r ∈ VG.Proof.AesGcmSiv.Arm.absorbR (State.addr p.W) p.SP, (VG.Proof.AesGcmSiv.Arm.argR p.SP).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.args_w' (by decide)
  · exact L.args_w' (by decide)
  · exact L.args_w' (by decide)
  · exact L.args_below

/-- `lensBlock` and its chunk: the lengths block absorbed. -/
theorem lens_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) (A : VG.Proof.AesGcmSiv.Arm.Args p t.mem) :
    WP isa lens t (VG.Proof.AesGcmSiv.Arm.AbsPost p
      [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))] t) := by
  have w₀ := E.perm.wW (show 176 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 180 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 184 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 188 + 4 ≤ 3760 by decide)
  have a₀ := E.perm.argR' L (k := 0) (by decide)
  have a₈ := E.perm.argR' L (k := 8) (by decide)
  obtain ⟨t₁, run₁, hm₁, r4₁, r5₁, ho₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa lensBlock t = some t₁ ∧
      t₁.mem = Proof.Cmac.store4 t.mem (State.addr p.W + BitVec.ofNat 64 176) (BitVec.ofNat 32 p.al <<< 3)
        (BitVec.ofNat 32 p.al >>> 29) (BitVec.ofNat 32 p.n <<< 3) (BitVec.ofNat 32 p.n >>> 29) ∧
      t₁.gpr .r4 = p.W + BitVec.ofNat 32 176 ∧ t₁.gpr .r5 = BitVec.ofNat 32 16 ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r0, .r1, .r2, .r4, .r5] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [lensBlock]; srun [E.r11, E.sp, L.wA, a₀, a₈, A.a0, A.a8, w₀, w₁, w₂, w₃], ?_, ?_, ?_,
      by others_tac, by rfl, by rfl, by rfl⟩
    · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, Proof.Cmac.store4,
        add_ofNat_assoc, Nat.reduceAdd]
    · simp [gpr_setReg, E.r11]
    · simp [gpr_setReg]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesGcmSiv.Arm.Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  have f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩] t.mem t₁.mem := by
    rw [hm₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine WP.mono (VG.Proof.AesGcmSiv.Arm.chunkB_ok L E₁ r4₁ r5₁) fun t₂ C => ?_
  have hb : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 176) 16 =
      Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n) := by
    have ea := GcmSiv.Words32.le64_words (BitVec.ofNat 32 p.al)
    have en := GcmSiv.Words32.le64_words (BitVec.ofNat 32 p.n)
    rw [toNat32 L.al_lt] at ea
    rw [toNat32 L.n_lt] at en
    rw [hm₁, Proof.Cmac.bytesAt_store4, ea, en, List.append_assoc]
  rw [hb] at C
  have dHY : ∀ d, d + 16 ≤ 176 → ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega) (by decide)
  refine ⟨C.env, by rw [C.rd, rd₁], by rw [C.wr, wr₁],
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  rw [C.out, Proof.AesGcm.Arm.blockAt_frame f₁ (dHY 64 (by decide)),
    Proof.AesGcm.Arm.blockAt_frame f₁ (dHY 80 (by decide))]

/-- The memory `tagIn` leaves. -/
def tagInMem (m : Mem) (W N : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 96)
    (rev (m.readW (W + BitVec.ofNat 64 92) 32) ^^^ m.readW N 32)
    (rev (m.readW (W + BitVec.ofNat 64 88) 32) ^^^ m.readW (N + BitVec.ofNat 64 4) 32)
    (rev (m.readW (W + BitVec.ofNat 64 84) 32) ^^^ m.readW (N + BitVec.ofNat 64 8) 32)
    ((rev (m.readW (W + BitVec.ofNat 64 80) 32) <<< 1) >>> 1)

theorem tagInMem_bytes (m : Mem) (W N : Addr) :
    bytesAt (VG.Proof.AesGcmSiv.Arm.tagInMem m W N) (W + BitVec.ofNat 64 96) 16 =
      GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.blockAt m (W + BitVec.ofNat 64 80))) (bytesAt m N 12) := by
  have e := GcmSiv.Words32.tagOf_words (rev (m.readW (W + BitVec.ofNat 64 92) 32))
    (rev (m.readW (W + BitVec.ofNat 64 88) 32)) (rev (m.readW (W + BitVec.ofNat 64 84) 32))
    (rev (m.readW (W + BitVec.ofNat 64 80) 32)) (m.readW N 32) (m.readW (N + BitVec.ofNat 64 4) 32)
    (m.readW (N + BitVec.ofNat 64 8) 32)
  rw [VG.Proof.AesGcmSiv.Arm.tagInMem, Proof.Cmac.bytesAt_store4, Proof.Gcm.Arm.blockAt_rev, Proof.Gcm.Arm.w4,
    GcmSiv.Words32.toBytes_append4, show (12 : Nat) = 4 + 4 + 4 from rfl, Proof.Cmac.bytesAt_add,
    Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW]
  simp only [add_ofNat_assoc, Nat.reduceAdd]
  rw [e]

theorem tagInMem_frame (m : Mem) (W N : Addr) : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m (VG.Proof.AesGcmSiv.Arm.tagInMem m W N) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem tagIn_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) :
    ∃ t' : State, runBlock isa tagIn t = some t' ∧ t'.mem = VG.Proof.AesGcmSiv.Arm.tagInMem t.mem (State.addr p.W) (State.addr p.N) ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r0, .r1, .r2, .r3, .r12] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₀ := E.perm.wR (show 80 + 4 ≤ 3760 by decide)
  have r₁ := E.perm.wR (show 84 + 4 ≤ 3760 by decide)
  have r₂ := E.perm.wR (show 88 + 4 ≤ 3760 by decide)
  have r₃ := E.perm.wR (show 92 + 4 ≤ 3760 by decide)
  have w₀ := E.perm.wW (show 96 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 100 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 104 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 108 + 4 ≤ 3760 by decide)
  have n₀ : InRegions (t.rd ++ t.wr) (State.addr p.N) 4 := by simpa using E.perm.nR (d := 0) (k := 4) (by decide)
  have n₄ := E.perm.nR (d := 4) (k := 4) (by decide)
  have n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  refine ⟨_, by simp only [tagIn]; srun [E.r10, E.r11, add_ofNat_zero, L.nA, L.wA, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃,
    n₀, n₄, n₈], ?_, by others_tac, by rfl, by rfl, by rfl⟩
  simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, VG.Proof.AesGcmSiv.Arm.tagInMem, Proof.Cmac.store4,
    add_ofNat_assoc, Nat.reduceAdd]

/-! ## `polyval` -/

/-- What `polyval` writes: what absorbing writes, and the tag input at `W + 96`. -/
abbrev polyR (W : Addr) (SP : BitVec 32) : List Region := ⟨W + BitVec.ofNat 64 96, 16⟩ :: VG.Proof.AesGcmSiv.Arm.absorbR W SP

/-- What `polyval` leaves, from `t`. -/
structure PolyPost (p : VG.Proof.AesGcmSiv.Arm.Prm) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (VG.Proof.AesGcmSiv.Arm.polyR (State.addr p.W) p.SP) t.mem t'.mem
  out : bytesAt t'.mem (State.addr p.W + BitVec.ofNat 64 96) 16 =
    tagInputG (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16) (bytesAt t.mem (State.addr p.N) 12)
      (bytesAt t.mem (State.addr p.D) p.n) (bytesAt t.mem (State.addr p.A) p.al)

/-- The additional data, as a chunk's source. -/
theorem srcA {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {s : State} (P : VG.Proof.AesGcmSiv.Arm.Perm p s) : VG.Proof.AesGcmSiv.Arm.Src p s p.A p.al :=
  ⟨P.aad, L.aw, L.a_w' (by decide), L.a_w' (by decide), L.ba⟩

/-- The data, as a chunk's source. -/
theorem srcD {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {s : State} (P : VG.Proof.AesGcmSiv.Arm.Perm p s) : VG.Proof.AesGcmSiv.Arm.Src p s p.D p.n :=
  ⟨covers_left P.d, L.dw, L.d_w' (by decide), L.d_w' (by decide), L.bd⟩

theorem polyval_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) (A : VG.Proof.AesGcmSiv.Arm.Args p t.mem)
    (hG : Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 80) = 0) :
    WP isa polyval t (VG.Proof.AesGcmSiv.Arm.PolyPost p t) := by
  have a₀ := E.perm.argR' L (k := 0) (by decide)
  -- The additional data.
  refine WP.seq (WP.of_runBlock ⟨_, by srun [E.sp, a₀, A.a0], ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.absorb_ok L (E.keep (fun r hr => by
      simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) (by rfl) (by rfl) (by rfl)) L.al_lt
    (VG.Proof.AesGcmSiv.Arm.srcA L (E.perm.of_eq (by rfl) (by rfl))) L.a_w (by simp [gpr_setReg, E.r7]) (by simp [gpr_setReg])) fun t₂ P₂ => ?_)
  simp only [mem_setReg] at P₂
  have P₂' := P₂.of_eq (t := t) rfl rfl rfl
  have A₂ : VG.Proof.AesGcmSiv.Arm.Args p t₂.mem := A.frame L P₂.frame (VG.Proof.AesGcmSiv.Arm.absorbR_args L)
  -- The data.
  have a₄ := P₂.env.perm.argR' L (k := 4) (by decide)
  have a₈ := P₂.env.perm.argR' L (k := 8) (by decide)
  refine WP.seq (WP.of_runBlock ⟨_, by srun [P₂.env.sp, a₄, a₈, A₂.a4, A₂.a8], ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.absorb_ok L (P₂.env.keep (fun r hr => by
      simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) (by rfl) (by rfl) (by rfl)) L.n_lt
    (VG.Proof.AesGcmSiv.Arm.srcD L (P₂.env.perm.of_eq (by rfl) (by rfl))) L.d_w (by simp [gpr_setReg]) (by simp [gpr_setReg])) fun t₄ P₄ => ?_)
  simp only [mem_setReg] at P₄
  rw [Proof.AesGcm.Arm.bytesAt_frame P₂.frame (VG.Proof.AesGcmSiv.Arm.absorbR_buf L.d_w L.bd) (by have := L.n_lt; omega)] at P₄
  have P₂₄ := AbsPost.trans L P₂' (P₄.of_eq rfl rfl rfl)
  have A₄ : VG.Proof.AesGcmSiv.Arm.Args p t₄.mem := A₂.frame L P₄.frame (VG.Proof.AesGcmSiv.Arm.absorbR_args L)
  -- The lengths.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.lens_ok L P₂₄.env A₄) fun t₅ P₅ => ?_)
  have P₂₅ := AbsPost.trans L P₂₄ P₅
  -- The tag input.
  obtain ⟨t₆, run₆, hm₆, ho₆, sp₆, rd₆, wr₆⟩ := VG.Proof.AesGcmSiv.Arm.tagIn_ok L P₂₅.env
  refine WP.of_runBlock ⟨t₆, run₆, P₂₅.env.of_others ho₆ sp₆ rd₆ wr₆, by rw [rd₆, P₂₅.rd], by rw [wr₆, P₂₅.wr],
    ?_, ?_⟩
  · refine (P₂₅.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans ?_
    rw [hm₆]
    exact (VG.Proof.AesGcmSiv.Arm.tagInMem_frame _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega
    have nN : bytesAt t₅.mem (State.addr p.N) 12 = bytesAt t.mem (State.addr p.N) 12 :=
      Proof.AesGcm.Arm.bytesAt_frame P₂₅.frame (VG.Proof.AesGcmSiv.Arm.absorbR_buf L.n_w L.bn) (by decide)
    rw [hm₆, VG.Proof.AesGcmSiv.Arm.tagInMem_bytes, nN, P₂₅.out, hG, hY, tagInputG, length_bytesAt, length_bytesAt,
      GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))
        (by simp [Spec.GcmSiv.le64])]
    simp only [mem_setReg]

end VG.Proof.AesGcmSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.Arm.Tag`. -/
section

/-!
# AES-GCM-SIV on ARMv7: a block encrypted with the encryption key (`tag`)

Untrusted: everything here is checked by Lean. `tag o` copies the block at
`W + 96` to `W + 112` (`copyMem`), zeroes the block at `W + o`, and calls
`vg_aes_ctr32` on that one block with the copy as the counter block: the
encryption of the block at `W + 96` with the encryption key's schedule at
`W + 192` (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (CtrCall CtrPost ctr_call below covers_cons covers_nil covers_append' add_ofNat_assoc
  add_ofNat_zero mem_store gpr_store sp_store rd_store wr_store z_store)

theorem blockAt_zero4 (m : Mem) (p : Addr) : Spec.Gcm.blockAt (Proof.Cmac.zero4 m p) p = 0 := by
  rw [Spec.Gcm.blockAt, Proof.Cmac.zero4_bytes]
  decide

/-- The memory after the copy of the counter block. -/
def copyMem (m : Mem) (W : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 112) (m.readW (W + BitVec.ofNat 64 96) 32)
    (m.readW (W + BitVec.ofNat 64 100) 32) (m.readW (W + BitVec.ofNat 64 104) 32)
    (m.readW (W + BitVec.ofNat 64 108) 32)

theorem copyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] m (VG.Proof.AesGcmSiv.Arm.copyMem m W) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem copyMem_bytes (m : Mem) (W : Addr) :
    bytesAt (VG.Proof.AesGcmSiv.Arm.copyMem m W) (W + BitVec.ofNat 64 112) 16 = bytesAt m (W + BitVec.ofNat 64 96) 16 := by
  rw [VG.Proof.AesGcmSiv.Arm.copyMem, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.bytesAt_split4]
  simp only [add_ofNat_assoc, Nat.reduceAdd]

/-- What `tag o` writes. -/
abbrev tagR (W : Addr) (SP : BitVec 32) (o : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩, ⟨W + BitVec.ofNat 64 1712, 2048⟩, below SP]

/-- What `tag o` leaves, from `t`. -/
structure TagPost (p : VG.Proof.AesGcmSiv.Arm.Prm) (o : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  r4 : t'.gpr .r4 = t.gpr .r4
  r5 : t'.gpr .r5 = t.gpr .r5
  frame : Frame (VG.Proof.AesGcmSiv.Arm.tagR (State.addr p.W) p.SP o) t.mem t'.mem
  out : bytesAt t'.mem (State.addr p.W + BitVec.ofNat 64 o) 16 =
    Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R
      (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 96) 16)

/-- The arguments of `tag o`'s call. -/
theorem tagArgs_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) {o : Nat} (ho : o = 0 ∨ o = 176) :
    ∃ t₁ : State, runBlock isa (copy16 cbO ccO ++ Impl.AesGcm.Arm.zero16 o ++ ctrArgs ++
        ([Impl.AesGcm.Arm.addI .r3 .r11 o] : List Instr)) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero4 (VG.Proof.AesGcmSiv.Arm.copyMem t.mem (State.addr p.W)) (State.addr p.W + BitVec.ofNat 64 o) ∧
      t₁.gpr .r0 = p.W + BitVec.ofNat 32 192 ∧ t₁.gpr .r1 = BitVec.ofNat 32 p.R ∧
      t₁.gpr .r2 = p.W + BitVec.ofNat 32 112 ∧ t₁.gpr .r3 = p.W + BitVec.ofNat 32 o ∧
      t₁.gpr .r12 = BitVec.ofNat 32 1 ∧ t₁.gpr .lr = p.W + BitVec.ofNat 32 1712 ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r0, .r1, .r2, .r3, .r12, .lr] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have r₀ := E.perm.wR (show 96 + 4 ≤ 3760 by decide)
  have r₁ := E.perm.wR (show 100 + 4 ≤ 3760 by decide)
  have r₂ := E.perm.wR (show 104 + 4 ≤ 3760 by decide)
  have r₃ := E.perm.wR (show 108 + 4 ≤ 3760 by decide)
  have w₀ := E.perm.wW (show 112 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 116 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 120 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 124 + 4 ≤ 3760 by decide)
  have z₀ := E.perm.wW (show o + 4 ≤ 3760 by omega)
  have z₁ := E.perm.wW (show o + 4 + 4 ≤ 3760 by omega)
  have z₂ := E.perm.wW (show o + 8 + 4 ≤ 3760 by omega)
  have z₃ := E.perm.wW (show o + 12 + 4 ≤ 3760 by omega)
  have o₁ : o < 3760 := by omega
  have o₂ : o + 4 < 3760 := by omega
  have o₃ : o + 8 < 3760 := by omega
  have o₄ : o + 12 < 3760 := by omega
  have i₁ : o < 4096 := by omega
  have i₂ : o + 4 < 4096 := by omega
  have i₃ : o + 8 < 4096 := by omega
  have i₄ : o + 12 < 4096 := by omega
  have oe : encodable (BitVec.ofNat 32 o) = true := by rcases ho with rfl | rfl <;> decide
  refine ⟨_, by simp only [copy16, Impl.AesGcm.Arm.zero16, ctrArgs]; srun [E.r8, E.r11, L.wA, r₀, r₁, r₂, r₃,
    w₀, w₁, w₂, w₃, z₀, z₁, z₂, z₃, o₁, o₂, o₃, o₄, i₁, i₂, i₃, i₄, oe], ?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, by rfl,
    by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, Proof.Cmac.zero4,
      Proof.Cmac.store4, VG.Proof.AesGcmSiv.Arm.copyMem, add_ofNat_assoc, Nat.reduceAdd]
    rfl
  all_goals simp [gpr_setReg, E.r8, E.r11]

/-- The arguments of `tag o`'s call, as `vg_aes_ctr32` needs them. -/
theorem tagCall {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t₁ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p t₁) {o : Nat} (ho : o = 0 ∨ o = 176)
    (r0 : t₁.gpr .r0 = p.W + BitVec.ofNat 32 192) (r1 : t₁.gpr .r1 = BitVec.ofNat 32 p.R)
    (r2 : t₁.gpr .r2 = p.W + BitVec.ofNat 32 112) (r3 : t₁.gpr .r3 = p.W + BitVec.ofNat 32 o)
    (r12 : t₁.gpr .r12 = BitVec.ofNat 32 1) (lr : t₁.gpr .lr = p.W + BitVec.ofNat 32 1712) :
    CtrCall t₁ (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 o)
      (p.W + BitVec.ofNat 32 1712) p.R 1 := by
  have hw := L.ww
  have o₁ : o < 3760 := by omega
  refine ⟨r0, r1, r2, r3, r12, lr, L.rounds3, by rw [E₁.sp]; exact L.sp8, by rw [L.wN (by decide)]; omega,
    by rw [L.wN (by decide)]; omega, by rw [L.wN o₁]; omega, by rw [L.wN (by decide)]; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [L.wA (show 192 < 3760 by decide), L.wA (show 112 < 3760 by decide), L.wA o₁,
      L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one]
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by omega)) (by decide) (by omega)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.w_w (by omega) (by omega) (by decide) :
      (⟨State.addr p.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact L.bw' (by decide)
  · exact L.bw' (by decide)
  · exact L.bw' (by omega)
  · exact L.bw' (by decide)
  · exact E₁.perm.wCR (by decide)
  · exact covers_cons (E₁.perm.wC (by decide)) (covers_cons (E₁.perm.wC (by omega))
      (covers_cons (E₁.perm.wC (by decide)) covers_nil))

theorem tag_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) {o : Nat} (ho : o = 0 ∨ o = 176) :
    WP isa (tag o) t (VG.Proof.AesGcmSiv.Arm.TagPost p o t) := by
  have hw := L.ww
  have o₁ : o < 3760 := by omega
  obtain ⟨t₁, run₁, hm₁, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.Arm.tagArgs_ok L E ho
  have E₁ : VG.Proof.AesGcmSiv.Arm.Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  have dO : (⟨State.addr p.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩ :=
    L.w_w (by omega) (by omega) (by decide)
  have cc := VG.Proof.AesGcmSiv.Arm.tagCall L E₁ ho r0 r1 r2 r3 r12 lr
  have fZ := Proof.Cmac.frame_store4 (m := VG.Proof.AesGcmSiv.Arm.copyMem t.mem (State.addr p.W)) (State.addr p.W + BitVec.ofNat 64 o) 0 0 0 0
  have f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 o, 16⟩]
      t.mem t₁.mem := by
    rw [hm₁, Proof.Cmac.zero4]
    exact ((VG.Proof.AesGcmSiv.Arm.copyMem_frame _ _).mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans
      (fZ.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp)
  have hb₁ : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 112) 16 =
      bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 96) 16 := by
    rw [hm₁, Proof.Cmac.zero4, Proof.AesGcm.Arm.bytesAt_frame fZ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dO.symm) (by decide), VG.Proof.AesGcmSiv.Arm.copyMem_bytes]
  have hz₁ : Spec.Gcm.blockAt t₁.mem (State.addr p.W + BitVec.ofNat 64 o) = 0 := by
    rw [hm₁]; exact VG.Proof.AesGcmSiv.Arm.blockAt_zero4 _ _
  have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 192) p.R =
      Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.Arm.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le)
      · exact (L.w_w (.inr (by omega)) (by decide) (by omega)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (ctr_call cc) fun t₂ P => ?_
  have fc := P.frame
  have hout := P.out
  simp only [L.wA (show 192 < 3760 by decide), L.wA (show 112 < 3760 by decide), L.wA o₁,
    L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one] at fc hout
  refine ⟨E₁.of_saved P.saved P.sp P.rd P.wr, by rw [P.rd, rd₁], by rw [P.wr, wr₁],
    by rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide)],
    by rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide)],
    (f₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp).trans (fc.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp), ?_⟩
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
  rw [Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
    show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 192) (16 * (p.R + 1))) =
      Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 192) p.R from rfl, ek₁, hb₁]

end VG.Proof.AesGcmSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.Arm.Crypt`. -/
section

/-!
# AES-GCM-SIV on ARMv7: counter mode (`crypt`)

Untrusted: everything here is checked by Lean. The counter block at
`W + 96` starts as the tag with the top bit of its last byte set
(`cryptHead_ok`); each block of the data is encrypted in place by
`vg_aes_ctr32` from a copy of it at `W + 112`, after which its first word is
incremented (`cryptBlock_ok`); the last bytes are XORed with the keystream
block, computed at `W + 176` (`cryptTail_ok`). `crypt_ok`: the data becomes
`ctr` of it (RFC 8452 §4).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.AesGcm.Arm (CtrCall CtrPost ctr_call below covers_cons covers_nil covers_append' covers_off
  covers_left covers_prefix add_ofNat_assoc add_ofNat_zero add32_ofNat_assoc eval_eq' eval_ne' z_cmp ofNat_sub32
  ofNat_add32 toNat32 mem_store gpr_store sp_store rd_store wr_store z_store mem_subFlags z_subFlags gpr_subFlags
  sp_subFlags rd_subFlags wr_subFlags LoopPre LoopOut xorLoop_ok xorBytes length_bytesAt)

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

theorem CtrSt.block {W : Addr} {icb : List Byte} {j : Nat} {m : Mem} (h : VG.Proof.AesGcmSiv.Arm.CtrSt W icb j m) :
    bytesAt m (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.counterBlock icb j := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    h.word, add_ofNat_assoc, h.rest]

/-- Bytes of a buffer outside the part a frame may also change. -/
theorem frame_outside {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {len a n : Nat}
    (hrs : ∀ r ∈ rs, r = ⟨P + BitVec.ofNat 64 a, n⟩ ∨ (⟨P, len⟩ : Region).Disjoint r) (hlen : len < 2 ^ 64)
    (han : a + n ≤ len) : ∀ p < len, (p < a ∨ a + n ≤ p) → m' (P + BitVec.ofNat 64 p) = m (P + BitVec.ofNat 64 p) :=
  fun p hp ho => hf _ fun r hr hc => by
    rcases hrs r hr with rfl | hd
    · exact Offset.disjoint P (d := p) (n := 1) (by omega) (by omega) (by omega) _ (Region.contains_self _ _) hc
    · exact hd _ (Offset.contains_base P (show p + 1 ≤ len by omega) (by omega)) hc

/-- What counter mode writes: the counter block, its copy, the block at
`W + 176`, `vg_aes_ctr32`'s working space, the data and the stack below
`SP`. -/
abbrev cryR (W D : Addr) (n : Nat) (SP : BitVec 32) : List Region :=
  [⟨W + BitVec.ofNat 64 96, 32⟩, ⟨W + BitVec.ofNat 64 176, 16⟩, ⟨W + BitVec.ofNat 64 1712, 2048⟩, ⟨D, n⟩, below SP]

/-- Block `j` of the data, as a 64-bit address. -/
theorem Lay.dA {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {j : Nat} (hj : j < p.n) :
    State.addr (p.D + BitVec.ofNat 32 j) = State.addr p.D + BitVec.ofNat 64 j :=
  addr_add (by have := L.dw; omega)

theorem Lay.dN {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {j : Nat} (hj : j < p.n) : (p.D + BitVec.ofNat 32 j).toNat = p.D.toNat + j := by
  have := L.dw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- What a block of counter mode leaves, from `t`. -/
structure BlockPost (p : VG.Proof.AesGcmSiv.Arm.Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (j : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  r4 : t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * (j + 1))
  r5 : t'.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * (j + 1))
  z : t'.z = decide ((p.n - 16 * (j + 1)) / 16 = 0)
  ctr : VG.Proof.AesGcmSiv.Arm.CtrSt (State.addr p.W) icb (j + 1) t'.mem
  data : bytesAt t'.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * (j + 1))
  frame : Frame (VG.Proof.AesGcmSiv.Arm.cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t'.mem

/-- The arguments of a block's call. -/
theorem blkArgs_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) {j : Nat}
    (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j)) :
    ∃ t₁ : State, runBlock isa (copy16 cbO ccO ++ ctrArgs ++ ([.mov .r3 (.reg .r4)] : List Instr)) t = some t₁ ∧
      t₁.mem = VG.Proof.AesGcmSiv.Arm.copyMem t.mem (State.addr p.W) ∧
      t₁.gpr .r0 = p.W + BitVec.ofNat 32 192 ∧ t₁.gpr .r1 = BitVec.ofNat 32 p.R ∧
      t₁.gpr .r2 = p.W + BitVec.ofNat 32 112 ∧ t₁.gpr .r3 = p.D + BitVec.ofNat 32 (16 * j) ∧
      t₁.gpr .r12 = BitVec.ofNat 32 1 ∧ t₁.gpr .lr = p.W + BitVec.ofNat 32 1712 ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r0, .r1, .r2, .r3, .r12, .lr] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have r₀ := E.perm.wR (show 96 + 4 ≤ 3760 by decide)
  have r₁ := E.perm.wR (show 100 + 4 ≤ 3760 by decide)
  have r₂ := E.perm.wR (show 104 + 4 ≤ 3760 by decide)
  have r₃ := E.perm.wR (show 108 + 4 ≤ 3760 by decide)
  have w₀ := E.perm.wW (show 112 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 116 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 120 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 124 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [copy16, ctrArgs]; srun [E.r8, E.r11, L.wA, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃], ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, Proof.Cmac.store4, VG.Proof.AesGcmSiv.Arm.copyMem,
      add_ofNat_assoc, Nat.reduceAdd]
  all_goals simp [gpr_setReg, E.r8, E.r11, h4]

/-- The arguments of a block's call, as `vg_aes_ctr32` needs them. -/
theorem blkCall {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t₁ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p t₁) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (r0 : t₁.gpr .r0 = p.W + BitVec.ofNat 32 192) (r1 : t₁.gpr .r1 = BitVec.ofNat 32 p.R)
    (r2 : t₁.gpr .r2 = p.W + BitVec.ofNat 32 112) (r3 : t₁.gpr .r3 = p.D + BitVec.ofNat 32 (16 * j))
    (r12 : t₁.gpr .r12 = BitVec.ofNat 32 1) (lr : t₁.gpr .lr = p.W + BitVec.ofNat 32 1712) :
    CtrCall t₁ (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 112) (p.D + BitVec.ofNat 32 (16 * j))
      (p.W + BitVec.ofNat 32 1712) p.R 1 := by
  have hn := L.n_lt
  have hdw := L.dw
  have hw := L.ww
  have dQ : (⟨State.addr p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  refine ⟨r0, r1, r2, r3, r12, lr, L.rounds3, by rw [E₁.sp]; exact L.sp8, by rw [L.wN (by decide)]; omega,
    by rw [L.wN (by decide)]; omega, by rw [L.dN (by omega)]; omega, by rw [L.wN (by decide)]; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [L.wA (show 192 < 3760 by decide), L.wA (show 112 < 3760 by decide), L.dA (show 16 * j < p.n by omega),
      L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one]
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact (dQ.sub_right (Lay.wSub (show 192 + 240 ≤ 3760 by decide))).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (dQ.sub_right (Lay.wSub (show 112 + 16 ≤ 3760 by decide))).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact dQ.sub_right (Lay.wSub (by decide))
  · exact L.bw' (by decide)
  · exact L.bw' (by decide)
  · exact L.bd.sub_right (Offset.sub_base _ (by omega))
  · exact L.bw' (by decide)
  · exact E₁.perm.wCR (by decide)
  · exact covers_cons (E₁.perm.wC (by decide)) (covers_cons (covers_off E₁.perm.d (by omega) (by omega))
      (covers_cons (E₁.perm.wC (by decide)) covers_nil))

/-- The code after a block's call. -/
theorem blkPost_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j)) (h5 : t.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j)) :
    ∃ t' : State, runBlock isa blockNext t = some t' ∧
      t'.mem = t.mem.writeW (State.addr p.W + BitVec.ofNat 64 96)
        (t.mem.readW (State.addr p.W + BitVec.ofNat 64 96) 32 + BitVec.ofNat 32 1) ∧
      t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * (j + 1)) ∧ t'.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * (j + 1)) ∧
      t'.z = decide ((p.n - 16 * (j + 1)) / 16 = 0) ∧ VG.Proof.AesGcmSiv.Arm.Others [.r0, .r4, .r5, .r12] t t' ∧ t'.sp = t.sp ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hn := L.n_lt
  have c₀ := E.perm.wR (show 96 + 4 ≤ 3760 by decide)
  have c₁ := E.perm.wW (show 96 + 4 ≤ 3760 by decide)
  have e5 : BitVec.ofNat 32 (p.n - 16 * j) - BitVec.ofNat 32 16 = BitVec.ofNat 32 (p.n - 16 * (j + 1)) := by
    rw [ofNat_sub32 (by omega) (by omega), show p.n - 16 * j - 16 = p.n - 16 * (j + 1) by omega]
  refine ⟨_, by simp only [blockNext, wholeLeft]; srun [E.r11, L.wA, h4, h5, c₀, c₁], ?_, ?_, ?_, ?_, by others_tac,
    by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, mem_subFlags]
  · simp [gpr_setReg, add32_ofNat_assoc, Nat.mul_succ]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, e5]
  · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, e5, VG.Proof.AesGcmSiv.Arm.ofNat_lsr32 (show p.n - 16 * (j + 1) < 2 ^ 32 by omega)]
    rw [z_cmp (by omega) (by decide)]
    rfl

theorem cryptBlock_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {j : Nat}
    (hj : 16 * (j + 1) ≤ p.n) (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j))
    (h5 : t.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j)) (C : VG.Proof.AesGcmSiv.Arm.CtrSt (State.addr p.W) icb j t.mem)
    (hx : bytesAt t.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j))
    (hc : Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph) :
    WP isa cryptBlock t (VG.Proof.AesGcmSiv.Arm.BlockPost p ciph icb x j t) := by
  have hw := L.ww
  have hn := L.n_lt
  have hdw := L.dw
  obtain ⟨t₁, run₁, hm₁, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.Arm.blkArgs_ok L E h4
  have E₁ : VG.Proof.AesGcmSiv.Arm.Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  have dQ : (⟨State.addr p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  have cc := VG.Proof.AesGcmSiv.Arm.blkCall L E₁ hj r0 r1 r2 r3 r12 lr
  -- What the copy changed.
  have f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact VG.Proof.AesGcmSiv.Arm.copyMem_frame _ _
  have dD : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩ : Region)],
      (⟨State.addr p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hcb : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.counterBlock icb j := by
    rw [hm₁, VG.Proof.AesGcmSiv.Arm.copyMem_bytes, C.block]
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph := by
    rw [← hc]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.Arm.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  have hx₁ : bytesAt t₁.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j) := by
    rw [Proof.AesGcm.Arm.bytesAt_frame f₁ dD (by omega), hx]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  refine WP.mono (ctr_call cc) fun t₂ P => ?_
  have fc := P.frame
  have hout := P.out
  simp only [L.wA (show 192 < 3760 by decide), L.wA (show 112 < 3760 by decide), L.dA (show 16 * j < p.n by omega),
    L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one] at fc hout
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    VG.Proof.AesGcmSiv.Arm.ctr32_single, List.cons.injEq, and_true] at hout
  have hb₂ : bytesAt t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * j)) 16 =
      Spec.Cmac.xor (bytesAt t₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * j)) 16) (GcmSiv.ksBlock ciph icb j) := by
    rw [Proof.Cmac.bytesAt_blockAt, hout, VG.Proof.AesGcmSiv.Arm.toBytes_xor, ← Proof.Cmac.bytesAt_blockAt, Spec.Gcm.blockAt,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
      show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 192) (16 * (p.R + 1))) =
        Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 192) p.R from rfl, hc₁, hcb]
  have hk : (GcmSiv.ksBlock ciph icb j).length = 16 := by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  have hx₂ : bytesAt t₂.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j + 16) := by
    rw [← hxl] at hx₁ ⊢
    refine GcmSiv.ctrPart_step ciph icb x _ (by decide) hk hx₁ ?_ (by rw [hb₂, List.take_of_length_le (by omega)])
    rw [hxl]
    refine VG.Proof.AesGcmSiv.Arm.frame_outside fc (fun q hq => ?_) (by omega) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inl rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inr L.bd.symm
  have E₂ : VG.Proof.AesGcmSiv.Arm.Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have h4₂ : t₂.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), h4]
  have h5₂ : t₂.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), h5]
  -- What the first two pieces changed.
  have f₂' : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩, ⟨State.addr p.D + BitVec.ofNat 64 (16 * j), 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 1712, 2048⟩, below p.SP] t.mem t₂.mem :=
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans fc
  have f₂ : Frame (VG.Proof.AesGcmSiv.Arm.cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t₂.mem := f₂'.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨State.addr p.D, p.n⟩, by simp, Offset.sub_base _ (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have dC : ∀ {d k : Nat}, 96 ≤ d → d + k ≤ 112 →
      ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨State.addr p.D + BitVec.ofNat 64 (16 * j), 16⟩,
        ⟨State.addr p.W + BitVec.ofNat 64 1712, 2048⟩, below p.SP],
        (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (dQ.sub_right (Lay.wSub (by omega))).symm
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.bw' (by omega)).symm
  have w₂ : t₂.mem.readW (State.addr p.W + BitVec.ofNat 64 96) 32 = t.mem.readW (State.addr p.W + BitVec.ofNat 64 96) 32 :=
    f₂'.readW (Region.contains_self _ _) (dC (k := 4) (Nat.le_refl _) (by decide)) (by decide)
  have r₂ : bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 100) 12 =
      bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 100) 12 :=
    Proof.AesGcm.Arm.bytesAt_frame f₂' (dC (by decide) (by decide)) (by decide)
  have fw : ∀ v : BitVec 32, Frame [⟨State.addr p.W + BitVec.ofNat 64 96, 4⟩] t₂.mem
      (t₂.mem.writeW (State.addr p.W + BitVec.ofNat 64 96) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain ⟨t₃, run₃, hm₃, r4₃, r5₃, z₃, ho₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesGcmSiv.Arm.blkPost_ok L E₂ hj h4₂ h5₂
  refine WP.of_runBlock ⟨t₃, run₃, E₂.of_others ho₃ sp₃ rd₃ wr₃, by rw [rd₃, P.rd, rd₁], by rw [wr₃, P.wr, wr₁],
    r4₃, r5₃, z₃, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hm₃, Mem.readW_writeW_self32, w₂, C.word]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [hm₃, Proof.AesGcm.Arm.bytesAt_frame (fw _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), r₂, C.rest]
  · rw [hm₃, Proof.AesGcm.Arm.bytesAt_frame (fw _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)) (Nat.le_of_lt (by omega)), hx₂,
      show 16 * j + 16 = 16 * (j + 1) by omega]
  · rw [hm₃]
    exact f₂.writeW (List.mem_cons_self ..) _ (Offset.contains _ (Nat.le_refl _) (by decide) (by decide))


/-- The encryption key's schedule misses what counter mode writes. -/
theorem key_cryR {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) :
    ∀ r ∈ VG.Proof.AesGcmSiv.Arm.cryR (State.addr p.W) (State.addr p.D) p.n p.SP,
      (⟨State.addr p.W + BitVec.ofNat 64 192, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm
  · exact (L.bw' (by decide)).symm

theorem ciph_cryR {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.Arm.cryR (State.addr p.W) (State.addr p.D) p.n p.SP) m m') :
    Spec.GcmSiv.ctxCiph m' (State.addr p.W + BitVec.ofNat 64 192) p.R =
      Spec.GcmSiv.ctxCiph m (State.addr p.W + BitVec.ofNat 64 192) p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.Arm.bytesAt_frame hf (fun r hr => (VG.Proof.AesGcmSiv.Arm.key_cryR L r hr).sub_left (Region.sub_prefix L.rounds_le))
    (by have := L.rounds_le; omega)]

/-- What the whole blocks of counter mode leave, from `t`. -/
structure BlocksPost (p : VG.Proof.AesGcmSiv.Arm.Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (b : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  r4 : t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * b)
  r5 : t'.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * b)
  ctr : VG.Proof.AesGcmSiv.Arm.CtrSt (State.addr p.W) icb b t'.mem
  data : bytesAt t'.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b)
  frame : Frame (VG.Proof.AesGcmSiv.Arm.cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t'.mem

theorem blocks_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) (hb1 : 1 ≤ p.n / 16)
    (h4 : t.gpr .r4 = p.D) (h5 : t.gpr .r5 = BitVec.ofNat 32 p.n)
    (C : VG.Proof.AesGcmSiv.Arm.CtrSt (State.addr p.W) icb 0 t.mem) (hx : bytesAt t.mem (State.addr p.D) p.n = x)
    (hc : Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph) :
    WP isa (.loop cryptBlock .ne) t (VG.Proof.AesGcmSiv.Arm.BlocksPost p ciph icb x (p.n / 16) t) := by
  refine WP.loop (M := isa) (body := cryptBlock) (c := .ne)
    (fun (k : Nat) (t' : State) => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ VG.Proof.AesGcmSiv.Arm.BlocksPost p ciph icb x j t t') ?_
    (p.n / 16 - 0) t
    ⟨0, rfl, hb1, ⟨E, rfl, rfl, by rw [h4, Nat.mul_zero, add_ofNat_zero], by rw [h5, Nat.mul_zero, Nat.sub_zero],
      C, by rw [hx, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  rintro k t' ⟨j, rfl, hj, P⟩
  have hc' : Spec.GcmSiv.ctxCiph t'.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph := by
    rw [VG.Proof.AesGcmSiv.Arm.ciph_cryR L P.frame, hc]
  refine WP.mono (VG.Proof.AesGcmSiv.Arm.cryptBlock_ok L P.env hxl (j := j) (by omega) P.r4 P.r5 P.ctr P.data hc') fun t'' Q => ?_
  have P' : VG.Proof.AesGcmSiv.Arm.BlocksPost p ciph icb x (j + 1) t t'' :=
    ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.r4, Q.r5, Q.ctr, Q.data, P.frame.trans Q.frame⟩
  have ev := eval_ne' Q.z
  by_cases he : j + 1 = p.n / 16
  · left
    exact ⟨ev.trans (by simp; omega), he ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp; omega), p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, P'⟩

/-- What the last bytes of counter mode leave, from `t`. -/
structure TailPost (p : VG.Proof.AesGcmSiv.Arm.Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  data : bytesAt t'.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x p.n
  frame : Frame (VG.Proof.AesGcmSiv.Arm.cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t'.mem

theorem cryptTail_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {b r : Nat}
    (hn : p.n = 16 * b + r) (hr1 : 1 ≤ r) (hr : r < 16) (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * b))
    (h5 : t.gpr .r5 = BitVec.ofNat 32 r) (C : VG.Proof.AesGcmSiv.Arm.CtrSt (State.addr p.W) icb b t.mem)
    (hx : bytesAt t.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b))
    (hc : Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph) :
    WP isa cryptTail t (VG.Proof.AesGcmSiv.Arm.TailPost p ciph icb x t) := by
  have hn' := L.n_lt
  have hdw := L.dw
  have hw := L.ww
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.tag_ok L E (o := 176) (by decide)) fun t₂ T => ?_)
  have fT := T.frame
  have dT : ∀ q ∈ VG.Proof.AesGcmSiv.Arm.tagR (State.addr p.W) p.SP 176, (⟨State.addr p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  have hx₂ : bytesAt t₂.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b) := by
    rw [Proof.AesGcm.Arm.bytesAt_frame fT dT (by omega), hx]
  have hks : bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 16 = GcmSiv.ksBlock ciph icb b := by
    rw [T.out, hc, C.block]
  have h4₂ : t₂.gpr .r4 = p.D + BitVec.ofNat 32 (16 * b) := by rw [T.r4, h4]
  have h5₂ : t₂.gpr .r5 = BitVec.ofNat 32 r := by rw [T.r5, h5]
  obtain ⟨t₃, run₃, r1₃, r2₃, r3₃, ho₃, m₃, sp₃, rd₃, wr₃⟩ : ∃ t₃ : State, runBlock isa
      [Impl.AesGcm.Arm.addI .r1 .r11 bO, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)] t₂ = some t₃ ∧
      t₃.gpr .r1 = p.W + BitVec.ofNat 32 176 ∧ t₃.gpr .r2 = p.D + BitVec.ofNat 32 (16 * b) ∧
      t₃.gpr .r3 = BitVec.ofNat 32 r ∧ VG.Proof.AesGcmSiv.Arm.Others [.r1, .r2, .r3] t₂ t₃ ∧ t₃.mem = t₂.mem ∧ t₃.sp = t₂.sp ∧
      t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
    · simp [gpr_setReg, T.env.r11]
    · simp [gpr_setReg, h4₂]
    · simp [gpr_setReg, h5₂]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have eD := L.dA (j := 16 * b) (by omega)
  have dQ : (⟨State.addr p.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  have lp : LoopPre t₃ (p.W + BitVec.ofNat 32 176) (p.D + BitVec.ofNat 32 (16 * b)) r := by
    refine ⟨r1₃, r2₃, r3₃, by omega, by omega, by rw [L.wN (by decide)]; omega, by rw [L.dN (by omega)]; omega,
      ?_, ?_, ?_⟩
    · rw [rd₃, wr₃, L.wA (by decide)]
      exact covers_prefix (T.env.perm.wCR (show 176 + 16 ≤ 3760 by decide)) (by omega)
    · rw [wr₃, eD]; exact covers_off T.env.perm.d (by omega) (by omega)
    · rw [eD, L.wA (by decide)]
      exact ((dQ.sub_right (Lay.wSub (show 176 + 16 ≤ 3760 by decide))).sub_right (Region.sub_prefix (by omega))).symm
  refine WP.mono (xorLoop_ok t₃ lp) fun t₄ ⟨hm₄, O⟩ => ?_
  rw [m₃, eD, L.wA (by decide)] at hm₄
  have hl : (xorBytes t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * b)) (State.addr p.W + BitVec.ofNat 64 176) r).length
      = r := by simp [xorBytes, Proof.Cmac.bytesAt_length]
  have fw := Proof.AesGcm.Arm.writeBytes_frame' t₂.mem (q := State.addr p.D + BitVec.ofNat 64 (16 * b)) hl
  rw [← hm₄] at fw
  have hk : (GcmSiv.ksBlock ciph icb b).length = 16 := by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  refine ⟨T.env.keep (fun q hq => by
      have h1 : q ≠ .r1 := by
        simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      have h2 : q ≠ .r2 := by
        simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      have h3 : q ≠ .r3 := by
        simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      have h0 : q ≠ .r0 := by
        simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      have h12 : q ≠ .r12 := by
        simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [O.other q h0 h1 h2 h3 h12, ho₃ q (by simp [h1, h2, h3])])
      (by rw [O.sp, sp₃]) (by rw [O.rd, rd₃]) (by rw [O.wr, wr₃]),
    by rw [O.rd, rd₃, T.rd], by rw [O.wr, wr₃, T.wr], ?_, ?_⟩
  · have hb' : bytesAt t₄.mem (State.addr p.D + BitVec.ofNat 64 (16 * b)) r = Spec.Cmac.xor
        (bytesAt t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * b)) r) ((GcmSiv.ksBlock ciph icb b).take r) := by
      have e := Proof.AesGcm.Arm.bytesAt_writeBytes_self t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * b))
        (xorBytes t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * b)) (State.addr p.W + BitVec.ofNat 64 176) r)
        (by omega)
      rw [hl] at e
      have hs := Proof.Cmac.bytesAt_add t₂.mem (State.addr p.W + BitVec.ofNat 64 176) r (16 - r)
      rw [show r + (16 - r) = 16 by omega, hks] at hs
      rw [hm₄, e, xorBytes, hs, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rfl
    have := GcmSiv.ctrPart_step ciph icb x _ (i := b) (n := r) (by omega) hk (by rw [hxl]; exact hx₂)
      (VG.Proof.AesGcmSiv.Arm.frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; omega) (by omega)) hb'
    rwa [hxl, ← hn] at this
  · refine (fT.sub fun q hq => ?_).trans (fw.sub fun q hq => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨State.addr p.D, p.n⟩, by simp, Offset.sub_base _ (by omega)⟩

/-- What `crypt` leaves, from `t`. -/
structure CryptPost (p : VG.Proof.AesGcmSiv.Arm.Prm) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (VG.Proof.AesGcmSiv.Arm.cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t'.mem
  data : bytesAt t'.mem (State.addr p.D) p.n =
    Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem (State.addr p.W) 16)) (bytesAt t.mem (State.addr p.D) p.n)

/-- The memory `cryptHead` leaves: the counter block from the tag. -/
def headMem (m : Mem) (W : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 96) (m.readW W 32) (m.readW (W + BitVec.ofNat 64 4) 32)
    (m.readW (W + BitVec.ofNat 64 8) 32) (m.readW (W + BitVec.ofNat 64 12) 32 ||| 0x80000000#32)

/-- The start of `crypt`: the counter block from the tag, and the data as
the bytes to encrypt. -/
theorem cryptHead_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) (A : VG.Proof.AesGcmSiv.Arm.Args p t.mem) :
    ∃ t₁ : State, runBlock isa cryptHead t = some t₁ ∧ t₁.mem = VG.Proof.AesGcmSiv.Arm.headMem t.mem (State.addr p.W) ∧
      t₁.gpr .r4 = p.D ∧ t₁.gpr .r5 = BitVec.ofNat 32 p.n ∧ t₁.z = decide (p.n / 16 = 0) ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r0, .r1, .r2, .r3, .r4, .r5, .r12] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have rT₀ : InRegions (t.rd ++ t.wr) (State.addr p.W) 4 := by simpa using E.perm.wR (show 0 + 4 ≤ 3760 by decide)
  have rT₁ := E.perm.wR (show 4 + 4 ≤ 3760 by decide)
  have rT₂ := E.perm.wR (show 8 + 4 ≤ 3760 by decide)
  have rT₃ := E.perm.wR (show 12 + 4 ≤ 3760 by decide)
  have w₀ := E.perm.wW (show 96 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 100 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 104 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 108 + 4 ≤ 3760 by decide)
  have a₄ := E.perm.argR' L (k := 4) (by decide)
  have a₈ := E.perm.argR' L (k := 8) (by decide)
  refine ⟨_, by simp only [cryptHead, wholeLeft]; srun [E.r11, E.sp, add_ofNat_zero, L.wA, rT₀, rT₁, rT₂, rT₃, w₀,
    w₁, w₂, w₃, a₄, a₈, A.a4, A.a8], ?_, ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, mem_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, VG.Proof.AesGcmSiv.Arm.headMem,
      Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, VG.Proof.AesGcmSiv.Arm.ofNat_lsr32 L.n_lt]
    rw [z_cmp (by have := L.n_lt; omega) (by decide)]
    rfl

theorem crypt_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) (A : VG.Proof.AesGcmSiv.Arm.Args p t.mem) :
    WP isa crypt t (VG.Proof.AesGcmSiv.Arm.CryptPost p t) := by
  have hw := L.ww
  have hn := L.n_lt
  obtain ⟨t₁, run₁, hm₁, r4₁, r5₁, z₁, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.Arm.cryptHead_ok L E A
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem (State.addr p.D) p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  have f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem := by
    rw [hm₁, VG.Proof.AesGcmSiv.Arm.headMem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have dD : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩ : Region)],
      (⟨State.addr p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hx₁ : bytesAt t₁.mem (State.addr p.D) p.n = bytesAt t.mem (State.addr p.D) p.n :=
    Proof.AesGcm.Arm.bytesAt_frame f₁ dD (by omega)
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 192) p.R =
      Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.Arm.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  have hicb : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 96) 16 =
      Spec.GcmSiv.initialCounter (bytesAt t.mem (State.addr p.W) 16) := by
    rw [hm₁, VG.Proof.AesGcmSiv.Arm.headMem, Proof.Cmac.bytesAt_store4, ← GcmSiv.Words32.initialCounter_words, Proof.Cmac.le4_readW,
      Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, ← Proof.Cmac.bytesAt_split4]
  have h4 := Proof.Cmac.bytesAt_add t₁.mem (State.addr p.W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, add_ofNat_assoc] at h4
  have C₀ : VG.Proof.AesGcmSiv.Arm.CtrSt (State.addr p.W) (Spec.GcmSiv.initialCounter (bytesAt t.mem (State.addr p.W) 16)) 0 t₁.mem := by
    refine ⟨?_, ?_⟩
    · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  have E₁ : VG.Proof.AesGcmSiv.Arm.Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  have fC : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩ : Region)],
      ∃ q' ∈ VG.Proof.AesGcmSiv.Arm.cryR (State.addr p.W) (State.addr p.D) p.n p.SP, Region.Sub q q' :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The whole blocks.
  have hmid : WP isa (.ite .eq (.block []) (.loop cryptBlock .ne)) t₁
      (VG.Proof.AesGcmSiv.Arm.BlocksPost p (Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem (State.addr p.W) 16)) (bytesAt t.mem (State.addr p.D) p.n)
        (p.n / 16) t₁) := by
    refine WP.ite (decide (p.n / 16 = 0)) (eval_eq' z₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : p.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨E₁, rfl, rfl, by rw [r4₁, Nat.mul_zero, add_ofNat_zero], by rw [r5₁, Nat.mul_zero, Nat.sub_zero], C₀,
        by rw [Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁], Frame.refl _ _⟩
    · have h0 : p.n / 16 ≠ 0 := by simpa using hf
      exact VG.Proof.AesGcmSiv.Arm.blocks_ok L E₁ hxl (by omega) r4₁ r5₁ C₀ hx₁ hc₁
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  have r5₂ : t₂.gpr .r5 = BitVec.ofNat 32 (p.n % 16) := by rw [B.r5]; congr 1; omega
  obtain ⟨t₃, run₃, z₃, ho₃, m₃, sp₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa [.cmp .r5 (Impl.AesGcm.Arm.imm 0)] t₂ = some t₃ ∧
      t₃.z = decide (p.n % 16 = 0) ∧ VG.Proof.AesGcmSiv.Arm.Others [] t₂ t₃ ∧ t₃.mem = t₂.mem ∧ t₃.sp = t₂.sp ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr := by
    refine ⟨_, by srun [r5₂], ?_, fun r _ => by rfl, by rfl, by rfl, by rfl, by rfl⟩
    simp only [z_subFlags]
    rw [z_cmp (by omega) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have E₃ : VG.Proof.AesGcmSiv.Arm.Env p t₃ := B.env.of_others ho₃ sp₃ rd₃ wr₃
  refine WP.ite (decide (p.n % 16 = 0)) (eval_eq' z₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨E₃, by rw [rd₃, B.rd, rd₁], by rw [wr₃, B.wr, wr₁], by rw [m₃]; exact (f₁.sub fC).trans B.frame, ?_⟩
    rw [m₃, B.data, show 16 * (p.n / 16) = p.n by omega, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : p.n % 16 ≠ 0 := by simpa using hf
    have hc₂ : Spec.GcmSiv.ctxCiph t₃.mem (State.addr p.W + BitVec.ofNat 64 192) p.R =
        Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R := by
      rw [m₃, VG.Proof.AesGcmSiv.Arm.ciph_cryR L B.frame, hc₁]
    refine WP.mono (VG.Proof.AesGcmSiv.Arm.cryptTail_ok L E₃ hxl (b := p.n / 16) (r := p.n % 16) (by omega) (by omega) (by omega)
      (by rw [ho₃ _ (by simp), B.r4]) (by rw [ho₃ _ (by simp), r5₂]) (m₃ ▸ B.ctr) (by rw [m₃]; exact B.data) hc₂)
      fun t₄ T => ?_
    refine ⟨T.env, by rw [T.rd, rd₃, B.rd, rd₁], by rw [T.wr, wr₃, B.wr, wr₁],
      ((f₁.sub fC).trans (m₃ ▸ B.frame)).trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.Arm.Fn`. -/
section

/-!
# AES-GCM-SIV on ARMv7: comparing the tags, and `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`

Untrusted: everything here is checked by Lean. `cmp` sets `r0` to 1 if the
tags at `W` and `W + 176` are equal and 0 if not, without a branch, as
AES-GCM's `cmpTail` does (`Proof.AesGcm.Arm.cmp_value`) (`cmp_ok`); `mask`
ANDs every byte of the data with `0 − r0`: it keeps the data if `r0` is 1
and zeroes it if `r0` is 0 (`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc)
open VG.Proof.AesGcm.Arm (add_ofNat_assoc add_ofNat_zero eval_eq' eval_ne' z_cmp ofNat_sub32 ofNat_add32
  mem_store gpr_store sp_store rd_store wr_store z_store mem_subFlags z_subFlags gpr_subFlags sp_subFlags rd_subFlags
  wr_subFlags length_bytesAt in_of_covers cmp_value words_eq_iff bytes_words)

theorem cmp_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) :
    ∃ t' : State, runBlock isa cmp t = some t' ∧
      t'.gpr .r0 = (if bytesAt t.mem (State.addr p.W) 16 =
        bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 176) 16 then 1 else 0) ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r0, .r1, .r2] t t' ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₀ : InRegions (t.rd ++ t.wr) (State.addr p.W) 4 := by simpa using E.perm.wR (show 0 + 4 ≤ 3760 by decide)
  have r₁ := E.perm.wR (show 4 + 4 ≤ 3760 by decide)
  have r₂ := E.perm.wR (show 8 + 4 ≤ 3760 by decide)
  have r₃ := E.perm.wR (show 12 + 4 ≤ 3760 by decide)
  have q₀ := E.perm.wR (show 176 + 4 ≤ 3760 by decide)
  have q₁ := E.perm.wR (show 180 + 4 ≤ 3760 by decide)
  have q₂ := E.perm.wR (show 184 + 4 ≤ 3760 by decide)
  have q₃ := E.perm.wR (show 188 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [VG.Impl.AesGcmSiv.Arm.cmp, VG.Impl.AesGcmSiv.Arm.xorW]; srun [E.r11, add_ofNat_zero, L.wA, r₀, r₁, r₂, r₃, q₀, q₁, q₂, q₃], ?_,
    by others_tac, by rfl, by rfl, by rfl, by rfl⟩
  simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  rw [cmp_value, bytes_words, bytes_words]
  simp only [add_ofNat_assoc, add_ofNat_zero, Nat.reduceAdd]
  congr 1
  exact propext (words_eq_iff _ _ _ _ _ _ _ _).symm

/-! ## The mask -/

abbrev maskBody : List Instr :=
  [.ldrb .r12 .r4 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r4 0, Impl.AesGcm.Arm.addI .r4 .r4 1,
    .subs .r5 .r5 (Impl.AesGcm.Arm.imm 1)]

theorem byte_and (a : Byte) (k : BitVec 32) : (a.setWidth 32 &&& k).setWidth 8 = a &&& k.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, show i < 32 by omega, hi, decide_true, Bool.true_and]

/-- Byte `i` at `D`, not yet written. -/
theorem dst_kept' {m : Mem} {D : Addr} {i : Nat} (hi : i < 2 ^ 64) (xs : List Byte)
    (hxs : xs.length = i) : VG.WriteBytes.writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [VG.WriteBytes.writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.lt_irrefl,
    ite_false]

/-- The first `i` bytes at `D`, each ANDed with `k`. -/
abbrev maskBytes (m : Mem) (D : Addr) (k : Byte) (i : Nat) : List Byte := (bytesAt m D i).map (· &&& k)

theorem maskLoop_ok (s : State) {D : BitVec 32} {n : Nat} (h4 : s.gpr .r4 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n)
    (hn1 : 1 ≤ n) (hn : n < 2 ^ 32) (hf : D.toNat + n ≤ 2 ^ 32) (hw : Covers [⟨State.addr D, n⟩] s.wr) :
    WP isa (.loop (.block VG.Proof.AesGcmSiv.Arm.maskBody) .ne) s fun s' =>
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr D) (VG.Proof.AesGcmSiv.Arm.maskBytes s.mem (State.addr D) ((s.gpr .r1).setWidth 8) n) ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r4, .r5, .r12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcmSiv.Arm.maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r4 = D + BitVec.ofNat 32 i ∧
      t.gpr .r5 = BitVec.ofNat 32 (n - i) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (State.addr D) (VG.Proof.AesGcmSiv.Arm.maskBytes s.mem (State.addr D) ((s.gpr .r1).setWidth 8) i) ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r4, .r5, .r12] s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, by omega, by rw [h4, add_ofNat_zero], by rw [h5, Nat.sub_zero],
      by simp [VG.Proof.AesGcmSiv.Arm.maskBytes, bytesAt, VG.WriteBytes.writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r4, r5, mem, g, sp, rd, wr⟩
  have ea : State.addr (D + BitVec.ofNat 32 i) = State.addr D + BitVec.ofNat 64 i := addr_add (by omega)
  have w₁ : InRegions t.wr (State.addr D + BitVec.ofNat 64 i) 1 := by rw [wr]; exact in_of_covers hw hi (by omega)
  have w₂ : InRegions (t.rd ++ t.wr) (State.addr D + BitVec.ofNat 64 i) 1 := Proof.AesGcm.Arm.in_left w₁
  have h1 : t.gpr .r1 = s.gpr .r1 := g _ (by decide)
  obtain ⟨t', run', mem', r4', r5', z', g', sp', rd', wr'⟩ : ∃ t', runBlock isa VG.Proof.AesGcmSiv.Arm.maskBody t = some t' ∧
      t'.mem = t.mem.writeW (State.addr D + BitVec.ofNat 64 i)
        (t.mem (State.addr D + BitVec.ofNat 64 i) &&& (s.gpr .r1).setWidth 8) ∧
      t'.gpr .r4 = D + BitVec.ofNat 32 (i + 1) ∧ t'.gpr .r5 = BitVec.ofNat 32 (n - (i + 1)) ∧
      t'.z = decide (n - (i + 1) = 0) ∧ VG.Proof.AesGcmSiv.Arm.Others [.r4, .r5, .r12] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
    refine ⟨_, by srun [r4, r5, add_ofNat_zero, ea, w₁, w₂], ?_, ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
    · simp only [mem_setReg, mem_store, mem_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, VG.Proof.AesGcmSiv.Arm.byte_and, h1]
    · simp [gpr_setReg, r4, Proof.AesGcm.Arm.add32_ofNat_assoc]
    · simp only [gpr_setReg, gpr_subFlags, ite_true, r5]
      rw [ofNat_sub32 (by omega) (by omega)]; rfl
    · simp only [z_setReg, z_subFlags]
      rw [z_cmp (by omega) (by decide)]
      congr 1; apply propext; omega
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (VG.Proof.AesGcmSiv.Arm.maskBytes s.mem (State.addr D) ((s.gpr .r1).setWidth 8) i).length = i := by
    simp [VG.Proof.AesGcmSiv.Arm.maskBytes, length_bytesAt]
  have hmem : t'.mem = VG.WriteBytes.writeBytes s.mem (State.addr D) (VG.Proof.AesGcmSiv.Arm.maskBytes s.mem (State.addr D) ((s.gpr .r1).setWidth 8) (i + 1)) := by
    rw [mem', mem, VG.Proof.AesGcmSiv.Arm.dst_kept' (by omega) _ hlen]
    simp only [VG.Proof.AesGcmSiv.Arm.maskBytes]
    rw [Proof.AesGcm.Arm.bytesAt_succ, List.map_append, List.map_cons, List.map_nil,
      VG.WriteBytes.writeBytes_snoc s.mem _ _ _ (by rw [List.length_map, length_bytesAt]; omega),
      List.length_map, length_bytesAt]
  have ev := eval_ne' z'
  have gg : VG.Proof.AesGcmSiv.Arm.Others [.r4, .r5, .r12] s t' := fun r hr => by rw [g' r hr, g r hr]
  by_cases he : i + 1 = n
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    exact ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega, r4', r5', hmem, gg,
      by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

theorem map_and_ff (xs : List Byte) : xs.map (· &&& (0#32 - BitVec.ofNat 32 1 : BitVec 32).setWidth 8) = xs := by
  rw [show (0#32 - BitVec.ofNat 32 1 : BitVec 32).setWidth 8 = BitVec.allOnes 8 by decide,
    show (fun x : Byte => x &&& BitVec.allOnes 8) = id from funext fun x => BitVec.and_allOnes, List.map_id]

theorem map_and_zero (xs : List Byte) : xs.map (· &&& (0#32 - BitVec.ofNat 32 0 : BitVec 32).setWidth 8) =
    Spec.GcmSiv.zeros xs.length := by
  rw [show (0#32 - BitVec.ofNat 32 0 : BitVec 32).setWidth 8 = 0#8 by decide]
  simp [Spec.GcmSiv.zeros, List.map_const']

/-- What `mask` leaves, from `t`, when `r0` is whether `c` holds. -/
structure MaskPost (p : VG.Proof.AesGcmSiv.Arm.Prm) (c : Prop) [Decidable c] (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t'
  r0 : t'.gpr .r0 = t.gpr .r0
  frame : Frame [⟨State.addr p.D, p.n⟩] t.mem t'.mem
  data : bytesAt t'.mem (State.addr p.D) p.n = if c then bytesAt t.mem (State.addr p.D) p.n else Spec.GcmSiv.zeros p.n

theorem mask_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) (A : VG.Proof.AesGcmSiv.Arm.Args p t.mem) {c : Prop} [Decidable c]
    (hok : t.gpr .r0 = BitVec.ofNat 32 (if c then 1 else 0)) :
    WP isa mask t (VG.Proof.AesGcmSiv.Arm.MaskPost p c t) := by
  have hn := L.n_lt
  have a₄ := E.perm.argR' L (k := 4) (by decide)
  have a₈ := E.perm.argR' L (k := 8) (by decide)
  obtain ⟨t₁, run₁, r1₁, r4₁, r5₁, z₁, ho₁, hm₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa
      [.ldrSp .r4 4, .ldrSp .r5 8, .mov .r1 (Impl.AesGcm.Arm.imm 0), .dp .sub .r1 .r1 (.reg .r0),
        .cmp .r5 (Impl.AesGcm.Arm.imm 0)] t = some t₁ ∧
      t₁.gpr .r1 = 0#32 - t.gpr .r0 ∧ t₁.gpr .r4 = p.D ∧ t₁.gpr .r5 = BitVec.ofNat 32 p.n ∧
      t₁.z = decide (p.n = 0) ∧ VG.Proof.AesGcmSiv.Arm.Others [.r1, .r4, .r5] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by srun [E.sp, a₄, a₈, A.a4, A.a8], ?_, ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
      rw [z_cmp hn (by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesGcmSiv.Arm.Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  have r0₁ : t₁.gpr .r0 = t.gpr .r0 := ho₁ _ (by decide)
  refine WP.ite (decide (p.n = 0)) (eval_eq' z₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n = 0 := by simpa using ht
    refine WP.block_nil ⟨E₁, r0₁, by rw [hm₁]; exact Frame.refl _ _, ?_⟩
    rw [h0]; split <;> simp [bytesAt, Spec.GcmSiv.zeros]
  · have h0 : p.n ≠ 0 := by simpa using hf
    refine WP.mono (VG.Proof.AesGcmSiv.Arm.maskLoop_ok t₁ r4₁ r5₁ (by omega) hn L.dw E₁.perm.d) fun t₂ ⟨hm₂, ho₂, sp₂, rd₂, wr₂⟩ => ?_
    have hl : (VG.Proof.AesGcmSiv.Arm.maskBytes t₁.mem (State.addr p.D) ((t₁.gpr .r1).setWidth 8) p.n).length = p.n := by
      simp [VG.Proof.AesGcmSiv.Arm.maskBytes, length_bytesAt]
    refine ⟨E₁.of_others ho₂ sp₂ rd₂ wr₂, by rw [ho₂ _ (by decide), r0₁],
      by rw [hm₂, ← hm₁]; exact Proof.AesGcm.Arm.writeBytes_frame' _ hl, ?_⟩
    have e := Proof.AesGcm.Arm.bytesAt_writeBytes_self t₁.mem (State.addr p.D)
      (VG.Proof.AesGcmSiv.Arm.maskBytes t₁.mem (State.addr p.D) ((t₁.gpr .r1).setWidth 8) p.n) (by omega)
    rw [hl] at e
    rw [hm₂, e, r1₁, hok, hm₁]
    simp only [VG.Proof.AesGcmSiv.Arm.maskBytes]
    split
    · exact VG.Proof.AesGcmSiv.Arm.map_and_ff _
    · rw [VG.Proof.AesGcmSiv.Arm.map_and_zero, length_bytesAt]

end VG.Proof.AesGcmSiv.Arm

/-!
## The arguments and the entry

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the public arguments (`prmOf`), how they lie (`lay_of`),
what the state may access (`args_of_seal`, `args_of_open`) and the stack
arguments (`args_of`). `recv` and `tagOut` copy the tag, whose address they
read from the stack (`recv_ok`, `tagOut_ok`). `entry`
loads `W` from the stack, saves our caller's registers at `W + 128`, as
AES-GCM does, and keeps the arguments in `r7`–`r11` (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (arg args bel covers_of_mem covers_left covers_prefix SavedAt savedR argAddr_zero stackArg_eq
  in_off add_ofNat_zero mem_store)

/-- The public arguments of a state. -/
def prmOf (s : State) : VG.Proof.AesGcmSiv.Arm.Prm where
  K := s.gpr .r0
  W := arg s 4
  N := s.gpr .r2
  A := s.gpr .r3
  D := arg s 1
  T := arg s 3
  SP := s.sp
  R := (s.gpr .r1).toNat
  al := (arg s 0).toNat
  n := (arg s 2).toNat

theorem args_eq (s : State) : args s 5 = VG.Proof.AesGcmSiv.Arm.argR s.sp := by
  simp only [args, argAddr_zero]

theorem lay_of {s : State} (h : VG.Proof.AesGcmSiv.Arm.oneLay s) : VG.Proof.AesGcmSiv.Arm.Lay (VG.Proof.AesGcmSiv.Arm.prmOf s) := by
  obtain ⟨sd, sw, nd, nw, ad, aw, td, tw, dw, da, wa, bs, bn, ba, bd, bt, bw, fK, fN, fA, fD, fT, fW, sp8, spf,
    hR⟩ := h
  rw [VG.Proof.AesGcmSiv.Arm.args_eq] at da wa
  exact ⟨fK, fW, fN, fA, fD, BitVec.isLt _, BitVec.isLt _, sp8, spf, fT, sw, sd, nw, nd, aw, ad, dw, tw, td, da, wa,
    bs, bn, ba, bd, bw, hR⟩

/-- The permissions, from the buffers' coverage. -/
theorem perm_of_cov {s : State} (hk : Covers [⟨State.addr (s.gpr .r0), 240⟩] (s.rd ++ s.wr))
    (hN : Covers [⟨State.addr (s.gpr .r2), 12⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨State.addr (arg s 1), (arg s 2).toNat⟩] s.wr) (hW : Covers [⟨State.addr (arg s 4), 3760⟩] s.wr)
    (ha : Covers [args s 5] (s.rd ++ s.wr)) (hT : Covers [⟨State.addr (arg s 3), 16⟩] (s.rd ++ s.wr))
    (hw : ∀ r ∈ s.wr, (args s 5).Disjoint r) : VG.Proof.AesGcmSiv.Arm.Perm (VG.Proof.AesGcmSiv.Arm.prmOf s) s := by
  rw [VG.Proof.AesGcmSiv.Arm.args_eq] at ha hw
  exact ⟨hk, hN, hA, hD, hW, ha, hw, hT⟩

/-- `seal`'s layout and permissions, and its tag, to write. -/
theorem args_of_seal {s : State} (h : VG.Proof.AesGcmSiv.Arm.sealPre s) :
    VG.Proof.AesGcmSiv.Arm.Lay (VG.Proof.AesGcmSiv.Arm.prmOf s) ∧ VG.Proof.AesGcmSiv.Arm.Perm (VG.Proof.AesGcmSiv.Arm.prmOf s) s ∧ Covers [⟨State.addr (arg s 3), 16⟩] s.wr := by
  obtain ⟨hrd, hwr, ta, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), 12⟩,
      ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩, args s 5], Covers [r] (s.rd ++ s.wr) :=
    fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨State.addr (arg s 1), (arg s 2).toNat⟩ : Region), ⟨State.addr (arg s 3), 16⟩,
      ⟨State.addr (arg s 4), 3760⟩], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  obtain ⟨-, -, -, -, -, -, -, -, -, da, wa, -⟩ := id hl
  exact ⟨VG.Proof.AesGcmSiv.Arm.lay_of hl, VG.Proof.AesGcmSiv.Arm.perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (mrd _ (by simp)) (covers_left (mwr _ (by simp))) (fun r hr => by
      rw [hwr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact da.symm
      · exact ta.symm
      · exact wa.symm), mwr _ (by simp)⟩

/-- `open`'s layout and permissions, with its received tag, to read. -/
theorem args_of_open {s : State} (h : VG.Proof.AesGcmSiv.Arm.openPre s) : VG.Proof.AesGcmSiv.Arm.Lay (VG.Proof.AesGcmSiv.Arm.prmOf s) ∧ VG.Proof.AesGcmSiv.Arm.Perm (VG.Proof.AesGcmSiv.Arm.prmOf s) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), 12⟩,
      ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩, ⟨State.addr (arg s 3), 16⟩, args s 5], Covers [r] (s.rd ++ s.wr) :=
    fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨State.addr (arg s 1), (arg s 2).toNat⟩ : Region), ⟨State.addr (arg s 4), 3760⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  obtain ⟨-, -, -, -, -, -, -, -, -, da, wa, -⟩ := id hl
  exact ⟨VG.Proof.AesGcmSiv.Arm.lay_of hl, VG.Proof.AesGcmSiv.Arm.perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (fun r hr => by
      rw [hwr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact da.symm
      · exact wa.symm)⟩

theorem args_of (s : State) : VG.Proof.AesGcmSiv.Arm.Args (VG.Proof.AesGcmSiv.Arm.prmOf s) s.mem :=
  ⟨by simp [VG.Proof.AesGcmSiv.Arm.prmOf, arg, stackArg_eq], by simp [VG.Proof.AesGcmSiv.Arm.prmOf, arg, stackArg_eq], by simp [VG.Proof.AesGcmSiv.Arm.prmOf, arg, stackArg_eq],
    by simp [VG.Proof.AesGcmSiv.Arm.prmOf, arg, stackArg_eq]⟩

/-- What the entry leaves. -/
structure Entered (s s₁ : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env (VG.Proof.AesGcmSiv.Arm.prmOf s) s₁
  saved : SavedAt s₁.mem (VG.Proof.AesGcmSiv.Arm.prmOf s).W s
  frame : Frame [savedR (VG.Proof.AesGcmSiv.Arm.prmOf s).W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- `entry`. -/
theorem entry_ok {s : State} (L : VG.Proof.AesGcmSiv.Arm.Lay (VG.Proof.AesGcmSiv.Arm.prmOf s)) (P : VG.Proof.AesGcmSiv.Arm.Perm (VG.Proof.AesGcmSiv.Arm.prmOf s) s) : WP isa (.block VG.Impl.AesGcmSiv.Arm.entry) s (VG.Proof.AesGcmSiv.Arm.Entered s) := by
  have hw := L.ww
  have ha : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 16)) 4 := P.argR' L (k := 16) (by decide)
  have e16 : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 16)) 32 = (VG.Proof.AesGcmSiv.Arm.prmOf s).W := by simp [VG.Proof.AesGcmSiv.Arm.prmOf, arg, stackArg_eq]
  refine Proof.AesGcm.Arm.entry_ok (off := 16) (by decide) ha (by rw [e16]; omega)
    (by rw [e16]; exact P.w2560) fun s₁ g16 g rd wr sp sv fr => ?_
  rw [e16] at g16 sv fr
  refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun s₂ hs₂ => ?_
  subst hs₂
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, by simp only [sp_setReg]; rw [sp]; rfl,
    P.of_eq (by simp only [rd_setReg]; exact rd) (by simp only [wr_setReg]; exact wr)⟩, by simpa [mem_setReg] using sv,
    by simpa [mem_setReg] using fr, by simp only [rd_setReg]; exact rd, by simp only [wr_setReg]; exact wr⟩
  all_goals simp [gpr_setReg, g, g16, VG.Proof.AesGcmSiv.Arm.prmOf]

/-! ## The tag's copies -/

/-- `tag`'s address, read from the stack. -/
theorem tagArg {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {s : State} (E : VG.Proof.AesGcmSiv.Arm.Env p s) (A : VG.Proof.AesGcmSiv.Arm.Args p s.mem) :
    s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 12)) 32 = p.T ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 12)) 4 := by
  rw [E.sp]; exact ⟨A.a12, E.perm.argR' L (k := 12) (by decide)⟩

/-- A 16-byte block copied by words, all loaded first. -/
theorem bytesAt_copy4 (m : Mem) (S T : Addr) :
    bytesAt (Proof.Cmac.store4 m T (m.readW S 32) (m.readW (S + BitVec.ofNat 64 4) 32)
      (m.readW (S + BitVec.ofNat 64 8) 32) (m.readW (S + BitVec.ofNat 64 12) 32)) T 16 = bytesAt m S 16 := by
  rw [Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.bytesAt_split4]

/-- `recv`: the received tag, at `T`, copied to `W`. -/
theorem recv_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {s : State} (E : VG.Proof.AesGcmSiv.Arm.Env p s) (A : VG.Proof.AesGcmSiv.Arm.Args p s.mem) :
    ∃ s', runBlock isa recv s = some s' ∧ Frame [⟨State.addr p.W, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr p.W) 16 = bytesAt s.mem (State.addr p.T) 16 ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r0, .r1, .r2, .r3, .r12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hT, hTa⟩ := VG.Proof.AesGcmSiv.Arm.tagArg L E A
  have tw := L.tw
  have eT : ∀ k, k < 16 → State.addr (p.T + BitVec.ofNat 32 k) = State.addr p.T + BitVec.ofNat 64 k :=
    fun k hk => addr_add (by omega)
  have t₀ : InRegions (s.rd ++ s.wr) (State.addr p.T) 4 := by
    simpa using in_off (d := 0) (n := 4) E.perm.t (by decide) (by decide)
  have t₁ := in_off (d := 4) (n := 4) E.perm.t (by decide) (by decide)
  have t₂ := in_off (d := 8) (n := 4) E.perm.t (by decide) (by decide)
  have t₃ := in_off (d := 12) (n := 4) E.perm.t (by decide) (by decide)
  have w₀ : InRegions s.wr (State.addr p.W) 4 := by simpa using E.perm.wW (show 0 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 4 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 8 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 12 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [recv]; srun [E.r11, add_ofNat_zero, L.wA, hT, hTa, eT, t₀, t₁, t₂, t₃, w₀, w₁, w₂, w₃],
    ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store]
    exact Proof.Cmac.frame_store4 _ _ _ _ _
  · simp only [mem_setReg, mem_store]
    exact VG.Proof.AesGcmSiv.Arm.bytesAt_copy4 _ _ _

/-- `tagOut`: the tag at `W` copied to `T`, which the state may write. -/
theorem tagOut_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {s : State} (E : VG.Proof.AesGcmSiv.Arm.Env p s) (A : VG.Proof.AesGcmSiv.Arm.Args p s.mem)
    (hTw : Covers [⟨State.addr p.T, 16⟩] s.wr) :
    ∃ s', runBlock isa tagOut s = some s' ∧ Frame [⟨State.addr p.T, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr p.T) 16 = bytesAt s.mem (State.addr p.W) 16 ∧
      VG.Proof.AesGcmSiv.Arm.Others [.r0, .r1, .r2, .r3, .r12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hT, hTa⟩ := VG.Proof.AesGcmSiv.Arm.tagArg L E A
  have tw := L.tw
  have eT : ∀ k, k < 16 → State.addr (p.T + BitVec.ofNat 32 k) = State.addr p.T + BitVec.ofNat 64 k :=
    fun k hk => addr_add (by omega)
  have t₀ : InRegions s.wr (State.addr p.T) 4 := by simpa using in_off (d := 0) (n := 4) hTw (by decide) (by decide)
  have t₁ := in_off (d := 4) (n := 4) hTw (by decide) (by decide)
  have t₂ := in_off (d := 8) (n := 4) hTw (by decide) (by decide)
  have t₃ := in_off (d := 12) (n := 4) hTw (by decide) (by decide)
  have w₀ : InRegions (s.rd ++ s.wr) (State.addr p.W) 4 := by simpa using E.perm.wR (show 0 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wR (show 4 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wR (show 8 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wR (show 12 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [tagOut]; srun [E.r11, add_ofNat_zero, L.wA, hT, hTa, eT, t₀, t₁, t₂, t₃, w₀, w₁, w₂, w₃],
    ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store]
    exact Proof.Cmac.frame_store4 _ _ _ _ _
  · simp only [mem_setReg, mem_store]
    exact VG.Proof.AesGcmSiv.Arm.bytesAt_copy4 _ _ _

/-! ## Regions -/

/-- Proves that a region is disjoint from each of a list of regions: parts
of `W`, the data, the stack below `SP`, or the key schedule. -/
macro "disj_tac" L:term : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true]
  repeat' apply And.intro
  all_goals first
    | (with_reducible refine Lay.w_w $L (.inl ?_) ?_ ?_) <;> decide
    | (with_reducible refine Lay.w_w $L (.inr ?_) ?_ ?_) <;> decide
    | (with_reducible refine Lay.d_w' $L ?_) <;> decide
    | (with_reducible refine (Lay.d_w' $L ?_).symm) <;> decide
    | (with_reducible refine Lay.k_w' $L ?_) <;> decide
    | (with_reducible refine Lay.n_w' $L ?_) <;> decide
    | (with_reducible refine Lay.a_w' $L ?_) <;> decide
    | (with_reducible refine (Lay.bw' $L ?_).symm) <;> decide
    | (with_reducible refine Lay.args_w' $L ?_) <;> decide
    | with_reducible exact Lay.k_d $L
    | with_reducible exact Lay.n_d $L
    | with_reducible exact Lay.a_d $L
    | (with_reducible refine Lay.t_w' $L ?_) <;> decide
    | with_reducible exact Lay.t_d $L
    | with_reducible exact (Lay.t_d $L).symm
    | with_reducible exact (Lay.d_w $L).symm
    | with_reducible exact (Lay.bk $L).symm
    | with_reducible exact (Lay.bn $L).symm
    | with_reducible exact (Lay.ba $L).symm
    | with_reducible exact (Lay.bd $L).symm
    | with_reducible exact Lay.args_below $L
    | with_reducible exact (Lay.d_args $L).symm))

end VG.Proof.AesGcmSiv.Arm

/-!
## `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, and
the restore compute `encryptWith` (RFC 8452 §4) of the arguments
(`seal_wp`), given that the tag input computed with GHASH is the RFC's
(`Proof.GcmSiv.Words.tagInputG`, related to it in `Verified.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.Arm (SavedAt savedR restore_ok)

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
abbrev TagInputEq : Prop := ∀ a n pt d : List Byte, Spec.GcmSiv.tagInput a n pt d = tagInputG a n pt d

theorem bytesAt_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨P, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' P n = bytesAt m P n :=
  Proof.AesGcm.Arm.bytesAt_frame hf hd hn

theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr} {R : Nat}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) (hR : 16 * (R + 1) ≤ 240) :
    Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [VG.Proof.AesGcmSiv.Arm.bytesAt_keep hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

/-- The end: our caller's registers restored. -/
theorem exit_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {s₀ t : State} (E : VG.Proof.AesGcmSiv.Arm.Env p t) (hsp : p.SP = s₀.sp)
    (hs : SavedAt t.mem p.W s₀) :
    WP isa (.block Impl.AesGcm.Arm.restore) t fun s' => abiPreserved s₀ s' ∧ s'.mem = t.mem ∧
      s'.gpr .r0 = t.gpr .r0 :=
  WP.mono (restore_ok E.r11 (by have := L.ww; omega) (covers_left (covers_prefix E.perm.w (by decide))) hs
    (by rw [E.sp, hsp])) fun _ ⟨a, m, r, _⟩ => ⟨a, m, r⟩
where
  covers_left {rd wr rs : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := Proof.AesGcm.Arm.covers_left h
  covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
      Covers [⟨p, n⟩] rs := Proof.AesGcm.Arm.covers_prefix h hn

/-- A run, which keeps the permissions. -/
theorem WP.rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', e, hq⟩ := h
  exact ⟨t, s', e, hq, (Exec.rdwr e).1, (Exec.rdwr e).2.1⟩

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (hti : VG.Proof.AesGcmSiv.Arm.TagInputEq) {s : State} (h : VG.Proof.AesGcmSiv.Arm.sealPre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealArm.post s s' := by
  obtain ⟨L, P, hTw⟩ := VG.Proof.AesGcmSiv.Arm.args_of_seal h
  have hRb := L.rounds_le
  have hn := L.n_lt
  have A₀ := VG.Proof.AesGcmSiv.Arm.args_of s
  refine WP.seq (WP.mono (WP.rdwr (VG.Proof.AesGcmSiv.Arm.entry_ok L P)) fun s₁ ⟨En, _, w₁⟩ => ?_)
  have A₁ : VG.Proof.AesGcmSiv.Arm.Args (VG.Proof.AesGcmSiv.Arm.prmOf s) s₁.mem := A₀.frame L En.frame (by disj_tac L)
  -- The keys.
  refine WP.seq (WP.mono (WP.rdwr (VG.Proof.AesGcmSiv.Arm.keys_ok L En.env)) fun s₂ ⟨Ky, _, w₂⟩ => ?_)
  have A₂ : VG.Proof.AesGcmSiv.Arm.Args (VG.Proof.AesGcmSiv.Arm.prmOf s) s₂.mem := A₁.frame L Ky.frame (by disj_tac L)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.polyval_ok L Ky.env A₂ Ky.hkey Ky.acc) fun s₃ Po => ?_)
  have A₃ : VG.Proof.AesGcmSiv.Arm.Args (VG.Proof.AesGcmSiv.Arm.prmOf s) s₃.mem := A₂.frame L Po.frame (by disj_tac L)
  -- The tag.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.tag_ok L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  have A₄ : VG.Proof.AesGcmSiv.Arm.Args (VG.Proof.AesGcmSiv.Arm.prmOf s) s₄.mem := A₃.frame L Tg.frame (by disj_tac L)
  -- Counter mode.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.crypt_ok L Tg.env A₄) fun s₅ Cr => ?_)
  have A₅ : VG.Proof.AesGcmSiv.Arm.Args (VG.Proof.AesGcmSiv.Arm.prmOf s) s₅.mem := A₄.frame L Cr.frame (by disj_tac L)
  -- The copy of the tag, and `restore`.
  have w₅ : s₅.wr = s.wr := by rw [Cr.wr, Tg.wr, Po.wr, w₂, w₁]
  obtain ⟨s₆, run₆, fT, hT₆, ho₆, sp₆, rd₆, wr₆⟩ := VG.Proof.AesGcmSiv.Arm.tagOut_ok L Cr.env A₅ (by rw [w₅]; exact hTw)
  have E₆ : VG.Proof.AesGcmSiv.Arm.Env (VG.Proof.AesGcmSiv.Arm.prmOf s) s₆ := Cr.env.of_others ho₆ sp₆ rd₆ wr₆
  have sv₆ : SavedAt s₆.mem (VG.Proof.AesGcmSiv.Arm.prmOf s).W s :=
    (((((En.saved.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame
      (by disj_tac L)).frame Cr.frame (by disj_tac L))).frame fT fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (L.t_w' (show 128 + 36 ≤ 3760 by decide)).symm
  refine WP.block_append (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  refine WP.mono (VG.Proof.AesGcmSiv.Arm.exit_ok L E₆ rfl sv₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).K) (VG.Proof.AesGcmSiv.Arm.prmOf s).R)
      (Spec.GcmSiv.keyLen (VG.Proof.AesGcmSiv.Arm.prmOf s).R) (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12)
      (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n) (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).A) (VG.Proof.AesGcmSiv.Arm.prmOf s).al) =
    (bytesAt s'.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n, bytesAt s'.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).T) 16)
  rw [hm, hT₆, VG.Proof.AesGcmSiv.Arm.bytesAt_keep fT (by disj_tac L) (by omega)]
  -- What the pieces read.
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).K) (VG.Proof.AesGcmSiv.Arm.prmOf s).R =
      Spec.GcmSiv.ctxCiph s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).K) (VG.Proof.AesGcmSiv.Arm.prmOf s).R :=
    VG.Proof.AesGcmSiv.Arm.ciph_keep En.frame (by disj_tac L) hRb
  have n₁ : bytesAt s₁.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12 = bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12 :=
    VG.Proof.AesGcmSiv.Arm.bytesAt_keep En.frame (by disj_tac L) (by decide)
  have n₂ : bytesAt s₂.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12 = bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12 := by
    rw [VG.Proof.AesGcmSiv.Arm.bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  have a₂ : bytesAt s₂.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).A) (VG.Proof.AesGcmSiv.Arm.prmOf s).al = bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).A) (VG.Proof.AesGcmSiv.Arm.prmOf s).al := by
    rw [VG.Proof.AesGcmSiv.Arm.bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega),
      VG.Proof.AesGcmSiv.Arm.bytesAt_keep En.frame (by disj_tac L) (by have := L.al_lt; omega)]
  have d₂ : bytesAt s₂.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n = bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n := by
    rw [VG.Proof.AesGcmSiv.Arm.bytesAt_keep Ky.frame (by disj_tac L) (by omega), VG.Proof.AesGcmSiv.Arm.bytesAt_keep En.frame (by disj_tac L) (by omega)]
  have d₄ : bytesAt s₄.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n = bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n := by
    rw [VG.Proof.AesGcmSiv.Arm.bytesAt_keep Tg.frame (by disj_tac L) (by omega), VG.Proof.AesGcmSiv.Arm.bytesAt_keep Po.frame (by disj_tac L) (by omega), d₂]
  have key₃ : Spec.GcmSiv.ctxCiph s₃.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 192) (VG.Proof.AesGcmSiv.Arm.prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 192) (VG.Proof.AesGcmSiv.Arm.prmOf s).R :=
    VG.Proof.AesGcmSiv.Arm.ciph_keep Po.frame (by disj_tac L) hRb
  have key₄ : Spec.GcmSiv.ctxCiph s₄.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 192) (VG.Proof.AesGcmSiv.Arm.prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 192) (VG.Proof.AesGcmSiv.Arm.prmOf s).R := by
    rw [VG.Proof.AesGcmSiv.Arm.ciph_keep Tg.frame (by disj_tac L) hRb, key₃]
  have t₅ : bytesAt s₅.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s₄.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 0) 16 :=
    VG.Proof.AesGcmSiv.Arm.bytesAt_keep Cr.frame (by disj_tac L) (by decide)
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
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).K) (VG.Proof.AesGcmSiv.Arm.prmOf s).R)
    (Spec.GcmSiv.keyLen (VG.Proof.AesGcmSiv.Arm.prmOf s).R) (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

end VG.Proof.AesGcmSiv.Arm

/-!
## `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the copy of the
received tag to `W`, the keys, counter mode on the data from it, POLYVAL of
the result and the tag input, its tag at `W + 176`, the comparison, the mask and the restore
compute `decryptWith` (RFC 8452 §5) of the arguments (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.Arm (SavedAt savedR)

theorem decrypt_eq (hti : VG.Proof.AesGcmSiv.Arm.TagInputEq) (ciph : Spec.GcmSiv.Cipher) (kl : Nat) (nonce ct aad tag : List Byte) :
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

theorem ite_ofNat (c : Prop) [Decidable c] :
    (if c then (1 : BitVec 32) else 0) = BitVec.ofNat 32 (if c then 1 else 0) := by
  split <;> rfl

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (hti : VG.Proof.AesGcmSiv.Arm.TagInputEq) {s : State} (h : VG.Proof.AesGcmSiv.Arm.openPre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openArm.post s s' := by
  obtain ⟨L, P⟩ := VG.Proof.AesGcmSiv.Arm.args_of_open h
  have hRb := L.rounds_le
  have hn := L.n_lt
  have A₀ := VG.Proof.AesGcmSiv.Arm.args_of s
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.entry_ok L P) fun s₀ En₀ => ?_)
  have A₀' : VG.Proof.AesGcmSiv.Arm.Args (VG.Proof.AesGcmSiv.Arm.prmOf s) s₀.mem := A₀.frame L En₀.frame (by disj_tac L)
  -- The received tag, copied to `W`.
  obtain ⟨s₁, run₁, fR, hR₁, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.Arm.recv_ok L En₀.env A₀'
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have fR' : Frame [⟨State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 0, 16⟩] s₀.mem s₁.mem := by
    rw [BitVec.add_zero]; exact fR
  have E₁ : VG.Proof.AesGcmSiv.Arm.Env (VG.Proof.AesGcmSiv.Arm.prmOf s) s₁ := En₀.env.of_others ho₁ sp₁ rd₁ wr₁
  have sv₁ : SavedAt s₁.mem (VG.Proof.AesGcmSiv.Arm.prmOf s).W s := En₀.saved.frame fR' (by disj_tac L)
  have f₁ : Frame [savedR (VG.Proof.AesGcmSiv.Arm.prmOf s).W, ⟨State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 0, 16⟩] s.mem s₁.mem :=
    (En₀.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  have A₁ : VG.Proof.AesGcmSiv.Arm.Args (VG.Proof.AesGcmSiv.Arm.prmOf s) s₁.mem := A₀'.frame L fR' (by disj_tac L)
  have hT₁ : bytesAt s₁.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).T) 16 := by
    rw [BitVec.add_zero, hR₁, VG.Proof.AesGcmSiv.Arm.bytesAt_keep En₀.frame (by disj_tac L) (by decide)]
  -- The keys.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.keys_ok L E₁) fun s₂ Ky => ?_)
  have A₂ : VG.Proof.AesGcmSiv.Arm.Args (VG.Proof.AesGcmSiv.Arm.prmOf s) s₂.mem := A₁.frame L Ky.frame (by disj_tac L)
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.crypt_ok L Ky.env A₂) fun s₃ Cr => ?_)
  have A₃ : VG.Proof.AesGcmSiv.Arm.Args (VG.Proof.AesGcmSiv.Arm.prmOf s) s₃.mem := A₂.frame L Cr.frame (by disj_tac L)
  have a₃ : bytesAt s₃.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 16) 16 =
      bytesAt s₂.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 16) 16 :=
    VG.Proof.AesGcmSiv.Arm.bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  have hG₃ : Spec.Gcm.blockAt s₃.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 64) =
      GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₃.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 16) 16)) := by
    rw [Proof.AesGcm.Arm.blockAt_frame Cr.frame (by disj_tac L), Ky.hkey, a₃]
  have hY₃ : Spec.Gcm.blockAt s₃.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 80) = 0 := by
    rw [Proof.AesGcm.Arm.blockAt_frame Cr.frame (by disj_tac L), Ky.acc]
  -- POLYVAL of the plaintext and the tag input.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.polyval_ok L Cr.env A₃ hG₃ hY₃) fun s₄ Po => ?_)
  have A₄ : VG.Proof.AesGcmSiv.Arm.Args (VG.Proof.AesGcmSiv.Arm.prmOf s) s₄.mem := A₃.frame L Po.frame (by disj_tac L)
  -- Its tag at `W + 176`.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.tag_ok L Po.env (o := 176) (by decide)) fun s₅ Tg => ?_)
  have A₅ : VG.Proof.AesGcmSiv.Arm.Args (VG.Proof.AesGcmSiv.Arm.prmOf s) s₅.mem := A₄.frame L Tg.frame (by disj_tac L)
  -- The comparison.
  obtain ⟨s₆, run₆, r0₆, ho₆, hm₆, sp₆, rd₆, wr₆⟩ := VG.Proof.AesGcmSiv.Arm.cmp_ok L Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : VG.Proof.AesGcmSiv.Arm.Env (VG.Proof.AesGcmSiv.Arm.prmOf s) s₆ := Tg.env.of_others ho₆ sp₆ rd₆ wr₆
  rw [VG.Proof.AesGcmSiv.Arm.ite_ofNat] at r0₆
  -- The mask.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.Arm.mask_ok L E₆ (hm₆ ▸ A₅) r0₆) fun s₇ Mk => ?_)
  -- The restore.
  have sv₇ : SavedAt s₇.mem (VG.Proof.AesGcmSiv.Arm.prmOf s).W s := by
    have := ((((sv₁.frame Ky.frame (by disj_tac L)).frame Cr.frame (by disj_tac L)).frame Po.frame
      (by disj_tac L)).frame Tg.frame (by disj_tac L))
    rw [← hm₆] at this
    exact this.frame Mk.frame (by disj_tac L)
  refine WP.mono (VG.Proof.AesGcmSiv.Arm.exit_ok L Mk.env rfl sv₇) fun s' ⟨ga, hm, hr0⟩ => ⟨ga, ?_⟩
  -- What the pieces read.
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).K) (VG.Proof.AesGcmSiv.Arm.prmOf s).R =
      Spec.GcmSiv.ctxCiph s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).K) (VG.Proof.AesGcmSiv.Arm.prmOf s).R :=
    VG.Proof.AesGcmSiv.Arm.ciph_keep f₁ (by disj_tac L) hRb
  have n₁ : bytesAt s₁.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12 = bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12 :=
    VG.Proof.AesGcmSiv.Arm.bytesAt_keep f₁ (by disj_tac L) (by decide)
  have n₃ : bytesAt s₃.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12 = bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12 := by
    rw [VG.Proof.AesGcmSiv.Arm.bytesAt_keep Cr.frame (by disj_tac L) (by decide), VG.Proof.AesGcmSiv.Arm.bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  have a₃' : bytesAt s₃.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).A) (VG.Proof.AesGcmSiv.Arm.prmOf s).al =
      bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).A) (VG.Proof.AesGcmSiv.Arm.prmOf s).al := by
    rw [VG.Proof.AesGcmSiv.Arm.bytesAt_keep Cr.frame (by disj_tac L) (by have := L.al_lt; omega),
      VG.Proof.AesGcmSiv.Arm.bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega),
      VG.Proof.AesGcmSiv.Arm.bytesAt_keep f₁ (by disj_tac L) (by have := L.al_lt; omega)]
  have d₂ : bytesAt s₂.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n = bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n := by
    rw [VG.Proof.AesGcmSiv.Arm.bytesAt_keep Ky.frame (by disj_tac L) (by omega), VG.Proof.AesGcmSiv.Arm.bytesAt_keep f₁ (by disj_tac L) (by omega)]
  have tag₂ : bytesAt s₂.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).T) 16 := by
    rw [VG.Proof.AesGcmSiv.Arm.bytesAt_keep Ky.frame (by disj_tac L) (by decide), hT₁]
  have tag₅ : bytesAt s₅.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).T) 16 := by
    rw [VG.Proof.AesGcmSiv.Arm.bytesAt_keep Tg.frame (by disj_tac L) (by decide), VG.Proof.AesGcmSiv.Arm.bytesAt_keep Po.frame (by disj_tac L) (by decide),
      VG.Proof.AesGcmSiv.Arm.bytesAt_keep Cr.frame (by disj_tac L) (by decide), tag₂]
  rw [BitVec.add_zero] at tag₂ tag₅
  have ci₄ : Spec.GcmSiv.ctxCiph s₄.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 192) (VG.Proof.AesGcmSiv.Arm.prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).W + BitVec.ofNat 64 192) (VG.Proof.AesGcmSiv.Arm.prmOf s).R := by
    rw [VG.Proof.AesGcmSiv.Arm.ciph_keep Po.frame (by disj_tac L) hRb, VG.Proof.AesGcmSiv.Arm.ciph_cryR L Cr.frame]
  have d₆ : bytesAt s₆.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n = bytesAt s₃.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n := by
    rw [hm₆, VG.Proof.AesGcmSiv.Arm.bytesAt_keep Tg.frame (by disj_tac L) (by omega), VG.Proof.AesGcmSiv.Arm.bytesAt_keep Po.frame (by disj_tac L) (by omega)]
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have pt₃ := Cr.data
  rw [tag₂, d₂, ci] at pt₃
  have po := Po.out
  rw [a₃, ← au, n₃, a₃', pt₃] at po
  have tg := Tg.out
  rw [ci₄, ci, po] at tg
  have md := Mk.data
  rw [hm₆, tg, tag₅] at md
  rw [← hm₆, d₆, pt₃] at md
  have ax : s'.gpr .r0 = s₆.gpr .r0 := by rw [hr0, Mk.r0]
  rw [r0₆, tg, tag₅] at ax
  show VG.Proof.AesGcmSiv.Arm.openPost (VG.Proof.AesGcmSiv.Arm.openResult s) s' (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n
  have hdec : VG.Proof.AesGcmSiv.Arm.openResult s =
      let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).K) (VG.Proof.AesGcmSiv.Arm.prmOf s).R)
        (Spec.GcmSiv.keyLen (VG.Proof.AesGcmSiv.Arm.prmOf s).R) (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12)
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12)
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).T) 16))
            (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n)) (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).A) (VG.Proof.AesGcmSiv.Arm.prmOf s).al)) =
          bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).T) 16 then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).T) 16))
          (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n))
      else none := VG.Proof.AesGcmSiv.Arm.decrypt_eq hti _ _ _ _ _ _
  simp only at hdec
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).K) (VG.Proof.AesGcmSiv.Arm.prmOf s).R)
    (Spec.GcmSiv.keyLen (VG.Proof.AesGcmSiv.Arm.prmOf s).R) (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12) = dk at md ax hdec
  rw [hdec]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).T) 16))
        (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n)) (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).A) (VG.Proof.AesGcmSiv.Arm.prmOf s).al)) =
      bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).T) 16
  · refine VG.Proof.AesGcmSiv.Arm.openPost_some (ite_eq_left_of_eq_true _ _ (eq_true hc)) ?_ ?_
    · rw [ax]; simp only [hc, ↓reduceIte]; rfl
    · rw [hm, md]; simp only [hc, ↓reduceIte]
  · have hc' : ¬bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).T) 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1
        (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).N) 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).T) 16))
          (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).D) (VG.Proof.AesGcmSiv.Arm.prmOf s).n)) (bytesAt s.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf s).A) (VG.Proof.AesGcmSiv.Arm.prmOf s).al)) :=
      Ne.symm hc
    refine VG.Proof.AesGcmSiv.Arm.openPost_none (ite_eq_right_of_eq_false _ _ (eq_false hc)) ?_ ?_
    · rw [ax]; simp only [hc', ↓reduceIte]; rfl
    · rw [hm, md]; simp only [hc', ↓reduceIte]

end VG.Proof.AesGcmSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.Arm.PolyvalCT`. -/
section

/-!
# AES-GCM-SIV on ARMv7: relating two runs, the keys and POLYVAL

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (`Eq2`) piece by piece, as the AArch64
ones do (`Proof.AesGcmSiv.AArch64`): the code between calls by the taint
analysis, from the registers that hold the public arguments in both runs
(`Env`, `rel_env`), those the pieces pin to the same values, and the stack
arguments, which both runs hold and nothing writes (`Args`, `ArgOk`,
`rel_envArg`); each call by its callee's proof; a branch on a flag both
runs agree on (`rel_ite`); a loop whose condition both runs agree on
(`rel_loop`); and the next piece from the states the correctness proofs
describe (`rel_seq`).
-/

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm
open VG.Proof.AesGcm.Arm (CtrCall GhCall KeyCall ctr_rel gh_rel key_rel)

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) c₁ VG.Proof.AesGcmSiv.Arm.TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 τ₁ τ₂) c₂ VG.Proof.AesGcmSiv.Arm.TT) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) (.seq c₁ c₂) VG.Proof.AesGcmSiv.Arm.TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Then, towards any relation of the final states. -/
theorem rel_seqQ {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) c₁ VG.Proof.AesGcmSiv.Arm.TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 τ₁ τ₂) c₂ Q) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) (.seq c₁ c₂) Q := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- The last piece, with what correctness says of each run's final state. -/
theorem rel_wpQ {c : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h : RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) c VG.Proof.AesGcmSiv.Arm.TT) (w₁ : WP isa c σ₁ F₁) (w₂ : WP isa c σ₂ F₂)
    (hq : ∀ a b, F₁ a → F₂ b → Q a b) : RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) c Q :=
  (h.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono
    (fun _ _ h => h) fun a b h => hq a b h.2.1 h.2.2

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) c VG.Proof.AesGcmSiv.Arm.TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := VG.Arm.taint) _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact Taint.agree_ofRegs hr) hc

/-- An empty block. -/
theorem rel_skip {σ₁ σ₂ : State} : RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) (.block []) VG.Proof.AesGcmSiv.Arm.TT :=
  VG.Proof.AesGcmSiv.Arm.rel_taint [] (by simp) ⟨.block [], rfl⟩

/-- Code the taint analysis checks, from registers the two runs agree on and
the first `n` bytes of stack arguments, the same in both runs and apart from
the writable regions. -/
theorem rel_arg {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (n : Nat) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hsp : σ₁.sp = σ₂.sp)
    (hw₁ : σ₁.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ σ₁.wr, Region.Disjoint ⟨State.addr σ₁.sp, n⟩ r)
    (hw₂ : σ₂.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ σ₂.wr, Region.Disjoint ⟨State.addr σ₂.sp, n⟩ r)
    (hm : ∀ k < n, σ₁.mem (VG.Arm.Taint.argByte σ₁ k) = σ₂.mem (VG.Arm.Taint.argByte σ₂ k))
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint rs n) c h).isSome = true) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) c VG.Proof.AesGcmSiv.Arm.TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := VG.Arm.taint) _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact agree_argTaint hr hsp hw₁ hw₂ hm) hc

theorem rel_gh {σ₁ σ₂ : State} {H Y D S : BitVec 32} {n : Nat} (h₁ : GhCall σ₁ H Y D S n)
    (h₂ : GhCall σ₂ H Y D S n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) Impl.AesGcm.Arm.ghFrame VG.Proof.AesGcmSiv.Arm.TT :=
  gh_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨H, Y, D, S, n, h₁, h₂, hsp⟩

theorem rel_ctr {σ₁ σ₂ : State} {K C D S : BitVec 32} {R n : Nat} (h₁ : CtrCall σ₁ K C D S R n)
    (h₂ : CtrCall σ₂ K C D S R n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) Impl.AesGcm.Arm.ctrFrame VG.Proof.AesGcmSiv.Arm.TT :=
  ctr_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩

theorem rel_key {σ₁ σ₂ : State} {K C S : BitVec 32} {L : Nat} (h₁ : KeyCall σ₁ K C S L)
    (h₂ : KeyCall σ₂ K C S L) : RelCT isa (Eq2 σ₁ σ₂) (.call "vg_aes_expand_key_scratch" Impl.Aes.Arm.expandKey) TT :=
  key_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, S, L, h₁, h₂⟩

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) t VG.Proof.AesGcmSiv.Arm.TT)
    (hf : b = false → RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) e VG.Proof.AesGcmSiv.Arm.TT) : RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) (.ite c t e) VG.Proof.AesGcmSiv.Arm.TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- A loop step in two runs: the condition agrees, and the runs are related
anew while it loops. -/
theorem rel_loop {body : Prog isa} {c : Cond} (I : Nat → State → State → Prop)
    (hstep : ∀ n σ₁ σ₂, I n σ₁ σ₂ → RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) body fun s₁ s₂ => isa.eval c s₁ = isa.eval c s₂ ∧
      (isa.eval c s₁ = some true → ∃ m < n, I m s₁ s₂))
    (n : Nat) {σ₁ σ₂ : State} (h : I n σ₁ σ₂) : RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) (.loop body c) VG.Proof.AesGcmSiv.Arm.TT := by
  refine (RelCT.loop (Q := VG.Proof.AesGcmSiv.Arm.TT) I (fun n => ?_) n).mono (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact h)
    fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hc, hi⟩ := hstep n s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂
  exact ⟨ht, hc, fun _ => trivial, hi⟩

/-- Constant time, from related runs from every pair of states. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) c VG.Proof.AesGcmSiv.Arm.TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The public arguments -/

theorem Env.agree {p : VG.Proof.AesGcmSiv.Arm.Prm} {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.Arm.Env p τ₂) :
    ∀ r ∈ VG.Proof.AesGcmSiv.Arm.envRegs, τ₁.gpr r = τ₂.gpr r := by
  intro r hr
  simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [E₁.r7, E₂.r7]
  · rw [E₁.r8, E₂.r8]
  · rw [E₁.r9, E₂.r9]
  · rw [E₁.r10, E₂.r10]
  · rw [E₁.r11, E₂.r11]

theorem Env.sp_eq {p : VG.Proof.AesGcmSiv.Arm.Prm} {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.Arm.Env p τ₂) : τ₁.sp = τ₂.sp := by
  rw [E₁.sp, E₂.sp]

/-- The registers holding the public arguments, and `rs`. -/
abbrev pubRegs (rs : List Reg) : List Reg := VG.Proof.AesGcmSiv.Arm.envRegs ++ rs

/-- Code the taint analysis checks, from the registers holding the public
arguments and the registers `rs` the two runs agree on. -/
theorem rel_env {c : Prog isa} {p : VG.Proof.AesGcmSiv.Arm.Prm} {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.Arm.Env p τ₂) (rs : List Reg)
    (hr : ∀ r ∈ rs, τ₁.gpr r = τ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs rs)) c h).isSome = true) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 τ₁ τ₂) c VG.Proof.AesGcmSiv.Arm.TT :=
  VG.Proof.AesGcmSiv.Arm.rel_taint (VG.Proof.AesGcmSiv.Arm.pubRegs rs) (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) hc

theorem argByte_eq {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {s₁ s₂ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p s₁) (E₂ : VG.Proof.AesGcmSiv.Arm.Env p s₂) (A₁ : VG.Proof.AesGcmSiv.Arm.Args p s₁.mem)
    (A₂ : VG.Proof.AesGcmSiv.Arm.Args p s₂.mem) : ∀ k < 12, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k) := by
  refine argMem_of (j := 3) (E₁.sp_eq E₂) (by rw [E₁.sp]; have := L.spf; omega) fun i hi => ?_
  have e : ∀ {s : State}, VG.Proof.AesGcmSiv.Arm.Env p s → VG.Proof.AesGcmSiv.Arm.Args p s.mem → stackArg s i = if i = 0 then BitVec.ofNat 32 p.al
      else if i = 1 then p.D else BitVec.ofNat 32 p.n := fun {s} E A => by
    rw [Proof.AesGcm.Arm.stackArg_eq, E.sp]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact A.a0
    · exact A.a4
    · exact A.a8
  rw [e E₁ A₁, e E₂ A₂]

/-- Code the taint analysis checks, from the registers holding the public
arguments, the registers `rs` the two runs agree on, and the first three
stack arguments. -/
theorem rel_envArg {c : Prog isa} {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.Arm.Env p τ₂)
    (A₁ : VG.Proof.AesGcmSiv.Arm.Args p τ₁.mem) (A₂ : VG.Proof.AesGcmSiv.Arm.Args p τ₂.mem) (rs : List Reg)
    (hr : ∀ r ∈ rs, τ₁.gpr r = τ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesGcmSiv.Arm.pubRegs rs) 12) c h).isSome = true) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 τ₁ τ₂) c VG.Proof.AesGcmSiv.Arm.TT := by
  have spf := L.spf
  have hw : ∀ {τ : State}, VG.Proof.AesGcmSiv.Arm.Env p τ →
      τ.sp.toNat + 12 ≤ 2 ^ 32 ∧ ∀ r ∈ τ.wr, Region.Disjoint ⟨State.addr τ.sp, 12⟩ r := fun E =>
    ⟨by rw [E.sp]; omega, fun r hr => by rw [E.sp]; exact (E.perm.argw r hr).sub_left (Region.sub_prefix (by decide))⟩
  exact VG.Proof.AesGcmSiv.Arm.rel_arg (VG.Proof.AesGcmSiv.Arm.pubRegs rs) 12 (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) (E₁.sp_eq E₂) (hw E₁) (hw E₂) (VG.Proof.AesGcmSiv.Arm.argByte_eq L E₁ E₂ A₁ A₂) hc

theorem argByte_eq16 {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {s₁ s₂ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p s₁) (E₂ : VG.Proof.AesGcmSiv.Arm.Env p s₂) (A₁ : VG.Proof.AesGcmSiv.Arm.Args p s₁.mem)
    (A₂ : VG.Proof.AesGcmSiv.Arm.Args p s₂.mem) : ∀ k < 16, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k) := by
  refine argMem_of (j := 4) (E₁.sp_eq E₂) (by rw [E₁.sp]; have := L.spf; omega) fun i hi => ?_
  have e : ∀ {s : State}, VG.Proof.AesGcmSiv.Arm.Env p s → VG.Proof.AesGcmSiv.Arm.Args p s.mem → stackArg s i = if i = 0 then BitVec.ofNat 32 p.al
      else if i = 1 then p.D else if i = 2 then BitVec.ofNat 32 p.n else p.T := fun {s} E A => by
    rw [Proof.AesGcm.Arm.stackArg_eq, E.sp]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact A.a0
    · exact A.a4
    · exact A.a8
    · exact A.a12
  rw [e E₁ A₁, e E₂ A₂]

/-- Code the taint analysis checks, from the registers holding the public
arguments, the registers `rs` the two runs agree on, and the first four
stack arguments (with `tag`). -/
theorem rel_envArg16 {c : Prog isa} {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.Arm.Env p τ₂)
    (A₁ : VG.Proof.AesGcmSiv.Arm.Args p τ₁.mem) (A₂ : VG.Proof.AesGcmSiv.Arm.Args p τ₂.mem) (rs : List Reg)
    (hr : ∀ r ∈ rs, τ₁.gpr r = τ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesGcmSiv.Arm.pubRegs rs) 16) c h).isSome = true) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 τ₁ τ₂) c VG.Proof.AesGcmSiv.Arm.TT := by
  have spf := L.spf
  have hw : ∀ {τ : State}, VG.Proof.AesGcmSiv.Arm.Env p τ →
      τ.sp.toNat + 16 ≤ 2 ^ 32 ∧ ∀ r ∈ τ.wr, Region.Disjoint ⟨State.addr τ.sp, 16⟩ r := fun E =>
    ⟨by rw [E.sp]; omega, fun r hr => by rw [E.sp]; exact (E.perm.argw r hr).sub_left (Region.sub_prefix (by decide))⟩
  exact VG.Proof.AesGcmSiv.Arm.rel_arg (VG.Proof.AesGcmSiv.Arm.pubRegs rs) 16 (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) (E₁.sp_eq E₂) (hw E₁) (hw E₂) (VG.Proof.AesGcmSiv.Arm.argByte_eq16 L E₁ E₂ A₁ A₂) hc

end VG.Proof.AesGcmSiv.Arm

/-!
## The keys are constant time

Untrusted: everything here is checked by Lean. Both runs derive the same
number of blocks (`rounds / 2 − 1`, from `r8`); the code around the calls
passes the taint analysis, and each call has the same arguments in both
runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Proof.AesGcm.Arm (CtrCall ctr_call KeyCall key_call eval_ne')

/-- A run of `derive` before block `i`. -/
structure DC (p : VG.Proof.AesGcmSiv.Arm.Prm) (i : Nat) (t : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t
  r4 : t.gpr .r4 = BitVec.ofNat 32 i

theorem derA_wp {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {i : Nat} {t : State} (h : VG.Proof.AesGcmSiv.Arm.DC p i t) :
    WP isa (.block deriveBlock) t fun t₁ =>
      CtrCall t₁ p.K (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 176) (p.W + BitVec.ofNat 32 1712) p.R 1 ∧
        VG.Proof.AesGcmSiv.Arm.DC p i t₁ := by
  obtain ⟨t₁, run₁, -, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.Arm.derArgs_ok L h.env h.r4
  have E₁ : VG.Proof.AesGcmSiv.Arm.Env p t₁ := h.env.of_others ho₁ sp₁ rd₁ wr₁
  exact WP.of_runBlock ⟨t₁, run₁, VG.Proof.AesGcmSiv.Arm.derCall L E₁ r0 r1 r2 r3 r12 lr, E₁, by rw [ho₁ _ (by decide), h.r4]⟩

theorem derC_wp {p : VG.Proof.AesGcmSiv.Arm.Prm} {i : Nat} {t : State}
    (h : CtrCall t p.K (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 176) (p.W + BitVec.ofNat 32 1712) p.R 1 ∧
      VG.Proof.AesGcmSiv.Arm.DC p i t) :
    WP isa Impl.AesGcm.Arm.ctrFrame t (VG.Proof.AesGcmSiv.Arm.DC p i) :=
  WP.mono (ctr_call h.1) fun _ P =>
    ⟨h.2.env.of_saved P.saved P.sp P.rd P.wr, by rw [P.saved _ (by decide) (by decide), h.2.r4]⟩

theorem derP_wp {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {i : Nat} (hi : i < p.R / 2 - 1) {t : State} (h : VG.Proof.AesGcmSiv.Arm.DC p i t) :
    WP isa (.block derivePost) t fun t' => VG.Proof.AesGcmSiv.Arm.DC p (i + 1) t' ∧ t'.z = decide (i + 1 = p.R / 2 - 1) := by
  obtain ⟨t', run', -, r4', z', ho', sp', rd', wr'⟩ := VG.Proof.AesGcmSiv.Arm.derPost_ok L h.env hi h.r4
  exact WP.of_runBlock ⟨t', run', ⟨h.env.of_others ho' sp' rd' wr', r4'⟩, z'⟩

theorem derA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [.r4])) (.block deriveBlock) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem derP_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [.r4])) (.block derivePost) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem der0_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs []))
    (.block [.mov .r4 (Impl.AesGcm.Arm.imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

/-- `derive`, in two runs with the same public arguments. -/
theorem derive_rel {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p σ₁) (E₂ : VG.Proof.AesGcmSiv.Arm.Env p σ₂) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) derive VG.Proof.AesGcmSiv.Arm.TT := by
  have hR := L.rounds
  have w0 : ∀ {σ : State}, VG.Proof.AesGcmSiv.Arm.Env p σ → WP isa (.block [.mov .r4 (Impl.AesGcm.Arm.imm 0)]) σ (VG.Proof.AesGcmSiv.Arm.DC p 0) := fun E =>
    Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun t ht => by
      subst ht
      exact ⟨E.keep (fun r hr => by
          simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
        by simp [gpr_setReg]⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_env E₁ E₂ [] (by simp) VG.Proof.AesGcmSiv.Arm.der0_check) (w0 E₁) (w0 E₂) fun τ₁ τ₂ D₁ D₂ => ?_
  refine VG.Proof.AesGcmSiv.Arm.rel_loop (fun m t₁ t₂ => ∃ i, m = (p.R / 2 - 1) - i ∧ i < p.R / 2 - 1 ∧ VG.Proof.AesGcmSiv.Arm.DC p i t₁ ∧ VG.Proof.AesGcmSiv.Arm.DC p i t₂)
    (fun m t₁ t₂ ⟨i, hm, hi, I₁, I₂⟩ => ?_) ((p.R / 2 - 1) - 0)
    ⟨0, rfl, by rcases hR with h | h <;> rw [h] <;> decide, D₁, D₂⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seqQ (VG.Proof.AesGcmSiv.Arm.rel_env I₁.env I₂.env [.r4] (by simp [I₁.r4, I₂.r4]) VG.Proof.AesGcmSiv.Arm.derA_check) (VG.Proof.AesGcmSiv.Arm.derA_wp L I₁)
    (VG.Proof.AesGcmSiv.Arm.derA_wp L I₂) fun u₁ u₂ A₁ A₂ => ?_
  refine VG.Proof.AesGcmSiv.Arm.rel_seqQ (VG.Proof.AesGcmSiv.Arm.rel_ctr A₁.1 A₂.1 (A₁.2.env.sp_eq A₂.2.env)) (VG.Proof.AesGcmSiv.Arm.derC_wp A₁) (VG.Proof.AesGcmSiv.Arm.derC_wp A₂)
    fun a b J₁ J₂ => ?_
  refine VG.Proof.AesGcmSiv.Arm.rel_wpQ (VG.Proof.AesGcmSiv.Arm.rel_env J₁.env J₂.env [.r4] (by simp [J₁.r4, J₂.r4]) VG.Proof.AesGcmSiv.Arm.derP_check) (VG.Proof.AesGcmSiv.Arm.derP_wp L hi J₁)
    (VG.Proof.AesGcmSiv.Arm.derP_wp L hi J₂) fun a' b' ⟨K₁, z₁⟩ ⟨K₂, z₂⟩ => ?_
  have ev₁ := eval_ne' z₁
  have ev₂ := eval_ne' z₂
  refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
  rw [ev₁] at hc
  have he : i + 1 ≠ p.R / 2 - 1 := by simpa using hc
  exact ⟨(p.R / 2 - 1) - (i + 1), by omega, i + 1, rfl, by omega, K₁, K₂⟩

theorem expA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [])) (.block expandArgs) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem hkey_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [])) (.block hkey) h).isSome
    = true := ⟨_, by taint_decide⟩

/-- `keys`, in two runs with the same public arguments. -/
theorem keys_rel {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p σ₁) (E₂ : VG.Proof.AesGcmSiv.Arm.Env p σ₂) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) VG.Impl.AesGcmSiv.Arm.keys VG.Proof.AesGcmSiv.Arm.TT := by
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.derive_rel L E₁ E₂) (VG.Proof.AesGcmSiv.Arm.derive_ok L E₁) (VG.Proof.AesGcmSiv.Arm.derive_ok L E₂) fun τ₁ τ₂ D₁ D₂ => ?_
  have wA : ∀ {τ : State}, VG.Proof.AesGcmSiv.Arm.Env p τ → WP isa (.block expandArgs) τ fun t₁ =>
      KeyCall t₁ (p.W + BitVec.ofNat 32 32) (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 1712)
        (Spec.GcmSiv.keyLen p.R) ∧ VG.Proof.AesGcmSiv.Arm.Env p t₁ := fun E => by
    obtain ⟨t₁, run₁, kc, E', -⟩ := VG.Proof.AesGcmSiv.Arm.expArgs_ok L E
    exact WP.of_runBlock ⟨t₁, run₁, kc, E'⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (c₁ := expand) ?_ (WP.mono (VG.Proof.AesGcmSiv.Arm.expand_ok L D₁.env) fun _ X => X.env)
    (WP.mono (VG.Proof.AesGcmSiv.Arm.expand_ok L D₂.env) fun _ X => X.env) fun u₁ u₂ F₁ F₂ =>
      VG.Proof.AesGcmSiv.Arm.rel_env F₁ F₂ [] (by simp) VG.Proof.AesGcmSiv.Arm.hkey_check
  exact VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_env D₁.env D₂.env [] (by simp) VG.Proof.AesGcmSiv.Arm.expA_check) (wA D₁.env) (wA D₂.env)
    fun a b ⟨k₁, _⟩ ⟨k₂, _⟩ => VG.Proof.AesGcmSiv.Arm.rel_key k₁ k₂

end VG.Proof.AesGcmSiv.Arm

/-!
## POLYVAL is constant time

Untrusted: everything here is checked by Lean. A chunk's blocks, their
number and the pointers come from the public lengths and addresses; the
calls of `vg_ghash` have the same arguments in both runs; the branches and
loops are on counts both runs agree on.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (GhCall gh_call eval_eq' eval_ne' z_cmp z_subFlags mem_subFlags gpr_subFlags sp_subFlags
  rd_subFlags wr_subFlags)

theorem chunkPre_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [.r4, .r5])) chunkPre h).isSome
    = true := ⟨_, by taint_decide⟩

theorem chunkEnd_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [.r5]))
    (.block wholeLeft) h).isSome = true := ⟨_, by taint_decide⟩

/-- A chunk, in two runs with the same public arguments, pointer and count. -/
theorem chunk_rel {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.Arm.Env p τ₂)
    {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ₁ : VG.Proof.AesGcmSiv.Arm.Src p τ₁ Q (16 * (m / 16)))
    (hQ₂ : VG.Proof.AesGcmSiv.Arm.Src p τ₂ Q (16 * (m / 16))) (a4 : τ₁.gpr .r4 = Q) (b4 : τ₂.gpr .r4 = Q)
    (a5 : τ₁.gpr .r5 = BitVec.ofNat 32 m) (b5 : τ₂.gpr .r5 = BitVec.ofNat 32 m) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 τ₁ τ₂) chunk VG.Proof.AesGcmSiv.Arm.TT := by
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_env E₁ E₂ [.r4, .r5] (by simp [a4, b4, a5, b5]) VG.Proof.AesGcmSiv.Arm.chunkPre_check)
    (VG.Proof.AesGcmSiv.Arm.chunkPre_ok L E₁ hm h16 hQ₁ a4 a5) (VG.Proof.AesGcmSiv.Arm.chunkPre_ok L E₂ hm h16 hQ₂ b4 b5) fun u₁ u₂ P₁ P₂ => ?_
  have wG : ∀ {u : State}, VG.Proof.AesGcmSiv.Arm.ChunkPre p Q m (min (m / 16) 64) τ₁ u ∨ VG.Proof.AesGcmSiv.Arm.ChunkPre p Q m (min (m / 16) 64) τ₂ u →
      WP isa Impl.AesGcm.Arm.ghFrame u fun w => VG.Proof.AesGcmSiv.Arm.Env p w ∧ w.gpr .r5 = BitVec.ofNat 32 (m - 16 * min (m / 16) 64) :=
    fun h => by
      rcases h with P | P <;>
      exact WP.mono (gh_call P.call) fun _ G =>
        ⟨P.env.of_saved G.saved G.sp G.rd G.wr, by rw [G.saved _ (by decide) (by decide), P.r5]⟩
  exact VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_gh P₁.call P₂.call (P₁.env.sp_eq P₂.env)) (wG (.inl P₁)) (wG (.inr P₂))
    fun w₁ w₂ G₁ G₂ => VG.Proof.AesGcmSiv.Arm.rel_env G₁.1 G₂.1 [.r5] (by simp [G₁.2, G₂.2]) VG.Proof.AesGcmSiv.Arm.chunkEnd_check

/-- The chunks, in two runs from `σ₁` and `σ₂` with the same public arguments. -/
theorem chunks_rel {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {σ₁ σ₂ : State} {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32)
    (hQ₁ : VG.Proof.AesGcmSiv.Arm.Src p σ₁ Q (16 * (m / 16))) (hQ₂ : VG.Proof.AesGcmSiv.Arm.Src p σ₂ Q (16 * (m / 16))) {d : Nat}
    (hd : d < m / 16) {τ₁ τ₂ : State} (I₁ : VG.Proof.AesGcmSiv.Arm.CInv p σ₁ Q m d τ₁) (I₂ : VG.Proof.AesGcmSiv.Arm.CInv p σ₂ Q m d τ₂) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 τ₁ τ₂) (.loop chunk .ne) VG.Proof.AesGcmSiv.Arm.TT := by
  refine VG.Proof.AesGcmSiv.Arm.rel_loop (fun k t₁ t₂ => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ VG.Proof.AesGcmSiv.Arm.CInv p σ₁ Q m d t₁ ∧ VG.Proof.AesGcmSiv.Arm.CInv p σ₂ Q m d t₂)
    (fun k t₁ t₂ ⟨d, hk, hd, J₁, J₂⟩ => ?_) (m / 16 - d) ⟨d, rfl, hd, I₁, I₂⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_wpQ (VG.Proof.AesGcmSiv.Arm.chunk_rel L J₁.abs.env J₂.abs.env (by omega) (by omega) (J₁.src hQ₁ hd) (J₂.src hQ₂ hd)
      J₁.r4 J₂.r4 J₁.r5 J₂.r5)
    (VG.Proof.AesGcmSiv.Arm.chunk_ok L J₁.abs.env (by omega) (by omega) (J₁.src hQ₁ hd) J₁.r4 J₁.r5)
    (VG.Proof.AesGcmSiv.Arm.chunk_ok L J₂.abs.env (by omega) (by omega) (J₂.src hQ₂ hd) J₂.r4 J₂.r5) fun a b C₁ C₂ => ?_
  obtain ⟨K₁, z₁⟩ := J₁.step L hQ₁ hd C₁
  obtain ⟨K₂, z₂⟩ := J₂.step L hQ₂ hd C₂
  have ev₁ := eval_ne' z₁
  have ev₂ := eval_ne' z₂
  refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
  rw [ev₁] at hc
  have he : m / 16 - (d + min (m / 16 - d) 64) ≠ 0 := by simpa using hc
  exact ⟨m / 16 - (d + min (m / 16 - d) 64), by omega, d + min (m / 16 - d) 64, rfl, by omega, K₁, K₂⟩

theorem absHead_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [.r4, .r5]))
    (.block wholeLeft) h).isSome = true := ⟨_, by taint_decide⟩

theorem absCmp_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [.r4, .r5]))
    (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem absTailPre_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [.r4, .r5])) absTailPre
    h).isSome = true := ⟨_, by taint_decide⟩

/-- `chunk` on the block at `W + 176`. -/
theorem chunkB_rel {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.Arm.Env p τ₂)
    (a4 : τ₁.gpr .r4 = p.W + BitVec.ofNat 32 176) (b4 : τ₂.gpr .r4 = p.W + BitVec.ofNat 32 176)
    (a5 : τ₁.gpr .r5 = BitVec.ofNat 32 16) (b5 : τ₂.gpr .r5 = BitVec.ofNat 32 16) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 τ₁ τ₂) chunk VG.Proof.AesGcmSiv.Arm.TT :=
  VG.Proof.AesGcmSiv.Arm.chunk_rel L E₁ E₂ (m := 16) (by decide) (by decide) (VG.Proof.AesGcmSiv.Arm.srcB L E₁.perm) (VG.Proof.AesGcmSiv.Arm.srcB L E₂.perm) a4 b4 a5 b5

/-- `cmp r5, #0`. -/
theorem cmp5_ok {t : State} {r : Nat} (hr : r < 2 ^ 32) (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) t fun t' => t'.z = decide (r = 0) ∧ t'.gpr = t.gpr ∧
      t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr :=
  Proof.AesGcm.Arm.WP.run ⟨_, by srun [h5], rfl⟩ fun t' ht => by
    subst ht
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only [z_subFlags]
    rw [z_cmp hr (by decide)]

/-- `absorb`, in two runs with the same public arguments, pointer and count. -/
theorem absorb_rel {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.Arm.Env p τ₂)
    {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32) (hd : (⟨State.addr Q, m⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩)
    (hQ₁ : VG.Proof.AesGcmSiv.Arm.Src p τ₁ Q m) (hQ₂ : VG.Proof.AesGcmSiv.Arm.Src p τ₂ Q m)
    (a4 : τ₁.gpr .r4 = Q) (b4 : τ₂.gpr .r4 = Q) (a5 : τ₁.gpr .r5 = BitVec.ofNat 32 m)
    (b5 : τ₂.gpr .r5 = BitVec.ofNat 32 m) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 τ₁ τ₂) absorb VG.Proof.AesGcmSiv.Arm.TT := by
  have wH : ∀ {τ : State}, VG.Proof.AesGcmSiv.Arm.Env p τ → τ.gpr .r4 = Q → τ.gpr .r5 = BitVec.ofNat 32 m →
      WP isa (.block wholeLeft) τ fun u => VG.Proof.AesGcmSiv.Arm.Env p u ∧ u.gpr .r4 = Q ∧ u.gpr .r5 = BitVec.ofNat 32 m ∧
        u.z = decide (m / 16 = 0) ∧ u.mem = τ.mem ∧ u.rd = τ.rd ∧ u.wr = τ.wr := fun E h4 h5 => by
    obtain ⟨u, run, z, ho, hm', sp, rd, wr⟩ := VG.Proof.AesGcmSiv.Arm.wholeLeft_ok hm h5
    exact WP.of_runBlock ⟨u, run, E.of_others ho sp rd wr, by rw [ho _ (by decide), h4],
      by rw [ho _ (by decide), h5], z, hm', rd, wr⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_env E₁ E₂ [.r4, .r5] (by simp [a4, b4, a5, b5]) VG.Proof.AesGcmSiv.Arm.absHead_check) (wH E₁ a4 a5)
    (wH E₂ b4 b5) fun u₁ u₂ ⟨F₁, u4₁, u5₁, z₁, m₁, rd₁, wr₁⟩ ⟨F₂, u4₂, u5₂, z₂, m₂, rd₂, wr₂⟩ => ?_
  have hQ₁' := hQ₁.of_eq rd₁ wr₁
  have hQ₂' := hQ₂.of_eq rd₂ wr₂
  -- The whole blocks.
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_ite (eval_eq' z₁) (eval_eq' z₂)
      (fun _ => VG.Proof.AesGcmSiv.Arm.rel_skip) (fun hf => ?_))
    (VG.Proof.AesGcmSiv.Arm.absMid_ok L F₁ hm hQ₁' u4₁ u5₁ z₁) (VG.Proof.AesGcmSiv.Arm.absMid_ok L F₂ hm hQ₂' u4₂ u5₂ z₂)
    fun w₁ w₂ ⟨A₁, r4₁, r5₁⟩ ⟨A₂, r4₂, r5₂⟩ => ?_
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact VG.Proof.AesGcmSiv.Arm.chunks_rel L hm (hQ₁'.take (by omega)) (hQ₂'.take (by omega)) (d := 0) (by omega)
      (CInv.zero F₁ u4₁ u5₁) (CInv.zero F₂ u4₂ u5₂)
  -- The last bytes.
  have wC : ∀ {w : State}, VG.Proof.AesGcmSiv.Arm.Env p w → w.gpr .r4 = Q + BitVec.ofNat 32 (16 * (m / 16)) →
      w.gpr .r5 = BitVec.ofNat 32 (m % 16) → WP isa (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) w fun u =>
        VG.Proof.AesGcmSiv.Arm.Env p u ∧ u.gpr .r4 = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ u.gpr .r5 = BitVec.ofNat 32 (m % 16) ∧
          u.z = decide (m % 16 = 0) ∧ u.rd = w.rd ∧ u.wr = w.wr := fun E h4 h5 =>
    WP.mono (VG.Proof.AesGcmSiv.Arm.cmp5_ok (by omega) h5) fun u ⟨z, g, _, sp, rd, wr⟩ =>
      ⟨E.keep (fun r _ => by rw [g]) sp rd wr, by rw [g, h4], by rw [g, h5], z, rd, wr⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_env A₁.env A₂.env [.r4, .r5] (by simp [r4₁, r4₂, r5₁, r5₂]) VG.Proof.AesGcmSiv.Arm.absCmp_check)
    (wC A₁.env r4₁ r5₁) (wC A₂.env r4₂ r5₂) fun c₁ c₂ ⟨G₁, c4₁, c5₁, cz₁, crd₁, cwr₁⟩ ⟨G₂, c4₂, c5₂, cz₂, crd₂, cwr₂⟩ => ?_
  refine VG.Proof.AesGcmSiv.Arm.rel_ite (eval_eq' cz₁) (eval_eq' cz₂) (fun _ => VG.Proof.AesGcmSiv.Arm.rel_skip) (fun hf => ?_)
  have h0 : m % 16 ≠ 0 := by simpa using hf
  have ea := hQ₁.addr (j := 16 * (m / 16)) (by omega)
  have dT : (⟨State.addr (Q + BitVec.ofNat 32 (16 * (m / 16))), m % 16⟩ : Region).Disjoint
      ⟨State.addr p.W, 3760⟩ := by
    rw [ea]; exact hd.sub_left (Offset.sub_base _ (by omega))
  have hs₁ := ((hQ₁'.slice (a := 16 * (m / 16)) (k := m % 16) (by omega) (by omega)).of_eq A₁.rd A₁.wr).of_eq crd₁ cwr₁
  have hs₂ := ((hQ₂'.slice (a := 16 * (m / 16)) (k := m % 16) (by omega) (by omega)).of_eq A₂.rd A₂.wr).of_eq crd₂ cwr₂
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_env G₁ G₂ [.r4, .r5] (by simp [c4₁, c4₂, c5₁, c5₂]) VG.Proof.AesGcmSiv.Arm.absTailPre_check)
    (VG.Proof.AesGcmSiv.Arm.absTailPre_ok L G₁ (by omega) (by omega) hs₁.rd hs₁.wrap dT c4₁ c5₁)
    (VG.Proof.AesGcmSiv.Arm.absTailPre_ok L G₂ (by omega) (by omega) hs₂.rd hs₂.wrap dT c4₂ c5₂) fun z₁ z₂ T₁ T₂ => ?_
  exact VG.Proof.AesGcmSiv.Arm.chunkB_rel L T₁.env T₂.env T₁.r4 T₂.r4 T₁.r5 T₂.r5

theorem lensBlock_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesGcmSiv.Arm.pubRegs []) 12) (.block lensBlock) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem tagIn_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [])) (.block tagIn) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem polyA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesGcmSiv.Arm.pubRegs []) 12)
    (.block [.mov .r4 (.reg .r7), .ldrSp .r5 0]) h).isSome = true := ⟨_, by taint_decide⟩

theorem polyD_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesGcmSiv.Arm.pubRegs []) 12)
    (.block [.ldrSp .r4 4, .ldrSp .r5 8]) h).isSome = true := ⟨_, by taint_decide⟩

/-- What a run keeps before a piece: the environment and the stack
arguments. -/
structure PR (p : VG.Proof.AesGcmSiv.Arm.Prm) (t : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t
  args : VG.Proof.AesGcmSiv.Arm.Args p t.mem

/-- After absorbing. -/
theorem PR.of_abs {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {xs : List Spec.GcmSiv.Elem} {t t' : State} (h : VG.Proof.AesGcmSiv.Arm.PR p t)
    (P : VG.Proof.AesGcmSiv.Arm.AbsPost p xs t t') : VG.Proof.AesGcmSiv.Arm.PR p t' :=
  ⟨P.env, h.args.frame L P.frame (VG.Proof.AesGcmSiv.Arm.absorbR_args L)⟩

/-- `polyval`, in two runs with the same public arguments. -/
theorem polyval_rel {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {σ₁ σ₂ : State} (R₁ : VG.Proof.AesGcmSiv.Arm.PR p σ₁) (R₂ : VG.Proof.AesGcmSiv.Arm.PR p σ₂) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) polyval VG.Proof.AesGcmSiv.Arm.TT := by
  have wA : ∀ {σ : State}, VG.Proof.AesGcmSiv.Arm.PR p σ → WP isa (.block [.mov .r4 (.reg .r7), .ldrSp .r5 0]) σ fun t =>
      VG.Proof.AesGcmSiv.Arm.PR p t ∧ t.gpr .r4 = p.A ∧ t.gpr .r5 = BitVec.ofNat 32 p.al := fun R => by
    have a₀ := R.env.perm.argR' L (k := 0) (by decide)
    refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [R.env.sp, a₀, R.args.a0], rfl⟩ fun t ht => ?_
    subst ht
    exact ⟨⟨R.env.keep (fun r hr => by
        simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, R.args⟩,
      by simp [gpr_setReg, R.env.r7], by simp [gpr_setReg]⟩
  have wD : ∀ {σ : State}, VG.Proof.AesGcmSiv.Arm.PR p σ → WP isa (.block [.ldrSp .r4 4, .ldrSp .r5 8]) σ fun t =>
      VG.Proof.AesGcmSiv.Arm.PR p t ∧ t.gpr .r4 = p.D ∧ t.gpr .r5 = BitVec.ofNat 32 p.n := fun R => by
    have a₄ := R.env.perm.argR' L (k := 4) (by decide)
    have a₈ := R.env.perm.argR' L (k := 8) (by decide)
    refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [R.env.sp, a₄, a₈, R.args.a4, R.args.a8], rfl⟩ fun t ht => ?_
    subst ht
    exact ⟨⟨R.env.keep (fun r hr => by
        simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, R.args⟩,
      by simp [gpr_setReg], by simp [gpr_setReg]⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_envArg L R₁.env R₂.env R₁.args R₂.args [] (by simp) VG.Proof.AesGcmSiv.Arm.polyA_check) (wA R₁) (wA R₂)
    fun a₁ a₂ ⟨G₁, a4₁, a5₁⟩ ⟨G₂, a4₂, a5₂⟩ => ?_
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.absorb_rel L G₁.env G₂.env L.al_lt L.a_w (VG.Proof.AesGcmSiv.Arm.srcA L G₁.env.perm) (VG.Proof.AesGcmSiv.Arm.srcA L G₂.env.perm) a4₁ a4₂ a5₁ a5₂)
    (VG.Proof.AesGcmSiv.Arm.absorb_ok L G₁.env L.al_lt (VG.Proof.AesGcmSiv.Arm.srcA L G₁.env.perm) L.a_w a4₁ a5₁)
    (VG.Proof.AesGcmSiv.Arm.absorb_ok L G₂.env L.al_lt (VG.Proof.AesGcmSiv.Arm.srcA L G₂.env.perm) L.a_w a4₂ a5₂)
    fun b₁ b₂ B₁ B₂ => ?_
  have H₁ := G₁.of_abs L B₁
  have H₂ := G₂.of_abs L B₂
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_envArg L H₁.env H₂.env H₁.args H₂.args [] (by simp) VG.Proof.AesGcmSiv.Arm.polyD_check) (wD H₁) (wD H₂)
    fun c₁ c₂ ⟨K₁, c4₁, c5₁⟩ ⟨K₂, c4₂, c5₂⟩ => ?_
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.absorb_rel L K₁.env K₂.env L.n_lt L.d_w (VG.Proof.AesGcmSiv.Arm.srcD L K₁.env.perm) (VG.Proof.AesGcmSiv.Arm.srcD L K₂.env.perm) c4₁ c4₂ c5₁ c5₂)
    (VG.Proof.AesGcmSiv.Arm.absorb_ok L K₁.env L.n_lt (VG.Proof.AesGcmSiv.Arm.srcD L K₁.env.perm) L.d_w c4₁ c5₁)
    (VG.Proof.AesGcmSiv.Arm.absorb_ok L K₂.env L.n_lt (VG.Proof.AesGcmSiv.Arm.srcD L K₂.env.perm) L.d_w c4₂ c5₂)
    fun d₁ d₂ D₁ D₂ => ?_
  have M₁ := K₁.of_abs L D₁
  have M₂ := K₂.of_abs L D₂
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (c₁ := lens) ?_ (VG.Proof.AesGcmSiv.Arm.lens_ok L M₁.env M₁.args) (VG.Proof.AesGcmSiv.Arm.lens_ok L M₂.env M₂.args) fun e₁ e₂ F₁ F₂ =>
    VG.Proof.AesGcmSiv.Arm.rel_env F₁.env F₂.env [] (by simp) VG.Proof.AesGcmSiv.Arm.tagIn_check
  have wL : ∀ {d : State}, VG.Proof.AesGcmSiv.Arm.PR p d → WP isa (.block lensBlock) d fun t =>
      VG.Proof.AesGcmSiv.Arm.Env p t ∧ t.gpr .r4 = p.W + BitVec.ofNat 32 176 ∧ t.gpr .r5 = BitVec.ofNat 32 16 := fun R => by
    have w₀ := R.env.perm.wW (show 176 + 4 ≤ 3760 by decide)
    have w₁ := R.env.perm.wW (show 180 + 4 ≤ 3760 by decide)
    have w₂ := R.env.perm.wW (show 184 + 4 ≤ 3760 by decide)
    have w₃ := R.env.perm.wW (show 188 + 4 ≤ 3760 by decide)
    have a₀ := R.env.perm.argR' L (k := 0) (by decide)
    have a₈ := R.env.perm.argR' L (k := 8) (by decide)
    refine Proof.AesGcm.Arm.WP.run ⟨_, by simp only [lensBlock]; srun [R.env.r11, R.env.sp, L.wA, a₀, a₈,
      R.args.a0, R.args.a8, w₀, w₁, w₂, w₃], rfl⟩ fun t ht => ?_
    subst ht
    refine ⟨R.env.keep (fun q hq => by
        simp only [VG.Proof.AesGcmSiv.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      by simp [gpr_setReg, R.env.r11], by simp [gpr_setReg]⟩
  exact VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_envArg L M₁.env M₂.env M₁.args M₂.args [] (by simp) VG.Proof.AesGcmSiv.Arm.lensBlock_check) (wL M₁)
    (wL M₂) fun f₁ f₂ ⟨K₁, x4₁, x5₁⟩ ⟨K₂, x4₂, x5₂⟩ => VG.Proof.AesGcmSiv.Arm.chunkB_rel L K₁ K₂ x4₁ x4₂ x5₁ x5₂

end VG.Proof.AesGcmSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.Arm.FnCT`. -/
section

/-!
# AES-GCM-SIV on ARMv7: the functions are constant time

Untrusted: everything here is checked by Lean. Two runs with the same
public arguments (`onePub`) have the same `prmOf`; each piece of `seal` and
`open` is related in the two runs by the lemmas of `PolyvalCT.lean`, the
counter mode's blocks by `vg_aes_ctr32`'s proof with
the same arguments in both runs, and the comparison, the mask and the
restore by the taint analysis (`seal_ct`, `open_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (CtrCall ctr_call eval_eq' eval_ne' arg args argAddr_zero)

/-! ## The tag -/

theorem tagA_check {o : Nat} (ho : o = 0 ∨ o = 176) : ∃ h, (VG.Taint.check VG.Arm.taint
    (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [])) (.block (copy16 cbO ccO ++ Impl.AesGcm.Arm.zero16 o ++ ctrArgs ++
      ([Impl.AesGcm.Arm.addI .r3 .r11 o] : List Instr))) h).isSome = true := by
  rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `tag o`, in two runs with the same public arguments. -/
theorem tag_rel {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.Arm.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.Arm.Env p τ₂) {o : Nat}
    (ho : o = 0 ∨ o = 176) : RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 τ₁ τ₂) (tag o) VG.Proof.AesGcmSiv.Arm.TT := by
  have w : ∀ {τ : State}, VG.Proof.AesGcmSiv.Arm.Env p τ → WP isa (.block (copy16 cbO ccO ++ Impl.AesGcm.Arm.zero16 o ++ ctrArgs ++
      ([Impl.AesGcm.Arm.addI .r3 .r11 o] : List Instr))) τ fun t₁ => CtrCall t₁ (p.W + BitVec.ofNat 32 192)
        (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 o) (p.W + BitVec.ofNat 32 1712) p.R 1 ∧ VG.Proof.AesGcmSiv.Arm.Env p t₁ :=
    fun E => by
      obtain ⟨t₁, run₁, -, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.Arm.tagArgs_ok L E ho
      have E' : VG.Proof.AesGcmSiv.Arm.Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
      exact WP.of_runBlock ⟨t₁, run₁, VG.Proof.AesGcmSiv.Arm.tagCall L E' ho r0 r1 r2 r3 r12 lr, E'⟩
  exact VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_env E₁ E₂ [] (by simp) (VG.Proof.AesGcmSiv.Arm.tagA_check ho)) (w E₁) (w E₂)
    fun a b A₁ A₂ => VG.Proof.AesGcmSiv.Arm.rel_ctr A₁.1 A₂.1 (A₁.2.sp_eq A₂.2)

/-! ## Counter mode -/

theorem blkA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [.r4, .r5]))
    (.block (copy16 cbO ccO ++ ctrArgs ++ ([.mov .r3 (.reg .r4)] : List Instr))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem blkP_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [.r4, .r5]))
    (.block blockNext) h).isSome = true := ⟨_, by taint_decide⟩

/-- What the constant-time proof needs of a run of counter mode after `j`
blocks. -/
structure BL (p : VG.Proof.AesGcmSiv.Arm.Prm) (j : Nat) (t : State) : Prop where
  env : VG.Proof.AesGcmSiv.Arm.Env p t
  r4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j)

/-- A block of counter mode, in two runs with the same public arguments,
pointer and count. -/
theorem cryptBlock_rel {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {τ₁ τ₂ : State} {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (B₁ : VG.Proof.AesGcmSiv.Arm.BL p j τ₁) (B₂ : VG.Proof.AesGcmSiv.Arm.BL p j τ₂) : RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 τ₁ τ₂) cryptBlock VG.Proof.AesGcmSiv.Arm.TT := by
  have w : ∀ {τ : State}, VG.Proof.AesGcmSiv.Arm.BL p j τ →
      WP isa (.block (copy16 cbO ccO ++ ctrArgs ++ ([.mov .r3 (.reg .r4)] : List Instr))) τ fun t₁ =>
        CtrCall t₁ (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 112) (p.D + BitVec.ofNat 32 (16 * j))
          (p.W + BitVec.ofNat 32 1712) p.R 1 ∧ VG.Proof.AesGcmSiv.Arm.BL p j t₁ := fun B => by
    obtain ⟨t₁, run₁, -, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.Arm.blkArgs_ok L B.env B.r4
    have E' : VG.Proof.AesGcmSiv.Arm.Env p t₁ := B.env.of_others ho₁ sp₁ rd₁ wr₁
    exact WP.of_runBlock ⟨t₁, run₁, VG.Proof.AesGcmSiv.Arm.blkCall L E' hj r0 r1 r2 r3 r12 lr, E', by rw [ho₁ _ (by decide), B.r4],
      by rw [ho₁ _ (by decide), B.r5]⟩
  have wc : ∀ {t : State}, (CtrCall t (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 112)
      (p.D + BitVec.ofNat 32 (16 * j)) (p.W + BitVec.ofNat 32 1712) p.R 1 ∧ VG.Proof.AesGcmSiv.Arm.BL p j t) →
      WP isa Impl.AesGcm.Arm.ctrFrame t (VG.Proof.AesGcmSiv.Arm.BL p j) := fun ⟨cc, B⟩ =>
    WP.mono (ctr_call cc) fun _ P => ⟨B.env.of_saved P.saved P.sp P.rd P.wr,
      by rw [P.saved _ (by decide) (by decide), B.r4], by rw [P.saved _ (by decide) (by decide), B.r5]⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_env B₁.env B₂.env [.r4, .r5] (by simp [B₁.r4, B₂.r4, B₁.r5, B₂.r5]) VG.Proof.AesGcmSiv.Arm.blkA_check) (w B₁)
    (w B₂) fun u₁ u₂ A₁ A₂ => ?_
  exact VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_ctr A₁.1 A₂.1 (A₁.2.env.sp_eq A₂.2.env)) (wc A₁) (wc A₂)
    fun w₁ w₂ C₁ C₂ => VG.Proof.AesGcmSiv.Arm.rel_env C₁.env C₂.env [.r4, .r5] (by simp [C₁.r4, C₂.r4, C₁.r5, C₂.r5]) VG.Proof.AesGcmSiv.Arm.blkP_check

/-- A block of counter mode, for its registers. -/
theorem cryptBlockL_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {j : Nat} (hj : 16 * (j + 1) ≤ p.n) {t : State} (B : VG.Proof.AesGcmSiv.Arm.BL p j t) :
    WP isa cryptBlock t fun t' => VG.Proof.AesGcmSiv.Arm.BL p (j + 1) t' ∧ t'.z = decide ((p.n - 16 * (j + 1)) / 16 = 0) := by
  obtain ⟨t₁, run₁, -, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.Arm.blkArgs_ok L B.env B.r4
  have E₁ : VG.Proof.AesGcmSiv.Arm.Env p t₁ := B.env.of_others ho₁ sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (ctr_call (VG.Proof.AesGcmSiv.Arm.blkCall L E₁ hj r0 r1 r2 r3 r12 lr)) fun t₂ P => ?_)
  have E₂ : VG.Proof.AesGcmSiv.Arm.Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have h4₂ : t₂.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), B.r4]
  have h5₂ : t₂.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), B.r5]
  obtain ⟨t₃, run₃, -, r4₃, r5₃, z₃, ho₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesGcmSiv.Arm.blkPost_ok L E₂ hj h4₂ h5₂
  exact WP.of_runBlock ⟨t₃, run₃, ⟨E₂.of_others ho₃ sp₃ rd₃ wr₃, r4₃, r5₃⟩, z₃⟩

/-- The whole blocks of counter mode, for their registers. -/
theorem cryptMidL_ok {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {t : State} (B : VG.Proof.AesGcmSiv.Arm.BL p 0 t) (hz : t.z = decide (p.n / 16 = 0)) :
    WP isa (.ite .eq (.block []) (.loop cryptBlock .ne)) t (VG.Proof.AesGcmSiv.Arm.BL p (p.n / 16)) := by
  refine WP.ite (decide (p.n / 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n / 16 = 0 := by simpa using ht
    rw [h0]; exact WP.block_nil B
  · have h0 : p.n / 16 ≠ 0 := by simpa using hf
    refine WP.loop (M := isa) (fun k t' => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ VG.Proof.AesGcmSiv.Arm.BL p j t') ?_
      (p.n / 16 - 0) t ⟨0, rfl, by omega, B⟩
    rintro k t' ⟨j, rfl, hj, B'⟩
    refine WP.mono (VG.Proof.AesGcmSiv.Arm.cryptBlockL_ok L (j := j) (by omega) B') fun t'' ⟨B'', z⟩ => ?_
    have ev := eval_ne' z
    by_cases he : j + 1 = p.n / 16
    · left; exact ⟨ev.trans (by simp; omega), he ▸ B''⟩
    · right; exact ⟨ev.trans (by simp; omega), p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, B''⟩

theorem cryptHead_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesGcmSiv.Arm.pubRegs []) 12) (.block cryptHead) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem crypt5_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [.r4, .r5]))
    (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem cryptTailRest_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesGcmSiv.Arm.pubRegs [.r4, .r5]))
    (.seq (.block [Impl.AesGcm.Arm.addI .r1 .r11 bO, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)])
      Impl.AesGcm.Arm.xorLoop) h).isSome = true := ⟨_, by taint_decide⟩

/-- `crypt`, in two runs with the same public arguments. -/
theorem crypt_rel {p : VG.Proof.AesGcmSiv.Arm.Prm} (L : VG.Proof.AesGcmSiv.Arm.Lay p) {σ₁ σ₂ : State} (R₁ : VG.Proof.AesGcmSiv.Arm.PR p σ₁) (R₂ : VG.Proof.AesGcmSiv.Arm.PR p σ₂) :
    RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) crypt VG.Proof.AesGcmSiv.Arm.TT := by
  have hn := L.n_lt
  have wh : ∀ {σ : State}, VG.Proof.AesGcmSiv.Arm.PR p σ → WP isa (.block cryptHead) σ fun t₁ => VG.Proof.AesGcmSiv.Arm.BL p 0 t₁ ∧
      t₁.z = decide (p.n / 16 = 0) := fun R => by
    obtain ⟨t₁, run₁, -, r4₁, r5₁, z₁, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.Arm.cryptHead_ok L R.env R.args
    exact WP.of_runBlock ⟨t₁, run₁, ⟨R.env.of_others ho₁ sp₁ rd₁ wr₁,
      by rw [r4₁, Nat.mul_zero, Proof.AesGcm.Arm.add_ofNat_zero], by rw [r5₁, Nat.mul_zero, Nat.sub_zero]⟩, z₁⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_envArg L R₁.env R₂.env R₁.args R₂.args [] (by simp) VG.Proof.AesGcmSiv.Arm.cryptHead_check) (wh R₁) (wh R₂)
    fun u₁ u₂ ⟨B₁, z₁⟩ ⟨B₂, z₂⟩ => ?_
  -- The whole blocks.
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => VG.Proof.AesGcmSiv.Arm.rel_skip) (fun hf => ?_))
    (VG.Proof.AesGcmSiv.Arm.cryptMidL_ok L B₁ z₁) (VG.Proof.AesGcmSiv.Arm.cryptMidL_ok L B₂ z₂) fun w₁ w₂ C₁ C₂ => ?_
  · have h0 : p.n / 16 ≠ 0 := by simpa using hf
    refine VG.Proof.AesGcmSiv.Arm.rel_loop (fun k t₁ t₂ => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ VG.Proof.AesGcmSiv.Arm.BL p j t₁ ∧ VG.Proof.AesGcmSiv.Arm.BL p j t₂)
      (fun k t₁ t₂ ⟨j, hk, hj, J₁, J₂⟩ => ?_) (p.n / 16 - 0) ⟨0, rfl, by omega, B₁, B₂⟩
    refine VG.Proof.AesGcmSiv.Arm.rel_wpQ (VG.Proof.AesGcmSiv.Arm.cryptBlock_rel L (j := j) (by omega) J₁ J₂)
      (VG.Proof.AesGcmSiv.Arm.cryptBlockL_ok L (by omega) J₁) (VG.Proof.AesGcmSiv.Arm.cryptBlockL_ok L (by omega) J₂) fun a b ⟨K₁, z₁⟩ ⟨K₂, z₂⟩ => ?_
    have ev₁ := eval_ne' z₁
    have ev₂ := eval_ne' z₂
    refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
    rw [ev₁] at hc
    have he : (p.n - 16 * (j + 1)) / 16 ≠ 0 := by simpa using hc
    exact ⟨p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, K₁, K₂⟩
  -- The last bytes.
  have r5₁ : w₁.gpr .r5 = BitVec.ofNat 32 (p.n % 16) := by rw [C₁.r5]; congr 1; omega
  have r5₂ : w₂.gpr .r5 = BitVec.ofNat 32 (p.n % 16) := by rw [C₂.r5]; congr 1; omega
  have wC : ∀ {w : State}, VG.Proof.AesGcmSiv.Arm.BL p (p.n / 16) w → w.gpr .r5 = BitVec.ofNat 32 (p.n % 16) →
      WP isa (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) w fun u =>
        VG.Proof.AesGcmSiv.Arm.BL p (p.n / 16) u ∧ u.z = decide (p.n % 16 = 0) := fun B h5 =>
    WP.mono (VG.Proof.AesGcmSiv.Arm.cmp5_ok (by omega) h5) fun u ⟨z, g, _, sp, rd, wr⟩ =>
      ⟨⟨B.env.keep (fun r _ => by rw [g]) sp rd wr, by rw [g, B.r4], by rw [g, B.r5]⟩, z⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_env C₁.env C₂.env [.r4, .r5] (by simp [C₁.r4, C₂.r4, C₁.r5, C₂.r5]) VG.Proof.AesGcmSiv.Arm.crypt5_check)
    (wC C₁ r5₁) (wC C₂ r5₂) fun c₁ c₂ ⟨D₁, cz₁⟩ ⟨D₂, cz₂⟩ => ?_
  refine VG.Proof.AesGcmSiv.Arm.rel_ite (eval_eq' cz₁) (eval_eq' cz₂) (fun _ => VG.Proof.AesGcmSiv.Arm.rel_skip) (fun _ => ?_)
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.tag_rel L D₁.env D₂.env (o := 176) (by decide)) (VG.Proof.AesGcmSiv.Arm.tag_ok L D₁.env (o := 176) (by decide))
    (VG.Proof.AesGcmSiv.Arm.tag_ok L D₂.env (o := 176) (by decide)) fun z₁ z₂ T₁ T₂ => ?_
  exact VG.Proof.AesGcmSiv.Arm.rel_env T₁.env T₂.env [.r4, .r5] (by simp [T₁.r4, T₂.r4, T₁.r5, T₂.r5, D₁.r4, D₂.r4, D₁.r5, D₂.r5])
    VG.Proof.AesGcmSiv.Arm.cryptTailRest_check

/-! ## The functions -/

theorem entry_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint [.r0, .r1, .r2, .r3] 20) (.block VG.Impl.AesGcmSiv.Arm.entry) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem sealEnd_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesGcmSiv.Arm.pubRegs []) 16)
    (.block (tagOut ++ Impl.AesGcm.Arm.restore)) h).isSome = true := ⟨_, by taint_decide⟩

theorem recv_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesGcmSiv.Arm.pubRegs []) 16) (.block recv) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem openEnd_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesGcmSiv.Arm.pubRegs []) 12)
    (.seq (.block cmp) (.seq mask (.block Impl.AesGcm.Arm.restore))) h).isSome = true := ⟨_, by taint_decide⟩

/-- The public arguments of two states with the same public data. -/
theorem prmOf_eq {σ₁ σ₂ : State} (h : VG.Proof.AesGcmSiv.Arm.onePub σ₁ σ₂) : VG.Proof.AesGcmSiv.Arm.prmOf σ₁ = VG.Proof.AesGcmSiv.Arm.prmOf σ₂ := by
  obtain ⟨hsp, h0, h1, h2, h3, ha⟩ := h
  simp only [VG.Proof.AesGcmSiv.Arm.prmOf, h0, h1, h2, h3, hsp, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide),
    ha 4 (by decide)]

/-- The entry, in two runs with the same public arguments. -/
theorem entry_rel {σ₁ σ₂ : State} (L₁ : VG.Proof.AesGcmSiv.Arm.Lay (VG.Proof.AesGcmSiv.Arm.prmOf σ₁)) (P₁ : VG.Proof.AesGcmSiv.Arm.Perm (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) σ₁) (L₂ : VG.Proof.AesGcmSiv.Arm.Lay (VG.Proof.AesGcmSiv.Arm.prmOf σ₂))
    (P₂ : VG.Proof.AesGcmSiv.Arm.Perm (VG.Proof.AesGcmSiv.Arm.prmOf σ₂) σ₂) (h : VG.Proof.AesGcmSiv.Arm.onePub σ₁ σ₂) : RelCT isa (VG.Proof.AesGcmSiv.Arm.Eq2 σ₁ σ₂) (.block VG.Impl.AesGcmSiv.Arm.entry) VG.Proof.AesGcmSiv.Arm.TT := by
  have hw : ∀ {σ : State}, VG.Proof.AesGcmSiv.Arm.Lay (VG.Proof.AesGcmSiv.Arm.prmOf σ) → VG.Proof.AesGcmSiv.Arm.Perm (VG.Proof.AesGcmSiv.Arm.prmOf σ) σ → σ.sp.toNat + 20 ≤ 2 ^ 32 ∧
      ∀ r ∈ σ.wr, Region.Disjoint ⟨State.addr σ.sp, 20⟩ r := fun L P => ⟨L.spf, P.argw⟩
  obtain ⟨hsp, h0, h1, h2, h3, ha⟩ := h
  exact VG.Proof.AesGcmSiv.Arm.rel_arg _ 20 (by simp [h0, h1, h2, h3]) hsp (hw L₁ P₁) (hw L₂ P₂)
    (argMem_of (j := 5) hsp L₁.spf fun i hi => ha i hi) VG.Proof.AesGcmSiv.Arm.entry_check

/-- After the entry, what a run keeps. -/
theorem PR.entry {s s₁ : State} (L : VG.Proof.AesGcmSiv.Arm.Lay (VG.Proof.AesGcmSiv.Arm.prmOf s)) (En : VG.Proof.AesGcmSiv.Arm.Entered s s₁) : VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf s) s₁ :=
  ⟨En.env, (VG.Proof.AesGcmSiv.Arm.args_of s).frame L En.frame (by disj_tac L)⟩

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub «seal» := by
  refine VG.Proof.AesGcmSiv.Arm.ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁, -⟩ := VG.Proof.AesGcmSiv.Arm.args_of_seal h₁
  obtain ⟨L₂, P₂, -⟩ := VG.Proof.AesGcmSiv.Arm.args_of_seal h₂
  have e := VG.Proof.AesGcmSiv.Arm.prmOf_eq hp
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.entry_rel L P₁ L₂ P₂ hp) (VG.Proof.AesGcmSiv.Arm.entry_ok L P₁) (VG.Proof.AesGcmSiv.Arm.entry_ok L₂ P₂) fun τ₁ τ₂ En₁ En₂ => ?_
  have R₁ := PR.entry L En₁
  have R₂ := PR.entry L₂ En₂
  rw [← e] at R₂
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.keys_rel L R₁.env R₂.env) (VG.Proof.AesGcmSiv.Arm.keys_ok L R₁.env) (VG.Proof.AesGcmSiv.Arm.keys_ok L R₂.env) fun a₁ a₂ K₁ K₂ => ?_
  have S₁ : VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) a₁ := ⟨K₁.env, R₁.args.frame L K₁.frame (by disj_tac L)⟩
  have S₂ : VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) a₂ := ⟨K₂.env, R₂.args.frame L K₂.frame (by disj_tac L)⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.polyval_rel L S₁ S₂) (VG.Proof.AesGcmSiv.Arm.polyval_ok L S₁.env S₁.args K₁.hkey K₁.acc)
    (VG.Proof.AesGcmSiv.Arm.polyval_ok L S₂.env S₂.args K₂.hkey K₂.acc) fun b₁ b₂ P₁ P₂ => ?_
  have U₁ : VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) b₁ := ⟨P₁.env, S₁.args.frame L P₁.frame (by disj_tac L)⟩
  have U₂ : VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) b₂ := ⟨P₂.env, S₂.args.frame L P₂.frame (by disj_tac L)⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.tag_rel L U₁.env U₂.env (o := 0) (by decide)) (VG.Proof.AesGcmSiv.Arm.tag_ok L U₁.env (o := 0) (by decide))
    (VG.Proof.AesGcmSiv.Arm.tag_ok L U₂.env (o := 0) (by decide)) fun c₁ c₂ T₁ T₂ => ?_
  have V₁ : VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) c₁ := ⟨T₁.env, U₁.args.frame L T₁.frame (by disj_tac L)⟩
  have V₂ : VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) c₂ := ⟨T₂.env, U₂.args.frame L T₂.frame (by disj_tac L)⟩
  exact VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.crypt_rel L V₁ V₂) (VG.Proof.AesGcmSiv.Arm.crypt_ok L V₁.env V₁.args) (VG.Proof.AesGcmSiv.Arm.crypt_ok L V₂.env V₂.args)
    fun d₁ d₂ C₁ C₂ => VG.Proof.AesGcmSiv.Arm.rel_envArg16 L C₁.env C₂.env (V₁.args.frame L C₁.frame (by disj_tac L))
      (V₂.args.frame L C₂.frame (by disj_tac L)) [] (by simp) VG.Proof.AesGcmSiv.Arm.sealEnd_check

theorem open_ct : ConstantTime isa openArm.pre openArm.pub «open» := by
  refine VG.Proof.AesGcmSiv.Arm.ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁⟩ := VG.Proof.AesGcmSiv.Arm.args_of_open h₁
  obtain ⟨L₂, P₂⟩ := VG.Proof.AesGcmSiv.Arm.args_of_open h₂
  have e := VG.Proof.AesGcmSiv.Arm.prmOf_eq hp
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.entry_rel L P₁ L₂ P₂ hp) (VG.Proof.AesGcmSiv.Arm.entry_ok L P₁) (VG.Proof.AesGcmSiv.Arm.entry_ok L₂ P₂) fun τ₁ τ₂ En₁ En₂ => ?_
  have R₀₁ := PR.entry L En₁
  have R₀₂ := PR.entry L₂ En₂
  rw [← e] at R₀₂
  have wr : ∀ {τ : State}, VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) τ → WP isa (.block recv) τ (VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁)) := fun {τ} R => by
    obtain ⟨t, run, fR, -, ho, sp, rd, wr⟩ := VG.Proof.AesGcmSiv.Arm.recv_ok L R.env R.args
    have fR' : Frame [⟨State.addr (VG.Proof.AesGcmSiv.Arm.prmOf σ₁).W + BitVec.ofNat 64 0, 16⟩] τ.mem t.mem := by
      rw [BitVec.add_zero]; exact fR
    exact WP.of_runBlock ⟨t, run, R.env.of_others ho sp rd wr, R.args.frame L fR' (by disj_tac L)⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.rel_envArg16 L R₀₁.env R₀₂.env R₀₁.args R₀₂.args [] (by simp) VG.Proof.AesGcmSiv.Arm.recv_check) (wr R₀₁) (wr R₀₂)
    fun ρ₁ ρ₂ R₁ R₂ => ?_
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.keys_rel L R₁.env R₂.env) (VG.Proof.AesGcmSiv.Arm.keys_ok L R₁.env) (VG.Proof.AesGcmSiv.Arm.keys_ok L R₂.env) fun a₁ a₂ K₁ K₂ => ?_
  have S₁ : VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) a₁ := ⟨K₁.env, R₁.args.frame L K₁.frame (by disj_tac L)⟩
  have S₂ : VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) a₂ := ⟨K₂.env, R₂.args.frame L K₂.frame (by disj_tac L)⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.crypt_rel L S₁ S₂) (VG.Proof.AesGcmSiv.Arm.crypt_ok L S₁.env S₁.args) (VG.Proof.AesGcmSiv.Arm.crypt_ok L S₂.env S₂.args)
    fun b₁ b₂ C₁ C₂ => ?_
  have U₁ : VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) b₁ := ⟨C₁.env, S₁.args.frame L C₁.frame (by disj_tac L)⟩
  have U₂ : VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) b₂ := ⟨C₂.env, S₂.args.frame L C₂.frame (by disj_tac L)⟩
  have hG : ∀ {σ τ : State}, VG.Proof.AesGcmSiv.Arm.KeysPost (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) σ τ → ∀ {u : State}, VG.Proof.AesGcmSiv.Arm.CryptPost (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) τ u →
      Spec.Gcm.blockAt u.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf σ₁).W + BitVec.ofNat 64 64) =
        GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt u.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf σ₁).W + BitVec.ofNat 64 16) 16)) ∧
      Spec.Gcm.blockAt u.mem (State.addr (VG.Proof.AesGcmSiv.Arm.prmOf σ₁).W + BitVec.ofNat 64 80) = 0 := by
    intro _ _ K _ C
    rw [Proof.AesGcm.Arm.blockAt_frame C.frame (by disj_tac L), K.hkey,
      Proof.AesGcm.Arm.blockAt_frame C.frame (by disj_tac L), K.acc,
      VG.Proof.AesGcmSiv.Arm.bytesAt_keep C.frame (by disj_tac L) (by decide)]
    exact ⟨rfl, rfl⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.polyval_rel L U₁ U₂) (VG.Proof.AesGcmSiv.Arm.polyval_ok L U₁.env U₁.args (hG K₁ C₁).1 (hG K₁ C₁).2)
    (VG.Proof.AesGcmSiv.Arm.polyval_ok L U₂.env U₂.args (hG K₂ C₂).1 (hG K₂ C₂).2) fun c₁ c₂ P₁ P₂ => ?_
  have V₁ : VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) c₁ := ⟨P₁.env, U₁.args.frame L P₁.frame (by disj_tac L)⟩
  have V₂ : VG.Proof.AesGcmSiv.Arm.PR (VG.Proof.AesGcmSiv.Arm.prmOf σ₁) c₂ := ⟨P₂.env, U₂.args.frame L P₂.frame (by disj_tac L)⟩
  refine VG.Proof.AesGcmSiv.Arm.rel_seq (VG.Proof.AesGcmSiv.Arm.tag_rel L V₁.env V₂.env (o := 176) (by decide)) (VG.Proof.AesGcmSiv.Arm.tag_ok L V₁.env (o := 176) (by decide))
    (VG.Proof.AesGcmSiv.Arm.tag_ok L V₂.env (o := 176) (by decide)) fun d₁ d₂ T₁ T₂ => ?_
  exact VG.Proof.AesGcmSiv.Arm.rel_envArg L T₁.env T₂.env (V₁.args.frame L T₁.frame (by disj_tac L))
    (V₂.args.frame L T₂.frame (by disj_tac L)) [] (by simp) VG.Proof.AesGcmSiv.Arm.openEnd_check

end VG.Proof.AesGcmSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.Arm.Verified`. -/
section

/-!
# AES-GCM-SIV on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, with the tag input computed with GHASH equal to the RFC's
(`tagInput_eq`, from `Proof.GcmSiv.Polyval`, imported here only so that the
other proofs need not import its algebra), a state satisfying each
precondition, and the shared contracts of `Spec/GcmSiv/Contract.lean` with
the working space as a last argument (`Proof/AesGcmSiv/Scratch.lean`, 470
words), with 8 bytes of stack: each call of `vg_aes_ctr32` or `vg_ghash`
pushes two words. The last section allocates the working space.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Impl.AesGcmSiv.Arm
open VG.Proof.AesGcm.Arm (bel arg args)

/-- RFC 8452 Appendix A: POLYVAL with `H` is GHASH with `H · x`. -/
theorem tagInput_eq : VG.Proof.AesGcmSiv.Arm.TagInputEq := fun a n pt d => by
  rw [GcmSiv.tagInput_eq, Spec.GcmSiv.polyval, GcmSiv.Polyval.polyvalFrom_eq]
  rfl

/-- `seal`'s state satisfying the precondition: no additional data, no
data, the tag at `0x4000` and `work` at `0x5000`, their addresses the stack
arguments at `sp + 12` and `sp + 16`. -/
def sealSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x800D then 0x40 else if a = 0x8011 then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x8000, 20⟩]
  wr := [⟨0, 0⟩, ⟨0x4000, 16⟩, ⟨0x5000, 3760⟩]

/-- `open`'s: as `seal`'s, with the tag read only. -/
def openSat : State :=
  { VG.Proof.AesGcmSiv.Arm.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4000, 16⟩, ⟨0x8000, 20⟩],
                 wr := [⟨0, 0⟩, ⟨0x5000, 3760⟩] }

theorem seal_verified : Verified Arm.target «seal» (Proof.AesGcmSiv.sealScratchContract Arm.abi 470 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesGcmSiv.Arm.seal_wp VG.Proof.AesGcmSiv.Arm.tagInput_eq hs) VG.Proof.AesGcmSiv.Arm.seal_ct (by
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Spec.GcmSiv.sealPost, VG.Proof.AesGcmSiv.Arm.sealArm, VG.Proof.AesGcmSiv.Arm.sealPre, VG.Proof.AesGcmSiv.Arm.oneLay, VG.Proof.AesGcmSiv.Arm.onePub, VG.Proof.AesGcmSiv.Arm.rounds, bel, arg, args, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesGcmSiv.Arm.sealSat)

theorem open_verified : Verified Arm.target «open» (Proof.AesGcmSiv.openScratchContract Arm.abi 470 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesGcmSiv.Arm.open_wp VG.Proof.AesGcmSiv.Arm.tagInput_eq hs) VG.Proof.AesGcmSiv.Arm.open_ct
    { pre := by sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.Arm.openArm, VG.Proof.AesGcmSiv.Arm.openResult, VG.Proof.AesGcmSiv.Arm.openPost,
        VG.Proof.AesGcmSiv.Arm.openPre, VG.Proof.AesGcmSiv.Arm.oneLay, VG.Proof.AesGcmSiv.Arm.onePub, VG.Proof.AesGcmSiv.Arm.rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr]
      -- `h` and the goal match on the same outcome of `decryptWith` with
      -- different matchers (`openPost`'s and `openContract`'s): split on it
      -- rather than have `exact h` unfold both to unify them.
      post := by
        intro s s' _ h
        sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.Arm.openArm, VG.Proof.AesGcmSiv.Arm.openResult, VG.Proof.AesGcmSiv.Arm.openPost,
          VG.Proof.AesGcmSiv.Arm.openPre, VG.Proof.AesGcmSiv.Arm.oneLay, VG.Proof.AesGcmSiv.Arm.onePub, VG.Proof.AesGcmSiv.Arm.rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.Arm.openArm, VG.Proof.AesGcmSiv.Arm.openResult, VG.Proof.AesGcmSiv.Arm.openPost,
          VG.Proof.AesGcmSiv.Arm.openPre, VG.Proof.AesGcmSiv.Arm.oneLay, VG.Proof.AesGcmSiv.Arm.onePub, VG.Proof.AesGcmSiv.Arm.rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        simp only [e]
        intro _
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by sig_implies_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.Arm.openArm, VG.Proof.AesGcmSiv.Arm.openResult, VG.Proof.AesGcmSiv.Arm.openPost,
        VG.Proof.AesGcmSiv.Arm.openPre, VG.Proof.AesGcmSiv.Arm.oneLay, VG.Proof.AesGcmSiv.Arm.onePub, VG.Proof.AesGcmSiv.Arm.rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr]
      sat := by sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.Arm.openArm, VG.Proof.AesGcmSiv.Arm.openResult, VG.Proof.AesGcmSiv.Arm.openPost,
        VG.Proof.AesGcmSiv.Arm.openPre, VG.Proof.AesGcmSiv.Arm.oneLay, VG.Proof.AesGcmSiv.Arm.onePub, VG.Proof.AesGcmSiv.Arm.rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr] [openSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesGcmSiv.Arm.openSat }

/-! ## With the working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (above), in a frame that allocates it
(`Verified.stackScratch`): their working space is their fifth stack
argument, after `aad_len`, `data`, `len` and `tag`, so the frame of 3792
bytes holds a copy of those four words, the address of the working space,
the saved `lr` and the working space (3784 bytes, rounded up to an
immediate `sub` can encode). The copies are read only where the pre- and
postconditions read the buffers, and `open`'s leak, whether it succeeds,
reads only its buffers (`Proof/AesGcmSiv/Scratch.lean`).
-/

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space: its four words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  { VG.Proof.AesGcmSiv.Arm.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0, 0⟩, ⟨0x4000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.GcmSiv.sealContract Arm.abi 3800).pre s := by
  implies_sat [Spec.GcmSiv.sealContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesGcmSiv.Arm.sealFrameSat

theorem seal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 3792 4 «seal»)
      (Spec.GcmSiv.sealContract Arm.abi 3800) :=
  Arm.Verified.stackScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 470) (pre := Spec.GcmSiv.sealPre Arm.abi.ptrBits)
    (post := Spec.GcmSiv.sealPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 4) VG.Proof.AesGcmSiv.Arm.seal_verified (by decide) (by decide) (by decide) (by decide)
    (sealPre_local _) (sealPost_local _) VG.Proof.AesGcmSiv.Arm.sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space: its four words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  { VG.Proof.AesGcmSiv.Arm.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4000, 16⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.GcmSiv.openContract Arm.abi 3800).pre s := by
  implies_sat [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Spec.GcmSiv.openPost,
    Spec.GcmSiv.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesGcmSiv.Arm.openFrameSat

theorem open_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 3792 4 «open»)
      (Spec.GcmSiv.openContract Arm.abi 3800) :=
  Arm.Verified.stackScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 470) (pre := Spec.GcmSiv.openPre Arm.abi.ptrBits)
    (post := Spec.GcmSiv.openPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.GcmSiv.openLeak Arm.abi.ptrBits))
    (m := 4) (Proof.AesGcmSiv.Verified.of_openScratch VG.Proof.AesGcmSiv.Arm.open_verified) (by decide) (by decide) (by decide) (by decide)
    (openPre_local _) (openPost_local _) VG.Proof.AesGcmSiv.Arm.openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesGcmSiv.Arm

end
