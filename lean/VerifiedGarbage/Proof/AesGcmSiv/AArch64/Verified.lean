import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Impl.AesGcmSiv.AArch64
import VerifiedGarbage.Proof.GcmSiv.Words32
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcmSiv.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.AArch64.Env`. -/
section

/-!
# AES-GCM-SIV on AArch64: the contracts, and where everything is

Untrusted: everything here is checked by Lean. The shared contracts of
`Spec/GcmSiv/Contract.lean`, with the working space as a last argument
(`Proof/AesGcmSiv/Scratch.lean`), imply these (`Verified.lean`). Every
argument but the working space is in a register, and a call (`bl`) stores
nothing in memory, so no stack is used.
-/

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.GcmSiv (ctxCiph keyLen encryptWith decryptWith zeros)

/-- The argument on the stack. -/
abbrev args (s : State) : Region := ⟨stackArgAddr s 0, 8⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 14

/-- What `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` both need, but for
the permissions: `(schedule = x0, rounds = x1, nonce = x2, aad = x3,
aad_len = x4, data = x5, len = x6, tag = x7, work = [sp])`. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .x0, 240⟩
  let nonce : Region := ⟨s.gpr .x2, 12⟩
  let aad : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let tag : Region := ⟨s.gpr .x7, 16⟩
  let work : Region := ⟨stackArg s 0, 3808⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (VG.Proof.AesGcmSiv.AArch64.args s) ∧ work.Disjoint (VG.Proof.AesGcmSiv.AArch64.args s) ∧
    (s.gpr .x0).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x7).toNat + 16 ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 3808 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 ≤ 2 ^ 64 ∧
    VG.Proof.AesGcmSiv.AArch64.rounds (s.gpr .x1)

/-- What `vg_aes_gcm_siv_seal` needs: `oneLay`, with `tag` the 16 bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .x0, 240⟩
  let nonce : Region := ⟨s.gpr .x2, 12⟩
  let aad : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let tag : Region := ⟨s.gpr .x7, 16⟩
  let work : Region := ⟨stackArg s 0, 3808⟩
  s.rd = [sch, nonce, aad, VG.Proof.AesGcmSiv.AArch64.args s] ∧ s.wr = [data, tag, work] ∧ VG.Proof.AesGcmSiv.AArch64.oneLay s

/-- What `vg_aes_gcm_siv_open` needs: `oneLay`, with the received tag the 16
bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .x0, 240⟩
  let nonce : Region := ⟨s.gpr .x2, 12⟩
  let aad : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let tag : Region := ⟨s.gpr .x7, 16⟩
  let work : Region := ⟨stackArg s 0, 3808⟩
  s.rd = [sch, nonce, aad, tag, VG.Proof.AesGcmSiv.AArch64.args s] ∧ s.wr = [data, work] ∧ VG.Proof.AesGcmSiv.AArch64.oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- `vg_aes_gcm_siv_seal`. -/
def sealAArch64 : Contract isa where
  pre := VG.Proof.AesGcmSiv.AArch64.sealPre
  post s s' :=
    VG.Spec.GcmSiv.encryptWith (VG.Spec.GcmSiv.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (keyLen (s.gpr .x1).toNat)
        (bytesAt s.mem (s.gpr .x2) 12) (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
        (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) =
      (bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat, bytesAt s'.mem (s.gpr .x7) 16)
  pub := VG.Proof.AesGcmSiv.AArch64.onePub

/-- What `vg_aes_gcm_siv_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  VG.Spec.GcmSiv.decryptWith (VG.Spec.GcmSiv.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (keyLen (s.gpr .x1).toNat)
    (bytesAt s.mem (s.gpr .x2) 12) (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
    (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (bytesAt s.mem (s.gpr .x7) 16)

/-- What `vg_aes_gcm_siv_open` leaves in `x0` and in the `n` bytes of data
at `D`, for the result `r`. Irreducible, so that checking a state against
it never evaluates `r`. -/
@[irreducible] def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
  | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem D n = VG.Spec.GcmSiv.zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : (s'.gpr .x0).setWidth 32 = 1) (hd : bytesAt s'.mem D n = pt) :
    VG.Proof.AesGcmSiv.AArch64.openPost r s' D n := by
  subst hr; unfold VG.Proof.AesGcmSiv.AArch64.openPost; exact ⟨hax, hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : (s'.gpr .x0).setWidth 32 = 0) (hd : bytesAt s'.mem D n = VG.Spec.GcmSiv.zeros n) :
    VG.Proof.AesGcmSiv.AArch64.openPost r s' D n := by
  subst hr; unfold VG.Proof.AesGcmSiv.AArch64.openPost; exact ⟨hax, hd⟩

/-- `vg_aes_gcm_siv_open`. It does not branch on whether the tag is right,
so its runs are related without the leak the shared contract allows. -/
def openAArch64 : Contract isa where
  pre := VG.Proof.AesGcmSiv.AArch64.openPre
  post s s' := VG.Proof.AesGcmSiv.AArch64.openPost (VG.Proof.AesGcmSiv.AArch64.openResult s) s' (s.gpr .x5) (s.gpr .x6).toNat
  pub := VG.Proof.AesGcmSiv.AArch64.onePub

end VG.Proof.AesGcmSiv.AArch64

/-!
## Where everything is

Untrusted: everything here is checked by Lean. The public arguments
(`Prm`): the key schedule of the key-generating key (240 bytes at `K`), the
working space (3808 bytes at `W`), the nonce (12 bytes at `N`), the
additional data (`al` bytes at `A`), the data (`n` bytes at `D`), the tag
(16 bytes at `T`), the stack pointer and the number of rounds; how their
regions lie (`Lay`); what a state may access (`Perm`); and the registers
that hold them throughout (`Env`), which the functions called preserve.
`grun` runs a block symbolically.
-/

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (covers_off in_off in_left covers_left Others Regs)

/-- Runs a block of the instructions the AES-GCM-SIV code uses. -/
macro "grun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
    sp_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq, and_self,
    Impl.AesGcm.AArch64.mov, Impl.AesGcm.AArch64.ptr, Impl.AesGcm.AArch64.imm, tagO, akO, ekO, hO, yO,
    cbO, ccO, tagPO, bO, skO, revO, ghO, scrO, List.cons_append, List.nil_append,
    List.append_assoc, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, and_true, true_and, eq_self_iff_true, $ts,*]) <;> try rfl)

/-- The public arguments. -/
structure Prm where
  /-- The key schedule of the key-generating key. -/
  K : Addr
  /-- The working space. -/
  W : Addr
  /-- The nonce. -/
  N : Addr
  /-- The additional data. -/
  A : Addr
  /-- The data. -/
  D : Addr
  /-- The tag. -/
  T : Addr
  /-- The stack pointer. -/
  SP : Addr
  /-- The number of rounds. -/
  R : Nat
  /-- The length of the additional data. -/
  al : Nat
  /-- The length of the data. -/
  n : Nat

/-- How the regions lie. -/
structure Lay (p : VG.Proof.AesGcmSiv.AArch64.Prm) : Prop where
  kw : p.K.toNat + 240 ≤ 2 ^ 64
  ww : p.W.toNat + 3808 ≤ 2 ^ 64
  nw : p.N.toNat + 12 ≤ 2 ^ 64
  aw : p.A.toNat + p.al ≤ 2 ^ 64
  dw : p.D.toNat + p.n ≤ 2 ^ 64
  k_w : (⟨p.K, 240⟩ : Region).Disjoint ⟨p.W, 3808⟩
  k_d : (⟨p.K, 240⟩ : Region).Disjoint ⟨p.D, p.n⟩
  n_w : (⟨p.N, 12⟩ : Region).Disjoint ⟨p.W, 3808⟩
  n_d : (⟨p.N, 12⟩ : Region).Disjoint ⟨p.D, p.n⟩
  a_w : (⟨p.A, p.al⟩ : Region).Disjoint ⟨p.W, 3808⟩
  a_d : (⟨p.A, p.al⟩ : Region).Disjoint ⟨p.D, p.n⟩
  d_w : (⟨p.D, p.n⟩ : Region).Disjoint ⟨p.W, 3808⟩
  tw : p.T.toNat + 16 ≤ 2 ^ 64
  t_w : (⟨p.T, 16⟩ : Region).Disjoint ⟨p.W, 3808⟩
  t_d : (⟨p.T, 16⟩ : Region).Disjoint ⟨p.D, p.n⟩
  rounds : p.R = 10 ∨ p.R = 14
  al_lt : p.al < 2 ^ 64
  n_lt : p.n < 2 ^ 64

/-- What a state may access. -/
structure Perm (p : VG.Proof.AesGcmSiv.AArch64.Prm) (s : State) : Prop where
  k : Covers [⟨p.K, 240⟩] (s.rd ++ s.wr)
  non : Covers [⟨p.N, 12⟩] (s.rd ++ s.wr)
  aad : Covers [⟨p.A, p.al⟩] (s.rd ++ s.wr)
  d : Covers [⟨p.D, p.n⟩] s.wr
  w : Covers [⟨p.W, 3808⟩] s.wr
  t : Covers [⟨p.T, 16⟩] (s.rd ++ s.wr)

theorem Perm.of_eq {p : VG.Proof.AesGcmSiv.AArch64.Prm} {s s' : State} (h : VG.Proof.AesGcmSiv.AArch64.Perm p s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesGcmSiv.AArch64.Perm p s' := by
  obtain ⟨a, b, c, d, e, f⟩ := h
  exact ⟨by rw [hrd, hwr]; exact a, by rw [hrd, hwr]; exact b, by rw [hrd, hwr]; exact c, by rw [hwr]; exact d,
    by rw [hwr]; exact e, by rw [hrd, hwr]; exact f⟩

/-- The registers holding the public arguments, the stack pointer, and what
the state may access. -/
structure Env (p : VG.Proof.AesGcmSiv.AArch64.Prm) (s : State) : Prop where
  x19 : s.gpr .x19 = p.W
  x20 : s.gpr .x20 = p.N
  x21 : s.gpr .x21 = p.K
  x22 : s.gpr .x22 = BitVec.ofNat 64 p.R
  x23 : s.gpr .x23 = p.A
  x24 : s.gpr .x24 = BitVec.ofNat 64 p.al
  x25 : s.gpr .x25 = p.D
  x26 : s.gpr .x26 = BitVec.ofNat 64 p.n
  sp : s.sp = p.SP
  perm : VG.Proof.AesGcmSiv.AArch64.Perm p s

/-- The registers `Env` pins. -/
abbrev envRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26]

/-- An environment, after code that keeps `x19`–`x26`, the stack pointer and
the permissions. -/
theorem Env.keep {p : VG.Proof.AesGcmSiv.AArch64.Prm} {s s' : State} (h : VG.Proof.AesGcmSiv.AArch64.Env p s) (hg : ∀ r ∈ VG.Proof.AesGcmSiv.AArch64.envRegs, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcmSiv.AArch64.Env p s' :=
  ⟨by rw [hg _ (by simp), h.x19], by rw [hg _ (by simp), h.x20], by rw [hg _ (by simp), h.x21],
    by rw [hg _ (by simp), h.x22], by rw [hg _ (by simp), h.x23], by rw [hg _ (by simp), h.x24],
    by rw [hg _ (by simp), h.x25], by rw [hg _ (by simp), h.x26], by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after a register apart from `x19`–`x26` is written. -/
theorem Env.write {p : VG.Proof.AesGcmSiv.AArch64.Prm} {s : State} (h : VG.Proof.AesGcmSiv.AArch64.Env p s) {r : Reg} (hr : r ∉ VG.Proof.AesGcmSiv.AArch64.envRegs) {sz : Size}
    (v : BitVec sz.bits) : VG.Proof.AesGcmSiv.AArch64.Env p (s.write sz r v) :=
  h.keep (fun q hq => by exact gpr_write_of_ne _ _ _ fun (e : q = r) => hr (e ▸ hq)) rfl rfl rfl

/-- An environment, after a call. -/
theorem Env.of_saved {p : VG.Proof.AesGcmSiv.AArch64.Prm} {s s' : State} (h : VG.Proof.AesGcmSiv.AArch64.Env p s)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcmSiv.AArch64.Env p s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide))
    hsp hrd hwr

/-- An environment, after a block that writes only the registers `rs`. -/
theorem Env.of_regs {p : VG.Proof.AesGcmSiv.AArch64.Prm} {s s' : State} {rs : List Reg} (h : VG.Proof.AesGcmSiv.AArch64.Env p s) (hr : Regs rs s s')
    (hd : ∀ r ∈ VG.Proof.AesGcmSiv.AArch64.envRegs, r ∉ rs := by decide) : VG.Proof.AesGcmSiv.AArch64.Env p s' :=
  h.keep (fun r h' => hr.others r (hd r h')) hr.sp hr.rd hr.wr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 3808) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 3808⟩ :=
  Offset.sub_base _ h

variable {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 3808) (hd : d + k ≤ 3808) :
    (⟨p.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem k_w' {d k : Nat} (hd : d + k ≤ 3808) : (⟨p.K, 240⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (VG.Proof.AesGcmSiv.AArch64.Lay.wSub hd)

theorem n_w' {d k : Nat} (hd : d + k ≤ 3808) : (⟨p.N, 12⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.n_w.sub_right (VG.Proof.AesGcmSiv.AArch64.Lay.wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 3808) : (⟨p.A, p.al⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (VG.Proof.AesGcmSiv.AArch64.Lay.wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 3808) : (⟨p.D, p.n⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (VG.Proof.AesGcmSiv.AArch64.Lay.wSub hd)

theorem t_w' {d k : Nat} (hd : d + k ≤ 3808) : (⟨p.T, 16⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.t_w.sub_right (VG.Proof.AesGcmSiv.AArch64.Lay.wSub hd)

theorem toNat_W {d : Nat} (hd : d < 3808) : (p.W + BitVec.ofNat 64 d).toNat = p.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem rounds_le : 16 * (p.R + 1) ≤ 240 := by rcases L.rounds with h | h <;> omega

theorem rounds3 : p.R = 10 ∨ p.R = 12 ∨ p.R = 14 := by rcases L.rounds with h | h <;> simp [h]

end Lay

/-- `W` itself, as the part at offset 0. -/
theorem Lay.w0 {p : VG.Proof.AesGcmSiv.AArch64.Prm} (_L : VG.Proof.AesGcmSiv.AArch64.Lay p) : p.W + BitVec.ofNat 64 0 = p.W := BitVec.add_zero _

namespace Perm

variable {p : VG.Proof.AesGcmSiv.AArch64.Prm} {s : State} (P : VG.Proof.AesGcmSiv.AArch64.Perm p s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 3808) : InRegions s.wr (p.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 3808) : InRegions (s.rd ++ s.wr) (p.W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 3808) : Covers [⟨p.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 3808) : Covers [⟨p.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_left (P.wC h)

/-- The first 2560 bytes of `W`, where AES-GCM's save area is. -/
theorem w2560 : Covers [⟨p.W, 2560⟩] s.wr :=
  Proof.AesGcm.AArch64.covers_prefix P.w (by decide)

theorem nR {d k : Nat} (h : d + k ≤ 12) : InRegions (s.rd ++ s.wr) (p.N + BitVec.ofNat 64 d) k :=
  in_off P.non h (by decide)

end Perm

/-- The registers `x19` and the permissions of an environment, as AES-GCM's
`exit_ok` needs them. -/
theorem Env.w2560R {p : VG.Proof.AesGcmSiv.AArch64.Prm} {s : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p s) : Covers [⟨p.W, 2560⟩] (s.rd ++ s.wr) :=
  covers_left E.perm.w2560

/-! ## Arithmetic -/

theorem ofNat_lsl (a k : Nat) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]

theorem movz_lit {k : Nat} (hk : k < 2 ^ 16) :
    BitVec.setWidth 64 (BitVec.ofNat 16 k) <<< (16 * 0) = BitVec.ofNat 64 k :=
  Proof.AesGcm.AArch64.movz_ofNat hk

theorem movz0 : (BitVec.setWidth 64 (0#16) <<< 0 : BitVec 64) = 0 := by decide

/-- A running block, with what is known of its result. -/
theorem WP.run {is : List Instr} {s : State} {Q R : State → Prop}
    (h : ∃ s', runBlock isa is s = some s' ∧ Q s') (hq : ∀ s', Q s' → R s') : WP isa (.block is) s R := by
  obtain ⟨s', h₁, h₂⟩ := h; exact WP.of_runBlock ⟨s', h₁, hq _ h₂⟩

/-- The `n` bytes at `p + d` within the `k` bytes at `p`. -/
theorem contains_at (p : Addr) {d n k : Nat} (h : d + n ≤ k) (hk : k < 2 ^ 64) :
    (⟨p, k⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := Offset.contains_base p h (by omega)

theorem contains_at0 (p : Addr) {n k : Nat} (h : n ≤ k) (hk : k < 2 ^ 64) :
    (⟨p, k⟩ : Region).Contains p n := by
  simpa using VG.Proof.AesGcmSiv.AArch64.contains_at p (d := 0) (by omega : 0 + n ≤ k) hk

/-- A block that writes only registers, with what is known of its result. -/
theorem WP.regs {is : List Instr} {s : State} {Q : State → Prop} {s' : State}
    (h : runBlock isa is s = some s') (hq : Q s') : WP isa (.block is) s Q := WP.of_runBlock ⟨s', h, hq⟩

end VG.Proof.AesGcmSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.AArch64.Derive`. -/
section

/-!
# AES-GCM-SIV on AArch64: the message keys (`derive`)

Untrusted: everything here is checked by Lean. Each step of `derive` writes
`little_endian_uint32(i) ‖ nonce` at `W + 112` and a zero block at
`W + 224` (`derArgs_ok`), on which `vg_aes_ctr32` leaves
`CIPH_K(little_endian_uint32(i) ‖ nonce)`, of which the first 8 bytes are
kept at `W + 16 + 8 i`: after the loop, the halves of `derive_keys`
(`derive_ok`, `DInv.keys`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (CtrCall CtrPost ctr_call GcmImpl in_off covers_off covers_left covers_cons
  covers_nil covers_append ofNat_add_ofNat add_ofNat_assoc ofNat_sub lsr_ofNat toNat_ofNat_of_lt eval_nonzero
  Others)

theorem setWidth_rt32 (v : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 v) = v := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem read4_readW (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by
  simp only [Mem.readW]; exact (BitVec.setWidth_eq _).symm

theorem read8_readW (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW]; exact (BitVec.setWidth_eq _).symm

/-- The memory after a step's block: the counter block and a zero block. -/
def derMem (m : Mem) (W N : Addr) (i : Nat) : Mem :=
  ((Proof.Cmac.store4 m (W + BitVec.ofNat 64 112) ((BitVec.ofNat 64 i).setWidth 32)
    (m.readW N 32) (m.readW (N + BitVec.ofNat 64 4) 32) (m.readW (N + BitVec.ofNat 64 8) 32)).writeW
    (W + BitVec.ofNat 64 224) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 232) (0 : BitVec 64)

/-- The arguments of a step: the counter block and a zero block. -/
theorem derArgs_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {i : Nat} (h27 : t.gpr .x27 = BitVec.ofNat 64 i) :
    ∃ t₁ : State, runBlock isa deriveBlock t = some t₁ ∧ t₁.mem = VG.Proof.AesGcmSiv.AArch64.derMem t.mem p.W p.N i ∧
      t₁.gpr .x0 = p.K ∧ t₁.gpr .x1 = BitVec.ofNat 64 p.R ∧ t₁.gpr .x2 = p.W + BitVec.ofNat 64 112 ∧
      t₁.gpr .x3 = p.W + BitVec.ofNat 64 224 ∧ t₁.gpr .x4 = BitVec.ofNat 64 1 ∧
      t₁.gpr .x5 = p.W + BitVec.ofNat 64 1760 ∧
      Others [.x9, .x10, .x11, .x0, .x1, .x2, .x3, .x4, .x5] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
  have n₀ : InRegions (t.rd ++ t.wr) p.N 4 := by simpa using E.perm.nR (d := 0) (k := 4) (by decide)
  have n₄ := E.perm.nR (d := 4) (k := 4) (by decide)
  have n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  have w₁ := E.perm.wW (show 112 + 4 ≤ 3808 by decide)
  have w₂ := E.perm.wW (show 116 + 4 ≤ 3808 by decide)
  have w₃ := E.perm.wW (show 120 + 4 ≤ 3808 by decide)
  have w₄ := E.perm.wW (show 124 + 4 ≤ 3808 by decide)
  have w₅ := E.perm.wW (show 224 + 8 ≤ 3808 by decide)
  have w₆ := E.perm.wW (show 232 + 8 ≤ 3808 by decide)
  refine ⟨_, by simp only [deriveBlock, zero16]; grun [E.x19, E.x20, BitVec.add_zero, n₀, n₄, n₈, w₁, w₂, w₃,
    w₄, w₅, w₆], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
  · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, VG.Proof.AesGcmSiv.AArch64.derMem, Proof.Cmac.store4, Mem.writeW,
      BitVec.setWidth_eq, VG.Proof.AesGcmSiv.AArch64.setWidth_rt32, VG.Proof.AesGcmSiv.AArch64.read4_readW, h27, add_ofNat_assoc, Nat.reduceAdd, Nat.reduceDiv, VG.Proof.AesGcmSiv.AArch64.movz0]
  · simp [gpr_write, E.x21]
  · simp [gpr_write, E.x22]
  · simp [gpr_write, E.x19]
  · simp [gpr_write, E.x19]
  · simp [gpr_write]
  · simp [gpr_write, E.x19]

theorem zc₁ (W : Addr) : (⟨W + BitVec.ofNat 64 224, 16⟩ : Region).Contains (W + BitVec.ofNat 64 224) (64 / 8) :=
  VG.Proof.AesGcmSiv.AArch64.contains_at0 _ (by decide) (by decide)

theorem zc₂ (W : Addr) : (⟨W + BitVec.ofNat 64 224, 16⟩ : Region).Contains (W + BitVec.ofNat 64 232) (64 / 8) := by
  rw [show W + BitVec.ofNat 64 232 = W + BitVec.ofNat 64 224 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc]]
  exact VG.Proof.AesGcmSiv.AArch64.contains_at _ (show 8 + 8 ≤ 16 by decide) (by decide)

/-- The counter block of a step: `little_endian_uint32(i) ‖ nonce`. -/
theorem derBlock_bytes (m : Mem) (W N : Addr) (i : Nat) :
    bytesAt (VG.Proof.AesGcmSiv.AArch64.derMem m W N i) (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt m N 12 := by
  have c₁ := VG.Proof.AesGcmSiv.AArch64.zc₁ W
  have c₂ := VG.Proof.AesGcmSiv.AArch64.zc₂ W
  rw [VG.Proof.AesGcmSiv.AArch64.derMem, Proof.AesGcm.AArch64.bytesAt_frame
      (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide),
    Proof.Cmac.bytesAt_store4, GcmSiv.le4_le32, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    show (12 : Nat) = 4 + (4 + 4) from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, add_ofNat_assoc]
  simp only [List.append_assoc]

/-- The zero block of a step. -/
theorem derZero_block (W N : Addr) (m : Mem) (i : Nat) :
    Spec.Gcm.blockAt (VG.Proof.AesGcmSiv.AArch64.derMem m W N i) (W + BitVec.ofNat 64 224) = 0 := by
  rw [VG.Proof.AesGcmSiv.AArch64.derMem, Spec.Gcm.blockAt, show W + BitVec.ofNat 64 232 = W + BitVec.ofNat 64 224 + BitVec.ofNat 64 8 by
    rw [add_ofNat_assoc], Proof.Cmac.bytesAt_store2]
  decide

theorem derMem_frame (m : Mem) (W N : Addr) (i : Nat) :
    Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 16⟩] m (VG.Proof.AesGcmSiv.AArch64.derMem m W N i) :=
  (((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp).writeW
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (VG.Proof.AesGcmSiv.AArch64.zc₁ W)).writeW
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (VG.Proof.AesGcmSiv.AArch64.zc₂ W)

/-- What `derive` writes. -/
abbrev derR (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 48⟩, ⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 16⟩,
    ⟨W + BitVec.ofNat 64 1760, 2048⟩]

/-- After `i` steps of `derive` from `σ`: the first `8 i` bytes of the halves
at `W + 16`. -/
structure DInv (p : VG.Proof.AesGcmSiv.AArch64.Prm) (σ : State) (i : Nat) (t : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t
  x27 : t.gpr .x27 = BitVec.ofNat 64 i
  le : i ≤ p.R / 2 - 1
  frame : Frame (VG.Proof.AesGcmSiv.AArch64.derR p.W) σ.mem t.mem
  out : bytesAt t.mem (p.W + BitVec.ofNat 64 16) (8 * i) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem p.K p.R) (bytesAt σ.mem p.N 12) i

/-- The code after the call of a step. -/
theorem derPost_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {i : Nat} (hi : i < p.R / 2 - 1)
    (h27 : t.gpr .x27 = BitVec.ofNat 64 i) :
    ∃ t' : State, runBlock isa derivePost t = some t' ∧
      t'.mem = t.mem.writeW (p.W + BitVec.ofNat 64 (16 + 8 * i)) (t.mem.readW (p.W + BitVec.ofNat 64 224) 64) ∧
      t'.gpr .x27 = BitVec.ofNat 64 (i + 1) ∧ t'.gpr .x10 = BitVec.ofNat 64 (p.R / 2 - 1 - (i + 1)) ∧
      Others [.x9, .x10, .x27] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR := L.rounds
  have rb := E.perm.wR (show 224 + 8 ≤ 3808 by decide)
  have wo := E.perm.wW (d := 16 + 8 * i) (n := 8) (by omega)
  have ea : p.W + BitVec.ofNat 64 i <<< 3 + BitVec.ofNat 64 16 = p.W + BitVec.ofNat 64 (16 + 8 * i) := by
    rw [VG.Proof.AesGcmSiv.AArch64.ofNat_lsl, add_ofNat_assoc]; congr 2; omega
  rw [← ea] at wo
  refine ⟨_, by simp only [derivePost]; grun [E.x19, E.x22, h27, rb, wo], ?_⟩
  refine ⟨?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
  · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, Mem.writeW, BitVec.setWidth_eq,
      VG.Proof.AesGcmSiv.AArch64.read8_readW, ea]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27, ofNat_add_ofNat]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27, ofNat_add_ofNat, E.x22]
    rw [lsr_ofNat _ _ (by omega), ofNat_sub (by omega) (by omega), ofNat_sub (by omega) (by omega)]

/-- Buffers outside `W` are kept by `derive`. -/
theorem bytesAt_derR {p : VG.Proof.AesGcmSiv.AArch64.Prm} (_L : VG.Proof.AesGcmSiv.AArch64.Lay p) {P : Addr} {len : Nat} (hP : (⟨P, len⟩ : Region).Disjoint ⟨p.W, 3808⟩)
    (hl : len ≤ 2 ^ 64) {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.AArch64.derR p.W) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hP.sub_right (Lay.wSub (by decide))) hl

/-- The key schedule is kept by `derive`. -/
theorem ciph_derR {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.AArch64.derR p.W) m m') :
    Spec.GcmSiv.ctxCiph m' p.K p.R = Spec.GcmSiv.ctxCiph m p.K p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [VG.Proof.AesGcmSiv.AArch64.bytesAt_derR L (L.k_w.sub_left (Region.sub_prefix L.rounds_le)) (by have := L.rounds_le; omega) hf]

/-- The arguments of a step's call. -/
theorem derCall {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t₁ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p t₁) (x0 : t₁.gpr .x0 = p.K)
    (x1 : t₁.gpr .x1 = BitVec.ofNat 64 p.R) (x2 : t₁.gpr .x2 = p.W + BitVec.ofNat 64 112)
    (x3 : t₁.gpr .x3 = p.W + BitVec.ofNat 64 224) (x4 : t₁.gpr .x4 = BitVec.ofNat 64 1)
    (x5 : t₁.gpr .x5 = p.W + BitVec.ofNat 64 1760) :
    CtrCall t₁ p.K (p.W + BitVec.ofNat 64 112) (p.W + BitVec.ofNat 64 224) (p.W + BitVec.ofNat 64 1760) p.R 1 :=
  { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5
    rounds := L.rounds3
    wrap := by rw [L.toNat_W (by decide)]; have := L.ww; omega
    n_lt := by decide
    kc := L.k_w' (by decide)
    kd := L.k_w' (by decide)
    ks := L.k_w' (by decide)
    cd := L.w_w (.inl (by decide)) (by decide) (by decide)
    cs := L.w_w (.inl (by decide)) (by decide) (by decide)
    ds := L.w_w (.inl (by decide)) (by decide) (by decide)
    reads := covers_append (covers_cons E₁.perm.k covers_nil)
      (covers_cons (E₁.perm.wCR (by decide)) (covers_cons (E₁.perm.wCR (by decide))
        (covers_cons (E₁.perm.wCR (by decide)) covers_nil)))
    writes := covers_cons (E₁.perm.wC (by decide)) (covers_cons (E₁.perm.wC (by decide))
        (covers_cons (E₁.perm.wC (by decide)) covers_nil)) }

/-- A step of `derive`. -/
theorem derStep_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {σ : State} {i : Nat} (hi : i < p.R / 2 - 1) {t : State}
    (I : VG.Proof.AesGcmSiv.AArch64.DInv p σ i t) :
    WP isa (.seq (.block deriveBlock) (.seq (callCtr v.callees) (.block derivePost))) t fun t' =>
      VG.Proof.AesGcmSiv.AArch64.DInv p σ (i + 1) t' ∧ t'.gpr .x10 = BitVec.ofNat 64 (p.R / 2 - 1 - (i + 1)) := by
  have hR := L.rounds
  have hw := L.ww
  have eN : bytesAt t.mem p.N 12 = bytesAt σ.mem p.N 12 := VG.Proof.AesGcmSiv.AArch64.bytesAt_derR L L.n_w (by decide) I.frame
  have eK : Spec.GcmSiv.ctxCiph t.mem p.K p.R = Spec.GcmSiv.ctxCiph σ.mem p.K p.R := VG.Proof.AesGcmSiv.AArch64.ciph_derR L I.frame
  obtain ⟨t₁, run₁, hm₁, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.AArch64.derArgs_ok I.env I.x27
  have E₁ : VG.Proof.AesGcmSiv.AArch64.Env p t₁ := I.env.keep (fun r hr => ho₁ r (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have cc := VG.Proof.AesGcmSiv.AArch64.derCall L E₁ x0 x1 x2 x3 x4 x5
  have hb₁ : bytesAt t₁.mem (p.W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt t.mem p.N 12 := by
    rw [hm₁]; exact VG.Proof.AesGcmSiv.AArch64.derBlock_bytes _ _ _ _
  have hz₁ : Spec.Gcm.blockAt t₁.mem (p.W + BitVec.ofNat 64 224) = 0 := by rw [hm₁]; exact VG.Proof.AesGcmSiv.AArch64.derZero_block _ _ _ _
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 112, 16⟩, ⟨p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by
    rw [hm₁]; exact VG.Proof.AesGcmSiv.AArch64.derMem_frame _ _ _ _
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_)
  have E₂ : VG.Proof.AesGcmSiv.AArch64.Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have h27₂ : t₂.gpr .x27 = BitVec.ofNat 64 i := by rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), I.x27]
  obtain ⟨t₃, run₃, hm₃, x27₃, x10₃, ho₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesGcmSiv.AArch64.derPost_ok L E₂ hi h27₂
  refine WP.of_runBlock ⟨t₃, run₃, ⟨E₂.keep (fun r hr => ho₃ r (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃, x27₃, by omega, ?_, ?_⟩,
    x10₃⟩
  · -- The frame.
    have fc := P.frame
    refine (I.frame.trans (f₁.sub fun r hr => ?_)).trans ((fc.sub fun r hr => ?_).trans (by
        rw [hm₃]
        exact (Frame.refl _ _).writeW (List.mem_cons_self) _ (Offset.contains p.W (d := 16 + 8 * i) (n := 8)
          (e := 16) (k := 48) (by omega) (by omega) (by omega))))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · -- The bytes.
    have fc := P.frame
    have dW : ∀ {d k : Nat}, d + k ≤ 3808 → 16 + 8 * i ≤ d ∨ d + k ≤ 16 →
        (⟨p.W + BitVec.ofNat 64 16, 8 * i⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ h₂ => L.w_w (by omega) (by omega) h₁
    have keep : bytesAt t₃.mem (p.W + BitVec.ofNat 64 16) (8 * i) =
        bytesAt t.mem (p.W + BitVec.ofNat 64 16) (8 * i) := by
      rw [hm₃, Proof.AesGcm.AArch64.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Region.contains_self (p.W + BitVec.ofNat 64 (16 + 8 * i)) 8))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW (by omega) (by omega)) (by omega),
        Proof.AesGcm.AArch64.bytesAt_frame fc (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact dW (by decide) (by omega)) (by omega),
        Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact dW (by decide) (by omega)) (by omega)]
    have hout := P.out
    simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
    have last : bytesAt t₃.mem (p.W + BitVec.ofNat 64 (16 + 8 * i)) 8 =
        (Spec.GcmSiv.ctxCiph σ.mem p.K p.R (Spec.GcmSiv.le32 i ++ bytesAt σ.mem p.N 12)).take 8 := by
      have e16 : bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 16 =
          bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 8 ++
            bytesAt t₂.mem (p.W + BitVec.ofNat 64 224 + BitVec.ofNat 64 8) 8 :=
        Proof.Cmac.bytesAt_add _ _ 8 8
      have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem p.K p.R = Spec.GcmSiv.ctxCiph t.mem p.K p.R := by
        unfold Spec.GcmSiv.ctxCiph
        rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rounds_le))
          (by omega)]
      rw [hm₃, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_readW,
        show bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 8 = (bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 16).take 8 by
          rw [e16, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)],
        Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt, hb₁,
        Proof.Cmac.aesWith_bytes _ _ (by rw [List.length_append, Proof.Cmac.bytesAt_length]; rfl),
        ← GcmSiv.aesWith_eq, show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem p.K (16 * (p.R + 1))) =
          Spec.GcmSiv.ctxCiph t₁.mem p.K p.R from rfl, ek₁, eK, eN]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, Proof.Cmac.bytesAt_add, GcmSiv.halves_succ, ← I.out, keep,
      add_ofNat_assoc, last]

/-- `derive`: the halves of `derive_keys` at `W + 16`. -/
theorem derive_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {σ : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p σ) :
    WP isa (derive v.callees) σ (VG.Proof.AesGcmSiv.AArch64.DInv p σ (p.R / 2 - 1)) := by
  have hR := L.rounds
  refine WP.seq (WP.run (Q := fun t => VG.Proof.AesGcmSiv.AArch64.DInv p σ 0 t) ⟨_, by grun [], ?_⟩ fun t I₀ => ?_)
  · exact ⟨E.keep (fun r hr => by
        simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
      by simp [gpr_write], Nat.zero_le _, by rw [mem_write]; exact Frame.refl _ _, rfl⟩
  refine WP.loop (M := isa) (fun m t => ∃ i, m = (p.R / 2 - 1) - i ∧ i < p.R / 2 - 1 ∧ VG.Proof.AesGcmSiv.AArch64.DInv p σ i t) ?_
    ((p.R / 2 - 1) - 0) _ ⟨0, rfl, by omega, I₀⟩
  rintro m t ⟨i, rfl, hi, I⟩
  refine WP.mono (VG.Proof.AesGcmSiv.AArch64.derStep_ok v L hi I) fun t' ⟨I', h10⟩ => ?_
  have ev := eval_nonzero h10 (by omega)
  by_cases he : i + 1 = p.R / 2 - 1
  · left; exact ⟨ev.trans (by simp [he]), he ▸ I'⟩
  · right; exact ⟨ev.trans (by simp; omega), (p.R / 2 - 1) - (i + 1), by omega, i + 1, rfl, by omega, I'⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DInv.keys {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {σ t : State} (I : VG.Proof.AesGcmSiv.AArch64.DInv p σ (p.R / 2 - 1) t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem p.K p.R) (Spec.GcmSiv.keyLen p.R) (bytesAt σ.mem p.N 12) =
      (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16,
        bytesAt t.mem (p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R)) := by
  have hR := L.rounds
  have hk : Spec.GcmSiv.keyLen p.R / 8 + 2 = p.R / 2 - 1 := by unfold Spec.GcmSiv.keyLen; omega
  have hl : 8 * (p.R / 2 - 1) = 16 + Spec.GcmSiv.keyLen p.R := by unfold Spec.GcmSiv.keyLen; omega
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, add_ofNat_assoc] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem p.K p.R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesGcmSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.AArch64.Keys`. -/
section

/-!
# AES-GCM-SIV on AArch64: the encryption key's schedule and GHASH's key

Untrusted: everything here is checked by Lean. `expand` writes the schedule
of the encryption key at `W + 240` (`expand_ok`), and `hkey` GHASH's key,
`H · x` for the authentication key `H` (POLYVAL's field element), in
GHASH's order at `W + 64`, and zeroes its accumulator (`hkey_ok`).
`keys_ok`: the three together.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (hkeyOf)
open VG.Proof.AesGcm.AArch64 (KeyCall KeyPost key_call GcmImpl covers_cons covers_nil covers_append
  ofNat_sub add_ofNat_assoc Others)

/-! ## `expand` -/

/-- What `expand` leaves: the schedule of the encryption key at `W + 240`. -/
structure ExpPost (p : VG.Proof.AesGcmSiv.AArch64.Prm) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t'
  frame : Frame [⟨p.W + BitVec.ofNat 64 240, 240⟩, ⟨p.W + BitVec.ofNat 64 1760, 512⟩] t.mem t'.mem
  ciph : Spec.GcmSiv.ctxCiph t'.mem (p.W + BitVec.ofNat 64 240) p.R =
    Spec.GcmSiv.aes (bytesAt t.mem (p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R))

theorem keyLen_lsl {R : Nat} (hR : R = 10 ∨ R = 14) :
    (BitVec.ofNat 64 R - BitVec.ofNat 64 6) <<< 2 = BitVec.ofNat 64 (Spec.GcmSiv.keyLen R) := by
  rw [ofNat_sub (by omega) (by omega), VG.Proof.AesGcmSiv.AArch64.ofNat_lsl]
  congr 1; unfold Spec.GcmSiv.keyLen; omega

/-- The arguments of `expand`'s call. -/
theorem expArgs_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) :
    ∃ t₁ : State, runBlock isa expandArgs t = some t₁ ∧
      KeyCall t₁ (p.W + BitVec.ofNat 64 32) (p.W + BitVec.ofNat 64 240) (p.W + BitVec.ofNat 64 1760)
        (Spec.GcmSiv.keyLen p.R) ∧ VG.Proof.AesGcmSiv.AArch64.Env p t₁ ∧ t₁.mem = t.mem := by
  have hl : Spec.GcmSiv.keyLen p.R = 16 ∨ Spec.GcmSiv.keyLen p.R = 32 := by
    unfold Spec.GcmSiv.keyLen; rcases L.rounds with h | h <;> omega
  have hl' := L.rounds
  refine ⟨_, by simp only [expandArgs]; grun [E.x19, E.x22], ⟨?x0, ?x1, ?x2, ?x3, ?len, ?kc, ?ks, ?cs, ?rd, ?wr⟩,
    E.keep (fun r hr => ?regs) ?sp ?rdE ?wrE, ?mem⟩
  case regs =>
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  case sp => rfl
  case rdE => rfl
  case wrE => rfl
  case mem => rfl
  case x0 => simp [gpr_write]
  case x1 => simp [gpr_write, VG.Proof.AesGcmSiv.AArch64.keyLen_lsl hl']
  case x2 => simp [gpr_write]
  case x3 => simp [gpr_write]
  case len => omega
  case kc => exact L.w_w (.inl (by omega)) (by omega) (by decide)
  case ks => exact L.w_w (.inl (by omega)) (by omega) (by decide)
  case cs => exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case rd =>
    exact covers_append (covers_cons (E.perm.wCR (by omega)) covers_nil)
      (covers_cons (E.perm.wCR (by decide)) (covers_cons (E.perm.wCR (by decide)) covers_nil))
  case wr => exact covers_cons (E.perm.wC (by decide)) (covers_cons (E.perm.wC (by decide)) covers_nil)

theorem expand_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) :
    WP isa (expand v.callees) t (VG.Proof.AesGcmSiv.AArch64.ExpPost p t) := by
  obtain ⟨t₁, run₁, kc, E₁, hm₁⟩ := VG.Proof.AesGcmSiv.AArch64.expArgs_ok L E
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (key_call v.key kc) fun t₂ P => ?_
  refine ⟨E₁.of_saved P.saved P.sp P.rd P.wr, by rw [← hm₁]; exact P.frame, ?_⟩
  have hr : Spec.Aes.rounds (Spec.GcmSiv.keyLen p.R / 4) = p.R := by
    unfold Spec.Aes.rounds Spec.GcmSiv.keyLen; rcases L.rounds with h | h <;> rw [h]
  have out := P.out
  rw [hr] at out
  rw [Spec.GcmSiv.ctxCiph, out, Spec.GcmSiv.aes, Proof.Cmac.bytesAt_length, hr, hm₁]

/-! ## `hkey` -/

/-- GHASH's key from the words `lo` and `hi` of the authentication key, as
`hkey` computes it: its high half and its low half. -/
abbrev hkHi (hi lo : BitVec 64) : BitVec 64 := (hi >>> 1) ^^^ (0xE100000000000000#64 &&& (0#64 - (lo &&& 1#64)))
abbrev hkLo (hi lo : BitVec 64) : BitVec 64 := (lo >>> 1) ||| (hi &&& 1#64).rotateRight 1

/-- The memory `hkey` leaves. -/
def hkeyMem (m : Mem) (W : Addr) : Mem :=
  let lo := m.readW (W + BitVec.ofNat 64 16) 64
  let hi := m.readW (W + BitVec.ofNat 64 24) 64
  (((m.writeW (W + BitVec.ofNat 64 64) (rev64 (VG.Proof.AesGcmSiv.AArch64.hkHi hi lo))).writeW (W + BitVec.ofNat 64 72)
    (rev64 (VG.Proof.AesGcmSiv.AArch64.hkLo hi lo))).writeW (W + BitVec.ofNat 64 80) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 88)
    (0 : BitVec 64)

theorem hkeyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 64, 32⟩] m (VG.Proof.AesGcmSiv.AArch64.hkeyMem m W) := by
  have ct : ∀ e, 64 ≤ e → e + 8 ≤ 96 → (⟨W + BitVec.ofNat 64 64, 32⟩ : Region).Contains (W + BitVec.ofNat 64 e) (64 / 8) :=
    fun e h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 64 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (ct 72 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (ct 80 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (ct 88 (by decide) (by decide))

theorem hkeyMem_key (m : Mem) (W : Addr) :
    Spec.Gcm.blockAt (VG.Proof.AesGcmSiv.AArch64.hkeyMem m W) (W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt m (W + BitVec.ofNat 64 16) 16)) := by
  have c₁ : (⟨W + BitVec.ofNat 64 80, 16⟩ : Region).Contains (W + BitVec.ofNat 64 80) (64 / 8) :=
    VG.Proof.AesGcmSiv.AArch64.contains_at0 _ (by decide) (by decide)
  have c₂ : (⟨W + BitVec.ofNat 64 80, 16⟩ : Region).Contains (W + BitVec.ofNat 64 88) (64 / 8) :=
    Offset.contains W (d := 88) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide)
  rw [VG.Proof.AesGcmSiv.AArch64.hkeyMem, Proof.AesGcm.AArch64.blockAt_frame
    (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide))]
  have e := Proof.Gcm.AArch64.blockAt_storeMem m (W + BitVec.ofNat 64 64)
    (VG.Proof.AesGcmSiv.AArch64.hkHi (m.readW (W + BitVec.ofNat 64 24) 64) (m.readW (W + BitVec.ofNat 64 16) 64))
    (VG.Proof.AesGcmSiv.AArch64.hkLo (m.readW (W + BitVec.ofNat 64 24) 64) (m.readW (W + BitVec.ofNat 64 16) 64))
  rw [Proof.Gcm.AArch64.storeMem, BitVec.add_zero, add_ofNat_assoc] at e
  rw [e, GcmSiv.Words.hkeyOf_words, GcmSiv.ofBytes_bytesAt, add_ofNat_assoc]

theorem hkeyMem_acc (m : Mem) (W : Addr) : Spec.Gcm.blockAt (VG.Proof.AesGcmSiv.AArch64.hkeyMem m W) (W + BitVec.ofNat 64 80) = 0 := by
  rw [VG.Proof.AesGcmSiv.AArch64.hkeyMem, show W + BitVec.ofNat 64 88 = W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc],
    Spec.Gcm.blockAt, Proof.Cmac.bytesAt_store2]
  decide

/-- `hkey`: GHASH's key at `W + 64` and its accumulator zeroed at `W + 80`. -/
theorem hkey_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) :
    ∃ t' : State, runBlock isa hkey t = some t' ∧ t'.mem = VG.Proof.AesGcmSiv.AArch64.hkeyMem t.mem p.W ∧
      Others [.x9, .x10, .x11, .x12, .x13] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₁ := E.perm.wR (show 16 + 8 ≤ 3808 by decide)
  have r₂ := E.perm.wR (show 24 + 8 ≤ 3808 by decide)
  have w₁ := E.perm.wW (show 64 + 8 ≤ 3808 by decide)
  have w₂ := E.perm.wW (show 72 + 8 ≤ 3808 by decide)
  have w₃ := E.perm.wW (show 80 + 8 ≤ 3808 by decide)
  have w₄ := E.perm.wW (show 88 + 8 ≤ 3808 by decide)
  refine ⟨_, by simp only [hkey, zero16]; grun [E.x19, r₁, r₂, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, VG.Proof.AesGcmSiv.AArch64.hkeyMem, Mem.writeW, BitVec.setWidth_eq,
      VG.Proof.AesGcmSiv.AArch64.read8_readW]
    rfl
  · others_tac
  all_goals rfl

/-! ## `keys` -/

/-- What `keys` writes: the keys, GHASH's key and accumulator, the blocks
the calls use, the encryption key's schedule and the working spaces. -/
abbrev keyR (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 112⟩, ⟨W + BitVec.ofNat 64 224, 16⟩, ⟨W + BitVec.ofNat 64 240, 3568⟩]

/-- What `keys` leaves, from `σ`. -/
structure KeysPost (p : VG.Proof.AesGcmSiv.AArch64.Prm) (σ t : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t
  frame : Frame (VG.Proof.AesGcmSiv.AArch64.keyR p.W) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem p.K p.R) (Spec.GcmSiv.keyLen p.R)
    (bytesAt σ.mem p.N 12)).1 = bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16
  ciph : Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R = Spec.GcmSiv.aes
    (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem p.K p.R) (Spec.GcmSiv.keyLen p.R) (bytesAt σ.mem p.N 12)).2
  hkey : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 64) =
    hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 80) = 0

theorem keys_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {σ : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p σ) :
    WP isa (VG.Impl.AesGcmSiv.AArch64.keys v.callees) σ (VG.Proof.AesGcmSiv.AArch64.KeysPost p σ) := by
  have hR := L.rounds
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.derive_ok v L E) fun t₂ I => ?_)
  have k0 : (⟨p.W + BitVec.ofNat 64 16, 112⟩ : Region) ∈ VG.Proof.AesGcmSiv.AArch64.keyR p.W := List.mem_cons_self
  have k1 : (⟨p.W + BitVec.ofNat 64 224, 16⟩ : Region) ∈ VG.Proof.AesGcmSiv.AArch64.keyR p.W := List.mem_cons_of_mem _ List.mem_cons_self
  have k2 : (⟨p.W + BitVec.ofNat 64 240, 3568⟩ : Region) ∈ VG.Proof.AesGcmSiv.AArch64.keyR p.W :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have f₂ : Frame (VG.Proof.AesGcmSiv.AArch64.keyR p.W) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, k0, Offset.sub p.W (by decide) (by decide)⟩
    · exact ⟨_, k0, Offset.sub p.W (by decide) (by decide)⟩
    · exact ⟨_, k1, fun _ h => h⟩
    · exact ⟨_, k2, Offset.sub p.W (by decide) (by decide)⟩
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.expand_ok v L I.env) fun t₃ X => ?_)
  obtain ⟨t₄, run₄, hm₄, ho₄, sp₄, rd₄, wr₄⟩ := VG.Proof.AesGcmSiv.AArch64.hkey_ok X.env
  have dK : ∀ {d k : Nat}, d + k ≤ 64 → 16 ≤ d → ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 240, 240⟩ : Region),
      ⟨p.W + BitVec.ofNat 64 1760, 512⟩], (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have f₃ : Frame (VG.Proof.AesGcmSiv.AArch64.keyR p.W) t₂.mem t₃.mem := X.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, k2, Offset.sub p.W (by decide) (by decide)⟩
  have f₄ : Frame (VG.Proof.AesGcmSiv.AArch64.keyR p.W) t₃.mem t₄.mem := by
    rw [hm₄]; exact (VG.Proof.AesGcmSiv.AArch64.hkeyMem_frame _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, k0, Offset.sub p.W (by decide) (by decide)⟩
  have dH : ∀ {d k : Nat}, d + k ≤ 64 → ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl h) (by omega) (by decide)
  have dH' : ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 240, 240⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have keys := I.keys L
  have a₃ : bytesAt t₃.mem (p.W + BitVec.ofNat 64 16) 16 = bytesAt t₂.mem (p.W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.AArch64.bytesAt_frame X.frame (dK (by decide) (by decide)) (by decide)
  have a₄ : bytesAt t₄.mem (p.W + BitVec.ofNat 64 16) 16 = bytesAt t₃.mem (p.W + BitVec.ofNat 64 16) 16 := by
    rw [hm₄]; exact Proof.AesGcm.AArch64.bytesAt_frame (VG.Proof.AesGcmSiv.AArch64.hkeyMem_frame _ _) (dH (by decide)) (by decide)
  refine WP.of_runBlock ⟨t₄, run₄, X.env.keep (fun r hr => ho₄ r (by
      simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄,
    (f₂.trans f₃).trans f₄, ?_, ?_, ?_, ?_⟩
  · rw [keys, a₄, a₃]
  · have hk := keys
    rw [Prod.ext_iff] at hk
    rw [hk.2, ← X.ciph]
    unfold Spec.GcmSiv.ctxCiph
    rw [hm₄, Proof.AesGcm.AArch64.bytesAt_frame (VG.Proof.AesGcmSiv.AArch64.hkeyMem_frame _ _) (fun r hr =>
      (dH' r hr).sub_left (Region.sub_prefix L.rounds_le)) (by omega)]
  · rw [hm₄, VG.Proof.AesGcmSiv.AArch64.hkeyMem_key, ← hm₄, a₄]
  · rw [hm₄]; exact VG.Proof.AesGcmSiv.AArch64.hkeyMem_acc _ _

end VG.Proof.AesGcmSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.AArch64.Absorb`. -/
section

/-!
# AES-GCM-SIV on AArch64: POLYVAL (`chunk`, `absorb`)

Untrusted: everything here is checked by Lean. POLYVAL is GHASH with the
key `H · x` on the same bits (`Proof.GcmSiv.Polyval`): `revLoop` copies up
to 64 blocks to `W + 480` with the bytes of each reversed, so that GHASH
reads each copy as POLYVAL reads the original (`revLoop_ok`), and `vg_ghash`
absorbs them (`chunk_ok`); `absorb` absorbs the padded string so, its last
bytes padded with zeros in the block at `W + 224` (`absorb_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.AesGcm.AArch64 (GcmImpl GhCall GhPost gh_call ofNat_add_ofNat in_off toNat_ofNat_of_lt covers_off
  covers_left covers_cons covers_nil covers_append ofNat_sub lsr_ofNat lsl4_ofNat eval_zero eval_nonzero
  add_ofNat_assoc Others in_of_covers)

/-! ## Reversing blocks -/

/-- The body of `revLoop`. -/
abbrev revBody : List Instr :=
  [.ldr .x .x12 .x11 0, .ldr .x .x13 .x11 8, .rev .x12 .x12, .rev .x13 .x13,
    .str .x .x13 .x14 0, .str .x .x12 .x14 8, Impl.AesGcm.AArch64.ptr .x11 .x11 16,
    Impl.AesGcm.AArch64.ptr .x14 .x14 16, .subImm .x .x15 .x15 1]

/-- The registers `revLoop` writes. -/
abbrev revRegs : List Reg := [.x11, .x12, .x13, .x14, .x15]

theorem revStep_ok {t : State} {S P : Addr} {j : Nat} (hj : j < 2 ^ 63)
    (h11 : t.gpr .x11 = S) (h14 : t.gpr .x14 = P) (h15 : t.gpr .x15 = BitVec.ofNat 64 (j + 1))
    (hr₀ : InRegions (t.rd ++ t.wr) S 8) (hr₈ : InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 8) 8)
    (hw₀ : InRegions t.wr P 8) (hw₈ : InRegions t.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ t' : State, runBlock isa VG.Proof.AesGcmSiv.AArch64.revBody t = some t' ∧
      t'.mem = Proof.Gcm.AArch64.storeMem t.mem P (t.mem.readW (S + BitVec.ofNat 64 8) 64) (t.mem.readW S 64) ∧
      t'.gpr .x11 = S + BitVec.ofNat 64 16 ∧ t'.gpr .x14 = P + BitVec.ofNat 64 16 ∧
      t'.gpr .x15 = BitVec.ofNat 64 j ∧ Others VG.Proof.AesGcmSiv.AArch64.revRegs t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [h11, h14, BitVec.add_zero, hr₀, hr₈, hw₀, hw₈], ?_⟩
  refine ⟨?_, by simp [gpr_write, h11], by simp [gpr_write, h14], ?_, by others_tac, rfl, rfl, rfl⟩
  · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, Proof.Gcm.AArch64.storeMem, Mem.writeW,
      BitVec.setWidth_eq, BitVec.add_zero, VG.Proof.AesGcmSiv.AArch64.read8_readW]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h15]
    rw [show (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 1) = BitVec.ofNat 64 j from by
      rw [ofNat_sub (by omega) (by omega)]; rfl]

theorem blocksAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Gcm.blocksAt m p (j + 1) = Spec.Gcm.blocksAt m p j ++ [Spec.Gcm.blockAt m (p + BitVec.ofNat 64 (16 * j))] := by
  simp [Spec.Gcm.blocksAt, List.range_succ]

/-- POLYVAL's field elements of the `k` blocks at `Q`. -/
abbrev elemsAt (m : Mem) (Q : Addr) (k : Nat) : List Spec.GcmSiv.Elem :=
  (List.range k).map fun i => Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * i)) 16)

/-- What `revLoop` leaves after `j` blocks, from `t₀`. -/
structure RInv (W : Addr) (Q : Addr) (c j : Nat) (t₀ t : State) : Prop where
  x11 : t.gpr .x11 = Q + BitVec.ofNat 64 (16 * j)
  x14 : t.gpr .x14 = W + BitVec.ofNat 64 (480 + 16 * j)
  x15 : t.gpr .x15 = BitVec.ofNat 64 (c - j)
  frame : Frame [⟨W + BitVec.ofNat 64 480, 16 * c⟩] t₀.mem t.mem
  out : Spec.Gcm.blocksAt t.mem (W + BitVec.ofNat 64 480) j = VG.Proof.AesGcmSiv.AArch64.elemsAt t₀.mem Q j
  others : Others VG.Proof.AesGcmSiv.AArch64.revRegs t₀ t
  sp : t.sp = t₀.sp
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr

/-- What a chunk may read: `k` bytes at `Q` apart from what it writes. -/
structure Src (p : VG.Proof.AesGcmSiv.AArch64.Prm) (s : State) (Q : Addr) (k : Nat) : Prop where
  rd : Covers [⟨Q, k⟩] (s.rd ++ s.wr)
  lt : k < 2 ^ 64
  wrap : Q.toNat + k ≤ 2 ^ 64
  y : (⟨Q, k⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 80, 16⟩
  rev : (⟨Q, k⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 480, 1280⟩

namespace Src

variable {p : VG.Proof.AesGcmSiv.AArch64.Prm} {s : State} {Q : Addr} {n : Nat} (h : VG.Proof.AesGcmSiv.AArch64.Src p s Q n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcmSiv.AArch64.Src p s' Q n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcmSiv.AArch64.Src p s (Q + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (Q.toNat + k) (2 ^ 64)
    omega
  y := h.y.sub_left (Offset.sub_base Q (by omega))
  rev := h.rev.sub_left (Offset.sub_base Q (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcmSiv.AArch64.Src p s Q k where
  rd := Proof.AesGcm.AArch64.covers_prefix h.rd hk
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  y := h.y.sub_left (Region.sub_prefix hk)
  rev := h.rev.sub_left (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : VG.Proof.AesGcmSiv.AArch64.Src p s (Q + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega)).take (by omega)

end Src

/-- A buffer apart from `W`. -/
theorem Src.ofW {p : VG.Proof.AesGcmSiv.AArch64.Prm} (_L : VG.Proof.AesGcmSiv.AArch64.Lay p) {s : State} {Q : Addr} {n : Nat} (hc : Covers [⟨Q, n⟩] (s.rd ++ s.wr))
    (hlt : n < 2 ^ 64) (hw : Q.toNat + n ≤ 2 ^ 64) (hd : (⟨Q, n⟩ : Region).Disjoint ⟨p.W, 3808⟩) : VG.Proof.AesGcmSiv.AArch64.Src p s Q n :=
  ⟨hc, hlt, hw, hd.sub_right (Lay.wSub (by decide)), hd.sub_right (Lay.wSub (by decide))⟩

/-- `revLoop`: `c` blocks at `Q` copied to `W + 480`, each reversed, so that
GHASH reads POLYVAL's field elements of them. -/
theorem revLoop_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t₀ : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t₀) {Q : Addr} {c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 64) (hQ : VG.Proof.AesGcmSiv.AArch64.Src p t₀ Q (16 * c)) (h11 : t₀.gpr .x11 = Q)
    (h14 : t₀.gpr .x14 = p.W + BitVec.ofNat 64 480) (h15 : t₀.gpr .x15 = BitVec.ofNat 64 c) :
    WP isa revLoop t₀ fun t => Frame [⟨p.W + BitVec.ofNat 64 480, 16 * c⟩] t₀.mem t.mem ∧
      Spec.Gcm.blocksAt t.mem (p.W + BitVec.ofNat 64 480) c = VG.Proof.AesGcmSiv.AArch64.elemsAt t₀.mem Q c ∧
      Others VG.Proof.AesGcmSiv.AArch64.revRegs t₀ t ∧ t.sp = t₀.sp ∧ t.rd = t₀.rd ∧ t.wr = t₀.wr := by
  have I₀ : VG.Proof.AesGcmSiv.AArch64.RInv p.W Q c 0 t₀ t₀ := ⟨by rw [h11, Nat.mul_zero, BitVec.add_zero], by rw [h14],
    by rw [h15, Nat.sub_zero], Frame.refl _ _, by simp only [Spec.Gcm.blocksAt, VG.Proof.AesGcmSiv.AArch64.elemsAt, List.range_zero, List.map_nil],
    fun _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcmSiv.AArch64.revBody) (c := .nonzero .x .x15)
    (fun (m : Nat) (t : State) => ∃ j, m = c - j ∧ j < c ∧ VG.Proof.AesGcmSiv.AArch64.RInv p.W Q c j t₀ t) ?_ (c - 0) t₀ ⟨0, rfl, hc1, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  have hw := L.ww
  have rq₀ := in_off (d := 16 * j) (n := 8) hQ.rd (by omega) hQ.lt
  have rq₈ := in_off (d := 16 * j + 8) (n := 8) hQ.rd (by omega) hQ.lt
  rw [← add_ofNat_assoc] at rq₈
  have ww₀ := E.perm.wW (d := 480 + 16 * j) (n := 8) (by omega)
  have ww₈ := E.perm.wW (d := 480 + 16 * j + 8) (n := 8) (by omega)
  rw [← add_ofNat_assoc] at ww₈
  rw [← I.rd, ← I.wr] at rq₀ rq₈
  rw [← I.wr] at ww₀ ww₈
  obtain ⟨t', run', hm', x11', x14', x15', ho', sp', rd', wr'⟩ :=
    VG.Proof.AesGcmSiv.AArch64.revStep_ok (j := c - j - 1) (by omega) I.x11 I.x14 (by rw [I.x15]; congr 1; omega) rq₀ rq₈ ww₀ ww₈
  refine WP.of_runBlock ⟨t', run', ?_⟩
  -- The source is outside the copies.
  have src : ∀ d, d + 8 ≤ 16 * c → t.mem.readW (Q + BitVec.ofNat 64 d) 64 = t₀.mem.readW (Q + BitVec.ofNat 64 d) 64 :=
    fun d hd => I.frame.readW (r := ⟨Q + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hQ.rev.sub_left (Offset.sub_base Q (by omega))).sub_right (Offset.sub p.W (by omega) (by omega)))
      (by decide)
  have c₁ : (⟨p.W + BitVec.ofNat 64 480, 16 * c⟩ : Region).Contains (p.W + BitVec.ofNat 64 (480 + 16 * j)) (64 / 8) :=
    Offset.contains p.W (by omega) (by omega) (by omega)
  have c₂ : (⟨p.W + BitVec.ofNat 64 480, 16 * c⟩ : Region).Contains
      (p.W + BitVec.ofNat 64 (480 + 16 * j) + BitVec.ofNat 64 8) (64 / 8) := by
    rw [add_ofNat_assoc]; exact Offset.contains p.W (by omega) (by omega) (by omega)
  have fr : Frame [⟨p.W + BitVec.ofNat 64 (480 + 16 * j), 16⟩] t.mem t'.mem := by
    rw [hm', Proof.Gcm.AArch64.storeMem, BitVec.add_zero]; exact Proof.Cmac.frame_store2 _ _ _
  have I' : VG.Proof.AesGcmSiv.AArch64.RInv p.W Q c (j + 1) t₀ t' := by
    refine ⟨by rw [x11', add_ofNat_assoc]; congr 2, by rw [x14', add_ofNat_assoc]; congr 2,
      by rw [x15', Nat.sub_sub], ?_, ?_, fun r hr => by rw [ho' r hr, I.others r hr],
      by rw [sp', I.sp], by rw [rd', I.rd], by rw [wr', I.wr]⟩
    · rw [hm', Proof.Gcm.AArch64.storeMem, BitVec.add_zero]
      exact (I.frame.writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂
    · have s₈ := src (16 * j + 8) (by omega)
      rw [← add_ofNat_assoc] at s₈
      rw [VG.Proof.AesGcmSiv.AArch64.blocksAt_succ, Proof.AesGcm.AArch64.blocksAt_frame fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint p.W (.inl (by omega)) (by omega) (by omega)) (by omega), I.out]
      simp only [VG.Proof.AesGcmSiv.AArch64.elemsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [add_ofNat_assoc, hm', Proof.Gcm.AArch64.blockAt_storeMem,
        GcmSiv.ofBytes_bytesAt, src (16 * j) (by omega), s₈]
  have ev := eval_nonzero x15' (show c - j - 1 < 2 ^ 64 by omega)
  by_cases he : j + 1 = c
  · left
    refine ⟨ev.trans (by simp [show c - j - 1 = 0 by omega]), ?_⟩
    exact ⟨I'.frame, he ▸ I'.out, I'.others, I'.sp, I'.rd, I'.wr⟩
  · right
    exact ⟨ev.trans (by simp; omega), c - (j + 1), by omega, j + 1, rfl, by omega, I'⟩

/-! ## A chunk -/

/-- What a chunk writes: GHASH's accumulator, the reversed blocks and
`vg_ghash`'s working space. -/
abbrev absR (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 480, 1280⟩]

/-- What a chunk leaves, from `t`, after absorbing `k` blocks of the `m`
bytes at `Q`. -/
structure ChunkPost (p : VG.Proof.AesGcmSiv.AArch64.Prm) (Q : Addr) (m k : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  x27 : t'.gpr .x27 = Q + BitVec.ofNat 64 (16 * k)
  x28 : t'.gpr .x28 = BitVec.ofNat 64 (m - 16 * k)
  x9 : t'.gpr .x9 = BitVec.ofNat 64 ((m - 16 * k) / 16)
  frame : Frame (VG.Proof.AesGcmSiv.AArch64.absR p.W) t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 80)) (VG.Proof.AesGcmSiv.AArch64.elemsAt t.mem Q k)

/-- `chunkLen`: the number of blocks of the chunk. -/
theorem chunkLen_ok {t : State} {m : Nat} (hm : m < 2 ^ 64) (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa chunkLen t fun t' => t'.gpr .x10 = BitVec.ofNat 64 (min (m / 16) 64) ∧
      Others [.x10] t t' ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, x10₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.lsr .x .x10 .x28 10] t = some t₁ ∧
      t₁.gpr .x10 = BitVec.ofNat 64 (m / 1024) ∧ Others [.x10] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by grun [], ?_, by others_tac, (by rfl), (by rfl), (by rfl), (by rfl)⟩
    simp [gpr_write, h28, lsr_ofNat _ _ hm]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (m / 1024 = 0)) (eval_zero x10₁ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 1024 = 0 := by simpa using ht
    refine WP.run ⟨_, by grun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, ite_true, BitVec.setWidth_eq, ho₁ .x28 (by decide), h28, lsr_ofNat _ _ hm]
      congr 1; omega
    · simp only [List.mem_singleton] at hr; simp only [gpr_write, hr, ite_false]; exact ho₁ r (by simpa using hr)
  · have h0 : m / 1024 ≠ 0 := by simpa using hf
    refine WP.run ⟨_, by grun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, ite_true, BitVec.setWidth_eq, VG.Proof.AesGcmSiv.AArch64.movz_lit (show 64 < 2 ^ 16 by decide)]
      congr 1; omega
    · simp only [List.mem_singleton] at hr; simp only [gpr_write, hr, ite_false]; exact ho₁ r (by simpa using hr)

/-- A chunk up to its call: up to 64 blocks reversed at `W + 480`, the
pointer and the count past them, and the arguments of `vg_ghash`. -/
structure ChunkPre (p : VG.Proof.AesGcmSiv.AArch64.Prm) (Q : Addr) (m k : Nat) (t t₅ : State) : Prop where
  call : GhCall t₅ (p.W + BitVec.ofNat 64 64) (p.W + BitVec.ofNat 64 80) (p.W + BitVec.ofNat 64 480)
    (p.W + BitVec.ofNat 64 1504) k
  env : VG.Proof.AesGcmSiv.AArch64.Env p t₅
  rd : t₅.rd = t.rd
  wr : t₅.wr = t.wr
  x27 : t₅.gpr .x27 = Q + BitVec.ofNat 64 (16 * k)
  x28 : t₅.gpr .x28 = BitVec.ofNat 64 (m - 16 * k)
  frame : Frame [⟨p.W + BitVec.ofNat 64 480, 16 * k⟩] t.mem t₅.mem
  out : Spec.Gcm.blocksAt t₅.mem (p.W + BitVec.ofNat 64 480) k = VG.Proof.AesGcmSiv.AArch64.elemsAt t.mem Q k

/-- The pieces of a chunk before its call. -/
theorem chunkPre_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {Q : Addr} {m : Nat} (hm : m < 2 ^ 64)
    (h16 : 16 ≤ m) (hQ : VG.Proof.AesGcmSiv.AArch64.Src p t Q (16 * (m / 16))) (h27 : t.gpr .x27 = Q) (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa chunkPre t (VG.Proof.AesGcmSiv.AArch64.ChunkPre p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.chunkLen_ok hm h28) fun t₁ ⟨x10₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ => ?_)
  obtain ⟨t₂, run₂, x11₂, x14₂, x15₂, ho₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa
      [Impl.AesGcm.AArch64.mov .x11 .x27, Impl.AesGcm.AArch64.ptr .x14 .x19 revO, Impl.AesGcm.AArch64.mov .x15 .x10]
        t₁ = some t₂ ∧
      t₂.gpr .x11 = Q ∧ t₂.gpr .x14 = p.W + BitVec.ofNat 64 480 ∧
      t₂.gpr .x15 = BitVec.ofNat 64 (min (m / 16) 64) ∧ Others [.x11, .x14, .x15] t₁ t₂ ∧ t₂.mem = t₁.mem ∧
      t₂.sp = t₁.sp ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    refine ⟨_, by grun [], ?_, ?_, ?_, by others_tac, (by rfl), (by rfl), (by rfl), (by rfl)⟩
    · simp [gpr_write, ho₁ .x27 (by decide), h27]
    · simp [gpr_write, ho₁ .x19 (by decide), E.x19]
    · simp [gpr_write, x10₁]
  refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
  have E₂ : VG.Proof.AesGcmSiv.AArch64.Env p t₂ := E.keep (fun r hr => by
      rw [ho₂ r (by
        simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ho₁ r (by
        simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)])
    (by rw [sp₂, sp₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have hk1 : 1 ≤ min (m / 16) 64 := by omega
  have hQ₂ : VG.Proof.AesGcmSiv.AArch64.Src p t₂ Q (16 * min (m / 16) 64) := (hQ.take (by omega)).of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.revLoop_ok L E₂ hk1 (by omega) hQ₂ x11₂ x14₂ x15₂)
    fun t₃ ⟨fr₃, out₃, ho₃, sp₃, rd₃, wr₃⟩ => ?_)
  have E₃ : VG.Proof.AesGcmSiv.AArch64.Env p t₃ := E₂.keep (fun r hr => ho₃ r (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, VG.Proof.AesGcmSiv.AArch64.revRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃
  have x10₃ : t₃.gpr .x10 = BitVec.ofNat 64 (min (m / 16) 64) := by
    rw [ho₃ _ (by decide), ho₂ _ (by decide), x10₁]
  have x27₃ : t₃.gpr .x27 = Q := by rw [ho₃ _ (by decide), ho₂ _ (by decide), ho₁ _ (by decide), h27]
  have x28₃ : t₃.gpr .x28 = BitVec.ofNat 64 m := by rw [ho₃ _ (by decide), ho₂ _ (by decide), ho₁ _ (by decide), h28]
  have m₂₁ : t₂.mem = t.mem := by rw [m₂, m₁]
  rw [m₂₁] at fr₃ out₃
  refine WP.run ⟨_, by simp only [chunkArgs, ghArgs]; grun [], rfl⟩ fun t₄ ht₄ => ?_
  subst ht₄
  refine ⟨⟨?x0, ?x1, ?x2, ?x3, ?x4, ?n_lt, ?hy, ?hs, ?yd, ?ys, ?ds, ?reads, ?writes⟩,
    E₃.keep (fun r hr => ?regs) (by rfl) (by rfl) (by rfl), by simp only [rd_write]; rw [rd₃, rd₂, rd₁], by simp only [wr_write]; rw [wr₃, wr₂, wr₁], ?_, ?_,
    by simp only [mem_write]; exact fr₃, by simp only [mem_write]; exact out₃⟩
  case regs =>
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  case x0 => simp [gpr_write, E₃.x19]
  case x1 => simp [gpr_write, E₃.x19]
  case x2 => simp [gpr_write, E₃.x19]
  case x3 => simp [gpr_write, x10₃]
  case x4 => simp [gpr_write, E₃.x19]
  case n_lt => omega
  case hy => exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case hs => exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case yd => exact L.w_w (.inl (by omega)) (by decide) (by omega)
  case ys => exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case ds => exact L.w_w (.inl (by omega)) (by omega) (by decide)
  case reads =>
    exact covers_append (covers_cons (E₃.perm.wCR (by decide)) (covers_cons (E₃.perm.wCR (by omega)) covers_nil))
      (covers_cons (E₃.perm.wCR (by decide)) (covers_cons (E₃.perm.wCR (by decide)) covers_nil))
  case writes => exact covers_cons (E₃.perm.wC (by decide)) (covers_cons (E₃.perm.wC (by decide)) covers_nil)
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x27₃, x10₃, VG.Proof.AesGcmSiv.AArch64.ofNat_lsl,
      add_ofNat_assoc]
    congr 2; omega
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x28₃, x10₃, VG.Proof.AesGcmSiv.AArch64.ofNat_lsl]
    rw [ofNat_sub (by omega) hm]; congr 2; omega

theorem chunk_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ : VG.Proof.AesGcmSiv.AArch64.Src p t Q (16 * (m / 16))) (h27 : t.gpr .x27 = Q)
    (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa (chunk v.callees) t (VG.Proof.AesGcmSiv.AArch64.ChunkPost p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  have hk : 16 * min (m / 16) 64 ≤ 1024 := by omega
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.chunkPre_ok L E hm h16 hQ h27 h28) fun t₅ Pr => ?_)
  refine WP.seq (WP.mono (gh_call v.gh Pr.call) fun t₆ P => ?_)
  have E₆ : VG.Proof.AesGcmSiv.AArch64.Env p t₆ := Pr.env.of_saved P.saved P.sp P.rd P.wr
  have x28₆ : t₆.gpr .x28 = BitVec.ofNat 64 (m - 16 * min (m / 16) 64) := by
    rw [P.saved _ (by decide) (by decide), Pr.x28]
  have dH : ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 480, 16 * min (m / 16) 64⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  have dY : ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 480, 16 * min (m / 16) 64⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 80, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  have out₆ := P.out
  rw [Proof.AesGcm.AArch64.blockAt_frame Pr.frame dH, Proof.AesGcm.AArch64.blockAt_frame Pr.frame dY, Pr.out]
    at out₆
  refine WP.run ⟨_, by grun [], rfl⟩ fun t₇ ht₇ => ?_
  subst ht₇
  refine ⟨E₆.keep (fun r hr => by
      simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
    by simp only [rd_write]; rw [P.rd, Pr.rd], by simp only [wr_write]; rw [P.wr, Pr.wr], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [P.saved _ (by decide) (by decide), Pr.x27]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; exact x28₆
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x28₆]
    rw [lsr_ofNat _ _ (by omega)]
  · simp only [mem_write]
    refine (Pr.frame.sub fun r hr => ?_).trans (P.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub p.W (by decide) (by decide)⟩
  · simp only [mem_write]; exact out₆

/-! ## Absorbing a string -/

theorem elemsAt_add (m : Mem) (Q : Addr) (d k : Nat) :
    VG.Proof.AesGcmSiv.AArch64.elemsAt m Q (d + k) = VG.Proof.AesGcmSiv.AArch64.elemsAt m Q d ++ VG.Proof.AesGcmSiv.AArch64.elemsAt m (Q + BitVec.ofNat 64 (16 * d)) k := by
  simp only [VG.Proof.AesGcmSiv.AArch64.elemsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, add_ofNat_assoc, Nat.mul_add]

theorem elemsAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr} {k : Nat}
    (hd : ∀ r ∈ rs, (⟨Q, 16 * k⟩ : Region).Disjoint r) (hk : 16 * k ≤ 2 ^ 64) : VG.Proof.AesGcmSiv.AArch64.elemsAt m' Q k = VG.Proof.AesGcmSiv.AArch64.elemsAt m Q k := by
  unfold VG.Proof.AesGcmSiv.AArch64.elemsAt
  rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt, Proof.AesGcm.AArch64.bytesAt_frame hf hd hk]

/-- What absorbing writes: what a chunk writes, and the block at `W + 224`. -/
abbrev absorbR (W : Addr) : List Region := ⟨W + BitVec.ofNat 64 224, 16⟩ :: VG.Proof.AesGcmSiv.AArch64.absR W

/-- What absorbing leaves, from `t`, having absorbed the elements `xs` and
written only `rs`. -/
structure Absorbed (p : VG.Proof.AesGcmSiv.AArch64.Prm) (rs : List Region) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame rs t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 80)) xs

/-- What absorbing a string leaves. -/
abbrev AbsPost (p : VG.Proof.AesGcmSiv.AArch64.Prm) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop := VG.Proof.AesGcmSiv.AArch64.Absorbed p (VG.Proof.AesGcmSiv.AArch64.absorbR p.W) xs t t'

theorem absorbR_H {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) : ∀ r ∈ VG.Proof.AesGcmSiv.AArch64.absorbR p.W, (⟨p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)

/-- A buffer apart from `W` misses what absorbing writes. -/
theorem absorbR_buf {p : VG.Proof.AesGcmSiv.AArch64.Prm} {Q : Addr} {k : Nat} (hd : (⟨Q, k⟩ : Region).Disjoint ⟨p.W, 3808⟩) :
    ∀ r ∈ VG.Proof.AesGcmSiv.AArch64.absorbR p.W, (⟨Q, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact hd.sub_right (Lay.wSub (by decide))

theorem absR_sub (W : Addr) : ∀ r ∈ VG.Proof.AesGcmSiv.AArch64.absR W, ∃ r' ∈ VG.Proof.AesGcmSiv.AArch64.absorbR W, Region.Sub r r' :=
  fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩

theorem Absorbed.trans {p : VG.Proof.AesGcmSiv.AArch64.Prm} {rs : List Region} {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (hH : ∀ r ∈ rs, (⟨p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r)
    (h₁ : VG.Proof.AesGcmSiv.AArch64.Absorbed p rs xs t t₁) (h₂ : VG.Proof.AesGcmSiv.AArch64.Absorbed p rs ys t₁ t₂) : VG.Proof.AesGcmSiv.AArch64.Absorbed p rs (xs ++ ys) t t₂ := by
  refine ⟨h₂.env, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.frame.trans h₂.frame, ?_⟩
  rw [h₂.out, h₁.out, Proof.AesGcm.AArch64.blockAt_frame h₁.frame hH, Proof.Gcm.ghashFrom_append]

theorem Absorbed.sub {p : VG.Proof.AesGcmSiv.AArch64.Prm} {rs rs' : List Region} {xs : List Spec.GcmSiv.Elem} {t t' : State}
    (h : VG.Proof.AesGcmSiv.AArch64.Absorbed p rs xs t t') (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : VG.Proof.AesGcmSiv.AArch64.Absorbed p rs' xs t t' :=
  ⟨h.env, h.rd, h.wr, h.frame.sub hs, h.out⟩

theorem AbsPost.trans {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h₁ : VG.Proof.AesGcmSiv.AArch64.AbsPost p xs t t₁) (h₂ : VG.Proof.AesGcmSiv.AArch64.AbsPost p ys t₁ t₂) : VG.Proof.AesGcmSiv.AArch64.AbsPost p (xs ++ ys) t t₂ :=
  Absorbed.trans (VG.Proof.AesGcmSiv.AArch64.absorbR_H L) h₁ h₂

theorem Absorbed.of_chunk {p : VG.Proof.AesGcmSiv.AArch64.Prm} {Q : Addr} {m k : Nat} {t t' : State}
    (h : VG.Proof.AesGcmSiv.AArch64.ChunkPost p Q m k t t') : VG.Proof.AesGcmSiv.AArch64.Absorbed p (VG.Proof.AesGcmSiv.AArch64.absR p.W) (VG.Proof.AesGcmSiv.AArch64.elemsAt t.mem Q k) t t' :=
  ⟨h.env, h.rd, h.wr, h.frame, h.out⟩

theorem Absorbed.of_eq {p : VG.Proof.AesGcmSiv.AArch64.Prm} {rs : List Region} {xs : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h : VG.Proof.AesGcmSiv.AArch64.Absorbed p rs xs t₁ t₂) (hm : t₁.mem = t.mem) (hrd : t₁.rd = t.rd) (hwr : t₁.wr = t.wr) :
    VG.Proof.AesGcmSiv.AArch64.Absorbed p rs xs t t₂ :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, hm ▸ h.frame, by rw [h.out, hm]⟩

theorem absR_H {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) : ∀ r ∈ VG.Proof.AesGcmSiv.AArch64.absR p.W, (⟨p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r :=
  fun r hr => VG.Proof.AesGcmSiv.AArch64.absorbR_H L r (List.mem_cons_of_mem _ hr)

/-- The chunks of the `m` bytes at `Q`, from `σ`, after `d` blocks. -/
structure CInv (p : VG.Proof.AesGcmSiv.AArch64.Prm) (σ : State) (Q : Addr) (m d : Nat) (t : State) : Prop where
  abs : VG.Proof.AesGcmSiv.AArch64.Absorbed p (VG.Proof.AesGcmSiv.AArch64.absR p.W) (VG.Proof.AesGcmSiv.AArch64.elemsAt σ.mem Q d) σ t
  x27 : t.gpr .x27 = Q + BitVec.ofNat 64 (16 * d)
  x28 : t.gpr .x28 = BitVec.ofNat 64 (m - 16 * d)

theorem CInv.src {p : VG.Proof.AesGcmSiv.AArch64.Prm} {σ t : State} {Q : Addr} {m d : Nat} (I : VG.Proof.AesGcmSiv.AArch64.CInv p σ Q m d t)
    (hQ : VG.Proof.AesGcmSiv.AArch64.Src p σ Q (16 * (m / 16))) (hd : d < m / 16) :
    VG.Proof.AesGcmSiv.AArch64.Src p t (Q + BitVec.ofNat 64 (16 * d)) (16 * ((m - 16 * d) / 16)) :=
  (hQ.slice (by omega)).of_eq I.abs.rd I.abs.wr

theorem CInv.zero {p : VG.Proof.AesGcmSiv.AArch64.Prm} {σ : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p σ) {Q : Addr} {m : Nat} (h27 : σ.gpr .x27 = Q)
    (h28 : σ.gpr .x28 = BitVec.ofNat 64 m) : VG.Proof.AesGcmSiv.AArch64.CInv p σ Q m 0 σ :=
  ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [VG.Proof.AesGcmSiv.AArch64.elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
    by rw [h27, Nat.mul_zero, BitVec.add_zero], by rw [h28, Nat.mul_zero, Nat.sub_zero]⟩

/-- A chunk, in the chunks. -/
theorem CInv.step {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {σ t t' : State} {Q : Addr} {m d : Nat} (_hm : m < 2 ^ 64)
    (hQ : VG.Proof.AesGcmSiv.AArch64.Src p σ Q (16 * (m / 16))) (hd : d < m / 16) (I : VG.Proof.AesGcmSiv.AArch64.CInv p σ Q m d t)
    (C : VG.Proof.AesGcmSiv.AArch64.ChunkPost p (Q + BitVec.ofNat 64 (16 * d)) (m - 16 * d) (min ((m - 16 * d) / 16) 64) t t') :
    VG.Proof.AesGcmSiv.AArch64.CInv p σ Q m (d + min (m / 16 - d) 64) t' ∧
      t'.gpr .x9 = BitVec.ofNat 64 (m / 16 - (d + min (m / 16 - d) 64)) := by
  have hk : min ((m - 16 * d) / 16) 64 = min (m / 16 - d) 64 := by congr 1; omega
  rw [hk] at C
  have hs := hQ.slice (a := 16 * d) (k := 16 * min (m / 16 - d) 64) (by omega)
  have C' := Absorbed.of_chunk C
  rw [VG.Proof.AesGcmSiv.AArch64.elemsAt_frame I.abs.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.y
      · exact hs.rev) (by omega)] at C'
  refine ⟨⟨by rw [VG.Proof.AesGcmSiv.AArch64.elemsAt_add]; exact Absorbed.trans (VG.Proof.AesGcmSiv.AArch64.absR_H L) I.abs C', by rw [C.x27, add_ofNat_assoc, Nat.mul_add],
    by rw [C.x28]; congr 1; omega⟩, by rw [C.x9]; congr 1; omega⟩

/-- The whole blocks: chunks until fewer than 16 bytes are left. -/
theorem chunks_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ : VG.Proof.AesGcmSiv.AArch64.Src p t Q (16 * (m / 16))) (h27 : t.gpr .x27 = Q)
    (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa (.loop (chunk v.callees) (.nonzero .x .x9)) t fun t' =>
      VG.Proof.AesGcmSiv.AArch64.Absorbed p (VG.Proof.AesGcmSiv.AArch64.absR p.W) (VG.Proof.AesGcmSiv.AArch64.elemsAt t.mem Q (m / 16)) t t' ∧
      t'.gpr .x27 = Q + BitVec.ofNat 64 (16 * (m / 16)) ∧ t'.gpr .x28 = BitVec.ofNat 64 (m % 16) := by
  refine WP.loop (M := isa) (body := chunk v.callees) (c := .nonzero .x .x9)
    (fun (k : Nat) (t' : State) => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ VG.Proof.AesGcmSiv.AArch64.CInv p t Q m d t') ?_
    (m / 16 - 0) t ⟨0, rfl, by omega, CInv.zero E h27 h28⟩
  rintro k t' ⟨d, rfl, hd, I⟩
  refine WP.mono (VG.Proof.AesGcmSiv.AArch64.chunk_ok v L I.abs.env (by omega) (by omega) (I.src hQ hd) I.x27 I.x28) fun t'' C => ?_
  obtain ⟨I', x9⟩ := I.step L hm hQ hd C
  have ev := eval_nonzero x9 (by omega)
  by_cases he : d + min (m / 16 - d) 64 = m / 16
  · left
    refine ⟨ev.trans (by simp; omega), he ▸ I'.abs, by rw [I'.x27, he], by rw [I'.x28, he]; congr 1; omega⟩
  · right
    exact ⟨ev.trans (by simp; omega), m / 16 - (d + min (m / 16 - d) 64), by omega, d + min (m / 16 - d) 64, rfl,
      by omega, I'⟩

end VG.Proof.AesGcmSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.AArch64.Polyval`. -/
section

/-!
# AES-GCM-SIV on AArch64: POLYVAL and the tag input (`polyval`)

Untrusted: everything here is checked by Lean. `absorb` absorbs a string
padded with zeros (`absorb_ok`): its whole blocks by chunks, its last bytes
copied over a zero block at `W + 224` and absorbed as one more chunk
(`absTail_ok`); `lensBlock` puts the lengths block there for one more
(`lens_ok`); `tagIn` turns POLYVAL's result into the tag input
(`tagIn_ok`). `polyval_ok`: the tag input of RFC 8452 §4, with POLYVAL as
GHASH with the key `H · x` (`Proof.GcmSiv.Words.tagInputG`), at `W + 96`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.GcmSiv.Words (hkeyOf tagInputG)
open VG.Proof.AesGcm.AArch64 (GcmImpl ofNat_add_ofNat in_off toNat_ofNat_of_lt covers_off covers_left
  ofNat_sub lsr_ofNat eval_zero add_ofNat_assoc Others LoopPre copyLoop_ok loopRegs length_bytesAt)

/-! ## The last bytes -/

/-- The last bytes copied over a zeroed block. -/
theorem pad_bytes (m : Mem) (c : Addr) (xs : List Byte) (hx : xs.length < 16) :
    bytesAt (writeBytes (Proof.Cmac.zero2 m c) c xs) c 16 = xs ++ Spec.GcmSiv.zeros (16 - xs.length) := by
  have hz := Proof.Cmac.zero2_bytes m c
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.AArch64.bytesAt_add] at hz
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.AArch64.bytesAt_add,
    Proof.AesGcm.AArch64.bytesAt_writeBytes_self _ _ _ (by omega),
    Proof.AesGcm.AArch64.bytesAt_frame (Proof.AesGcm.AArch64.writeBytes_frame' _ rfl) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base c (Nat.le_refl _) (by omega)) (by omega)]
  refine congrArg (xs ++ ·) ?_
  have := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at this
  rw [this, Nat.add_sub_cancel_left]
  simp [Spec.Cmac.zeros, Spec.GcmSiv.zeros, List.drop_replicate]

theorem zero2_eq (m : Mem) (W : Addr) :
    (m.writeW (W + BitVec.ofNat 64 224) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 232) (0 : BitVec 64) =
      Proof.Cmac.zero2 m (W + BitVec.ofNat 64 224) := by
  rw [Proof.Cmac.zero2, add_ofNat_assoc]

/-- The block at `W + 224` as a chunk's source. -/
theorem srcB {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {s : State} (P : VG.Proof.AesGcmSiv.AArch64.Perm p s) : VG.Proof.AesGcmSiv.AArch64.Src p s (p.W + BitVec.ofNat 64 224) 16 where
  rd := P.wCR (by decide)
  lt := by decide
  wrap := by rw [L.toNat_W (by decide)]; have := L.ww; omega
  y := L.w_w (.inr (by decide)) (by decide) (by decide)
  rev := L.w_w (.inl (by decide)) (by decide) (by decide)

/-- One chunk of the 16 bytes at `W + 224`: their field element absorbed. -/
theorem chunkB_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t)
    (h27 : t.gpr .x27 = p.W + BitVec.ofNat 64 224) (h28 : t.gpr .x28 = BitVec.ofNat 64 16) :
    WP isa (chunk v.callees) t (VG.Proof.AesGcmSiv.AArch64.Absorbed p (VG.Proof.AesGcmSiv.AArch64.absR p.W)
      [Spec.GcmSiv.ofBytes (bytesAt t.mem (p.W + BitVec.ofNat 64 224) 16)] t) :=
  WP.mono (VG.Proof.AesGcmSiv.AArch64.chunk_ok v L E (m := 16) (by decide) (by decide) (VG.Proof.AesGcmSiv.AArch64.srcB L E.perm) h27 h28) fun t' C => by
    have A := Absorbed.of_chunk C
    simpa [VG.Proof.AesGcmSiv.AArch64.elemsAt] using A

/-- What `absTailPre` leaves: the last bytes, padded, at `W + 224`, as the
bytes to absorb. -/
structure TailPre (p : VG.Proof.AesGcmSiv.AArch64.Prm) (P : Addr) (r : Nat) (t t₃ : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t₃
  rd : t₃.rd = t.rd
  wr : t₃.wr = t.wr
  x27 : t₃.gpr .x27 = p.W + BitVec.ofNat 64 224
  x28 : t₃.gpr .x28 = BitVec.ofNat 64 16
  frame : Frame [⟨p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₃.mem
  bytes : bytesAt t₃.mem (p.W + BitVec.ofNat 64 224) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r)

/-- `absTailPre`: the last `r` (1 to 15) bytes at `P`, padded with zeros. -/
theorem absTailPre_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {P : Addr} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨P, r⟩] (t.rd ++ t.wr))
    (hd : (⟨P, r⟩ : Region).Disjoint ⟨p.W, 3808⟩) (h27 : t.gpr .x27 = P) (h28 : t.gpr .x28 = BitVec.ofNat 64 r) :
    WP isa absTailPre t (VG.Proof.AesGcmSiv.AArch64.TailPre p P r t) := by
  have hw := L.ww
  have w₀ := E.perm.wW (show 224 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wW (show 232 + 8 ≤ 3808 by decide)
  -- The block zeroed, and the copy's arguments.
  obtain ⟨t₁, run₁, hm₁, x11₁, x12₁, x13₁, ho₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State,
      runBlock isa (zero16 bO ++ [Impl.AesGcm.AArch64.ptr .x11 .x19 bO, Impl.AesGcm.AArch64.mov .x12 .x27,
        Impl.AesGcm.AArch64.mov .x13 .x28]) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero2 t.mem (p.W + BitVec.ofNat 64 224) ∧ t₁.gpr .x11 = p.W + BitVec.ofNat 64 224 ∧
      t₁.gpr .x12 = P ∧ t₁.gpr .x13 = BitVec.ofNat 64 r ∧ Others [.x9, .x11, .x12, .x13] t t₁ ∧
      t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [zero16]; grun [E.x19, w₀, w₈], ?_, ?_, ?_, ?_, by others_tac, (by rfl), (by rfl), (by rfl)⟩
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, VG.Proof.AesGcmSiv.AArch64.movz0, ← VG.Proof.AesGcmSiv.AArch64.zero2_eq]
    · simp [gpr_write, E.x19]
    · simp [gpr_write, h27]
    · simp [gpr_write, h28]
  unfold absTailPre
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesGcmSiv.AArch64.Env p t₁ := E.keep (fun q hq => ho₁ q (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have dB : (⟨P, r⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 224, r⟩ :=
    (hd.sub_right (Lay.wSub (show 224 + 16 ≤ 3808 by decide))).sub_right (Region.sub_prefix (by omega))
  have lp : LoopPre t₁ P (p.W + BitVec.ofNat 64 224) r :=
    ⟨by omega, by rw [rd₁, wr₁]; exact hc, Proof.AesGcm.AArch64.covers_prefix (E₁.perm.wC (show 224 + 16 ≤ 3808 by decide))
      (by omega), dB⟩
  refine WP.seq (WP.mono (copyLoop_ok t₁ x12₁ x11₁ x13₁ (by omega) lp) fun t₂ ⟨hm₂, _, _, ho₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : VG.Proof.AesGcmSiv.AArch64.Env p t₂ := E₁.keep (fun q hq => ho₂ q (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  -- The data is outside the zeroed block.
  have hd₁ : bytesAt t₁.mem P r = bytesAt t.mem P r := by
    rw [hm₁]
    exact Proof.AesGcm.AArch64.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _)
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by decide)))
      (by omega)
  have hb₂ : bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r) := by
    have hl := length_bytesAt t.mem P r
    rw [hm₂, hd₁, hm₁, VG.Proof.AesGcmSiv.AArch64.pad_bytes _ _ _ (by omega), hl]
  have f₂ : Frame [⟨p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₂.mem := by
    rw [hm₂, hm₁]
    exact (Proof.Cmac.frame_store2 _ _ _).trans
      ((Proof.AesGcm.AArch64.writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  refine WP.run ⟨_, by grun [], rfl⟩ fun t₃ ht₃ => ?_
  subst ht₃
  exact ⟨E₂.keep (fun q hq => by
      simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
    by simp only [rd_write]; rw [rd₂, rd₁], by simp only [wr_write]; rw [wr₂, wr₁],
    by simp [gpr_write, E₂.x19], by simp [gpr_write, VG.Proof.AesGcmSiv.AArch64.movz_lit (show 16 < 2 ^ 16 by decide)],
    by simp only [mem_write]; exact f₂, by simp only [mem_write]; exact hb₂⟩

/-- `absTail`: the last `r` (1 to 15) bytes at `P`, padded with zeros, absorbed. -/
theorem absTail_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {P : Addr} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨P, r⟩] (t.rd ++ t.wr))
    (hd : (⟨P, r⟩ : Region).Disjoint ⟨p.W, 3808⟩) (h27 : t.gpr .x27 = P) (h28 : t.gpr .x28 = BitVec.ofNat 64 r) :
    WP isa (absTail v.callees) t
      (VG.Proof.AesGcmSiv.AArch64.AbsPost p [Spec.GcmSiv.ofBytes (bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.absTailPre_ok L E hr1 hr hc hd h27 h28) fun t₃ T => ?_)
  refine WP.mono (VG.Proof.AesGcmSiv.AArch64.chunkB_ok v L T.env T.x27 T.x28) fun t₄ C => ?_
  rw [T.bytes] at C
  have dHY : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 224, 16⟩ : Region)], ∀ d, d + 16 ≤ 224 →
      (⟨p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun q hq d hd => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega) (by decide)
  refine ⟨C.env, by rw [C.rd, T.rd], by rw [C.wr, T.wr],
    (T.frame.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  rw [C.out, Proof.AesGcm.AArch64.blockAt_frame T.frame (fun q hq => dHY q hq 64 (by decide)),
    Proof.AesGcm.AArch64.blockAt_frame T.frame (fun q hq => dHY q hq 80 (by decide))]

/-! ## Absorbing a string -/

/-- The field elements of `n` bytes at `Q`, padded. -/
theorem elems_pad16_bytesAt (m : Mem) (Q : Addr) (n : Nat) :
    Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m Q n)) = VG.Proof.AesGcmSiv.AArch64.elemsAt m Q (n / 16) ++
      if n % 16 = 0 then [] else
        [Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++
          Spec.GcmSiv.zeros (16 - n % 16))] := by
  have hs := Proof.AesGcm.AArch64.bytesAt_add m Q (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega] at hs
  have hl := length_bytesAt m Q (16 * (n / 16))
  rw [GcmSiv.elems_pad16, length_bytesAt, hs, List.take_left' hl, List.drop_left' hl, GcmSiv.elems_bytesAt]

/-- The whole blocks of `absorb`, once `x9` holds their number. -/
theorem absMid_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (hQ : VG.Proof.AesGcmSiv.AArch64.Src p t Q m) (h27 : t.gpr .x27 = Q) (h28 : t.gpr .x28 = BitVec.ofNat 64 m)
    (h9 : t.gpr .x9 = BitVec.ofNat 64 (m / 16)) :
    WP isa (.ite (.zero .x .x9) (.block []) (.loop (chunk v.callees) (.nonzero .x .x9))) t fun t₂ =>
      VG.Proof.AesGcmSiv.AArch64.Absorbed p (VG.Proof.AesGcmSiv.AArch64.absR p.W) (VG.Proof.AesGcmSiv.AArch64.elemsAt t.mem Q (m / 16)) t t₂ ∧
        t₂.gpr .x27 = Q + BitVec.ofNat 64 (16 * (m / 16)) ∧ t₂.gpr .x28 = BitVec.ofNat 64 (m % 16) := by
  refine WP.ite (decide (m / 16 = 0)) (eval_zero h9 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [h0, VG.Proof.AesGcmSiv.AArch64.elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [h27, h0, Nat.mul_zero, BitVec.add_zero], by rw [h28]; congr 1; omega⟩
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact VG.Proof.AesGcmSiv.AArch64.chunks_ok v L E hm (by omega) (hQ.take (by omega)) h27 h28

/-- `absorb`'s first block. -/
theorem absHead_ok {t : State} {m : Nat} (hm : m < 2 ^ 64) (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa (.block [.lsr .x .x9 .x28 4]) t fun t₁ => t₁.gpr .x9 = BitVec.ofNat 64 (m / 16) ∧
      Others [.x9] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
  WP.run ⟨_, by grun [], rfl⟩ fun t₁ ht₁ => by
    subst ht₁
    exact ⟨by simp [gpr_write, h28, lsr_ofNat _ _ hm], by others_tac, rfl, rfl, rfl, rfl⟩

theorem absorb_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {Q : Addr} {m : Nat}
    (hc : Covers [⟨Q, m⟩] (t.rd ++ t.wr)) (hm : m < 2 ^ 64) (hw : Q.toNat + m ≤ 2 ^ 64)
    (hd : (⟨Q, m⟩ : Region).Disjoint ⟨p.W, 3808⟩) (h27 : t.gpr .x27 = Q) (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa (absorb v.callees) t (VG.Proof.AesGcmSiv.AArch64.AbsPost p (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem Q m))) t) := by
  have hQ : VG.Proof.AesGcmSiv.AArch64.Src p t Q m := Src.ofW L hc hm hw hd
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.absHead_ok hm h28) fun t₁ ⟨x9₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ => ?_)
  have E₁ : VG.Proof.AesGcmSiv.AArch64.Env p t₁ := E.keep (fun q hq => ho₁ q (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.absMid_ok v L E₁ hm (hQ.of_eq rd₁ wr₁) (by rw [ho₁ _ (by decide), h27])
    (by rw [ho₁ _ (by decide), h28]) x9₁) fun t₂ ⟨P₂, x27₂, x28₂⟩ => ?_)
  rw [m₁] at P₂
  have P₂' := P₂.of_eq m₁ rd₁ wr₁
  rw [VG.Proof.AesGcmSiv.AArch64.elems_pad16_bytesAt]
  refine WP.ite (decide (m % 16 = 0)) (eval_zero x28₂ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil (P₂'.sub (VG.Proof.AesGcmSiv.AArch64.absR_sub p.W))
  · have h0 : m % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    have hs := hQ.slice (a := 16 * (m / 16)) (k := m % 16) (by omega)
    have dT : (⟨Q + BitVec.ofNat 64 (16 * (m / 16)), m % 16⟩ : Region).Disjoint ⟨p.W, 3808⟩ :=
      hd.sub_left (Offset.sub_base Q (by omega))
    refine WP.mono (VG.Proof.AesGcmSiv.AArch64.absTail_ok v L P₂'.env (by omega) (by omega) (by rw [P₂'.rd, P₂'.wr]; exact hs.rd) dT x27₂ x28₂)
      fun t₃ T => ?_
    have e := Proof.AesGcm.AArch64.bytesAt_frame P₂'.frame (fun r hr => dT.sub_right ?_) (by omega)
    · rw [e] at T
      exact AbsPost.trans L (P₂'.sub (VG.Proof.AesGcmSiv.AArch64.absR_sub p.W)) T
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

/-! ## The lengths, and the tag input -/

theorem le64_word (x : Nat) : Spec.GcmSiv.le64 x = Proof.Cmac.le8 (BitVec.ofNat 64 x) := GcmSiv.le64_le8 x

/-- `lensBlock` and its chunk: the lengths block absorbed. -/
theorem lens_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) :
    WP isa (lens v.callees) t (VG.Proof.AesGcmSiv.AArch64.AbsPost p
      [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))] t) := by
  have w₀ := E.perm.wW (show 224 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wW (show 232 + 8 ≤ 3808 by decide)
  obtain ⟨t₁, run₁, hm₁, x27₁, x28₁, ho₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa VG.Impl.AesGcmSiv.AArch64.lensBlock t = some t₁ ∧
      t₁.mem = (t.mem.writeW (p.W + BitVec.ofNat 64 224) (BitVec.ofNat 64 (8 * p.al))).writeW
        (p.W + BitVec.ofNat 64 224 + BitVec.ofNat 64 8) (BitVec.ofNat 64 (8 * p.n)) ∧
      t₁.gpr .x27 = p.W + BitVec.ofNat 64 224 ∧ t₁.gpr .x28 = BitVec.ofNat 64 16 ∧
      Others [.x9, .x27, .x28] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [VG.Impl.AesGcmSiv.AArch64.lensBlock]; grun [E.x19, E.x24, E.x26, w₀, w₈], ?_, ?_, ?_, by others_tac, (by rfl), (by rfl),
      (by rfl)⟩
    · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, Mem.writeW, BitVec.setWidth_eq,
        add_ofNat_assoc, VG.Proof.AesGcmSiv.AArch64.ofNat_lsl, E.x24, E.x26]
      rw [Nat.mul_comm p.al, Nat.mul_comm p.n]; rfl
    · simp [gpr_write, E.x19]
    · simp [gpr_write, VG.Proof.AesGcmSiv.AArch64.movz_lit (show 16 < 2 ^ 16 by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesGcmSiv.AArch64.Env p t₁ := E.keep (fun q hq => ho₁ q (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  refine WP.mono (VG.Proof.AesGcmSiv.AArch64.chunkB_ok v L E₁ x27₁ x28₁) fun t₂ C => ?_
  have hb : bytesAt t₁.mem (p.W + BitVec.ofNat 64 224) 16 =
      Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n) := by
    rw [hm₁, Proof.Cmac.bytesAt_store2, VG.Proof.AesGcmSiv.AArch64.le64_word, VG.Proof.AesGcmSiv.AArch64.le64_word]
  rw [hb] at C
  have dHY : ∀ d, d + 16 ≤ 224 → ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 224, 16⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega) (by decide)
  refine ⟨C.env, by rw [C.rd, rd₁], by rw [C.wr, wr₁],
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  rw [C.out, Proof.AesGcm.AArch64.blockAt_frame f₁ (dHY 64 (by decide)),
    Proof.AesGcm.AArch64.blockAt_frame f₁ (dHY 80 (by decide))]

/-- The memory `tagIn` leaves. -/
def tagInMem (m : Mem) (W N : Addr) : Mem :=
  let lo := rev64 (m.readW (W + BitVec.ofNat 64 88) 64) ^^^ m.readW N 64
  let hi := ((rev64 (m.readW (W + BitVec.ofNat 64 80) 64) ^^^ (m.readW (N + BitVec.ofNat 64 8) 32).setWidth 64)
    <<< 1) >>> 1
  (m.writeW (W + BitVec.ofNat 64 96) lo).writeW (W + BitVec.ofNat 64 104) hi

theorem tagInMem_bytes (m : Mem) (W N : Addr) :
    bytesAt (VG.Proof.AesGcmSiv.AArch64.tagInMem m W N) (W + BitVec.ofNat 64 96) 16 =
      GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.blockAt m (W + BitVec.ofNat 64 80))) (bytesAt m N 12) := by
  rw [VG.Proof.AesGcmSiv.AArch64.tagInMem, show W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc],
    Proof.Cmac.bytesAt_store2, ← Proof.Gcm.AArch64.blockAt_rev, BitVec.add_zero, add_ofNat_assoc,
    GcmSiv.toBytes_append, show (12 : Nat) = 8 + 4 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le4_readW, GcmSiv.tagOf_words, GcmSiv.Words.shl_shr_one]

theorem tagInMem_frame (m : Mem) (W N : Addr) : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m (VG.Proof.AesGcmSiv.AArch64.tagInMem m W N) := by
  rw [VG.Proof.AesGcmSiv.AArch64.tagInMem, show W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc]]
  exact Proof.Cmac.frame_store2 _ _ _

theorem tagIn_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) :
    ∃ t' : State, runBlock isa tagIn t = some t' ∧ t'.mem = VG.Proof.AesGcmSiv.AArch64.tagInMem t.mem p.W p.N ∧
      Others [.x9, .x10, .x11] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₀ := E.perm.wR (show 80 + 8 ≤ 3808 by decide)
  have r₈ := E.perm.wR (show 88 + 8 ≤ 3808 by decide)
  have w₀ := E.perm.wW (show 96 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wW (show 104 + 8 ≤ 3808 by decide)
  have n₀ : InRegions (t.rd ++ t.wr) p.N 8 := by simpa using E.perm.nR (d := 0) (k := 8) (by decide)
  have n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  refine ⟨_, by simp only [tagIn]; grun [E.x19, E.x20, BitVec.add_zero, r₀, r₈, w₀, w₈, n₀, n₈], ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, VG.Proof.AesGcmSiv.AArch64.tagInMem, Mem.writeW, BitVec.setWidth_eq,
    VG.Proof.AesGcmSiv.AArch64.read8_readW, VG.Proof.AesGcmSiv.AArch64.read4_readW]

/-! ## `polyval` -/

/-- What `polyval` writes: what absorbing writes, and the tag input at `W + 96`. -/
abbrev polyR (W : Addr) : List Region := ⟨W + BitVec.ofNat 64 96, 16⟩ :: VG.Proof.AesGcmSiv.AArch64.absorbR W

/-- What `polyval` leaves, from `t`. -/
structure PolyPost (p : VG.Proof.AesGcmSiv.AArch64.Prm) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (VG.Proof.AesGcmSiv.AArch64.polyR p.W) t.mem t'.mem
  out : bytesAt t'.mem (p.W + BitVec.ofNat 64 96) 16 =
    tagInputG (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16) (bytesAt t.mem p.N 12) (bytesAt t.mem p.D p.n)
      (bytesAt t.mem p.A p.al)

theorem polyval_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t)
    (hG : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 80) = 0) :
    WP isa (polyval v.callees) t (VG.Proof.AesGcmSiv.AArch64.PolyPost p t) := by
  -- The additional data.
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.absorb_ok v L ((E.write (by decide) _).write (by decide) _) (by simp only [rd_write, wr_write]; exact E.perm.aad) L.al_lt L.aw L.a_w
    (by simp [gpr_write, E.x23]) (by simp [gpr_write, E.x24])) fun t₂ P₂ => ?_)
  simp only [mem_write] at P₂
  have P₂' := P₂.of_eq (t := t) rfl rfl rfl
  -- The data.
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.absorb_ok v L ((P₂.env.write (by decide) _).write (by decide) _) (by simp only [rd_write, wr_write]; exact covers_left P₂.env.perm.d)
    L.n_lt L.dw L.d_w (by simp [gpr_write, P₂.env.x25]) (by simp [gpr_write, P₂.env.x26])) fun t₄ P₄ => ?_)
  simp only [mem_write] at P₄
  rw [Proof.AesGcm.AArch64.bytesAt_frame P₂.frame (VG.Proof.AesGcmSiv.AArch64.absorbR_buf L.d_w) (by have := L.n_lt; omega)] at P₄
  have P₂₄ := AbsPost.trans L P₂' (P₄.of_eq rfl rfl rfl)
  -- The lengths.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.lens_ok v L P₂₄.env) fun t₅ P₅ => ?_)
  have P₂₅ := AbsPost.trans L P₂₄ P₅
  -- The tag input.
  obtain ⟨t₆, run₆, hm₆, ho₆, sp₆, rd₆, wr₆⟩ := VG.Proof.AesGcmSiv.AArch64.tagIn_ok P₂₅.env
  refine WP.of_runBlock ⟨t₆, run₆, P₂₅.env.keep (fun q hq => ho₆ q (by
      simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆,
    by rw [rd₆, P₂₅.rd], by rw [wr₆, P₂₅.wr], ?_, ?_⟩
  · refine (P₂₅.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans ?_
    rw [hm₆]
    exact (VG.Proof.AesGcmSiv.AArch64.tagInMem_frame _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega
    have nN : bytesAt t₅.mem p.N 12 = bytesAt t.mem p.N 12 :=
      Proof.AesGcm.AArch64.bytesAt_frame P₂₅.frame (VG.Proof.AesGcmSiv.AArch64.absorbR_buf L.n_w) (by decide)
    rw [hm₆, VG.Proof.AesGcmSiv.AArch64.tagInMem_bytes, nN, P₂₅.out, hG, hY, tagInputG, length_bytesAt, length_bytesAt,
      GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))
        (by simp [Spec.GcmSiv.le64])]
    simp only [mem_write]

end VG.Proof.AesGcmSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.AArch64.Tag`. -/
section

/-!
# AES-GCM-SIV on AArch64: the tag (`tag`)

Untrusted: everything here is checked by Lean. `tag o` encrypts the block at
`W + 96` with the encryption key's schedule at `W + 240` into the block at
`W + o`, by `vg_aes_ctr32` of one zero block from a copy of it at `W + 112`
(`tag_ok`): the tag, the tag `open` computes, and counter mode's last
keystream block.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (GcmImpl CtrCall CtrPost ctr_call covers_cons covers_nil covers_append
  add_ofNat_assoc Others)

theorem blockAt_zero2 (m : Mem) (p : Addr) : Spec.Gcm.blockAt (Proof.Cmac.zero2 m p) p = 0 := by
  rw [Spec.Gcm.blockAt, Proof.Cmac.zero2_bytes]
  decide

/-- The memory after the copy of the counter block. -/
def copyMem (m : Mem) (W : Addr) : Mem :=
  (m.writeW (W + BitVec.ofNat 64 112) (m.readW (W + BitVec.ofNat 64 96) 64)).writeW
    (W + BitVec.ofNat 64 120) (m.readW (W + BitVec.ofNat 64 104) 64)

theorem copyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] m (VG.Proof.AesGcmSiv.AArch64.copyMem m W) := by
  rw [VG.Proof.AesGcmSiv.AArch64.copyMem, show W + BitVec.ofNat 64 120 = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc]]
  exact Proof.Cmac.frame_store2 _ _ _

theorem copyMem_bytes (m : Mem) (W : Addr) :
    bytesAt (VG.Proof.AesGcmSiv.AArch64.copyMem m W) (W + BitVec.ofNat 64 112) 16 = bytesAt m (W + BitVec.ofNat 64 96) 16 := by
  rw [VG.Proof.AesGcmSiv.AArch64.copyMem, show W + BitVec.ofNat 64 120 = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc],
    show W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc],
    Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

/-- What `tag o` writes. -/
abbrev tagR (W : Addr) (o : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩, ⟨W + BitVec.ofNat 64 1760, 2048⟩]

/-- What `tag o` leaves, from `t`. -/
structure TagPost (p : VG.Proof.AesGcmSiv.AArch64.Prm) (o : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  x27 : t'.gpr .x27 = t.gpr .x27
  x28 : t'.gpr .x28 = t.gpr .x28
  frame : Frame (VG.Proof.AesGcmSiv.AArch64.tagR p.W o) t.mem t'.mem
  out : bytesAt t'.mem (p.W + BitVec.ofNat 64 o) 16 =
    Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R (bytesAt t.mem (p.W + BitVec.ofNat 64 96) 16)

/-- The arguments of `tag o`'s call. -/
theorem tagArgs_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {o : Nat} (ho : o = 0 ∨ o = 224) :
    ∃ t₁ : State, runBlock isa (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++ [Impl.AesGcm.AArch64.ptr .x3 .x19 o]) t =
      some t₁ ∧ t₁.mem = Proof.Cmac.zero2 (VG.Proof.AesGcmSiv.AArch64.copyMem t.mem p.W) (p.W + BitVec.ofNat 64 o) ∧
      t₁.gpr .x0 = p.W + BitVec.ofNat 64 240 ∧ t₁.gpr .x1 = BitVec.ofNat 64 p.R ∧
      t₁.gpr .x2 = p.W + BitVec.ofNat 64 112 ∧ t₁.gpr .x3 = p.W + BitVec.ofNat 64 o ∧
      t₁.gpr .x4 = BitVec.ofNat 64 1 ∧ t₁.gpr .x5 = p.W + BitVec.ofNat 64 1760 ∧
      Others [.x9, .x0, .x1, .x2, .x3, .x4, .x5] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have r₀ := E.perm.wR (show 96 + 8 ≤ 3808 by decide)
  have r₈ := E.perm.wR (show 104 + 8 ≤ 3808 by decide)
  have w₀ := E.perm.wW (show 112 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wW (show 120 + 8 ≤ 3808 by decide)
  have z₀ := E.perm.wW (show o + 8 ≤ 3808 by omega)
  have z₈ := E.perm.wW (show o + 8 + 8 ≤ 3808 by omega)
  have o₁ : o % 8 = 0 := by omega
  have o₂ : o < 32768 := by omega
  have o₃ : (o + 8) % 8 = 0 := by omega
  have o₄ : o + 8 < 32768 := by omega
  have o₅ : o < 4096 := by omega
  refine ⟨_, by simp only [copy16, zero16, ctrArgs]; grun [E.x19, E.x22, r₀, r₈, w₀, w₈, z₀, z₈, o₁, o₂, o₃, o₄, o₅],
    ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · have sep : ∀ v : BitVec (8 * 8), (t.mem.write (p.W + BitVec.ofNat 64 112) 8 v).read (p.W + BitVec.ofNat 64 104) 8 =
        t.mem.read (p.W + BitVec.ofNat 64 104) 8 := fun _ =>
      Mem.read_write_sep (Offset.sep p.W (.inl (by decide)) (by decide) (by decide)) (by decide)
    rw [Proof.Cmac.zero2, VG.Proof.AesGcmSiv.AArch64.copyMem, add_ofNat_assoc]
    simp only [mem_write, sep, Mem.writeW, BitVec.setWidth_eq, VG.Proof.AesGcmSiv.AArch64.read8_readW, VG.Proof.AesGcmSiv.AArch64.movz0]
  all_goals simp [gpr_write, E.x19, E.x22]

/-- The arguments of `tag o`'s call, as `vg_aes_ctr32` needs them. -/
theorem tagCall {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t₁ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p t₁) {o : Nat} (ho : o = 0 ∨ o = 224)
    (x0 : t₁.gpr .x0 = p.W + BitVec.ofNat 64 240) (x1 : t₁.gpr .x1 = BitVec.ofNat 64 p.R)
    (x2 : t₁.gpr .x2 = p.W + BitVec.ofNat 64 112) (x3 : t₁.gpr .x3 = p.W + BitVec.ofNat 64 o)
    (x4 : t₁.gpr .x4 = BitVec.ofNat 64 1) (x5 : t₁.gpr .x5 = p.W + BitVec.ofNat 64 1760) :
    CtrCall t₁ (p.W + BitVec.ofNat 64 240) (p.W + BitVec.ofNat 64 112) (p.W + BitVec.ofNat 64 o)
      (p.W + BitVec.ofNat 64 1760) p.R 1 :=
  have hw := L.ww
  { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5
    rounds := L.rounds3
    wrap := by rw [L.toNat_W (by omega)]; omega
    n_lt := by decide
    kc := L.w_w (.inr (by decide)) (by decide) (by decide)
    kd := L.w_w (.inr (by omega)) (by decide) (by omega)
    ks := L.w_w (.inl (by decide)) (by decide) (by decide)
    cd := (L.w_w (by omega) (by omega) (by decide) :
      (⟨p.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 112, 16⟩).symm
    cs := L.w_w (.inl (by decide)) (by decide) (by decide)
    ds := L.w_w (.inl (by omega)) (by omega) (by decide)
    reads := covers_append (covers_cons (E₁.perm.wCR (by decide)) covers_nil)
      (covers_cons (E₁.perm.wCR (by decide)) (covers_cons (E₁.perm.wCR (by omega))
        (covers_cons (E₁.perm.wCR (by decide)) covers_nil)))
    writes := covers_cons (E₁.perm.wC (by decide)) (covers_cons (E₁.perm.wC (by omega))
        (covers_cons (E₁.perm.wC (by decide)) covers_nil)) }

theorem tag_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {o : Nat}
    (ho : o = 0 ∨ o = 224) :
    WP isa (tag v.callees o) t (VG.Proof.AesGcmSiv.AArch64.TagPost p o t) := by
  have hw := L.ww
  obtain ⟨t₁, run₁, hm₁, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.AArch64.tagArgs_ok E ho
  have E₁ : VG.Proof.AesGcmSiv.AArch64.Env p t₁ := E.keep (fun r hr => ho₁ r (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have dO : (⟨p.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 112, 16⟩ :=
    L.w_w (by omega) (by omega) (by decide)
  have cc := VG.Proof.AesGcmSiv.AArch64.tagCall L E₁ ho x0 x1 x2 x3 x4 x5
  have fZ := Proof.Cmac.frame_store2 (m := VG.Proof.AesGcmSiv.AArch64.copyMem t.mem p.W) (p.W + BitVec.ofNat 64 o) 0 0
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 112, 16⟩, ⟨p.W + BitVec.ofNat 64 o, 16⟩] t.mem t₁.mem := by
    rw [hm₁, Proof.Cmac.zero2]
    exact ((VG.Proof.AesGcmSiv.AArch64.copyMem_frame _ _).mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans
      (fZ.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp)
  have hb₁ : bytesAt t₁.mem (p.W + BitVec.ofNat 64 112) 16 = bytesAt t.mem (p.W + BitVec.ofNat 64 96) 16 := by
    rw [hm₁, Proof.Cmac.zero2, Proof.AesGcm.AArch64.bytesAt_frame fZ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dO.symm) (by decide), VG.Proof.AesGcmSiv.AArch64.copyMem_bytes]
  have hz₁ : Spec.Gcm.blockAt t₁.mem (p.W + BitVec.ofNat 64 o) = 0 := by rw [hm₁]; exact VG.Proof.AesGcmSiv.AArch64.blockAt_zero2 _ _
  have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (p.W + BitVec.ofNat 64 240) p.R =
      Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le)
      · exact (L.w_w (.inr (by omega)) (by decide) (by omega)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_
  have fc := P.frame
  rw [Nat.mul_one] at fc
  refine ⟨E₁.of_saved P.saved P.sp P.rd P.wr, by rw [P.rd, rd₁], by rw [P.wr, wr₁],
    by rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide)],
    by rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide)],
    (f₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp).trans (fc.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp), ?_⟩
  have hout := P.out
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
  rw [Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
    show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (p.W + BitVec.ofNat 64 240) (16 * (p.R + 1))) =
      Spec.GcmSiv.ctxCiph t₁.mem (p.W + BitVec.ofNat 64 240) p.R from rfl, ek₁, hb₁]

end VG.Proof.AesGcmSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.AArch64.Crypt`. -/
section

/-!
# AES-GCM-SIV on AArch64: counter mode (`crypt`)

Untrusted: everything here is checked by Lean. The counter block at
`W + 96` starts as the tag with the top bit of its last byte set
(`cryptHead_ok`); each block of the data is encrypted in place by
`vg_aes_ctr32` from a copy of it at `W + 112`, after which its first word is
incremented (`cryptBlock_ok`); the last bytes are XORed with the keystream
block, computed at `W + 224` (`cryptTail_ok`). `crypt_ok`: the data becomes
`ctr` of it (RFC 8452 §4).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.AesGcm.AArch64 (GcmImpl CtrCall CtrPost ctr_call covers_cons covers_nil covers_append covers_off
  covers_left add_ofNat_assoc ofNat_sub lsr_ofNat eval_zero eval_nonzero toNat_ofNat_of_lt Others LoopPre
  xorLoop_ok loopRegs xorBytes length_bytesAt)

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

theorem CtrSt.block {W : Addr} {icb : List Byte} {j : Nat} {m : Mem} (h : VG.Proof.AesGcmSiv.AArch64.CtrSt W icb j m) :
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
`W + 224`, `vg_aes_ctr32`'s working space and the data. -/
abbrev cryR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 96, 32⟩, ⟨W + BitVec.ofNat 64 224, 16⟩, ⟨W + BitVec.ofNat 64 1760, 2048⟩, ⟨D, n⟩]

/-- What a block of counter mode leaves, from `t`. -/
structure BlockPost (p : VG.Proof.AesGcmSiv.AArch64.Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (j : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  x27 : t'.gpr .x27 = p.D + BitVec.ofNat 64 (16 * (j + 1))
  x28 : t'.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * (j + 1))
  x9 : t'.gpr .x9 = BitVec.ofNat 64 ((p.n - 16 * (j + 1)) / 16)
  ctr : VG.Proof.AesGcmSiv.AArch64.CtrSt p.W icb (j + 1) t'.mem
  data : bytesAt t'.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * (j + 1))
  frame : Frame (VG.Proof.AesGcmSiv.AArch64.cryR p.W p.D p.n) t.mem t'.mem

/-- The arguments of a block's call. -/
theorem blkArgs_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {j : Nat}
    (h27 : t.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j)) :
    ∃ t₁ : State, runBlock isa (copy16 cbO ccO ++ ctrArgs ++ [Impl.AesGcm.AArch64.mov .x3 .x27]) t = some t₁ ∧
      t₁.mem = VG.Proof.AesGcmSiv.AArch64.copyMem t.mem p.W ∧
      t₁.gpr .x0 = p.W + BitVec.ofNat 64 240 ∧ t₁.gpr .x1 = BitVec.ofNat 64 p.R ∧
      t₁.gpr .x2 = p.W + BitVec.ofNat 64 112 ∧ t₁.gpr .x3 = p.D + BitVec.ofNat 64 (16 * j) ∧
      t₁.gpr .x4 = BitVec.ofNat 64 1 ∧ t₁.gpr .x5 = p.W + BitVec.ofNat 64 1760 ∧
      Others [.x9, .x0, .x1, .x2, .x3, .x4, .x5] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have r₀ := E.perm.wR (show 96 + 8 ≤ 3808 by decide)
  have r₈ := E.perm.wR (show 104 + 8 ≤ 3808 by decide)
  have w₀ := E.perm.wW (show 112 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wW (show 120 + 8 ≤ 3808 by decide)
  refine ⟨_, by simp only [copy16, ctrArgs]; grun [E.x19, E.x22, r₀, r₈, w₀, w₈], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · have sep : ∀ v : BitVec (8 * 8), (t.mem.write (p.W + BitVec.ofNat 64 112) 8 v).read (p.W + BitVec.ofNat 64 104) 8 =
        t.mem.read (p.W + BitVec.ofNat 64 104) 8 := fun _ =>
      Mem.read_write_sep (Offset.sep p.W (.inl (by decide)) (by decide) (by decide)) (by decide)
    rw [VG.Proof.AesGcmSiv.AArch64.copyMem]
    simp only [mem_write, sep, Mem.writeW, BitVec.setWidth_eq, VG.Proof.AesGcmSiv.AArch64.read8_readW]
  all_goals simp [gpr_write, E.x19, E.x22, h27]

theorem setWidth_rt32' (v : BitVec 32) : (BitVec.setWidth 32 (BitVec.setWidth 64 v) : BitVec 32) = v :=
  VG.Proof.AesGcmSiv.AArch64.setWidth_rt32 v

/-- The arguments of a block's call, as `vg_aes_ctr32` needs them. -/
theorem blkCall {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t₁ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p t₁) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (x0 : t₁.gpr .x0 = p.W + BitVec.ofNat 64 240) (x1 : t₁.gpr .x1 = BitVec.ofNat 64 p.R)
    (x2 : t₁.gpr .x2 = p.W + BitVec.ofNat 64 112) (x3 : t₁.gpr .x3 = p.D + BitVec.ofNat 64 (16 * j))
    (x4 : t₁.gpr .x4 = BitVec.ofNat 64 1) (x5 : t₁.gpr .x5 = p.W + BitVec.ofNat 64 1760) :
    CtrCall t₁ (p.W + BitVec.ofNat 64 240) (p.W + BitVec.ofNat 64 112) (p.D + BitVec.ofNat 64 (16 * j))
      (p.W + BitVec.ofNat 64 1760) p.R 1 :=
  have hn := L.n_lt
  have hdw := L.dw
  have dQ : (⟨p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨p.W, 3808⟩ :=
    L.d_w.sub_left (Offset.sub_base p.D (by omega))
  { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5
    rounds := L.rounds3
    wrap := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * j) (by omega)]
      have : p.D.toNat + 16 * j < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt this]; omega
    n_lt := by decide
    kc := L.w_w (.inr (by decide)) (by decide) (by decide)
    kd := (dQ.sub_right (Lay.wSub (show 240 + 240 ≤ 3808 by decide))).symm
    ks := L.w_w (.inl (by decide)) (by decide) (by decide)
    cd := (dQ.sub_right (Lay.wSub (show 112 + 16 ≤ 3808 by decide))).symm
    cs := L.w_w (.inl (by decide)) (by decide) (by decide)
    ds := dQ.sub_right (Lay.wSub (by decide))
    reads := covers_append (covers_cons (E₁.perm.wCR (by decide)) covers_nil)
      (covers_cons (E₁.perm.wCR (by decide)) (covers_cons (covers_left (covers_off E₁.perm.d (by omega) hn))
        (covers_cons (E₁.perm.wCR (by decide)) covers_nil)))
    writes := covers_cons (E₁.perm.wC (by decide)) (covers_cons (covers_off E₁.perm.d (by omega) hn)
        (covers_cons (E₁.perm.wC (by decide)) covers_nil)) }

theorem cryptBlock_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {j : Nat}
    (hj : 16 * (j + 1) ≤ p.n) (h27 : t.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j))
    (h28 : t.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j)) (C : VG.Proof.AesGcmSiv.AArch64.CtrSt p.W icb j t.mem)
    (hx : bytesAt t.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * j))
    (hc : Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R = ciph) :
    WP isa (cryptBlock v.callees) t (VG.Proof.AesGcmSiv.AArch64.BlockPost p ciph icb x j t) := by
  have hw := L.ww
  have hn := L.n_lt
  have hdw := L.dw
  obtain ⟨t₁, run₁, hm₁, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.AArch64.blkArgs_ok E h27
  have E₁ : VG.Proof.AesGcmSiv.AArch64.Env p t₁ := E.keep (fun r hr => ho₁ r (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have dQ : (⟨p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨p.W, 3808⟩ :=
    L.d_w.sub_left (Offset.sub_base p.D (by omega))
  have cc := VG.Proof.AesGcmSiv.AArch64.blkCall L E₁ hj x0 x1 x2 x3 x4 x5
  -- What the copy changed.
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 112, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact VG.Proof.AesGcmSiv.AArch64.copyMem_frame _ _
  have dD : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 112, 16⟩ : Region)], (⟨p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hcb : bytesAt t₁.mem (p.W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.counterBlock icb j := by
    rw [hm₁, VG.Proof.AesGcmSiv.AArch64.copyMem_bytes, C.block]
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (p.W + BitVec.ofNat 64 240) p.R = ciph := by
    rw [← hc]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  have hx₁ : bytesAt t₁.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * j) := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ dD (by omega), hx]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  refine WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_
  have fc := P.frame
  rw [Nat.mul_one] at fc
  have hout := P.out
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    VG.Proof.AesGcmSiv.AArch64.ctr32_single, List.cons.injEq, and_true] at hout
  have hb₂ : bytesAt t₂.mem (p.D + BitVec.ofNat 64 (16 * j)) 16 =
      Spec.Cmac.xor (bytesAt t₁.mem (p.D + BitVec.ofNat 64 (16 * j)) 16) (GcmSiv.ksBlock ciph icb j) := by
    rw [Proof.Cmac.bytesAt_blockAt, hout, VG.Proof.AesGcmSiv.AArch64.toBytes_xor, ← Proof.Cmac.bytesAt_blockAt, Spec.Gcm.blockAt,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
      show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (p.W + BitVec.ofNat 64 240) (16 * (p.R + 1))) =
        Spec.GcmSiv.ctxCiph t₁.mem (p.W + BitVec.ofNat 64 240) p.R from rfl, hc₁, hcb]
  have hk : (GcmSiv.ksBlock ciph icb j).length = 16 := by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  have hx₂ : bytesAt t₂.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * j + 16) := by
    rw [← hxl] at hx₁ ⊢
    refine GcmSiv.ctrPart_step ciph icb x p.D (by decide) hk hx₁ ?_ (by rw [hb₂, List.take_of_length_le (by omega)])
    rw [hxl]
    refine VG.Proof.AesGcmSiv.AArch64.frame_outside fc (fun q hq => ?_) hn (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inl rfl
    · exact .inr (L.d_w' (by decide))
  have E₂ : VG.Proof.AesGcmSiv.AArch64.Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have c₀ := E₂.perm.wR (show 96 + 4 ≤ 3808 by decide)
  have c₁ := E₂.perm.wW (show 96 + 4 ≤ 3808 by decide)
  have h27₂ : t₂.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), h27]
  have h28₂ : t₂.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), h28]
  -- What the first two pieces changed.
  have f₂' : Frame [⟨p.W + BitVec.ofNat 64 112, 16⟩, ⟨p.D + BitVec.ofNat 64 (16 * j), 16⟩,
      ⟨p.W + BitVec.ofNat 64 1760, 2048⟩] t.mem t₂.mem :=
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans fc
  have f₂ : Frame (VG.Proof.AesGcmSiv.AArch64.cryR p.W p.D p.n) t.mem t₂.mem := f₂'.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨⟨p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub p.W (by decide) (by decide)⟩
    · exact ⟨⟨p.D, p.n⟩, by simp, Offset.sub_base p.D (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have dC : ∀ {d k : Nat}, 96 ≤ d → d + k ≤ 112 →
      ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨p.D + BitVec.ofNat 64 (16 * j), 16⟩,
        ⟨p.W + BitVec.ofNat 64 1760, 2048⟩], (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (dQ.sub_right (Lay.wSub (by omega))).symm
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have w₂ : t₂.mem.readW (p.W + BitVec.ofNat 64 96) 32 = t.mem.readW (p.W + BitVec.ofNat 64 96) 32 :=
    f₂'.readW (Region.contains_self _ _) (dC (k := 4) (Nat.le_refl _) (by decide)) (by decide)
  have r₂ : bytesAt t₂.mem (p.W + BitVec.ofNat 64 100) 12 = bytesAt t.mem (p.W + BitVec.ofNat 64 100) 12 :=
    Proof.AesGcm.AArch64.bytesAt_frame f₂' (dC (by decide) (by decide)) (by decide)
  have fw : ∀ v : BitVec 32, Frame [⟨p.W + BitVec.ofNat 64 96, 4⟩] t₂.mem
      (t₂.mem.writeW (p.W + BitVec.ofNat 64 96) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.run ⟨_, by grun [E₂.x19, c₀, c₁, h27₂, h28₂], rfl⟩ fun t₃ ht₃ => ?_
  subst ht₃
  have hmem : ∀ v : BitVec 32, t₂.mem.write (p.W + BitVec.ofNat 64 96) 4 v =
      t₂.mem.writeW (p.W + BitVec.ofNat 64 96) v := fun v => by
    simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]
  refine ⟨E₂.keep (fun r hr => by
      simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
    by simp only [rd_write]; rw [P.rd, rd₁], by simp only [wr_write]; rw [P.wr, wr₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27₂, add_ofNat_assoc]
    congr 2
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h28₂]
    rw [ofNat_sub (by omega) (by omega)]; congr 1
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h28₂]
    rw [ofNat_sub (by omega) (by omega), lsr_ofNat _ _ (by omega)]; congr 2
  · simp only [mem_write, VG.Proof.AesGcmSiv.AArch64.setWidth_rt32]
    refine ⟨?_, ?_⟩
    · rw [hmem, Mem.readW_writeW_self32, VG.Proof.AesGcmSiv.AArch64.read4_readW, w₂, C.word]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
      omega
    · rw [hmem, Proof.AesGcm.AArch64.bytesAt_frame (fw _) (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
          (by decide), r₂, C.rest]
  · simp only [mem_write]
    rw [hmem, Proof.AesGcm.AArch64.bytesAt_frame (fw _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)) (Nat.le_of_lt hn), hx₂,
      show 16 * j + 16 = 16 * (j + 1) by omega]
  · simp only [mem_write]
    rw [hmem]
    exact f₂.writeW (List.mem_cons_self ..) _ (Offset.contains p.W (Nat.le_refl _) (by decide) (by decide))

/-- The encryption key's schedule misses what counter mode writes. -/
theorem key_cryR {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) :
    ∀ r ∈ VG.Proof.AesGcmSiv.AArch64.cryR p.W p.D p.n, (⟨p.W + BitVec.ofNat 64 240, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm

theorem ciph_cryR {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {m m' : Mem} (hf : Frame (VG.Proof.AesGcmSiv.AArch64.cryR p.W p.D p.n) m m') :
    Spec.GcmSiv.ctxCiph m' (p.W + BitVec.ofNat 64 240) p.R = Spec.GcmSiv.ctxCiph m (p.W + BitVec.ofNat 64 240) p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => (VG.Proof.AesGcmSiv.AArch64.key_cryR L r hr).sub_left (Region.sub_prefix L.rounds_le))
    (by have := L.rounds_le; omega)]

/-- What the whole blocks of counter mode leave, from `t`. -/
structure BlocksPost (p : VG.Proof.AesGcmSiv.AArch64.Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (b : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  x27 : t'.gpr .x27 = p.D + BitVec.ofNat 64 (16 * b)
  x28 : t'.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * b)
  ctr : VG.Proof.AesGcmSiv.AArch64.CtrSt p.W icb b t'.mem
  data : bytesAt t'.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * b)
  frame : Frame (VG.Proof.AesGcmSiv.AArch64.cryR p.W p.D p.n) t.mem t'.mem

theorem blocks_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) (hb1 : 1 ≤ p.n / 16)
    (h27 : t.gpr .x27 = p.D) (h28 : t.gpr .x28 = BitVec.ofNat 64 p.n)
    (C : VG.Proof.AesGcmSiv.AArch64.CtrSt p.W icb 0 t.mem) (hx : bytesAt t.mem p.D p.n = x)
    (hc : Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R = ciph) :
    WP isa (.loop (cryptBlock v.callees) (.nonzero .x .x9)) t (VG.Proof.AesGcmSiv.AArch64.BlocksPost p ciph icb x (p.n / 16) t) := by
  refine WP.loop (M := isa) (body := cryptBlock v.callees) (c := .nonzero .x .x9)
    (fun (k : Nat) (t' : State) => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ VG.Proof.AesGcmSiv.AArch64.BlocksPost p ciph icb x j t t') ?_
    (p.n / 16 - 0) t
    ⟨0, rfl, hb1, ⟨E, rfl, rfl, by rw [h27, Nat.mul_zero, BitVec.add_zero], by rw [h28, Nat.mul_zero, Nat.sub_zero],
      C, by rw [hx, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  rintro k t' ⟨j, rfl, hj, P⟩
  have hc' : Spec.GcmSiv.ctxCiph t'.mem (p.W + BitVec.ofNat 64 240) p.R = ciph := by
    rw [VG.Proof.AesGcmSiv.AArch64.ciph_cryR L P.frame, hc]
  refine WP.mono (VG.Proof.AesGcmSiv.AArch64.cryptBlock_ok v L P.env hxl (j := j) (by omega) P.x27 P.x28 P.ctr P.data hc') fun t'' Q => ?_
  have P' : VG.Proof.AesGcmSiv.AArch64.BlocksPost p ciph icb x (j + 1) t t'' :=
    ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.x27, Q.x28, Q.ctr, Q.data, P.frame.trans Q.frame⟩
  have ev := eval_nonzero Q.x9 (by have := L.n_lt; omega)
  by_cases he : j + 1 = p.n / 16
  · left
    exact ⟨ev.trans (by simp; omega), he ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp; omega), p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, P'⟩

/-- What the last bytes of counter mode leave, from `t`. -/
structure TailPost (p : VG.Proof.AesGcmSiv.AArch64.Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  data : bytesAt t'.mem p.D p.n = GcmSiv.ctrPart ciph icb x p.n
  frame : Frame (VG.Proof.AesGcmSiv.AArch64.cryR p.W p.D p.n) t.mem t'.mem

theorem cryptTail_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {b r : Nat}
    (hn : p.n = 16 * b + r) (hr1 : 1 ≤ r) (hr : r < 16) (h27 : t.gpr .x27 = p.D + BitVec.ofNat 64 (16 * b))
    (h28 : t.gpr .x28 = BitVec.ofNat 64 r) (C : VG.Proof.AesGcmSiv.AArch64.CtrSt p.W icb b t.mem)
    (hx : bytesAt t.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * b))
    (hc : Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R = ciph) :
    WP isa (cryptTail v.callees) t (VG.Proof.AesGcmSiv.AArch64.TailPost p ciph icb x t) := by
  have hn' := L.n_lt
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.tag_ok v L E (o := 224) (by decide)) fun t₂ T => ?_)
  have fT := T.frame
  have dT : ∀ q ∈ VG.Proof.AesGcmSiv.AArch64.tagR p.W 224, (⟨p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact L.d_w' (by decide)
  have hx₂ : bytesAt t₂.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * b) := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame fT dT (Nat.le_of_lt hn'), hx]
  have hks : bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 16 = GcmSiv.ksBlock ciph icb b := by
    rw [T.out, hc, C.block]
  have h27₂ : t₂.gpr .x27 = p.D + BitVec.ofNat 64 (16 * b) := by rw [T.x27, h27]
  have h28₂ : t₂.gpr .x28 = BitVec.ofNat 64 r := by rw [T.x28, h28]
  obtain ⟨t₃, run₃, x11₃, x12₃, x13₃, ho₃, m₃, sp₃, rd₃, wr₃⟩ : ∃ t₃ : State, runBlock isa
      [Impl.AesGcm.AArch64.ptr .x11 .x19 bO, Impl.AesGcm.AArch64.mov .x12 .x27, Impl.AesGcm.AArch64.mov .x13 .x28]
        t₂ = some t₃ ∧
      t₃.gpr .x11 = p.W + BitVec.ofNat 64 224 ∧ t₃.gpr .x12 = p.D + BitVec.ofNat 64 (16 * b) ∧
      t₃.gpr .x13 = BitVec.ofNat 64 r ∧ Others [.x11, .x12, .x13] t₂ t₃ ∧ t₃.mem = t₂.mem ∧ t₃.sp = t₂.sp ∧
      t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by grun [], ?_, ?_, ?_, by others_tac, (by rfl), (by rfl), (by rfl), (by rfl)⟩
    · simp [gpr_write, T.env.x19]
    · simp [gpr_write, h27₂]
    · simp [gpr_write, h28₂]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have dQ : (⟨p.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨p.W, 3808⟩ :=
    L.d_w.sub_left (Offset.sub_base p.D (by omega))
  have lp : LoopPre t₃ (p.W + BitVec.ofNat 64 224) (p.D + BitVec.ofNat 64 (16 * b)) r := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [rd₃, wr₃]
      exact Proof.AesGcm.AArch64.covers_prefix (T.env.perm.wCR (show 224 + 16 ≤ 3808 by decide)) (by omega)
    · rw [wr₃]; exact covers_off T.env.perm.d (by omega) hn'
    · exact ((dQ.sub_right (Lay.wSub (show 224 + 16 ≤ 3808 by decide))).sub_right (Region.sub_prefix (by omega))).symm
  refine WP.mono (xorLoop_ok t₃ x11₃ x12₃ x13₃ (by omega) lp) fun t₄ ⟨hm₄, ho₄, sp₄, rd₄, wr₄⟩ => ?_
  rw [m₃] at hm₄
  have hl : (xorBytes t₂.mem (p.D + BitVec.ofNat 64 (16 * b)) (p.W + BitVec.ofNat 64 224) r).length = r := by
    simp [xorBytes, Proof.Cmac.bytesAt_length]
  have fw := Proof.AesGcm.AArch64.writeBytes_frame' t₂.mem (q := p.D + BitVec.ofNat 64 (16 * b)) hl
  rw [← hm₄] at fw
  have hk : (GcmSiv.ksBlock ciph icb b).length = 16 := by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  refine ⟨T.env.keep (fun q hq => by
      rw [ho₄ q (by
        simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ho₃ q (by
        simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)])
      (by rw [sp₄, sp₃]) (by rw [rd₄, rd₃]) (by rw [wr₄, wr₃]),
    by rw [rd₄, rd₃, T.rd], by rw [wr₄, wr₃, T.wr], ?_, ?_⟩
  · have hb' : bytesAt t₄.mem (p.D + BitVec.ofNat 64 (16 * b)) r = Spec.Cmac.xor
        (bytesAt t₂.mem (p.D + BitVec.ofNat 64 (16 * b)) r) ((GcmSiv.ksBlock ciph icb b).take r) := by
      have e := Proof.AesGcm.AArch64.bytesAt_writeBytes_self t₂.mem (p.D + BitVec.ofNat 64 (16 * b))
        (xorBytes t₂.mem (p.D + BitVec.ofNat 64 (16 * b)) (p.W + BitVec.ofNat 64 224) r) (by omega)
      rw [hl] at e
      have hs := Proof.Cmac.bytesAt_add t₂.mem (p.W + BitVec.ofNat 64 224) r (16 - r)
      rw [show r + (16 - r) = 16 by omega, hks] at hs
      rw [hm₄, e, xorBytes, hs, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rfl
    have := GcmSiv.ctrPart_step ciph icb x p.D (i := b) (n := r) (by omega) hk (by rw [hxl]; exact hx₂)
      (VG.Proof.AesGcmSiv.AArch64.frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; exact hn') (by omega)) hb'
    rwa [hxl, ← hn] at this
  · refine (fT.sub fun q hq => ?_).trans (fw.sub fun q hq => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨⟨p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub p.W (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨p.D, p.n⟩, by simp, Offset.sub_base p.D (by omega)⟩

/-- What `crypt` leaves, from `t`. -/
structure CryptPost (p : VG.Proof.AesGcmSiv.AArch64.Prm) (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (VG.Proof.AesGcmSiv.AArch64.cryR p.W p.D p.n) t.mem t'.mem
  data : bytesAt t'.mem p.D p.n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R)
    (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) (bytesAt t.mem p.D p.n)

/-- The memory `cryptHead` leaves: the counter block from the tag. -/
def headMem (m : Mem) (W : Addr) : Mem :=
  (m.writeW (W + BitVec.ofNat 64 96) (m.readW W 64)).writeW (W + BitVec.ofNat 64 104)
    (m.readW (W + BitVec.ofNat 64 8) 64 ||| 0x8000000000000000#64)

/-- The start of `crypt`: the counter block from the tag, and the data as
the bytes to encrypt. -/
theorem cryptHead_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) :
    ∃ t₁ : State, runBlock isa cryptHead t = some t₁ ∧ t₁.mem = VG.Proof.AesGcmSiv.AArch64.headMem t.mem p.W ∧
      t₁.gpr .x27 = p.D ∧ t₁.gpr .x28 = BitVec.ofNat 64 p.n ∧ t₁.gpr .x9 = BitVec.ofNat 64 (p.n / 16) ∧
      Others [.x9, .x10, .x27, .x28] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have rT₀ : InRegions (t.rd ++ t.wr) p.W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3808 by decide)
  have rT₈ := E.perm.wR (show 8 + 8 ≤ 3808 by decide)
  have w₀ := E.perm.wW (show 96 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wW (show 104 + 8 ≤ 3808 by decide)
  refine ⟨_, by simp only [cryptHead]; grun [E.x19, BitVec.add_zero, rT₀, rT₈, w₀, w₈], ?_, ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · have sep : ∀ v : BitVec (8 * 8), (t.mem.write (p.W + BitVec.ofNat 64 96) 8 v).read (p.W + BitVec.ofNat 64 8) 8 =
        t.mem.read (p.W + BitVec.ofNat 64 8) 8 := fun _ =>
      Mem.read_write_sep (Offset.sep p.W (.inl (by decide)) (by decide) (by decide)) (by decide)
    have mz : (BitVec.setWidth 64 (32768 : BitVec 16) <<< 48 : BitVec 64) = 0x8000000000000000#64 := by decide
    rw [VG.Proof.AesGcmSiv.AArch64.headMem]
    simp only [mem_write, sep, mz, Mem.writeW, BitVec.setWidth_eq, VG.Proof.AesGcmSiv.AArch64.read8_readW]
  · simp [gpr_write, E.x25]
  · simp [gpr_write, E.x26]
  · simp [gpr_write, E.x26, lsr_ofNat _ _ L.n_lt]

theorem crypt_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) :
    WP isa (crypt v.callees) t (VG.Proof.AesGcmSiv.AArch64.CryptPost p t) := by
  have hw := L.ww
  have hn := L.n_lt
  obtain ⟨t₁, run₁, hm₁, x27₁, x28₁, x9₁, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.AArch64.cryptHead_ok L E
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem p.D p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem := by
    rw [hm₁, VG.Proof.AesGcmSiv.AArch64.headMem, show p.W + BitVec.ofNat 64 104 = p.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by
      rw [add_ofNat_assoc]]
    exact Proof.Cmac.frame_store2 _ _ _
  have dD : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hx₁ : bytesAt t₁.mem p.D p.n = bytesAt t.mem p.D p.n := Proof.AesGcm.AArch64.bytesAt_frame f₁ dD (Nat.le_of_lt hn)
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (p.W + BitVec.ofNat 64 240) p.R =
      Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  have hicb : bytesAt t₁.mem (p.W + BitVec.ofNat 64 96) 16 =
      Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16) := by
    rw [hm₁, VG.Proof.AesGcmSiv.AArch64.headMem, show p.W + BitVec.ofNat 64 104 = p.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by
        rw [add_ofNat_assoc], Proof.Cmac.bytesAt_store2, ← GcmSiv.initialCounter_words, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]
  have h4 := Proof.Cmac.bytesAt_add t₁.mem (p.W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, add_ofNat_assoc] at h4
  have C₀ : VG.Proof.AesGcmSiv.AArch64.CtrSt p.W (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) 0 t₁.mem := by
    refine ⟨?_, ?_⟩
    · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  have E₁ : VG.Proof.AesGcmSiv.AArch64.Env p t₁ := E.keep (fun r hr => ho₁ r (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have fC : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 96, 16⟩ : Region)], ∃ q' ∈ VG.Proof.AesGcmSiv.AArch64.cryR p.W p.D p.n, Region.Sub q q' :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub p.W (by decide) (by decide)⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The whole blocks.
  have hmid : WP isa (.ite (.zero .x .x9) (.block []) (.loop (cryptBlock v.callees) (.nonzero .x .x9))) t₁
      (VG.Proof.AesGcmSiv.AArch64.BlocksPost p (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) (bytesAt t.mem p.D p.n) (p.n / 16) t₁) := by
    refine WP.ite (decide (p.n / 16 = 0)) (eval_zero x9₁ (by omega)) (fun ht => ?_) (fun hf => ?_)
    · have h0 : p.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨E₁, rfl, rfl, by rw [x27₁, Nat.mul_zero, BitVec.add_zero], by rw [x28₁, Nat.mul_zero, Nat.sub_zero], C₀,
        by rw [Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁], Frame.refl _ _⟩
    · have h0 : p.n / 16 ≠ 0 := by simpa using hf
      exact VG.Proof.AesGcmSiv.AArch64.blocks_ok v L E₁ hxl (by omega) x27₁ x28₁ C₀ hx₁ hc₁
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  have x28₂ : t₂.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [B.x28]; congr 1; omega
  refine WP.ite (decide (p.n % 16 = 0)) (eval_zero x28₂ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨B.env, by rw [B.rd, rd₁], by rw [B.wr, wr₁], (f₁.sub fC).trans B.frame, ?_⟩
    rw [B.data, show 16 * (p.n / 16) = p.n by omega, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : p.n % 16 ≠ 0 := by simpa using hf
    have hc₂ : Spec.GcmSiv.ctxCiph t₂.mem (p.W + BitVec.ofNat 64 240) p.R =
        Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
      rw [VG.Proof.AesGcmSiv.AArch64.ciph_cryR L B.frame, hc₁]
    refine WP.mono (VG.Proof.AesGcmSiv.AArch64.cryptTail_ok v L B.env hxl (b := p.n / 16) (r := p.n % 16) (by omega) (by omega) (by omega)
      B.x27 x28₂ B.ctr B.data hc₂) fun t₄ T => ?_
    refine ⟨T.env, by rw [T.rd, B.rd, rd₁], by rw [T.wr, B.wr, wr₁], ((f₁.sub fC).trans B.frame).trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.AArch64.Fn`. -/
section

/-!
# AES-GCM-SIV on AArch64: comparing the tags, and `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`

Untrusted: everything here is checked by Lean. `cmp` leaves in `x27`
whether the received tag at `W` equals the computed one at `W + 224`,
without a branch (`cmp_ok`); `mask` ANDs every byte of the data with
`0 − x27`, leaving it if the tags are equal and zeroing it if not
(`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc)
open VG.Proof.AesGcm.AArch64 (add_ofNat_assoc ofNat_sub eval_zero eval_nonzero Others in_of_covers
  length_bytesAt succ_ofNat read_one)

/-- `x27` from the words of the tags: 1 if they are equal, 0 if not. -/
theorem ok_val (d : BitVec 64) :
    (BitVec.setWidth 64 (1#16) <<< 0 : BitVec 64) - BitVec.ofNat 64 (if d = 0 then 0 else 1) =
      BitVec.ofNat 64 (if d = 0 then 1 else 0) := by
  by_cases h : d = 0 <;> simp only [h, ↓reduceIte] <;> decide

theorem cmp_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) :
    ∃ t' : State, runBlock isa cmp t = some t' ∧
      t'.gpr .x27 = BitVec.ofNat 64 (if bytesAt t.mem p.W 16 = bytesAt t.mem (p.W + BitVec.ofNat 64 224) 16
        then 1 else 0) ∧
      Others [.x9, .x10, .x11, .x12, .x27] t t' ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₀ : InRegions (t.rd ++ t.wr) p.W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3808 by decide)
  have r₈ := E.perm.wR (show 8 + 8 ≤ 3808 by decide)
  have u₀ := E.perm.wR (show 224 + 8 ≤ 3808 by decide)
  have u₈ := E.perm.wR (show 232 + 8 ≤ 3808 by decide)
  refine ⟨_, by simp only [VG.Impl.AesGcmSiv.AArch64.cmp]; grun [E.x19, BitVec.add_zero, r₀, r₈, u₀, u₈, gpr_addWithCarry, c_addWithCarry,
    mem_addWithCarry, rd_addWithCarry, wr_addWithCarry, sp_addWithCarry, c_write], ?_,
    fun r hr => ?_, (by rfl), (by rfl), (by rfl), (by rfl)⟩
  · have key := Proof.AesGcm.AArch64.words_eq t.mem p.W (p.W + BitVec.ofNat 64 224)
    rw [add_ofNat_assoc] at key
    simp only [gpr_addWithCarry, gpr_write, Mem.readW, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
      Size.bits, Nat.reduceAdd, show (BitVec.setWidth 64 0#16 <<< (16 * 0) : BitVec 64) = 0 from rfl, Nat.reduceDiv,
      Nat.reduceMul]
    refine (congrArg (HSub.hSub (BitVec.setWidth 64 (1#16) <<< 0 : BitVec 64))
      (Proof.AesGcm.AArch64.carry_val _)).trans ((VG.Proof.AesGcmSiv.AArch64.ok_val _).trans ?_)
    simp only [Mem.readW, BitVec.setWidth_eq] at key
    simp only [key]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, gpr_addWithCarry, hr]

/-! ## The mask -/

abbrev maskBody : List Instr :=
  [.ldrb .x14 .x12 0, .logic .and .w .x14 .x14 .x11, .strb .x14 .x12 0, Impl.AesGcm.AArch64.ptr .x12 .x12 1,
    .subImm .x .x13 .x13 1]

theorem byte_and (a : BitVec (8 * 1)) (k : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 a)) &&& BitVec.setWidth 32 k))) =
      a &&& k.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, show i < 64 by omega, show i < 32 by omega,
    hi, decide_true, Bool.true_and]

theorem maskStep_ok (s : State) {A : Addr} (ha : s.gpr .x12 + BitVec.ofNat 64 0 = A) (w : InRegions s.wr A 1) :
    ∃ s', runBlock isa VG.Proof.AesGcmSiv.AArch64.maskBody s = some s' ∧ s'.mem = s.mem.writeW A (s.mem A &&& (s.gpr .x11).setWidth 8) ∧
      s'.gpr .x12 = s.gpr .x12 + 1 ∧ s'.gpr .x13 = s.gpr .x13 - 1 ∧
      Others [.x12, .x13, .x14] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have wa := Proof.AesGcm.AArch64.in_left (rd := s.rd) w
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, VG.Proof.AesGcmSiv.AArch64.maskBody,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      Impl.AesGcm.AArch64.ptr, ha, w, wa]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], by others_tac, rfl, rfl, rfl⟩
  simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, Mem.writeW, VG.Proof.AesGcmSiv.AArch64.byte_and, read_one,
    Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

/-- Byte `i` at `D`, not yet written. -/
theorem dst_kept' {m : Mem} {D : Addr} {i : Nat} (hi : i < 2 ^ 64) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.lt_irrefl,
    ite_false]

/-- The first `i` bytes at `D`, each ANDed with `k`. -/
abbrev maskBytes (m : Mem) (D : Addr) (k : Byte) (i : Nat) : List Byte := (bytesAt m D i).map (· &&& k)

theorem maskLoop_ok (s : State) {D : Addr} {n : Nat} (hd : s.gpr .x12 = D) (hn : s.gpr .x13 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hnl : n < 2 ^ 64) (hw : Covers [⟨D, n⟩] s.wr) :
    WP isa (.loop (.block VG.Proof.AesGcmSiv.AArch64.maskBody) (.nonzero .x .x13)) s fun s' =>
      s'.mem = writeBytes s.mem D (VG.Proof.AesGcmSiv.AArch64.maskBytes s.mem D ((s.gpr .x11).setWidth 8) n) ∧
      Others [.x12, .x13, .x14] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcmSiv.AArch64.maskBody) (c := .nonzero .x .x13)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .x12 = D + BitVec.ofNat 64 i ∧
      t.gpr .x13 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (VG.Proof.AesGcmSiv.AArch64.maskBytes s.mem D ((s.gpr .x11).setWidth 8) i) ∧
      Others [.x12, .x13, .x14] s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, by omega, by rw [hd]; simp, by rw [hn, Nat.sub_zero], by simp [VG.Proof.AesGcmSiv.AArch64.maskBytes, bytesAt, writeBytes_nil],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, x12, x13, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x12', x13', g', sp', rd', wr'⟩ := VG.Proof.AesGcmSiv.AArch64.maskStep_ok t (A := D + BitVec.ofNat 64 i)
    (by rw [x12, BitVec.add_zero]) (by rw [wr]; exact in_of_covers hw hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (VG.Proof.AesGcmSiv.AArch64.maskBytes s.mem D ((s.gpr .x11).setWidth 8) i).length = i := by
    simp [VG.Proof.AesGcmSiv.AArch64.maskBytes, length_bytesAt]
  have h11 : t.gpr .x11 = s.gpr .x11 := g _ (by decide)
  have hmem : t'.mem = writeBytes s.mem D (VG.Proof.AesGcmSiv.AArch64.maskBytes s.mem D ((s.gpr .x11).setWidth 8) (i + 1)) := by
    rw [mem', mem, VG.Proof.AesGcmSiv.AArch64.dst_kept' (by omega) _ hlen, h11]
    simp only [VG.Proof.AesGcmSiv.AArch64.maskBytes]
    rw [Proof.AesGcm.AArch64.bytesAt_succ, List.map_append, List.map_cons, List.map_nil,
      writeBytes_snoc s.mem D _ _ (by rw [List.length_map, length_bytesAt]; omega),
      List.length_map, length_bytesAt]
  have x13'' : t'.gpr .x13 = BitVec.ofNat 64 (n - (i + 1)) := by
    rw [x13', x13, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := eval_nonzero (r := .x13) (a := n - (i + 1)) x13'' (by omega)
  have gg : Others [.x12, .x13, .x14] s t' := fun r hr => by rw [g' r hr, g r hr]
  by_cases he : i + 1 = n
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x12', x12, BitVec.add_assoc, succ_ofNat], x13'', hmem, gg, by rw [sp', sp], by rw [rd', rd],
      by rw [wr', wr]⟩

theorem map_and_ff (xs : List Byte) : xs.map (· &&& (0#64 - BitVec.ofNat 64 1 : BitVec 64).setWidth 8) = xs := by
  rw [show (0#64 - BitVec.ofNat 64 1 : BitVec 64).setWidth 8 = BitVec.allOnes 8 by decide,
    show (fun x : Byte => x &&& BitVec.allOnes 8) = id from funext fun x => BitVec.and_allOnes, List.map_id]

theorem map_and_zero (xs : List Byte) : xs.map (· &&& (0#64 - BitVec.ofNat 64 0 : BitVec 64).setWidth 8) =
    Spec.GcmSiv.zeros xs.length := by
  rw [show (0#64 - BitVec.ofNat 64 0 : BitVec 64).setWidth 8 = 0#8 by decide]
  simp [Spec.GcmSiv.zeros, List.map_const']

/-- What `mask` leaves, from `t`, when `x27` is whether `c` holds. -/
structure MaskPost (p : VG.Proof.AesGcmSiv.AArch64.Prm) (c : Prop) [Decidable c] (t t' : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t'
  x27 : t'.gpr .x27 = t.gpr .x27
  frame : Frame [⟨p.D, p.n⟩] t.mem t'.mem
  data : bytesAt t'.mem p.D p.n = if c then bytesAt t.mem p.D p.n else Spec.GcmSiv.zeros p.n

theorem mask_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {c : Prop} [Decidable c]
    (hok : t.gpr .x27 = BitVec.ofNat 64 (if c then 1 else 0)) :
    WP isa mask t (VG.Proof.AesGcmSiv.AArch64.MaskPost p c t) := by
  have hn := L.n_lt
  obtain ⟨t₁, run₁, x11₁, x12₁, x13₁, ho₁, hm₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa
      [Impl.AesGcm.AArch64.imm .x9 0, .sub .x .x11 .x9 .x27, Impl.AesGcm.AArch64.mov .x12 .x25,
        Impl.AesGcm.AArch64.mov .x13 .x26] t = some t₁ ∧
      t₁.gpr .x11 = 0#64 - t.gpr .x27 ∧ t₁.gpr .x12 = p.D ∧ t₁.gpr .x13 = BitVec.ofNat 64 p.n ∧
      Others [.x9, .x11, .x12, .x13] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by grun [], ?_, ?_, ?_, by others_tac, (by rfl), (by rfl), (by rfl), (by rfl)⟩
    · simp [gpr_write]
    · simp [gpr_write, E.x25]
    · simp [gpr_write, E.x26]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesGcmSiv.AArch64.Env p t₁ := E.keep (fun r hr => ho₁ r (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have x27₁ : t₁.gpr .x27 = t.gpr .x27 := ho₁ _ (by decide)
  refine WP.ite (decide (p.n = 0)) (eval_zero x13₁ hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n = 0 := by simpa using ht
    refine WP.block_nil ⟨E₁, x27₁, by rw [hm₁]; exact Frame.refl _ _, ?_⟩
    rw [h0]; split <;> simp [bytesAt, Spec.GcmSiv.zeros]
  · have h0 : p.n ≠ 0 := by simpa using hf
    refine WP.mono (VG.Proof.AesGcmSiv.AArch64.maskLoop_ok t₁ x12₁ x13₁ (by omega) hn E₁.perm.d) fun t₂ ⟨hm₂, ho₂, sp₂, rd₂, wr₂⟩ => ?_
    have hl : (VG.Proof.AesGcmSiv.AArch64.maskBytes t₁.mem p.D ((t₁.gpr .x11).setWidth 8) p.n).length = p.n := by
      simp [VG.Proof.AesGcmSiv.AArch64.maskBytes, length_bytesAt]
    refine ⟨E₁.keep (fun r hr => ho₂ r (by
        simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂,
      by rw [ho₂ _ (by decide), x27₁], by rw [hm₂, ← hm₁]; exact Proof.AesGcm.AArch64.writeBytes_frame' _ hl, ?_⟩
    have e := Proof.AesGcm.AArch64.bytesAt_writeBytes_self t₁.mem p.D
      (VG.Proof.AesGcmSiv.AArch64.maskBytes t₁.mem p.D ((t₁.gpr .x11).setWidth 8) p.n) (by omega)
    rw [hl] at e
    rw [hm₂, e, x11₁, hok, hm₁]
    simp only [VG.Proof.AesGcmSiv.AArch64.maskBytes]
    split
    · exact VG.Proof.AesGcmSiv.AArch64.map_and_ff _
    · rw [VG.Proof.AesGcmSiv.AArch64.map_and_zero, length_bytesAt]

end VG.Proof.AesGcmSiv.AArch64

/-!
## The arguments and the entry

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the public arguments (`prmOf`), how they lie (`lay_of`)
and what the state may access (`args_of_seal`, `args_of_open`). `entry`
loads `W` from the stack, saves our caller's registers at `W + 128`, as
AES-GCM does, keeps the arguments in `x19`–`x26` and `tag` at `W + 216`
(`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (saved)
open VG.Proof.AesGcm.AArch64 (covers_of_mem covers_left SavedAt savedR save_ok savedMem_frame savedAt_save in_off
  Others)

/-- The public arguments of a state. -/
def prmOf (s : State) : VG.Proof.AesGcmSiv.AArch64.Prm where
  K := s.gpr .x0
  W := stackArg s 0
  N := s.gpr .x2
  A := s.gpr .x3
  D := s.gpr .x5
  T := s.gpr .x7
  SP := s.sp
  R := (s.gpr .x1).toNat
  al := (s.gpr .x4).toNat
  n := (s.gpr .x6).toNat

theorem lay_of {s : State} (h : VG.Proof.AesGcmSiv.AArch64.oneLay s) : VG.Proof.AesGcmSiv.AArch64.Lay (VG.Proof.AesGcmSiv.AArch64.prmOf s) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, _, _, b1, b2, b3, b4, b5, b6, _, hR⟩ := h
  exact ⟨b1, b6, b2, b3, b4, d2, d1, d4, d3, d6, d5, d9, b5, d8, d7, hR, BitVec.isLt _, BitVec.isLt _⟩

/-- The permissions, from the buffers' coverage. -/
theorem perm_of_cov {s : State} (hk : Covers [⟨s.gpr .x0, 240⟩] (s.rd ++ s.wr))
    (hN : Covers [⟨s.gpr .x2, 12⟩] (s.rd ++ s.wr)) (hA : Covers [⟨s.gpr .x3, (s.gpr .x4).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .x5, (s.gpr .x6).toNat⟩] s.wr) (hW : Covers [⟨stackArg s 0, 3808⟩] s.wr)
    (hT : Covers [⟨s.gpr .x7, 16⟩] (s.rd ++ s.wr)) : VG.Proof.AesGcmSiv.AArch64.Perm (VG.Proof.AesGcmSiv.AArch64.prmOf s) s :=
  ⟨hk, hN, hA, hD, hW, hT⟩

/-- `seal`'s layout and permissions, its tag to write, and its stack argument
to read. -/
theorem args_of_seal {s : State} (h : VG.Proof.AesGcmSiv.AArch64.sealPre s) :
    VG.Proof.AesGcmSiv.AArch64.Lay (VG.Proof.AesGcmSiv.AArch64.prmOf s) ∧ VG.Proof.AesGcmSiv.AArch64.Perm (VG.Proof.AesGcmSiv.AArch64.prmOf s) s ∧ Covers [⟨s.gpr .x7, 16⟩] s.wr ∧ Covers [VG.Proof.AesGcmSiv.AArch64.args s] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, 12⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩, VG.Proof.AesGcmSiv.AArch64.args s],
      Covers [r] (s.rd ++ s.wr) := fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region), ⟨s.gpr .x7, 16⟩, ⟨stackArg s 0, 3808⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨VG.Proof.AesGcmSiv.AArch64.lay_of hl, VG.Proof.AesGcmSiv.AArch64.perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (covers_left (mwr _ (by simp))), mwr _ (by simp), mrd _ (by simp)⟩

/-- `open`'s layout and permissions, with its received tag to read, and its
stack argument to read. -/
theorem args_of_open {s : State} (h : VG.Proof.AesGcmSiv.AArch64.openPre s) :
    VG.Proof.AesGcmSiv.AArch64.Lay (VG.Proof.AesGcmSiv.AArch64.prmOf s) ∧ VG.Proof.AesGcmSiv.AArch64.Perm (VG.Proof.AesGcmSiv.AArch64.prmOf s) s ∧ Covers [VG.Proof.AesGcmSiv.AArch64.args s] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, 12⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
      ⟨s.gpr .x7, 16⟩, VG.Proof.AesGcmSiv.AArch64.args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region), ⟨stackArg s 0, 3808⟩], Covers [r] s.wr :=
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨VG.Proof.AesGcmSiv.AArch64.lay_of hl, VG.Proof.AesGcmSiv.AArch64.perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (mrd _ (by simp)), mrd _ (by simp)⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- What the entry writes: the save area and `tag`'s address. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 96⟩

/-- `tag`'s address, at `W + 216`. -/
abbrev TagSlot (p : VG.Proof.AesGcmSiv.AArch64.Prm) (m : Mem) : Prop := m.readW (p.W + BitVec.ofNat 64 216) 64 = p.T

/-- `entry`. -/
theorem entry_ok {s : State} (P : VG.Proof.AesGcmSiv.AArch64.Perm (VG.Proof.AesGcmSiv.AArch64.prmOf s) s) (hA : Covers [VG.Proof.AesGcmSiv.AArch64.args s] (s.rd ++ s.wr)) :
    WP isa (.block entry) s fun s₁ => VG.Proof.AesGcmSiv.AArch64.Env (VG.Proof.AesGcmSiv.AArch64.prmOf s) s₁ ∧ SavedAt s₁.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).W s ∧
      Frame [VG.Proof.AesGcmSiv.AArch64.entryR (VG.Proof.AesGcmSiv.AArch64.prmOf s).W] s.mem s₁.mem ∧ VG.Proof.AesGcmSiv.AArch64.TagSlot (VG.Proof.AesGcmSiv.AArch64.prmOf s) s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have a₀ : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa [VG.Proof.AesGcmSiv.AArch64.args, stackArgAddr] using in_off (d := 0) (n := 8) hA (by decide) (by decide)
  refine WP.block_append (WP.block_append (WP.run ⟨_, by grun [BitVec.add_zero, a₀], rfl⟩ fun s₀ hs₀ => ?_))
  subst hs₀
  have hW₀ : (s.write .x .x9 (s.mem.readW s.sp 64)).gpr .x9 = (VG.Proof.AesGcmSiv.AArch64.prmOf s).W := by
    simp [gpr_write, VG.Proof.AesGcmSiv.AArch64.prmOf, stackArg, stackArgAddr]
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok _ .x9 hW₀ (by simpa only [wr_write] using P.w2560)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hWv : (VG.Proof.AesGcmSiv.AArch64.prmOf s).W = s.mem.readW s.sp 64 := by simp [VG.Proof.AesGcmSiv.AArch64.prmOf, stackArg, stackArgAddr, Mem.readW]
  have w216 : InRegions s₁.wr (s.mem.readW s.sp 64 + BitVec.ofNat 64 216) 8 := by
    rw [wr₁, ← hWv]; simpa only [wr_write] using in_off P.w (show 216 + 8 ≤ 3808 by decide) (by decide)
  refine WP.run ⟨_, by grun [g₁, BitVec.add_zero, w216], rfl⟩ fun s₂ hs₂ => ?_
  subst hs₂
  have hs : ∀ r ∈ saved, (s.write .x .x9 (s.mem.readW s.sp 64)).gpr r.1 = s.gpr r.1 := by
    intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  have sv : SavedAt s₁.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).W s := by
    rw [m₁]; exact fun p hp => (savedAt_save _ _ _ p hp).trans (hs p hp)
  have fS : Frame [VG.Proof.AesGcmSiv.AArch64.entryR (VG.Proof.AesGcmSiv.AArch64.prmOf s).W] s.mem s₁.mem := by
    rw [m₁]; simp only [mem_write]
    exact (savedMem_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have c216 : (VG.Proof.AesGcmSiv.AArch64.entryR (VG.Proof.AesGcmSiv.AArch64.prmOf s).W).Contains ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 216) (64 / 8) := by
    rw [show (VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 216 = ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 128) + BitVec.ofNat 64 88 from
      (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by decide) (by decide)
  have e : ∀ (m : Mem) (a : Addr) (v : BitVec 64), m.write a 8 v = m.writeW a v := fun m a v => by
    simp [Mem.writeW]
  rw [← hWv] at *
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp only [sp_write]; rw [sp₁]; rfl,
    P.of_eq (by simp only [rd_write]; exact rd₁) (by simp only [wr_write]; exact wr₁)⟩, ?_, ?_, ?_, ?_, ?_⟩
  iterate 8 (simp [gpr_write, g₁, VG.Proof.AesGcmSiv.AArch64.prmOf, VG.Proof.AesGcmSiv.AArch64.ofNat_toNat64, stackArg, stackArgAddr, Mem.readW])
  · simp only [mem_write, e]
    exact sv.frame ((Frame.refl [(⟨(VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 216, 8⟩ : Region)] _).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  · simp only [mem_write, e]
    exact fS.writeW (List.mem_singleton_self _) _ c216
  · simp only [mem_write, e, VG.Proof.AesGcmSiv.AArch64.TagSlot, Mem.readW_writeW_self64]
    simp [gpr_write, g₁, VG.Proof.AesGcmSiv.AArch64.prmOf]
  · simp only [rd_write]; exact rd₁
  · simp only [wr_write]; exact wr₁

/-! ## The tag's copies -/

/-- A 16-byte block copied from `S` to `T`, by words. -/
theorem bytesAt_copy2 (m : Mem) (S T : Addr) (hs : Mem.Sep (S + BitVec.ofNat 64 8) (64 / 8) T (64 / 8)) :
    bytesAt ((m.writeW T (m.readW S 64)).writeW (T + BitVec.ofNat 64 8)
      ((m.writeW T (m.readW S 64)).readW (S + BitVec.ofNat 64 8) 64)) T 16 = bytesAt m S 16 := by
  rw [Mem.readW_writeW_sep hs (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
    ← Proof.Cmac.bytesAt_split]

/-- `recv`: the received tag, at `T`, copied to `W`. -/
theorem recv_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {s : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p s) (hT : VG.Proof.AesGcmSiv.AArch64.TagSlot p s.mem) :
    ∃ s', runBlock isa recv s = some s' ∧ Frame [⟨p.W, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem p.W 16 = bytesAt s.mem p.T 16 ∧ s'.gpr .x9 = p.T ∧ Others [.x9, .x10] s s' ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := E.perm.wR (show 216 + 8 ≤ 3808 by decide)
  have t₀ : InRegions (s.rd ++ s.wr) p.T 8 := by simpa using in_off (d := 0) (n := 8) E.perm.t (by decide) (by decide)
  have t₈ := in_off (d := 8) (n := 8) E.perm.t (by decide) (by decide)
  have w₀ : InRegions s.wr p.W 8 := by simpa using E.perm.wW (show 0 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wW (show 8 + 8 ≤ 3808 by decide)
  have hT' : s.mem.read (p.W + BitVec.ofNat 64 216) 8 = p.T := by rw [VG.Proof.AesGcmSiv.AArch64.read8_readW]; exact hT
  have hs : Mem.Sep (p.T + BitVec.ofNat 64 8) (64 / 8) p.W (64 / 8) :=
    L.t_w.sep (Offset.contains_base p.T (d := 8) (n := 8) (k := 16) (by decide) (by decide))
      (by simpa using Offset.contains_base p.W (d := 0) (n := 8) (k := 3808) (by decide) (by decide))
  refine ⟨_, by simp only [recv]; grun [E.x19, BitVec.add_zero, r₀, hT', t₀, t₈, w₀, w₈], ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, VG.Proof.AesGcmSiv.AArch64.read8_readW]
    exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, VG.Proof.AesGcmSiv.AArch64.read8_readW]
    exact VG.Proof.AesGcmSiv.AArch64.bytesAt_copy2 _ _ _ hs
  · simp [gpr_write]

/-- `tagOut`: the tag at `W` copied to `T`, which the state may write. -/
theorem tagOut_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {s : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p s) (hT : VG.Proof.AesGcmSiv.AArch64.TagSlot p s.mem)
    (hTw : Covers [⟨p.T, 16⟩] s.wr) :
    ∃ s', runBlock isa tagOut s = some s' ∧ Frame [⟨p.T, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem p.T 16 = bytesAt s.mem p.W 16 ∧ s'.gpr .x9 = p.T ∧ Others [.x9, .x10] s s' ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := E.perm.wR (show 216 + 8 ≤ 3808 by decide)
  have t₀ : InRegions s.wr p.T 8 := by simpa using in_off (d := 0) (n := 8) hTw (by decide) (by decide)
  have t₈ := in_off (d := 8) (n := 8) hTw (by decide) (by decide)
  have w₀ : InRegions (s.rd ++ s.wr) p.W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wR (show 8 + 8 ≤ 3808 by decide)
  have hT' : s.mem.read (p.W + BitVec.ofNat 64 216) 8 = p.T := by rw [VG.Proof.AesGcmSiv.AArch64.read8_readW]; exact hT
  have hs : Mem.Sep (p.W + BitVec.ofNat 64 8) (64 / 8) p.T (64 / 8) :=
    L.t_w.symm.sep (Offset.contains_base p.W (d := 8) (n := 8) (k := 3808) (by decide) (by decide))
      (by simpa using Offset.contains_base p.T (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  refine ⟨_, by simp only [tagOut]; grun [E.x19, BitVec.add_zero, r₀, hT', t₀, t₈, w₀, w₈], ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, VG.Proof.AesGcmSiv.AArch64.read8_readW]
    exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, VG.Proof.AesGcmSiv.AArch64.read8_readW]
    exact VG.Proof.AesGcmSiv.AArch64.bytesAt_copy2 _ _ _ hs
  · simp [gpr_write]

/-! ## Regions -/

/-- Proves that a region is disjoint from each of a list of regions: parts
of `W`, the data, or the key schedule. -/
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
    | with_reducible exact Lay.k_d $L
    | with_reducible exact Lay.n_d $L
    | with_reducible exact Lay.a_d $L
    | (with_reducible refine Lay.t_w' $L ?_) <;> decide
    | with_reducible exact Lay.t_d $L
    | with_reducible exact (Lay.t_d $L).symm
    | with_reducible exact (Lay.d_w $L).symm))

end VG.Proof.AesGcmSiv.AArch64

/-!
## `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, the
copy of the tag to `tag` and the restore compute `encryptWith` (RFC 8452 §4) of the arguments
(`seal_wp`), given that the tag input computed with GHASH is the RFC's
(`Proof.GcmSiv.Words.tagInputG`, related to it in `Verified.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.AArch64 (GcmImpl SavedAt savedR exit_ok)

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
abbrev TagInputEq : Prop := ∀ a n pt d : List Byte, Spec.GcmSiv.tagInput a n pt d = tagInputG a n pt d

theorem bytesAt_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨P, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' P n = bytesAt m P n :=
  Proof.AesGcm.AArch64.bytesAt_frame hf hd hn

theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr} {R : Nat}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) (hR : 16 * (R + 1) ≤ 240) :
    Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [VG.Proof.AesGcmSiv.AArch64.bytesAt_keep hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

/-- A run, which keeps the permissions. -/
theorem WP.rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', e, hq⟩ := h
  exact ⟨t, s', e, hq, (Exec.rdwr e).1, (Exec.rdwr e).2.1⟩

/-- `tag`'s address in `W`, after code that misses it. -/
theorem TagSlot.frame {p : VG.Proof.AesGcmSiv.AArch64.Prm} {m m' : Mem} (h : VG.Proof.AesGcmSiv.AArch64.TagSlot p m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p.W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r) : VG.Proof.AesGcmSiv.AArch64.TagSlot p m' := by
  unfold VG.Proof.AesGcmSiv.AArch64.TagSlot at *
  rw [hf.readW (r := ⟨p.W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) hd (by decide), h]

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (v : GcmImpl) (hti : VG.Proof.AesGcmSiv.AArch64.TagInputEq) {s : State} (h : VG.Proof.AesGcmSiv.AArch64.sealPre s) :
    WP isa («seal» v.callees) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  obtain ⟨L, P, hTw, hA⟩ := VG.Proof.AesGcmSiv.AArch64.args_of_seal h
  have hRb := L.rounds_le
  have hn := L.n_lt
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.entry_ok P hA) fun s₁ ⟨E₁, sv₁, f₁, sl₁, rd₁, wr₁⟩ => ?_)
  -- The keys.
  refine WP.seq (WP.mono (WP.rdwr (VG.Proof.AesGcmSiv.AArch64.keys_ok v L E₁)) fun s₂ ⟨Ky, _, kw⟩ => ?_)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.polyval_ok v L Ky.env Ky.hkey Ky.acc) fun s₃ Po => ?_)
  -- The tag.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.tag_ok v L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  -- Counter mode.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.crypt_ok v L Tg.env) fun s₅ Cr => ?_)
  -- The copy of the tag, and `restore`.
  have sl₅ : VG.Proof.AesGcmSiv.AArch64.TagSlot (VG.Proof.AesGcmSiv.AArch64.prmOf s) s₅.mem :=
    (((sl₁.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame (by disj_tac L)).frame
      Cr.frame (by disj_tac L)
  have w₅ : s₅.wr = s.wr := by rw [Cr.wr, Tg.wr, Po.wr, kw, wr₁]
  obtain ⟨s₆, run₆, fT, hT₆, -, ho₆, sp₆, rd₆, wr₆⟩ := VG.Proof.AesGcmSiv.AArch64.tagOut_ok L Cr.env sl₅ (by rw [w₅]; exact hTw)
  have E₆ : VG.Proof.AesGcmSiv.AArch64.Env (VG.Proof.AesGcmSiv.AArch64.prmOf s) s₆ := Cr.env.keep (fun r hr => ho₆ r (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  have sv₆ : SavedAt s₆.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).W s :=
    (((((sv₁.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame (by disj_tac L)).frame
      Cr.frame (by disj_tac L))).frame fT fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (L.t_w' (show 128 + 88 ≤ 3808 by decide)).symm
  refine WP.block_append (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  refine WP.mono (exit_ok (s₀ := s) E₆.x19 E₆.sp E₆.w2560R sv₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).K (VG.Proof.AesGcmSiv.AArch64.prmOf s).R) (Spec.GcmSiv.keyLen (VG.Proof.AesGcmSiv.AArch64.prmOf s).R)
      (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12) (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n) (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).A (VG.Proof.AesGcmSiv.AArch64.prmOf s).al) =
    (bytesAt s'.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n, bytesAt s'.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).T 16)
  rw [hm, hT₆, VG.Proof.AesGcmSiv.AArch64.bytesAt_keep fT (by disj_tac L) (by omega)]
  -- What the pieces read.
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).K (VG.Proof.AesGcmSiv.AArch64.prmOf s).R = Spec.GcmSiv.ctxCiph s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).K (VG.Proof.AesGcmSiv.AArch64.prmOf s).R :=
    VG.Proof.AesGcmSiv.AArch64.ciph_keep f₁ (by disj_tac L) hRb
  have n₁ : bytesAt s₁.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12 = bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12 := VG.Proof.AesGcmSiv.AArch64.bytesAt_keep f₁ (by disj_tac L) (by decide)
  have n₂ : bytesAt s₂.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12 = bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12 := by
    rw [VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  have a₂ : bytesAt s₂.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).A (VG.Proof.AesGcmSiv.AArch64.prmOf s).al = bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).A (VG.Proof.AesGcmSiv.AArch64.prmOf s).al := by
    rw [VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega),
      VG.Proof.AesGcmSiv.AArch64.bytesAt_keep f₁ (by disj_tac L) (by have := L.al_lt; omega)]
  have d₂ : bytesAt s₂.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n = bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n := by
    rw [VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Ky.frame (by disj_tac L) (by omega), VG.Proof.AesGcmSiv.AArch64.bytesAt_keep f₁ (by disj_tac L) (by omega)]
  have d₄ : bytesAt s₄.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n = bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n := by
    rw [VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Tg.frame (by disj_tac L) (by omega), VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Po.frame (by disj_tac L) (by omega), d₂]
  have key₃ : Spec.GcmSiv.ctxCiph s₃.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 240) (VG.Proof.AesGcmSiv.AArch64.prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 240) (VG.Proof.AesGcmSiv.AArch64.prmOf s).R :=
    VG.Proof.AesGcmSiv.AArch64.ciph_keep Po.frame (by disj_tac L) hRb
  have key₄ : Spec.GcmSiv.ctxCiph s₄.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 240) (VG.Proof.AesGcmSiv.AArch64.prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 240) (VG.Proof.AesGcmSiv.AArch64.prmOf s).R := by
    rw [VG.Proof.AesGcmSiv.AArch64.ciph_keep Tg.frame (by disj_tac L) hRb, key₃]
  have t₅ : bytesAt s₅.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s₄.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 0) 16 :=
    VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  rw [L.w0] at t₅
  have tg := Tg.out
  rw [L.w0] at tg
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have po := Po.out
  rw [n₂, a₂, d₂] at po
  rw [Cr.data, t₅, d₄, key₄, ci, tg, key₃, ci, po, ← au]
  unfold Spec.GcmSiv.encryptWith
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).K (VG.Proof.AesGcmSiv.AArch64.prmOf s).R)
    (Spec.GcmSiv.keyLen (VG.Proof.AesGcmSiv.AArch64.prmOf s).R) (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

end VG.Proof.AesGcmSiv.AArch64

/-!
## `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the copy of the
received tag to `W`, the keys, counter mode on the data from it, POLYVAL of
the result and the tag input, its tag at `W + 224`, the comparison, the mask
and the restore compute `decryptWith` (RFC 8452 §5) of the arguments (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.AArch64 (GcmImpl SavedAt savedR exit_ok Others)

theorem decrypt_eq (hti : VG.Proof.AesGcmSiv.AArch64.TagInputEq) (ciph : Spec.GcmSiv.Cipher) (kl : Nat) (nonce ct aad tag : List Byte) :
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

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (v : GcmImpl) (hti : VG.Proof.AesGcmSiv.AArch64.TagInputEq) {s : State} (h : VG.Proof.AesGcmSiv.AArch64.openPre s) :
    WP isa («open» v.callees) s fun s' => GprAbi s s' ∧ openAArch64.post s s' := by
  obtain ⟨L, P, hA⟩ := VG.Proof.AesGcmSiv.AArch64.args_of_open h
  have hRb := L.rounds_le
  have hn := L.n_lt
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.entry_ok P hA) fun s₀ ⟨E₀, sv₀, f₀, sl₀, _, _⟩ => ?_)
  -- The received tag, copied to `W`.
  obtain ⟨s₁, run₁, fR, hR₁, -, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.AArch64.recv_ok L E₀ sl₀
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesGcmSiv.AArch64.Env (VG.Proof.AesGcmSiv.AArch64.prmOf s) s₁ := E₀.keep (fun r hr => ho₁ r (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have fR' : Frame [⟨(VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 0, 16⟩] s₀.mem s₁.mem := by rw [L.w0]; exact fR
  have sv₁ : SavedAt s₁.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).W s := sv₀.frame fR' (by disj_tac L)
  have f₁ : Frame [VG.Proof.AesGcmSiv.AArch64.entryR (VG.Proof.AesGcmSiv.AArch64.prmOf s).W, ⟨(VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 0, 16⟩] s.mem s₁.mem :=
    (f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨(VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 0, 16⟩, by simp, fun _ h => h⟩)
  have hT₁ : bytesAt s₁.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).W 16 = bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).T 16 := by
    rw [hR₁, VG.Proof.AesGcmSiv.AArch64.bytesAt_keep f₀ (by disj_tac L) (by decide)]
  -- The keys.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.keys_ok v L E₁) fun s₂ Ky => ?_)
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.crypt_ok v L Ky.env) fun s₃ Cr => ?_)
  have a₃ : bytesAt s₃.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 16) 16 :=
    VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  have hG₃ : Spec.Gcm.blockAt s₃.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 64) =
      GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₃.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 16) 16)) := by
    rw [Proof.AesGcm.AArch64.blockAt_frame Cr.frame (by disj_tac L), Ky.hkey, a₃]
  have hY₃ : Spec.Gcm.blockAt s₃.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 80) = 0 := by
    rw [Proof.AesGcm.AArch64.blockAt_frame Cr.frame (by disj_tac L), Ky.acc]
  -- POLYVAL of the plaintext and the tag input.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.polyval_ok v L Cr.env hG₃ hY₃) fun s₄ Po => ?_)
  -- Its tag at `W + 224`.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.tag_ok v L Po.env (o := 224) (by decide)) fun s₅ Tg => ?_)
  -- The comparison.
  obtain ⟨s₆, run₆, x27₆, ho₆, hm₆, sp₆, rd₆, wr₆⟩ := VG.Proof.AesGcmSiv.AArch64.cmp_ok Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : VG.Proof.AesGcmSiv.AArch64.Env (VG.Proof.AesGcmSiv.AArch64.prmOf s) s₆ := Tg.env.keep (fun r hr => ho₆ r (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  -- The mask.
  refine WP.seq (WP.mono (VG.Proof.AesGcmSiv.AArch64.mask_ok L E₆ x27₆) fun s₇ Mk => ?_)
  -- `ok` and the restore.
  refine WP.block_append (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  have sv₇ : SavedAt s₇.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).W s := by
    have := ((((sv₁.frame Ky.frame (by disj_tac L)).frame Cr.frame (by disj_tac L)).frame Po.frame
      (by disj_tac L)).frame Tg.frame (by disj_tac L))
    rw [← hm₆] at this
    exact this.frame Mk.frame (by disj_tac L)
  refine WP.mono (exit_ok (s₀ := s) (Mk.env.write (by decide) _).x19 (Mk.env.write (by decide) _).sp
    (Mk.env.write (by decide) _).w2560R (by simp only [mem_write]; exact sv₇)) fun s' ⟨ga, hm, hx0, _⟩ => ⟨ga, ?_⟩
  -- What the pieces read.
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).K (VG.Proof.AesGcmSiv.AArch64.prmOf s).R = Spec.GcmSiv.ctxCiph s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).K (VG.Proof.AesGcmSiv.AArch64.prmOf s).R :=
    VG.Proof.AesGcmSiv.AArch64.ciph_keep f₁ (by disj_tac L) hRb
  have n₁ : bytesAt s₁.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12 = bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12 := VG.Proof.AesGcmSiv.AArch64.bytesAt_keep f₁ (by disj_tac L) (by decide)
  have n₃ : bytesAt s₃.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12 = bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12 := by
    rw [VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Cr.frame (by disj_tac L) (by decide), VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  have a₃' : bytesAt s₃.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).A (VG.Proof.AesGcmSiv.AArch64.prmOf s).al = bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).A (VG.Proof.AesGcmSiv.AArch64.prmOf s).al := by
    rw [VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Cr.frame (by disj_tac L) (by have := L.al_lt; omega),
      VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega),
      VG.Proof.AesGcmSiv.AArch64.bytesAt_keep f₁ (by disj_tac L) (by have := L.al_lt; omega)]
  have d₂ : bytesAt s₂.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n = bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n := by
    rw [VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Ky.frame (by disj_tac L) (by omega), VG.Proof.AesGcmSiv.AArch64.bytesAt_keep f₁ (by disj_tac L) (by omega)]
  have tag₂ : bytesAt s₂.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 0) 16 = bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).T 16 := by
    rw [VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Ky.frame (by disj_tac L) (by decide), L.w0, hT₁]
  have tag₅ : bytesAt s₅.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 0) 16 = bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).T 16 := by
    rw [VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Tg.frame (by disj_tac L) (by decide), VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Po.frame (by disj_tac L) (by decide),
      VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Cr.frame (by disj_tac L) (by decide), tag₂]
  rw [L.w0] at tag₂ tag₅
  have ci₄ : Spec.GcmSiv.ctxCiph s₄.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 240) (VG.Proof.AesGcmSiv.AArch64.prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf s).W + BitVec.ofNat 64 240) (VG.Proof.AesGcmSiv.AArch64.prmOf s).R := by
    rw [VG.Proof.AesGcmSiv.AArch64.ciph_keep Po.frame (by disj_tac L) hRb, VG.Proof.AesGcmSiv.AArch64.ciph_cryR L Cr.frame]
  have d₆ : bytesAt s₆.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n = bytesAt s₃.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n := by
    rw [hm₆, VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Tg.frame (by disj_tac L) (by omega), VG.Proof.AesGcmSiv.AArch64.bytesAt_keep Po.frame (by disj_tac L) (by omega)]
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
  have ax : s'.gpr .x0 = s₆.gpr .x27 := by
    rw [hx0]; simp only [gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero]; exact Mk.x27
  rw [x27₆, tg, tag₅] at ax
  show VG.Proof.AesGcmSiv.AArch64.openPost (VG.Proof.AesGcmSiv.AArch64.openResult s) s' (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n
  have hdec : VG.Proof.AesGcmSiv.AArch64.openResult s =
      let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).K (VG.Proof.AesGcmSiv.AArch64.prmOf s).R)
        (Spec.GcmSiv.keyLen (VG.Proof.AesGcmSiv.AArch64.prmOf s).R) (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12)
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12)
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).T 16))
            (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n)) (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).A (VG.Proof.AesGcmSiv.AArch64.prmOf s).al)) =
          bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).T 16 then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).T 16))
          (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n))
      else none := VG.Proof.AesGcmSiv.AArch64.decrypt_eq hti _ _ _ _ _ _
  simp only at hdec
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).K (VG.Proof.AesGcmSiv.AArch64.prmOf s).R)
    (Spec.GcmSiv.keyLen (VG.Proof.AesGcmSiv.AArch64.prmOf s).R) (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12) = dk at md ax hdec
  rw [hdec]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).T 16))
        (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n)) (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).A (VG.Proof.AesGcmSiv.AArch64.prmOf s).al)) =
      bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).T 16
  · refine VG.Proof.AesGcmSiv.AArch64.openPost_some (ite_eq_left_of_eq_true _ _ (eq_true hc)) ?_ ?_
    · rw [ax]; simp only [hc, ↓reduceIte]; rfl
    · rw [hm]; simp only [mem_write]; rw [md]; simp only [hc, ↓reduceIte]
  · have hc' : ¬bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).T 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).N 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).T 16))
          (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).D (VG.Proof.AesGcmSiv.AArch64.prmOf s).n)) (bytesAt s.mem (VG.Proof.AesGcmSiv.AArch64.prmOf s).A (VG.Proof.AesGcmSiv.AArch64.prmOf s).al)) := Ne.symm hc
    refine VG.Proof.AesGcmSiv.AArch64.openPost_none (ite_eq_right_of_eq_false _ _ (eq_false hc)) ?_ ?_
    · rw [ax]; simp only [hc', ↓reduceIte]; rfl
    · rw [hm]; simp only [mem_write]; rw [md]; simp only [hc', ↓reduceIte]

end VG.Proof.AesGcmSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.AArch64.PolyvalCT`. -/
section

/-!
# AES-GCM-SIV on AArch64: relating two runs, the keys and POLYVAL

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (`Eq2`) piece by piece, as AES-GCM's do
(`Proof.AesGcm.AArch64.rel_seq`): the code between calls by the taint
analysis, from the registers that hold the public arguments in both runs
(`Env`, `rel_env`) and those the pieces pin to the same values; each call
by its callee's proof; and the next piece from the states the correctness
proofs describe.
-/

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_taint)

theorem Env.agree {p : VG.Proof.AesGcmSiv.AArch64.Prm} {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.AArch64.Env p τ₂) :
    ∀ r ∈ VG.Proof.AesGcmSiv.AArch64.envRegs, τ₁.gpr r = τ₂.gpr r := by
  intro r hr
  simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [E₁.x19, E₂.x19]
  · rw [E₁.x20, E₂.x20]
  · rw [E₁.x21, E₂.x21]
  · rw [E₁.x22, E₂.x22]
  · rw [E₁.x23, E₂.x23]
  · rw [E₁.x24, E₂.x24]
  · rw [E₁.x25, E₂.x25]
  · rw [E₁.x26, E₂.x26]

theorem Env.sp_eq {p : VG.Proof.AesGcmSiv.AArch64.Prm} {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.AArch64.Env p τ₂) : τ₁.sp = τ₂.sp := by
  rw [E₁.sp, E₂.sp]

/-- The registers holding the public arguments, and `rs`. -/
abbrev pubRegs (rs : List Reg) : List Reg := VG.Proof.AesGcmSiv.AArch64.envRegs ++ rs

/-- Code the taint analysis checks, from the registers holding the public
arguments and the registers `rs` the two runs agree on. -/
theorem rel_env {c : Prog isa} {p : VG.Proof.AesGcmSiv.AArch64.Prm} {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.AArch64.Env p τ₂) (rs : List Reg)
    (hr : ∀ r ∈ rs, τ₁.gpr r = τ₂.gpr r)
    (hc : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.envRegs ++ rs)) c h).isSome = true) :
    RelCT isa (Eq2 τ₁ τ₂) c TT :=
  rel_taint (VG.Proof.AesGcmSiv.AArch64.envRegs ++ rs) (E₁.sp_eq E₂) (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) hc

/-- Then, towards any relation of the final states. -/
theorem rel_seqQ {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ Q) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) Q := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- The last piece, with what correctness says of each run's final state. -/
theorem rel_wpQ {c : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h : RelCT isa (Eq2 σ₁ σ₂) c TT) (w₁ : WP isa c σ₁ F₁) (w₂ : WP isa c σ₂ F₂)
    (hq : ∀ a b, F₁ a → F₂ b → Q a b) : RelCT isa (Eq2 σ₁ σ₂) c Q :=
  (h.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono
    (fun _ _ h => h) fun a b h => hq a b h.2.1 h.2.2

/-- `a; (b; (c; (d; e)))`, related as `(a; (b; (c; d))); e`. -/
theorem RelCT.assoc4 {P Q : State → State → Prop} {a b c d e : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c d))) e) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d e)))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
  | seq d₁ e₁' =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
  | seq d₂ e₂' =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) e₁')
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) e₂')
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- A loop step in two runs: the condition agrees, and the runs are related
anew while it loops. -/
theorem rel_loop {body : Prog isa} {c : Cond} (I : Nat → State → State → Prop)
    (hstep : ∀ n σ₁ σ₂, I n σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) body fun s₁ s₂ => isa.eval c s₁ = isa.eval c s₂ ∧
      (isa.eval c s₁ = some true → ∃ m < n, I m s₁ s₂))
    (n : Nat) {σ₁ σ₂ : State} (h : I n σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (.loop body c) TT := by
  refine (RelCT.loop (Q := TT) I (fun n => ?_) n).mono (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact h)
    fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hc, hi⟩ := hstep n s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂
  exact ⟨ht, hc, fun _ => trivial, hi⟩

end VG.Proof.AesGcmSiv.AArch64

/-!
## The keys are constant time

Untrusted: everything here is checked by Lean. Both runs derive the same
number of blocks (`rounds / 2 − 1`, from `x22`); the code around the calls
passes the taint analysis, and each call has the same arguments in both
runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ctr rel_key GcmImpl CtrCall ctr_call KeyCall key_call eval_nonzero
  Others)

/-- A run of `derive` before block `i`. -/
structure DC (p : VG.Proof.AesGcmSiv.AArch64.Prm) (i : Nat) (t : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t
  x27 : t.gpr .x27 = BitVec.ofNat 64 i

theorem derA_wp {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {i : Nat} {t : State} (h : VG.Proof.AesGcmSiv.AArch64.DC p i t) :
    WP isa (.block deriveBlock) t fun t₁ =>
      CtrCall t₁ p.K (p.W + BitVec.ofNat 64 112) (p.W + BitVec.ofNat 64 224) (p.W + BitVec.ofNat 64 1760) p.R 1 ∧
        VG.Proof.AesGcmSiv.AArch64.DC p i t₁ := by
  obtain ⟨t₁, run₁, -, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.AArch64.derArgs_ok h.env h.x27
  have E₁ : VG.Proof.AesGcmSiv.AArch64.Env p t₁ := h.env.keep (fun r hr => ho₁ r (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  exact WP.of_runBlock ⟨t₁, run₁, VG.Proof.AesGcmSiv.AArch64.derCall L E₁ x0 x1 x2 x3 x4 x5, E₁, by rw [ho₁ _ (by decide), h.x27]⟩

theorem derC_wp (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} {i : Nat} {t : State}
    (h : CtrCall t p.K (p.W + BitVec.ofNat 64 112) (p.W + BitVec.ofNat 64 224) (p.W + BitVec.ofNat 64 1760) p.R 1 ∧
      VG.Proof.AesGcmSiv.AArch64.DC p i t) :
    WP isa (callCtr v.callees) t (VG.Proof.AesGcmSiv.AArch64.DC p i) :=
  WP.mono (ctr_call v.ctr h.1) fun _ P =>
    ⟨h.2.env.of_saved P.saved P.sp P.rd P.wr, by rw [P.saved _ (by decide) (by decide), h.2.x27]⟩

theorem derP_wp {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {i : Nat} (hi : i < p.R / 2 - 1) {t : State} (h : VG.Proof.AesGcmSiv.AArch64.DC p i t) :
    WP isa (.block derivePost) t fun t' =>
      VG.Proof.AesGcmSiv.AArch64.DC p (i + 1) t' ∧ t'.gpr .x10 = BitVec.ofNat 64 (p.R / 2 - 1 - (i + 1)) := by
  obtain ⟨t', run', -, x27', x10', ho', sp', rd', wr'⟩ := VG.Proof.AesGcmSiv.AArch64.derPost_ok L h.env hi h.x27
  exact WP.of_runBlock ⟨t', run', ⟨h.env.keep (fun r hr => ho' r (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp' rd' wr', x27'⟩, x10'⟩

theorem derA_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [.x27])) (.block deriveBlock) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem derP_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [.x27])) (.block derivePost) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem der0_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [])) (.block [Impl.AesGcm.AArch64.imm .x27 0]) h).isSome =
    true := ⟨_, by taint_decide⟩

/-- `derive`, in two runs with the same public arguments. -/
theorem derive_rel (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p σ₁) (E₂ : VG.Proof.AesGcmSiv.AArch64.Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (derive v.callees) TT := by
  have hR := L.rounds
  have w0 : ∀ {σ : State}, VG.Proof.AesGcmSiv.AArch64.Env p σ → WP isa (.block [Impl.AesGcm.AArch64.imm .x27 0]) σ (VG.Proof.AesGcmSiv.AArch64.DC p 0) := fun E =>
    WP.run ⟨_, by grun [], rfl⟩ fun t ht => by
      subst ht
      exact ⟨E.keep (fun r hr => by
          simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
        by simp [gpr_write]⟩
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.rel_env E₁ E₂ [] (by simp) VG.Proof.AesGcmSiv.AArch64.der0_check) (w0 E₁) (w0 E₂) fun τ₁ τ₂ D₁ D₂ => ?_
  refine VG.Proof.AesGcmSiv.AArch64.rel_loop (fun m t₁ t₂ => ∃ i, m = (p.R / 2 - 1) - i ∧ i < p.R / 2 - 1 ∧ VG.Proof.AesGcmSiv.AArch64.DC p i t₁ ∧ VG.Proof.AesGcmSiv.AArch64.DC p i t₂)
    (fun m t₁ t₂ ⟨i, hm, hi, I₁, I₂⟩ => ?_) ((p.R / 2 - 1) - 0) ⟨0, rfl, by omega, D₁, D₂⟩
  refine VG.Proof.AesGcmSiv.AArch64.rel_seqQ (VG.Proof.AesGcmSiv.AArch64.rel_env I₁.env I₂.env [.x27] (by simp [I₁.x27, I₂.x27]) VG.Proof.AesGcmSiv.AArch64.derA_check) (VG.Proof.AesGcmSiv.AArch64.derA_wp L I₁)
    (VG.Proof.AesGcmSiv.AArch64.derA_wp L I₂) fun u₁ u₂ A₁ A₂ => ?_
  refine VG.Proof.AesGcmSiv.AArch64.rel_seqQ (rel_ctr v.ctr A₁.1 A₂.1 (A₁.2.env.sp_eq A₂.2.env)) (VG.Proof.AesGcmSiv.AArch64.derC_wp v A₁) (VG.Proof.AesGcmSiv.AArch64.derC_wp v A₂)
    fun a b J₁ J₂ => ?_
  refine VG.Proof.AesGcmSiv.AArch64.rel_wpQ (VG.Proof.AesGcmSiv.AArch64.rel_env J₁.env J₂.env [.x27] (by simp [J₁.x27, J₂.x27]) VG.Proof.AesGcmSiv.AArch64.derP_check) (VG.Proof.AesGcmSiv.AArch64.derP_wp L hi J₁)
    (VG.Proof.AesGcmSiv.AArch64.derP_wp L hi J₂) fun a' b' ⟨K₁, x10₁⟩ ⟨K₂, x10₂⟩ => ?_
  have ev₁ := eval_nonzero x10₁ (by omega)
  have ev₂ := eval_nonzero x10₂ (by omega)
  refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
  rw [ev₁] at hc
  have he : i + 1 ≠ p.R / 2 - 1 := by simp at hc; omega
  exact ⟨(p.R / 2 - 1) - (i + 1), by omega, i + 1, rfl, by omega, K₁, K₂⟩

theorem expA_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [])) (.block expandArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem hkey_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [])) (.block hkey) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `keys`, in two runs with the same public arguments. -/
theorem keys_rel (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p σ₁) (E₂ : VG.Proof.AesGcmSiv.AArch64.Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (VG.Impl.AesGcmSiv.AArch64.keys v.callees) TT := by
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.derive_rel v L E₁ E₂) (VG.Proof.AesGcmSiv.AArch64.derive_ok v L E₁) (VG.Proof.AesGcmSiv.AArch64.derive_ok v L E₂) fun τ₁ τ₂ D₁ D₂ => ?_
  have wA : ∀ {τ : State}, VG.Proof.AesGcmSiv.AArch64.Env p τ → WP isa (.block expandArgs) τ fun t₁ =>
      KeyCall t₁ (p.W + BitVec.ofNat 64 32) (p.W + BitVec.ofNat 64 240) (p.W + BitVec.ofNat 64 1760)
        (Spec.GcmSiv.keyLen p.R) ∧ VG.Proof.AesGcmSiv.AArch64.Env p t₁ := fun E => by
    obtain ⟨t₁, run₁, kc, E', -⟩ := VG.Proof.AesGcmSiv.AArch64.expArgs_ok L E
    exact WP.of_runBlock ⟨t₁, run₁, kc, E'⟩
  refine rel_seq (c₁ := expand v.callees) ?_ (WP.mono (VG.Proof.AesGcmSiv.AArch64.expand_ok v L D₁.env) fun _ X => X.env)
    (WP.mono (VG.Proof.AesGcmSiv.AArch64.expand_ok v L D₂.env) fun _ X => X.env) fun u₁ u₂ F₁ F₂ =>
      VG.Proof.AesGcmSiv.AArch64.rel_env F₁ F₂ [] (by simp) VG.Proof.AesGcmSiv.AArch64.hkey_check
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.rel_env D₁.env D₂.env [] (by simp) VG.Proof.AesGcmSiv.AArch64.expA_check) (wA D₁.env) (wA D₂.env)
    fun a b ⟨k₁, A₁⟩ ⟨k₂, A₂⟩ => rel_key v.key k₁ k₂ (A₁.sp_eq A₂)

end VG.Proof.AesGcmSiv.AArch64

/-!
## POLYVAL is constant time

Untrusted: everything here is checked by Lean. Both runs absorb the same
chunks of blocks: their number depends only on the lengths, which are
public; the code around each call of `vg_ghash` passes the taint analysis,
and each call has the same arguments in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_gh rel_ite GcmImpl GhCall gh_call eval_zero eval_nonzero Others)

theorem chunkPre_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [.x27, .x28])) chunkPre h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chunkEnd_check :
    ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [.x28])) (.block [.lsr .x .x9 .x28 4]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A chunk, in two runs with the same public arguments, pointer and count. -/
theorem chunk_rel (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.AArch64.Env p τ₂)
    {Q : Addr} {m : Nat} (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ₁ : VG.Proof.AesGcmSiv.AArch64.Src p τ₁ Q (16 * (m / 16)))
    (hQ₂ : VG.Proof.AesGcmSiv.AArch64.Src p τ₂ Q (16 * (m / 16))) (a27 : τ₁.gpr .x27 = Q) (b27 : τ₂.gpr .x27 = Q)
    (a28 : τ₁.gpr .x28 = BitVec.ofNat 64 m) (b28 : τ₂.gpr .x28 = BitVec.ofNat 64 m) :
    RelCT isa (Eq2 τ₁ τ₂) (chunk v.callees) TT := by
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.rel_env E₁ E₂ [.x27, .x28] (by simp [a27, b27, a28, b28]) VG.Proof.AesGcmSiv.AArch64.chunkPre_check)
    (VG.Proof.AesGcmSiv.AArch64.chunkPre_ok L E₁ hm h16 hQ₁ a27 a28) (VG.Proof.AesGcmSiv.AArch64.chunkPre_ok L E₂ hm h16 hQ₂ b27 b28) fun u₁ u₂ P₁ P₂ => ?_
  have wG : ∀ {u : State}, VG.Proof.AesGcmSiv.AArch64.ChunkPre p Q m (min (m / 16) 64) τ₁ u ∨ VG.Proof.AesGcmSiv.AArch64.ChunkPre p Q m (min (m / 16) 64) τ₂ u →
      WP isa (callGh v.callees) u fun w => VG.Proof.AesGcmSiv.AArch64.Env p w ∧ w.gpr .x28 = BitVec.ofNat 64 (m - 16 * min (m / 16) 64) :=
    fun h => by
      rcases h with P | P <;>
      exact WP.mono (gh_call v.gh P.call) fun _ G =>
        ⟨P.env.of_saved G.saved G.sp G.rd G.wr, by rw [G.saved _ (by decide) (by decide), P.x28]⟩
  exact rel_seq (rel_gh v.gh P₁.call P₂.call (P₁.env.sp_eq P₂.env)) (wG (.inl P₁)) (wG (.inr P₂))
    fun w₁ w₂ G₁ G₂ => VG.Proof.AesGcmSiv.AArch64.rel_env G₁.1 G₂.1 [.x28] (by simp [G₁.2, G₂.2]) VG.Proof.AesGcmSiv.AArch64.chunkEnd_check

/-- The chunks, in two runs from `σ₁` and `σ₂` with the same public arguments. -/
theorem chunks_rel (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {σ₁ σ₂ : State} {Q : Addr} {m : Nat} (hm : m < 2 ^ 64)
    (h16 : 16 ≤ m) (hQ₁ : VG.Proof.AesGcmSiv.AArch64.Src p σ₁ Q (16 * (m / 16))) (hQ₂ : VG.Proof.AesGcmSiv.AArch64.Src p σ₂ Q (16 * (m / 16))) {d : Nat}
    (hd : d < m / 16) {τ₁ τ₂ : State} (I₁ : VG.Proof.AesGcmSiv.AArch64.CInv p σ₁ Q m d τ₁) (I₂ : VG.Proof.AesGcmSiv.AArch64.CInv p σ₂ Q m d τ₂) :
    RelCT isa (Eq2 τ₁ τ₂) (.loop (chunk v.callees) (.nonzero .x .x9)) TT := by
  refine VG.Proof.AesGcmSiv.AArch64.rel_loop (fun k t₁ t₂ => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ VG.Proof.AesGcmSiv.AArch64.CInv p σ₁ Q m d t₁ ∧ VG.Proof.AesGcmSiv.AArch64.CInv p σ₂ Q m d t₂)
    (fun k t₁ t₂ ⟨d, hk, hd, J₁, J₂⟩ => ?_) (m / 16 - d) ⟨d, rfl, hd, I₁, I₂⟩
  refine VG.Proof.AesGcmSiv.AArch64.rel_wpQ (VG.Proof.AesGcmSiv.AArch64.chunk_rel v L J₁.abs.env J₂.abs.env (by omega) (by omega) (J₁.src hQ₁ hd) (J₂.src hQ₂ hd)
      J₁.x27 J₂.x27 J₁.x28 J₂.x28)
    (VG.Proof.AesGcmSiv.AArch64.chunk_ok v L J₁.abs.env (by omega) (by omega) (J₁.src hQ₁ hd) J₁.x27 J₁.x28)
    (VG.Proof.AesGcmSiv.AArch64.chunk_ok v L J₂.abs.env (by omega) (by omega) (J₂.src hQ₂ hd) J₂.x27 J₂.x28) fun a b C₁ C₂ => ?_
  obtain ⟨K₁, x9₁⟩ := J₁.step L hm hQ₁ hd C₁
  obtain ⟨K₂, x9₂⟩ := J₂.step L hm hQ₂ hd C₂
  have ev₁ := eval_nonzero x9₁ (by omega)
  have ev₂ := eval_nonzero x9₂ (by omega)
  refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
  rw [ev₁] at hc
  have he : d + min (m / 16 - d) 64 ≠ m / 16 := by simp at hc; omega
  exact ⟨m / 16 - (d + min (m / 16 - d) 64), by omega, d + min (m / 16 - d) 64, rfl, by omega, K₁, K₂⟩

theorem absHead_check :
    ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [.x27, .x28])) (.block [.lsr .x .x9 .x28 4]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem absTailPre_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [.x27, .x28])) absTailPre h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `chunk` on the block at `W + 224`. -/
theorem chunkB_rel (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.AArch64.Env p τ₂)
    (a27 : τ₁.gpr .x27 = p.W + BitVec.ofNat 64 224) (b27 : τ₂.gpr .x27 = p.W + BitVec.ofNat 64 224)
    (a28 : τ₁.gpr .x28 = BitVec.ofNat 64 16) (b28 : τ₂.gpr .x28 = BitVec.ofNat 64 16) :
    RelCT isa (Eq2 τ₁ τ₂) (chunk v.callees) TT :=
  VG.Proof.AesGcmSiv.AArch64.chunk_rel v L E₁ E₂ (m := 16) (by decide) (by decide) (VG.Proof.AesGcmSiv.AArch64.srcB L E₁.perm) (VG.Proof.AesGcmSiv.AArch64.srcB L E₂.perm) a27 b27 a28 b28

/-- `absorb`, in two runs with the same public arguments, pointer and count. -/
theorem absorb_rel (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.AArch64.Env p τ₂)
    {Q : Addr} {m : Nat} (hm : m < 2 ^ 64) (hw : Q.toNat + m ≤ 2 ^ 64) (hd : (⟨Q, m⟩ : Region).Disjoint ⟨p.W, 3808⟩)
    (hc₁ : Covers [⟨Q, m⟩] (τ₁.rd ++ τ₁.wr)) (hc₂ : Covers [⟨Q, m⟩] (τ₂.rd ++ τ₂.wr))
    (a27 : τ₁.gpr .x27 = Q) (b27 : τ₂.gpr .x27 = Q) (a28 : τ₁.gpr .x28 = BitVec.ofNat 64 m)
    (b28 : τ₂.gpr .x28 = BitVec.ofNat 64 m) :
    RelCT isa (Eq2 τ₁ τ₂) (absorb v.callees) TT := by
  have hQ₁ : VG.Proof.AesGcmSiv.AArch64.Src p τ₁ Q m := Src.ofW L hc₁ hm hw hd
  have hQ₂ : VG.Proof.AesGcmSiv.AArch64.Src p τ₂ Q m := Src.ofW L hc₂ hm hw hd
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.rel_env E₁ E₂ [.x27, .x28] (by simp [a27, b27, a28, b28]) VG.Proof.AesGcmSiv.AArch64.absHead_check) (VG.Proof.AesGcmSiv.AArch64.absHead_ok hm a28)
    (VG.Proof.AesGcmSiv.AArch64.absHead_ok hm b28) fun u₁ u₂ ⟨x9₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x9₂, ho₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₁ : VG.Proof.AesGcmSiv.AArch64.Env p u₁ := E₁.keep (fun q hq => ho₁ q (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have F₂ : VG.Proof.AesGcmSiv.AArch64.Env p u₂ := E₂.keep (fun q hq => ho₂ q (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  have u27₁ : u₁.gpr .x27 = Q := by rw [ho₁ _ (by decide), a27]
  have u27₂ : u₂.gpr .x27 = Q := by rw [ho₂ _ (by decide), b27]
  have u28₁ : u₁.gpr .x28 = BitVec.ofNat 64 m := by rw [ho₁ _ (by decide), a28]
  have u28₂ : u₂.gpr .x28 = BitVec.ofNat 64 m := by rw [ho₂ _ (by decide), b28]
  have hQ₁' := hQ₁.of_eq rd₁ wr₁
  have hQ₂' := hQ₂.of_eq rd₂ wr₂
  -- The whole blocks.
  refine rel_seq (rel_ite (eval_zero x9₁ (by omega)) (eval_zero x9₂ (by omega))
      (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun hf => ?_))
    (VG.Proof.AesGcmSiv.AArch64.absMid_ok v L F₁ hm hQ₁' u27₁ u28₁ x9₁) (VG.Proof.AesGcmSiv.AArch64.absMid_ok v L F₂ hm hQ₂' u27₂ u28₂ x9₂)
    fun w₁ w₂ ⟨A₁, x27₁, x28₁⟩ ⟨A₂, x27₂, x28₂⟩ => ?_
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact VG.Proof.AesGcmSiv.AArch64.chunks_rel v L hm (by omega) (hQ₁'.take (by omega)) (hQ₂'.take (by omega)) (d := 0) (by omega)
      (CInv.zero F₁ u27₁ u28₁) (CInv.zero F₂ u27₂ u28₂)
  -- The last bytes.
  refine rel_ite (eval_zero x28₁ (by omega)) (eval_zero x28₂ (by omega))
    (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun hf => ?_)
  have h0 : m % 16 ≠ 0 := by simpa using hf
  have dT : (⟨Q + BitVec.ofNat 64 (16 * (m / 16)), m % 16⟩ : Region).Disjoint ⟨p.W, 3808⟩ :=
    hd.sub_left (Offset.sub_base Q (by omega))
  have hs₁ := (hQ₁'.slice (a := 16 * (m / 16)) (k := m % 16) (by omega)).of_eq A₁.rd A₁.wr
  have hs₂ := (hQ₂'.slice (a := 16 * (m / 16)) (k := m % 16) (by omega)).of_eq A₂.rd A₂.wr
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.rel_env A₁.env A₂.env [.x27, .x28] (by simp [x27₁, x27₂, x28₁, x28₂]) VG.Proof.AesGcmSiv.AArch64.absTailPre_check)
    (VG.Proof.AesGcmSiv.AArch64.absTailPre_ok L A₁.env (by omega) (by omega) hs₁.rd dT x27₁ x28₁)
    (VG.Proof.AesGcmSiv.AArch64.absTailPre_ok L A₂.env (by omega) (by omega) hs₂.rd dT x27₂ x28₂) fun z₁ z₂ T₁ T₂ => ?_
  exact VG.Proof.AesGcmSiv.AArch64.chunkB_rel v L T₁.env T₂.env T₁.x27 T₂.x27 T₁.x28 T₂.x28

theorem lensBlock_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [])) (.block lensBlock) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagIn_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [])) (.block tagIn) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem polyA_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs []))
    (.block [Impl.AesGcm.AArch64.mov .x27 .x23, Impl.AesGcm.AArch64.mov .x28 .x24]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem polyD_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs []))
    (.block [Impl.AesGcm.AArch64.mov .x27 .x25, Impl.AesGcm.AArch64.mov .x28 .x26]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- Two registers set to the arguments in `x19`–`x26`. -/
theorem mov2_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} {t : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p t) {a b : Reg} (_ha : a ∈ VG.Proof.AesGcmSiv.AArch64.envRegs) (hb : b ∈ VG.Proof.AesGcmSiv.AArch64.envRegs) :
    WP isa (.block [Impl.AesGcm.AArch64.mov .x27 a, Impl.AesGcm.AArch64.mov .x28 b]) t fun t' =>
      VG.Proof.AesGcmSiv.AArch64.Env p t' ∧ t'.gpr .x27 = t.gpr a ∧ t'.gpr .x28 = t.gpr b ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine WP.of_runBlock ⟨_, by grun [], ?_⟩
  have hb' : b ≠ .x27 := fun e => by subst e; revert hb; decide
  exact ⟨(E.write (by decide) _).write (by decide) _, by simp [gpr_write], by simp [gpr_write, hb'], rfl, rfl, rfl⟩

/-- `polyval`, in two runs with the same public arguments. -/
theorem polyval_rel (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p σ₁) (E₂ : VG.Proof.AesGcmSiv.AArch64.Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (polyval v.callees) TT := by
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.rel_env E₁ E₂ [] (by simp) VG.Proof.AesGcmSiv.AArch64.polyA_check) (VG.Proof.AesGcmSiv.AArch64.mov2_ok E₁ (a := .x23) (b := .x24) (by decide) (by decide))
    (VG.Proof.AesGcmSiv.AArch64.mov2_ok E₂ (a := .x23) (b := .x24) (by decide) (by decide)) fun a₁ a₂ ⟨G₁, a27₁, a28₁, _, rd₁, wr₁⟩
      ⟨G₂, a27₂, a28₂, _, rd₂, wr₂⟩ => ?_
  rw [E₁.x23] at a27₁; rw [E₁.x24] at a28₁; rw [E₂.x23] at a27₂; rw [E₂.x24] at a28₂
  have hc₁ : Covers [⟨p.A, p.al⟩] (a₁.rd ++ a₁.wr) := G₁.perm.aad
  have hc₂ : Covers [⟨p.A, p.al⟩] (a₂.rd ++ a₂.wr) := G₂.perm.aad
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.absorb_rel v L G₁ G₂ L.al_lt L.aw L.a_w hc₁ hc₂ a27₁ a27₂ a28₁ a28₂)
    (VG.Proof.AesGcmSiv.AArch64.absorb_ok v L G₁ hc₁ L.al_lt L.aw L.a_w a27₁ a28₁) (VG.Proof.AesGcmSiv.AArch64.absorb_ok v L G₂ hc₂ L.al_lt L.aw L.a_w a27₂ a28₂)
    fun b₁ b₂ B₁ B₂ => ?_
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.rel_env B₁.env B₂.env [] (by simp) VG.Proof.AesGcmSiv.AArch64.polyD_check)
    (VG.Proof.AesGcmSiv.AArch64.mov2_ok B₁.env (a := .x25) (b := .x26) (by decide) (by decide))
    (VG.Proof.AesGcmSiv.AArch64.mov2_ok B₂.env (a := .x25) (b := .x26) (by decide) (by decide)) fun c₁ c₂ ⟨H₁, c27₁, c28₁, _, _, _⟩
      ⟨H₂, c27₂, c28₂, _, _, _⟩ => ?_
  rw [B₁.env.x25] at c27₁; rw [B₁.env.x26] at c28₁; rw [B₂.env.x25] at c27₂; rw [B₂.env.x26] at c28₂
  have dc₁ : Covers [⟨p.D, p.n⟩] (c₁.rd ++ c₁.wr) := Proof.AesGcm.AArch64.covers_left H₁.perm.d
  have dc₂ : Covers [⟨p.D, p.n⟩] (c₂.rd ++ c₂.wr) := Proof.AesGcm.AArch64.covers_left H₂.perm.d
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.absorb_rel v L H₁ H₂ L.n_lt L.dw L.d_w dc₁ dc₂ c27₁ c27₂ c28₁ c28₂)
    (VG.Proof.AesGcmSiv.AArch64.absorb_ok v L H₁ dc₁ L.n_lt L.dw L.d_w c27₁ c28₁) (VG.Proof.AesGcmSiv.AArch64.absorb_ok v L H₂ dc₂ L.n_lt L.dw L.d_w c27₂ c28₂)
    fun d₁ d₂ D₁ D₂ => ?_
  refine rel_seq (c₁ := lens v.callees) ?_ (VG.Proof.AesGcmSiv.AArch64.lens_ok v L D₁.env) (VG.Proof.AesGcmSiv.AArch64.lens_ok v L D₂.env) fun e₁ e₂ F₁ F₂ =>
    VG.Proof.AesGcmSiv.AArch64.rel_env F₁.env F₂.env [] (by simp) VG.Proof.AesGcmSiv.AArch64.tagIn_check
  have wL : ∀ {d : State}, VG.Proof.AesGcmSiv.AArch64.Env p d → WP isa (.block lensBlock) d fun t =>
      VG.Proof.AesGcmSiv.AArch64.Env p t ∧ t.gpr .x27 = p.W + BitVec.ofNat 64 224 ∧ t.gpr .x28 = BitVec.ofNat 64 16 := fun E => by
    have w₀ := E.perm.wW (show 224 + 8 ≤ 3808 by decide)
    have w₈ := E.perm.wW (show 232 + 8 ≤ 3808 by decide)
    refine WP.run ⟨_, by simp only [lensBlock]; grun [E.x19, E.x24, E.x26, w₀, w₈], rfl⟩ fun t ht => ?_
    subst ht
    refine ⟨E.keep (fun q hq => by
        simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
      by simp [gpr_write, E.x19], by simp [gpr_write, VG.Proof.AesGcmSiv.AArch64.movz_lit (show 16 < 2 ^ 16 by decide)]⟩
  exact rel_seq (VG.Proof.AesGcmSiv.AArch64.rel_env D₁.env D₂.env [] (by simp) VG.Proof.AesGcmSiv.AArch64.lensBlock_check) (wL D₁.env) (wL D₂.env)
    fun f₁ f₂ ⟨K₁, x27₁, x28₁⟩ ⟨K₂, x27₂, x28₂⟩ => VG.Proof.AesGcmSiv.AArch64.chunkB_rel v L K₁ K₂ x27₁ x27₂ x28₁ x28₂

end VG.Proof.AesGcmSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.AArch64.FnCT`. -/
section

/-!
# AES-GCM-SIV on AArch64: the tag, counter mode and the functions are constant time

Untrusted: everything here is checked by Lean. Each call of `vg_aes_ctr32`
has the same arguments in both runs, which encrypt the same number of
blocks; the code around the calls, the comparison and the mask pass the
taint analysis (`open` never branches on whether the tag is right). The
loads of `W` from the stack and of `tag`'s address from `W` give the same
address in both runs (by correctness), and the taint analysis checks the
code after them (`entry_rel`, `rel_ldrT`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ctr rel_ite rel_taint ct_of GcmImpl CtrCall ctr_call eval_zero in_off
  RelCT.block_split
  eval_nonzero Others add_ofNat_assoc ofNat_sub lsr_ofNat)

/-! ## The tag -/

theorem tagA_check {o : Nat} (ho : o = 0 ∨ o = 224) : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs []))
    (.block (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++ [Impl.AesGcm.AArch64.ptr .x3 .x19 o])) h).isSome = true := by
  rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `tag o`, in two runs with the same public arguments. -/
theorem tag_rel (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.AArch64.Env p τ₂) {o : Nat}
    (ho : o = 0 ∨ o = 224) : RelCT isa (Eq2 τ₁ τ₂) (tag v.callees o) TT := by
  have w : ∀ {τ : State}, VG.Proof.AesGcmSiv.AArch64.Env p τ → WP isa (.block (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++
      [Impl.AesGcm.AArch64.ptr .x3 .x19 o])) τ fun t₁ => CtrCall t₁ (p.W + BitVec.ofNat 64 240)
        (p.W + BitVec.ofNat 64 112) (p.W + BitVec.ofNat 64 o) (p.W + BitVec.ofNat 64 1760) p.R 1 ∧ VG.Proof.AesGcmSiv.AArch64.Env p t₁ :=
    fun E => by
      obtain ⟨t₁, run₁, -, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.AArch64.tagArgs_ok E ho
      have E' : VG.Proof.AesGcmSiv.AArch64.Env p t₁ := E.keep (fun r hr => ho₁ r (by
        simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
      exact WP.of_runBlock ⟨t₁, run₁, VG.Proof.AesGcmSiv.AArch64.tagCall L E' ho x0 x1 x2 x3 x4 x5, E'⟩
  exact rel_seq (VG.Proof.AesGcmSiv.AArch64.rel_env E₁ E₂ [] (by simp) (VG.Proof.AesGcmSiv.AArch64.tagA_check ho)) (w E₁) (w E₂)
    fun a b A₁ A₂ => rel_ctr v.ctr A₁.1 A₂.1 (A₁.2.sp_eq A₂.2)

/-! ## Counter mode -/

theorem blkA_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [.x27, .x28]))
    (.block (copy16 cbO ccO ++ ctrArgs ++ [Impl.AesGcm.AArch64.mov .x3 .x27])) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem blkP_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [.x27, .x28]))
    (.block [.ldr .w .x9 .x19 cbO, .addImm .w .x9 .x9 1, .str .w .x9 .x19 cbO, Impl.AesGcm.AArch64.ptr .x27 .x27 16,
      .subImm .x .x28 .x28 16, .lsr .x .x9 .x28 4]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A block of counter mode, in two runs with the same public arguments,
pointer and count. -/
theorem cryptBlock_rel (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p τ₁) (E₂ : VG.Proof.AesGcmSiv.AArch64.Env p τ₂)
    {j : Nat} (hj : 16 * (j + 1) ≤ p.n) (a27 : τ₁.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j))
    (b27 : τ₂.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j)) (a28 : τ₁.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j))
    (b28 : τ₂.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j)) :
    RelCT isa (Eq2 τ₁ τ₂) (cryptBlock v.callees) TT := by
  have w : ∀ {τ : State}, VG.Proof.AesGcmSiv.AArch64.Env p τ → τ.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) →
      τ.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) →
      WP isa (.block (copy16 cbO ccO ++ ctrArgs ++ [Impl.AesGcm.AArch64.mov .x3 .x27])) τ fun t₁ =>
        CtrCall t₁ (p.W + BitVec.ofNat 64 240) (p.W + BitVec.ofNat 64 112) (p.D + BitVec.ofNat 64 (16 * j))
          (p.W + BitVec.ofNat 64 1760) p.R 1 ∧ VG.Proof.AesGcmSiv.AArch64.Env p t₁ ∧ t₁.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) ∧
          t₁.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) := fun E h27 h28 => by
    obtain ⟨t₁, run₁, -, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.AArch64.blkArgs_ok E h27
    have E' : VG.Proof.AesGcmSiv.AArch64.Env p t₁ := E.keep (fun r hr => ho₁ r (by
      simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
    exact WP.of_runBlock ⟨t₁, run₁, VG.Proof.AesGcmSiv.AArch64.blkCall L E' hj x0 x1 x2 x3 x4 x5, E', by rw [ho₁ _ (by decide), h27],
      by rw [ho₁ _ (by decide), h28]⟩
  have wc : ∀ {t : State}, (CtrCall t (p.W + BitVec.ofNat 64 240) (p.W + BitVec.ofNat 64 112)
      (p.D + BitVec.ofNat 64 (16 * j)) (p.W + BitVec.ofNat 64 1760) p.R 1 ∧ VG.Proof.AesGcmSiv.AArch64.Env p t ∧
      t.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) ∧ t.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j)) →
      WP isa (callCtr v.callees) t fun u => VG.Proof.AesGcmSiv.AArch64.Env p u ∧ u.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) ∧
        u.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) := fun ⟨cc, E, h27, h28⟩ =>
    WP.mono (ctr_call v.ctr cc) fun _ P => ⟨E.of_saved P.saved P.sp P.rd P.wr,
      by rw [P.saved _ (by decide) (by decide), h27], by rw [P.saved _ (by decide) (by decide), h28]⟩
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.rel_env E₁ E₂ [.x27, .x28] (by simp [a27, b27, a28, b28]) VG.Proof.AesGcmSiv.AArch64.blkA_check) (w E₁ a27 a28)
    (w E₂ b27 b28) fun u₁ u₂ A₁ A₂ => ?_
  exact rel_seq (rel_ctr v.ctr A₁.1 A₂.1 (A₁.2.1.sp_eq A₂.2.1)) (wc A₁) (wc A₂)
    fun w₁ w₂ ⟨F₁, c27₁, c28₁⟩ ⟨F₂, c27₂, c28₂⟩ => VG.Proof.AesGcmSiv.AArch64.rel_env F₁ F₂ [.x27, .x28] (by simp [c27₁, c27₂, c28₁, c28₂])
      VG.Proof.AesGcmSiv.AArch64.blkP_check

/-- What the constant-time proof needs of a run of counter mode after `j`
blocks. -/
structure BL (p : VG.Proof.AesGcmSiv.AArch64.Prm) (j : Nat) (t : State) : Prop where
  env : VG.Proof.AesGcmSiv.AArch64.Env p t
  x27 : t.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j)
  x28 : t.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j)

/-- A block of counter mode, for its registers. -/
theorem cryptBlockL_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {j : Nat} (hj : 16 * (j + 1) ≤ p.n) {t : State}
    (B : VG.Proof.AesGcmSiv.AArch64.BL p j t) :
    WP isa (cryptBlock v.callees) t fun t' => VG.Proof.AesGcmSiv.AArch64.BL p (j + 1) t' ∧
      t'.gpr .x9 = BitVec.ofNat 64 ((p.n - 16 * (j + 1)) / 16) := by
  have hn := L.n_lt
  obtain ⟨t₁, run₁, -, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.AArch64.blkArgs_ok B.env B.x27
  have E₁ : VG.Proof.AesGcmSiv.AArch64.Env p t₁ := B.env.keep (fun r hr => ho₁ r (by
    simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (ctr_call v.ctr (VG.Proof.AesGcmSiv.AArch64.blkCall L E₁ hj x0 x1 x2 x3 x4 x5)) fun t₂ P => ?_)
  have E₂ : VG.Proof.AesGcmSiv.AArch64.Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have h27₂ : t₂.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), B.x27]
  have h28₂ : t₂.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), B.x28]
  have c₀ := E₂.perm.wR (show 96 + 4 ≤ 3808 by decide)
  have c₁ := E₂.perm.wW (show 96 + 4 ≤ 3808 by decide)
  refine WP.run ⟨_, by grun [E₂.x19, c₀, c₁, h27₂, h28₂], rfl⟩ fun t₃ ht₃ => ?_
  subst ht₃
  refine ⟨⟨E₂.keep (fun r hr => by
      simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, ?_, ?_⟩, ?_⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27₂, add_ofNat_assoc]
    congr 2
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h28₂]
    rw [ofNat_sub (by omega) (by omega)]; congr 1
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h28₂]
    rw [ofNat_sub (by omega) (by omega), lsr_ofNat _ _ (by omega)]; congr 2

/-- The whole blocks of counter mode, for their registers. -/
theorem cryptMidL_ok (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {t : State} (B : VG.Proof.AesGcmSiv.AArch64.BL p 0 t)
    (h9 : t.gpr .x9 = BitVec.ofNat 64 (p.n / 16)) :
    WP isa (.ite (.zero .x .x9) (.block []) (.loop (cryptBlock v.callees) (.nonzero .x .x9))) t
      (VG.Proof.AesGcmSiv.AArch64.BL p (p.n / 16)) := by
  have hn := L.n_lt
  refine WP.ite (decide (p.n / 16 = 0)) (eval_zero h9 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n / 16 = 0 := by simpa using ht
    rw [h0]; exact WP.block_nil B
  · have h0 : p.n / 16 ≠ 0 := by simpa using hf
    refine WP.loop (M := isa) (fun k t' => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ VG.Proof.AesGcmSiv.AArch64.BL p j t') ?_
      (p.n / 16 - 0) t ⟨0, rfl, by omega, B⟩
    rintro k t' ⟨j, rfl, hj, B'⟩
    refine WP.mono (VG.Proof.AesGcmSiv.AArch64.cryptBlockL_ok v L (j := j) (by omega) B') fun t'' ⟨B'', x9⟩ => ?_
    have ev := eval_nonzero x9 (by omega)
    by_cases he : j + 1 = p.n / 16
    · left; exact ⟨ev.trans (by simp; omega), he ▸ B''⟩
    · right; exact ⟨ev.trans (by simp; omega), p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, B''⟩

theorem cryptHead_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [])) (.block cryptHead) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cryptTailRest_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [.x27, .x28]))
    (.seq (.block [Impl.AesGcm.AArch64.ptr .x11 .x19 bO, Impl.AesGcm.AArch64.mov .x12 .x27,
      Impl.AesGcm.AArch64.mov .x13 .x28]) Impl.AesGcm.AArch64.xorLoop) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `crypt`, in two runs with the same public arguments. -/
theorem crypt_rel (v : GcmImpl) {p : VG.Proof.AesGcmSiv.AArch64.Prm} (L : VG.Proof.AesGcmSiv.AArch64.Lay p) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p σ₁) (E₂ : VG.Proof.AesGcmSiv.AArch64.Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (crypt v.callees) TT := by
  have hn := L.n_lt
  have wh : ∀ {σ : State}, VG.Proof.AesGcmSiv.AArch64.Env p σ → WP isa (.block cryptHead) σ fun t₁ => VG.Proof.AesGcmSiv.AArch64.BL p 0 t₁ ∧
      t₁.gpr .x9 = BitVec.ofNat 64 (p.n / 16) := fun E => by
    obtain ⟨t₁, run₁, -, x27₁, x28₁, x9₁, ho₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesGcmSiv.AArch64.cryptHead_ok L E
    exact WP.of_runBlock ⟨t₁, run₁, ⟨E.keep (fun r hr => ho₁ r (by
      simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁,
      by rw [x27₁, Nat.mul_zero, BitVec.add_zero], by rw [x28₁, Nat.mul_zero, Nat.sub_zero]⟩, x9₁⟩
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.rel_env E₁ E₂ [] (by simp) VG.Proof.AesGcmSiv.AArch64.cryptHead_check) (wh E₁) (wh E₂)
    fun u₁ u₂ ⟨B₁, x9₁⟩ ⟨B₂, x9₂⟩ => ?_
  -- The whole blocks.
  refine rel_seq (rel_ite (eval_zero x9₁ (by omega)) (eval_zero x9₂ (by omega))
      (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun hf => ?_))
    (VG.Proof.AesGcmSiv.AArch64.cryptMidL_ok v L B₁ x9₁) (VG.Proof.AesGcmSiv.AArch64.cryptMidL_ok v L B₂ x9₂) fun w₁ w₂ C₁ C₂ => ?_
  · have h0 : p.n / 16 ≠ 0 := by simpa using hf
    refine VG.Proof.AesGcmSiv.AArch64.rel_loop (fun k t₁ t₂ => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ VG.Proof.AesGcmSiv.AArch64.BL p j t₁ ∧ VG.Proof.AesGcmSiv.AArch64.BL p j t₂)
      (fun k t₁ t₂ ⟨j, hk, hj, J₁, J₂⟩ => ?_) (p.n / 16 - 0) ⟨0, rfl, by omega, B₁, B₂⟩
    refine VG.Proof.AesGcmSiv.AArch64.rel_wpQ (VG.Proof.AesGcmSiv.AArch64.cryptBlock_rel v L J₁.env J₂.env (j := j) (by omega) J₁.x27 J₂.x27 J₁.x28 J₂.x28)
      (VG.Proof.AesGcmSiv.AArch64.cryptBlockL_ok v L (by omega) J₁) (VG.Proof.AesGcmSiv.AArch64.cryptBlockL_ok v L (by omega) J₂) fun a b ⟨K₁, x9₁⟩ ⟨K₂, x9₂⟩ => ?_
    have ev₁ := eval_nonzero x9₁ (by omega)
    have ev₂ := eval_nonzero x9₂ (by omega)
    refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
    rw [ev₁] at hc
    have he : j + 1 ≠ p.n / 16 := by simp at hc; omega
    exact ⟨p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, K₁, K₂⟩
  -- The last bytes.
  have x28₁ : w₁.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [C₁.x28]; congr 1; omega
  have x28₂ : w₂.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [C₂.x28]; congr 1; omega
  refine rel_ite (eval_zero x28₁ (by omega)) (eval_zero x28₂ (by omega))
    (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun _ => ?_)
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.tag_rel v L C₁.env C₂.env (o := 224) (by decide)) (VG.Proof.AesGcmSiv.AArch64.tag_ok v L C₁.env (o := 224) (by decide))
    (VG.Proof.AesGcmSiv.AArch64.tag_ok v L C₂.env (o := 224) (by decide)) fun z₁ z₂ T₁ T₂ => ?_
  exact VG.Proof.AesGcmSiv.AArch64.rel_env T₁.env T₂.env [.x27, .x28] (by simp [T₁.x27, T₂.x27, T₁.x28, T₂.x28, C₁.x27, C₂.x27, C₁.x28, C₂.x28])
    VG.Proof.AesGcmSiv.AArch64.cryptTailRest_check

/-! ## The functions -/

/-- `ldr x9, [sp]`: `W` in `x9`. -/
theorem ldr9_ok {s : State} (hA : Covers [VG.Proof.AesGcmSiv.AArch64.args s] (s.rd ++ s.wr)) :
    WP isa (.block [.ldrSp .x9 0]) s fun s' => s'.gpr .x9 = stackArg s 0 ∧ (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a₀ : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa [VG.Proof.AesGcmSiv.AArch64.args, stackArgAddr] using in_off (d := 0) (n := 8) hA (by decide) (by decide)
  refine WP.run ⟨_, by grun [BitVec.add_zero, a₀], rfl⟩ fun s' hs => ?_
  subst hs
  exact ⟨by simp [gpr_write, stackArg, stackArgAddr, Mem.readW], fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl⟩

theorem ldr9_check : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x9 0]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem entryRest_check : ∃ h, (taint.check (Taint.ofRegs [.x9, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7])
    (.block (Impl.AesGcm.AArch64.save .x9 ++ [Impl.AesGcm.AArch64.mov .x19 .x9, Impl.AesGcm.AArch64.mov .x20 .x2,
      Impl.AesGcm.AArch64.mov .x21 .x0, Impl.AesGcm.AArch64.mov .x22 .x1, Impl.AesGcm.AArch64.mov .x23 .x3,
      Impl.AesGcm.AArch64.mov .x24 .x4, Impl.AesGcm.AArch64.mov .x25 .x5, Impl.AesGcm.AArch64.mov .x26 .x6,
      .str .x .x7 .x19 tagPO])) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [])) (.block Impl.AesGcm.AArch64.restore) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem openEnd_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs []))
    (.seq (.block cmp) (.seq mask (.block ([Impl.AesGcm.AArch64.mov .x0 .x27] ++ Impl.AesGcm.AArch64.restore)))) h).isSome =
    true := ⟨_, by taint_decide⟩

/-- The public arguments of two states with the same public data. -/
theorem prmOf_eq {σ₁ σ₂ : State} (h : VG.Proof.AesGcmSiv.AArch64.onePub σ₁ σ₂) : VG.Proof.AesGcmSiv.AArch64.prmOf σ₁ = VG.Proof.AesGcmSiv.AArch64.prmOf σ₂ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hsp, hw⟩ := h
  simp only [VG.Proof.AesGcmSiv.AArch64.prmOf, h0, h1, h2, h3, h4, h5, h6, h7, hsp, hw]

/-- The entry, in two runs with the same public arguments. -/
theorem entry_rel {σ₁ σ₂ : State} (h : VG.Proof.AesGcmSiv.AArch64.onePub σ₁ σ₂) (hA₁ : Covers [VG.Proof.AesGcmSiv.AArch64.args σ₁] (σ₁.rd ++ σ₁.wr))
    (hA₂ : Covers [VG.Proof.AesGcmSiv.AArch64.args σ₂] (σ₂.rd ++ σ₂.wr)) : RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hsp, hw⟩ := h
  show RelCT isa _ (.block ([.ldrSp .x9 0] ++ Impl.AesGcm.AArch64.save .x9 ++ _)) _
  rw [List.append_assoc]
  refine RelCT.block_split (rel_seq (rel_taint [] hsp (by simp) VG.Proof.AesGcmSiv.AArch64.ldr9_check) (VG.Proof.AesGcmSiv.AArch64.ldr9_ok hA₁) (VG.Proof.AesGcmSiv.AArch64.ldr9_ok hA₂)
    fun τ₁ τ₂ ⟨x9₁, g₁, sp₁, _, _⟩ ⟨x9₂, g₂, sp₂, _, _⟩ => ?_)
  refine rel_taint _ (by rw [sp₁, sp₂, hsp]) ?_ VG.Proof.AesGcmSiv.AArch64.entryRest_check
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; rw [x9₁, x9₂, hw]
  · rw [g₁ r h9, g₂ r h9]
    simp only [List.mem_cons, List.not_mem_nil, or_false, h9, false_or] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3, h4, h5, h6, h7]

/-- The entry of the second run, with the first's public arguments. -/
theorem entry_pub {σ₁ σ₂ : State} (hp : VG.Proof.AesGcmSiv.AArch64.onePub σ₁ σ₂) (P : VG.Proof.AesGcmSiv.AArch64.Perm (VG.Proof.AesGcmSiv.AArch64.prmOf σ₂) σ₂)
    (hA : Covers [VG.Proof.AesGcmSiv.AArch64.args σ₂] (σ₂.rd ++ σ₂.wr)) :
    WP isa (.block entry) σ₂ fun s => VG.Proof.AesGcmSiv.AArch64.Env (VG.Proof.AesGcmSiv.AArch64.prmOf σ₁) s ∧ VG.Proof.AesGcmSiv.AArch64.TagSlot (VG.Proof.AesGcmSiv.AArch64.prmOf σ₁) s.mem := by
  rw [VG.Proof.AesGcmSiv.AArch64.prmOf_eq hp]
  exact WP.mono (VG.Proof.AesGcmSiv.AArch64.entry_ok P hA) fun _ h => ⟨h.1, h.2.2.2.1⟩

/-- `ldr x9, [x19, #216]`: `tag`'s address in `x9`. -/
theorem ldrT_ok {p : VG.Proof.AesGcmSiv.AArch64.Prm} {s : State} (E : VG.Proof.AesGcmSiv.AArch64.Env p s) (hT : VG.Proof.AesGcmSiv.AArch64.TagSlot p s.mem) :
    WP isa (.block [.ldr .x .x9 .x19 tagPO]) s fun s' => s'.gpr .x9 = p.T ∧ VG.Proof.AesGcmSiv.AArch64.Env p s' := by
  have r₀ := E.perm.wR (show 216 + 8 ≤ 3808 by decide)
  have hT' : s.mem.read (p.W + BitVec.ofNat 64 216) 8 = p.T := by rw [VG.Proof.AesGcmSiv.AArch64.read8_readW]; exact hT
  refine WP.run ⟨_, by grun [E.x19, r₀, hT'], rfl⟩ fun s' hs => ?_
  subst hs
  exact ⟨by simp [gpr_write], E.write (by decide) _⟩

theorem ldrT_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [])) (.block [.ldr .x .x9 .x19 tagPO]) h).isSome =
    true := ⟨_, by taint_decide⟩

/-- `ldr x9, [x19, #216]` and then `l`, which the taint analysis checks with
`x9` public, in two runs with the same public arguments. -/
theorem rel_ldrT {p : VG.Proof.AesGcmSiv.AArch64.Prm} {σ₁ σ₂ : State} (E₁ : VG.Proof.AesGcmSiv.AArch64.Env p σ₁) (E₂ : VG.Proof.AesGcmSiv.AArch64.Env p σ₂) (T₁ : VG.Proof.AesGcmSiv.AArch64.TagSlot p σ₁.mem)
    (T₂ : VG.Proof.AesGcmSiv.AArch64.TagSlot p σ₂.mem) {l : List Instr}
    (hc : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [.x9])) (.block l) h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) (.block (([.ldr .x .x9 .x19 tagPO] : List Instr) ++ l)) TT :=
  RelCT.block_split (rel_seq (VG.Proof.AesGcmSiv.AArch64.rel_env E₁ E₂ [] (by simp) VG.Proof.AesGcmSiv.AArch64.ldrT_check) (VG.Proof.AesGcmSiv.AArch64.ldrT_ok E₁ T₁) (VG.Proof.AesGcmSiv.AArch64.ldrT_ok E₂ T₂)
    fun _ _ ⟨x9₁, E₁'⟩ ⟨x9₂, E₂'⟩ => VG.Proof.AesGcmSiv.AArch64.rel_env E₁' E₂' [.x9] (by simp [x9₁, x9₂]) hc)

theorem sealEnd_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [.x9]))
    (.block (tagOut.tail ++ Impl.AesGcm.AArch64.restore)) h).isSome = true := ⟨_, by taint_decide⟩

theorem recv_check : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesGcmSiv.AArch64.pubRegs [.x9])) (.block recv.tail) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem seal_ct (v : GcmImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub («seal» v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁, -, hA₁⟩ := VG.Proof.AesGcmSiv.AArch64.args_of_seal h₁
  obtain ⟨-, P₂, -, hA₂⟩ := VG.Proof.AesGcmSiv.AArch64.args_of_seal h₂
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.entry_rel hp hA₁ hA₂) (VG.Proof.AesGcmSiv.AArch64.entry_ok P₁ hA₁) (VG.Proof.AesGcmSiv.AArch64.entry_pub hp P₂ hA₂)
    fun τ₁ τ₂ ⟨E₁, _, _, S₁, _⟩ ⟨E₂, S₂⟩ => ?_
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.keys_rel v L E₁ E₂) (VG.Proof.AesGcmSiv.AArch64.keys_ok v L E₁) (VG.Proof.AesGcmSiv.AArch64.keys_ok v L E₂) fun a₁ a₂ K₁ K₂ => ?_
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.polyval_rel v L K₁.env K₂.env) (VG.Proof.AesGcmSiv.AArch64.polyval_ok v L K₁.env K₁.hkey K₁.acc)
    (VG.Proof.AesGcmSiv.AArch64.polyval_ok v L K₂.env K₂.hkey K₂.acc) fun b₁ b₂ P₁ P₂ => ?_
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.tag_rel v L P₁.env P₂.env (o := 0) (by decide)) (VG.Proof.AesGcmSiv.AArch64.tag_ok v L P₁.env (o := 0) (by decide))
    (VG.Proof.AesGcmSiv.AArch64.tag_ok v L P₂.env (o := 0) (by decide)) fun c₁ c₂ T₁ T₂ => ?_
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.crypt_rel v L T₁.env T₂.env) (VG.Proof.AesGcmSiv.AArch64.crypt_ok v L T₁.env) (VG.Proof.AesGcmSiv.AArch64.crypt_ok v L T₂.env)
    fun d₁ d₂ C₁ C₂ => ?_
  have sl : ∀ {τ a b c d : State}, VG.Proof.AesGcmSiv.AArch64.TagSlot (VG.Proof.AesGcmSiv.AArch64.prmOf σ₁) τ.mem → VG.Proof.AesGcmSiv.AArch64.KeysPost (VG.Proof.AesGcmSiv.AArch64.prmOf σ₁) τ a → VG.Proof.AesGcmSiv.AArch64.PolyPost (VG.Proof.AesGcmSiv.AArch64.prmOf σ₁) a b →
      VG.Proof.AesGcmSiv.AArch64.TagPost (VG.Proof.AesGcmSiv.AArch64.prmOf σ₁) 0 b c → VG.Proof.AesGcmSiv.AArch64.CryptPost (VG.Proof.AesGcmSiv.AArch64.prmOf σ₁) c d → VG.Proof.AesGcmSiv.AArch64.TagSlot (VG.Proof.AesGcmSiv.AArch64.prmOf σ₁) d.mem := fun S K P T C =>
    (((S.frame K.frame (by disj_tac L)).frame P.frame (by disj_tac L)).frame T.frame (by disj_tac L)).frame C.frame
      (by disj_tac L)
  exact VG.Proof.AesGcmSiv.AArch64.rel_ldrT (l := tagOut.tail ++ Impl.AesGcm.AArch64.restore) C₁.env C₂.env (sl S₁ K₁ P₁ T₁ C₁)
    (sl S₂ K₂ P₂ T₂ C₂) VG.Proof.AesGcmSiv.AArch64.sealEnd_check

theorem open_ct (v : GcmImpl) : ConstantTime isa openAArch64.pre openAArch64.pub («open» v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁, hA₁⟩ := VG.Proof.AesGcmSiv.AArch64.args_of_open h₁
  obtain ⟨-, P₂, hA₂⟩ := VG.Proof.AesGcmSiv.AArch64.args_of_open h₂
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.entry_rel hp hA₁ hA₂) (VG.Proof.AesGcmSiv.AArch64.entry_ok P₁ hA₁) (VG.Proof.AesGcmSiv.AArch64.entry_pub hp P₂ hA₂)
    fun τ₁ τ₂ ⟨E₁, _, _, S₁, _⟩ ⟨E₂, S₂⟩ => ?_
  have wr : ∀ {τ : State}, VG.Proof.AesGcmSiv.AArch64.Env (VG.Proof.AesGcmSiv.AArch64.prmOf σ₁) τ → VG.Proof.AesGcmSiv.AArch64.TagSlot (VG.Proof.AesGcmSiv.AArch64.prmOf σ₁) τ.mem → WP isa (.block recv) τ (VG.Proof.AesGcmSiv.AArch64.Env (VG.Proof.AesGcmSiv.AArch64.prmOf σ₁)) :=
    fun E S => by
      obtain ⟨t, run, -, -, -, ho, sp, rd, wr⟩ := VG.Proof.AesGcmSiv.AArch64.recv_ok L E S
      exact WP.of_runBlock ⟨t, run, E.keep (fun r hr => ho r (by
        simp only [VG.Proof.AesGcmSiv.AArch64.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp rd wr⟩
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.rel_ldrT (l := recv.tail) E₁ E₂ S₁ S₂ VG.Proof.AesGcmSiv.AArch64.recv_check) (wr E₁ S₁) (wr E₂ S₂) fun ρ₁ ρ₂ R₁ R₂ => ?_
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.keys_rel v L R₁ R₂) (VG.Proof.AesGcmSiv.AArch64.keys_ok v L R₁) (VG.Proof.AesGcmSiv.AArch64.keys_ok v L R₂) fun a₁ a₂ K₁ K₂ => ?_
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.crypt_rel v L K₁.env K₂.env) (VG.Proof.AesGcmSiv.AArch64.crypt_ok v L K₁.env) (VG.Proof.AesGcmSiv.AArch64.crypt_ok v L K₂.env) fun b₁ b₂ C₁ C₂ => ?_
  have hG : ∀ {σ τ : State}, VG.Proof.AesGcmSiv.AArch64.KeysPost (VG.Proof.AesGcmSiv.AArch64.prmOf σ₁) σ τ → ∀ {u : State}, VG.Proof.AesGcmSiv.AArch64.CryptPost (VG.Proof.AesGcmSiv.AArch64.prmOf σ₁) τ u →
      Spec.Gcm.blockAt u.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf σ₁).W + BitVec.ofNat 64 64) =
        GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt u.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf σ₁).W + BitVec.ofNat 64 16) 16)) ∧
      Spec.Gcm.blockAt u.mem ((VG.Proof.AesGcmSiv.AArch64.prmOf σ₁).W + BitVec.ofNat 64 80) = 0 := by
    intro _ _ K _ C
    rw [Proof.AesGcm.AArch64.blockAt_frame C.frame (by disj_tac L), K.hkey,
      Proof.AesGcm.AArch64.blockAt_frame C.frame (by disj_tac L), K.acc,
      VG.Proof.AesGcmSiv.AArch64.bytesAt_keep C.frame (by disj_tac L) (by decide)]
    exact ⟨rfl, rfl⟩
  refine rel_seq (VG.Proof.AesGcmSiv.AArch64.polyval_rel v L C₁.env C₂.env) (VG.Proof.AesGcmSiv.AArch64.polyval_ok v L C₁.env (hG K₁ C₁).1 (hG K₁ C₁).2)
    (VG.Proof.AesGcmSiv.AArch64.polyval_ok v L C₂.env (hG K₂ C₂).1 (hG K₂ C₂).2) fun c₁ c₂ P₁ P₂ => ?_
  exact rel_seq (VG.Proof.AesGcmSiv.AArch64.tag_rel v L P₁.env P₂.env (o := 224) (by decide)) (VG.Proof.AesGcmSiv.AArch64.tag_ok v L P₁.env (o := 224) (by decide))
    (VG.Proof.AesGcmSiv.AArch64.tag_ok v L P₂.env (o := 224) (by decide)) fun d₁ d₂ T₁ T₂ => VG.Proof.AesGcmSiv.AArch64.rel_env T₁.env T₂.env [] (by simp) VG.Proof.AesGcmSiv.AArch64.openEnd_check

end VG.Proof.AesGcmSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcmSiv.AArch64.Verified`. -/
section

/-!
# AES-GCM-SIV on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`), with the tag input computed with GHASH equal to the RFC's
(`tagInput_eq`, from `Proof.GcmSiv.Polyval`, imported here only so that the
other proofs need not import its algebra), a state satisfying each
precondition, and the shared contracts of `Spec/GcmSiv/Contract.lean` with
the working space as a last argument (`Proof/AesGcmSiv/Scratch.lean`, 476
words), with no stack: the calls keep the return address in `x30`, which
each function saves in the working space. The last section allocates the
working space.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.Impl.AesGcmSiv.AArch64
open VG.Proof.AesGcm.AArch64 (GcmImpl)

/-- RFC 8452 Appendix A: POLYVAL with `H` is GHASH with `H · x`. -/
theorem tagInput_eq : VG.Proof.AesGcmSiv.AArch64.TagInputEq := fun a n pt d => by
  rw [GcmSiv.tagInput_eq, Spec.GcmSiv.polyval, GcmSiv.Polyval.polyvalFrom_eq]
  rfl

/-! ## v8–v15 -/

theorem seal_keepsV (v : GcmImpl) : («seal» v.callees).allInstrs keepsV = true := by
  simp only [«seal», VG.Impl.AesGcmSiv.AArch64.keys, derive, expand, polyval, absorb, absTail, absTailPre, chunk, chunkPre, chunkLen, revLoop,
    lens, tag, tagOut, crypt, cryptBlock, cryptTail, callCtr, callKey, callGh, Impl.AesGcm.AArch64.copyLoop,
    Impl.AesGcm.AArch64.xorLoop, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

theorem open_keepsV (v : GcmImpl) : («open» v.callees).allInstrs keepsV = true := by
  simp only [«open», VG.Impl.AesGcmSiv.AArch64.keys, derive, expand, polyval, absorb, absTail, absTailPre, chunk, chunkPre, chunkLen, revLoop,
    lens, tag, recv, crypt, cryptBlock, cryptTail, mask, callCtr, callKey, callGh, Impl.AesGcm.AArch64.copyLoop,
    Impl.AesGcm.AArch64.xorLoop, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

/-! ## Correctness -/

theorem seal_correct (v : GcmImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesGcmSiv.AArch64.seal_wp v VG.Proof.AesGcmSiv.AArch64.tagInput_eq hs) (VG.Proof.AesGcmSiv.AArch64.seal_keepsV v)

theorem open_correct (v : GcmImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesGcmSiv.AArch64.open_wp v VG.Proof.AesGcmSiv.AArch64.tagInput_eq hs) (VG.Proof.AesGcmSiv.AArch64.open_keepsV v)

/-! ## States satisfying the preconditions (with empty buffers) -/

/-- `seal`'s: the tag at `0x5000`, and `work` at `0x8000`, its address at
`sp`. -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | .x7 => 0x5000 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10001 then 0x80 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x10000, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩, ⟨0x8000, 3808⟩]

/-- `open`'s: as `seal`'s, with the tag read only. -/
def openSat : State := { VG.Proof.AesGcmSiv.AArch64.sealSat with
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x10000, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x8000, 3808⟩] }

/-! ## The shared contracts, with the working space as an argument -/

theorem seal_verified (v : GcmImpl) :
    Verified AArch64.target («seal» v.callees) (Proof.AesGcmSiv.sealScratchContract AArch64.abi 476) :=
  Verified.of_correct (VG.Proof.AesGcmSiv.AArch64.seal_correct v) (VG.Proof.AesGcmSiv.AArch64.seal_ct v) (by
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Spec.GcmSiv.sealPost, VG.Proof.AesGcmSiv.AArch64.sealAArch64, VG.Proof.AesGcmSiv.AArch64.sealPre, VG.Proof.AesGcmSiv.AArch64.oneLay, VG.Proof.AesGcmSiv.AArch64.onePub, VG.Proof.AesGcmSiv.AArch64.args, VG.Proof.AesGcmSiv.AArch64.rounds, AArch64.abi, AArch64.argRegs,
      AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat] using VG.Proof.AesGcmSiv.AArch64.sealSat)

theorem open_verified (v : GcmImpl) :
    Verified AArch64.target («open» v.callees) (Proof.AesGcmSiv.openScratchContract AArch64.abi 476) :=
  Verified.of_correct (VG.Proof.AesGcmSiv.AArch64.open_correct v) (VG.Proof.AesGcmSiv.AArch64.open_ct v)
    { pre := by sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.AArch64.openAArch64, VG.Proof.AesGcmSiv.AArch64.openResult, VG.Proof.AesGcmSiv.AArch64.openPost,
        VG.Proof.AesGcmSiv.AArch64.openPre, VG.Proof.AesGcmSiv.AArch64.oneLay, VG.Proof.AesGcmSiv.AArch64.onePub, VG.Proof.AesGcmSiv.AArch64.args, VG.Proof.AesGcmSiv.AArch64.rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      -- `h` and the goal match on the same outcome of `decryptWith` with
      -- different matchers (`openPost`'s and `openContract`'s): split on it
      -- rather than have `exact h` unfold both to unify them.
      post := by
        intro s s' _ h
        sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.AArch64.openAArch64, VG.Proof.AesGcmSiv.AArch64.openResult, VG.Proof.AesGcmSiv.AArch64.openPost,
          VG.Proof.AesGcmSiv.AArch64.openPre, VG.Proof.AesGcmSiv.AArch64.oneLay, VG.Proof.AesGcmSiv.AArch64.onePub, VG.Proof.AesGcmSiv.AArch64.args, VG.Proof.AesGcmSiv.AArch64.rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.AArch64.openAArch64, VG.Proof.AesGcmSiv.AArch64.openResult, VG.Proof.AesGcmSiv.AArch64.openPost,
          VG.Proof.AesGcmSiv.AArch64.openPre, VG.Proof.AesGcmSiv.AArch64.oneLay, VG.Proof.AesGcmSiv.AArch64.onePub, VG.Proof.AesGcmSiv.AArch64.args, VG.Proof.AesGcmSiv.AArch64.rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop] at h
        intro _
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by sig_implies_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.AArch64.openAArch64, VG.Proof.AesGcmSiv.AArch64.openResult, VG.Proof.AesGcmSiv.AArch64.openPost,
        VG.Proof.AesGcmSiv.AArch64.openPre, VG.Proof.AesGcmSiv.AArch64.oneLay, VG.Proof.AesGcmSiv.AArch64.onePub, VG.Proof.AesGcmSiv.AArch64.args, VG.Proof.AesGcmSiv.AArch64.rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := by sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Spec.GcmSiv.openPost, Spec.GcmSiv.openLeak, VG.Proof.AesGcmSiv.AArch64.openAArch64, VG.Proof.AesGcmSiv.AArch64.openResult, VG.Proof.AesGcmSiv.AArch64.openPost,
        VG.Proof.AesGcmSiv.AArch64.openPre, VG.Proof.AesGcmSiv.AArch64.oneLay, VG.Proof.AesGcmSiv.AArch64.onePub, VG.Proof.AesGcmSiv.AArch64.args, VG.Proof.AesGcmSiv.AArch64.rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop] [openSat, sealSat] using VG.Proof.AesGcmSiv.AArch64.openSat }

/-! ## With the working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (above), in a frame that allocates it
(`Verified.stackArgScratch`): their working space is their first stack
argument, as the eight argument registers are taken, so the frame of 3824
bytes holds the address of the working space and the working space, at the
next 16-byte boundary. The code itself uses no stack: its calls keep the
return address in `x30`. `open`'s leak, whether it succeeds, reads only its
buffers (`openLeak_local`).
-/

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space. -/
def sealFrameSat : State :=
  { VG.Proof.AesGcmSiv.AArch64.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩], wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.GcmSiv.sealContract AArch64.abi 3824).pre s := by
  implies_sat [Spec.GcmSiv.sealContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Spec.GcmSiv.sealPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesGcmSiv.AArch64.sealFrameSat

theorem seal_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 3824 0 («seal» v.callees))
      (Spec.GcmSiv.sealContract AArch64.abi 3824) :=
  AArch64.Verified.stackArgScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 476) (pre := Spec.GcmSiv.sealPre AArch64.abi.ptrBits)
    (post := Spec.GcmSiv.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3824)
    (VG.Proof.AesGcmSiv.AArch64.seal_verified v) (by decide) (by decide) (sealPre_local _) (sealPost_local _) VG.Proof.AesGcmSiv.AArch64.sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space. -/
def openFrameSat : State :=
  { VG.Proof.AesGcmSiv.AArch64.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x5000, 16⟩], wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.GcmSiv.openContract AArch64.abi 3824).pre s := by
  implies_sat [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Spec.GcmSiv.openPost,
    Spec.GcmSiv.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD,
    List.range, List.range.loop] [openFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesGcmSiv.AArch64.openFrameSat

theorem open_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 3824 0 («open» v.callees))
      (Spec.GcmSiv.openContract AArch64.abi 3824) :=
  AArch64.Verified.stackArgScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 476) (pre := Spec.GcmSiv.openPre AArch64.abi.ptrBits)
    (post := Spec.GcmSiv.openPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3824)
    (leak := some (Spec.GcmSiv.openLeak AArch64.abi.ptrBits))
    (Proof.AesGcmSiv.Verified.of_openScratch (VG.Proof.AesGcmSiv.AArch64.open_verified v)) (by decide) (by decide) (openPre_local _)
    (openPost_local _) VG.Proof.AesGcmSiv.AArch64.openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesGcmSiv.AArch64

end
