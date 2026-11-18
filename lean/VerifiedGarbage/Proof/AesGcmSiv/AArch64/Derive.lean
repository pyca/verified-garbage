module

public import VerifiedGarbage.Proof.GcmSiv.Spec
public import VerifiedGarbage.Impl.AesGcmSiv.AArch64
public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
public import VerifiedGarbage.Spec.GcmSiv
import VerifiedGarbage.Proof.AesGcm.AArch64.Save
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Spec.GcmSiv.Contract

/-! ### `AesGcmSiv.AArch64.Env`, which this module and modules that import it used -/

section

/-!
# AES-GCM-SIV on AArch64: the contracts, and where everything is

Untrusted: everything here is checked by Lean. The shared contracts of
`Spec/GcmSiv/Contract.lean`, with the working space as a last argument
(`Proof/AesGcmSiv/Scratch.lean`), imply these (`Verified.lean`). Every
argument but the working space is in a register, and a call (`bl`) stores
nothing in memory, so no stack is used.
-/

@[expose] public section

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
    data.Disjoint work ∧ data.Disjoint (args s) ∧ work.Disjoint (args s) ∧
    (s.gpr .x0).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x7).toNat + 16 ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 3808 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 ≤ 2 ^ 64 ∧
    rounds (s.gpr .x1)

/-- What `vg_aes_gcm_siv_seal` needs: `oneLay`, with `tag` the 16 bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .x0, 240⟩
  let nonce : Region := ⟨s.gpr .x2, 12⟩
  let aad : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let tag : Region := ⟨s.gpr .x7, 16⟩
  let work : Region := ⟨stackArg s 0, 3808⟩
  s.rd = [sch, nonce, aad, args s] ∧ s.wr = [data, tag, work] ∧ oneLay s

/-- What `vg_aes_gcm_siv_open` needs: `oneLay`, with the received tag the 16
bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .x0, 240⟩
  let nonce : Region := ⟨s.gpr .x2, 12⟩
  let aad : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let tag : Region := ⟨s.gpr .x7, 16⟩
  let work : Region := ⟨stackArg s 0, 3808⟩
  s.rd = [sch, nonce, aad, tag, args s] ∧ s.wr = [data, work] ∧ oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- `vg_aes_gcm_siv_seal`. -/
def sealAArch64 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (keyLen (s.gpr .x1).toNat)
        (bytesAt s.mem (s.gpr .x2) 12) (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
        (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) =
      (bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat, bytesAt s'.mem (s.gpr .x7) 16)
  pub := onePub

/-- What `vg_aes_gcm_siv_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (keyLen (s.gpr .x1).toNat)
    (bytesAt s.mem (s.gpr .x2) 12) (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
    (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (bytesAt s.mem (s.gpr .x7) 16)

/-- What `vg_aes_gcm_siv_open` leaves in `x0` and in the `n` bytes of data
at `D`, for the result `r`. Irreducible, so that checking a state against
it never evaluates `r`. -/
@[irreducible] def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
  | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : (s'.gpr .x0).setWidth 32 = 1) (hd : bytesAt s'.mem D n = pt) :
    openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : (s'.gpr .x0).setWidth 32 = 0) (hd : bytesAt s'.mem D n = zeros n) :
    openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

/-- `vg_aes_gcm_siv_open`. It does not branch on whether the tag is right,
so its runs are related without the leak the shared contract allows. -/
def openAArch64 : Contract isa where
  pre := openPre
  post s s' := openPost (openResult s) s' (s.gpr .x5) (s.gpr .x6).toNat
  pub := onePub

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
tactic_template "grun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
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
structure Lay (p : Prm) : Prop where
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
structure Perm (p : Prm) (s : State) : Prop where
  k : Covers [⟨p.K, 240⟩] (s.rd ++ s.wr)
  non : Covers [⟨p.N, 12⟩] (s.rd ++ s.wr)
  aad : Covers [⟨p.A, p.al⟩] (s.rd ++ s.wr)
  d : Covers [⟨p.D, p.n⟩] s.wr
  w : Covers [⟨p.W, 3808⟩] s.wr
  t : Covers [⟨p.T, 16⟩] (s.rd ++ s.wr)

theorem Perm.of_eq {p : Prm} {s s' : State} (h : Perm p s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm p s' := by
  obtain ⟨a, b, c, d, e, f⟩ := h
  exact ⟨by rw [hrd, hwr]; exact a, by rw [hrd, hwr]; exact b, by rw [hrd, hwr]; exact c, by rw [hwr]; exact d,
    by rw [hwr]; exact e, by rw [hrd, hwr]; exact f⟩

/-- The registers holding the public arguments, the stack pointer, and what
the state may access. -/
structure Env (p : Prm) (s : State) : Prop where
  x19 : s.gpr .x19 = p.W
  x20 : s.gpr .x20 = p.N
  x21 : s.gpr .x21 = p.K
  x22 : s.gpr .x22 = BitVec.ofNat 64 p.R
  x23 : s.gpr .x23 = p.A
  x24 : s.gpr .x24 = BitVec.ofNat 64 p.al
  x25 : s.gpr .x25 = p.D
  x26 : s.gpr .x26 = BitVec.ofNat 64 p.n
  sp : s.sp = p.SP
  perm : Perm p s

/-- The registers `Env` pins. -/
abbrev envRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26]

/-- An environment, after code that keeps `x19`–`x26`, the stack pointer and
the permissions. -/
theorem Env.keep {p : Prm} {s s' : State} (h : Env p s) (hg : ∀ r ∈ envRegs, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env p s' :=
  ⟨by rw [hg _ (by simp), h.x19], by rw [hg _ (by simp), h.x20], by rw [hg _ (by simp), h.x21],
    by rw [hg _ (by simp), h.x22], by rw [hg _ (by simp), h.x23], by rw [hg _ (by simp), h.x24],
    by rw [hg _ (by simp), h.x25], by rw [hg _ (by simp), h.x26], by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after a register apart from `x19`–`x26` is written. -/
theorem Env.write {p : Prm} {s : State} (h : Env p s) {r : Reg} (hr : r ∉ envRegs) {sz : Size}
    (v : BitVec sz.bits) : Env p (s.write sz r v) :=
  h.keep (fun q hq => by exact gpr_write_of_ne _ _ _ fun (e : q = r) => hr (e ▸ hq)) rfl rfl rfl

/-- An environment, after a call. -/
theorem Env.of_saved {p : Prm} {s s' : State} (h : Env p s)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env p s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide))
    hsp hrd hwr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 3808) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 3808⟩ :=
  Offset.sub_base _ h

variable {p : Prm} (L : Lay p)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 3808) (hd : d + k ≤ 3808) :
    (⟨p.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega_using [ha]) (by have := L.ww; omega_using [hd])

theorem k_w' {d k : Nat} (hd : d + k ≤ 3808) : (⟨p.K, 240⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (wSub hd)

theorem n_w' {d k : Nat} (hd : d + k ≤ 3808) : (⟨p.N, 12⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.n_w.sub_right (wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 3808) : (⟨p.A, p.al⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 3808) : (⟨p.D, p.n⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (wSub hd)

theorem t_w' {d k : Nat} (hd : d + k ≤ 3808) : (⟨p.T, 16⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.t_w.sub_right (wSub hd)

theorem toNat_W {d : Nat} (hd : d < 3808) : (p.W + BitVec.ofNat 64 d).toNat = p.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd]), Nat.mod_eq_of_lt (by omega_using [hd, this])]

theorem rounds_le : 16 * (p.R + 1) ≤ 240 := by rcases L.rounds with h | h <;> rw [h] <;> decide

theorem rounds3 : p.R = 10 ∨ p.R = 12 ∨ p.R = 14 := by rcases L.rounds with h | h <;> simp [h]

end Lay

/-- `W` itself, as the part at offset 0. -/
theorem Lay.w0 {p : Prm} (_L : Lay p) : p.W + BitVec.ofNat 64 0 = p.W := BitVec.add_zero _

namespace Perm

variable {p : Prm} {s : State} (P : Perm p s)
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
theorem Env.w2560R {p : Prm} {s : State} (E : Env p s) : Covers [⟨p.W, 2560⟩] (s.rd ++ s.wr) :=
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
    (⟨p, k⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := Offset.contains_base p h (by omega_using [h, hk])

theorem contains_at0 (p : Addr) {n k : Nat} (h : n ≤ k) (hk : k < 2 ^ 64) :
    (⟨p, k⟩ : Region).Contains p n := by
  simpa using contains_at p (d := 0) (by omega_using [h] : 0 + n ≤ k) hk

end VG.Proof.AesGcmSiv.AArch64

end

end

/-!
# AES-GCM-SIV on AArch64: the message keys (`derive`)

Untrusted: everything here is checked by Lean. Each step of `derive` writes
`little_endian_uint32(i) ‖ nonce` at `W + 112` and a zero block at
`W + 224` (`derArgs_ok`), on which `vg_aes_ctr32` leaves
`CIPH_K(little_endian_uint32(i) ‖ nonce)`, of which the first 8 bytes are
kept at `W + 16 + 8 i`: after the loop, the halves of `derive_keys`
(`derive_ok`, `DInv.keys`).
-/

@[expose] public section

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
theorem derArgs_ok {p : Prm} {t : State} (E : Env p t) {i : Nat} (h27 : t.gpr .x27 = BitVec.ofNat 64 i) :
    ∃ t₁ : State, runBlock isa deriveBlock t = some t₁ ∧ t₁.mem = derMem t.mem p.W p.N i ∧
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
  · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, derMem, Proof.Cmac.store4, Mem.writeW,
      BitVec.setWidth_eq, setWidth_rt32, read4_readW, h27, add_ofNat_assoc, Nat.reduceAdd, Nat.reduceDiv, movz0]
  · simp [gpr_write, E.x21]
  · simp [gpr_write, E.x22]
  · simp [gpr_write, E.x19]
  · simp [gpr_write, E.x19]
  · simp [gpr_write]
  · simp [gpr_write, E.x19]

theorem zc₁ (W : Addr) : (⟨W + BitVec.ofNat 64 224, 16⟩ : Region).Contains (W + BitVec.ofNat 64 224) (64 / 8) :=
  contains_at0 _ (by decide) (by decide)

theorem zc₂ (W : Addr) : (⟨W + BitVec.ofNat 64 224, 16⟩ : Region).Contains (W + BitVec.ofNat 64 232) (64 / 8) := by
  rw [show W + BitVec.ofNat 64 232 = W + BitVec.ofNat 64 224 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc]]
  exact contains_at _ (show 8 + 8 ≤ 16 by decide) (by decide)

/-- The counter block of a step: `little_endian_uint32(i) ‖ nonce`. -/
theorem derBlock_bytes (m : Mem) (W N : Addr) (i : Nat) :
    bytesAt (derMem m W N i) (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt m N 12 := by
  have c₁ := zc₁ W
  have c₂ := zc₂ W
  rw [derMem, Proof.AesGcm.AArch64.bytesAt_frame
      (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide),
    Proof.Cmac.bytesAt_store4, GcmSiv.le4_le32, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    show (12 : Nat) = 4 + (4 + 4) from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, add_ofNat_assoc]
  simp only [List.append_assoc]

/-- The zero block of a step. -/
theorem derZero_block (W N : Addr) (m : Mem) (i : Nat) :
    Spec.Gcm.blockAt (derMem m W N i) (W + BitVec.ofNat 64 224) = 0 := by
  rw [derMem, Spec.Gcm.blockAt, show W + BitVec.ofNat 64 232 = W + BitVec.ofNat 64 224 + BitVec.ofNat 64 8 by
    rw [add_ofNat_assoc], Proof.Cmac.bytesAt_store2]
  decide

theorem derMem_frame (m : Mem) (W N : Addr) (i : Nat) :
    Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 16⟩] m (derMem m W N i) :=
  (((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp).writeW
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (zc₁ W)).writeW
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (zc₂ W)

/-- What `derive` writes. -/
abbrev derR (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 48⟩, ⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 16⟩,
    ⟨W + BitVec.ofNat 64 1760, 2048⟩]

/-- After `i` steps of `derive` from `σ`: the first `8 i` bytes of the halves
at `W + 16`. -/
structure DInv (p : Prm) (σ : State) (i : Nat) (t : State) : Prop where
  env : Env p t
  x27 : t.gpr .x27 = BitVec.ofNat 64 i
  le : i ≤ p.R / 2 - 1
  frame : Frame (derR p.W) σ.mem t.mem
  out : bytesAt t.mem (p.W + BitVec.ofNat 64 16) (8 * i) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem p.K p.R) (bytesAt σ.mem p.N 12) i

/-- The code after the call of a step. -/
theorem derPost_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {i : Nat} (hi : i < p.R / 2 - 1)
    (h27 : t.gpr .x27 = BitVec.ofNat 64 i) :
    ∃ t' : State, runBlock isa derivePost t = some t' ∧
      t'.mem = t.mem.writeW (p.W + BitVec.ofNat 64 (16 + 8 * i)) (t.mem.readW (p.W + BitVec.ofNat 64 224) 64) ∧
      t'.gpr .x27 = BitVec.ofNat 64 (i + 1) ∧ t'.gpr .x10 = BitVec.ofNat 64 (p.R / 2 - 1 - (i + 1)) ∧
      Others [.x9, .x10, .x27] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR := L.rounds
  have rb := E.perm.wR (show 224 + 8 ≤ 3808 by decide)
  have wo := E.perm.wW (d := 16 + 8 * i) (n := 8) (by omega_arith)
  have ea : p.W + BitVec.ofNat 64 i <<< 3 + BitVec.ofNat 64 16 = p.W + BitVec.ofNat 64 (16 + 8 * i) := by
    rw [ofNat_lsl, add_ofNat_assoc]; congr 2; omega_arith
  rw [← ea] at wo
  refine ⟨_, by simp only [derivePost]; grun [E.x19, E.x22, h27, rb, wo], ?_⟩
  refine ⟨?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
  · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, Mem.writeW, BitVec.setWidth_eq,
      read8_readW, ea]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27, ofNat_add_ofNat]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27, ofNat_add_ofNat, E.x22]
    rw [lsr_ofNat _ _ (by omega_arith), ofNat_sub (by omega_arith) (by omega_arith), ofNat_sub (by omega_arith) (by omega_arith)]

/-- Buffers outside `W` are kept by `derive`. -/
theorem bytesAt_derR {p : Prm} (_L : Lay p) {P : Addr} {len : Nat} (hP : (⟨P, len⟩ : Region).Disjoint ⟨p.W, 3808⟩)
    (hl : len ≤ 2 ^ 64) {m m' : Mem} (hf : Frame (derR p.W) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hP.sub_right (Lay.wSub (by decide))) hl

/-- The key schedule is kept by `derive`. -/
theorem ciph_derR {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (derR p.W) m m') :
    Spec.GcmSiv.ctxCiph m' p.K p.R = Spec.GcmSiv.ctxCiph m p.K p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_derR L (L.k_w.sub_left (Region.sub_prefix L.rounds_le)) (by have := L.rounds_le; omega_arith) hf]

/-- The arguments of a step's call. -/
theorem derCall {p : Prm} (L : Lay p) {t₁ : State} (E₁ : Env p t₁) (x0 : t₁.gpr .x0 = p.K)
    (x1 : t₁.gpr .x1 = BitVec.ofNat 64 p.R) (x2 : t₁.gpr .x2 = p.W + BitVec.ofNat 64 112)
    (x3 : t₁.gpr .x3 = p.W + BitVec.ofNat 64 224) (x4 : t₁.gpr .x4 = BitVec.ofNat 64 1)
    (x5 : t₁.gpr .x5 = p.W + BitVec.ofNat 64 1760) :
    CtrCall t₁ p.K (p.W + BitVec.ofNat 64 112) (p.W + BitVec.ofNat 64 224) (p.W + BitVec.ofNat 64 1760) p.R 1 :=
  { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5
    rounds := L.rounds3
    wrap := by rw [L.toNat_W (by decide)]; have := L.ww; omega_arith
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
theorem derStep_ok (v : GcmImpl) {p : Prm} (L : Lay p) {σ : State} {i : Nat} (hi : i < p.R / 2 - 1) {t : State}
    (I : DInv p σ i t) :
    WP isa (.seq (.block deriveBlock) (.seq (callCtr v.callees) (.block derivePost))) t fun t' =>
      DInv p σ (i + 1) t' ∧ t'.gpr .x10 = BitVec.ofNat 64 (p.R / 2 - 1 - (i + 1)) := by
  have hR := L.rounds
  have hw := L.ww
  have eN : bytesAt t.mem p.N 12 = bytesAt σ.mem p.N 12 := bytesAt_derR L L.n_w (by decide) I.frame
  have eK : Spec.GcmSiv.ctxCiph t.mem p.K p.R = Spec.GcmSiv.ctxCiph σ.mem p.K p.R := ciph_derR L I.frame
  obtain ⟨t₁, run₁, hm₁, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := derArgs_ok I.env I.x27
  have E₁ : Env p t₁ := I.env.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have cc := derCall L E₁ x0 x1 x2 x3 x4 x5
  have hb₁ : bytesAt t₁.mem (p.W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt t.mem p.N 12 := by
    rw [hm₁]; exact derBlock_bytes _ _ _ _
  have hz₁ : Spec.Gcm.blockAt t₁.mem (p.W + BitVec.ofNat 64 224) = 0 := by rw [hm₁]; exact derZero_block _ _ _ _
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 112, 16⟩, ⟨p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by
    rw [hm₁]; exact derMem_frame _ _ _ _
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_)
  have E₂ : Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have h27₂ : t₂.gpr .x27 = BitVec.ofNat 64 i := by rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), I.x27]
  obtain ⟨t₃, run₃, hm₃, x27₃, x10₃, ho₃, sp₃, rd₃, wr₃⟩ := derPost_ok L E₂ hi h27₂
  refine WP.of_runBlock ⟨t₃, run₃, ⟨E₂.keep (fun r hr => ho₃ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃, x27₃, by omega_arith, ?_, ?_⟩,
    x10₃⟩
  · -- The frame.
    have fc := P.frame
    refine (I.frame.trans (f₁.sub fun r hr => ?_)).trans ((fc.sub fun r hr => ?_).trans (by
        rw [hm₃]
        exact (Frame.refl _ _).writeW (List.mem_cons_self) _ (Offset.contains p.W (d := 16 + 8 * i) (n := 8)
          (e := 16) (k := 48) (by omega_arith) (by omega_arith) (by omega_arith))))
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
      fun h₁ h₂ => L.w_w (by omega_arith) (by omega_arith) h₁
    have keep : bytesAt t₃.mem (p.W + BitVec.ofNat 64 16) (8 * i) =
        bytesAt t.mem (p.W + BitVec.ofNat 64 16) (8 * i) := by
      rw [hm₃, Proof.AesGcm.AArch64.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Region.contains_self (p.W + BitVec.ofNat 64 (16 + 8 * i)) 8))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW (by omega_arith) (by omega_arith)) (by omega_arith),
        Proof.AesGcm.AArch64.bytesAt_frame fc (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact dW (by decide) (by omega_arith)) (by omega_arith),
        Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact dW (by decide) (by omega_arith)) (by omega_arith)]
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
          (by omega_arith)]
      rw [hm₃, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_readW,
        show bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 8 = (bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 16).take 8 by
          rw [e16, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)],
        Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt, hb₁,
        Proof.Cmac.aesWith_bytes _ _ (by rw [List.length_append, Proof.Cmac.bytesAt_length]; rfl),
        ← GcmSiv.aesWith_eq, show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem p.K (16 * (p.R + 1))) =
          Spec.GcmSiv.ctxCiph t₁.mem p.K p.R from rfl, ek₁, eK, eN]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega_arith, Proof.Cmac.bytesAt_add, GcmSiv.halves_succ, ← I.out, keep,
      add_ofNat_assoc, last]

/-- `derive`: the halves of `derive_keys` at `W + 16`. -/
theorem derive_ok (v : GcmImpl) {p : Prm} (L : Lay p) {σ : State} (E : Env p σ) :
    WP isa (derive v.callees) σ (DInv p σ (p.R / 2 - 1)) := by
  have hR := L.rounds
  refine WP.seq (WP.run (Q := fun t => DInv p σ 0 t) ⟨_, by grun [], ?_⟩ fun t I₀ => ?_)
  · exact ⟨E.keep (fun r hr => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
      by simp [gpr_write], Nat.zero_le _, by rw [mem_write]; exact Frame.refl _ _, rfl⟩
  refine WP.loop (M := isa) (fun m t => ∃ i, m = (p.R / 2 - 1) - i ∧ i < p.R / 2 - 1 ∧ DInv p σ i t) ?_
    ((p.R / 2 - 1) - 0) _ ⟨0, rfl, by omega_arith, I₀⟩
  rintro m t ⟨i, rfl, hi, I⟩
  refine WP.mono (derStep_ok v L hi I) fun t' ⟨I', h10⟩ => ?_
  have ev := eval_nonzero h10 (by omega_arith)
  by_cases he : i + 1 = p.R / 2 - 1
  · left; exact ⟨ev.trans (by simp [he]), he ▸ I'⟩
  · right; exact ⟨ev.trans (by simp; omega_arith), (p.R / 2 - 1) - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, I'⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DInv.keys {p : Prm} (L : Lay p) {σ t : State} (I : DInv p σ (p.R / 2 - 1) t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem p.K p.R) (Spec.GcmSiv.keyLen p.R) (bytesAt σ.mem p.N 12) =
      (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16,
        bytesAt t.mem (p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R)) := by
  have hR := L.rounds
  have hk : Spec.GcmSiv.keyLen p.R / 8 + 2 = p.R / 2 - 1 := by unfold Spec.GcmSiv.keyLen; omega_arith
  have hl : 8 * (p.R / 2 - 1) = 16 + Spec.GcmSiv.keyLen p.R := by unfold Spec.GcmSiv.keyLen; omega_arith
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, add_ofNat_assoc] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem p.K p.R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesGcmSiv.AArch64
