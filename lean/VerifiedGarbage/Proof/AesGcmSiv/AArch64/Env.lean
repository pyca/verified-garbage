import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.Save
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Impl.AesGcmSiv.AArch64

/-!
# AES-GCM-SIV on AArch64: where everything is

Untrusted: everything here is checked by Lean. The public arguments
(`Prm`): the key schedule of the key-generating key (240 bytes at `K`), the
working space (4096 bytes at `W`), the nonce (12 bytes at `N`), the
additional data (`al` bytes at `A`), the data (`n` bytes at `D`), the stack
pointer and the number of rounds; how their regions lie (`Lay`); what a
state may access (`Perm`); and the registers that hold them throughout
(`Env`), which the functions called preserve. `grun` runs a block
symbolically.
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
    cbO, ccO, bO, t2O, skO, revO, ghO, scrO, List.cons_append, List.nil_append,
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
  ww : p.W.toNat + 4096 ≤ 2 ^ 64
  nw : p.N.toNat + 12 ≤ 2 ^ 64
  aw : p.A.toNat + p.al ≤ 2 ^ 64
  dw : p.D.toNat + p.n ≤ 2 ^ 64
  k_w : (⟨p.K, 240⟩ : Region).Disjoint ⟨p.W, 4096⟩
  k_d : (⟨p.K, 240⟩ : Region).Disjoint ⟨p.D, p.n⟩
  n_w : (⟨p.N, 12⟩ : Region).Disjoint ⟨p.W, 4096⟩
  n_d : (⟨p.N, 12⟩ : Region).Disjoint ⟨p.D, p.n⟩
  a_w : (⟨p.A, p.al⟩ : Region).Disjoint ⟨p.W, 4096⟩
  a_d : (⟨p.A, p.al⟩ : Region).Disjoint ⟨p.D, p.n⟩
  d_w : (⟨p.D, p.n⟩ : Region).Disjoint ⟨p.W, 4096⟩
  rounds : p.R = 10 ∨ p.R = 14
  al_lt : p.al < 2 ^ 64
  n_lt : p.n < 2 ^ 64

/-- What a state may access. -/
structure Perm (p : Prm) (s : State) : Prop where
  k : Covers [⟨p.K, 240⟩] (s.rd ++ s.wr)
  non : Covers [⟨p.N, 12⟩] (s.rd ++ s.wr)
  aad : Covers [⟨p.A, p.al⟩] (s.rd ++ s.wr)
  d : Covers [⟨p.D, p.n⟩] s.wr
  w : Covers [⟨p.W, 4096⟩] s.wr

theorem Perm.of_eq {p : Prm} {s s' : State} (h : Perm p s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm p s' := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨by rw [hrd, hwr]; exact a, by rw [hrd, hwr]; exact b, by rw [hrd, hwr]; exact c, by rw [hwr]; exact d,
    by rw [hwr]; exact e⟩

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

/-- An environment, after a block that writes only the registers `rs`. -/
theorem Env.of_regs {p : Prm} {s s' : State} {rs : List Reg} (h : Env p s) (hr : Regs rs s s')
    (hd : ∀ r ∈ envRegs, r ∉ rs := by decide) : Env p s' :=
  h.keep (fun r h' => hr.others r (hd r h')) hr.sp hr.rd hr.wr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 4096) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 4096⟩ :=
  Offset.sub_base _ h

variable {p : Prm} (L : Lay p)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 4096) (hd : d + k ≤ 4096) :
    (⟨p.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem k_w' {d k : Nat} (hd : d + k ≤ 4096) : (⟨p.K, 240⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (wSub hd)

theorem n_w' {d k : Nat} (hd : d + k ≤ 4096) : (⟨p.N, 12⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.n_w.sub_right (wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 4096) : (⟨p.A, p.al⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 4096) : (⟨p.D, p.n⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (wSub hd)

theorem toNat_W {d : Nat} (hd : d < 4096) : (p.W + BitVec.ofNat 64 d).toNat = p.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem rounds_le : 16 * (p.R + 1) ≤ 240 := by rcases L.rounds with h | h <;> rw [h] <;> decide

theorem rounds3 : p.R = 10 ∨ p.R = 12 ∨ p.R = 14 := by rcases L.rounds with h | h <;> simp [h]

end Lay

/-- `W` itself, as the part at offset 0. -/
theorem Lay.w0 {p : Prm} (_L : Lay p) : p.W + BitVec.ofNat 64 0 = p.W := BitVec.add_zero _

namespace Perm

variable {p : Prm} {s : State} (P : Perm p s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 4096) : InRegions s.wr (p.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 4096) : InRegions (s.rd ++ s.wr) (p.W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 4096) : Covers [⟨p.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 4096) : Covers [⟨p.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
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
    (⟨p, k⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := Offset.contains_base p h (by omega)

theorem contains_at0 (p : Addr) {n k : Nat} (h : n ≤ k) (hk : k < 2 ^ 64) :
    (⟨p, k⟩ : Region).Contains p n := by
  simpa using contains_at p (d := 0) (by omega : 0 + n ≤ k) hk

/-- A block that writes only registers, with what is known of its result. -/
theorem WP.regs {is : List Instr} {s : State} {Q : State → Prop} {s' : State}
    (h : runBlock isa is s = some s') (hq : Q s') : WP isa (.block is) s Q := WP.of_runBlock ⟨s', h, hq⟩

end VG.Proof.AesGcmSiv.AArch64
