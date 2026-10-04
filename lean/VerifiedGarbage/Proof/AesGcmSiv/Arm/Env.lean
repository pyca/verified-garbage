import VerifiedGarbage.Proof.AesGcmSiv.Arm.Contract
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.AesGcm.Arm.Callee
import VerifiedGarbage.Impl.AesGcmSiv.Arm

/-!
# AES-GCM-SIV on ARMv7: where everything is

Untrusted: everything here is checked by Lean. The public arguments
(`Prm`): the key schedule of the key-generating key (240 bytes at `K`), the
working space (4096 bytes at `W`), the nonce (12 bytes at `N`), the
additional data (`al` bytes at `A`), the data (`n` bytes at `D`), the stack
pointer and the number of rounds, all 32-bit; how their regions lie, apart
from each other, from the stack arguments (16 bytes at `SP`) and from the 8
bytes below `SP` that the calls' frames use (`Lay`); what a state may access
(`Perm`); the registers that hold some of them throughout (`Env`), which the
functions called preserve; and the stack arguments `aad_len`, `data` and
`len` (`Args`), which nothing writes. `srun` runs a block symbolically.
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
    Impl.AesGcmSiv.Arm.t2O, Impl.AesGcmSiv.Arm.skO, Impl.AesGcmSiv.Arm.revO, Impl.AesGcmSiv.Arm.ghO,
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
  /-- The stack pointer. -/
  SP : BitVec 32
  /-- The number of rounds. -/
  R : Nat
  /-- The length of the additional data. -/
  al : Nat
  /-- The length of the data. -/
  n : Nat

/-- The stack arguments. -/
abbrev argR (SP : BitVec 32) : Region := ⟨State.addr SP, 16⟩

/-- How the regions lie. -/
structure Lay (p : Prm) : Prop where
  kw : p.K.toNat + 240 ≤ 2 ^ 32
  ww : p.W.toNat + 4096 ≤ 2 ^ 32
  nw : p.N.toNat + 12 ≤ 2 ^ 32
  aw : p.A.toNat + p.al ≤ 2 ^ 32
  dw : p.D.toNat + p.n ≤ 2 ^ 32
  al_lt : p.al < 2 ^ 32
  n_lt : p.n < 2 ^ 32
  sp8 : 8 ≤ p.SP.toNat
  spf : p.SP.toNat + 16 ≤ 2 ^ 32
  k_w : (⟨State.addr p.K, 240⟩ : Region).Disjoint ⟨State.addr p.W, 4096⟩
  k_d : (⟨State.addr p.K, 240⟩ : Region).Disjoint ⟨State.addr p.D, p.n⟩
  n_w : (⟨State.addr p.N, 12⟩ : Region).Disjoint ⟨State.addr p.W, 4096⟩
  n_d : (⟨State.addr p.N, 12⟩ : Region).Disjoint ⟨State.addr p.D, p.n⟩
  a_w : (⟨State.addr p.A, p.al⟩ : Region).Disjoint ⟨State.addr p.W, 4096⟩
  a_d : (⟨State.addr p.A, p.al⟩ : Region).Disjoint ⟨State.addr p.D, p.n⟩
  d_w : (⟨State.addr p.D, p.n⟩ : Region).Disjoint ⟨State.addr p.W, 4096⟩
  d_args : (⟨State.addr p.D, p.n⟩ : Region).Disjoint (argR p.SP)
  w_args : (⟨State.addr p.W, 4096⟩ : Region).Disjoint (argR p.SP)
  bk : (below p.SP).Disjoint ⟨State.addr p.K, 240⟩
  bn : (below p.SP).Disjoint ⟨State.addr p.N, 12⟩
  ba : (below p.SP).Disjoint ⟨State.addr p.A, p.al⟩
  bd : (below p.SP).Disjoint ⟨State.addr p.D, p.n⟩
  bw : (below p.SP).Disjoint ⟨State.addr p.W, 4096⟩
  rounds : p.R = 10 ∨ p.R = 14

/-- What a state may access. -/
structure Perm (p : Prm) (s : State) : Prop where
  k : Covers [⟨State.addr p.K, 240⟩] (s.rd ++ s.wr)
  non : Covers [⟨State.addr p.N, 12⟩] (s.rd ++ s.wr)
  aad : Covers [⟨State.addr p.A, p.al⟩] (s.rd ++ s.wr)
  d : Covers [⟨State.addr p.D, p.n⟩] s.wr
  w : Covers [⟨State.addr p.W, 4096⟩] s.wr
  args : Covers [argR p.SP] (s.rd ++ s.wr)
  /-- Nothing the state may write overlaps the stack arguments. -/
  argw : ∀ r ∈ s.wr, (argR p.SP).Disjoint r

theorem Perm.of_eq {p : Prm} {s s' : State} (h : Perm p s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm p s' := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  exact ⟨by rw [hrd, hwr]; exact a, by rw [hrd, hwr]; exact b, by rw [hrd, hwr]; exact c, by rw [hwr]; exact d,
    by rw [hwr]; exact e, by rw [hrd, hwr]; exact f, by rw [hwr]; exact g⟩

/-- The registers holding some of the public arguments, the stack pointer,
and what the state may access. -/
structure Env (p : Prm) (s : State) : Prop where
  r7 : s.gpr .r7 = p.A
  r8 : s.gpr .r8 = BitVec.ofNat 32 p.R
  r9 : s.gpr .r9 = p.K
  r10 : s.gpr .r10 = p.N
  r11 : s.gpr .r11 = p.W
  sp : s.sp = p.SP
  perm : Perm p s

/-- The registers `Env` pins. -/
abbrev envRegs : List Reg := [.r7, .r8, .r9, .r10, .r11]

/-- An environment, after code that keeps `r7`–`r11`, the stack pointer and
the permissions. -/
theorem Env.keep {p : Prm} {s s' : State} (h : Env p s) (hg : ∀ r ∈ envRegs, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env p s' :=
  ⟨by rw [hg _ (by simp), h.r7], by rw [hg _ (by simp), h.r8], by rw [hg _ (by simp), h.r9],
    by rw [hg _ (by simp), h.r10], by rw [hg _ (by simp), h.r11], by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after a call. -/
theorem Env.of_saved {p : Prm} {s s' : State} (h : Env p s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env p s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

/-- An environment, after code that writes only the registers `rs`. -/
theorem Env.of_others {p : Prm} {s s' : State} {rs : List Reg} (h : Env p s) (ho : Others rs s s')
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hd : ∀ r ∈ envRegs, r ∉ rs := by decide) :
    Env p s' :=
  h.keep (fun r h' => ho r (hd r h')) hsp hrd hwr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 4096) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 4096⟩ :=
  Offset.sub_base _ h

variable {p : Prm} (L : Lay p)
include L

/-- An offset into `W`, as a 64-bit address. -/
theorem wA {d : Nat} (hd : d < 4096) : State.addr (p.W + BitVec.ofNat 32 d) = State.addr p.W + BitVec.ofNat 64 d :=
  addr_add (by have := L.ww; omega)

theorem wN {d : Nat} (hd : d < 4096) : (p.W + BitVec.ofNat 32 d).toNat = p.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 4096) (hd : d + k ≤ 4096) :
    (⟨State.addr p.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem k_w' {d k : Nat} (hd : d + k ≤ 4096) :
    (⟨State.addr p.K, 240⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (wSub hd)

theorem n_w' {d k : Nat} (hd : d + k ≤ 4096) :
    (⟨State.addr p.N, 12⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.n_w.sub_right (wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 4096) :
    (⟨State.addr p.A, p.al⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 4096) :
    (⟨State.addr p.D, p.n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (wSub hd)

theorem bw' {d k : Nat} (hd : d + k ≤ 4096) : (below p.SP).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.bw.sub_right (wSub hd)

theorem args_w' {d k : Nat} (hd : d + k ≤ 4096) : (argR p.SP).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.w_args.symm.sub_right (wSub hd)

/-- The stack arguments lie above the stack below `SP`. -/
theorem args_below : (argR p.SP).Disjoint (below p.SP) :=
  Offset.base_disjoint_below (State.addr p.SP) (n := 8) (k := 16) (by have := L.spf; omega)

theorem rounds_le : 16 * (p.R + 1) ≤ 240 := by rcases L.rounds with h | h <;> rw [h] <;> decide

theorem rounds3 : p.R = 10 ∨ p.R = 12 ∨ p.R = 14 := by rcases L.rounds with h | h <;> simp [h]

theorem toNat_R : (BitVec.ofNat 32 p.R).toNat = p.R := by
  rcases L.rounds with h | h <;> rw [h] <;> rfl

theorem ofNat_R_lt : p.R < 2 ^ 32 := by rcases L.rounds with h | h <;> rw [h] <;> decide

end Lay

namespace Perm

variable {p : Prm} {s : State} (P : Perm p s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 4096) : InRegions s.wr (State.addr p.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 4096) : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 4096) : Covers [⟨State.addr p.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 4096) : Covers [⟨State.addr p.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_left (P.wC h)

/-- The first 2560 bytes of `W`, where AES-GCM's save area is. -/
theorem w2560 : Covers [⟨State.addr p.W, 2560⟩] s.wr := covers_prefix P.w (by decide)

theorem nR {d k : Nat} (h : d + k ≤ 12) : InRegions (s.rd ++ s.wr) (State.addr p.N + BitVec.ofNat 64 d) k :=
  in_off P.non h (by decide)

end Perm

/-! ## The stack arguments -/

/-- The stack arguments `aad_len`, `data` and `len` in the memory `m`. -/
structure Args (p : Prm) (m : Mem) : Prop where
  a0 : m.readW (State.addr (p.SP + BitVec.ofNat 32 0)) 32 = BitVec.ofNat 32 p.al
  a4 : m.readW (State.addr (p.SP + BitVec.ofNat 32 4)) 32 = p.D
  a8 : m.readW (State.addr (p.SP + BitVec.ofNat 32 8)) 32 = BitVec.ofNat 32 p.n

theorem argA {p : Prm} (L : Lay p) {k : Nat} (hk : k < 16) :
    State.addr (p.SP + BitVec.ofNat 32 k) = State.addr p.SP + BitVec.ofNat 64 k :=
  addr_add (by have := L.spf; omega)

/-- The stack arguments, after writes apart from them. -/
theorem Args.frame {p : Prm} (L : Lay p) {m m' : Mem} (h : Args p m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (argR p.SP).Disjoint r) : Args p m' := by
  have e : ∀ k, k + 4 ≤ 16 → m'.readW (State.addr (p.SP + BitVec.ofNat 32 k)) 32 =
      m.readW (State.addr (p.SP + BitVec.ofNat 32 k)) 32 := fun k hk => by
    rw [argA L (by omega)]
    exact hf.readW (r := ⟨State.addr p.SP + BitVec.ofNat 64 k, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)
  exact ⟨by rw [e 0 (by decide), h.a0], by rw [e 4 (by decide), h.a4], by rw [e 8 (by decide), h.a8]⟩

/-- A stack argument may be read. -/
theorem Perm.argR' {p : Prm} {s : State} (P : Perm p s) (L : Lay p) {k : Nat} (hk : k + 4 ≤ 16) :
    InRegions (s.rd ++ s.wr) (State.addr (p.SP + BitVec.ofNat 32 k)) 4 := by
  rw [argA L (by omega)]; exact in_off P.args hk (by decide)

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
  simpa using contains_at p (d := 0) (by omega : 0 + n ≤ k) hk

end VG.Proof.AesGcmSiv.Arm
