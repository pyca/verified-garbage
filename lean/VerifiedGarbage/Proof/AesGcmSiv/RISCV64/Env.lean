module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM-SIV on RISC-V: where everything is

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/Env.lean`): the public values of a call (`Cx`):
the key schedule of the key-generating key (240 bytes at `K`), the working
space (3840 bytes at `W`), the nonce (12 bytes at `N`), the additional data
(`al` bytes at `A`), the data (`n` bytes at `D`), the tag (16 bytes at `T`),
the number of rounds and the stack pointer `SP`, below which `vg_ghash`'s
frame takes 2048 bytes; what the precondition says of them (`Lay`); what a
state may access (`Perm`); and the registers holding them throughout
(`Env`), which the functions called preserve. What a piece keeps of the
registers is `PK`.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.RISCV64
open VG.Proof.AesGcm.RISCV64 (covers_off in_off covers_prefix)

/-! ## The public values -/

/-- The public values of a call of `seal` or `open`. -/
structure Cx where
  K : Addr
  W : Addr
  N : Addr
  A : Addr
  D : Addr
  T : Addr
  SP : Addr
  R : Nat
  al : Nat
  n : Nat

/-- What the precondition says of the public values. -/
structure Lay (c : Cx) : Prop where
  kw : c.K.toNat + 240 ≤ 2 ^ 64
  ww : c.W.toNat + 3840 ≤ 2 ^ 64
  nw : c.N.toNat + 12 ≤ 2 ^ 64
  aw : c.A.toNat + c.al ≤ 2 ^ 64
  dw : c.D.toNat + c.n ≤ 2 ^ 64
  tw : c.T.toNat + 16 ≤ 2 ^ 64
  k_w : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.W, 3840⟩
  k_d : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.D, c.n⟩
  n_w : (⟨c.N, 12⟩ : Region).Disjoint ⟨c.W, 3840⟩
  n_d : (⟨c.N, 12⟩ : Region).Disjoint ⟨c.D, c.n⟩
  a_w : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.W, 3840⟩
  a_d : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.D, c.n⟩
  d_w : (⟨c.D, c.n⟩ : Region).Disjoint ⟨c.W, 3840⟩
  t_w : (⟨c.T, 16⟩ : Region).Disjoint ⟨c.W, 3840⟩
  t_d : (⟨c.T, 16⟩ : Region).Disjoint ⟨c.D, c.n⟩
  rounds : c.R = 10 ∨ c.R = 14
  n_lt : c.n < 2 ^ 64
  al_lt : c.al < 2 ^ 64
  wal : c.W.toNat % 8 = 0
  spal : c.SP.toNat % 16 = 0
  spge : 2048 ≤ c.SP.toNat
  b_w : (below c.SP 2048).Disjoint ⟨c.W, 3840⟩
  b_a : (below c.SP 2048).Disjoint ⟨c.A, c.al⟩
  b_d : (below c.SP 2048).Disjoint ⟨c.D, c.n⟩

/-- What a state may access. -/
structure Perm (c : Cx) (s : State) : Prop where
  k : Covers [⟨c.K, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨c.W, 3840⟩] s.wr
  nc : Covers [⟨c.N, 12⟩] (s.rd ++ s.wr)
  a : Covers [⟨c.A, c.al⟩] (s.rd ++ s.wr)
  d : Covers [⟨c.D, c.n⟩] s.wr
  t : Covers [⟨c.T, 16⟩] (s.rd ++ s.wr)

theorem Perm.of_eq {c : Cx} {s s' : State} (h : Perm c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm c s' :=
  ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w, by rw [hrd, hwr]; exact h.nc,
    by rw [hrd, hwr]; exact h.a, by rw [hwr]; exact h.d, by rw [hrd, hwr]; exact h.t⟩

/-- Where the nonce's copy is. -/
def nP (W : Addr) : Addr := W + BitVec.ofNat 64 1520

/-! ## What the pieces keep -/

/-- The registers the pieces keep: those holding the public values. -/
def keepRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8]

/-- What a piece keeps. -/
structure PK (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  gpr : ∀ r ∈ keepRegs, s'.gpr r = s.gpr r

theorem PK.refl (s : State) : PK s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem PK.trans {s t u : State} (h₁ : PK s t) (h₂ : PK t u) : PK s u :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr)⟩

theorem PK.ofUpd {s t : State} {d : Reg} {v : BitVec 64} (u : Steps.Upd s t d v)
    (hd : d ∉ keepRegs := by decide) : PK s t :=
  ⟨u.rd, u.wr, u.sp, fun r hr => u.other r fun h => hd (h ▸ hr)⟩

theorem PK.ofMupd {s t : State} {m : Mem} (u : Steps.Mupd s t m) : PK s t :=
  ⟨u.rd, u.wr, u.sp, fun r _ => by rw [u.gpr]⟩

theorem keep_preserved : ∀ r ∈ keepRegs, r ∈ preserved := by decide

/-- After a call, which keeps the callee-saved registers. -/
theorem PK.ofSaved {s t : State} (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hs : ∀ r ∈ preserved, t.gpr r = s.gpr r) : PK s t :=
  ⟨hrd, hwr, hsp, fun r hr => hs r (keep_preserved r hr)⟩

/-! ## The environment -/

/-- The registers holding the public values throughout, the stack pointer,
and what the state may access. -/
structure Env (c : Cx) (s : State) : Prop where
  s0 : s.gpr .s0 = c.W
  s1 : s.gpr .s1 = c.N
  s2 : s.gpr .s2 = c.K
  s3 : s.gpr .s3 = BitVec.ofNat 64 c.R
  s4 : s.gpr .s4 = c.A
  s5 : s.gpr .s5 = BitVec.ofNat 64 c.al
  s6 : s.gpr .s6 = c.D
  s7 : s.gpr .s7 = BitVec.ofNat 64 c.n
  s8 : s.gpr .s8 = c.T
  sp : s.sp = c.SP
  perm : Perm c s

theorem Env.of_pk {c : Cx} {s s' : State} (h : Env c s) (k : PK s s') : Env c s' :=
  ⟨by rw [k.gpr .s0 (by decide), h.s0], by rw [k.gpr .s1 (by decide), h.s1],
    by rw [k.gpr .s2 (by decide), h.s2], by rw [k.gpr .s3 (by decide), h.s3],
    by rw [k.gpr .s4 (by decide), h.s4], by rw [k.gpr .s5 (by decide), h.s5],
    by rw [k.gpr .s6 (by decide), h.s6], by rw [k.gpr .s7 (by decide), h.s7],
    by rw [k.gpr .s8 (by decide), h.s8], k.sp.trans h.sp, h.perm.of_eq k.rd k.wr⟩

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 3840) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 3840⟩ :=
  Offset.sub_base _ h

variable {c : Cx} (L : Lay c)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 3840) (hd : d + k ≤ 3840) :
    (⟨c.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

omit L in
/-- `W` and a part of it. -/
theorem w0_w {n d k : Nat} (h : n ≤ d) (hd : d + k ≤ 3840) :
    (⟨c.W, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.base_disjoint _ h (by omega)

theorem k_w' {d k : Nat} (hd : d + k ≤ 3840) : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (wSub hd)

theorem n_w' {d k : Nat} (hd : d + k ≤ 3840) : (⟨c.N, 12⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.n_w.sub_right (wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 3840) : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 3840) : (⟨c.D, c.n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (wSub hd)

theorem t_w' {d k : Nat} (hd : d + k ≤ 3840) : (⟨c.T, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.t_w.sub_right (wSub hd)

theorem b_w' {d k : Nat} (hd : d + k ≤ 3840) : (below c.SP 2048).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.b_w.sub_right (wSub hd)

theorem wrapW {d : Nat} (hd : d < 3840) : (c.W + BitVec.ofNat 64 d).toNat = c.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- `W + d` is aligned for a multiple `d` of 8. -/
theorem wal8 {d : Nat} (hd : d < 3840) (h8 : d % 8 = 0) : (c.W + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [L.wrapW hd]; have := L.wal; omega

/-- `W + d` is aligned for a multiple `d` of 4. -/
theorem wal4 {d : Nat} (hd : d < 3840) (h4 : d % 4 = 0) : (c.W + BitVec.ofNat 64 d).toNat % 4 = 0 := by
  rw [L.wrapW hd]; have := L.wal; omega

theorem rb : 16 * (c.R + 1) ≤ 240 := by rcases L.rounds with h | h <;> rw [h] <;> decide

end Lay

namespace Perm

variable {c : Cx} {s : State} (P : Perm c s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 3840) : InRegions s.wr (c.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 3840) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 3840) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  Covers.right (P.wC h)

theorem wR {d n : Nat} (h : d + n ≤ 3840) : InRegions (s.rd ++ s.wr) (c.W + BitVec.ofNat 64 d) n :=
  P.wCR h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem nR {d n : Nat} (h : d + n ≤ 12) : InRegions (s.rd ++ s.wr) (c.N + BitVec.ofNat 64 d) n :=
  in_off P.nc h (by decide)

theorem tR {d n : Nat} (h : d + n ≤ 16) : InRegions (s.rd ++ s.wr) (c.T + BitVec.ofNat 64 d) n :=
  in_off P.t h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `len` bytes at `P` that the code may read, apart from `W`
and the stack below `SP`. -/
structure Buf (c : Cx) (s : State) (P : Addr) (len : Nat) : Prop where
  rd : Covers [⟨P, len⟩] (s.rd ++ s.wr)
  lt : len < 2 ^ 64
  wrap : P.toNat + len ≤ 2 ^ 64
  w : (⟨P, len⟩ : Region).Disjoint ⟨c.W, 3840⟩
  b : (below c.SP 2048).Disjoint ⟨P, len⟩

namespace Buf

variable {c : Cx} {s : State} {P : Addr} {len : Nat} (h : Buf c s P len)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Buf c s' P len :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ len) : Buf c s (P + BitVec.ofNat 64 k) (len - k) where
  rd := covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (P.toNat + k) (2 ^ 64)
    omega
  w := h.w.sub_left (Offset.sub_base P (by omega))
  b := h.b.sub_right (Offset.sub_base P (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ len) : Buf c s P k where
  rd := covers_prefix h.rd hk
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)
  b := h.b.sub_right (Region.sub_prefix hk)

theorem wd {d k : Nat} (hd : d + k ≤ 3840) : (⟨P, len⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  h.w.sub_right (Lay.wSub hd)

end Buf

/-- The additional data as a buffer. -/
theorem Lay.bufA {c : Cx} (L : Lay c) {s : State} (P : Perm c s) : Buf c s c.A c.al :=
  ⟨P.a, L.al_lt, L.aw, L.a_w, L.b_a⟩

/-- The data as a buffer. -/
theorem Lay.bufD {c : Cx} (L : Lay c) {s : State} (P : Perm c s) : Buf c s c.D c.n :=
  ⟨Covers.right P.d, L.n_lt, L.dw, L.d_w, L.b_d⟩

end VG.Proof.AesGcmSiv.RISCV64
