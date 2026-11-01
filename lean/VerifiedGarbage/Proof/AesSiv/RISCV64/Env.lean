module

public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-SIV on RISC-V: where everything is

Untrusted: everything here is checked by Lean. The public values of a call
of `encrypt` or `decrypt` (`Cx`): the key context (512 bytes at `C`), the
working space (2576 bytes at `W`), the `N` descriptors of the components of
associated data (16 bytes each at `A`), the data (`n` bytes at `D`), the
synthetic IV (16 bytes at `V`) and the number of rounds; what the
precondition says of them (`Lay`); what a state may access (`Perm`); and the
registers holding them throughout (`Env`), which the functions called
preserve. What a piece keeps of the registers is `PK`. The strings S2V
absorbs are buffers the code may read (`Buf`). As on PPC64LE
(`Proof/AesSiv/PPC64LE/Env.lean`), with the key context and `W` aligned
(`Lay.cal`, `Lay.wal`), as RISC-V's doubleword accesses need.
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.AesCcm.RISCV64 (covers_off in_off covers_prefix)

/-! ## The public values -/

/-- The public values of a call of `encrypt` or `decrypt`. -/
structure Cx where
  C : Addr
  W : Addr
  A : Addr
  D : Addr
  V : Addr
  R : Nat
  N : Nat
  n : Nat

/-- What the precondition says of the public values. -/
structure Lay (c : Cx) : Prop where
  cw : c.C.toNat + 512 ≤ 2 ^ 64
  ww : c.W.toNat + 2576 ≤ 2 ^ 64
  cal : c.C.toNat % 8 = 0
  wal : c.W.toNat % 8 = 0
  aw : c.A.toNat + 16 * c.N ≤ 2 ^ 64
  dw : c.D.toNat + c.n ≤ 2 ^ 64
  vw : c.V.toNat + 16 ≤ 2 ^ 64
  c_w : (⟨c.C, 512⟩ : Region).Disjoint ⟨c.W, 2576⟩
  c_d : (⟨c.C, 512⟩ : Region).Disjoint ⟨c.D, c.n⟩
  a_w : (⟨c.A, 16 * c.N⟩ : Region).Disjoint ⟨c.W, 2576⟩
  a_d : (⟨c.A, 16 * c.N⟩ : Region).Disjoint ⟨c.D, c.n⟩
  d_w : (⟨c.D, c.n⟩ : Region).Disjoint ⟨c.W, 2576⟩
  v_w : (⟨c.V, 16⟩ : Region).Disjoint ⟨c.W, 2576⟩
  v_d : (⟨c.V, 16⟩ : Region).Disjoint ⟨c.D, c.n⟩
  rounds : c.R = 10 ∨ c.R = 12 ∨ c.R = 14
  n_lt : c.n < 2 ^ 64

/-- What a state may access. -/
structure Perm (c : Cx) (s : State) : Prop where
  ctx : Covers [⟨c.C, 512⟩] (s.rd ++ s.wr)
  w : Covers [⟨c.W, 2576⟩] s.wr
  a : Covers [⟨c.A, 16 * c.N⟩] (s.rd ++ s.wr)
  d : Covers [⟨c.D, c.n⟩] s.wr
  v : Covers [⟨c.V, 16⟩] (s.rd ++ s.wr)

theorem Perm.of_eq {c : Cx} {s s' : State} (h : Perm c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm c s' :=
  ⟨by rw [hrd, hwr]; exact h.ctx, by rw [hwr]; exact h.w, by rw [hrd, hwr]; exact h.a,
    by rw [hwr]; exact h.d, by rw [hrd, hwr]; exact h.v⟩

/-! ## What the pieces keep -/

/-- The registers the pieces keep: the public values, and our caller's. -/
def keepRegs : List Reg :=
  [.s1, .s2, .s3, .s9, .s10, .s11]

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

theorem PK.ofUpd {s t : State} {d : Reg} {v : BitVec 64} (u : Upd s t d v)
    (hd : d ∉ keepRegs := by decide) : PK s t :=
  ⟨u.rd, u.wr, u.sp, fun r hr => u.other r fun h => hd (h ▸ hr)⟩

theorem PK.ofMupd {s t : State} {m : Mem} (u : Mupd s t m) : PK s t :=
  ⟨u.rd, u.wr, u.sp, fun r _ => by rw [u.gpr]⟩

theorem keep_preserved : ∀ r ∈ keepRegs, r ∈ preserved := by decide

/-- After a call, which keeps the callee-saved registers. -/
theorem PK.ofSaved {s t : State} (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hs : ∀ r ∈ preserved, t.gpr r = s.gpr r) : PK s t :=
  ⟨hrd, hwr, hsp, fun r hr => hs r (keep_preserved r hr)⟩

/-- After code that writes only the registers `rs`, none of `keepRegs`. -/
theorem PK.ofKeep {s t : State} {rs : List Reg} (h : Keep rs s t) (hsp : t.sp = s.sp)
    (hr : ∀ r ∈ keepRegs, r ∉ rs := by decide) : PK s t :=
  ⟨h.2.1, h.2.2, hsp, fun r hk => h.gpr (hr r hk)⟩

/-! ## The environment -/

/-- The registers holding the public values throughout, and what the state
may access. -/
structure Env (c : Cx) (s : State) : Prop where
  s1 : s.gpr .s1 = c.W
  s2 : s.gpr .s2 = c.C
  s3 : s.gpr .s3 = BitVec.ofNat 64 c.R
  s9 : s.gpr .s9 = c.D
  s10 : s.gpr .s10 = BitVec.ofNat 64 c.n
  s11 : s.gpr .s11 = c.V
  perm : Perm c s

theorem Env.of_pk {c : Cx} {s s' : State} (h : Env c s) (k : PK s s') : Env c s' :=
  ⟨by rw [k.gpr .s1 (by decide), h.s1], by rw [k.gpr .s2 (by decide), h.s2],
    by rw [k.gpr .s3 (by decide), h.s3], by rw [k.gpr .s9 (by decide), h.s9],
    by rw [k.gpr .s10 (by decide), h.s10], by rw [k.gpr .s11 (by decide), h.s11], h.perm.of_eq k.rd k.wr⟩

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2576) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2576⟩ :=
  Offset.sub_base _ h

theorem cSub {C : Addr} {d n : Nat} (h : d + n ≤ 512) : Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ ⟨C, 512⟩ :=
  Offset.sub_base _ h

variable {c : Cx} (L : Lay c)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2576) (hd : d + k ≤ 2576) :
    (⟨c.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

omit L in
/-- `W` and a part of it. -/
theorem w0_w {n d k : Nat} (h : n ≤ d) (hd : d + k ≤ 2576) :
    (⟨c.W, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.base_disjoint _ h (by omega)

theorem c_w' {a n d k : Nat} (ha : a + n ≤ 512) (hd : d + k ≤ 2576) :
    (⟨c.C + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  (L.c_w.sub_left (cSub ha)).sub_right (wSub hd)

theorem c0_w' {n d k : Nat} (hn : n ≤ 512) (hd : d + k ≤ 2576) :
    (⟨c.C, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  (L.c_w.sub_left (Region.sub_prefix hn)).sub_right (wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 2576) : (⟨c.D, c.n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (wSub hd)

theorem v_w' {d k : Nat} (hd : d + k ≤ 2576) : (⟨c.V, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.v_w.sub_right (wSub hd)

theorem wrapW {d : Nat} (hd : d < 2576) : (c.W + BitVec.ofNat 64 d).toNat = c.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem wrapC {d : Nat} (hd : d < 512) : (c.C + BitVec.ofNat 64 d).toNat = c.C.toNat + d := by
  have := L.cw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Doublewords of `W` are aligned. -/
theorem alW {d : Nat} (hd : d % 8 = 0) (hlt : d < 2576) : (c.W + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [L.wrapW hlt]; have := L.wal; omega

/-- Doublewords of the key context are aligned. -/
theorem alC {d : Nat} (hd : d % 8 = 0) (hlt : d < 512) : (c.C + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [L.wrapC hlt]; have := L.cal; omega

theorem rb : 16 * (c.R + 1) ≤ 240 := by rcases L.rounds with h | h | h <;> rw [h] <;> decide

end Lay

namespace Perm

variable {c : Cx} {s : State} (P : Perm c s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 2576) : InRegions s.wr (c.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2576) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 2576) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  Covers.right (P.wC h)

theorem wR {d n : Nat} (h : d + n ≤ 2576) : InRegions (s.rd ++ s.wr) (c.W + BitVec.ofNat 64 d) n :=
  P.wCR h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem cC {d n : Nat} (h : d + n ≤ 512) : Covers [⟨c.C + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.ctx h (by decide)

theorem c0C {n : Nat} (h : n ≤ 512) : Covers [⟨c.C, n⟩] (s.rd ++ s.wr) :=
  covers_prefix P.ctx h

theorem vR {d n : Nat} (h : d + n ≤ 16) : InRegions (s.rd ++ s.wr) (c.V + BitVec.ofNat 64 d) n :=
  in_off P.v h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `len` bytes at `P` that the code may read, apart from `W`. -/
structure Buf (c : Cx) (s : State) (P : Addr) (len : Nat) : Prop where
  rd : Covers [⟨P, len⟩] (s.rd ++ s.wr)
  lt : len < 2 ^ 64
  wrap : P.toNat + len ≤ 2 ^ 64
  w : (⟨P, len⟩ : Region).Disjoint ⟨c.W, 2576⟩

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

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ len) : Buf c s P k where
  rd := covers_prefix h.rd hk
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)

theorem wd {d k : Nat} (hd : d + k ≤ 2576) : (⟨P, len⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  h.w.sub_right (Lay.wSub hd)

end Buf

/-- The data as a buffer. -/
theorem Lay.bufD {c : Cx} (L : Lay c) {s : State} (P : Perm c s) : Buf c s c.D c.n :=
  ⟨Covers.right P.d, L.n_lt, L.dw, L.d_w⟩

end VG.Proof.AesSiv.RISCV64
