module

import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Aes.Circuit
public import VerifiedGarbage.TCB.RISCV64.Isa
public meta import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# AES-GCM on RISC-V: where everything is

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcm/PPC64LE/Env.lean`): the key context (256 bytes at `c`), the
streaming state (80 bytes at `st`) and the working space (2560 bytes at `w`)
(`Lay`), each 8-byte aligned (a doubleword access faults otherwise): the
state is disjoint from the parts of `W` other than `[16, 96)` (where `seal`
and `open` keep it), and the context from both. `Perm` says the state may
read the context and write the state and `W`; `Env` adds the registers the
pieces keep (`frozen`), pinned to values `V`, among them the three pointers
in `s2`, `s1` and `s0`, the stack pointer, and that the 2048 bytes below it,
which `vg_ghash`'s frame uses, are apart from the context, the state and `W`
(`StkOk`).

Also here: what a buffer of data must satisfy (`DataOk`), the bytes a copy
writes (`bytesAt_writeBytes`), and arithmetic on lengths.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

/-! ## Covering regions -/

/-- The part of a region at an offset is covered when the region is. -/
theorem covers_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine h a m ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem in_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 d) n :=
  covers_off h hd hk _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem in_left {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts :=
  Covers.of_mem fun x hx => by simp only [List.mem_singleton] at hx; exact hx ▸ h

theorem covers_left {rd wr rs : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => in_left (h a n hi)

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-! ## The layout -/

/-- The regions: the context, the state and the parts of `W`. -/
structure Lay (c st w : Addr) : Prop where
  cw : c.toNat + 256 ≤ 2 ^ 64
  sw : st.toNat + 80 ≤ 2 ^ 64
  ww : w.toNat + 2560 ≤ 2 ^ 64
  cs : (⟨c, 256⟩ : Region).Disjoint ⟨st, 80⟩
  cw' : (⟨c, 256⟩ : Region).Disjoint ⟨w, 2560⟩
  sa : (⟨st, 80⟩ : Region).Disjoint ⟨w, 16⟩
  sb : (⟨st, 80⟩ : Region).Disjoint ⟨w + BitVec.ofNat 64 96, 2464⟩
  ca : c.toNat % 8 = 0
  sal : st.toNat % 8 = 0
  wal : w.toNat % 8 = 0

/-- The layout, for an environment's registers. -/
theorem Lay.v {V : Reg → BitVec 64} {c st w : Addr} (L : Lay c st w) (h29 : V .s2 = c) (h30 : V .s1 = st)
    (h31 : V .s0 = w) : Lay (V .s2) (V .s1) (V .s0) := by
  rw [h29, h30, h31]; exact L

/-- What a state may access. -/
structure Perm (c st w : Addr) (s : State) : Prop where
  ctx : Covers [⟨c, 256⟩] (s.rd ++ s.wr)
  st : Covers [⟨st, 80⟩] s.wr
  w : Covers [⟨w, 2560⟩] s.wr

/-- The registers the pieces keep: the nonce's length (`s7`), the other
arguments of the functions (`s8`–`s11`), the rounds (`s3`), and the
context, the state and `W` (`s2`, `s1`, `s0`): every callee-saved register
but `s4`–`s6`. -/
def frozen : List Reg := [.s0, .s1, .s2, .s3, .s7, .s8, .s9, .s10, .s11]

/-- The 2048 bytes below the stack pointer `sp`, which `vg_ghash`'s frame
uses, are apart from the context, the state and `W`. -/
structure StkOk (c st w sp : Addr) : Prop where
  c : (⟨c, 256⟩ : Region).Disjoint (below sp 2048)
  st : (⟨st, 80⟩ : Region).Disjoint (below sp 2048)
  w : (⟨w, 2560⟩ : Region).Disjoint (below sp 2048)
  al : sp.toNat % 16 = 0
  ge : 2048 ≤ sp.toNat

/-- The registers `frozen` hold their values `V`, the stack pointer is `sp`,
and the state may access the context, the state and `W` (at `V s2`,
`V s1` and `V s0`), apart from the stack below `sp`. -/
structure Env (V : Reg → BitVec 64) (sp : Addr) (s : State) : Prop where
  fr : ∀ r ∈ frozen, s.gpr r = V r
  sp : s.sp = sp
  perm : Perm (V .s2) (V .s1) (V .s0) s
  stk : StkOk (V .s2) (V .s1) (V .s0) s.sp

theorem Perm.of_eq {c st w : Addr} {s s' : State} (h : Perm c st w s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Perm c st w s' := by
  obtain ⟨a, b, d⟩ := h; exact ⟨by rw [hrd, hwr]; exact a, by rw [hwr]; exact b, by rw [hwr]; exact d⟩

theorem Env.s2 {V : Reg → BitVec 64} {sp : Addr} {s : State} (h : Env V sp s) : s.gpr .s2 = V .s2 :=
  h.fr _ (by decide)
theorem Env.s1 {V : Reg → BitVec 64} {sp : Addr} {s : State} (h : Env V sp s) : s.gpr .s1 = V .s1 :=
  h.fr _ (by decide)
theorem Env.s0 {V : Reg → BitVec 64} {sp : Addr} {s : State} (h : Env V sp s) : s.gpr .s0 = V .s0 :=
  h.fr _ (by decide)
theorem Env.stk' {V : Reg → BitVec 64} {sp : Addr} {s : State} (h : Env V sp s) :
    StkOk (V .s2) (V .s1) (V .s0) sp := h.sp ▸ h.stk

theorem Env.s3 {V : Reg → BitVec 64} {sp : Addr} {s : State} (h : Env V sp s) : s.gpr .s3 = V .s3 :=
  h.fr _ (by decide)

/-- An environment, after code that keeps the frozen registers, `sp` and the
permissions. -/
theorem Env.keep {V : Reg → BitVec 64} {sp : Addr} {s s' : State} (h : Env V sp s)
    (hg : ∀ r ∈ frozen, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env V sp s' :=
  ⟨fun r hr => (hg r hr).trans (h.fr r hr), hsp.trans h.sp, h.perm.of_eq hrd hwr, hsp ▸ h.stk⟩

/-- What a block that keeps everything but some registers leaves. -/
structure Keeps (s s' : State) : Prop where
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Keeps.refl (s : State) : Keeps s s := ⟨rfl, rfl, rfl, rfl⟩

/-- What code that writes only memory it may keeps: the regions and the stack
pointer. -/
structure Keeps' (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

namespace Lay

/-! ### Sub-regions -/

theorem ctxSub {C : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ ⟨C, 256⟩ :=
  Offset.sub_base _ h

theorem stSub {S : Addr} {d n : Nat} (h : d + n ≤ 80) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 80⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

theorem bSub {W : Addr} {d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W + BitVec.ofNat 64 96, 2464⟩ :=
  Offset.sub _ h₁ (by omega)

theorem aSub {W : Addr} {d n : Nat} (h : d + n ≤ 16) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 16⟩ :=
  Offset.sub_base _ h

variable {c st w : Addr} (L : Lay c st w)
include L

/-- Parts of the state and of `W` outside `[16, 96)` are disjoint. -/
theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 2560)) :
    (⟨st + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w + BitVec.ofNat 64 d, k⟩ := by
  rcases hd with hd | ⟨h₁, h₂⟩
  · exact (L.sa.sub_left (stSub ha)).sub_right (aSub hd)
  · exact (L.sb.sub_left (stSub ha)).sub_right (bSub h₁ h₂)

theorem ctx_st {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 80) :
    (⟨c + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨st + BitVec.ofNat 64 d, k⟩ :=
  (L.cs.sub_left (ctxSub ha)).sub_right (stSub hd)

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨c + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w + BitVec.ofNat 64 d, k⟩ :=
  (L.cw'.sub_left (ctxSub ha)).sub_right (wSub hd)

omit L in
/-- Parts of the state are disjoint. -/
theorem st_st {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 80) (hd : d + k ≤ 80) :
    (⟨st + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨st + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

/-- Doublewords of the context, the state and `W` are aligned. -/
theorem cal {d : Nat} (hd : d % 8 = 0) (h : d < 256) : (c + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  have := L.cw; have := L.ca
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega)]
  omega

theorem stal {d : Nat} (hd : d % 8 = 0) (h : d < 80) : (st + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  have := L.sw; have := L.sal
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega)]
  omega

theorem stal4 {d : Nat} (hd : d % 4 = 0) (h : d < 80) : (st + BitVec.ofNat 64 d).toNat % 4 = 0 := by
  have := L.sw; have := L.sal
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega)]
  omega

theorem wal8 {d : Nat} (hd : d % 8 = 0) (h : d < 2560) : (w + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  have := L.ww; have := L.wal
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega)]
  omega

theorem w_fit {d n : Nat} (h : d + n ≤ 2560) (hn : 0 < n) : (w + BitVec.ofNat 64 d).toNat + n ≤ 2 ^ 64 := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega)]
  omega

theorem st_fit {d n : Nat} (h : d + n ≤ 80) (hn : 0 < n) : (st + BitVec.ofNat 64 d).toNat + n ≤ 2 ^ 64 := by
  have := L.sw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega)]
  omega

omit L in
/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨w + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

omit L in
theorem ctx_ctx {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 256) (hd : d + k ≤ 256) :
    (⟨c + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨c + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

end Lay

namespace Perm

variable {c st w : Addr} {s : State} (P : Perm c st w s)
include P

theorem ctxR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (c + BitVec.ofNat 64 d) n :=
  in_off P.ctx h (by decide)

theorem stW {d n : Nat} (h : d + n ≤ 80) : InRegions s.wr (st + BitVec.ofNat 64 d) n :=
  in_off P.st h (by decide)

theorem stR {d n : Nat} (h : d + n ≤ 80) : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 d) n :=
  in_left (P.stW h)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (w + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (w + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem ctxC {d n : Nat} (h : d + n ≤ 256) : Covers [⟨c + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.ctx h (by decide)

theorem stC {d n : Nat} (h : d + n ≤ 80) : Covers [⟨st + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.st h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨w + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Buffers of data -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from the
state, `W` and the stack below the stack pointer that `vg_ghash` uses. -/
structure DataOk (st w : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  fit : D.toNat + n ≤ 2 ^ 64
  st : (⟨D, n⟩ : Region).Disjoint ⟨st, 80⟩
  w : (⟨D, n⟩ : Region).Disjoint ⟨w, 2560⟩
  sk : (⟨D, n⟩ : Region).Disjoint (below s.sp 2048)

namespace DataOk

variable {st w : Addr} {s : State} {D : Addr} {n : Nat} (h : DataOk st w s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    DataOk st w s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd, sk := by rw [hsp]; exact h.sk }

theorem toNat_add {j : Nat} (hj : j < n) : (D + BitVec.ofNat 64 j).toNat = D.toNat + j := by
  have := h.fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : DataOk st w s D k where
  rd := covers_prefix h.rd hk
  lt := by have := h.lt; omega
  fit := by have := h.fit; omega
  st := h.st.sub_left (Region.sub_prefix hk)
  w := h.w.sub_left (Region.sub_prefix hk)
  sk := h.sk.sub_left (Region.sub_prefix hk)

/-- The `k` (at least one) bytes from `j` on. -/
theorem sub {j k : Nat} (hjk : j + k ≤ n) (hk : 0 < k) : DataOk st w s (D + BitVec.ofNat 64 j) k := by
  have hs : Region.Sub ⟨D + BitVec.ofNat 64 j, k⟩ ⟨D, n⟩ := Offset.sub_base _ hjk
  refine ⟨covers_off h.rd hjk h.lt, by have := h.lt; omega, ?_, h.st.sub_left hs, h.w.sub_left hs,
    h.sk.sub_left hs⟩
  rw [h.toNat_add (by omega)]; have := h.fit; omega

end DataOk

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

/-- The bytes at `p`, after writing `xs` at `p + o`: the first `o`, then `xs`. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (o : Nat) (xs : List Byte) (h : o + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 o) xs) p (o + xs.length) = bytesAt m p o ++ xs := by
  rw [bytesAt_add]
  congr 1
  · simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp [bytesAt])
    intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h₁, ite_true,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some]

theorem bytesAt_writeBytes_self (m : Mem) (p : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  have := bytesAt_writeBytes m p 0 xs (by omega)
  simp only [Nat.zero_add, BitVec.add_zero] at this
  rw [this]; rfl

theorem bytesAt_writeBytes_self' (m : Mem) (p : Addr) {xs : List Byte} {n : Nat} (hn : xs.length = n)
    (h : n < 2 ^ 64) : bytesAt (writeBytes m p xs) p n = xs := by
  subst hn; exact bytesAt_writeBytes_self m p xs h

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-- The bytes at `p` after writing `xs` there: `xs`, then what was there. -/
theorem bytesAt_writeBytes_prefix (m : Mem) (p : Addr) (xs : List Byte) {n : Nat} (hn : xs.length ≤ n)
    (h : n < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p n = xs ++ bytesAt m (p + BitVec.ofNat 64 xs.length) (n - xs.length) := by
  rw [show n = xs.length + (n - xs.length) by omega, bytesAt_add, bytesAt_writeBytes_self _ _ _ (by omega),
    Nat.add_sub_cancel_left]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [writeBytes, BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := xs.length) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  simp [show ¬ (xs.length + i < xs.length) by omega]

/-- A write of `xs` at `q`, within `R`, keeps everything outside `R`. -/
theorem writeBytes_frame' (m : Mem) {q : Addr} {xs : List Byte} {n : Nat} (hn : xs.length = n) :
    Frame [⟨q, n⟩] m (writeBytes m q xs) :=
  writeBytes_frame m q xs (by rw [hn]; exact Region.contains_self _ _)

/-- Running a block with what is known of its result. -/
theorem WP.run {is : List Instr} {s : State} {Q R : State → Prop}
    (h : ∃ s', runBlock isa is s = some s' ∧ Q s') (hq : ∀ s', Q s' → R s') : WP isa (.block is) s R := by
  obtain ⟨s', h₁, h₂⟩ := h; exact WP.of_runBlock ⟨s', h₁, hq _ h₂⟩

/-! ## Arithmetic -/

theorem toNat64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_sub64 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

theorem ofNat_add64 (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem and15 (x : BitVec 64) : x &&& BitVec.ofNat 64 15 = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 15) (by decide),
    show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shr4 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem ofNat_eq_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n = 0) ↔ n = 0 := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; rw [toNat64 h] at this; simpa using this
  · rintro rfl; rfl

end VG.Proof.AesGcm.RISCV64
