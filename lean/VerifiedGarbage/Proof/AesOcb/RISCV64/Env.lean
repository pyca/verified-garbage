module

import VerifiedGarbage.Impl.AesOcb.RISCV64
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-!
# AES-OCB on RISCV64: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes
at `K`) and the working space (2560 bytes at `W`) (`Lay`); what a state may
access (`Perm`); the registers the pieces keep (AES-GCM's `frozen`), pinned
to values `V`, among them `K` in `s2` and `W` in `s0`, and the stack
pointer (`Env`); the buffers of the associated data, the nonce and the data
(`Buf`, `DBuf`). The pieces write the parts of `W` in `mutR` (and the data),
so our caller's registers saved in `W` at `[128, 248)` stay as the entry
left them, and so do the addresses of the associated data and the data
there (`Slots`). As on PPC64LE (`Proof/AesOcb/PPC64LE/Env.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOcb.RISCV64
open VG.Proof.AesGcm.RISCV64 (frozen covers_off in_off in_left covers_left)

/-- Branching on a register holding `n`, while it is not zero. -/
theorem eval_nonzero {s : State} {r : Reg} {n : Nat} (h : s.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    isa.eval (.nonzero r) s = some (!decide (n = 0)) := by
  rw [Steps.eval_nonzero_ofNat s r hn h]; simp

theorem eval_zero {s : State} {r : Reg} {n : Nat} (h : s.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    isa.eval (.zero r) s = some (decide (n = 0)) :=
  Steps.eval_zero_ofNat s r hn h

theorem frozen_preserved : ∀ r ∈ frozen, r ∈ preserved := by decide

/-! ## The regions -/

/-- The key context and `W`. -/
structure Lay (K W : Addr) : Prop where
  kw : K.toNat + 256 ≤ 2 ^ 64
  ww : W.toNat + 2560 ≤ 2 ^ 64
  k_w : (⟨K, 256⟩ : Region).Disjoint ⟨W, 2560⟩
  kal : K.toNat % 8 = 0
  wal : W.toNat % 8 = 0

/-- What a state may access. -/
structure Perm (K W : Addr) (s : State) : Prop where
  k : Covers [⟨K, 256⟩] (s.rd ++ s.wr)
  w : Covers [⟨W, 2560⟩] s.wr

/-- The registers `frozen` hold their values `V`, the stack pointer is `sp`,
and the state may access the key context and `W` (at `V s2` and `V s0`). -/
structure Env (V : Reg → BitVec 64) (sp : Addr) (s : State) : Prop where
  fr : ∀ r ∈ frozen, s.gpr r = V r
  sp : s.sp = sp
  perm : Perm (V .s2) (V .s0) s

theorem Perm.of_eq {K W : Addr} {s s' : State} (h : Perm K W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm K W s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

section
variable {V : Reg → BitVec 64} {sp : Addr} {s : State} (h : Env V sp s)
include h

theorem Env.s0 : s.gpr .s0 = V .s0 := h.fr _ (by decide)
theorem Env.s1 : s.gpr .s1 = V .s1 := h.fr _ (by decide)
theorem Env.s2 : s.gpr .s2 = V .s2 := h.fr _ (by decide)
theorem Env.s3 : s.gpr .s3 = V .s3 := h.fr _ (by decide)
theorem Env.s7 : s.gpr .s7 = V .s7 := h.fr _ (by decide)
theorem Env.s8 : s.gpr .s8 = V .s8 := h.fr _ (by decide)
theorem Env.s9 : s.gpr .s9 = V .s9 := h.fr _ (by decide)
theorem Env.s10 : s.gpr .s10 = V .s10 := h.fr _ (by decide)
theorem Env.s11 : s.gpr .s11 = V .s11 := h.fr _ (by decide)

/-- An environment, after code that keeps the frozen registers, `sp` and the
permissions. -/
theorem Env.keep {s' : State} (hg : ∀ r ∈ frozen, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env V sp s' :=
  ⟨fun r hr => (hg r hr).trans (h.fr r hr), hsp.trans h.sp, h.perm.of_eq hrd hwr⟩

/-- An environment, after code that writes only the registers `rs`. -/
theorem Env.others {s' : State} {rs : List Reg} (hg : ∀ r, r ∉ rs → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hd : ∀ r ∈ frozen, r ∉ rs := by decide) : Env V sp s' :=
  h.keep (fun r hr => hg r (hd r hr)) hsp hrd hwr

/-- An environment, after a call. -/
theorem Env.of_saved {s' : State} (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env V sp s' :=
  h.keep (fun r hr => hg r (frozen_preserved r hr)) hsp hrd hwr

end

namespace Lay

theorem kSub {K : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨K + BitVec.ofNat 64 d, n⟩ ⟨K, 256⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

variable {K W : Addr} (L : Lay K W)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem k_w' {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨K + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  (L.k_w.sub_left (kSub ha)).sub_right (wSub hd)

/-- `W + d`, as a number. -/
theorem toNat_w {d : Nat} (hd : d < 2560) : (W + BitVec.ofNat 64 d).toNat = W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

end Lay

namespace Perm

variable {K W : Addr} {s : State} (P : Perm K W s)
include P

theorem kR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 d) n :=
  in_off P.k h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem kC {d n : Nat} (h : d + n ≤ 256) : Covers [⟨K + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.k h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W`. -/
structure Buf (W : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩

namespace Buf

variable {W : Addr} {s : State} {D : Addr} {n : Nat} (h : Buf W s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Buf W s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : Buf W s (D + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega
  w := h.w.sub_left (Offset.sub_base D (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Buf W s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : Buf W s (D + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega)).take (by omega)

end Buf

/-- The data: a buffer that the code may also write, apart from the key
context. -/
structure DBuf (K W : Addr) (s : State) (D : Addr) (n : Nat) : Prop extends Buf W s D n where
  wr : Covers [⟨D, n⟩] s.wr
  k : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩

namespace DBuf

variable {K W : Addr} {s : State} {D : Addr} {n : Nat} (h : DBuf K W s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DBuf K W s' D n :=
  { h.toBuf.of_eq hrd hwr with wr := by rw [hwr]; exact h.wr, k := h.k }

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : DBuf K W s (D + BitVec.ofNat 64 a) k where
  toBuf := h.toBuf.slice hk
  wr := fun x m hx => covers_off h.wr (d := a) (n := k) hk h.lt x m hx
  k := h.k.sub_right ((Offset.sub_base D (by omega)))

end DBuf

/-! ## What the pieces write -/

/-- The parts of `W` the pieces write: `[0, 128)` and `[256, 2560)`, around
our caller's registers. -/
abbrev wA (W : Addr) : Region := ⟨W, 128⟩
abbrev wB (W : Addr) : Region := ⟨W + BitVec.ofNat 64 256, 2304⟩

/-- What the pieces may change: those parts of `W` and the data. -/
abbrev mutR (W D : Addr) (n : Nat) : List Region := [wA W, wB W, ⟨D, n⟩]

theorem sub_wA {W : Addr} {d k : Nat} (h : d + k ≤ 128) : Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (wA W) := by
  simpa using Offset.sub W (d := d) (n := k) (e := 0) (k := 128) (by omega) (by omega)

theorem sub_wB {W : Addr} {d k : Nat} (h₁ : 256 ≤ d) (h : d + k ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (wB W) := Offset.sub W (by omega) (by omega)

/-- A part of `W` within `[0, 128)`, as a part the pieces may write. -/
theorem in_mutA {W D : Addr} {n d k : Nat} (h : d + k ≤ 128) :
    ∃ r' ∈ mutR W D n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' := ⟨_, List.mem_cons_self .., sub_wA h⟩

/-- A part of `W` from 256 on, as a part the pieces may write. -/
theorem in_mutB {W D : Addr} {n d k : Nat} (h₁ : 256 ≤ d) (h : d + k ≤ 2560) :
    ∃ r' ∈ mutR W D n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB h₁ h⟩

/-- A part of `W`, as a part the pieces may write. -/
theorem in_mutW {W D : Addr} {n d k : Nat} (h : d + k ≤ 128 ∨ (256 ≤ d ∧ d + k ≤ 2560)) :
    ∃ r' ∈ mutR W D n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with h | ⟨h₁, h₂⟩
  · exact in_mutA h
  · exact in_mutB h₁ h₂

/-- The data, as a part the pieces may write. -/
theorem in_mutD {W D : Addr} {n : Nat} {r : Region} (h : Region.Sub r ⟨D, n⟩) :
    ∃ r' ∈ mutR W D n, Region.Sub r r' := ⟨_, by simp, h⟩

/-- A frame within a part of `W` the pieces may write. -/
theorem frame_mutW {W D : Addr} {n d k : Nat} (h : d + k ≤ 128 ∨ (256 ≤ d ∧ d + k ≤ 2560)) {m m' : Mem}
    (f : Frame [⟨W + BitVec.ofNat 64 d, k⟩] m m') : Frame (mutR W D n) m m' :=
  f.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact in_mutW h

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {d k : Nat} (hd : 128 ≤ d ∧ d + k ≤ 256) :
    ∀ r ∈ mutR W D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 128) (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (hD.sub_right (Lay.wSub (by omega))).symm

/-- The addresses of the associated data and of the data, which the entry
keeps in `W`. -/
structure Slots (W A D : Addr) (m : Mem) : Prop where
  aad : m.readW (W + BitVec.ofNat 64 232) 64 = A
  data : m.readW (W + BitVec.ofNat 64 240) 64 = D

/-- The slots, after writes to the parts the pieces write. -/
theorem Slots.mut {K W A D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {m m' : Mem} (hf : Frame (mutR W D n) m m') (S : Slots W A D m) : Slots W A D m' := by
  have k : ∀ d, 128 ≤ d → d + 8 ≤ 256 →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _)
      (kept_mut L hD ⟨h₁, h₂⟩) (by decide)
  exact ⟨by rw [k 232 (by decide) (by decide)]; exact S.aad, by rw [k 240 (by decide) (by decide)]; exact S.data⟩

/-- `W + d` is aligned, for an aligned `d`. -/
theorem Lay.alW {K W : Addr} (L : Lay K W) {d : Nat} (hd : d % 8 = 0) : (W + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := L.wal
  omega

/-- The key context misses the parts the pieces write. -/
theorem k_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ r ∈ mutR W D n, (⟨K, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact hD

end VG.Proof.AesOcb.RISCV64
