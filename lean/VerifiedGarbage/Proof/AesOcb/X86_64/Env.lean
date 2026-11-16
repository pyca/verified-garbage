module
public import VerifiedGarbage.Proof.Framework.X86_64.Call

import VerifiedGarbage.Proof.AesCcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Aes

/-!
# AES-OCB on x86-64: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes
at `K`), the working space (`wn` bytes at `W`, 3584 for the functions over
the AES block functions) and the 8 bytes of stack
below `SP` that the calls use (`Lay`); what a state may access (`Perm`); the
registers holding `K` and `W` and the stack pointer (`Env`); and the public
values the entry keeps in `W` (`Slots`). The pieces write the parts of `W`
in `mutR` (and the data, and the stack below `SP`), so the slots and our
caller's registers saved in `W` stay as the entry left them.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.X86_64 (covers_off in_off in_left covers_left)

/-! ## The regions -/

/-- The key context, `W` (of `wn` bytes) and the stack below `SP` used by
the calls. -/
structure LayN (K W SP : Addr) (wn : Nat) : Prop where
  kw : K.toNat + 256 ≤ 2 ^ 64
  ww : W.toNat + wn ≤ 2 ^ 64
  k_w : (⟨K, 256⟩ : Region).Disjoint ⟨W, wn⟩
  stk_k : (below SP 8).Disjoint ⟨K, 256⟩
  stk_w : (below SP 8).Disjoint ⟨W, wn⟩
  sp : 8 ≤ SP.toNat

/-- `LayN` with the 3584 bytes of `W` of the functions over the AES block
functions. -/
abbrev Lay (K W SP : Addr) : Prop := LayN K W SP 3584

/-- What a state may access. -/
structure PermN (K W : Addr) (wn : Nat) (s : State) : Prop where
  k : Covers [⟨K, 256⟩] (s.rd ++ s.wr)
  w : Covers [⟨W, wn⟩] s.wr

abbrev Perm (K W : Addr) (s : State) : Prop := PermN K W 3584 s

/-- The registers holding the key context, `W` and the stack pointer, and
what the state may access. -/
structure EnvN (K W SP : Addr) (wn : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = K
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = SP
  perm : PermN K W wn s

abbrev Env (K W SP : Addr) (s : State) : Prop := EnvN K W SP 3584 s

theorem PermN.of_eq {K W : Addr} {wn : Nat} {s s' : State} (h : PermN K W wn s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : PermN K W wn s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `r14`, `r15`, `rsp` and the permissions. -/
theorem EnvN.keep {K W SP : Addr} {wn : Nat} {s s' : State} (h : EnvN K W SP wn s)
    (hg : ∀ r ∈ [Reg.r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    EnvN K W SP wn s' :=
  ⟨by rw [hg _ (by simp), h.r14], by rw [hg _ (by simp), h.r15], by rw [hg _ (by simp), h.rsp],
    h.perm.of_eq hrd hwr⟩

theorem EnvN.of_saved {K W SP : Addr} {wn : Nat} {s s' : State} (h : EnvN K W SP wn s)
    (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : EnvN K W SP wn s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg _ (by decide)) hrd hwr

namespace LayN

theorem wSub {W : Addr} {wn d n : Nat} (h : d + n ≤ wn) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, wn⟩ :=
  Offset.sub_base _ h

variable {K W SP : Addr} {wn : Nat} (L : LayN K W SP wn)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ wn) (hd : d + k ≤ wn) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega_using [ha, this]) (by have := L.ww; omega_using [hd, this])

theorem stk_w' {a n : Nat} (ha : a + n ≤ wn) : (below SP 8).Disjoint ⟨W + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (wSub ha)

/-- `w_w` below byte 640. -/
theorem w_w6 (hwn : 640 ≤ wn) {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 640) (hd : d + k ≤ 640) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  L.w_w h (Nat.le_trans ha hwn) (Nat.le_trans hd hwn)

theorem stk_w6 (hwn : 640 ≤ wn) {a n : Nat} (ha : a + n ≤ 640) : (below SP 8).Disjoint ⟨W + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w' (Nat.le_trans ha hwn)

end LayN

/-- `LayN.wSub` below byte 640. -/
theorem LayN.wSub6 {W : Addr} {wn : Nat} (hwn : 640 ≤ wn) {d n : Nat} (h : d + n ≤ 640) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, wn⟩ :=
  LayN.wSub (Nat.le_trans h hwn)

namespace Lay

theorem kSub {K : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨K + BitVec.ofNat 64 d, n⟩ ⟨K, 256⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 3584) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 3584⟩ :=
  Offset.sub_base _ h

variable {K W SP : Addr} (L : Lay K W SP)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 3584) (hd : d + k ≤ 3584) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  LayN.w_w L h ha hd

theorem stk_w' {a n : Nat} (ha : a + n ≤ 3584) : (below SP 8).Disjoint ⟨W + BitVec.ofNat 64 a, n⟩ :=
  LayN.stk_w' L ha

end Lay

namespace PermN

variable {K W : Addr} {wn : Nat} {s : State} (P : PermN K W wn s)
include P

theorem kR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 d) n :=
  in_off P.k h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ wn) (hw : wn < 2 ^ 64 := by decide) :
    InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  in_off P.w h hw

theorem wR {d n : Nat} (h : d + n ≤ wn) (hw : wn < 2 ^ 64 := by decide) :
    InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h hw)

theorem wC {d n : Nat} (h : d + n ≤ wn) (hw : wn < 2 ^ 64 := by decide) :
    Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h hw

/-! Below byte 640 of a working space of at least 640 bytes: the offsets of
the slots and blocks of `Impl/AesOcb/X86_64.lean`. -/

theorem wW6 (hwn : 640 ≤ wn) (hw : wn < 2 ^ 64) {d n : Nat} (h : d + n ≤ 640) :
    InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  P.wW (Nat.le_trans h hwn) hw

theorem wR6 (hwn : 640 ≤ wn) (hw : wn < 2 ^ 64) {d n : Nat} (h : d + n ≤ 640) :
    InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  P.wR (Nat.le_trans h hwn) hw

theorem wC6 (hwn : 640 ≤ wn) (hw : wn < 2 ^ 64) {d n : Nat} (h : d + n ≤ 640) :
    Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  P.wC (Nat.le_trans h hwn) hw

end PermN

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W` and
the stack below `SP`. -/
structure BufN (W SP : Addr) (wn : Nat) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, wn⟩
  stk : (below SP 8).Disjoint ⟨D, n⟩

abbrev Buf (W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop := BufN W SP 3584 s D n

namespace BufN

variable {W SP : Addr} {wn : Nat} {s : State} {D : Addr} {n : Nat} (h : BufN W SP wn s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : BufN W SP wn s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : BufN W SP wn s (D + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega_using [hk]) h.lt
  lt := by have := h.lt; omega_using [this]
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega_using [hk, this])]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega_arith
  w := h.w.sub_left (Offset.sub_base D (by omega_using [hk]))
  stk := h.stk.sub_right (Offset.sub_base D (by omega_using [hk]))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : BufN W SP wn s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_using [hk, hc]⟩
  lt := by have := h.lt; omega_using [hk, this]
  wrap := by have := h.wrap; omega_using [hk, this]
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : BufN W SP wn s (D + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega_using [hk])).take (by omega_using [hk])

end BufN

/-- The data: a buffer that the code may also write, apart from the key
context. -/
structure DBufN (K W SP : Addr) (wn : Nat) (s : State) (D : Addr) (n : Nat) : Prop extends BufN W SP wn s D n where
  wr : Covers [⟨D, n⟩] s.wr
  k : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩

abbrev DBuf (K W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop := DBufN K W SP 3584 s D n

namespace DBufN

variable {K W SP : Addr} {wn : Nat} {s : State} {D : Addr} {n : Nat} (h : DBufN K W SP wn s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DBufN K W SP wn s' D n :=
  { h.toBufN.of_eq hrd hwr with wr := by rw [hwr]; exact h.wr, k := h.k }

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : DBufN K W SP wn s (D + BitVec.ofNat 64 a) k where
  toBufN := h.toBufN.slice hk
  wr := by
    have := (h.toBufN.drop (k := a) (by omega_using [hk]))
    exact fun x m hx => covers_off h.wr (d := a) (n := k) hk h.lt x m hx
  k := h.k.sub_right ((Offset.sub_base D (by omega_using [hk])))

end DBufN

/-! ## The slots -/

/-- The public values the entry keeps in `W`: the data and its length, the
tag length, the rounds, the associated data, the nonce and its length. -/
structure Slots (W : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (m : Mem) : Prop where
  data : m.readW (W + BitVec.ofNat 64 208) 64 = D
  len : m.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n
  tl : m.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 tl
  rounds : m.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R
  aad : m.readW (W + BitVec.ofNat 64 240) 64 = A
  nonce : m.readW (W + BitVec.ofNat 64 288) 64 = N
  nlen : m.readW (W + BitVec.ofNat 64 296) 64 = BitVec.ofNat 64 nl

/-- The parts of `W` the pieces write: the blocks at `[0, 160)`, `[248, 288)`
(the length of the associated data, `bottom` and `Offset_0`),
`[384, 2560)` and the table of `L_j`, `[2560, 3584)`. -/
abbrev wA (W : Addr) : Region := ⟨W, 160⟩
abbrev wB (W : Addr) : Region := ⟨W + BitVec.ofNat 64 248, 40⟩
abbrev wC (W : Addr) : Region := ⟨W + BitVec.ofNat 64 384, 2176⟩
abbrev wT (W : Addr) : Region := ⟨W + BitVec.ofNat 64 2560, 1024⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (W SP D : Addr) (n : Nat) : List Region := [wA W, wB W, wC W, below SP 8, ⟨D, n⟩, wT W]

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩)
    {d k : Nat} (hd : 160 ≤ d ∧ d + k ≤ 248 ∨ 288 ≤ d ∧ d + k ≤ 384) :
    ∀ r ∈ mutR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 160) (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · rcases hd with hd | hd
    · exact L.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
    · exact L.w_w (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact L.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact (L.stk_w' (by omega_using [hd])).symm
  · exact (hD.sub_right (Lay.wSub (by omega_using [hd]))).symm
  · exact L.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)

/-- The key context misses the parts the pieces write. -/
theorem k_mut {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ r ∈ mutR W SP D n, (⟨K, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.stk_k.symm
  · exact hD
  · exact L.k_w.sub_right (Lay.wSub (by decide))

end VG.Proof.AesOcb.X86_64
