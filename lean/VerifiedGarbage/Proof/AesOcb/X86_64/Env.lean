import VerifiedGarbage.Proof.AesOcb.X86_64.Contract
import VerifiedGarbage.Proof.AesCcm.X86_64.Env
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Impl.AesOcb.X86_64

/-!
# AES-OCB on x86-64: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes
at `K`), the working space (2560 bytes at `W`) and the 8 bytes of stack
below `SP` that the calls use (`Lay`); what a state may access (`Perm`); the
registers holding `K` and `W` and the stack pointer (`Env`); and the public
values the entry keeps in `W` (`Slots`). The pieces write the parts of `W`
in `mutR` (and the data, and the stack below `SP`), so the slots and our
caller's registers saved in `W` stay as the entry left them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.X86_64 (covers_off in_off in_left covers_left)

/-! ## The regions -/

/-- The key context, `W` and the stack below `SP` used by the calls. -/
structure Lay (K W SP : Addr) : Prop where
  kw : K.toNat + 256 ≤ 2 ^ 64
  ww : W.toNat + 2560 ≤ 2 ^ 64
  k_w : (⟨K, 256⟩ : Region).Disjoint ⟨W, 2560⟩
  stk_k : (below SP 8).Disjoint ⟨K, 256⟩
  stk_w : (below SP 8).Disjoint ⟨W, 2560⟩
  sp : 8 ≤ SP.toNat

/-- What a state may access. -/
structure Perm (K W : Addr) (s : State) : Prop where
  k : Covers [⟨K, 256⟩] (s.rd ++ s.wr)
  w : Covers [⟨W, 2560⟩] s.wr

/-- The registers holding the key context, `W` and the stack pointer, and
what the state may access. -/
structure Env (K W SP : Addr) (s : State) : Prop where
  r14 : s.gpr .r14 = K
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = SP
  perm : Perm K W s

theorem Perm.of_eq {K W : Addr} {s s' : State} (h : Perm K W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm K W s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `r14`, `r15`, `rsp` and the permissions. -/
theorem Env.keep {K W SP : Addr} {s s' : State} (h : Env K W SP s)
    (hg : ∀ r ∈ [Reg.r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Env K W SP s' :=
  ⟨by rw [hg _ (by simp), h.r14], by rw [hg _ (by simp), h.r15], by rw [hg _ (by simp), h.rsp],
    h.perm.of_eq hrd hwr⟩

theorem Env.of_saved {K W SP : Addr} {s s' : State} (h : Env K W SP s)
    (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env K W SP s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg _ (by decide)) hrd hwr

namespace Lay

theorem kSub {K : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨K + BitVec.ofNat 64 d, n⟩ ⟨K, 256⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

variable {K W SP : Addr} (L : Lay K W SP)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem k_w' {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨K + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  (L.k_w.sub_left (kSub ha)).sub_right (wSub hd)

theorem stk_w' {a n : Nat} (ha : a + n ≤ 2560) : (below SP 8).Disjoint ⟨W + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (wSub ha)

theorem stk_k' {a n : Nat} (ha : a + n ≤ 256) : (below SP 8).Disjoint ⟨K + BitVec.ofNat 64 a, n⟩ :=
  L.stk_k.sub_right (kSub ha)

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

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W` and
the stack below `SP`. -/
structure Buf (W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  stk : (below SP 8).Disjoint ⟨D, n⟩

namespace Buf

variable {W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : Buf W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Buf W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : Buf W SP s (D + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega
  w := h.w.sub_left (Offset.sub_base D (by omega))
  stk := h.stk.sub_right (Offset.sub_base D (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Buf W SP s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : Buf W SP s (D + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega)).take (by omega)

end Buf

/-- The data: a buffer that the code may also write, apart from the key
context. -/
structure DBuf (K W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop extends Buf W SP s D n where
  wr : Covers [⟨D, n⟩] s.wr
  k : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩

namespace DBuf

variable {K W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : DBuf K W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DBuf K W SP s' D n :=
  { h.toBuf.of_eq hrd hwr with wr := by rw [hwr]; exact h.wr, k := h.k }

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : DBuf K W SP s (D + BitVec.ofNat 64 a) k where
  toBuf := h.toBuf.slice hk
  wr := by
    have := (h.toBuf.drop (k := a) (by omega))
    exact fun x m hx => covers_off h.wr (d := a) (n := k) hk h.lt x m hx
  k := h.k.sub_right ((Offset.sub_base D (by omega)))

end DBuf

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
(the length of the associated data, `bottom` and `Offset_0`) and
`[384, 2560)`. -/
abbrev wA (W : Addr) : Region := ⟨W, 160⟩
abbrev wB (W : Addr) : Region := ⟨W + BitVec.ofNat 64 248, 40⟩
abbrev wC (W : Addr) : Region := ⟨W + BitVec.ofNat 64 384, 2176⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (W SP D : Addr) (n : Nat) : List Region := [wA W, wB W, wC W, below SP 8, ⟨D, n⟩]

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {d k : Nat} (hd : 160 ≤ d ∧ d + k ≤ 248 ∨ 288 ≤ d ∧ d + k ≤ 384) :
    ∀ r ∈ mutR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 160) (.inr (by omega)) (by omega) (by decide)
  · rcases hd with hd | hd
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm
  · exact (hD.sub_right (Lay.wSub (by omega))).symm

/-- The key context misses the parts the pieces write. -/
theorem k_mut {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ r ∈ mutR W SP D n, (⟨K, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.stk_k.symm
  · exact hD

end VG.Proof.AesOcb.X86_64
