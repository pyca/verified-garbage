import VerifiedGarbage.Proof.AesOcb.AArch64.Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Impl.AesOcb.AArch64
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-OCB on AArch64: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes
at `K`) and the working space (2560 bytes at `W`) (`Lay`); what a state may
access (`Perm`); the registers holding `W`, `K`, the data `D`, the rounds
`R` and the data's length `n` throughout, and the stack pointer (`Env`); the
public arguments the entry keeps in `W` (`Slots`). The pieces write the
parts of `W` in `mutR` (and the data), so the slots and our caller's
registers saved in `W` stay as the entry left them. `orun` runs a block
symbolically.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (covers_off in_off in_left covers_left)

theorem write8 (m : Mem) (a : Addr) (v : BitVec (8 * 8)) : m.write a 8 v = m.writeW a v := by
  simp [Mem.writeW]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp [Mem.readW]

theorem imm_lit (k : Nat) (h : k < 2 ^ 16) : BitVec.setWidth 64 (BitVec.ofNat 16 k) <<< (16 * 0) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- Runs a block of the instructions the AES-OCB code uses. -/
macro "orun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.AArch64.addr,
    State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
    sp_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq, and_self,
    Impl.AesGcm.AArch64.mov, Impl.AesGcm.AArch64.ptr, Impl.AesGcm.AArch64.imm, ld, st,
    tagO, ofsO, ckO, sumO, ldO, l0O, lO, tmpO, t2O, ohO, savO, tlO, aadO, alenO, nO, nlO, botO, o0O, bufO, scrO,
    List.cons_append, List.nil_append, List.append_assoc, reduceCtorEq, ↓reduceIte, Nat.reduceLT,
    Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
    and_true, true_and, eq_self_iff_true, write8, read8, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.add_zero, $ts,*]) <;> try rfl)

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    show (exec x s).bind (runBlock isa (a ++ b)) = ((exec x s).bind (runBlock isa a)).bind (runBlock isa b)
    rw [Option.bind_assoc]
    congr 1
    funext u
    exact ih u

/-! ## The regions -/

/-- The key context and `W`. -/
structure Lay (K W : Addr) : Prop where
  kw : K.toNat + 256 ≤ 2 ^ 64
  ww : W.toNat + 2560 ≤ 2 ^ 64
  k_w : (⟨K, 256⟩ : Region).Disjoint ⟨W, 2560⟩

/-- What a state may access. -/
structure Perm (K W : Addr) (s : State) : Prop where
  k : Covers [⟨K, 256⟩] (s.rd ++ s.wr)
  w : Covers [⟨W, 2560⟩] s.wr

/-- The registers holding `W`, the key context, the data, the rounds and the
data's length, the stack pointer, and what the state may access. -/
structure Env (K W D : Addr) (R n : Nat) (SP : Addr) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = K
  x21 : s.gpr .x21 = D
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  x28 : s.gpr .x28 = BitVec.ofNat 64 n
  sp : s.sp = SP
  perm : Perm K W s

/-- The registers `Env` fixes. -/
abbrev envRegs : List Reg := [.x19, .x20, .x21, .x22, .x28]

theorem Perm.of_eq {K W : Addr} {s s' : State} (h : Perm K W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm K W s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps its registers, the stack pointer
and the permissions. -/
theorem Env.keep {K W D : Addr} {R n : Nat} {SP : Addr} {s s' : State} (h : Env K W D R n SP s)
    (hg : ∀ r ∈ envRegs, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env K W D R n SP s' :=
  ⟨by rw [hg _ (by simp), h.x19], by rw [hg _ (by simp), h.x20], by rw [hg _ (by simp), h.x21],
    by rw [hg _ (by simp), h.x22], by rw [hg _ (by simp), h.x28], by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after code that writes only the registers `rs`. -/
theorem Env.others {K W D : Addr} {R n : Nat} {SP : Addr} {s s' : State} (h : Env K W D R n SP s)
    {rs : List Reg} (hg : ∀ r, r ∉ rs → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hd : ∀ r ∈ envRegs, r ∉ rs := by decide) : Env K W D R n SP s' :=
  h.keep (fun r hr => hg r (hd r hr)) hsp hrd hwr

/-- An environment, after a call. -/
theorem Env.of_saved {K W D : Addr} {R n : Nat} {SP : Addr} {s s' : State} (h : Env K W D R n SP s)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env K W D R n SP s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

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

/-! ## The slots -/

/-- The public values the entry keeps in `W`: the tag length, the associated
data and its length, the nonce and its length. -/
structure Slots (W : Addr) (N A : Addr) (nl al tl : Nat) (m : Mem) : Prop where
  tl : m.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl
  aad : m.readW (W + BitVec.ofNat 64 aadO) 64 = A
  alen : m.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al
  nonce : m.readW (W + BitVec.ofNat 64 nO) 64 = N
  nlen : m.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl

/-- The parts of `W` the pieces write: `[0, 160)` and `[288, 2560)`. -/
abbrev wA (W : Addr) : Region := ⟨W, 160⟩
abbrev wB (W : Addr) : Region := ⟨W + BitVec.ofNat 64 288, 2272⟩

/-- What the pieces may change: those parts of `W` and the data. -/
abbrev mutR (W D : Addr) (n : Nat) : List Region := [wA W, wB W, ⟨D, n⟩]

theorem sub_wA {W : Addr} {d k : Nat} (h : d + k ≤ 160) : Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (wA W) := by
  simpa using Offset.sub W (d := d) (n := k) (e := 0) (k := 160) (by omega) (by omega)

theorem sub_wB {W : Addr} {d k : Nat} (h₁ : 288 ≤ d) (h : d + k ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (wB W) := Offset.sub W (by omega) (by omega)

/-- A part of `W` within `[0, 160)`, as a part the pieces may write. -/
theorem in_mutA {W D : Addr} {n d k : Nat} (h : d + k ≤ 160) :
    ∃ r' ∈ mutR W D n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' := ⟨_, List.mem_cons_self .., sub_wA h⟩

/-- A part of `W` from 288 on, as a part the pieces may write. -/
theorem in_mutB {W D : Addr} {n d k : Nat} (h₁ : 288 ≤ d) (h : d + k ≤ 2560) :
    ∃ r' ∈ mutR W D n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB h₁ h⟩

/-- The data, as a part the pieces may write. -/
theorem in_mutD {W D : Addr} {n : Nat} {r : Region} (h : Region.Sub r ⟨D, n⟩) :
    ∃ r' ∈ mutR W D n, Region.Sub r r' := ⟨_, by simp, h⟩

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {d k : Nat} (hd : 160 ≤ d ∧ d + k ≤ 288) :
    ∀ r ∈ mutR W D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 160) (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (hD.sub_right (Lay.wSub (by omega))).symm

/-- The key context misses the parts the pieces write. -/
theorem k_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ r ∈ mutR W D n, (⟨K, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact hD

/-- A word of `W` that the pieces do not write. -/
theorem kept_read {K W D : Addr} {n : Nat} (L : Lay K W) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {m m' : Mem} (h : Frame (mutR W D n) m m') {d : Nat} (hd : 160 ≤ d ∧ d + 8 ≤ 288) :
    m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  h.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_mut L hDW hd) (by decide)

/-- The slots, after a frame within the parts the pieces write. -/
theorem Slots.of_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {m m' : Mem} (h : Frame (mutR W D n) m m') {N A : Addr} {nl al tl : Nat}
    (S : Slots W N A nl al tl m) : Slots W N A nl al tl m' where
  tl := by rw [kept_read L hDW h (by decide), S.tl]
  aad := by rw [kept_read L hDW h (by decide), S.aad]
  alen := by rw [kept_read L hDW h (by decide), S.alen]
  nonce := by rw [kept_read L hDW h (by decide), S.nonce]
  nlen := by rw [kept_read L hDW h (by decide), S.nlen]

end VG.Proof.AesOcb.AArch64
