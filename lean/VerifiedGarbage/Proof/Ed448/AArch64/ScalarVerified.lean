module

import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLoop
import VerifiedGarbage.Proof.Ed448.ScalarWords
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ed448.AArch64.Scalar
meta import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLoop
meta import VerifiedGarbage.Proof.Ed448.ScalarWords
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Spec.Ed448.Contract
meta import VerifiedGarbage.Impl.Ed448.AArch64.Scalar

/-! ### `Ed448.AArch64.ScalarMulAddMain`, which this module and modules that import it used -/

section

/-! ### `Ed448.AArch64.ScalarMain`, which this module and modules that import it used -/

section

/-! ### `Ed448.AArch64.ScalarOperands`, which this module and modules that import it used -/

section

/-!
# Ed448 scalar multiply-add on AArch64: the operands

Each 57-byte input is copied to the working space as eight words, the top
one its last byte (`copy57_ok`), without reading past it; the values of
words in the working space are `mv`. The inputs are outside the working
space, so the copies leave them unchanged.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x word off Outside ofs contains_sc writeW_outside
  word_writeW_self)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- The value of the `n` words at `base + o`, lowest first. -/
def mv (m : Mem) (base : Addr) : Nat → Nat → Nat
  | _, 0 => 0
  | o, n + 1 => (word m base o).toNat + 2 ^ 64 * mv m base (o + 8) n

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n)
    (by omega_arith) (by omega_arith)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega_arith

/-- A word of a buffer disjoint from the working space, after writes inside it. -/
theorem readW_far {base p : Addr} {n o k d : Nat} {m m' : Mem} (h : Outside base o k m m')
    (hk : o + k ≤ 8192) (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hdn : d + 8 ≤ n)
    (hn : n ≤ 2 ^ 64) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  (Mem.readW_congr fun i hi => (h _ (Or.inr (by
    rw [Offset.add_add]; have := far hd (i := d + i) (by omega_arith) hn; omega_arith))).symm).symm

/-- One word copied from `src + 8i` to `x4 + o + 8i`. -/
def copyPair (src : Reg) (o i : Nat) : List Instr :=
  [.ldr .x .x5 src (8 * i), .str .x .x5 .x4 (o + 8 * i)]

theorem copy57_eq (src : Reg) (o : Nat) : copy57 src o =
    (List.range 7).flatMap (copyPair src o) ++
      ([.ldrb .x5 src 56, .str .x .x5 .x4 (o + 56)] : List Instr) := rfl

/-- What a copy keeps: all registers but `x5`, the permissions and the stack pointer. -/
structure CopyKeeps (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x5 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem CopyKeeps.trans {s t u : State} (h : CopyKeeps s t) (k : CopyKeeps t u) : CopyKeeps s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp⟩

/-- The setting of a copy: the base of the working space in `x4`, the
source in `src`, outside it. -/
structure CopyPre (s : State) (base p : Addr) (src : Reg) (o : Nat) : Prop where
  x4 : s.gpr .x4 = base
  hsrc : s.gpr src = p
  src5 : src ≠ .x5
  src4 : src ≠ .x4
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  rd : (⟨p, 57⟩ : Region) ∈ s.rd ++ s.wr
  disj : (⟨p, 57⟩ : Region).Disjoint ⟨base, 8192⟩
  o8 : o % 8 = 0
  olt : o + 64 ≤ 8192

theorem CopyPre.of_keeps {s t : State} {base p : Addr} {src : Reg} {o : Nat}
    (h : CopyPre s base p src o) (k : CopyKeeps s t) : CopyPre t base p src o :=
  ⟨(k.gpr _ (by decide)).trans h.x4, (k.gpr _ h.src5).trans h.hsrc, h.src5, h.src4, k.wr ▸ h.wr,
    by rw [k.rd, k.wr]; exact h.rd, h.disj, h.o8, h.olt⟩

theorem copyPair_ok {s : State} {base p : Addr} {src : Reg} {o : Nat} (h : CopyPre s base p src o)
    (i : Nat) (hi : i < 7) :
    WP isa (.block (copyPair src o i)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * i)) (s.mem.readW (p + BitVec.ofNat 64 (8 * i)) 64) ∧
      CopyKeeps s t := by
  rw [copyPair, WP.block_cons_iff]
  refine ⟨_, exec_ldr_x ⟨by omega_arith, by omega_arith⟩ (by
    rw [h.hsrc]; exact ⟨_, h.rd, Offset.contains_base p (by omega_arith) (by omega_arith)⟩), ?_⟩
  rw [WP.block_cons_iff]
  have hw : InRegions (s.write .x .x5 (s.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * i)) 64)).wr
      ((s.write .x .x5 (s.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * i)) 64)).gpr .x4 +
        BitVec.ofNat 64 (o + 8 * i)) 8 := by
    rw [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ _ (by decide), h.x4]
    exact ⟨_, h.wr, contains_sc (by have := h.olt; omega_arith)⟩
  refine ⟨_, exec_str_x ⟨by have := h.o8; omega_arith, by have := h.olt; omega_arith⟩ hw, WP.block_nil ?_⟩
  refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩⟩
  simp only [RegUpd.mem_write, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ _
    (show Reg.x4 ≠ .x5 by decide), BitVec.setWidth_eq, h.x4, h.hsrc]

/-- The first `n` words copied. -/
theorem copyWords_ok {s : State} {base p : Addr} {src : Reg} {o : Nat} (h : CopyPre s base p src o) :
    ∀ n ≤ 7, WP isa (.block ((List.range n).flatMap (copyPair src o))) s fun t =>
      (∀ j < n, word t.mem base (o + 8 * j) = s.mem.readW (p + BitVec.ofNat 64 (8 * j)) 64) ∧
      Outside base o (8 * n) s.mem t.mem ∧ CopyKeeps s t
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _,
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyWords_ok h n (by omega_arith)) fun a ⟨wa, oa, ka⟩ => ?_
    have olt := h.olt
    refine WP.mono (copyPair_ok (h.of_keeps ka) n (by omega_arith)) fun t ⟨mt, kt⟩ => ?_
    have rp : a.mem.readW (p + BitVec.ofNat 64 (8 * n)) 64 =
        s.mem.readW (p + BitVec.ofNat 64 (8 * n)) 64 :=
      readW_far oa (by omega_arith) h.disj (by omega_arith) (by omega_arith)
    refine ⟨fun j hj => ?_, ?_, ka.trans kt⟩
    · rw [mt, rp]
      rcases Nat.lt_or_ge j n with hj' | hj'
      · rw [Ed25519.AArch64.word_writeW_sep _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
        exact wa j hj'
      · obtain rfl : j = n := by omega_arith
        exact word_writeW_self _ _ _ _
    · rw [mt]
      exact oa.mono (Nat.le_refl _) (by omega_arith) |>.trans
        ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

theorem mv8 (m : Mem) (base : Addr) (o : Nat) : mv m base o 8 =
    (word m base o).toNat + 2 ^ 64 * ((word m base (o + 8)).toNat + 2 ^ 64 *
    ((word m base (o + 16)).toNat + 2 ^ 64 * ((word m base (o + 24)).toNat + 2 ^ 64 *
    ((word m base (o + 32)).toNat + 2 ^ 64 * ((word m base (o + 40)).toNat + 2 ^ 64 *
    ((word m base (o + 48)).toNat + 2 ^ 64 * (word m base (o + 56)).toNat)))))) := by
  simp only [mv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]

theorem toNat_byte64 (b : Byte) :
    (BitVec.setWidth (8 * 8) ((b.setWidth 32).setWidth 64)).toNat = b.toNat := by
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega_arith

/-- A 57-byte input copied as eight words. -/
theorem copy57_ok {s : State} {base p : Addr} {src : Reg} {o : Nat} (h : CopyPre s base p src o) :
    WP isa (.block (copy57 src o)) s fun t =>
      mv t.mem base o 8 = decodeLE (bytesAt s.mem p 57) ∧ Outside base o 64 s.mem t.mem ∧
      CopyKeeps s t := by
  rw [copy57_eq, WP.block_append_iff]
  refine WP.mono (copyWords_ok h 7 (Nat.le_refl _)) fun a ⟨wa, oa, ka⟩ => ?_
  have ha := h.of_keeps ka
  have olt := h.olt
  have o8 := h.o8
  have hb : InRegions (a.rd ++ a.wr) (a.gpr src + BitVec.ofNat 64 56) 1 := by
    rw [ha.hsrc]; exact ⟨_, ha.rd, Offset.contains_base p (d := 56) (n := 1) (by omega_arith) (by omega_arith)⟩
  have hw : InRegions a.wr (a.gpr .x4 + BitVec.ofNat 64 (o + 56)) 8 := by
    rw [ha.x4]; exact ⟨_, ha.wr, contains_sc (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, read_x,
    Size.bytes, show (56 : Nat) % 1 = 0 from rfl, show (56 : Nat) < 4096 * 1 from by decide, and_self,
    hb, show (o + 56) % 8 = 0 by omega_arith, show o + 56 < 4096 * 8 by omega_arith, hw,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  rw [ha.x4, ha.hsrc, Ed25519.AArch64.write64_eq_writeW]
  refine ⟨?_, oa.mono (Nat.le_refl _) (by omega_arith) |>.trans
    ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)),
    ka.trans ⟨fun r hr => by simp only [RegUpd.gpr_write, hr, ite_false], rfl, rfl, rfl⟩⟩
  have byte : (a.mem.read (p + BitVec.ofNat 64 56) 1) = s.mem (p + BitVec.ofNat 64 56) := by
    rw [Ed25519.AArch64.read_byte]
    exact oa _ (Or.inr (by have := far h.disj (i := 56) (by omega_arith) (by omega_arith); omega_arith))
  rw [mv8, decode57]
  have w0 := wa 0 (by omega_arith); have w1 := wa 1 (by omega_arith); have w2 := wa 2 (by omega_arith)
  have w3 := wa 3 (by omega_arith); have w4 := wa 4 (by omega_arith); have w5 := wa 5 (by omega_arith)
  have w6 := wa 6 (by omega_arith)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at w0 w1 w2 w3 w4 w5 w6
  simp only [Ed25519.AArch64.word_writeW_self]
  rw [Ed25519.AArch64.word_writeW_sep _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
    w0, w1, w2, w3, w4, w5, w6, byte, toNat_byte64]

theorem Outside.mv_eq {base : Addr} {o k : Nat} {m m' : Mem} (h : Outside base o k m m') :
    ∀ (n d : Nat), (d + 8 * n ≤ o ∨ o + k ≤ d) → d + 8 * n < 2 ^ 64 → mv m' base d n = mv m base d n
  | 0, _, _, _ => rfl
  | n + 1, d, hd, hl => by
    show (word m' base d).toNat + 2 ^ 64 * mv m' base (d + 8) n =
      (word m base d).toNat + 2 ^ 64 * mv m base (d + 8) n
    rw [Outside.mv_eq h n (d + 8) (by omega_arith) (by omega_arith), h.word (by omega_arith) (by omega_arith)]

/-- The bytes of a buffer disjoint from the working space, after writes
inside it only. -/
theorem bytesAt_outside {m m' : Mem} {p base : Addr} {n o k : Nat} (h : Outside base o k m m')
    (hk : o + k ≤ 8192) (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n := by
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  exact h _ (Or.inr (by have := far hd hi hn; omega_arith))

/-- The operands: `k` then `r` at `XK`, `s` then one at `YS`. -/
theorem operands_ok {s : State} {base : Addr} (hb : s.gpr .x4 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hr : (⟨s.gpr .x1, 57⟩ : Region) ∈ s.rd ++ s.wr) (hk : (⟨s.gpr .x2, 57⟩ : Region) ∈ s.rd ++ s.wr)
    (hs : (⟨s.gpr .x3, 57⟩ : Region) ∈ s.rd ++ s.wr)
    (dr : (⟨s.gpr .x1, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    (dk : (⟨s.gpr .x2, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    (ds : (⟨s.gpr .x3, 57⟩ : Region).Disjoint ⟨base, 8192⟩) :
    WP isa (.block operands) s fun t =>
      mv t.mem base XK 8 = decodeLE (bytesAt s.mem (s.gpr .x2) 57) ∧
      mv t.mem base (XK + 64) 8 = decodeLE (bytesAt s.mem (s.gpr .x1) 57) ∧
      mv t.mem base YS 8 = decodeLE (bytesAt s.mem (s.gpr .x3) 57) ∧
      word t.mem base (YS + 64) = 1 ∧ Outside base XK 200 s.mem t.mem ∧
      t.gpr .x2 = base ∧ (∀ r, r ∉ [Reg.x2, .x5] → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [operands, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (copy57_ok ⟨hb, rfl, by decide, by decide, hw, hk, dk, by decide, by decide⟩)
    fun a ⟨va, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy57_ok ⟨(ka.gpr _ (by decide)).trans hb, (ka.gpr _ (by decide)), by decide,
    by decide, ka.wr ▸ hw, by rw [ka.rd, ka.wr]; exact hr, dr, by decide, by decide⟩)
    fun b ⟨vb, ob, kb⟩ => ?_
  rw [WP.block_append_iff]
  have kab := ka.trans kb
  refine WP.mono (copy57_ok ⟨(kab.gpr _ (by decide)).trans hb, (kab.gpr _ (by decide)), by decide,
    by decide, kab.wr ▸ hw, by rw [kab.rd, kab.wr]; exact hs, ds, by decide, by decide⟩)
    fun c ⟨vc, oc, kc⟩ => ?_
  have kac := kab.trans kc
  have hwc : InRegions c.wr (c.gpr .x4 + BitVec.ofNat 64 (YS + 64)) 8 := by
    rw [kac.gpr _ (by decide), hb, kac.wr]; exact ⟨_, hw, contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, read_x,
    Impl.Ed25519.AArch64.mov, Size.bytes, show (YS + 64) % 8 = 0 from rfl,
    show YS + 64 < 4096 * 8 from by decide, show (0 : Nat) < 4096 from by decide,
    show 16 * 0 < Size.x.bits from by decide, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hwc,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.some.injEq, exists_eq_left']
  have x4c : c.gpr .x4 = base := (kac.gpr _ (by decide)).trans hb
  have one : BitVec.setWidth (8 * 8) (BitVec.setWidth 64
      (BitVec.setWidth Size.x.bits (1 : BitVec 16) <<< (16 * 0))) = (1 : BitVec 64) := by decide
  rw [x4c, Ed25519.AArch64.write64_eq_writeW, one]
  have ho : Outside base (YS + 64) 8 c.mem (c.mem.writeW (off base (YS + 64)) (1 : BitVec 64)) :=
    writeW_outside _ _ _ (by decide)
  refine ⟨?_, ?_, ?_, word_writeW_self _ _ _ _, ?_, by simp only [BitVec.add_zero, BitVec.setWidth_eq],
    fun r hr => ?_, kac.rd, kac.wr, by simp only [RegUpd.sp_write]; exact kac.sp⟩
  · rw [Outside.mv_eq ho 8 XK (by decide) (by decide), Outside.mv_eq oc 8 XK (by decide) (by decide),
      Outside.mv_eq ob 8 XK (by decide) (by decide), va]
  · rw [Outside.mv_eq ho 8 (XK + 64) (by decide) (by decide), Outside.mv_eq oc 8 (XK + 64) (by decide) (by decide), vb,
      bytesAt_outside oa (by decide) dr (by decide)]
  · rw [Outside.mv_eq ho 8 YS (by decide) (by decide), vc, bytesAt_outside ob (by decide) ds (by decide),
      bytesAt_outside oa (by decide) ds (by decide)]
  · exact (((oa.mono (by decide) (by decide)).trans (ob.mono (by decide) (by decide))).trans
      (oc.mono (by decide) (by decide))).trans (ho.mono (by decide) (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2, ite_false]
    exact kac.gpr r hr.2

end VG.Proof.Ed448.AArch64

end

end

/-! ### `Ed448.AArch64.ScalarIO`, which only this module used -/

section

/-! ### `Ed448.AArch64.MemWords`, which only this module used -/

section

/-!
# Ed448 on AArch64: words stored and loaded relative to a register

A list of `str` (`strs`) or `ldr` (`ldrs`) at offsets from one base
register, proven once by induction on the list: the stores write the words
in turn (`wrs`), each of which a later read finds if the offsets are
separate (`word_wrs`), and the loads read them.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x word off Outside ofs writeW_outside word_writeW_sep
  word_writeW_self)

/-- `str x_r, [b, #d]` for each `(r, d)`. -/
def strs (b : Reg) (ps : List (Reg × Nat)) : List Instr := ps.map fun p => .str .x p.1 b p.2

/-- `ldr x_r, [b, #d]` for each `(r, d)`. -/
def ldrs (b : Reg) (ps : List (Reg × Nat)) : List Instr := ps.map fun p => .ldr .x p.1 b p.2

/-- The registers' values `g` written in turn at their offsets from `base`. -/
def wrs (m : Mem) (base : Addr) (g : Reg → BitVec 64) : List (Reg × Nat) → Mem
  | [] => m
  | p :: ps => wrs (m.writeW (off base p.2) (g p.1)) base g ps

theorem strs_ok {base : Addr} (b : Reg) : ∀ (ps : List (Reg × Nat)) (s : State), s.gpr b = base →
    (∀ p ∈ ps, p.2 % 8 = 0 ∧ p.2 < 32768 ∧ InRegions s.wr (off base p.2) 8) →
    WP isa (.block (strs b ps)) s fun t => t = { s with mem := wrs s.mem base s.gpr ps }
  | [], s, _, _ => WP.block_nil rfl
  | p :: ps, s, hb, hw => by
    obtain ⟨h8, hl, hr⟩ := hw p List.mem_cons_self
    rw [strs, List.map_cons, WP.block_cons_iff]
    refine ⟨_, exec_str_x ⟨h8, hl⟩ (by rw [hb]; exact hr), ?_⟩
    rw [hb]
    exact WP.mono (strs_ok b ps _ hb fun q hq => hw q (List.mem_cons_of_mem _ hq)) fun t ht => ht

/-- Two words at offsets `d` and `e` do not overlap. -/
def Sep8 (d e : Nat) : Prop := d + 8 ≤ e ∨ e + 8 ≤ d

instance (d e : Nat) : Decidable (Sep8 d e) := inferInstanceAs (Decidable (_ ∨ _))

theorem word_wrs_of_sep (m : Mem) (base : Addr) (g : Reg → BitVec 64) :
    ∀ (ps : List (Reg × Nat)) {d : Nat}, (∀ p ∈ ps, Sep8 p.2 d ∧ p.2 + 8 ≤ 2 ^ 64) →
      d + 8 ≤ 2 ^ 64 → word (wrs m base g ps) base d = word m base d
  | [], _, _, _ => rfl
  | p :: ps, d, h, hd => by
    rw [wrs, word_wrs_of_sep _ base g ps (fun q hq => h q (List.mem_cons_of_mem _ hq)) hd]
    obtain ⟨h1, h2⟩ := h p List.mem_cons_self
    exact word_writeW_sep m base _ h1.symm h2 hd

theorem word_wrs (m : Mem) (base : Addr) (g : Reg → BitVec 64) :
    ∀ (ps : List (Reg × Nat)), ps.Pairwise (fun p q => Sep8 p.2 q.2) →
      (∀ p ∈ ps, p.2 + 8 ≤ 2 ^ 64) → ∀ p ∈ ps, word (wrs m base g ps) base p.2 = g p.1
  | [], _, _, _, hp => nomatch hp
  | p :: ps, hs, hl, q, hq => by
    rw [List.pairwise_cons] at hs
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [wrs, word_wrs_of_sep _ base g ps (fun r hr => ⟨hs.1 r hr |>.symm, hl r
        (List.mem_cons_of_mem _ hr)⟩) (hl _ List.mem_cons_self)]
      exact word_writeW_self m base _ _
    · exact word_wrs _ base g ps hs.2 (fun r hr => hl r (List.mem_cons_of_mem _ hr)) q hq
where
  symm {a b : Nat} (h : Sep8 a b) : Sep8 b a := h.symm

theorem wrs_outside (m : Mem) (base : Addr) (g : Reg → BitVec 64) {o n : Nat} (hn : o + n < 2 ^ 64) :
    ∀ (ps : List (Reg × Nat)), (∀ p ∈ ps, o ≤ p.2 ∧ p.2 + 8 ≤ o + n) →
      Outside base o n m (wrs m base g ps)
  | [], _ => Outside.refl _ _ _ _
  | p :: ps, h => by
    obtain ⟨h1, h2⟩ := h p List.mem_cons_self
    exact ((writeW_outside m base (g p.1) (by omega_using [hn, h2])).mono h1 (by omega_using [h2])).trans
      (wrs_outside _ base g hn ps fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem wrs_frame {R : Region} {m : Mem} (base : Addr) (g : Reg → BitVec 64) :
    ∀ (ps : List (Reg × Nat)) (m' : Mem), Frame [R] m m' →
      (∀ p ∈ ps, R.Contains (off base p.2) 8) → Frame [R] m (wrs m' base g ps)
  | [], _, h, _ => h
  | p :: ps, _, h, hc => wrs_frame base g ps _
      (h.writeW (List.mem_singleton_self _) _ (hc p List.mem_cons_self))
      fun q hq => hc q (List.mem_cons_of_mem _ hq)

theorem ldrs_ok {base : Addr} (b : Reg) : ∀ (ps : List (Reg × Nat)) (s : State), s.gpr b = base →
    (∀ p ∈ ps, p.2 % 8 = 0 ∧ p.2 < 32768 ∧ InRegions (s.rd ++ s.wr) (off base p.2) 8 ∧ p.1 ≠ b) →
    (ps.map (·.1)).Nodup →
    WP isa (.block (ldrs b ps)) s fun t =>
      (∀ p ∈ ps, t.gpr p.1 = word s.mem base p.2) ∧ Keeps (ps.map (·.1)) s t
  | [], s, _, _, _ => WP.block_nil ⟨(fun _ h => nomatch h), Keeps.refl _ _⟩
  | p :: ps, s, hb, hw, hnd => by
    obtain ⟨h8, hl, hr, hpb⟩ := hw p List.mem_cons_self
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [ldrs, List.map_cons, WP.block_cons_iff]
    refine ⟨_, exec_ldr_x ⟨h8, hl⟩ (by rw [hb]; exact hr), ?_⟩
    let s1 := s.write .x p.1 (s.mem.readW (s.gpr b + BitVec.ofNat 64 p.2) 64)
    have k1 : ∀ r, r ≠ p.1 → s1.gpr r = s.gpr r := fun r hr =>
      RegUpd.gpr_write_of_ne s .x _ hr
    refine WP.mono (ldrs_ok b ps s1 ((k1 b (Ne.symm hpb)).trans hb) (fun q hq => hw q
      (List.mem_cons_of_mem _ hq)) hnd.2) fun t ⟨ht, kt⟩ => ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [kt.gpr _ hnd.1, RegUpd.gpr_write_self, BitVec.setWidth_eq, hb]
      · exact ht q hq
    · refine ⟨fun r hr => ?_, kt.mem, kt.rd, kt.wr, kt.sp⟩
      rw [List.map_cons, List.mem_cons, not_or] at hr
      rw [kt.gpr r hr.2, k1 r hr.1]

end VG.Proof.Ed448.AArch64

end

end


/-!
# Ed448 scalar arithmetic on AArch64: entry and exit

The callee-saved registers saved in the working space and restored, the
constants set up, the remainder of the top bytes of a 114-byte input, and
the remainder written out as 57 bytes.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x const64_ok word off Outside ofs contains_sc)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-! ## The callee-saved registers -/

/-- The callee-saved registers `g` in the working space at `base`. -/
def Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ p ∈ saved, word m base p.2 = g p.1

theorem saved_ok : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 + 8 ≤ 64 := by decide

theorem saved_sep : saved.Pairwise (fun p q => Sep8 p.2 q.2) := by decide

theorem saveRegs_ok {s : State} {base : Addr} (b : Reg) (hb : s.gpr b = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block (saveRegs b)) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 0 64 s.mem t.mem ∧ Saved base s.gpr t.mem := by
  refine WP.mono (strs_ok b saved s hb fun p hp => ?_) fun t ht => ?_
  · obtain ⟨h8, hl⟩ := saved_ok p hp
    exact ⟨h8, by omega_using [hl], _, hw, contains_sc (by omega_using [hl])⟩
  · subst ht
    refine ⟨rfl, rfl, rfl, rfl,
      wrs_outside _ _ _ (by omega_using []) _ fun p hp => ⟨Nat.zero_le _, (saved_ok p hp).2⟩,
      fun p hp => word_wrs _ _ _ _ saved_sep (fun q hq => by have := (saved_ok q hq).2; omega_using [this]) p hp⟩

/-- The registers `saved` holds. -/
def savedRegs : List Reg := saved.map (·.1)

theorem restoreRegs_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64} (hsv : Saved base g s.mem) :
    WP isa (.block restoreRegs) s fun t =>
      (∀ p ∈ saved, t.gpr p.1 = g p.1) ∧ Keeps savedRegs s t := by
  refine WP.mono (ldrs_ok .x2 saved s hb (fun p hp => ?_) (by decide)) fun t ⟨ht, kt⟩ =>
    ⟨fun p hp => (ht p hp).trans (hsv p hp), kt⟩
  obtain ⟨h8, hl⟩ := saved_ok p hp
  exact ⟨h8, by omega_using [hl], ⟨_, List.mem_append_right _ hw, contains_sc (by omega_using [hl])⟩,
    (by decide : ∀ p ∈ saved, p.1 ≠ .x2) p hp⟩

/-! ## The constants -/

theorem consts_ok (s : State) :
    WP isa (.block consts) s fun t => Consts t ∧ Keeps constRegs s t := by
  simp only [consts, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s C0 c0) fun a ⟨a0, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok a C1 c1) fun b ⟨b1, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok b C2 c2) fun c ⟨c2', kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok c C3 c3) fun d ⟨d3, kd⟩ => ?_
  apply WP.of_runBlock
  simp only [KT, Z, runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [C0, RegUpd.gpr_write, reduceCtorEq, ite_false]
    rw [kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide)]; exact a0
  · simp only [C1, RegUpd.gpr_write, reduceCtorEq, ite_false]
    rw [kd.gpr _ (by decide), kc.gpr _ (by decide)]; exact b1
  · simp only [C2, RegUpd.gpr_write, reduceCtorEq, ite_false]
    rw [kd.gpr _ (by decide)]; exact c2'
  · simp only [C3, RegUpd.gpr_write, reduceCtorEq, ite_false]; exact d3
  · simp only [KT, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [Z, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [constRegs, C0, C1, C2, C3, KT, Z, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    simp only [RegUpd.gpr_write, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
    rw [kd.gpr _ (by simp [C3, hr.2.2.2.1]), kc.gpr _ (by simp [C2, hr.2.2.1]),
      kb.gpr _ (by simp [C1, hr.2.1]), ka.gpr _ (by simp [C0, hr.1])]
  · exact kd.mem.trans (kc.mem.trans (kb.mem.trans ka.mem))
  · exact kd.rd.trans (kc.rd.trans (kb.rd.trans ka.rd))
  · exact kd.wr.trans (kc.wr.trans (kb.wr.trans ka.wr))
  · exact kd.sp.trans (kc.sp.trans (kb.sp.trans ka.sp))

/-! ## The top bytes -/

theorem toNat_byte (b : Byte) : ((b.setWidth 32).setWidth 64).toNat = b.toNat := by
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega_using []

theorem decode_two (m : Mem) (p : Addr) :
    decodeLE (bytesAt m p 2) = (m p).toNat + 256 * (m (p + 1)).toNat := by
  simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, decodeLE, BitVec.add_zero, Nat.mul_zero, Nat.add_zero]
  rfl

/-- The remainder of the top two bytes of a 114-byte input. -/
theorem init114_ok (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 112) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 113) 1) :
    WP isa (.block init114) s fun t =>
      rem t = decodeLE (bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 112) 2) ∧
      t.gpr .x3 = BitVec.ofNat 64 112 ∧
      Keeps [.x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] s t := by
  apply WP.of_runBlock
  simp only [init114, zeroHigh, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    show (112 : Nat) % 1 = 0 from rfl,
    show (112 : Nat) < 4096 * 1 from by decide, show (113 : Nat) < 4096 * 1 from by decide,
    and_self, h0, h1, show 8 < Size.x.bits from by decide, show 16 * 0 < Size.x.bits from by decide,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [decode_two, show s.gpr .x1 + BitVec.ofNat 64 112 + 1 = s.gpr .x1 + BitVec.ofNat 64 113 by
      rw [BitVec.add_assoc]; rfl]
    simp only [rem, rv, R, RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    have b0 := (s.mem (s.gpr .x1 + BitVec.ofNat 64 112)).isLt
    have b1 := (s.mem (s.gpr .x1 + BitVec.ofNat 64 113)).isLt
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, toNat_byte, toNat_byte, Nat.shiftLeft_eq]
    have z : (BitVec.setWidth Size.x.bits (0 : BitVec 16) <<< (16 * 0)).toNat = 0 := by decide
    rw [Ed25519.AArch64.read_byte, Ed25519.AArch64.read_byte, z]
    omega_using []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

/-! ## The result -/

theorem readW_write_byte (m : Mem) (q : Addr) {d e : Nat} (h : d + 8 ≤ e) (he : e < 2 ^ 64)
    (v : BitVec (8 * 1)) :
    (m.write (q + BitVec.ofNat 64 e) 1 v).readW (q + BitVec.ofNat 64 d) 64 =
      m.readW (q + BitVec.ofNat 64 d) 64 := by
  simp only [Mem.readW]
  rw [Mem.read_write_sep (Offset.sep q (Or.inl h) (by omega_using [h, he]) (by omega_using [he])) (by decide)]

theorem write_byte_self (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v a = v := by
  simp only [Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_lt_one, ite_true, Nat.mul_zero]
  exact BitVec.extractLsb'_eq_self

theorem toNat_zero8 : (0 : BitVec (8 * 1)).toNat = 0 := rfl

theorem outWords_ok : ∀ p ∈ outWords, p.2 % 8 = 0 ∧ p.2 + 8 ≤ 56 := by decide

theorem outWords_sep : outWords.Pairwise (fun p q => Sep8 p.2 q.2) := by decide

/-- The zero byte at `q + 56`. -/
theorem zeroByte_ok {s : State} {q : Addr} (hq : s.gpr .x0 = q)
    (hb : InRegions s.wr (q + BitVec.ofNat 64 56) 1) :
    WP isa (.block [.movz .x .x12 0 0, .strb .x12 .x0 56]) s fun t =>
      t.mem = s.mem.write (q + BitVec.ofNat 64 56) 1 0 ∧ (∀ r, r ≠ .x12 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, State.read, hq,
    show 16 * 0 < Size.x.bits from by decide, show (56 : Nat) % 1 = 0 from rfl,
    show (56 : Nat) < 4096 * 1 from by decide, and_self, RegUpd.wr_write, RegUpd.gpr_write,
    RegUpd.mem_write, ite_true, ite_false, reduceCtorEq, hb, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨congrArg _ (by decide), fun r hr => by simp only [hr, ite_false], rfl, trivial, rfl⟩

/-- The remainder to the 57 bytes at `q`. -/
theorem outStore_ok {s : State} {q : Addr} (hq : s.gpr .x0 = q) (hw : (⟨q, 57⟩ : Region) ∈ s.wr) :
    WP isa (.block (outWords.map (fun p => .str .x p.1 .x0 p.2) ++
        ([.movz .x .x12 0 0, .strb .x12 .x0 56] : List Instr))) s fun t =>
      decodeLE (bytesAt t.mem q 57) = rem s ∧ Frame [⟨q, 57⟩] s.mem t.mem ∧
      (∀ r, r ≠ .x12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rw [WP.block_append_iff]
  refine WP.mono (strs_ok .x0 outWords s hq fun p hp => ?_) fun a ha => ?_
  · obtain ⟨h8, hl⟩ := outWords_ok p hp
    exact ⟨h8, by omega_using [hl], _, hw, Offset.contains_base q (by omega_using [hl]) (by omega_using [hl])⟩
  subst ha
  have hb : InRegions s.wr (q + BitVec.ofNat 64 56) 1 :=
    ⟨_, hw, Offset.contains_base q (d := 56) (n := 1) (by omega_using []) (by omega_using [])⟩
  refine WP.mono (zeroByte_ok hq hb) fun t ⟨mt, gt, rdt, wrt, spt⟩ => ?_
  refine ⟨?_, ?_, gt, rdt, wrt, spt⟩
  · rw [mt, decode57]
    have hw' : ∀ p ∈ outWords, word (wrs s.mem q s.gpr outWords) q p.2 = s.gpr p.1 :=
      word_wrs _ _ _ _ outWords_sep fun p hp => by have := (outWords_ok p hp).2; omega_using [this]
    have w0 := hw' (.x5, 0) (by decide)
    have w1 := hw' (.x6, 8) (by decide)
    have w2 := hw' (.x7, 16) (by decide)
    have w3 := hw' (.x8, 24) (by decide)
    have w4 := hw' (.x9, 32) (by decide)
    have w5 := hw' (.x10, 40) (by decide)
    have w6 := hw' (.x11, 48) (by decide)
    simp (disch := decide) only [readW_write_byte, write_byte_self, w0, w1, w2, w3, w4, w5, w6,
      toNat_zero8, Nat.mul_zero, Nat.add_zero]
    rw [rem_eq]
  · rw [mt]
    exact (wrs_frame q s.gpr outWords s.mem (Frame.refl _ _) fun p hp =>
      Offset.contains_base q (by have := (outWords_ok p hp).2; omega_using [this])
        (by have := (outWords_ok p hp).2; omega_using [this])).write
      (List.mem_singleton_self _) _ (Offset.contains_base q (d := 56) (n := 1) (by omega_using []) (by omega_using []))

end VG.Proof.Ed448.AArch64

end

end


/-!
# Ed448 scalar reduction on AArch64: the whole function

The contract the proof is written against (`scalarReduceLocal`, stated for
AArch64), and the
correctness of `vg_ed448_scalar_reduce` against it: the working space is
written only where the callee-saved registers are saved, so the input is
read unchanged; they are restored before the result is written.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps word off Outside ofs contains_sc)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- A buffer of `n` bytes is its own encoding. -/
theorem bytesAt_encode (m : Mem) (q : Addr) (n : Nat) :
    bytesAt m q n = Spec.Ed448.encodeLE n (decodeLE (bytesAt m q n)) := by
  rw [encodeLE_eq, decodeLE_eq, bytesAt_eq, Proof.X25519.leNum_bytesAt_read,
    ← Proof.X25519.bytesAt_leBytes]

/-- `vg_ed448_scalar_reduce(out = x0, wide = x1, scratch = x2)`. -/
def scalarReduceLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 114⟩] ∧ s.wr = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x1, 114⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩
  post s t := bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarReduce (bytesAt s.mem (s.gpr .x1) 114)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

/-- `finish`: the callee-saved registers restored, and the remainder written to the 57 bytes at `q`. -/
theorem finish_ok {s : State} {base q : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64} (hsv : Saved base g s.mem)
    (hq : s.gpr .x0 = q) (hwo : (⟨q, 57⟩ : Region) ∈ s.wr) :
    WP isa (.block finish) s fun t =>
      bytesAt t.mem q 57 = Spec.Ed448.encodeLE 57 (rem s) ∧ (∀ p ∈ saved, t.gpr p.1 = g p.1) ∧
      (∀ r, r ∉ Reg.x12 :: savedRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp := by
  rw [finish, List.append_assoc, WP.block_append_iff]
  refine WP.mono (restoreRegs_ok hb hw hsv) fun a ⟨ra, ka⟩ => ?_
  have qa : a.gpr .x0 = q := (ka.gpr _ (by decide)).trans hq
  refine WP.mono (outStore_ok qa (ka.wr ▸ hwo)) fun t ⟨vt, _, gt, _, _, spt⟩ => ?_
  refine ⟨?_, fun p hp => (gt _ ((by decide : ∀ p ∈ saved, p.1 ≠ .x12) p hp)).trans (ra p hp),
    fun r hr => ?_, spt.trans ka.sp⟩
  · rw [bytesAt_encode, vt, show rem a = rem s from Keeps.rv_eq ka (by decide)]
  · simp only [List.mem_cons, not_or] at hr
    rw [gt r hr.1, ka.gpr r hr.2]

theorem scalarReduce_correct {s : State} (hs : scalarReduceLocal.pre s) :
    WP isa scalarReduce s fun t => abiPreserved s t ∧ scalarReduceLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  obtain ⟨hr, hw, hd⟩ := hs
  have hws : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have hwo : (⟨s.gpr .x0, 57⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarReduce]
  apply WP.seq
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .x2 rfl hws) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₁) fun s₂ ⟨c₂, k₂⟩ => ?_
  have x1₂ : s₂.gpr .x1 = s.gpr .x1 := (k₂.gpr _ (by decide)).trans (congrFun g₁ _)
  have rdw₂ : s₂.rd ++ s₂.wr = s.rd ++ s.wr := by rw [k₂.rd, k₂.wr, rd₁, wr₁]
  have inw : ∀ d n, d + n ≤ 114 → InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x1 + BitVec.ofNat 64 d) n :=
    fun d n h => ⟨⟨s.gpr .x1, 114⟩, by rw [rdw₂, hr]; simp,
      by rw [x1₂]; exact Offset.contains_base _ h (by omega_using [h])⟩
  refine WP.mono (init114_ok s₂ (inw 112 1 (by omega_using [])) (inw 113 1 (by omega_using [])))
    fun s₃ ⟨v₃, b₃, k₃⟩ => ?_
  have c₃ : Consts s₃ := c₂.of_keeps k₃ (by decide)
  have x1₃ : s₃.gpr .x1 = s.gpr .x1 := (k₃.gpr _ (by decide)).trans x1₂
  have m₃ : s₃.mem = s₁.mem := k₃.mem.trans k₂.mem
  apply WP.seq
  have hi : LoopInv 114 s₃ 14 s₃ := by
    refine ⟨by decide, by decide, b₃, ?_, Keeps.refl _ _⟩
    rw [v₃, k₃.mem, k₃.gpr .x1 (by decide)]
    simp only [Nat.reduceMul, Nat.reduceSub]
    have hlt := decodeLE_lt' (bytesAt s₂.mem (s₂.gpr .x1 + BitVec.ofNat 64 112) 2)
    rw [bytesAt_length] at hlt
    have : (256 : Nat) ^ 2 < L := by decide +kernel
    exact (Nat.mod_eq_of_lt (by omega_using [hlt, this])).symm
  refine WP.mono (scalarLoop_ok s₃ c₃ (by decide) hi fun k hk => by
      rw [k₃.rd, k₃.wr, ← x1₂.trans x1₃.symm]
      exact inw (8 * k) 8 (by omega_using [hk])) fun s₄ ⟨v₄, k₄⟩ => ?_
  have x2₄ : s₄.gpr .x2 = s.gpr .x2 := by
    rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), g₁]
  have x0₄ : s₄.gpr .x0 = s.gpr .x0 := by
    rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), g₁]
  have wr₄ : s₄.wr = s.wr := by rw [k₄.wr, k₃.wr, k₂.wr, wr₁]
  have sv₄ : Saved (s.gpr .x2) s.gpr s₄.mem := by rw [k₄.mem, m₃]; exact sv₁
  refine WP.mono (finish_ok x2₄ (wr₄ ▸ hws) sv₄ x0₄ (wr₄ ▸ hwo)) fun t ⟨bt, rt, gt, spt⟩ => ?_
  refine ⟨⟨fun r hpres => ?_, spt.trans (k₄.sp.trans (k₃.sp.trans (k₂.sp.trans sp₁)))⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hpres
    rcases hpres with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.x19, 0) (by decide)
    · exact rt (.x20, 8) (by decide)
    · exact rt (.x21, 16) (by decide)
    · exact rt (.x22, 24) (by decide)
    · exact rt (.x23, 32) (by decide)
    · exact rt (.x24, 40) (by decide)
    · exact rt (.x25, 48) (by decide)
    · exact rt (.x26, 56) (by decide)
    all_goals
      rw [gt _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), g₁]
  · show bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarReduce (bytesAt s.mem (s.gpr .x1) 114)
    rw [bt, v₄, x1₃, m₃, bytesAt_outside o₁ (by decide) hd (by decide)]
    rfl

end VG.Proof.Ed448.AArch64

end

end

/-! ### `Ed448.AArch64.ScalarColumns`, which only this module used -/

section

/-!
# Ed448 scalar multiply-add on AArch64: product scanning

A term (`term_ok`): `x_i · y_j`, loaded from the working space, added to a
three-word accumulator; a column's terms (`terms_ok`), by induction on them;
and the sixteen columns (`columns_ok`), by induction on the columns, each
storing its low word at `ACC` and passing the rest of its accumulator on, in
`x5–x7` rotated. The columns of `r + k s` sum to it (`mulCols_sum`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x word off Outside ofs contains_sc writeW_outside
  word_writeW_self)

/-- The working space at `base`, in `x2`, with zero in `x26`. -/
structure Wk (s : State) (base : Addr) : Prop where
  x2 : s.gpr .x2 = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  z : s.gpr .x26 = 0

theorem Wk.of_keeps {rs : List Reg} {s t : State} {base : Addr} (h : Wk s base) (k : Keeps rs s t)
    (h2 : .x2 ∉ rs) (h26 : .x26 ∉ rs) : Wk t base :=
  ⟨(k.gpr _ h2).trans h.x2, k.wr ▸ h.wr, (k.gpr _ h26).trans h.z⟩

/-- The `i`-th left and `j`-th right operand. -/
abbrev xw (m : Mem) (base : Addr) (i : Nat) : Nat := (word m base (XK + 8 * i)).toNat
abbrev yw (m : Mem) (base : Addr) (j : Nat) : Nat := (word m base (YS + 8 * j)).toNat

theorem umulh_eq (a b : BitVec 64) :
    (a * b).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat =
      a.toNat * b.toNat := mul_halves a b

/-- `term`: `a₀ a₁ a₂ += x_i · y_j`. -/
theorem term_ok {s : State} {base : Addr} {a0 a1 a2 : Reg} (hs : Wk s base)
    (hd : [a0, a1, a2, .x12, .x13, .x14, .x15, .x26, .x2].Nodup) {i j : Nat} (hi : i < 16)
    (hj : j < 9) (hb : rv s [a0, a1, a2] + xw s.mem base i * yw s.mem base j < 2 ^ 192) :
    WP isa (.block (term a0 a1 a2 i j)) s fun t =>
      rv t [a0, a1, a2] = rv s [a0, a1, a2] + xw s.mem base i * yw s.mem base j ∧
      Keeps [.x12, .x13, .x14, .x15, a0, a1, a2] s t := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h0a, h0b, h0c, h0d, h0z, h0x⟩, ⟨h12, h1a, h1b, h1c, h1d, h1z, h1x⟩,
    ⟨h2a, h2b, h2c, h2d, h2z, h2x⟩, -⟩ := hd
  have l1 : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (XK + 8 * i)) 8 := by
    rw [hs.x2]; exact ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [XK]; omega_arith)⟩
  have l2 : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (YS + 8 * j)) 8 := by
    rw [hs.x2]; exact ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [YS]; omega_arith)⟩
  apply WP.of_runBlock
  simp only [term, Z, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    Size.bytes, show (XK + 8 * i) % 8 = 0 by simp only [XK]; omega_arith,
    show XK + 8 * i < 4096 * 8 by simp only [XK]; omega_arith,
    show (YS + 8 * j) % 8 = 0 by simp only [YS]; omega_arith,
    show YS + 8 * j < 4096 * 8 by simp only [YS]; omega_arith, and_self, l1, l2,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.c_addWithCarry, BitVec.setWidth_eq, Ne.symm h01, Ne.symm h02, Ne.symm h12,
    h0a, h0b, h0c, h0d, h1a, h1b, h1c, h1d, h2a, h2b, h2c, h2d,
    Ne.symm h0d, Ne.symm h0z, Ne.symm h1z, hs.z,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [rv, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, BitVec.setWidth_eq, h01, h02, h12,
      Ne.symm h01, Ne.symm h02, Ne.symm h12, ite_true, ite_false, Nat.mul_zero, Nat.add_zero]
    have ex : xw s.mem base i = (s.mem.read (s.gpr .x2 + BitVec.ofNat 64 (XK + 8 * i)) 8).toNat := by
      simp only [xw, word, off, Mem.readW, hs.x2, BitVec.setWidth_eq]
    have ey : yw s.mem base j = (s.mem.read (s.gpr .x2 + BitVec.ofNat 64 (YS + 8 * j)) 8).toNat := by
      simp only [yw, word, off, Mem.readW, hs.x2, BitVec.setWidth_eq]
    rw [ex, ey] at hb ⊢
    simp only [rv, Nat.mul_zero, Nat.add_zero] at hb
    generalize s.mem.read (s.gpr .x2 + BitVec.ofNat 64 (XK + 8 * i)) 8 = x at hb ⊢
    generalize s.mem.read (s.gpr .x2 + BitVec.ofNat 64 (YS + 8 * j)) 8 = y at hb ⊢
    have hp := umulh_eq x y
    generalize x * y = lo at hp ⊢
    generalize BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64) = hi at hp ⊢
    have v0 := addWithCarry_val (s.gpr a0) lo false
    generalize decide (2 ^ 64 ≤ (s.gpr a0).toNat + lo.toNat + false.toNat) = c0 at v0 ⊢
    have v1 := addWithCarry_val (s.gpr a1) hi c0
    generalize decide (2 ^ 64 ≤ (s.gpr a1).toNat + hi.toNat + c0.toNat) = c1 at v1 ⊢
    have v2 : (s.gpr a2 + 0 + BitVec.ofNat 64 c1.toNat).toNat = ((s.gpr a2).toNat + c1.toNat) % 2 ^ 64 := by
      rw [show s.gpr a2 + 0 = s.gpr a2 from BitVec.add_zero _, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := Bool.toNat_le c1
      rw [Nat.mod_eq_of_lt (a := c1.toNat) (by omega_arith)]
    rw [v2]
    have := (s.gpr a0).isLt; have := (s.gpr a1).isLt; have := (s.gpr a2).isLt
    have := Bool.toNat_le c0; have := Bool.toNat_le c1
    generalize (s.gpr a0 + lo + BitVec.ofNat 64 false.toNat).toNat = A0 at v0 ⊢
    simp only [Bool.toNat_false, Nat.add_zero] at v0
    generalize (s.gpr a1 + hi + BitVec.ofNat 64 c0.toNat).toNat = A1 at v1 ⊢
    generalize x.toNat * y.toNat = P at hp hb ⊢
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

/-- The sum of a column's terms. -/
def colSum (xv yv : Nat → Nat) (ts : List (Nat × Nat)) : Nat := (ts.map fun t => xv t.1 * yv t.2).sum

theorem colSum_cons (xv yv : Nat → Nat) (t : Nat × Nat) (ts : List (Nat × Nat)) :
    colSum xv yv (t :: ts) = xv t.1 * yv t.2 + colSum xv yv ts := by
  simp [colSum]

/-- A column's terms, by induction on them. -/
theorem terms_ok {base : Addr} {a0 a1 a2 : Reg}
    (hd : [a0, a1, a2, .x12, .x13, .x14, .x15, .x26, .x2].Nodup) :
    ∀ (ts : List (Nat × Nat)) (s : State), Wk s base → (∀ t ∈ ts, t.1 < 16 ∧ t.2 < 9) →
      rv s [a0, a1, a2] + colSum (xw s.mem base) (yw s.mem base) ts < 2 ^ 192 →
      WP isa (.block (ts.flatMap fun t => term a0 a1 a2 t.1 t.2)) s fun s' =>
        rv s' [a0, a1, a2] = rv s [a0, a1, a2] + colSum (xw s.mem base) (yw s.mem base) ts ∧
        Keeps [.x12, .x13, .x14, .x15, a0, a1, a2] s s'
  | [], s, _, _, _ => WP.block_nil ⟨by simp [colSum], Keeps.refl _ _⟩
  | t :: ts, s, hs, hc, hb => by
    rw [List.flatMap_cons, WP.block_append_iff]
    rw [colSum_cons] at hb
    have hct := hc t List.mem_cons_self
    refine WP.mono (term_ok hs hd hct.1 hct.2 (by omega_arith)) fun s1 ⟨e1, k1⟩ => ?_
    have hn := hd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨⟨-, -, -, -, -, -, h0z, h0x⟩, ⟨-, -, -, -, -, h1z, h1x⟩, ⟨-, -, -, -, h2z, h2x⟩, -⟩ := hn
    have hs1 : Wk s1 base := hs.of_keeps k1
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨by decide, by decide, by decide, by decide, Ne.symm h0x, Ne.symm h1x, Ne.symm h2x⟩)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨by decide, by decide, by decide, by decide, Ne.symm h0z, Ne.symm h1z, Ne.symm h2z⟩)
    have m1 : s1.mem = s.mem := k1.mem
    refine WP.mono (terms_ok hd ts s1 hs1 (fun t' ht' => hc t' (List.mem_cons_of_mem _ ht'))
      (by rw [e1, m1]; omega_arith)) fun s2 ⟨e2, k2⟩ => ⟨?_, k1.trans k2⟩
    rw [e2, e1, colSum_cons, m1]
    omega_arith

/-- The registers a product's columns change. -/
def colX : List Reg := [.x5, .x6, .x7, .x12, .x13, .x14, .x15]

/-- The accumulator of column `k`. -/
def acc (k : Nat) : List Reg := [accR k 0, accR k 1, accR k 2]

theorem accR_mod (k n : Nat) : accR k n = [Reg.x5, .x6, .x7].getD ((k + n) % 3) .x5 := rfl

theorem acc_succ (k : Nat) : acc (k + 1) = [accR k 1, accR k 2, accR k 0] := by
  simp only [acc, accR_mod]
  refine List.cons_eq_cons.mpr ⟨by rw [Nat.add_right_comm], List.cons_eq_cons.mpr
    ⟨by rw [Nat.add_assoc], List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
  rw [show k + 1 + 2 = k + 3 by omega_arith, Nat.add_mod_right, Nat.add_zero]

theorem acc_cases (k : Nat) :
    acc k = [.x5, .x6, .x7] ∨ acc k = [.x6, .x7, .x5] ∨ acc k = [.x7, .x5, .x6] := by
  simp only [acc, accR_mod]
  rcases (by omega_arith : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h <;>
  simp only [Nat.add_mod k, h] <;> simp

theorem acc_nodup (k : Nat) :
    [accR k 0, accR k 1, accR k 2, .x12, .x13, .x14, .x15, .x26, .x2].Nodup := by
  have := acc_cases k
  simp only [acc, List.cons.injEq, and_true] at this
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> decide

theorem acc_colX (k : Nat) : ∀ r ∈ [Reg.x12, .x13, .x14, .x15, accR k 0, accR k 1, accR k 2],
    r ∈ colX := by
  have := acc_cases k
  simp only [acc, List.cons.injEq, and_true] at this
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> decide

theorem accR_colX (k n : Nat) (hn : n < 3) : accR k n ∈ colX := by
  have := acc_colX k
  rcases (by omega_arith : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> exact this _ (by simp)

/-- A column: its terms, its low word stored at `ACC + 8k`, and the rest of
the accumulator passed on. -/
theorem column_ok {s : State} {base : Addr} (hs : Wk s base) (k : Nat) (hk : k < 16)
    (hc : ∀ t ∈ mulCol k, t.1 < 16 ∧ t.2 < 9)
    (hb : rv s (acc k) + colSum (xw s.mem base) (yw s.mem base) (mulCol k) < 2 ^ 192) :
    WP isa (.block (column k)) s fun s' =>
      (word s'.mem base (ACC + 8 * k)).toNat + 2 ^ 64 * rv s' (acc (k + 1)) =
        rv s (acc k) + colSum (xw s.mem base) (yw s.mem base) (mulCol k) ∧
      (∀ r, r ∉ colX → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Outside base (ACC + 8 * k) 8 s.mem s'.mem := by
  have hsub := acc_colX k
  rw [column, WP.block_append_iff]
  refine WP.mono (terms_ok (acc_nodup k) (mulCol k) s hs hc hb) fun s1 ⟨e1, k1⟩ => ?_
  have hs1 : Wk s1 base := hs.of_keeps k1 (fun h => by have := hsub _ h; simp [colX] at this)
    (fun h => by have := hsub _ h; simp [colX] at this)
  have hw : InRegions s1.wr (s1.gpr .x2 + BitVec.ofNat 64 (ACC + 8 * k)) 8 := by
    rw [hs1.x2]; exact ⟨_, hs1.wr, contains_sc (by simp only [ACC]; omega_arith)⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_str_x ⟨by simp only [ACC]; omega_arith, by simp only [ACC]; omega_arith⟩ hw, ?_⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits from by decide,
    ite_true, Option.some.injEq, exists_eq_left']
  have hn := acc_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨⟨h01, h02, -⟩, ⟨h12, -⟩, -⟩ := hn
  refine ⟨?_, fun r hr => ?_, k1.rd, k1.wr, k1.sp, ?_⟩
  · rw [acc_succ]
    simp only [rv, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ _ (Ne.symm h01),
      RegUpd.gpr_write_of_ne _ _ _ (Ne.symm h02), RegUpd.mem_write, hs1.x2, word_writeW_self]
    simp only [acc, rv] at e1 ⊢
    rw [show (BitVec.setWidth 64 (BitVec.setWidth Size.x.bits (0 : BitVec 16) <<< (16 * 0))).toNat = 0
      from rfl]
    omega_arith
  · have hr0 : r ≠ accR k 0 := fun e => hr (e ▸ accR_colX k 0 (by decide))
    rw [RegUpd.gpr_write_of_ne _ _ _ hr0]
    exact k1.gpr r (fun h => hr (hsub _ h))
  · simp only [RegUpd.mem_write, hs1.x2]
    rw [← k1.mem]; exact writeW_outside _ _ _ (by simp only [ACC]; omega_arith)

theorem mv_succ_last (m : Mem) (base : Addr) :
    ∀ (o n : Nat), mv m base o (n + 1) = mv m base o n + 2 ^ (64 * n) * (word m base (o + 8 * n)).toNat
  | o, 0 => by simp [mv]
  | o, n + 1 => by
    rw [mv, mv_succ_last m base (o + 8) n, mv, pow64_succ,
      show o + 8 + 8 * n = o + 8 * (n + 1) by omega_arith]
    generalize 2 ^ (64 * n) = Q
    grind

/-- The columns' values: `Σ_{m<n} 2^(64m) colSum (mulCol (k + m))`, in Horner
form, whose only power is `2⁶⁴`. -/
def colsVal (xv yv : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => colSum xv yv (mulCol k) + 2 ^ 64 * colsVal xv yv (k + 1) n

theorem colsVal_succ_last (xv yv : Nat → Nat) :
    ∀ k n, colsVal xv yv k (n + 1) = colsVal xv yv k n + 2 ^ (64 * n) * colSum xv yv (mulCol (k + n))
  | k, 0 => by simp [colsVal]
  | k, n + 1 => by
    rw [colsVal, colsVal_succ_last xv yv (k + 1) n, colsVal, pow64_succ,
      show k + 1 + n = k + (n + 1) by omega_arith]
    generalize 2 ^ (64 * n) = Q
    grind

theorem colSum_le (xv yv : Nat → Nat) :
    ∀ ts : List (Nat × Nat), (∀ t ∈ ts, xv t.1 < 2 ^ 64 ∧ yv t.2 < 2 ^ 64) →
      colSum xv yv ts ≤ ts.length * ((2 ^ 64 - 1) * (2 ^ 64 - 1))
  | [], _ => by simp [colSum]
  | t :: ts, h => by
    rw [colSum_cons, List.length_cons, Nat.succ_mul]
    have h1 := h t List.mem_cons_self
    have hp : xv t.1 * yv t.2 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
    have := colSum_le xv yv ts fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    omega_arith

theorem colSum_congr (xv yv xv' yv' : Nat → Nat) (ts : List (Nat × Nat))
    (h : ∀ t ∈ ts, xv t.1 = xv' t.1 ∧ yv t.2 = yv' t.2) :
    colSum xv yv ts = colSum xv' yv' ts := by
  simp only [colSum]
  exact congrArg List.sum (List.map_congr_left fun t ht => by rw [(h t ht).1, (h t ht).2])

theorem mulCol_hc : ∀ k < 16, ∀ t ∈ mulCol k, t.1 < 16 ∧ t.2 < 9 := by decide
theorem mulCol_len : ∀ k < 16, (mulCol k).length ≤ 9 := by decide

theorem colX_x2 : Reg.x2 ∉ colX := by decide
theorem colX_x26 : Reg.x26 ∉ colX := by decide

/-- The first `n` columns of the product. -/
theorem columns_ok {s₀ : State} {base : Addr} (hs : Wk s₀ base) (h0 : rv s₀ (acc 0) = 0) :
    ∀ n ≤ 16, WP isa (.block ((List.range n).flatMap column)) s₀ fun s =>
      (∀ r, r ∉ colX → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      Outside base ACC (8 * n) s₀.mem s.mem ∧
      mv s.mem base ACC n + 2 ^ (64 * n) * rv s (acc n) =
        colsVal (xw s₀.mem base) (yw s₀.mem base) 0 n ∧
      rv s (acc n) < 2 ^ 128
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _,
      by simp [mv, colsVal, h0], by rw [h0]; decide⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (columns_ok hs h0 n (by omega_arith)) fun s ⟨g, rd, wr, sp, o, e, b⟩ => ?_
    have hsS : Wk s base := ⟨(g _ colX_x2).trans hs.x2, wr ▸ hs.wr, (g _ colX_x26).trans hs.z⟩
    have hcn := mulCol_hc n (by omega_arith)
    have same : ∀ t ∈ mulCol n, xw s.mem base t.1 = xw s₀.mem base t.1 ∧
        yw s.mem base t.2 = yw s₀.mem base t.2 := fun t ht => by
      have := hcn t ht
      exact ⟨by rw [xw, o.word (by simp only [XK, ACC]; omega_arith) (by simp only [XK]; omega_arith)],
        by rw [yw, o.word (by simp only [YS, ACC]; omega_arith) (by simp only [YS]; omega_arith)]⟩
    have cs := colSum_congr _ _ _ _ (mulCol n) same
    have cb := colSum_le (xw s.mem base) (yw s.mem base) (mulCol n)
      fun t _ => ⟨(word s.mem base _).isLt, (word s.mem base _).isLt⟩
    have hwn := Nat.mul_le_mul_right ((2 ^ 64 - 1) * (2 ^ 64 - 1)) (mulCol_len n (by omega_arith))
    rw [List.flatMap_singleton]
    refine WP.mono (column_ok hsS n (by omega_arith) hcn (by omega_arith))
      fun s' ⟨e', g', rd', wr', sp', o'⟩ => ?_
    refine ⟨fun r hr => (g' r hr).trans (g r hr), rd'.trans rd, wr'.trans wr, sp'.trans sp,
      (o.mono (Nat.le_refl _) (by omega_arith)).trans (o'.mono (by omega_arith) (by omega_arith)), ?_, ?_⟩
    · rw [mv_succ_last, Outside.mv_eq o' n ACC (by omega_arith) (by simp only [ACC]; omega_arith),
        colsVal_succ_last, Nat.zero_add, pow64_succ, ← cs]
      generalize 2 ^ (64 * n) = Q at e ⊢
      calc mv s.mem base ACC n + Q * (word s'.mem base (ACC + 8 * n)).toNat +
            2 ^ 64 * Q * rv s' (acc (n + 1))
          = mv s.mem base ACC n + Q * ((word s'.mem base (ACC + 8 * n)).toNat +
              2 ^ 64 * rv s' (acc (n + 1))) := by grind
        _ = mv s.mem base ACC n + Q * rv s (acc n) + Q * colSum (xw s.mem base)
              (yw s.mem base) (mulCol n) := by rw [e']; grind
        _ = _ := by rw [e]
    · omega_arith

/-- Eight words' value, in Horner form. -/
def val8 (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * (f 3 + 2 ^ 64 * (f 4 + 2 ^ 64 * (f 5 +
    2 ^ 64 * (f 6 + 2 ^ 64 * f 7))))))

theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

/-- `val8` unfolded (stated, as `simp` would otherwise generate it at length). -/
theorem val8_eq (f : Nat → Nat) : val8 f =
    f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * (f 3 + 2 ^ 64 * (f 4 + 2 ^ 64 * (f 5 +
      2 ^ 64 * (f 6 + 2 ^ 64 * f 7)))))) := rfl

/-- The columns of `r + k s`: with `k` the left operands `0–7`, `r` the
left operands `8–15`, `s` the right operands `0–7` and one the right
operand 8. -/
theorem mulCols_sum (xv yv : Nat → Nat) (h1 : yv 8 = 1) :
    colsVal xv yv 0 16 = val8 xv * val8 yv + val8 (fun i => xv (8 + i)) := by
  simp only [colsVal, colSum, mulCol, range8, List.filter_cons, List.filter_nil, Nat.reduceSub,
    Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceAdd, and_self, and_true, and_false,
    decide_true, decide_false, ite_true, ite_false, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.sum_cons, List.sum_nil, val8_eq, h1, Nat.mul_one,
    Nat.add_zero, Nat.zero_le, Nat.le_refl, Bool.false_eq_true]
  generalize 2 ^ 64 = B
  grind

theorem mv8_val (m : Mem) (base : Addr) (o : Nat) :
    mv m base o 8 = val8 fun i => (word m base (o + 8 * i)).toNat := by
  simp only [mv8, val8_eq, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]

theorem pow_mono {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by omega_arith) h

theorem sq_add_le (n : Nat) : 2 ^ n * 2 ^ n + 2 ^ n ≤ 2 ^ (2 * n + 1) := by
  have : 2 ^ n ≤ 2 ^ (n + n) := Nat.pow_le_pow_right (by omega_arith) (by omega_arith)
  rw [Nat.pow_succ, Nat.mul_two, Nat.two_mul, Nat.pow_add]
  rw [Nat.pow_add] at this
  omega_arith

/-- `columns`: `r + k s` into the sixteen words at `ACC`, from `k`, `r`, `s`
(each below `2^456`) and one at `XK`, `XK + 64`, `YS` and `YS + 64`. -/
theorem product_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hone : word s.mem base (YS + 64) = 1)
    (hk : mv s.mem base XK 8 < 2 ^ 456) (hr : mv s.mem base (XK + 64) 8 < 2 ^ 456)
    (hs : mv s.mem base YS 8 < 2 ^ 456) :
    WP isa (.block columns) s fun t =>
      mv t.mem base ACC 16 = mv s.mem base (XK + 64) 8 + mv s.mem base XK 8 * mv s.mem base YS 8 ∧
      (∀ r, r ∉ .x26 :: colX → t.gpr r = s.gpr r) ∧ t.gpr .x26 = 0 ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ Outside base ACC 128 s.mem t.mem := by
  rw [columns, WP.block_append_iff]
  apply WP.mono (Q := fun (a : State) => Wk a base ∧ rv a (acc 0) = 0 ∧ a.mem = s.mem ∧
    (∀ r, r ∉ [Reg.x26, .x5, .x6, .x7] → a.gpr r = s.gpr r) ∧ a.rd = s.rd ∧ a.wr = s.wr ∧ a.sp = s.sp)
  · apply WP.of_runBlock
    simp only [Z, runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.x.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, hw, rfl⟩, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; exact hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  intro a ⟨ha, h0, ma, ga, rda, wra, spa⟩
  refine WP.mono (columns_ok ha h0 16 (Nat.le_refl _)) fun t ⟨gt, rdt, wrt, spt, ot, et, bt⟩ => ?_
  have hsum := mulCols_sum (xw a.mem base) (yw a.mem base) (by rw [yw, ma, Nat.mul_comm, hone]; rfl)
  have ex : val8 (xw a.mem base) = mv s.mem base XK 8 := by rw [mv8_val, ma]
  have ey : val8 (yw a.mem base) = mv s.mem base YS 8 := by rw [mv8_val, ma]
  have er : val8 (fun i => xw a.mem base (8 + i)) = mv s.mem base (XK + 64) 8 := by
    rw [mv8_val, ma]
    exact congrArg val8 (funext fun i => by rw [xw, show XK + 8 * (8 + i) = XK + 64 + 8 * i by omega_arith])
  rw [hsum, ex, ey, er] at et
  refine ⟨?_, fun r hr => ?_, (gt _ colX_x26).trans ha.z, rdt.trans rda, wrt.trans wra,
    spt.trans spa, by rw [← ma]; exact ot⟩
  · generalize hP : (2 : Nat) ^ (64 * 16) = P at et
    have hb : (2 : Nat) ^ 456 * 2 ^ 456 + 2 ^ 456 ≤ P :=
      Nat.le_trans (Nat.le_trans (sq_add_le 456) (pow_mono (a := 2 * 456 + 1) (b := 64 * 16) (by decide))) (Nat.le_of_eq hP)
    generalize (2 : Nat) ^ 456 = Q at hk hs hr hb
    have hp := Nat.mul_lt_mul'' hk hs
    have hA : rv t (acc 16) = 0 := by
      rcases Nat.eq_zero_or_pos (rv t (acc 16)) with h | h
      · exact h
      · have := Nat.mul_le_mul_left P h
        generalize P * rv t (acc 16) = A at et this
        generalize mv s.mem base XK 8 * mv s.mem base YS 8 = M at hp et
        omega_arith
    rw [hA, Nat.mul_zero, Nat.add_zero] at et
    rw [et, Nat.add_comm]
  · simp only [List.mem_cons, not_or] at hr
    have h5 : r ≠ .x5 := by rintro rfl; exact hr.2 (by decide)
    have h6 : r ≠ .x6 := by rintro rfl; exact hr.2 (by decide)
    have h7 : r ≠ .x7 := by rintro rfl; exact hr.2 (by decide)
    have hr' : r ∉ [Reg.x26, .x5, .x6, .x7] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr.1, h5, h6, h7⟩
    rw [gt r hr.2, ga r hr']

/-- `8n` bytes at `base + o` are `n` words. -/
theorem decode_mv (m : Mem) (base : Addr) :
    ∀ (n o : Nat), Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (off base o) (8 * n)) = mv m base o n
  | 0, _ => rfl
  | n + 1, o => by
    have e := words_step m (off base o) (8 * (n + 1)) 0 (by omega_arith)
    simp only [Nat.mul_zero, Nat.sub_zero, Nat.zero_add, Nat.mul_one, BitVec.add_zero] at e
    rw [e, show 8 * (n + 1) - 8 = 8 * n by omega_arith, show off base o + BitVec.ofNat 64 8 = off base (o + 8)
      from Offset.add_add base o 8, decode_mv m base n (o + 8), mv]

end VG.Proof.Ed448.AArch64

end

end


/-!
# Ed448 scalar multiply-add on AArch64: the whole function

`vg_ed448_scalar_mul_add` copies `k`, `r` and `s` to the working space,
forms `r + k s` in sixteen words by product scanning, and reduces them with
the loop of `vg_ed448_scalar_reduce`, from a zero remainder. The working
space is written only where the callee-saved registers are saved, the
operands and the product, so the inputs are read unchanged and the saved
registers are restored.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps word off Outside ofs contains_sc)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `vg_ed448_scalar_mul_add(out = x0, r = x1, k = x2, s = x3, scratch = x4)`. -/
def scalarMulAddLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 57⟩, ⟨s.gpr .x2, 57⟩, ⟨s.gpr .x3, 57⟩] ∧
    s.wr = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x4, 8192⟩] ∧
    (⟨s.gpr .x1, 57⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (⟨s.gpr .x2, 57⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (⟨s.gpr .x3, 57⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩
  post s t := bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarMulAdd (bytesAt s.mem (s.gpr .x1) 57)
    (bytesAt s.mem (s.gpr .x2) 57) (bytesAt s.mem (s.gpr .x3) 57)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4

/-- The loop over the words at `ACC`, with a zero remainder. -/
theorem accInit_ok (s : State) :
    WP isa (.block accInit) s fun t =>
      t.gpr .x1 = s.gpr .x2 + BitVec.ofNat 64 ACC ∧ rem t = 0 ∧ t.gpr .x3 = BitVec.ofNat 64 128 ∧
      Keeps [.x1, .x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [accInit, zeroHigh, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, show ACC < 4096 from by decide,
    show 16 * 0 < Size.x.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
      Ed25519.AArch64.read_x]
  · simp only [rem, rv, R, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem pow256_57 : (256 : Nat) ^ 57 = 2 ^ 456 :=
  calc (256 : Nat) ^ 57 = (2 ^ 8) ^ 57 := rfl
    _ = 2 ^ (8 * 57) := (Nat.pow_mul 2 8 57).symm
    _ = 2 ^ 456 := by rw [show 8 * 57 = 456 from rfl]

/-- The registers `vg_ed448_scalar_mul_add` changes before it restores the
callee-saved ones. -/
def mulAddClob : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26]

theorem clob_sub : ∀ r ∈ clob, r ∈ mulAddClob := by decide
theorem accInit_sub : ∀ r ∈ [Reg.x1, .x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11], r ∈ mulAddClob := by
  decide
theorem consts_sub : ∀ r ∈ constRegs, r ∈ mulAddClob := by decide
theorem colX_sub : ∀ r ∈ Reg.x26 :: colX, r ∈ mulAddClob := by decide
theorem operands_sub : ∀ r ∈ [Reg.x2, .x5], r ∈ mulAddClob := by decide

theorem decodeLE_lt456 (m : Mem) (p : Addr) : decodeLE (bytesAt m p 57) < 2 ^ 456 := by
  have h := decodeLE_lt' (bytesAt m p 57)
  rw [bytesAt_length, pow256_57] at h
  exact h

theorem scalarMulAdd_correct {s : State} (hs : scalarMulAddLocal.pre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  obtain ⟨hr, hw, dr, dk, ds⟩ := hs
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .x4 = b := ⟨_, rfl⟩
  rw [hbase] at hw dr dk ds
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have hwo : (⟨s.gpr .x0, 57⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have hin : ∀ r ∈ [Reg.x1, .x2, .x3], (⟨s.gpr r, 57⟩ : Region) ∈ s.rd ++ s.wr := by
    intro r hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl <;> rw [hr] <;> simp
  rw [scalarMulAdd]
  apply WP.seq
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (saveRegs_ok .x4 hbase hws) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  have in₁ : ∀ r ∈ [Reg.x1, .x2, .x3], (⟨s₁.gpr r, 57⟩ : Region) ∈ s₁.rd ++ s₁.wr := by
    rw [g₁, rd₁, wr₁]; exact hin
  refine WP.mono (operands_ok (s := s₁) (base := base) (by rw [g₁]; exact hbase) (wr₁ ▸ hws)
    (in₁ _ (by decide)) (in₁ _ (by decide)) (in₁ _ (by decide)) (by rw [g₁]; exact dr)
    (by rw [g₁]; exact dk) (by rw [g₁]; exact ds))
    fun s₂ ⟨vk₂, vr₂, vs₂, one₂, o₂, x2₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
  have ek : decodeLE (bytesAt s₁.mem (s₁.gpr .x2) 57) = decodeLE (bytesAt s.mem (s.gpr .x2) 57) := by
    rw [g₁, bytesAt_outside o₁ (by decide) dk (by decide)]
  have er : decodeLE (bytesAt s₁.mem (s₁.gpr .x1) 57) = decodeLE (bytesAt s.mem (s.gpr .x1) 57) := by
    rw [g₁, bytesAt_outside o₁ (by decide) dr (by decide)]
  have es : decodeLE (bytesAt s₁.mem (s₁.gpr .x3) 57) = decodeLE (bytesAt s.mem (s.gpr .x3) 57) := by
    rw [g₁, bytesAt_outside o₁ (by decide) ds (by decide)]
  rw [ek] at vk₂; rw [er] at vr₂; rw [es] at vs₂
  rw [WP.block_append_iff]
  refine WP.mono (product_ok x2₂ (wr₂ ▸ wr₁ ▸ hws) one₂ (vk₂ ▸ decodeLE_lt456 _ _)
    (vr₂ ▸ decodeLE_lt456 _ _) (vs₂ ▸ decodeLE_lt456 _ _))
    fun s₃ ⟨v₃, g₃, z₃, rd₃, wr₃, sp₃, o₃⟩ => ?_
  rw [vk₂, vr₂, vs₂] at v₃
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₃) fun s₄ ⟨c₄, k₄⟩ => ?_
  refine WP.mono (accInit_ok s₄) fun s₅ ⟨x1₅, r₅, x3₅, k₅⟩ => ?_
  have c₅ : Consts s₅ := c₄.of_keeps k₅ (by decide)
  have x2₄ : s₄.gpr .x2 = base := (k₄.gpr _ (by decide)).trans ((g₃ _ (by decide)).trans x2₂)
  have m₅ : s₅.mem = s₃.mem := k₅.mem.trans k₄.mem
  have rdw₅ : s₅.rd ++ s₅.wr = s.rd ++ s.wr := by
    rw [k₅.rd, k₅.wr, k₄.rd, k₄.wr, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]
  apply WP.seq
  have hi : LoopInv 128 s₅ 16 s₅ := by
    refine ⟨by decide, by decide, x3₅, ?_, Keeps.refl _ _⟩
    rw [r₅]; rfl
  refine WP.mono (scalarLoop_ok s₅ c₅ (by decide) hi fun k hk => by
      rw [rdw₅, x1₅, x2₄, Offset.add_add]
      exact ⟨_, List.mem_append_right _ hws, contains_sc (by simp only [ACC]; omega_using [hk])⟩)
    fun s₆ ⟨v₆, k₆⟩ => ?_
  have x2₆ : s₆.gpr .x2 = base := by rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), x2₄]
  have g₆ : ∀ r, r ∉ mulAddClob → s₆.gpr r = s.gpr r := fun r hr' => by
    rw [k₆.gpr r fun h => hr' (clob_sub r h), k₅.gpr r fun h => hr' (accInit_sub r h),
      k₄.gpr r fun h => hr' (consts_sub r h), g₃ r fun h => hr' (colX_sub r h),
      g₂ r fun h => hr' (operands_sub r h), g₁]
  have x0₆ : s₆.gpr .x0 = s.gpr .x0 := g₆ _ (by decide)
  have wr₆ : s₆.wr = s.wr := by rw [k₆.wr, k₅.wr, k₄.wr, wr₃, wr₂, wr₁]
  have sv₆ : Saved base s.gpr s₆.mem := by
    intro p hp
    have hl := (saved_ok p hp).2
    rw [k₆.mem, m₅, Ed25519.AArch64.Outside.word o₃ (by simp only [ACC]; omega_using [hl]) (by omega_using [hl]),
      Ed25519.AArch64.Outside.word o₂ (by simp only [XK]; omega_using [hl]) (by omega_using [hl])]
    exact sv₁ p hp
  refine WP.mono (finish_ok x2₆ (wr₆ ▸ hws) sv₆ x0₆ (wr₆ ▸ hwo)) fun t ⟨bt, rt, gt, spt⟩ => ?_
  refine ⟨⟨fun r hpres => ?_, spt.trans (k₆.sp.trans (k₅.sp.trans (k₄.sp.trans
    (sp₃.trans (sp₂.trans sp₁)))))⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hpres
    rcases hpres with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.x19, 0) (by decide)
    · exact rt (.x20, 8) (by decide)
    · exact rt (.x21, 16) (by decide)
    · exact rt (.x22, 24) (by decide)
    · exact rt (.x23, 32) (by decide)
    · exact rt (.x24, 40) (by decide)
    · exact rt (.x25, 48) (by decide)
    · exact rt (.x26, 56) (by decide)
    all_goals rw [gt _ (by decide), g₆ _ (by decide)]
  · show bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarMulAdd (bytesAt s.mem (s.gpr .x1) 57)
      (bytesAt s.mem (s.gpr .x2) 57) (bytesAt s.mem (s.gpr .x3) 57)
    rw [bt, v₆, x1₅, x2₄, m₅, show (128 : Nat) = 8 * 16 from rfl, decode_mv, v₃]
    rfl

end VG.Proof.Ed448.AArch64

end

end

/-!
# Ed448 scalar arithmetic on AArch64: `Verified`

Correctness includes the ABI. Taint analysis checks that secret input bytes
never determine branches or memory addresses: only the arguments, which
are public, do. A concrete witness proves the signature contract is
satisfiable.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64

theorem scalarReduce_ok (s : State) (hs : scalarReduceLocal.pre s) :
    ∃ t s', Exec isa scalarReduce s t s' ∧ abiPreserved s s' ∧ scalarReduceLocal.post s s' :=
  scalarReduce_correct hs

theorem scalarReduce_ct :
    ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h0, h1, h2]

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' :=
  scalarMulAdd_correct hs

theorem scalarMulAdd_ct :
    ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2, h3, h4⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

end VG.Proof.Ed448.AArch64
