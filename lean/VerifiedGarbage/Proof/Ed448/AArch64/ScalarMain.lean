module

import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLoop
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ed448.ScalarWords
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Impl.Ed448.AArch64.Scalar
import VerifiedGarbage.Proof.Framework.AddrArith

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
