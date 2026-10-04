import VerifiedGarbage.Proof.Ed448.AArch64.ScalarIO

/-!
# Ed448 scalar multiply-add on AArch64: the operands

Each 57-byte input is copied to the working space as eight words, the top
one its last byte (`copy57_ok`), without reading past it; the values of
words in the working space are `mv`. The inputs are outside the working
space, so the copies leave them unchanged.
-/

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
    (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

/-- A word of a buffer disjoint from the working space, after writes inside it. -/
theorem readW_far {base p : Addr} {n o k d : Nat} {m m' : Mem} (h : Outside base o k m m')
    (hk : o + k ≤ 8192) (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hdn : d + 8 ≤ n)
    (hn : n ≤ 2 ^ 64) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  (Mem.readW_congr fun i hi => (h _ (Or.inr (by
    rw [Offset.add_add]; have := far hd (i := d + i) (by omega) hn; omega))).symm).symm

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
  refine ⟨_, exec_ldr_x ⟨by omega, by omega⟩ (by
    rw [h.hsrc]; exact ⟨_, h.rd, Offset.contains_base p (by omega) (by omega)⟩), ?_⟩
  rw [WP.block_cons_iff]
  have hw : InRegions (s.write .x .x5 (s.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * i)) 64)).wr
      ((s.write .x .x5 (s.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * i)) 64)).gpr .x4 +
        BitVec.ofNat 64 (o + 8 * i)) 8 := by
    rw [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ _ (by decide), h.x4]
    exact ⟨_, h.wr, contains_sc (by have := h.olt; omega)⟩
  refine ⟨_, exec_str_x ⟨by have := h.o8; omega, by have := h.olt; omega⟩ hw, WP.block_nil ?_⟩
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
    refine WP.mono (copyWords_ok h n (by omega)) fun a ⟨wa, oa, ka⟩ => ?_
    have olt := h.olt
    refine WP.mono (copyPair_ok (h.of_keeps ka) n (by omega)) fun t ⟨mt, kt⟩ => ?_
    have rp : a.mem.readW (p + BitVec.ofNat 64 (8 * n)) 64 =
        s.mem.readW (p + BitVec.ofNat 64 (8 * n)) 64 :=
      readW_far oa (by omega) h.disj (by omega) (by omega)
    refine ⟨fun j hj => ?_, ?_, ka.trans kt⟩
    · rw [mt, rp]
      rcases Nat.lt_or_ge j n with hj' | hj'
      · rw [Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega)]
        exact wa j hj'
      · obtain rfl : j = n := by omega
        exact word_writeW_self _ _ _ _
    · rw [mt]
      exact oa.mono (Nat.le_refl _) (by omega) |>.trans
        ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))

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
  omega

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
    rw [ha.hsrc]; exact ⟨_, ha.rd, Offset.contains_base p (d := 56) (n := 1) (by omega) (by omega)⟩
  have hw : InRegions a.wr (a.gpr .x4 + BitVec.ofNat 64 (o + 56)) 8 := by
    rw [ha.x4]; exact ⟨_, ha.wr, contains_sc (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, read_x,
    Size.bytes, show (56 : Nat) % 1 = 0 from rfl, show (56 : Nat) < 4096 * 1 from by decide, and_self,
    hb, show (o + 56) % 8 = 0 by omega, show o + 56 < 4096 * 8 by omega, hw,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  rw [ha.x4, ha.hsrc, Ed25519.AArch64.write64_eq_writeW]
  refine ⟨?_, oa.mono (Nat.le_refl _) (by omega) |>.trans
    ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)),
    ka.trans ⟨fun r hr => by simp only [RegUpd.gpr_write, hr, ite_false], rfl, rfl, rfl⟩⟩
  have byte : (a.mem.read (p + BitVec.ofNat 64 56) 1) = s.mem (p + BitVec.ofNat 64 56) := by
    rw [Ed25519.AArch64.read_byte]
    exact oa _ (Or.inr (by have := far h.disj (i := 56) (by omega) (by omega); omega))
  rw [mv8, decode57]
  have w0 := wa 0 (by omega); have w1 := wa 1 (by omega); have w2 := wa 2 (by omega)
  have w3 := wa 3 (by omega); have w4 := wa 4 (by omega); have w5 := wa 5 (by omega)
  have w6 := wa 6 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at w0 w1 w2 w3 w4 w5 w6
  simp only [Ed25519.AArch64.word_writeW_self]
  rw [Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    w0, w1, w2, w3, w4, w5, w6, byte, toNat_byte64]

theorem Outside.mv_eq {base : Addr} {o k : Nat} {m m' : Mem} (h : Outside base o k m m') :
    ∀ (n d : Nat), (d + 8 * n ≤ o ∨ o + k ≤ d) → d + 8 * n < 2 ^ 64 → mv m' base d n = mv m base d n
  | 0, _, _, _ => rfl
  | n + 1, d, hd, hl => by
    show (word m' base d).toNat + 2 ^ 64 * mv m' base (d + 8) n =
      (word m base d).toNat + 2 ^ 64 * mv m base (d + 8) n
    rw [Outside.mv_eq h n (d + 8) (by omega) (by omega), h.word (by omega) (by omega)]

/-- The bytes of a buffer disjoint from the working space, after writes
inside it only. -/
theorem bytesAt_outside {m m' : Mem} {p base : Addr} {n o k : Nat} (h : Outside base o k m m')
    (hk : o + k ≤ 8192) (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n := by
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  exact h _ (Or.inr (by have := far hd hi hn; omega))

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
