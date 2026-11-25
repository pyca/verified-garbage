module

public import VerifiedGarbage.Impl.Ed25519.AArch64.FixedBase
public import VerifiedGarbage.Proof.Ed25519.AArch64.Pairs
public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
public import VerifiedGarbage.Proof.Ed25519.CombDigits64
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
import VerifiedGarbage.Proof.Ed25519.AArch64.Bits
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
import VerifiedGarbage.Proof.Ed25519.AArch64.Points
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.X25519.AArch64.Ops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range

/-!
# Ed25519's base-point multiplication on AArch64: the comb

The static's words as a contract states them (`CombHeld`) and as the code reads them (`TblAt`);
the scalar's nibbles (`scalarNibbles_ok`); the entry of a digit (`entry_ok`), which the target-independent
`combEntry64_ok` represents; the addition (`addEntry_ok`); and the loop, which leaves `[s]B` in
slots 0–3 (`combMultiply_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Pairs
open VG.Proof.Ed25519.AArch64.Pairs VG.Proof.Ed25519 VG.Proof.Ed25519.Word64 VG.Proof.X25519

/-! ## The tables -/

theorem combWords_length : combWords.length = 6144 := by simp [combWords]

theorem combWords_getD {q : Nat} (hq : q < 6144) : combWords.getD q 0 = combWord q := by
  simp [combWords, List.getD_eq_getElem?_getD, hq]

theorem combConsts_eq : combConsts = [(combSym, combWords)] := rfl

/-- The region of the tables at `T`. -/
abbrev TBL (T : Addr) : Region := ⟨T, 8 * combWords.length⟩

/-- The region of the tables. -/
abbrev tblRegion (s : State) : Region := TBL (s.syms combSym)

/-- The tables' words at `T`. -/
def TblWords (T : Addr) (m : Mem) : Prop :=
  ∀ i < combWords.length, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0

/-- The static, in `s`, as a contract states it: its words, not wrapping around, apart from the
regions `wr`. -/
def CombHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < combWords.length, s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0) ∧
  (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ r

/-- The static at `T`: readable, beyond the working space at `base`, word `i` its `combWord i`. -/
structure TblAt (s : State) (base T : Addr) : Prop where
  rd : ∀ i < 6144, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (8 * i)) 8
  far : ∀ i < 49152, 8192 ≤ ofs base (T + BitVec.ofNat 64 i)
  val : ∀ i < 6144, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = combWord i

/-- The static survives what keeps the regions and the memory beyond the working space. -/
theorem TblAt.of_far {s t : State} {base T : Addr} (h : TblAt s base T)
    (hrw : t.rd ++ t.wr = s.rd ++ s.wr) (hm : ∀ x, 8192 ≤ ofs base x → t.mem x = s.mem x) :
    TblAt t base T :=
  ⟨fun i hi => hrw ▸ h.rd i hi, h.far, fun i hi => by
    rw [← h.val i hi]
    refine Mem.readW_congr fun b hb => hm _ ?_
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact h.far _ (by omega_using [hi, hb])⟩

/-- The static, from a contract's facts: readable, and apart from the working space at `base`,
one of the regions `wr`. -/
theorem CombHeld.tblAt {s : State} {wr : List Region} {base : Addr} (h : CombHeld s wr)
    (hrd : tblRegion s ∈ s.rd) (hsc : (⟨base, 8192⟩ : Region) ∈ wr) : TblAt s base (s.syms combSym) := by
  obtain ⟨held, fit, dj⟩ := h
  have hl := combWords_length
  refine ⟨fun i hi => ⟨_, List.mem_append_left _ hrd, Offset.contains_base _ (by omega_using [hi, hl])
    (by omega_using [hi])⟩, fun i hi => ?_, fun i hi => by rw [held i (by omega_using [hi, hl]), combWords_getD hi]⟩
  refine Nat.le_of_not_lt fun hlt => dj _ hsc _
    (Offset.contains_base _ (d := i) (n := 1) (k := 8 * combWords.length) (by omega_using [hi, hl]) (by omega_using [hi])) ?_
  simp only [Region.Contains]; simp only [ofs] at hlt; omega_using [hlt]

/-- The memory of the contracts' witnesses: the static at `0x100000` (irreducible: unfolding it
in a definitional check would evaluate the table). -/
@[irreducible] def satMem : Mem := constMem 0x100000 combWords

theorem satMem_held : ∀ i < combWords.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  unfold satMem
  intro i hi
  exact constMem_held _ _ (by rw [combWords_length]; omega_using []) i hi

/-! ## The scalar's nibbles -/

/-- Nibble `i` of the bytes at `k`. -/
def nibAt (m : Mem) (k : Addr) (i : Nat) : Nat := (m (off k (i / 2))).toNat / 16 ^ (i % 2) % 16

theorem nibAt_eq (m : Mem) (k : Addr) {i : Nat} (hi : i < 64) :
    nibAt m k i = nib (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m k 32)) i := by
  rw [nib, decodeLE_nibble, nibbleOf, nibAt]
  obtain hg : (Spec.Ed25519.bytesAt m k 32).getD (i / 2) 0 = m (off k (i / 2)) := by
    simp [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, show i / 2 < 32 by omega_using [hi]]
  rw [hg]
  have := (m (off k (i / 2))).isLt
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, ite_eq_right (by decide), Nat.pow_zero, Nat.div_one]
  · rw [h, ite_eq_left rfl, Nat.pow_one]; omega_using []

/-- The first `n` nibbles of the scalar `S` in the working space. -/
def NibAt (m : Mem) (base : Addr) (n S : Nat) : Prop :=
  ∀ i < n, m (off base (NIB + i)) = BitVec.ofNat 8 (nib S i)

private theorem nib_lo (b : BitVec 8) :
    (((b.setWidth 64 &&& (15 : BitVec 64)).setWidth 32).setWidth 8 : BitVec 8) = BitVec.ofNat 8 (b.toNat / 16 ^ 0 % 16) := by
  revert b; decide +kernel

private theorem nib_hi (b : BitVec 8) :
    (((b.setWidth 64 >>> 4).setWidth 32).setWidth 8 : BitVec 8) = BitVec.ofNat 8 (b.toNat / 16 ^ 1 % 16) := by
  revert b; decide +kernel

theorem nibbleByte_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k) (h11 : s.gpr .x11 = 15)
    {j : Nat} (hj : j < 32) (hr : InRegions (s.rd ++ s.wr) (off k j) 1) :
    WP isa (.block (nibbleByte j)) s fun t =>
      t.mem = (s.mem.write (off base (NIB + 2 * j)) 1 (BitVec.ofNat 8 ((s.mem (off k j)).toNat / 16 ^ 0 % 16))).write
        (off base (NIB + (2 * j + 1))) 1 (BitVec.ofNat 8 ((s.mem (off k j)).toNat / 16 ^ 1 % 16)) ∧
      (∀ r, r ∉ [Reg.x8, .x9] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hN : NIB = 768 := rfl
  have hw : ∀ d, d < 8192 → InRegions s.wr (off base d) 1 := fun d hd =>
    ⟨_, hs.wr, Offset.contains_base _ hd (by omega_using [hd])⟩
  have w0 := hw (NIB + 2 * j) (by omega_using [hj, hN])
  have w1 := hw (NIB + (2 * j + 1)) (by omega_using [hj, hN])
  have l0 : NIB + 2 * j < 4096 * 1 := by omega_using [hj, hN]
  have l1 : NIB + (2 * j + 1) < 4096 * 1 := by omega_using [hj, hN]
  have lj : j < 4096 * 1 := by omega_using [hj]
  have hb : ∀ (m : Mem) (a : Addr), ((m.read a 1).setWidth 32).setWidth 64 = (m a).setWidth 64 :=
    VG.Proof.X25519.AArch64.read1_toNat
  apply WP.of_runBlock
  simp only [nibbleByte, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Nat.mod_one, l0, l1, lj, and_self,
    show (4 : Nat) < Size.x.bits from by decide, State.read, Size.bits,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hs.x0, hk, h11, hr, w0, w1, hb, nib_lo, nib_hi,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, trivial, trivial, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

private theorem write1 (m : Mem) (a x : Addr) (w : BitVec 8) : (m.write a 1 w) x = if x = a then w else m x := by
  by_cases h : x = a
  · subst h; simp [Mem.write]
  · simp only [Mem.write, sub_toNat_lt_one, h, ite_false]

/-- The nibbles, from the scalar at `k`, apart from the working space. -/
theorem scalarNibbles_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa (.block scalarNibbles) s fun t => PowersKeep base NIB 64 s t ∧
      NibAt t.mem base 64 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32)) := by
  have hN : NIB = 768 := rfl
  rw [scalarNibbles, WP.block_append_iff]
  obtain h15 : WP isa (.block [.movz .x .x11 15 0]) s fun t => t.gpr .x11 = 15 ∧ Keeps [.x11] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits from by decide,
      ite_true, Option.some.injEq, exists_eq_left', RegUpd.gpr_write_self]
    refine ⟨by decide, ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩⟩
    exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hq)
  refine WP.mono h15 fun a ⟨a11, ka⟩ => ?_
  obtain hsa := hs.of_keeps ka (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun n t => Scr t base ∧ t.gpr .x1 = k ∧ t.gpr .x11 = 15 ∧
      (∀ r, r ∉ [Reg.x8, .x9] → t.gpr r = a.gpr r) ∧ t.rd = a.rd ∧ t.wr = a.wr ∧ t.sp = a.sp ∧
      Outside base NIB 64 a.mem t.mem ∧ ∀ i < 2 * n, t.mem (off base (NIB + i)) = BitVec.ofNat 8 (nibAt a.mem k i))
    (fun j t hj ⟨ht, t1, t11, tg, trd, twr, tsp, tm, tn⟩ => ?_) 32 (Nat.le_refl _) a
    ⟨hsa, (ka.gpr _ (by decide)).trans hk, a11, fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _,
      fun i hi => absurd hi (by omega_using [])⟩) fun t ⟨_, _, _, tg, trd, twr, tsp, tm, tn⟩ => ⟨⟨fun r h19 h1 hc => ?_, ?_, ?_, ?_, ?_⟩, fun i hi => ?_⟩
  · refine WP.mono (nibbleByte_ok ht t1 t11 hj (by rw [trd, twr, ka.rd, ka.wr]; exact hr j hj))
      fun u ⟨um, ug, urd, uwr, usp⟩ => ?_
    obtain e : t.mem (off k j) = a.mem (off k j) := tm _ (Or.inr (by have := hd j hj; omega_using [this, hN]))
    rw [e] at um
    obtain w : ∀ (m : Mem) (d : Nat) (x : BitVec 8) (y : Addr), (m.write (off base d) 1 x) y =
        if y = off base d then x else m y := fun m d x y => write1 m _ y x
    refine ⟨⟨(ug _ (by decide)).trans ht.x0, uwr ▸ ht.wr, ht.nowrap⟩, (ug _ (by decide)).trans t1,
      (ug _ (by decide)).trans t11, fun r hr => (ug r hr).trans (tg r hr), urd.trans trd, uwr.trans twr,
      usp.trans tsp, fun x hx => ?_, fun i hi => ?_⟩
    · obtain n0 : x ≠ off base (NIB + 2 * j) := fun h => by
        rw [h, ofs_off' base (by omega_using [hj, hN])] at hx; omega_using [hx, hj]
      obtain n1 : x ≠ off base (NIB + (2 * j + 1)) := fun h => by
        rw [h, ofs_off' base (by omega_using [hj, hN])] at hx; omega_using [hx, hj]
      rw [um, w, w, ite_eq_right n1, ite_eq_right n0]
      exact tm x hx
    · rw [um, w, w]
      rcases (by omega_using [hi] : i < 2 * j ∨ i = 2 * j ∨ i = 2 * j + 1) with h | h | h
      · rw [ite_eq_right fun h' => by
            have := (off_eq_iff base (by omega_using [hj, hN, h]) (by omega_using [hj, hN])).mp h'; omega_using [this, h],
          ite_eq_right fun h' => by
            have := (off_eq_iff base (by omega_using [hj, hN, h]) (by omega_using [hj, hN])).mp h'; omega_using [this, h]]
        exact tn i h
      · subst h
        rw [ite_eq_right fun h' => by
            have := (off_eq_iff base (by omega_using [hj, hN]) (by omega_using [hj, hN])).mp h'; omega_using [this],
          ite_eq_left rfl, nibAt, show 2 * j / 2 = j by omega_using [], show 2 * j % 2 = 0 by omega_using []]
      · subst h
        rw [ite_eq_left rfl, nibAt, show (2 * j + 1) / 2 = j by omega_using [], show (2 * j + 1) % 2 = 1 by omega_using []]
  · rw [tg r (fun h => hc ((by decide : ∀ q ∈ [Reg.x8, .x9], q ∈ clob) r h)),
      ka.gpr r (fun h => hc ((by decide : ∀ q ∈ [Reg.x11], q ∈ clob) r h))]
  · rw [trd, ka.rd]
  · rw [twr, ka.wr]
  · rw [tsp, ka.sp]
  · rw [← ka.mem]; exact TableFrame.table tm
  · rw [tn i hi, nibAt_eq _ _ hi, ka.mem]

/-! ## The digit -/

private theorem digit_bits : ∀ n < 16,
    (0 : BitVec 64) - ((BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63) = mask (decide (n < 8)) ∧
      ((BitVec.ofNat 64 n - BitVec.ofNat 64 8) ^^^ mask (decide (n < 8))) - mask (decide (n < 8)) =
        BitVec.ofNat 64 (mag n) := by decide

private theorem byte_nat : ∀ n < 16, (BitVec.ofNat 8 n).setWidth 64 = BitVec.ofNat 64 n := by decide

theorem digit_ok {s : State} {base : Addr} (hs : Scr s base) {i n : Nat} (hi : i < 64) (hn : n < 16)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 i) (h10 : s.gpr .x10 = 0)
    (hm : s.mem (off base (NIB + i)) = BitVec.ofNat 8 n) :
    WP isa (.block digit) s fun t => t.gpr .x8 = BitVec.ofNat 64 (mag n) ∧ t.gpr .x9 = mask (decide (n < 8)) ∧
      Keeps [.x8, .x9] s t := by
  have hN : NIB = 768 := rfl
  have ha : base + BitVec.ofNat 64 i + BitVec.ofNat 64 NIB = off base (NIB + i) := by
    rw [Offset.add_add, Nat.add_comm]
  have hr : InRegions (s.rd ++ s.wr) (off base (NIB + i)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by show _ ≤ 8192; omega_using [hi, hN]) (by omega_using [hi, hN])⟩
  have hb : ∀ (m : Mem) (a : Addr), ((m.read a 1).setWidth 32).setWidth 64 = (m a).setWidth 64 :=
    VG.Proof.X25519.AArch64.read1_toNat
  apply WP.of_runBlock
  simp only [digit, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Nat.mod_one,
    show NIB < 4096 * 1 from by decide, show (8 : Nat) < 4096 from by decide, show (63 : Nat) < Size.x.bits from by decide,
    and_self, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hs.x0, h19, h10, ha, hr, hb, hm, byte_nat n hn,
    (digit_bits n hn).1, (digit_bits n hn).2, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-! ## The selection -/

/-- Word `q < 12` of entry `a` of table `i`: the identity's `[1, 1, 0]` for `a = 0`. -/
def selWord (i a q : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((combCoord (combCached64 i a) (q / 4)).val / 2 ^ (64 * (q % 4)) % 2 ^ 64)

theorem selWord_succ {i m q : Nat} (hm : m < 8) (hq : q < 12) :
    combWord (96 * i + 12 * m + q) = selWord i (m + 1) q := by
  unfold combWord selWord combPart
  rw [show (96 * i + 12 * m + q) / 96 = i by omega_using [hm, hq], show (96 * i + 12 * m + q) % 96 / 12 = m by omega_using [hm, hq],
    show (96 * i + 12 * m + q) % 12 = q by omega_using [hq], show (96 * i + 12 * m + q) % 4 = q % 4 by omega_using []]

private theorem selWord_zero_fact : ∀ q < 12,
    BitVec.ofNat 64 ((combCoord ⟨1, 1, 0, 2⟩ (q / 4)).val / 2 ^ (64 * (q % 4)) % 2 ^ 64) =
      (if q = 0 ∨ q = 4 then 1 else 0 : BitVec 64) := by decide

theorem selWord_zero (i q : Nat) (hq : q < 12) : selWord i 0 q = (if q = 0 ∨ q = 4 then 1 else 0 : BitVec 64) := by
  obtain e : combCached64 i 0 = ⟨1, 1, 0, 2⟩ := by
    unfold combCached64 combCached combCached16; split <;> rfl
  rw [selWord, e]
  exact selWord_zero_fact q hq

private theorem entryReg_ne : ∀ q < 12, ∀ q' < 12, q ≠ q' → entryReg q ≠ entryReg q' := by decide

private theorem entryReg_out : ∀ q < 12, entryReg q ∉ [Reg.x0, .x1, .x2, .x3, .x8, .x9, .x10, .x19] := by decide

private theorem entryReg_mem : ∀ q < 12, entryReg q ∈ [Reg.x4, .x5, .x6, .x7, .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x24] := by
  decide

/-- The registers the selection writes, but `x1`. -/
abbrev selRegs : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x24]

theorem selectPair_ok {s : State} {p : Addr} (hp : s.gpr .x1 = p) {j : Nat} (hj : j < 6) {w0 w1 : BitVec 64}
    (r0 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16 * j)) 8)
    (r1 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16 * j) + 8) 8)
    (e0 : s.mem.readW (p + BitVec.ofNat 64 (16 * j)) 64 = w0)
    (e1 : s.mem.readW (p + BitVec.ofNat 64 (16 * j) + 8) 64 = w1) :
    WP isa (.block (selectPair j)) s fun t =>
      t.gpr (entryReg (2 * j)) = (if s.zf = true then w0 else s.gpr (entryReg (2 * j))) ∧
      t.gpr (entryReg (2 * j + 1)) = (if s.zf = true then w1 else s.gpr (entryReg (2 * j + 1))) ∧
      t.zf = s.zf ∧ (∀ r, r ∉ [Reg.x2, .x3, entryReg (2 * j), entryReg (2 * j + 1)] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain a := entryReg_out (2 * j) (by omega_using [hj])
  obtain b := entryReg_out (2 * j + 1) (by omega_using [hj])
  obtain ab := entryReg_ne (2 * j) (by omega_using [hj]) (2 * j + 1) (by omega_using [hj]) (by omega_using [])
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at a b
  have l : 16 * j ≤ 504 := by omega_using [hj]
  have al : 16 * j % 8 = 0 := by omega_using []
  apply WP.of_runBlock
  simp only [selectPair, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, State.load, CondCode.holds,
    RegUpd.gpr_write, RegUpd.zf_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, l, al, hp, r0, r1, and_self,
    ne_eq, reduceCtorEq, not_false_eq_true, BitVec.setWidth_eq, ite_true, ite_false,
    a.2.2.1, a.2.2.2.1, Ne.symm a.2.2.2.1, b.2.2.1, b.2.2.2.1, ab, Ne.symm ab, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, trivial, fun r hr => ?_, trivial, trivial, trivial, rfl⟩
  · rw [← e0]; rfl
  · rw [← e1]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- What a candidate's words do to the registers, after `n` pairs: those so far are the candidate's
where the condition holds. -/
structure PairInv (s₀ : State) (W : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  done : ∀ q < 2 * n, s.gpr (entryReg q) = if s₀.zf = true then W q else s₀.gpr (entryReg q)
  rest : ∀ q < 12, 2 * n ≤ q → s.gpr (entryReg q) = s₀.gpr (entryReg q)
  zf : s.zf = s₀.zf
  gpr : ∀ r, r ∉ selRegs → s.gpr r = s₀.gpr r
  x8 : s.gpr .x8 = s₀.gpr .x8
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem selectPairs_ok {s : State} {p : Addr} (hp : s.gpr .x1 = p) {W : Nat → BitVec 64}
    (hr : ∀ q < 12, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * q)) 8)
    (hw : ∀ q < 12, s.mem.readW (p + BitVec.ofNat 64 (8 * q)) 64 = W q) :
    WP isa (.block ((List.range 6).flatMap selectPair)) s (PairInv s W 6) := by
  refine wp_range_flatMap (M := isa) (PairInv s W) (fun j t hj h => ?_) 6 (Nat.le_refl _) s
    ⟨fun q hq => absurd hq (by omega_using []), fun _ _ _ => rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  have a0 : p + BitVec.ofNat 64 (16 * j) = p + BitVec.ofNat 64 (8 * (2 * j)) := by
    rw [show 16 * j = 8 * (2 * j) by omega_using []]
  have a1 : p + BitVec.ofNat 64 (16 * j) + 8 = p + BitVec.ofNat 64 (8 * (2 * j + 1)) := by
    rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega_using []]
  refine WP.mono (selectPair_ok ((h.gpr _ (by decide)).trans hp) hj (w0 := W (2 * j)) (w1 := W (2 * j + 1))
    (by rw [a0, h.rd, h.wr]; exact hr _ (by omega_using [hj])) (by rw [a1, h.rd, h.wr]; exact hr _ (by omega_using [hj]))
    (by rw [a0, h.mem]; exact hw _ (by omega_using [hj])) (by rw [a1, h.mem]; exact hw _ (by omega_using [hj])))
    fun u ⟨u0, u1, uz, ug, um, urd, uwr, usp⟩ => ?_
  obtain m0 := entryReg_mem (2 * j) (by omega_using [hj])
  obtain m1 := entryReg_mem (2 * j + 1) (by omega_using [hj])
  obtain o8 : ∀ r, r ∉ selRegs → r ∉ [Reg.x2, .x3, entryReg (2 * j), entryReg (2 * j + 1)] := fun r hr hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h
    · subst h; exact hr (by decide)
    · subst h; exact hr (by decide)
    · exact hr ((by decide : ∀ q ∈ [Reg.x4, .x5, .x6, .x7, .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x24], q ∈ selRegs) r (h ▸ m0))
    · exact hr ((by decide : ∀ q ∈ [Reg.x4, .x5, .x6, .x7, .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x24], q ∈ selRegs) r (h ▸ m1))
  obtain other : ∀ q < 12, q ≠ 2 * j → q ≠ 2 * j + 1 → u.gpr (entryReg q) = t.gpr (entryReg q) := fun q hq h0 h1 => by
    refine ug _ fun hm => ?_
    obtain o := entryReg_out q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm o
    rcases hm with h | h | h | h
    · exact o.2.2.1 h
    · exact o.2.2.2.1 h
    · exact entryReg_ne q hq _ (by omega_using [hj]) h0 h
    · exact entryReg_ne q hq _ (by omega_using [hj]) h1 h
  refine ⟨fun q hq => ?_, fun q hq hn => ?_, uz.trans h.zf, fun r hr => (ug r (o8 r hr)).trans (h.gpr r hr), ?_,
    um.trans h.mem, urd.trans h.rd, uwr.trans h.wr, usp.trans h.sp⟩
  · rcases (by omega_using [hq] : q < 2 * j ∨ q = 2 * j ∨ q = 2 * j + 1) with hq | rfl | rfl
    · rw [other q (by omega_using [hq, hj]) (by omega_using [hq]) (by omega_using [hq])]; exact h.done q hq
    · rw [u0, h.zf, h.rest _ (by omega_using [hj]) (Nat.le_refl _)]
    · rw [u1, h.zf, h.rest _ (by omega_using [hj]) (by omega_using [])]
  · rw [other q hq (by omega_using [hn]) (by omega_using [hn])]; exact h.rest q hq (by omega_using [hn])
  · refine (ug _ fun hm => ?_).trans h.x8
    obtain o := entryReg_out (2 * j) (by omega_using [hj])
    obtain o' := entryReg_out (2 * j + 1) (by omega_using [hj])
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, reduceCtorEq, false_or] at hm o o'
    rcases hm with h | h
    · exact o.2.2.2.2.1 h.symm
    · exact o'.2.2.2.2.1 h.symm

private theorem count_fact : ∀ a ≤ 8, ∀ m < 8,
    (BitVec.ofNat 64 a - BitVec.ofNat 64 m) - BitVec.ofNat 64 1 = BitVec.ofNat 64 a - BitVec.ofNat 64 (m + 1) ∧
      decide (((BitVec.ofNat 64 a - BitVec.ofNat 64 (m + 1)) &&& (BitVec.ofNat 64 a - BitVec.ofNat 64 (m + 1)) : Word) = 0) =
        decide (a = m + 1) := by decide

theorem selectTest_ok {s : State} {a m : Nat} (ha : a ≤ 8) (hm : m < 8)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 a - BitVec.ofNat 64 m) :
    WP isa (.block [.subImm .x .x8 .x8 1, .tst .x .x8 .x8]) s fun t =>
      t.gpr .x8 = BitVec.ofNat 64 a - BitVec.ofNat 64 (m + 1) ∧ t.zf = decide (a = m + 1) ∧ Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show (1 : Nat) < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, h8, (count_fact a ha m hm).1, (count_fact a ha m hm).2,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem advance_ok (s : State) :
    WP isa (.block [.addImm .x .x1 .x1 96]) s fun t =>
      t.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 96 ∧ Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show (96 : Nat) < 4096 from by decide,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

/-- The selection's invariant after `m` candidates. -/
structure SelInv (s₀ : State) (base T : Addr) (i a m : Nat) (s : State) : Prop where
  x1 : s.gpr .x1 = T + BitVec.ofNat 64 (768 * i + 96 * m)
  x8 : s.gpr .x8 = BitVec.ofNat 64 a - BitVec.ofNat 64 m
  words : ∀ q < 12, s.gpr (entryReg q) = if a ≤ m then selWord i a q else selWord i 0 q
  gpr : ∀ r, r ∉ .x1 :: selRegs → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem selectEntry_ok {s₀ s : State} {base T : Addr} {i a m : Nat} (htb : TblAt s₀ base T) (hi : i < 64) (ha : a ≤ 8)
    (hm : m < 8) (h : SelInv s₀ base T i a m s) : WP isa (.block selectEntry) s (SelInv s₀ base T i a (m + 1)) := by
  obtain ad : ∀ q, T + BitVec.ofNat 64 (768 * i + 96 * m) + BitVec.ofNat 64 (8 * q) =
      T + BitVec.ofNat 64 (8 * (96 * i + 12 * m + q)) := fun q => by
    rw [Offset.add_add, show 768 * i + 96 * m + 8 * q = 8 * (96 * i + 12 * m + q) by omega_using []]
  simp only [selectEntry, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (selectTest_ok ha hm h.x8) fun t ⟨t8, tz, kt⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectPairs_ok (W := selWord i (m + 1)) ((kt.gpr _ (by decide)).trans h.x1) (fun q hq => by
      rw [ad, kt.rd, kt.wr, h.rd, h.wr]; exact htb.rd _ (by omega_using [hi, hm, hq])) (fun q hq => by
      rw [ad, kt.mem, h.mem, htb.val _ (by omega_using [hi, hm, hq]), selWord_succ hm hq])) fun u hu => ?_
  refine WP.mono (advance_ok u) fun v ⟨v1, kv⟩ => ?_
  refine ⟨?_, ?_, fun q hq => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [v1, hu.gpr _ (by decide), kt.gpr _ (by decide), h.x1, Offset.add_add,
      show 768 * i + 96 * m + 96 = 768 * i + 96 * (m + 1) by omega_using []]
  · rw [kv.gpr _ (by decide), hu.x8, t8]
  · obtain o := entryReg_out q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o
    rw [kv.gpr _ (by simpa only [List.mem_singleton] using o.2.1), hu.done q (by omega_using [hq]), tz,
      kt.gpr _ (by simpa only [List.mem_singleton] using o.2.2.2.2.1), h.words q hq]
    rcases (by omega_using [] : a ≤ m ∨ a = m + 1 ∨ m + 1 < a) with h1 | h1 | h1
    · rw [ite_eq_right (by rw [decide_eq_true_eq]; omega_using [h1]), ite_eq_left h1, ite_eq_left (by omega_using [h1])]
    · subst h1; rw [ite_eq_left (decide_eq_true rfl), ite_eq_left (Nat.le_refl _)]
    · rw [ite_eq_right (by rw [decide_eq_true_eq]; omega_using [h1]), ite_eq_right (by omega_using [h1]),
        ite_eq_right (by omega_using [h1])]
  · simp only [List.mem_cons, not_or] at hr
    obtain ⟨h1, hr⟩ := hr
    rw [kv.gpr r (by simpa only [List.mem_singleton] using h1), hu.gpr r (by simpa only [List.mem_cons, not_or] using hr),
      kt.gpr r (by simp only [List.mem_singleton]; exact hr.2.2.2.2.2.2.1), h.gpr r (by simpa only [List.mem_cons, not_or] using ⟨h1, hr⟩)]
  · rw [kv.mem, hu.mem, kt.mem, h.mem]
  · rw [kv.rd, hu.rd, kt.rd, h.rd]
  · rw [kv.wr, hu.wr, kt.wr, h.wr]
  · rw [kv.sp, hu.sp, kt.sp, h.sp]

theorem selectInit_ok (s : State) (i : Nat) :
    WP isa (.block selectInit) s fun t => (∀ q < 12, t.gpr (entryReg q) = selWord i 0 q) ∧
      Keeps [.x4, .x5, .x6, .x7, .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [selectInit, List.range, List.range.loop, List.map_cons, List.map_nil, entryReg, List.getD_cons_zero,
    List.getD_cons_succ, runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨fun q hq => ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [selWord_zero i q hq]
    rcases (by omega_using [hq] : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false] <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

theorem select_ok {s : State} {base T : Addr} {i a : Nat} (htb : TblAt s base T) (hi : i < 64) (ha : a ≤ 8)
    (h1 : s.gpr .x1 = T + BitVec.ofNat 64 (768 * i)) (h8 : s.gpr .x8 = BitVec.ofNat 64 a) :
    WP isa (.block select) s fun t => (∀ q < 12, t.gpr (entryReg q) = selWord i a q) ∧
      t.gpr .x1 = T + BitVec.ofNat 64 (768 * (i + 1)) ∧
      (∀ r, r ∉ .x1 :: selRegs → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rw [select, WP.block_append_iff]
  refine WP.mono (selectInit_ok s i) fun u ⟨uw, ku⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (SelInv s base T i a) (fun m t hm h => selectEntry_ok htb hi ha hm h) 8
    (Nat.le_refl _) u ⟨?_, ?_, fun q hq => ?_, fun r hr => ku.gpr r fun hm => hr ?_, ku.mem, ku.rd, ku.wr, ku.sp⟩)
    fun t h => ⟨fun q hq => ?_, ?_, h.gpr, h.mem, h.rd, h.wr, h.sp⟩
  · rw [ku.gpr _ (by decide), h1, Nat.mul_zero, Nat.add_zero]
  · rw [ku.gpr _ (by decide), h8, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.sub_zero]
  · rw [uw q hq]
    split
    · rw [show a = 0 by omega_using [‹a ≤ 0›]]
    · rfl
  · exact (by decide : ∀ q ∈ [Reg.x4, .x5, .x6, .x7, .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x24], q ∈ Reg.x1 :: selRegs) r hm
  · rw [h.words q hq, ite_eq_left ha]
  · rw [h.x1, show 768 * i + 96 * 8 = 768 * (i + 1) by omega_using []]

/-- The entry's coordinates in registers. -/
theorem entry_v4 {t : State} {i a : Nat} (h : ∀ q < 12, t.gpr (entryReg q) = selWord i a q) :
    v4 t .x4 .x5 .x6 .x7 = (combCoord (combCached64 i a) 0).val ∧
    v4 t .x12 .x13 .x14 .x15 = (combCoord (combCached64 i a) 1).val ∧
    v4 t .x21 .x22 .x23 .x24 = (combCoord (combCached64 i a) 2).val := by
  obtain hv : ∀ x : Spec.X25519.Fe, val4 (BitVec.ofNat 64 (x.val / 2 ^ (64 * 0) % 2 ^ 64)) (BitVec.ofNat 64 (x.val / 2 ^ (64 * 1) % 2 ^ 64))
      (BitVec.ofNat 64 (x.val / 2 ^ (64 * 2) % 2 ^ 64)) (BitVec.ofNat 64 (x.val / 2 ^ (64 * 3) % 2 ^ 64)) = x.val := fun x => by
    have := x.isLt
    simp only [val4, BitVec.toNat_ofNat, Spec.X25519.P, Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.div_one, Nat.mod_mod,
      show 64 * 2 = 128 from rfl, show 64 * 3 = 192 from rfl] at this ⊢
    omega_using [this]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hv]; exact congr (congr (congr (congrArg val4 (h 0 (by decide))) (h 1 (by decide))) (h 2 (by decide))) (h 3 (by decide))
  · rw [← hv]; exact congr (congr (congr (congrArg val4 (h 4 (by decide))) (h 5 (by decide))) (h 6 (by decide))) (h 7 (by decide))
  · rw [← hv]; exact congr (congr (congr (congrArg val4 (h 8 (by decide))) (h 9 (by decide))) (h 10 (by decide))) (h 11 (by decide))

/-! ## The sign -/

/-- `p` less an element, in words. -/
theorem negT_value (c0 c1 c2 c3 : Word) (hc : val4 c0 c1 c2 c3 < Spec.X25519.P) :
    let n0 : Word := 0 - BitVec.ofNat 64 19
    let n1 : Word := 0 - BitVec.ofNat 64 1
    let n3 : Word := n1 >>> 1
    let k0 := carryOut n0 (~~~c0) true
    let k1 := carryOut n1 (~~~c1) k0
    let k2 := carryOut n1 (~~~c2) k1
    toFe (val4 (addCarry n0 (~~~c0) true) (addCarry n1 (~~~c1) k0) (addCarry n1 (~~~c2) k1)
      (addCarry n3 (~~~c3) k2)) = 0 - toFe (val4 c0 c1 c2 c3) := by
  intro n0 n1 n3 k0 k1 k2
  obtain e := sub4_value n0 n1 n1 n3 c0 c1 c2 c3 true
  obtain hp : val4 n0 n1 n1 n3 = Spec.X25519.P := by decide
  obtain hl := val4_lt (addCarry n0 (~~~c0) true) (addCarry n1 (~~~c1) k0) (addCarry n1 (~~~c2) k1) (addCarry n3 (~~~c3) k2)
  obtain hk := Bool.toNat_le (carryOut n3 (~~~c3) k2)
  rw [← toFe_zero]
  apply toFe_sub
  simp only [Bool.toNat_true, Nat.sub_self, Nat.add_zero] at e
  rw [hp] at e
  change val4 (addCarry n0 (~~~c0) true) (addCarry n1 (~~~c1) k0) (addCarry n1 (~~~c2) k1) (addCarry n3 (~~~c3) k2) +
    val4 c0 c1 c2 c3 = Spec.X25519.P + 2 ^ 256 * (1 - (carryOut n3 (~~~c3) k2).toNat) at e
  generalize val4 (addCarry n0 (~~~c0) true) (addCarry n1 (~~~c1) k0) (addCarry n1 (~~~c2) k1) (addCarry n3 (~~~c3) k2) = R at *
  have h1 : (carryOut n3 (~~~c3) k2).toNat = 1 := by omega_using [e, hl, hc, hk]
  rw [h1, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at e
  rw [e, Nat.mod_self, Nat.zero_mod]

theorem negT_ok (s : State) (hz : s.gpr .x10 = 0) (hc : v4 s .x21 .x22 .x23 .x24 < Spec.X25519.P) :
    WP isa (.block negT) s fun t =>
      toFe (v4 t .x2 .x17 .x20 .x8) = 0 - toFe (v4 s .x21 .x22 .x23 .x24) ∧ Keeps [.x2, .x3, .x8, .x17, .x20] s t := by
  apply WP.of_runBlock
  simp only [v4, negT, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show (19 : Nat) < 4096 from by decide,
    show (1 : Nat) < 4096 from by decide, show (1 : Nat) < Size.x.bits from by decide,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, hz, Option.some.injEq, exists_eq_left']
  sum_done (negT_value (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24) hc)

private theorem mask_zero : ∀ b : Bool, decide ((mask b &&& mask b : Word) = 0) = !b := by decide

theorem negateRegs_ok (s : State) {sg : Bool} (h9 : s.gpr .x9 = mask sg) :
    WP isa (.block negateRegs) s fun t =>
      v4 t .x16 .x4 .x5 .x6 = (if sg = true then v4 s .x12 .x13 .x14 .x15 else v4 s .x4 .x5 .x6 .x7) ∧
      v4 t .x12 .x13 .x14 .x15 = (if sg = true then v4 s .x4 .x5 .x6 .x7 else v4 s .x12 .x13 .x14 .x15) ∧
      v4 t .x21 .x22 .x23 .x24 = (if sg = true then v4 s .x2 .x17 .x20 .x8 else v4 s .x21 .x22 .x23 .x24) ∧
      Keeps [.x16, .x4, .x5, .x6, .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [negateRegs, swapWord, List.cons_append, List.nil_append, v4, runBlock_cons, runStep_some, runBlock_nil,
    exec, read_x, CondCode.holds, RegUpd.zf_write, h9, mask_zero, Bool.not_not,
    ↓RegUpd.gpr_write, BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left', ite_val4]
  refine ⟨trivial, trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-! ## The entry in memory -/

/-- `t` is `s` but for the registers of `lclob` and slots 0–13, and `x1` and `x19`. -/
structure EF (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ .x1 :: .x19 :: lclob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 448 s.mem t.mem

theorem EF.trans {base : Addr} {s t u : State} (h : EF base s t) (k : EF base t u) : EF base s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem EF.of_lf {base : Addr} {s t : State} (h : LF base s t) : EF base s t :=
  ⟨fun r hr => h.gpr r fun hm => hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)), h.rd, h.wr, h.sp, h.mem⟩

theorem EF.of_keeps {base : Addr} {rs : List Reg} {s t : State} (k : Keeps rs s t)
    (hr : ∀ r ∈ rs, r ∈ .x1 :: .x19 :: lclob) : EF base s t :=
  ⟨fun r h => k.gpr r fun hm => h (hr r hm), k.rd, k.wr, k.sp, by rw [k.mem]; exact Outside.refl _ _ _ _⟩

theorem EF.scr {base : Addr} {s t : State} (h : EF base s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem EF.zero {base : Addr} {s t : State} (h : EF base s t) (hz : s.gpr .x10 = 0) : t.gpr .x10 = 0 :=
  (h.gpr _ (by decide)).trans hz

theorem entryStore_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block entryStore) s fun t =>
      env t.mem base 4 = toFe (v4 s .x16 .x4 .x5 .x6) ∧ env t.mem base 5 = toFe (v4 s .x12 .x13 .x14 .x15) ∧
      env t.mem base 6 = toFe (v4 s .x21 .x22 .x23 .x24) ∧
      (∀ i : Slot, i ≠ 4 → i ≠ 5 → i ≠ 6 → env t.mem base i = env s.mem base i ∧
        fe t.mem base (offset i) = fe s.mem base (offset i)) ∧ t.gpr = s.gpr ∧ LF base s t := by
  simp only [entryStore, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (putPairs_ok hs 4 (by decide) _ _ _ _) fun a ⟨pa, ga, fa⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (putPairs_ok (pa.scr hs) 5 (by decide) _ _ _ _) fun b ⟨pb, gb, fb⟩ => ?_
  refine WP.mono (putPairs_ok (pb.scr (pa.scr hs)) 6 (by decide) _ _ _ _) fun t ⟨pt, gt, ft⟩ => ?_
  refine ⟨?_, ?_, ?_, fun i h4 h5 h6 => ⟨?_, ?_⟩, by rw [gt, gb, ga],
    (pa.lf (by decide)).trans ((pb.lf (by decide)).trans (pt.lf (by decide)))⟩
  · rw [env, F, pt.fe (by decide), pb.fe (by decide), fa]
  · rw [env, F, pt.fe (by decide), fb, v4, ga]
  · rw [env, F, ft, v4, gb, ga]
  · rw [env, env, F, pt.fe h6, pb.fe h5, pa.fe h4]
  · rw [pt.fe h6, pb.fe h5, pa.fe h4]

/-- Digit `x19`'s entry, `[(n - 8) 16^i]B` cached, in slots 4–6. -/
theorem entry_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T) {i n : Nat} (hi : i < 64)
    (hn : n < 16) (h19 : s.gpr .x19 = BitVec.ofNat 64 i) (h1 : s.gpr .x1 = T + BitVec.ofNat 64 (768 * i))
    (h10 : s.gpr .x10 = 0) (hm : s.mem (off base (NIB + i)) = BitVec.ofNat 8 n) :
    WP isa (.block entry) s fun t =>
      (∃ q, q.Z = 1 ∧ Rep q ((((n : ℤ) - 8) * 16 ^ i) • baseAff) ∧ env t.mem base 4 = q.Y - q.X ∧
        env t.mem base 5 = q.Y + q.X ∧ env t.mem base 6 = q.T * 2 * Spec.Ed25519.d) ∧
      (∀ j : Slot, j.val < 4 → env t.mem base j = env s.mem base j ∧ fe t.mem base (offset j) = fe s.mem base (offset j)) ∧
      t.gpr .x1 = T + BitVec.ofNat 64 (768 * (i + 1)) ∧ t.gpr .x19 = s.gpr .x19 ∧ EF base s t := by
  obtain hmag : mag n ≤ 8 := Nat.le_of_lt_succ (mag_lt hn)
  rw [entry, WP.block_append_iff]
  refine WP.mono (digit_ok hs hi hn h19 h10 hm) fun a ⟨a8, a9, ka⟩ => ?_
  obtain hta : TblAt a base T := htb.of_far (by rw [ka.rd, ka.wr]) fun x _ => by rw [ka.mem]
  rw [WP.block_append_iff]
  refine WP.mono (select_ok hta hi hmag ((ka.gpr _ (by decide)).trans h1) a8) fun b ⟨bw, b1, bg, bm, brd, bwr, bsp⟩ => ?_
  obtain ⟨bx, by', bt⟩ := entry_v4 bw
  obtain b10 : b.gpr .x10 = 0 := by rw [bg _ (by decide), ka.gpr _ (by decide), h10]
  rw [WP.block_append_iff]
  refine WP.mono (negT_ok b b10 (by rw [bt]; exact Fin.isLt _)) fun c ⟨ct, kc⟩ => ?_
  obtain c9 : c.gpr .x9 = mask (decide (n < 8)) := by rw [kc.gpr _ (by decide), bg _ (by decide), a9]
  obtain hsc : Scr c base := ⟨by rw [kc.gpr _ (by decide), bg _ (by decide), ka.gpr _ (by decide)]; exact hs.x0,
    by rw [kc.wr, bwr, ka.wr]; exact hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (negateRegs_ok c c9) fun d ⟨dx, dy, dt, kd⟩ => ?_
  refine WP.mono (entryStore_ok (hsc.of_keeps kd (by decide))) fun t ⟨t4, t5, t6, tr, tg, tl⟩ => ?_
  obtain kk : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x24], c.gpr r = b.gpr r := by
    intro r hr
    exact kc.gpr r fun h => by revert r; decide
  obtain cx : v4 c .x4 .x5 .x6 .x7 = v4 b .x4 .x5 .x6 .x7 := by
    rw [v4, kk _ (by decide), kk _ (by decide), kk _ (by decide), kk _ (by decide)]
  obtain cy : v4 c .x12 .x13 .x14 .x15 = v4 b .x12 .x13 .x14 .x15 := by
    rw [v4, kk _ (by decide), kk _ (by decide), kk _ (by decide), kk _ (by decide)]
  obtain cz : v4 c .x21 .x22 .x23 .x24 = v4 b .x21 .x22 .x23 .x24 := by
    rw [v4, kk _ (by decide), kk _ (by decide), kk _ (by decide), kk _ (by decide)]
  rw [cx, cy, bx, by'] at dx dy
  rw [cz, bt] at dt
  rw [bt, toFe_self] at ct
  obtain md : d.mem = s.mem := by rw [kd.mem, kc.mem, bm, ka.mem]
  obtain tf : ∀ (z : Bool) (x y : Nat), toFe (if z = true then x else y) = if z = true then toFe x else toFe y :=
    fun z x y => by cases z <;> rfl
  rw [dx, tf, toFe_self, toFe_self] at t4
  rw [dy, tf, toFe_self, toFe_self] at t5
  rw [dt, tf, ct, toFe_self] at t6
  obtain ⟨q, hq, hqz, hrq⟩ := combEntry64_ok i n hi hn
  refine ⟨⟨q, hqz, hrq, ?_⟩, fun j hj => ?_, ?_, ?_, ?_⟩
  · obtain c0 : ∀ p, combCoord p 0 = p.X := fun _ => rfl
    obtain c1 : ∀ p, combCoord p 1 = p.Y := fun _ => rfl
    obtain c2 : ∀ p, combCoord p 2 = p.Z := fun _ => rfl
    rw [c0, c1] at t4 t5
    rw [c2] at t6
    obtain hc := congrArg (fun p => (p.X, p.Y, p.Z)) hq
    simp only [cache, Prod.mk.injEq] at hc
    rw [t4, t5, t6]
    by_cases hlt : n < 8
    · simp only [hlt, ↓reduceIte, negCached] at hc
      simp only [hlt, decide_true, ↓reduceIte]
      exact hc
    · simp only [hlt, ↓reduceIte] at hc
      simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hc
  · obtain h := tr j (by rintro rfl; revert hj; decide) (by rintro rfl; revert hj; decide) (by rintro rfl; revert hj; decide)
    rw [md] at h
    exact h
  · rw [tg, kd.gpr _ (by decide), kc.gpr _ (by decide), b1]
  · rw [tg, kd.gpr _ (by decide), kc.gpr _ (by decide), bg _ (by decide), ka.gpr _ (by decide)]
  · refine (EF.of_keeps ka (by decide)).trans (EF.trans (t := b) ⟨fun r hr => bg r fun h => hr ?_, brd, bwr, bsp, ?_⟩
      ((EF.of_keeps kc (by decide)).trans ((EF.of_keeps kd (by decide)).trans (EF.of_lf tl))))
    · exact (by decide : ∀ q ∈ Reg.x1 :: selRegs, q ∈ .x1 :: .x19 :: lclob) r h
    · rw [bm]; exact Outside.refl _ _ _ _

/-! ## The addition -/

theorem addA_ok {s : State} {base : Addr} (hs : Scr s base) (hz : s.gpr .x10 = 0) (hb : Sm s.mem base 0) :
    WP isa (.block addA) s fun t => Put base 8 s t ∧
      F t.mem base (offset 8) = env s.mem base 4 * (env s.mem base 1 - env s.mem base 0) ∧
      fe t.mem base (offset 8) < 2 ^ 255 + 2 ^ 135 := by
  rw [addA, WP.block_append_iff]
  refine WP.mono (diffRegs_ok hs hz 1 0 (by decide) (by decide) hb) fun u ⟨e, k⟩ => ?_
  refine WP.mono (mulInto_ok (hs.of_keeps k (by decide)) ((k.gpr _ (by decide)).trans hz) 8 4 (by decide)) fun t ⟨p, h, l⟩ => ?_
  exact ⟨Put.of_keeps k (fun _ h => h) p, by rw [h, e, k.mem], l⟩

theorem addB_ok {s : State} {base : Addr} (hs : Scr s base) (hz : s.gpr .x10 = 0) (ha : Sm s.mem base 1)
    (hb : Sm s.mem base 0) :
    WP isa (.block addB) s fun t => Put base 9 s t ∧
      F t.mem base (offset 9) = env s.mem base 5 * (env s.mem base 1 + env s.mem base 0) ∧
      fe t.mem base (offset 9) < 2 ^ 255 + 2 ^ 135 := by
  rw [addB, WP.block_append_iff]
  refine WP.mono (sumRegs_ok hs hz 1 0 (by decide) (by decide) ha hb) fun u ⟨e, k⟩ => ?_
  refine WP.mono (mulInto_ok (hs.of_keeps k (by decide)) ((k.gpr _ (by decide)).trans hz) 9 5 (by decide)) fun t ⟨p, h, l⟩ => ?_
  exact ⟨Put.of_keeps k (fun _ h => h) p, by rw [h, e, k.mem], l⟩

theorem sumIn_ok (s : State) (hz : s.gpr .x10 = 0)
    (hb : v4 s .x4 .x5 .x6 .x7 + v4 s .x21 .x22 .x23 .x24 < 2 ^ 256 + 2 ^ 191) :
    WP isa (.block (sum3 .x4 .x5 .x6 .x7 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3)) s fun t =>
      toFe (v4 t .x4 .x5 .x6 .x7) = toFe (v4 s .x4 .x5 .x6 .x7) + toFe (v4 s .x21 .x22 .x23 .x24) ∧
      Keeps [.x4, .x5, .x6, .x7, .x2, .x3] s t := by
  sum_run hz
  sum_done (sum3_value _ _ _ _ _ _ _ _ hb)

theorem sumIn4_ok (s : State) (hz : s.gpr .x10 = 0)
    (hb : v4 s .x4 .x5 .x6 .x7 + v4 s .x21 .x22 .x23 .x24 < 2 * 2 ^ 256 - 38) :
    WP isa (.block (sum4 .x4 .x5 .x6 .x7 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3)) s fun t =>
      toFe (v4 t .x4 .x5 .x6 .x7) = toFe (v4 s .x4 .x5 .x6 .x7) + toFe (v4 s .x21 .x22 .x23 .x24) ∧
      Keeps [.x4, .x5, .x6, .x7, .x2, .x3] s t := by
  sum_run hz
  sum_done (sum4_value _ _ _ _ _ _ _ _ hb)

theorem sumTwice_ok (s : State) (hz : s.gpr .x10 = 0)
    (hb : v4 s .x4 .x5 .x6 .x7 + v4 s .x4 .x5 .x6 .x7 < 2 ^ 256 + 2 ^ 191) :
    WP isa (.block (sum3 .x4 .x5 .x6 .x7 .x4 .x5 .x6 .x7 .x4 .x5 .x6 .x7 .x2 .x3)) s fun t =>
      toFe (v4 t .x4 .x5 .x6 .x7) = toFe (v4 s .x4 .x5 .x6 .x7) + toFe (v4 s .x4 .x5 .x6 .x7) ∧
      Keeps [.x4, .x5, .x6, .x7, .x2, .x3] s t := by
  sum_run hz
  sum_done (sum3_value _ _ _ _ _ _ _ _ hb)

/-- Four registers a block keeps. -/
theorem v4_keeps {rs : List Reg} {s t : State} (k : Keeps rs s t) {a b c d : Reg} (h : ∀ r ∈ [a, b, c, d], r ∉ rs) :
    v4 t a b c d = v4 s a b c d := by
  rw [v4, k.gpr a (h a (by simp)), k.gpr b (h b (by simp)), k.gpr c (h c (by simp)), k.gpr d (h d (by simp))]

theorem addEH_ok {s : State} {base : Addr} (hs : Scr s base) (hz : s.gpr .x10 = 0) (ha : Sm s.mem base 9)
    (hb : Sm s.mem base 8) :
    WP isa (.block addEH) s fun t => env t.mem base 7 = env s.mem base 9 - env s.mem base 8 ∧
      env t.mem base 11 = env s.mem base 9 + env s.mem base 8 ∧
      (∀ i : Slot, i ≠ 7 → i ≠ 11 → env t.mem base i = env s.mem base i ∧ fe t.mem base (offset i) = fe s.mem base (offset i)) ∧
      LF base s t := by
  rw [show addEH = (loadPairs (offset 9) .x4 .x5 .x6 .x7 ++ loadPairs (offset 8) .x21 .x22 .x23 .x24) ++
    (diff4 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3 ++
    (storePairs (offset 7) .x12 .x13 .x14 .x15 ++
    (sum3 .x4 .x5 .x6 .x7 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3 ++
    storePairs (offset 11) .x4 .x5 .x6 .x7))) by simp only [addEH, List.append_assoc], WP.block_append_iff]
  refine WP.mono (two_ok hs 9 8 (by decide) (by decide)) fun a ⟨a9, a8, ka⟩ => ?_
  obtain hsa := hs.of_keeps ka (by decide)
  obtain za := (ka.gpr .x10 (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (diffReg_ok a za (by rw [a8]; omega_using [hb])) fun b ⟨eb, kb⟩ => ?_
  obtain hsb := hsa.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (putPairs_ok hsb 7 (by decide) _ _ _ _) fun c ⟨pc, gc, fc⟩ => ?_
  obtain c4 : v4 c .x4 .x5 .x6 .x7 = fe s.mem base (offset 9) := by
    rw [← a9, v4, gc]; exact v4_keeps kb (by decide)
  obtain c21 : v4 c .x21 .x22 .x23 .x24 = fe s.mem base (offset 8) := by
    rw [← a8, v4, gc]; exact v4_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sumIn_ok c (pc.zero ((kb.gpr _ (by decide)).trans za)) (by rw [c4, c21]; omega_using [ha, hb]))
    fun d ⟨ed, kd⟩ => ?_
  refine WP.mono (putPairs_ok ((pc.scr hsb).of_keeps kd (by decide)) 11 (by decide) _ _ _ _) fun t ⟨pt, _, ft⟩ => ?_
  rw [a9, a8] at eb
  rw [c4, c21] at ed
  refine ⟨?_, ?_, fun i h7 h11 => ⟨?_, ?_⟩, ?_⟩
  · rw [env, F, pt.fe (by decide), kd.mem, fc]; exact eb
  · rw [env, F, ft]; exact ed
  · rw [env, env, F, pt.fe h11, kd.mem, pc.fe h7, kb.mem, ka.mem]
  · rw [pt.fe h11, kd.mem, pc.fe h7, kb.mem, ka.mem]
  · exact (LF.of_keeps ka (by decide)).trans ((LF.of_keeps kb (by decide)).trans ((pc.lf (by decide)).trans
      ((LF.of_keeps kd (by decide)).trans (pt.lf (by decide)))))

theorem addFG_ok {s : State} {base : Addr} (hs : Scr s base) (hz : s.gpr .x10 = 0) (ha : Sm s.mem base 2)
    (hb : Sm s.mem base 10) :
    WP isa (.block addFG) s fun t => Put base 13 s t ∧
      F t.mem base (offset 13) = (env s.mem base 2 + env s.mem base 2) + env s.mem base 10 ∧
      toFe (v4 t .x12 .x13 .x14 .x15) = (env s.mem base 2 + env s.mem base 2) - env s.mem base 10 := by
  simp only [addFG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (getPairs_ok hs 2 (by decide) (by decide)) fun a ⟨a2, ka⟩ => ?_
  obtain hsa := hs.of_keeps ka (by decide)
  obtain za := (ka.gpr .x10 (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (sumTwice_ok a za (by rw [a2]; omega_using [ha])) fun b ⟨eb, kb⟩ => ?_
  obtain hsb := hsa.of_keeps kb (by decide)
  obtain zb := (kb.gpr .x10 (by decide)).trans za
  rw [WP.block_append_iff]
  refine WP.mono (getPairs_ok hsb 10 (by decide) (by decide)) fun c ⟨c10, kc⟩ => ?_
  obtain hsc := hsb.of_keeps kc (by decide)
  obtain zc := (kc.gpr .x10 (by decide)).trans zb
  obtain c4 : v4 c .x4 .x5 .x6 .x7 = v4 b .x4 .x5 .x6 .x7 := v4_keeps kc (by decide)
  rw [kb.mem, ka.mem] at c10
  rw [WP.block_append_iff]
  refine WP.mono (diffReg_ok c zc (by rw [c10]; omega_using [hb])) fun d ⟨ed, kd⟩ => ?_
  obtain d4 : v4 d .x4 .x5 .x6 .x7 = v4 b .x4 .x5 .x6 .x7 := (v4_keeps kd (by decide)).trans c4
  obtain d21 : v4 d .x21 .x22 .x23 .x24 = fe s.mem base (offset 10) := (v4_keeps kd (by decide)).trans c10
  obtain lt := val4_lt (b.gpr .x4) (b.gpr .x5) (b.gpr .x6) (b.gpr .x7)
  rw [WP.block_append_iff]
  refine WP.mono (sumIn4_ok d ((kd.gpr _ (by decide)).trans zc) (by
      rw [d4, d21]
      show val4 _ _ _ _ + _ < _
      omega_using [lt, hb])) fun e ⟨ee, ke⟩ => ?_
  refine WP.mono (putPairs_ok ((hsc.of_keeps kd (by decide)).of_keeps ke (by decide)) 13 (by decide) _ _ _ _)
    fun t ⟨pt, gt, ft⟩ => ?_
  obtain kk : Keeps lclob s e := (ka.mono (by decide)).trans ((kb.mono (by decide)).trans ((kc.mono (by decide)).trans
    ((kd.mono (by decide)).trans (ke.mono (by decide)))))
  rw [a2] at eb
  rw [c4, eb, c10] at ed
  rw [d4, eb, d21] at ee
  refine ⟨Put.of_keeps kk (fun _ h => h) pt, ?_, ?_⟩
  · rw [F, ft]; exact ee
  · rw [v4, gt, show val4 _ _ _ _ = v4 e .x12 .x13 .x14 .x15 from rfl, v4_keeps ke (by decide)]; exact ed

/-- What `addEntry` computes, from the point's coordinates and the cached entry's. -/
def mixed (x y z t q₀ q₁ q₂ : Spec.X25519.Fe) : Spec.Ed25519.Point :=
  let a := q₀ * (y - x)
  let b := q₁ * (y + x)
  let c := t * q₂
  let e := b - a
  let h := b + a
  let g := (z + z) + c
  let f := (z + z) - c
  ⟨e * f, g * h, g * f, e * h⟩

theorem mixed_eq (p q : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixed p.X p.Y p.Z p.T (q.Y - q.X) (q.Y + q.X) (q.T * 2 * Spec.Ed25519.d) = Spec.Ed25519.pointAdd p q := by
  simp only [mixed, Spec.Ed25519.pointAdd, hz]
  -- `-lia`: Lean 4.36's `grind` builds a proof the kernel rejects from `lia`
  -- over `Fin` of a non-literal modulus (lean4#15857, fixed in 4.37).
  congr 1 <;> grind -lia

/-- The accumulator's coordinates are below `2²⁵⁵ + 2¹³⁶`. -/
abbrev AccSm (m : Mem) (base : Addr) : Prop := ∀ i : Slot, i.val < 4 → Sm m base i

theorem addEntry_ok {s : State} {base : Addr} (hs : Scr s base) (hz : s.gpr .x10 = 0) (ha : AccSm s.mem base) :
    WP isa (.block addEntry.flatten) s fun t =>
      point (env t.mem base) 0 1 2 3 = (let e := env s.mem base; mixed (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6)) ∧
      AccSm t.mem base ∧ LF base s t := by
  simp only [addEntry, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [WP.block_append_iff]
  refine WP.mono (addA_ok hs hz (ha 0 (by decide))) fun a ⟨pa, fa, ba⟩ => ?_
  obtain hsa := pa.scr hs
  obtain za := pa.zero hz
  rw [WP.block_append_iff]
  refine WP.mono (addB_ok hsa za (by rw [Sm, pa.fe (by decide)]; exact ha 1 (by decide))
    (by rw [Sm, pa.fe (by decide)]; exact ha 0 (by decide))) fun b ⟨pb, fb, bb⟩ => ?_
  obtain hsb := pb.scr hsa
  obtain zb := pb.zero za
  rw [WP.block_append_iff]
  refine WP.mono (mulSlots_ok hsb zb 10 3 6 (by decide) (by decide)) fun c ⟨pc, fc, bc⟩ => ?_
  obtain hsc := pc.scr hsb
  obtain zc := pc.zero zb
  rw [WP.block_append_iff]
  refine WP.mono (addEH_ok hsc zc (by rw [Sm, pc.fe (by decide)]; omega_using [bb])
    (by rw [Sm, pc.fe (by decide), pb.fe (by decide)]; omega_using [ba])) fun d ⟨d7, d11, dr, dl⟩ => ?_
  obtain hsd := dl.scr hsc
  obtain zd := dl.zero zc
  rw [WP.block_append_iff]
  refine WP.mono (addFG_ok hsd zd (by
      rw [Sm, (dr 2 (by decide) (by decide)).2, pc.fe (by decide), pb.fe (by decide), pa.fe (by decide)]
      exact ha 2 (by decide)) (by rw [Sm, (dr 10 (by decide) (by decide)).2]; omega_using [bc]))
    fun e ⟨pe, fe', ef⟩ => ?_
  obtain hse := pe.scr hsd
  obtain ze := pe.zero zd
  rw [WP.block_append_iff]
  refine WP.mono (mulKeep_ok hse ze 2 13 (by decide)) fun f ⟨pf, ff, bf, kf⟩ => ?_
  obtain hsf := pf.scr hse
  obtain zf := pf.zero ze
  rw [WP.block_append_iff]
  refine WP.mono (mulKeep_ok hsf zf 0 7 (by decide)) fun g ⟨pg, fg, bg, _⟩ => ?_
  obtain hsg := pg.scr hsf
  obtain zg := pg.zero zf
  rw [WP.block_append_iff]
  refine WP.mono (mulSlotsKeep_ok hsg zg 1 13 11 (by decide) (by decide)) fun h ⟨ph, fh, bh, kh⟩ => ?_
  refine WP.mono (mulKeep_ok (ph.scr hsg) (ph.zero zg) 3 7 (by decide)) fun t ⟨pt, ft, bt, _⟩ => ?_
  -- The values.
  obtain ca : ∀ i : Slot, i.val < 7 → env c.mem base i = env s.mem base i := fun i hi => by
    rw [env, env, F, pc.fe (by rintro rfl; revert hi; decide), pb.fe (by rintro rfl; revert hi; decide),
      pa.fe (by rintro rfl; revert hi; decide)]
  obtain c8 : env c.mem base 8 = env s.mem base 4 * (env s.mem base 1 - env s.mem base 0) := by
    rw [← fa, env, F, pc.fe (by decide), pb.fe (by decide)]
  obtain ea : ∀ i : Slot, i.val < 7 → env a.mem base i = env s.mem base i := fun i hi => by
    rw [env, env, F, pa.fe (by rintro rfl; revert hi; decide)]
  obtain eb : ∀ i : Slot, i.val < 7 → env b.mem base i = env s.mem base i := fun i hi => by
    rw [env, env, F, pb.fe (by rintro rfl; revert hi; decide), pa.fe (by rintro rfl; revert hi; decide)]
  obtain c9 : env c.mem base 9 = env s.mem base 5 * (env s.mem base 1 + env s.mem base 0) := by
    rw [← ea 5 (by decide), ← ea 1 (by decide), ← ea 0 (by decide), ← fb, env, F, pc.fe (by decide)]
  obtain c10 : env c.mem base 10 = env s.mem base 3 * env s.mem base 6 := by
    rw [← eb 3 (by decide), ← eb 6 (by decide), ← fc]
    rfl
  rw [c9, c8] at d7 d11
  rw [(dr 2 (by decide) (by decide)).1, (dr 10 (by decide) (by decide)).1, c10, ca 2 (by decide)] at fe' ef
  obtain e7 : env e.mem base 7 = env d.mem base 7 := by rw [env, env, F, pe.fe (by decide)]
  obtain e11 : env e.mem base 11 = env d.mem base 11 := by rw [env, env, F, pe.fe (by decide)]
  obtain e13 : env e.mem base 13 = F e.mem base (offset 13) := rfl
  obtain g13 : env g.mem base 13 = env e.mem base 13 := by rw [env, env, F, pg.fe (by decide), pf.fe (by decide)]
  obtain g11 : env g.mem base 11 = env e.mem base 11 := by rw [env, env, F, pg.fe (by decide), pf.fe (by decide)]
  obtain f7 : env f.mem base 7 = env e.mem base 7 := by rw [env, env, F, pf.fe (by decide)]
  obtain h7 : env h.mem base 7 = env e.mem base 7 := by
    rw [env, env, F, ph.fe (by decide), pg.fe (by decide), pf.fe (by decide)]
  rw [e13, fe', ef] at ff
  rw [f7, e7, d7, kf, ef] at fg
  rw [g13, e13, fe', g11, e11, d11] at fh
  rw [h7, e7, d7, kh, show toFe (fe g.mem base (offset 11)) = env g.mem base 11 from rfl, g11, e11, d11] at ft
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · simp only [point, mixed]
    obtain t0 : env t.mem base 0 = F g.mem base (offset 0) := by rw [env, F, pt.fe (by decide), ph.fe (by decide)]
    obtain t1 : env t.mem base 1 = F h.mem base (offset 1) := by rw [env, F, pt.fe (by decide)]
    obtain t2 : env t.mem base 2 = F f.mem base (offset 2) := by
      rw [env, F, pt.fe (by decide), ph.fe (by decide), pg.fe (by decide)]
    rw [t0, t1, t2, show env t.mem base 3 = F t.mem base (offset 3) from rfl, fg, fh, ff, ft]
  · obtain hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 :=
      (by decide : ∀ i : Slot, i.val < 4 → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) i hi
    rcases hc with rfl | rfl | rfl | rfl
    · rw [Sm, pt.fe (by decide), ph.fe (by decide)]; omega_using [bg]
    · rw [Sm, pt.fe (by decide)]; omega_using [bh]
    · rw [Sm, pt.fe (by decide), ph.fe (by decide), pg.fe (by decide)]; omega_using [bf]
    · rw [Sm]; omega_using [bt]
  · exact (pa.lf (by decide)).trans ((pb.lf (by decide)).trans ((pc.lf (by decide)).trans (dl.trans
      ((pe.lf (by decide)).trans ((pf.lf (by decide)).trans ((pg.lf (by decide)).trans ((ph.lf (by decide)).trans
      (pt.lf (by decide)))))))))

/-! ## The loop -/

/-- What the comb keeps: every register but `x1`, `x19` and the field code's, and the working space
but slots 0–21. -/
abbrev CK (base : Addr) (s t : State) : Prop := PowersKeep base NIB 64 s t

theorem EF.ck {base : Addr} {s t : State} (h : EF base s t) : CK base s t :=
  ⟨fun r h19 h1 hc => h.gpr r fun hm => by
    simp only [List.mem_cons] at hm
    rcases hm with h | h | h
    · exact h1 h
    · exact h19 h
    · exact hc ((by decide : ∀ q ∈ lclob, q ∈ clob) r h), h.rd, h.wr, h.sp,
    TableFrame.workspace (h.mem.mono (by decide) (by decide))⟩

/-- The loop's invariant, after `j` steps. -/
structure CombInv (s₀ : State) (base T : Addr) (S : Nat) (j : Nat) (s : State) : Prop where
  scr : Scr s base
  zero : s.gpr .x10 = 0
  x19 : s.gpr .x19 = BitVec.ofNat 64 j
  x1 : s.gpr .x1 = T + BitVec.ofNat 64 (768 * j)
  nib : NibAt s.mem base 64 S
  acc : Rep (point (env s.mem base) 0 1 2 3) ((((17 * combGVal : Nat) : ℤ) + digitSum64 S j) • baseAff)
  small : AccSm s.mem base
  keep : EF base s₀ s

theorem next_ok (s : State) {j : Nat} (hj : j < 64) (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 64]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ (t.gpr .x8 != 0) = decide (j + 1 ≠ 64) ∧ Keeps [.x8, .x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show (1 : Nat) < 4096 from by decide,
    show (64 : Nat) < 4096 from by decide, RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h19,
    ← BitVec.ofNat_add, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (by decide : ∀ j < 64, (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 64 != 0) = decide (j + 1 ≠ 64)) j hj,
    ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem far_of {base : Addr} {s t : State} (h : EF base s t) : ∀ x, 8192 ≤ ofs base x → t.mem x = s.mem x :=
  fun x hx => h.mem x (Or.inr (by omega_using [hx]))

theorem NibAt.of_ef {base : Addr} {s t : State} (h : EF base s t) {n S : Nat} (hn : n ≤ 64) (hb : NibAt s.mem base n S) :
    NibAt t.mem base n S := fun i hi => by
  have hN : NIB = 768 := rfl
  rw [h.mem _ (Or.inr (by rw [ofs_off' base (by omega_using [hN, hi, hn])]; omega_using [hN])), hb i hi]

theorem combStep_ok {s₀ s : State} {base T : Addr} {S j : Nat} (htb : TblAt s₀ base T) (hj : j < 64)
    (h : CombInv s₀ base T S j s) :
    WP isa (.block combStep) s fun t => isa.eval (.nonzero .x .x8) t = some (decide (j + 1 ≠ 64)) ∧
      CombInv s₀ base T S (j + 1) t := by
  obtain hts : TblAt s base T := htb.of_far (by rw [h.keep.rd, h.keep.wr]) (far_of h.keep)
  rw [combStep, WP.block_append_iff]
  refine WP.mono (entry_ok h.scr hts hj (nib_lt S j) h.x19 h.x1 h.zero (h.nib j hj))
    fun a ⟨⟨q, hqz, hrq, a4, a5, a6⟩, ar, a1, a19, ka⟩ => ?_
  obtain hsa := ka.scr h.scr
  rw [WP.block_append_iff]
  refine WP.mono (addEntry_ok hsa (ka.zero h.zero) fun i hi => by rw [Sm, (ar i hi).2]; exact h.small i hi)
    fun b ⟨bp, bs, lb⟩ => ?_
  refine WP.mono (next_ok b hj (by rw [lb.gpr _ (by decide), a19, h.x19])) fun t ⟨t19, t8, kt⟩ => ?_
  obtain kk : EF base s t := ka.trans ((EF.of_lf lb).trans (EF.of_keeps kt (by decide)))
  refine ⟨?_, kk.scr h.scr, kk.zero h.zero, t19, ?_, h.nib.of_ef kk (Nat.le_refl _), ?_, ?_, h.keep.trans kk⟩
  · show some (t.read .x .x8 != 0) = _
    rw [read_x, t8]
  · rw [kt.gpr _ (by decide), lb.gpr _ (by decide), a1]
  · rw [kt.mem, bp]
    simp only [(ar 0 (by decide)).1, (ar 1 (by decide)).1, (ar 2 (by decide)).1, (ar 3 (by decide)).1, a4, a5, a6]
    obtain e := mixed_eq (point (env s.mem base) 0 1 2 3) q hqz
    simp only [point] at e
    rw [e, digitSum64, ← add_assoc, add_smul]
    exact pointAdd_rep h.acc (by simpa only [sdig] using hrq)
  · rw [kt.mem]; exact bs

theorem combSteps_ok {s : State} {base T : Addr} {S : Nat} (htb : TblAt s base T) (h : CombInv s base T S 0 s) :
    WP isa (.loop (.block combStep) (.nonzero .x .x8)) s (CombInv s base T S 64) := by
  apply WP.loop (fun n t => CombInv s base T S (64 - n) t ∧ 0 < n ∧ n ≤ 64) (n := 64)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega_using [hn0]⟩
    refine WP.mono (combStep_ok htb (by omega_using []) ht) fun u ⟨ue, hu⟩ => ?_
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨by rw [ue]; rfl, hu⟩
    · refine Or.inr ⟨by rw [ue]; simp only [show 64 - (k + 1) + 1 ≠ 64 by omega_using [hk], ne_eq,
        not_false_eq_true, decide_true], k, by omega_using [], ?_, by omega_using [hk], by omega_using [hn]⟩
      rw [show 64 - k = 64 - (k + 1) + 1 by omega_using [hn]]; exact hu
  · exact ⟨h, by decide, by decide⟩

/-! ## The start -/

private def combStartCheck (p : Spec.Ed25519.Point) : Bool :=
  combStart.X * p.Z == p.X && combStart.Y * p.Z == p.Y && p.Z != 0

private theorem combStart_check :
    combStartCheck (Spec.Ed25519.pointMul (17 * combGVal) Spec.Ed25519.basePoint) = true := by
  decide +kernel

theorem combStart_ok : Rep combStart ((17 * combGVal) • baseAff) := by
  obtain hp := pointMul_rep (17 * combGVal) basePoint_rep
  have hc := combStart_check
  simp only [combStartCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  exact combPt_rep (q := combStartAff) hp hx hy

theorem combRegs_ok (s : State) :
    WP isa (.block [.movz .w .x10 0 0, .adrSym .x1 combSym, .movz .w .x19 0 0]) s fun t =>
      t.gpr .x10 = 0 ∧ t.gpr .x1 = s.syms combSym ∧ t.gpr .x19 = 0 ∧ Keeps [.x10, .x1, .x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, rfl, by decide, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

private theorem small_start : ∀ i : Slot, i.val < 4 →
    smallAfterOps (constPointOps combStart) (fun _ => false) i = true := by decide

/-- `[s]B` into slots 0–3, from the scalar's nibbles. -/
theorem combMultiply_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T) (hT : s.syms combSym = T)
    {S : Nat} (hS : S < 2 ^ 256) (hb : NibAt s.mem base 64 S) :
    WP isa combMultiply s fun t => Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ CK base s t := by
  have hN : NIB = 768 := rfl
  rw [combMultiply, combInit]
  apply WP.seq
  rw [WP.block_append_iff, constPoint]
  refine WP.mono_syms (fieldCode_okS _ hs (Small.none s.mem base)) fun a ⟨ka, ea, sa⟩ sya => ?_
  refine WP.mono (combRegs_ok a) fun b ⟨b10, b1, b19, kb⟩ => ?_
  obtain hsb : Scr b base := (ka.scr hs).of_keeps kb (by decide)
  obtain fb : ∀ x, 768 ≤ ofs base x → b.mem x = s.mem x := fun x hx => by
    rw [kb.mem]; exact ka.mem x (Or.inr (by omega_using [hx]))
  obtain htb' : TblAt b base T := htb.of_far (by rw [kb.rd, kb.wr, ka.rd, ka.wr])
    fun x hx => fb x (by omega_using [hx])
  refine WP.mono (combSteps_ok (S := S) htb' ⟨hsb, b10, b19, ?_, fun i hi => ?_, ?_, fun i hi => ?_,
    EF.of_keeps (rs := []) ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩ nofun⟩) fun t ht => ⟨?_, ?_⟩
  · rw [b1, sya, hT, Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  · rw [fb _ (by rw [ofs_off' base (by omega_using [hN, hi])]; omega_using [hN]), hb i hi]
  · rw [kb.mem, ea, constPoint_eval]
    simpa only [digitSum64, add_zero, natCast_zsmul] using combStart_ok
  · rw [kb.mem]; exact sa i (small_start i hi)
  · have := ht.acc
    rw [comb64_total hS, natCast_zsmul] at this
    exact this
  · refine PowersKeep.trans (t := b) ⟨fun r h19 h1 hc => ?_, ?_, ?_, ?_, ?_⟩ ht.keep.ck
    · rw [kb.gpr r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun h => hc (h ▸ by decide), h1, h19⟩), ka.gpr r hc]
    · rw [kb.rd, ka.rd]
    · rw [kb.wr, ka.wr]
    · rw [kb.sp, ka.sp]
    · rw [kb.mem]; exact TableFrame.workspace ka.mem

end VG.Proof.Ed25519.AArch64
