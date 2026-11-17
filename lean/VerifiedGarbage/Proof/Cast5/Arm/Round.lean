module

public import VerifiedGarbage.Proof.Cast5.Rotate
public import VerifiedGarbage.Proof.Cast5.Round
public import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Cast5.Arm.Run
public import VerifiedGarbage.Proof.Scan.Arm
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Impl.Cast5.Arm
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `Cast5.Arm.Scan`, which this module and modules that import it used -/

section

/-!
# CAST5 on ARMv7: the scan of a table

`scan sym o` makes four lookups in the static `sym`, one after the other
(`look_ok`): each reads its word of the 256 entries as 32 rows of eight
(`Proof/Scan/Arm.lean`), keeps the row of its index's high five bits, and
picks among that row's words by the index's low three bits (`pick_ok`). It
leaves in `r8 + k` word `k` of the entry whose number is in `r4 + k`
(`scan_ok`); `r2`, `r3` and `lr` are saved in the scan's ten words at `o` in
the working space at `r12`, which hold its indices, counts and values
meanwhile, and restored.
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm
open VG.Impl.Scan.Arm (mlaCol rows colReg)

/-- Word `k` of entry `e` of the table at the 32-bit address `T`. -/
def tw (m : Mem) (T : BitVec 32) (e k : Nat) : BitVec 32 :=
  m.readW (State.addr (T + BitVec.ofNat 32 (16 * e + 4 * k))) 32

/-- Word `k` of entry `e` of a table held at `T`, which does not wrap. -/
theorem tw_table {m : Mem} {T : BitVec 32} {a b c d : Byte → Spec.Cast5.Word} (hT : T.toNat + 4096 ≤ 2 ^ 32)
    (h : Held m (State.addr T) (Impl.Cast5.table a b c d)) {e k : Nat} (he : e < 256) (hk : k < 4) :
    tw m T e k = tableEnt a b c d e k := by
  rw [← ent_table h he hk, tw, ent, addr_add (by omega_arith)]

/-- Memory holding a table, later: its words are kept by writes apart from it. -/
theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} {W : List (BitVec 64)} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 8 * W.length⟩ r) (hl : 8 * W.length < 2 ^ 64) (h : Held m T W) :
    Held m' T W := fun i hi => by
  rw [hf.readW (Offset.contains_base _ (by omega_arith) (by omega_arith)) hd (by decide)]
  exact h i hi

/-! ## The indices, a byte each -/

/-- The four indices `ix`, a byte each, the first the lowest. -/
def packN (ix : Nat → Nat) : Nat := ix 0 + 256 * ix 1 + 65536 * ix 2 + 16777216 * ix 3

theorem packN_lt {ix : Nat → Nat} (h : ∀ k < 4, ix k < 256) : packN ix < 2 ^ 32 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  unfold packN
  omega_arith

theorem packN_byte {ix : Nat → Nat} (h : ∀ k < 4, ix k < 256) {k : Nat} (hk : k < 4) :
    packN ix / 256 ^ k % 256 = ix k := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  unfold packN
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow] <;> omega_arith

/-- The indices as `scanStart` packs them. -/
theorem pack_eq (a b c d : BitVec 32) :
    a + b <<< 8 + c <<< 16 + d <<< 24 =
      BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.reducePow]
  omega_arith

theorem and255 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n &&& 255).toNat = n % 256 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, show (255 : BitVec 32).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem and7 {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n &&& 7 = BitVec.ofNat 32 (n % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    show (7 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

theorem shr8 {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 8 = BitVec.ofNat 32 (n / 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h]
  omega_arith

/-! ## Choosing among the row's words -/

/-- The selector of column `c`: 1 if the index's low three bits `l` are `c`. -/
theorem pickSel : ∀ l < 8, ∀ c < 8,
    ((BitVec.ofNat 32 l ^^^ BitVec.ofNat 32 c) - 1) >>> 31 = if l = c then 1 else 0 := by decide

/-- What the picks of the columns below `e` have added to `r1` (`m` false),
or to `r3` (`m` true): column `l`, if it is one of them and of that kind. -/
def pickR (a : Nat → BitVec 32) (l e : Nat) (m : Bool) : BitVec 32 := if l < e ∧ mlaCol l = m then a l else 0

theorem mul_one_add_zero (x : BitVec 32) : x * 1 + 0 = x := by
  show x * 1#32 + 0#32 = x
  rw [BitVec.mul_one, BitVec.add_zero]

theorem pickR_hit (a : Nat → BitVec 32) (l c : Nat) :
    a c * (if l = c then 1 else 0) + pickR a l c (mlaCol c) = pickR a l (c + 1) (mlaCol c) := by
  unfold pickR
  by_cases h : l = c
  · subst h
    rw [ite_eq_left rfl, ite_eq_right (fun h => Nat.lt_irrefl _ h.1), ite_eq_left ⟨Nat.lt_succ_self _, rfl⟩,
      mul_one_add_zero]
  · rw [ite_eq_right h, Scan.Arm.mul_zero_add]
    by_cases hl : l < c ∧ mlaCol l = mlaCol c
    · rw [ite_eq_left hl, ite_eq_left ⟨by omega_using [hl.1], hl.2⟩]
    · rw [ite_eq_right hl, ite_eq_right fun h' => hl ⟨by omega_using [h'.1, h], h'.2⟩]

theorem pickR_miss (a : Nat → BitVec 32) (l : Nat) {c : Nat} {m : Bool} (hm : mlaCol c ≠ m) :
    pickR a l c m = pickR a l (c + 1) m := by
  unfold pickR
  by_cases hl : l < c ∧ mlaCol l = m
  · rw [ite_eq_left hl, ite_eq_left ⟨by omega_using [hl.1], hl.2⟩]
  · rw [ite_eq_right hl, ite_eq_right fun h' => hl ⟨by
      have : l ≠ c := fun e => hm (e ▸ h'.2)
      omega_using [h'.1, this], h'.2⟩]

theorem pickR_res (W : Nat → BitVec 32) {l : Nat} (hl : l < 8) :
    pickR (fun c => Scan.Arm.val c (W c)) l 8 false - pickR (fun c => Scan.Arm.val c (W c)) l 8 true = W l := by
  show (if l < 8 ∧ mlaCol l = false then Scan.Arm.val l (W l) else 0) -
    (if l < 8 ∧ mlaCol l = true then Scan.Arm.val l (W l) else 0) = W l
  unfold Scan.Arm.val
  cases hm : mlaCol l
  · obtain e1 : l < 8 ∧ false = false := ⟨hl, rfl⟩
    obtain e2 : ¬(l < 8 ∧ false = true) := fun h => Bool.false_ne_true h.2
    rw [ite_eq_left e1, ite_eq_right e2, ite_eq_right Bool.false_ne_true]
    show W l - 0#32 = W l
    rw [BitVec.sub_zero]
  · obtain e1 : ¬(l < 8 ∧ true = false) := fun h => Bool.false_ne_true h.2.symm
    obtain e2 : l < 8 ∧ true = true := ⟨hl, rfl⟩
    rw [ite_eq_right e1, ite_eq_left e2, ite_eq_left rfl]
    show 0#32 - -W l = W l
    rw [BitVec.zero_sub, BitVec.neg_neg]

/-- Column `c`, if the index's low three bits `l` (in `lr`) are `c`. -/
theorem pick_ok (s : State) (a : Nat → BitVec 32) {l c : Nat} (hl : l < 8) (hc : c < 8)
    (hlr : s.gpr .lr = BitVec.ofNat 32 l) (ha : s.gpr (colReg c) = a c)
    (h1 : s.gpr .r1 = pickR a l c false) (h3 : s.gpr .r3 = pickR a l c true) :
    WP isa (.block (pick c)) s fun t =>
      t.gpr .r1 = pickR a l (c + 1) false ∧ t.gpr .r3 = pickR a l (c + 1) true ∧
      (∀ q, q ≠ .r0 → q ≠ .r1 → q ≠ .r3 → t.gpr q = s.gpr q) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  obtain hcv := toNat_ofNat_lt (j := c) (by omega_using [hc])
  unfold pick
  cases hk : mlaCol c
  · simp only [Bool.false_eq_true, ite_false]
    crun [hcv, hlr, Scan.Arm.exec_mla, Scan.Arm.colReg_ne_r0, h1, h3]
    refine ⟨?_, pickR_miss a l (by rw [hk]; decide), fun q h0 h1' _ => by simp only [h0, h1', ite_false]⟩
    rw [pickSel l hl c hc, ← hk, ha]
    exact pickR_hit a l c
  · simp only [ite_true]
    crun [hcv, hlr, Scan.Arm.exec_mla, Scan.Arm.colReg_ne_r0, h1, h3]
    refine ⟨pickR_miss a l (by rw [hk]; decide), ?_, fun q h0 _ h3' => by simp only [h0, h3', ite_false]⟩
    rw [pickSel l hl c hc, ← hk, ha]
    exact pickR_hit a l c

/-! ## The scan -/

/-- The address of the scan's ten words, at `o` in the working space at `r12`. -/
scoped notation:max "sbase " s:max o:max => State.addr (State.gpr s Reg.r12) + BitVec.ofNat 64 o

/-- What a scan needs: the indices below 256; its ten words at `o` in the
working space at `r12`, writable and within the address space; and the
table, 4096 bytes at the static's address, readable, within the address
space and apart from those words. -/
structure ScanPre (sym : String) (o : Nat) (s : State) : Prop where
  idx : ∀ k < 4, (s.gpr (idxReg k)).toNat < 256
  cfit : (s.gpr .r12).toNat + o + 40 ≤ 2 ^ 32
  ofit : o + 40 ≤ 4096
  inS : ∀ {off w : Nat}, off + w ≤ 40 → InRegions s.wr (sbase s o + BitVec.ofNat 64 off) w
  tfit : (s.syms sym).toNat + 4096 ≤ 2 ^ 32
  trd : (⟨State.addr (s.syms sym), 4096⟩ : Region) ∈ s.rd ++ s.wr
  dTS : Region.Disjoint ⟨State.addr (s.syms sym), 4096⟩ ⟨sbase s o, 40⟩

theorem syms_mem (s : State) (m : Mem) : (putMem s m).syms = s.syms := rfl
theorem syms_sub (s : State) (x y : BitVec 32) : (putSub s x y).syms = s.syms := rfl

/-- The indices of a scan from `s`. -/
def ixs (s : State) (k : Nat) : Nat := (s.gpr (idxReg k)).toNat

/-- The address of a word of the table, as the rows of lookup `k` read it:
word `c` of row `r` of group `g` is word `k` of entry `8 (8 g + r) + c`. -/
theorem wordAddr_eq {T : BitVec 32} (hT : T.toNat + 4096 ≤ 2 ^ 32) {k g r c : Nat} (hk : k < 4) (hg : g < 4)
    (hr : r < 8) (hc : c < 8) :
    State.addr (T + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 (1024 * g) + BitVec.ofNat 32 (wordOff r c)) =
      State.addr T + BitVec.ofNat 64 (16 * (8 * (8 * g + r) + c) + 4 * k) := by
  unfold wordOff
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add, addr_add (by omega_arith)]
  exact congrArg (fun n => State.addr T + BitVec.ofNat 64 n) (by omega_arith)

/-- A slot read past a store to another. -/
theorem slot_rw (m : Mem) (D : Addr) {i j : Nat} (x : BitVec 32) (h : j + 4 ≤ i ∨ i + 4 ≤ j) (hi : i < 4096)
    (hj : j < 4096) :
    (m.writeW (D + BitVec.ofNat 64 i) x).readW (D + BitVec.ofNat 64 j) 32 = m.readW (D + BitVec.ofNat 64 j) 32 :=
  Mem.readW_writeW_sep (Offset.sep D (d := j) (n := 4) (e := i) (k := 4) h (by omega_arith) (by omega_arith))
    (by decide)

/-- A slot of the scan past the count of `rows`, at 20. -/
theorem scanSlot_frame {m m' : Mem} {D : Addr} (h : Frame [⟨D + BitVec.ofNat 64 20, 4⟩] m m') {i : Nat}
    (hi : i + 4 ≤ 20 ∨ 24 ≤ i) (hi' : i < 4096) :
    m'.readW (D + BitVec.ofNat 64 i) 32 = m.readW (D + BitVec.ofNat 64 i) 32 :=
  h.readW (r := ⟨D + BitVec.ofNat 64 i, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega_using [hi]) (by omega_arith) (by decide)) (by decide)

/-- The state of a scan of the table `sym` from `s` with `k` lookups made:
`r2`, `r3` and `lr` of `s`, the indices left, the count and the values in
their slots, and nothing else of memory written. -/
structure LookAt (s : State) (sym : String) (o k : Nat) (v : State) : Prop where
  r12 : v.gpr .r12 = s.gpr .r12
  fr : Frame [⟨sbase s o, 40⟩] s.mem v.mem
  s2 : v.mem.readW (sbase s o + BitVec.ofNat 64 0) 32 = s.gpr .r2
  s3 : v.mem.readW (sbase s o + BitVec.ofNat 64 4) 32 = s.gpr .r3
  slr : v.mem.readW (sbase s o + BitVec.ofNat 64 8) 32 = s.gpr .lr
  sx : v.mem.readW (sbase s o + BitVec.ofNat 64 12) 32 = BitVec.ofNat 32 (packN (ixs s) / 256 ^ k)
  sk : v.mem.readW (sbase s o + BitVec.ofNat 64 16) 32 = BitVec.ofNat 32 (4 * k)
  sv : ∀ j < k, v.mem.readW (sbase s o + BitVec.ofNat 64 (24 + 4 * j)) 32 =
    tw s.mem (s.syms sym) (ixs s (k - 1 - j)) (k - 1 - j)
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  sp : v.sp = s.sp
  syms : v.syms = s.syms

theorem count_step : ∀ k < 4, BitVec.ofNat 32 (4 * k) + 4 = BitVec.ofNat 32 (4 * (k + 1)) ∧
    (BitVec.ofNat 32 (4 * k) + 4 - 16 == 0) = decide (k + 1 = 4) := by decide

/-- The end of a lookup: the values moved up one slot, the lookup's value
`r1 - r3` in the first, and the count `c` of lookups, times four, on four. -/
theorem lookEnd_ok (p : State) {o : Nat} {D : Addr}
    (aS : ∀ off, off < 40 → State.addr (p.gpr .r12 + BitVec.ofNat 32 (o + off)) = D + BitVec.ofNat 64 off)
    (hoff : ∀ off, off < 40 → o + off < 4096)
    (inS : ∀ {off w : Nat}, off + w ≤ 40 → InRegions p.wr (D + BitVec.ofNat 64 off) w) {c : BitVec 32}
    (hc : p.mem.readW (D + BitVec.ofNat 64 16) 32 = c) :
    WP isa (.block (lookEnd o)) p fun w =>
      w.mem = ((((p.mem.writeW (D + BitVec.ofNat 64 36) (p.mem.readW (D + BitVec.ofNat 64 32) 32)).writeW
        (D + BitVec.ofNat 64 32) (p.mem.readW (D + BitVec.ofNat 64 28) 32)).writeW
        (D + BitVec.ofNat 64 28) (p.mem.readW (D + BitVec.ofNat 64 24) 32)).writeW
        (D + BitVec.ofNat 64 24) (p.gpr .r1 - p.gpr .r3)).writeW (D + BitVec.ofNat 64 16) (c + 4) ∧
      w.z = (c + 4 - 16 == 0) ∧ w.gpr .r12 = p.gpr .r12 ∧ w.rd = p.rd ∧ w.wr = p.wr ∧ w.sp = p.sp := by
  have inS' : ∀ {off w : Nat}, off + w ≤ 40 → InRegions (p.rd ++ p.wr) (D + BitVec.ofNat 64 off) w :=
    fun hw => by obtain ⟨g, hg, hc⟩ := inS hw; exact ⟨g, List.mem_append_right _ hg, hc⟩
  unfold lookEnd
  crun [aS, hoff, inS, inS', slot_rw, Mem.readW_writeW_self32, or_true, true_or, hc]

/-- A lookup: the value of the next index to the first of the values' slots. -/
theorem look_ok {s v : State} {sym : String} {o k : Nat} (hp : ScanPre sym o s) (hk : k < 4)
    (hv : LookAt s sym o k v) :
    WP isa (look sym o) v fun w => LookAt s sym o (k + 1) w ∧ w.z = decide (k + 1 = 4) := by
  have hcf := hp.cfit
  have hof := hp.ofit
  have hTf := hp.tfit
  have hix : ∀ j < 4, ixs s j < 256 := hp.idx
  obtain hpl := packN_lt hix
  obtain hxk : packN (ixs s) / 256 ^ k < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hpl
  obtain hxb : BitVec.ofNat 32 (packN (ixs s) / 256 ^ k) &&& 255 = s.gpr (idxReg k) :=
    BitVec.eq_of_toNat_eq (by rw [and255 hxk, packN_byte hix hk]; rfl)
  obtain hik := hix k hk
  obtain ⟨h, hh⟩ : ∃ h, ixs s k / 8 = h := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, ixs s k % 8 = l := ⟨_, rfl⟩
  obtain hh32 : h < 32 := by omega_using [hik, hh]
  obtain hl8 : l < 8 := by omega_using [hl]
  obtain hhl : 8 * h + l = ixs s k := by omega_using [hh, hl]
  -- The slots and the table.
  have hfr := hv.fr
  have s2 := hv.s2
  have s3 := hv.s3
  have slr := hv.slr
  have sx := hv.sx
  have sk := hv.sk
  have sv := hv.sv
  have dTS := hp.dTS
  have trd := hp.trd
  obtain ⟨D, hD⟩ : ∃ D, sbase s o = D := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, s.syms sym = T := ⟨_, rfl⟩
  rw [hD] at hfr s2 s3 slr sx sk sv dTS
  rw [hT] at hTf dTS trd sv
  have aS : ∀ off, off < 40 → State.addr (s.gpr .r12 + BitVec.ofNat 32 (o + off)) = D + BitVec.ofNat 64 off :=
    fun off ho => by rw [addr_add (by omega_arith), ← hD, Offset.add_add]
  have hoff : ∀ off, off < 40 → o + off < 4096 := fun off ho => by omega_arith
  have inS : ∀ {off w : Nat}, off + w ≤ 40 → InRegions s.wr (D + BitVec.ofNat 64 off) w :=
    fun hw => by rw [← hD]; exact hp.inS hw
  have inS' : ∀ {off w : Nat}, off + w ≤ 40 → InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 off) w :=
    fun hw => by obtain ⟨g, hg, hc⟩ := inS hw; exact ⟨g, List.mem_append_right _ hg, hc⟩
  -- A word of the table, in a memory that differs from `s.mem` in the slots.
  have tword (m : Mem) (hm : Frame [⟨D, 40⟩] s.mem m) (e : Nat) (he : e < 256) :
      m.readW (State.addr T + BitVec.ofNat 64 (16 * e + 4 * k)) 32 = tw s.mem T e k := by
    rw [hm.readW (r := ⟨State.addr T + BitVec.ofNat 64 (16 * e + 4 * k), 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dTS.sub_left (Offset.sub_base _ (by omega_arith))) (by decide), tw, addr_add (by omega_arith)]
  have hrd := hv.rd
  have hwr := hv.wr
  have v12 := hv.r12
  unfold look
  refine WP.seq ?_
  unfold lookStart
  rw [WP.block_append_iff, WP.block_append_iff]
  -- The index.
  have hA : WP isa (.block [.ldr .r0 .r12 (o + 12), .dp .and .r0 .r0 (.imm 255)]) v fun u =>
      u.gpr .r0 = s.gpr (idxReg k) ∧ (∀ q, q ≠ .r0 → u.gpr q = v.gpr q) ∧ u.mem = v.mem ∧ u.rd = v.rd ∧
      u.wr = v.wr ∧ u.sp = v.sp := by
    crun [v12, aS, hoff, inS', hrd, hwr, sx]
    exact ⟨hxb, fun q hq => by simp only [hq, ite_false]⟩
  refine VG.Arm.WP.mono_syms hA fun u ⟨u0, uo, um, urd, uwr, usp⟩ usy => ?_
  -- Its row's one-hot word, and the columns cleared.
  refine VG.Arm.WP.mono_syms (Scan.Arm.start_ok u (by rw [u0]; exact hik))
    fun t ⟨t2, t3, tc, to, tm, trd', twr, tsp⟩ tsy => ?_
  obtain t12 : t.gpr .r12 = s.gpr .r12 := (to _ (by decide)).trans ((uo _ (by decide)).trans v12)
  -- The table's pointer.
  have hB : WP isa (.block [.adrSym .lr sym, .ldr .r0 .r12 (o + 16), .dp .add .lr .lr (.reg .r0)]) t fun x =>
      x.gpr .lr = T + BitVec.ofNat 32 (4 * k) ∧ (∀ q, q ≠ .r0 → q ≠ .lr → x.gpr q = t.gpr q) ∧ x.mem = t.mem ∧
      x.rd = t.rd ∧ x.wr = t.wr ∧ x.sp = t.sp := by
    have hsy := hv.syms
    crun [exec_adrSym, t12, aS, hoff, inS', trd', twr, urd, uwr, hrd, hwr, tm, um, sk, tsy, usy, hsy, hT]
    exact fun q h0 hl' => by simp only [h0, hl', ite_false]
  refine VG.Arm.WP.mono_syms hB fun x ⟨xl, xo, xm, xrd, xwr, xsp⟩ xsy => ?_
  obtain x12 : x.gpr .r12 = s.gpr .r12 := (xo _ (by decide) (by decide)).trans t12
  -- The rows.
  obtain pre : Scan.Arm.RowsPre wordOff 1024 (o + 20) h (T + BitVec.ofNat 32 (4 * k)) x :=
    { hh := hh32
      r2 := by rw [xo _ (by decide) (by decide), t2, u0, ← hh]; rfl
      r3 := by rw [xo _ (by decide) (by decide), t3]
      lr := xl
      cols := fun c hc => by rw [xo _ (Scan.Arm.colReg_ne_r0 c) (Scan.Arm.colReg_ne_lr c), tc c hc]
      hcnt := hoff 20 (by decide)
      slot := by rw [x12, aS 20 (by decide), xwr, twr, uwr, hwr]; exact inS (by decide)
      hstride := by decide
      hoffs := fun r hr c hc => by unfold wordOff; omega_arith
      rd := fun g hg r hr c hc => by
        rw [wordAddr_eq hTf hk hg hr hc, xrd, trd', urd, hrd, xwr, twr, uwr, hwr]
        exact ⟨_, trd, Offset.contains_base (State.addr T) (n := 4) (k := 4096) (by omega_arith) (by omega_arith)⟩
      dis := fun g hg r hr c hc => by
        rw [wordAddr_eq hTf hk hg hr hc, x12, aS 20 (by decide)]
        exact (dTS.sub_left (Offset.sub_base _ (n := 4) (by omega_arith))).sub_right (Offset.sub_base _ (by decide)) }
  refine WP.seq (VG.Arm.WP.mono_syms (Scan.Arm.rows_ok pre) fun y ⟨yc, yo, yfr, yrd, ywr, ysp⟩ ysy => ?_)
  rw [x12, aS 20 (by decide), xm, tm, um] at yfr
  obtain y12 : y.gpr .r12 = s.gpr .r12 := (yo _ (by decide)).trans x12
  -- The words of the index's row.
  obtain ⟨W, hW⟩ : ∃ W : Nat → BitVec 32, W = fun c => tw s.mem T (8 * h + c) k := ⟨_, rfl⟩
  obtain ya : ∀ c < 8, y.gpr (colReg c) = Scan.Arm.val c (W c) := by
    intro c hc
    rw [yc c hc, hW, Scan.Arm.wordAt, wordAddr_eq hTf hk (by omega_using [hh32]) (by omega_arith) hc,
      show 16 * (8 * (8 * (h / 8) + h % 8) + c) + 4 * k = 16 * (8 * h + c) + 4 * k by omega_arith, xm, tm, um]
    exact congrArg _ (tword v.mem hfr _ (by omega_using [hh32, hc]))
  -- The slots after the rows.
  have ysl {i : Nat} (hi : i + 4 ≤ 20 ∨ 24 ≤ i) (hi' : i < 4096) :
      y.mem.readW (D + BitVec.ofNat 64 i) 32 = v.mem.readW (D + BitVec.ofNat 64 i) 32 := scanSlot_frame yfr hi hi'
  obtain yrd' : y.rd = s.rd := yrd.trans (xrd.trans (trd'.trans (urd.trans hrd)))
  obtain ywr' : y.wr = s.wr := ywr.trans (xwr.trans (twr.trans (uwr.trans hwr)))
  rw [List.append_assoc, WP.block_append_iff]
  -- The index's low three bits, and the indices left.
  have hP : WP isa (.block (pickStart o)) y fun z =>
      z.gpr .lr = BitVec.ofNat 32 l ∧ z.gpr .r1 = 0 ∧ z.gpr .r3 = 0 ∧
      (∀ q, q ≠ .r1 → q ≠ .r2 → q ≠ .r3 → q ≠ .lr → z.gpr q = y.gpr q) ∧
      z.mem = y.mem.writeW (D + BitVec.ofNat 64 12) (BitVec.ofNat 32 (packN (ixs s) / 256 ^ (k + 1))) ∧
      z.rd = y.rd ∧ z.wr = y.wr ∧ z.sp = y.sp := by
    have ysx := (ysl (i := 12) (by decide) (by decide)).trans sx
    unfold pickStart
    crun [y12, aS, hoff, inS, inS', yrd', ywr', ysx]
    refine ⟨?_, fun q h1 h2 h3 hl' => by simp only [h1, h2, h3, hl', ite_false], ?_⟩
    · rw [and7 hxk, ← hl, ← packN_byte hix hk, Nat.mod_mod_of_dvd _ (by decide)]
    · rw [shr8 hxk, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  refine VG.Arm.WP.mono_syms hP fun z ⟨zl, z1, z3, zo, zm, zrd, zwr, zsp⟩ zsy => ?_
  rw [WP.block_append_iff]
  -- The picks of the columns below `e`.
  have picks : ∀ e ≤ 8, WP isa (.block ((List.range e).flatMap pick)) z fun p =>
      p.gpr .r1 = pickR (fun c => Scan.Arm.val c (W c)) l e false ∧
      p.gpr .r3 = pickR (fun c => Scan.Arm.val c (W c)) l e true ∧
      (∀ q, q ≠ .r0 → q ≠ .r1 → q ≠ .r3 → p.gpr q = z.gpr q) ∧ p.mem = z.mem ∧ p.rd = z.rd ∧ p.wr = z.wr ∧
      p.sp = z.sp := by
    intro e he
    induction e with
    | zero =>
      exact WP.block_nil ⟨by rw [z1, pickR, ite_eq_right (fun h' => Nat.not_lt_zero _ h'.1)],
        by rw [z3, pickR, ite_eq_right (fun h' => Nat.not_lt_zero _ h'.1)], fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
    | succ e ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        WP.block_append_iff]
      refine WP.mono (ih (by omega_using [he])) fun p ⟨p1, p3, po, pm, prd, pwr, psp⟩ => ?_
      obtain he8 : e < 8 := by omega_using [he]
      refine WP.mono (pick_ok p (fun c => Scan.Arm.val c (W c)) hl8 he8
        (by rw [po _ (by decide) (by decide) (by decide), zl])
        (by rw [po _ (Scan.Arm.colReg_ne_r0 e) (Scan.Arm.colReg_ne_r1 e) (Scan.Arm.colReg_ne_r3 e),
          zo _ (Scan.Arm.colReg_ne_r1 e) (Scan.Arm.colReg_ne_r2 e) (Scan.Arm.colReg_ne_r3 e)
            (Scan.Arm.colReg_ne_lr e), ya e he8]) p1 p3)
        fun q ⟨q1, q3, qo, qm, qrd, qwr, qsp⟩ => ?_
      exact ⟨q1, q3, fun r h0 h1 h3 => (qo r h0 h1 h3).trans (po r h0 h1 h3), qm.trans pm, qrd.trans prd,
        qwr.trans pwr, qsp.trans psp⟩
  refine VG.Arm.WP.mono_syms (picks 8 (Nat.le_refl _)) fun p ⟨p1, p3, po, pm, prd, pwr, psp⟩ psy => ?_
  rw [zm] at pm
  obtain p12 : p.gpr .r12 = s.gpr .r12 :=
    (po _ (by decide) (by decide) (by decide)).trans ((zo _ (by decide) (by decide) (by decide) (by decide)).trans y12)
  obtain prd' : p.rd = s.rd := prd.trans (zrd.trans yrd')
  obtain pwr' : p.wr = s.wr := pwr.trans (zwr.trans ywr')
  obtain psp' : p.sp = s.sp := psp.trans (zsp.trans (ysp.trans (xsp.trans (tsp.trans (usp.trans hv.sp)))))
  obtain psy' : p.syms = s.syms := psy.trans (zsy.trans (ysy.trans (xsy.trans (tsy.trans (usy.trans hv.syms)))))
  -- The value, and the count.
  obtain res : p.gpr .r1 - p.gpr .r3 = tw s.mem T (ixs s k) k := by
    rw [p1, p3, pickR_res W hl8, hW]
    show tw s.mem T (8 * h + l) k = _
    rw [hhl]
  have y16 := (ysl (i := 16) (by decide) (by decide)).trans sk
  have y0 := (ysl (i := 0) (by decide) (by decide)).trans s2
  have y4 := (ysl (i := 4) (by decide) (by decide)).trans s3
  have y8 := (ysl (i := 8) (by decide) (by decide)).trans slr
  obtain ⟨c1, c2⟩ := count_step k hk
  obtain yf : Frame [⟨D, 40⟩] s.mem y.mem :=
    hfr.trans (yfr.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩)
  have aSp : ∀ off, off < 40 → State.addr (p.gpr .r12 + BitVec.ofNat 32 (o + off)) = D + BitVec.ofNat 64 off :=
    fun off ho => by rw [p12]; exact aS off ho
  -- The slots after the indices left are stored.
  have psl {i : Nat} (hi : i + 4 ≤ 12 ∨ 24 ≤ i) (hi' : i < 4096) :
      p.mem.readW (D + BitVec.ofNat 64 i) 32 = v.mem.readW (D + BitVec.ofNat 64 i) 32 := by
    rw [pm, slot_rw _ _ _ (by omega_using [hi]) (by decide) hi', ysl (by omega_using [hi]) hi']
  obtain p16 : p.mem.readW (D + BitVec.ofNat 64 16) 32 = BitVec.ofNat 32 (4 * k) := by
    rw [pm, slot_rw _ _ _ (by decide) (by decide) (by decide), ysl (by decide) (by decide), sk]
  refine VG.Arm.WP.mono_syms (lookEnd_ok p aSp hoff (fun hw => by rw [pwr']; exact inS hw) p16)
    fun w ⟨wm, wz, w12, wrd, wwr, wsp⟩ wsy => ?_
  rw [res, c1] at wm
  obtain pf : Frame [⟨D, 40⟩] s.mem p.mem := by
    rw [pm]; exact yf.writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  refine ⟨⟨w12.trans p12, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, wrd.trans prd', wwr.trans pwr', wsp.trans psp',
    wsy.trans psy'⟩, by rw [wz, c2]⟩
  all_goals rw [hD, wm]
  · exact ((((pf.writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  · simp (disch := decide) only [slot_rw]
    rw [psl (by decide) (by decide), s2]
  · simp (disch := decide) only [slot_rw]
    rw [psl (by decide) (by decide), s3]
  · simp (disch := decide) only [slot_rw]
    rw [psl (by decide) (by decide), slr]
  · simp (disch := decide) only [slot_rw]
    rw [pm, Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]
  · rw [hT]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega_using [hj, hk]) with rfl | rfl | rfl | rfl
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32, Nat.reduceMul, Nat.reduceAdd]
      rfl
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32, Nat.reduceMul, Nat.reduceAdd]
      rw [psl (by decide) (by decide), sv 0 (by omega_using [hj])]
      rw [show k + 1 - 1 - 1 = k - 1 - 0 by omega_arith]
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32, Nat.reduceMul, Nat.reduceAdd]
      rw [psl (by decide) (by decide), sv 1 (by omega_using [hj])]
      rw [show k + 1 - 1 - 2 = k - 1 - 1 by omega_arith]
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32, Nat.reduceMul, Nat.reduceAdd]
      rw [psl (by decide) (by decide), sv 2 (by omega_using [hj])]
      rw [show k + 1 - 1 - 3 = k - 1 - 2 by omega_arith]

/-- The scan: `r8 + k` is word `k` of the entry of the table whose number
is in `r4 + k`; only `r0`, `r1`, `r4`–`r11` and the scan's ten words are
written. -/
theorem scan_ok (s : State) (sym : String) (o : Nat) (h : ScanPre sym o s) :
    WP isa (scan sym o) s fun t =>
      (∀ k < 4, t.gpr (accReg k) = tw s.mem (s.syms sym) (s.gpr (idxReg k)).toNat k) ∧
      Keep [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s t ∧
      Frame [⟨sbase s o, 40⟩] s.mem t.mem := by
  have hcf := h.cfit
  have hof := h.ofit
  obtain ⟨D, hD⟩ : ∃ D, sbase s o = D := ⟨_, rfl⟩
  have aS : ∀ off, off < 40 → State.addr (s.gpr .r12 + BitVec.ofNat 32 (o + off)) = D + BitVec.ofNat 64 off :=
    fun off ho => by rw [addr_add (by omega_arith), ← hD, Offset.add_add]
  obtain a0 : State.addr (s.gpr .r12 + BitVec.ofNat 32 o) = D + BitVec.ofNat 64 0 := by
    rw [addr_add (by omega_arith), hD, BitVec.add_zero]
  have hoff : ∀ off, off < 40 → o + off < 4096 := fun off ho => by omega_arith
  obtain ho : o < 4096 := by omega_arith
  have inS : ∀ {off w : Nat}, off + w ≤ 40 → InRegions s.wr (D + BitVec.ofNat 64 off) w :=
    fun hw => by rw [← hD]; exact h.inS hw
  have inS' : ∀ {off w : Nat}, off + w ≤ 40 → InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 off) w :=
    fun hw => by obtain ⟨g, hg, hc⟩ := inS hw; exact ⟨g, List.mem_append_right _ hg, hc⟩
  unfold scan
  -- `r2`, `r3`, `lr` and the indices to their slots.
  have hS : WP isa (.block (scanStart o)) s fun u =>
      u.mem = ((((s.mem.writeW (D + BitVec.ofNat 64 0) (s.gpr .r2)).writeW (D + BitVec.ofNat 64 4) (s.gpr .r3)).writeW
        (D + BitVec.ofNat 64 8) (s.gpr .lr)).writeW (D + BitVec.ofNat 64 12)
        (s.gpr .r4 + s.gpr .r5 <<< 8 + s.gpr .r6 <<< 16 + s.gpr .r7 <<< 24)).writeW (D + BitVec.ofNat 64 16)
        (0 : BitVec 32) ∧
      u.gpr .r12 = s.gpr .r12 ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
    unfold scanStart
    crun [a0, aS, hoff, ho, inS]
  refine WP.seq (VG.Arm.WP.mono_syms hS fun u ⟨um, u12, urd, uwr, usp⟩ usy => ?_)
  obtain h₀ : LookAt s sym o 0 u := by
    refine ⟨u12, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero j), urd, uwr, usp, usy⟩
    all_goals rw [hD, um]
    · exact (((((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32]
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32]
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32]
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32]
      rw [pack_eq, Nat.pow_zero, Nat.div_one]
      rfl
    · rw [Mem.readW_writeW_self32]
      rfl
  -- The lookups.
  have loop : WP isa (.loop (look sym o) .ne) u (LookAt s sym o 4) := by
    refine WP.loop (M := isa) (fun n (v : State) => ∃ k, n = 4 - k ∧ k < 4 ∧ LookAt s sym o k v) ?_ 4 u
      ⟨0, rfl, by decide, h₀⟩
    rintro n v ⟨k, rfl, hk, hv⟩
    refine WP.mono (look_ok h hk hv) fun w ⟨hw, wz⟩ => ?_
    by_cases he : k + 1 = 4
    · exact .inl ⟨by show some (!w.z) = _; rw [wz, decide_eq_true he]; rfl, he ▸ hw⟩
    · exact .inr ⟨by show some (!w.z) = _; rw [wz, decide_eq_false he]; rfl, 4 - (k + 1), by omega_using [hk], k + 1,
        rfl, by omega_using [hk, he], hw⟩
  refine WP.seq (WP.mono loop fun v hv => ?_)
  -- The values, and `r2`, `r3` and `lr` back.
  have s2 := hv.s2
  have s3 := hv.s3
  have slr := hv.slr
  have r36 := hv.sv 3 (by decide)
  have r32 := hv.sv 2 (by decide)
  have r28 := hv.sv 1 (by decide)
  have r24 := hv.sv 0 (by decide)
  have hfr := hv.fr
  rw [hD] at s2 s3 slr r36 r32 r28 r24
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at r36 r32 r28 r24
  have v12 := hv.r12
  have hrd := hv.rd
  have hwr := hv.wr
  have hE : WP isa (.block (scanEnd o)) v fun t =>
      t.gpr .r8 = tw s.mem (s.syms sym) (ixs s 0) 0 ∧ t.gpr .r9 = tw s.mem (s.syms sym) (ixs s 1) 1 ∧
      t.gpr .r10 = tw s.mem (s.syms sym) (ixs s 2) 2 ∧ t.gpr .r11 = tw s.mem (s.syms sym) (ixs s 3) 3 ∧
      t.gpr .r2 = s.gpr .r2 ∧ t.gpr .r3 = s.gpr .r3 ∧ t.gpr .lr = s.gpr .lr ∧ t.gpr .r12 = s.gpr .r12 ∧
      t.mem = v.mem ∧ t.rd = v.rd ∧ t.wr = v.wr ∧ t.sp = v.sp := by
    unfold scanEnd
    crun [v12, a0, aS, hoff, ho, inS', hrd, hwr, s2, s3, slr, r36, r32, r28, r24]
  refine WP.mono hE fun t ⟨t8, t9, t10, t11, t2, t3, tlr, t12, tm, trd, twr, tsp⟩ => ?_
  refine ⟨fun k hk => ?_, ⟨fun r hr => ?_, trd.trans hrd, twr.trans hwr, tsp.trans hv.sp⟩, by rw [tm]; exact hfr⟩
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl
    · exact t8
    · exact t9
    · exact t10
    · exact t11
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hr
    cases r
    case r2 => exact t2
    case r3 => exact t3
    case r12 => exact t12
    case lr => exact tlr
    all_goals first
      | exact absurd rfl h0
      | exact absurd rfl h1
      | exact absurd rfl h4
      | exact absurd rfl h5
      | exact absurd rfl h6
      | exact absurd rfl h7
      | exact absurd rfl h8
      | exact absurd rfl h9
      | exact absurd rfl h10
      | exact absurd rfl h11

end VG.Proof.Cast5.Arm

end

end

/-!
# CAST5 on ARMv7: a round

`round up` computes `I` (`byType mix`, `rotate`), spreads its bytes over
`r4`–`r7` (`spread`), scans `VG_CAST5_S1234` and combines the four values into `f`
(`byType comb`), makes the Feistel step (`feistel`), and moves the type and
the count of rounds left on (`next`).
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm
open VG.Impl.Cast5 (s1234Sym)

/-! ## Choosing by the type -/

/-- The address of the slot at `off` of the working space at `r12`. -/
scoped notation:max "slot " s:max off:max => State.addr (State.gpr s Reg.r12 + BitVec.ofNat 32 off)

theorem byType_ok (s : State) (f : Nat → List Instr) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3)
    (hin : InRegions (s.rd ++ s.wr) (slot s 20) 4) (hv : s.mem.readW (slot s 20) 32 = BitVec.ofNat 32 t)
    {Q : State → Prop} (hQ : ∀ u, Keep [.r0] s u → u.mem = s.mem → WP isa (.block (f t)) u Q) :
    WP isa (byType f) s Q := by
  unfold byType
  refine WP.seq ?_
  crun [typeOff, hin, hv]
  rcases ht with rfl | rfl | rfl
  · refine WP.ite true rfl (fun _ => hQ _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ rfl)
      (fun h => absurd h (by decide))
    simp only [List.mem_singleton] at hr
    simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ hr
  · refine WP.ite false rfl (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq ?_
    crun
    refine WP.ite true rfl (fun _ => hQ _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ rfl)
      (fun h => absurd h (by decide))
    simp only [List.mem_singleton] at hr
    simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ hr
  · refine WP.ite false rfl (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq ?_
    crun
    refine WP.ite false rfl (fun h => absurd h (by decide)) (fun _ =>
      hQ _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ rfl)
    simp only [List.mem_singleton] at hr
    simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ hr

/-! ## The pieces of a round -/

theorem mix_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {km d : Spec.Cast5.Word}
    (h3 : s.gpr .r3 = d) (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 4)
    (hv : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 32 = km) :
    WP isa (.block (Impl.Cast5.Arm.mix t)) s fun u => u.gpr .r1 = Proof.Cast5.mix t km d ∧ Keep [.r1] s u ∧ u.mem = s.mem := by
  rcases ht with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.Arm.mix
    crun [hin, hv, h3]
    exact ⟨rfl, ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩⟩

theorem rotateStep_ok (s : State) {b : Nat} (hb : b < 5) {a kb : BitVec 32}
    (h1 : s.gpr .r1 = a) (h0 : s.gpr .r0 = kb) :
    WP isa (.block (rotateStep b)) s fun u =>
      u.gpr .r1 = Proof.Cast5.step a kb b ∧ u.gpr .r0 = (if b < 4 then kb >>> 1 else kb) ∧
      Keep [.r0, .r1, .r4, .r5] s u ∧ u.mem = s.mem := by
  have hn : 1 ≤ 32 - 2 ^ b ∧ 32 - 2 ^ b ≤ 31 := by
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega_using [hb]) with h | h | h | h | h <;>
      subst h <;> decide
  unfold rotateStep
  by_cases h4 : b < 4
  · rw [ite_eq_left h4]
    crun [h1, h0, hn]
    exact ⟨rfl, by rw [ite_eq_left h4], ⟨by keep_regs, rfl, rfl, rfl⟩⟩
  · rw [ite_eq_right h4]
    crun [h1, h0, hn]
    exact ⟨rfl, by rw [ite_eq_right h4], ⟨by keep_regs, rfl, rfl, rfl⟩⟩

theorem rotate_ok (s : State) {a kr : BitVec 32} (h1 : s.gpr .r1 = a)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 4)
    (hv : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 32 = kr) :
    WP isa (.block rotate) s fun u =>
      u.gpr .r1 = a.rotateLeft (kr.toNat % 32) ∧ Keep [.r0, .r1, .r4, .r5] s u ∧ u.mem = s.mem := by
  have e : rotate = [.ldr .r0 .lr 64] ++ rotateStep 0 ++ rotateStep 1 ++ rotateStep 2 ++ rotateStep 3 ++
      rotateStep 4 := rfl
  rw [e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  have k0 : WP isa (.block [.ldr .r0 .lr 64]) s fun u =>
      u.gpr .r0 = kr ∧ u.gpr .r1 = a ∧ Keep [.r0, .r1, .r4, .r5] s u ∧ u.mem = s.mem := by
    crun [hin, hv, h1]
    exact ⟨fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp only [gpr_setReg, hr.1, ite_false],
      rfl, rfl, rfl⟩
  refine WP.mono k0 fun t₀ ⟨k₀, a₀, p₀, m₀⟩ => ?_
  refine WP.mono (rotateStep_ok t₀ (by decide) a₀ k₀) fun t₁ ⟨a₁, k₁, p₁, m₁⟩ => ?_
  rw [ite_eq_left (by decide)] at k₁
  refine WP.mono (rotateStep_ok t₁ (by decide) a₁ k₁) fun t₂ ⟨a₂, k₂, p₂, m₂⟩ => ?_
  rw [ite_eq_left (by decide)] at k₂
  refine WP.mono (rotateStep_ok t₂ (by decide) a₂ k₂) fun t₃ ⟨a₃, k₃, p₃, m₃⟩ => ?_
  rw [ite_eq_left (by decide)] at k₃
  refine WP.mono (rotateStep_ok t₃ (by decide) a₃ k₃) fun t₄ ⟨a₄, k₄, p₄, m₄⟩ => ?_
  rw [ite_eq_left (by decide)] at k₄
  refine WP.mono (rotateStep_ok t₄ (by decide) a₄ k₄) fun t₅ ⟨a₅, _, p₅, m₅⟩ => ?_
  refine ⟨?_, p₀.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))), by rw [m₅, m₄, m₃, m₂, m₁, m₀]⟩
  rw [a₅, Proof.Cast5.steps_eq]

/-- Index `k` of a scan of `I`: byte `k` of `I` (from the least significant). -/
def idx (i : BitVec 32) : Nat → BitVec 32
  | 0 => i &&& 255
  | 1 => i >>> 8 &&& 255
  | 2 => i >>> 16 &&& 255
  | _ => i >>> 24

theorem idx_toNat (i : BitVec 32) {k : Nat} (hk : k < 4) :
    (idx i k).toNat = i.toNat / 2 ^ (8 * k) % 256 := by
  have := i.isLt
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
    simp only [idx, BitVec.toNat_ushiftRight, BitVec.toNat_and, Nat.shiftRight_eq_div_pow,
      show (255 : BitVec 32).toNat = 255 from rfl, show (255 : Nat) = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] <;> omega_using []

theorem idx_lt (i : BitVec 32) {k : Nat} (hk : k < 4) : (idx i k).toNat < 256 := by
  rw [idx_toNat i hk]; omega_using []

theorem idx_byte (i : BitVec 32) {k : Nat} (hk : k < 4) :
    BitVec.ofNat 8 (idx i k).toNat = Spec.Cast5.byte i (3 - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, idx_toNat i hk]
  simp only [Spec.Cast5.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;> omega_using []

theorem spread_ok (s : State) {i : BitVec 32} (h1 : s.gpr .r1 = i) :
    WP isa (.block spread) s fun u =>
      (∀ k < 4, u.gpr (idxReg k) = idx i k) ∧ Keep [.r4, .r5, .r6, .r7] s u ∧ u.mem = s.mem := by
  unfold spread
  crun [h1]
  refine ⟨fun k hk => ?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩⟩
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem comb_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) :
    WP isa (.block (Impl.Cast5.Arm.comb t)) s fun u =>
      u.gpr .r1 = Proof.Cast5.comb t (s.gpr .r11) (s.gpr .r10) (s.gpr .r9) (s.gpr .r8) ∧ Keep [.r1] s u ∧
        u.mem = s.mem := by
  rcases ht with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.Arm.comb
    crun
    exact ⟨rfl, ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩⟩

theorem feistel_ok (s : State) (up : Bool) :
    WP isa (.block (feistel up)) s fun u =>
      u.gpr .r2 = s.gpr .r3 ∧ u.gpr .r3 = s.gpr .r1 ^^^ s.gpr .r2 ∧
      u.gpr .lr = (if up then s.gpr .lr + 4 else s.gpr .lr - 4) ∧ Keep [.r1, .r2, .r3, .lr] s u ∧
      u.mem = s.mem := by
  cases up <;>
  · unfold feistel
    crun
    exact ⟨by keep_regs, rfl, rfl, rfl⟩

/-- The type after `t`. -/
def nextT (up : Bool) (t : Nat) : Nat :=
  if up then (if t = 3 then 1 else t + 1) else (if t = 1 then 3 else t - 1)

/-- The type `v` (in `r0`) to its slot, then the count of rounds left down. -/
theorem nextTail_ok (s : State) {v cnt : BitVec 32} (h0 : s.gpr .r0 = v)
    (hinT : InRegions s.wr (slot s 20) 4)
    (hinC : InRegions s.wr (slot s 16) 4) (hvC : (s.mem.writeW (slot s 20) v).readW (slot s 16) 32 = cnt) :
    WP isa (.block [.str .r0 .r12 typeOff, .ldr .r0 .r12 cntOff, .subs .r0 .r0 (.imm 1), .str .r0 .r12 cntOff]) s
      fun u => u.mem = (s.mem.writeW (slot s 20) v).writeW (slot s 16) (cnt - 1) ∧ u.z = (cnt - 1 == 0) ∧
        Keep [.r0] s u := by
  have hinC' : InRegions (s.rd ++ s.wr) (slot s 16) 4 := by
    obtain ⟨g, hg, hc⟩ := hinC; exact ⟨g, List.mem_append_right _ hg, hc⟩
  crun [typeOff, cntOff, h0, hinT, hinC, hinC', hvC]
  exact ⟨by keep_regs, rfl, rfl, rfl⟩

theorem next_ok (s : State) (up : Bool) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {cnt : BitVec 32}
    (hinT : InRegions s.wr (slot s 20) 4) (hvT : s.mem.readW (slot s 20) 32 = BitVec.ofNat 32 t)
    (hinC : InRegions s.wr (slot s 16) 4) (hvC : s.mem.readW (slot s 16) 32 = cnt)
    (hsep : Mem.Sep (slot s 16) 4 (slot s 20) 4) :
    WP isa (next up) s fun u =>
      u.mem = (s.mem.writeW (slot s 20) (BitVec.ofNat 32 (nextT up t))).writeW (slot s 16) (cnt - 1) ∧
      u.z = (cnt - 1 == 0) ∧ Keep [.r0] s u := by
  have hinT' : InRegions (s.rd ++ s.wr) (slot s 20) 4 := by
    obtain ⟨g, hg, hc⟩ := hinT; exact ⟨g, List.mem_append_right _ hg, hc⟩
  have hvC' (v : BitVec 32) : (s.mem.writeW (slot s 20) v).readW (slot s 16) 32 = cnt := by
    rw [Mem.readW_writeW_sep hsep (by decide), hvC]
  -- The rest, from the state after the branch, which wrote only `r0` and the flags.
  have tail : ∀ u : State, Keep [.r0] s u → u.mem = s.mem → u.gpr .r0 = BitVec.ofNat 32 (nextT up t) →
      WP isa (.block [.str .r0 .r12 typeOff, .ldr .r0 .r12 cntOff, .subs .r0 .r0 (.imm 1),
        .str .r0 .r12 cntOff]) u fun w =>
      w.mem = (s.mem.writeW (slot s 20) (BitVec.ofNat 32 (nextT up t))).writeW (slot s 16) (cnt - 1) ∧
      w.z = (cnt - 1 == 0) ∧ Keep [.r0] s w := by
    intro u uk um u0
    have e12 : u.gpr .r12 = s.gpr .r12 := uk.gpr _ (by decide)
    have es (off : Nat) : slot u off = slot s off := by rw [e12]
    refine WP.mono (nextTail_ok u u0 (by rw [es, uk.wr]; exact hinT) (by rw [es, uk.wr]; exact hinC)
      (by rw [es, es, um]; exact hvC' _)) fun w ⟨wm, wz, wk⟩ => ⟨by rw [wm, es, es, um], wz, uk.trans wk⟩
  unfold next
  cases up <;> rcases ht with rfl | rfl | rfl
  all_goals
    refine WP.seq ?_
    crun [typeOff, hinT', hvT]
  all_goals
    refine WP.seq (wp_ite_eq (fun h => ?_) (fun h => ?_))
  all_goals first
    | exact absurd (h.symm.trans (z_sub _ _ _)) (by decide)
    | refine WP.mono (Q := fun u : State => Keep [.r0] s u ∧ u.mem = s.mem ∧
          u.gpr .r0 = BitVec.ofNat 32 (nextT _ _)) ?_ fun u ⟨a, b, c⟩ => tail u a b c
      crun
      exact ⟨⟨by keep_regs, rfl, rfl, rfl⟩, by decide⟩

/-! ## The round -/

/-- `f` of a round of type `t` with the subkeys `km`, `kr`, on `D = d`. -/
def fT (t : Nat) (km kr d : Spec.Cast5.Word) : Spec.Cast5.Word :=
  let i := (Proof.Cast5.mix t km d).rotateLeft (kr.toNat % 32)
  Proof.Cast5.comb t (Spec.Cast5.S1 (Spec.Cast5.byte i 0)) (Spec.Cast5.S2 (Spec.Cast5.byte i 1))
    (Spec.Cast5.S3 (Spec.Cast5.byte i 2)) (Spec.Cast5.S4 (Spec.Cast5.byte i 3))

/-- What a round needs: `(L, R)` in `(r2, r3)`; `Kmᵢ` at `lr` and `Krᵢ` at
`lr + 64`; the type `t` and the count `cnt` of rounds left in their slots;
the scan's slots writable; and the table `VG_CAST5_S1234`, readable and
apart from them. -/
structure RoundPre (s : State) (km kr l r : Spec.Cast5.Word) (t : Nat) (cnt : BitVec 32) : Prop where
  r2 : s.gpr .r2 = l
  r3 : s.gpr .r3 = r
  inM : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 4
  valM : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 32 = km
  inR : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 4
  valR : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 32 = kr
  ht : t = 1 ∨ t = 2 ∨ t = 3
  inT : InRegions s.wr (slot s 20) 4
  valT : s.mem.readW (slot s 20) 32 = BitVec.ofNat 32 t
  inC : InRegions s.wr (slot s 16) 4
  valC : s.mem.readW (slot s 16) 32 = cnt
  sep : Mem.Sep (slot s 16) 4 (slot s 20) 4
  cfit : (s.gpr .r12).toNat + 64 ≤ 2 ^ 32
  inS : ∀ {off w : Nat}, off + w ≤ 40 → InRegions s.wr (sbase s 24 + BitVec.ofNat 64 off) w
  tfit : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  trd : (⟨State.addr (s.syms s1234Sym), 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (State.addr (s.syms s1234Sym)) Impl.Cast5.s1234
  dTS : Region.Disjoint ⟨State.addr (s.syms s1234Sym), 4096⟩ ⟨sbase s 24, 40⟩

theorem RoundPre.inT' {s : State} {km kr l r : Spec.Cast5.Word} {t : Nat} {cnt : BitVec 32}
    (h : RoundPre s km kr l r t cnt) : InRegions (s.rd ++ s.wr) (slot s 20) 4 := by
  obtain ⟨g, hg, hc⟩ := h.inT; exact ⟨g, List.mem_append_right _ hg, hc⟩

/-- The registers a round writes before its Feistel step. -/
def preRegs : List Reg := [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- The registers a round writes. -/
def roundRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

/-- The slots of the working space, as the scan addresses them. -/
theorem slot_addr {s : State} (hc : (s.gpr .r12).toNat + 64 ≤ 2 ^ 32) {off : Nat} (ho : off < 64) :
    slot s off = State.addr (s.gpr .r12) + BitVec.ofNat 64 off := addr_add (by omega_using [hc, ho])

/-- A slot below the scan's, in a memory that differs in the scan's words. -/
theorem frame_slot (s : State) {m m' : Mem} (hf : Frame [⟨sbase s 24, 40⟩] m m')
    (hc : (s.gpr .r12).toNat + 64 ≤ 2 ^ 32) {off : Nat} (ho : off + 4 ≤ 24) :
    m'.readW (slot s off) 32 = m.readW (slot s off) 32 := by
  rw [slot_addr hc (by omega_using [ho])]
  exact hf.readW (r := ⟨State.addr (s.gpr .r12) + BitVec.ofNat 64 off, 4⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl ho) (by omega_using [ho]) (by decide)) (by decide)

theorem round_ok (s : State) (up : Bool) {km kr l r : Spec.Cast5.Word} {t : Nat} {cnt : BitVec 32}
    (h : RoundPre s km kr l r t cnt) :
    WP isa (round up) s fun u =>
      u.gpr .r2 = r ∧ u.gpr .r3 = l ^^^ fT t km kr r ∧
      u.gpr .lr = (if up then s.gpr .lr + 4 else s.gpr .lr - 4) ∧
      (∃ m, Frame [⟨sbase s 24, 40⟩] s.mem m ∧
        u.mem = (m.writeW (slot s 20) (BitVec.ofNat 32 (nextT up t))).writeW (slot s 16) (cnt - 1)) ∧
      u.z = (cnt - 1 == 0) ∧ Keep roundRegs s u := by
  have ht := h.ht
  unfold round
  -- `I` before the rotation.
  refine WP.seq (VG.Arm.WP.mono_syms (byType_ok s Impl.Cast5.Arm.mix (Q := fun v => v.gpr .r1 = Proof.Cast5.mix t km r ∧
      Keep [.r0, .r1] s v ∧ v.mem = s.mem) ht h.inT' h.valT fun u uk um => ?_) fun v hv vsy => ?_)
  · have g (q : Reg) (hq : q ≠ .r0) : u.gpr q = s.gpr q := uk.gpr q (by simpa using hq)
    exact WP.mono (mix_ok u ht (by rw [g _ (by decide)]; exact h.r3)
      (by rw [uk.rd, uk.wr, g _ (by decide)]; exact h.inM) (by rw [um, g _ (by decide)]; exact h.valM))
      fun v ⟨v1, vk, vm⟩ => ⟨v1, (uk.mono (by decide)).trans (vk.mono (by decide)), vm.trans um⟩
  obtain ⟨v1, vk, vm⟩ := hv
  have gv (q : Reg) (hq : q ∉ [Reg.r0, .r1]) : v.gpr q = s.gpr q := vk.gpr q hq
  -- The rotation, the indices and the scan.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine (VG.Arm.WP.mono_syms (rotate_ok v v1 (kr := kr) (by rw [vk.rd, vk.wr, gv _ (by decide)]; exact h.inR)
    (by rw [vm, gv _ (by decide)]; exact h.valR)) fun w ⟨w1, wk, wm⟩ wsy => ?_)
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32) = i := ⟨_, rfl⟩
  rw [hi] at w1
  refine VG.Arm.WP.mono_syms (spread_ok w w1) fun x ⟨xi, xk, xm⟩ xsy => ?_
  have kx := (vk.mono (by decide)).trans ((wk.mono (by decide)).trans
    (xk.mono (show ∀ q ∈ [Reg.r4, .r5, .r6, .r7], q ∈ preRegs by decide)))
  have mx : x.mem = s.mem := xm.trans (wm.trans vm)
  have sx : x.syms = s.syms := xsy.trans (wsy.trans vsy)
  have r12x : x.gpr .r12 = s.gpr .r12 := kx.gpr _ (by decide)
  have sp : ScanPre s1234Sym spillEcb x :=
    { idx := fun k hk => by rw [xi k hk]; exact idx_lt i hk
      cfit := by rw [r12x]; have := h.cfit; unfold spillEcb; omega_using [this]
      ofit := by decide
      inS := fun hw => by rw [r12x, kx.wr]; exact h.inS hw
      tfit := by rw [sx]; exact h.tfit
      trd := by rw [sx, kx.rd, kx.wr]; exact h.trd
      dTS := by rw [sx, r12x]; exact h.dTS }
  refine WP.seq (WP.mono (scan_ok x s1234Sym spillEcb sp) fun y ⟨ya, yk, yf⟩ => ?_)
  have kxy := kx.trans (yk.mono (show ∀ r ∈ [Reg.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11], r ∈ preRegs by decide))
  rw [r12x, mx] at yf
  obtain yf : Frame [⟨sbase s 24, 40⟩] s.mem y.mem := yf
  have r12y : y.gpr .r12 = s.gpr .r12 := kxy.gpr _ (by decide)
  have esl (off : Nat) : slot y off = slot s off := by rw [r12y]
  have valT : y.mem.readW (slot y 20) 32 = BitVec.ofNat 32 t := by
    rw [esl, frame_slot s yf h.cfit (by decide)]; exact h.valT
  -- `f`.
  refine WP.seq (WP.mono (byType_ok y Impl.Cast5.Arm.comb (Q := fun z => z.gpr .r1 = fT t km kr r ∧
      Keep preRegs s z ∧ z.mem = y.mem) ht (by rw [kxy.rd, kxy.wr, r12y]; exact h.inT')
      valT fun u uk um => ?_) fun z hz => ?_)
  · have g (q : Reg) (hq : q ≠ .r0) : u.gpr q = y.gpr q := uk.gpr q (by simpa using hq)
    refine WP.mono (comb_ok u ht) fun z ⟨z1, zk, zm⟩ => ⟨?_, kxy.trans ((uk.mono (by decide)).trans
      (zk.mono (by decide))), zm.trans um⟩
    have hT := h.tfit
    have ent (k : Nat) (hk : k < 4) : y.gpr (accReg k) = tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2
        Spec.Cast5.S1 (idx i k).toNat k := by
      rw [ya k hk, mx, xi k hk, sx]; exact tw_table hT h.held (idx_lt i hk) hk
    have a0 : y.gpr .r8 = _ := ent 0 (by decide)
    have a1 : y.gpr .r9 = _ := ent 1 (by decide)
    have a2 : y.gpr .r10 = _ := ent 2 (by decide)
    have a3 : y.gpr .r11 = _ := ent 3 (by decide)
    rw [z1, g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide), a0, a1, a2, a3]
    unfold fT
    rw [hi]
    simp only [tableEnt, idx_byte i (show 0 < 4 by decide), idx_byte i (show 1 < 4 by decide),
      idx_byte i (show 2 < 4 by decide), idx_byte i (show 3 < 4 by decide)]
  obtain ⟨z1, zk, zm⟩ := hz
  have gz (q : Reg) (hq : q ∉ preRegs) : z.gpr q = s.gpr q := zk.gpr q hq
  -- The Feistel step, then the type and the count.
  refine WP.seq (WP.mono (feistel_ok z up) fun a ⟨a2, a3, alr, ak, am⟩ => ?_)
  have ka := (zk.mono (show ∀ q ∈ preRegs, q ∈ roundRegs by decide)).trans
    (ak.mono (show ∀ q ∈ [Reg.r1, .r2, .r3, .lr], q ∈ roundRegs by decide))
  have r12a : a.gpr .r12 = s.gpr .r12 := ka.gpr _ (by decide)
  have es (off : Nat) : slot a off = slot s off := by rw [r12a]
  have ma : a.mem = y.mem := am.trans zm
  have hinT := h.inT
  have hinC := h.inC
  refine WP.mono (next_ok a up ht (cnt := cnt) (by rw [es, ka.wr]; exact h.inT)
    (by rw [es, ma, frame_slot s yf h.cfit (by decide)]; exact h.valT)
    (by rw [es, ka.wr]; exact h.inC) (by rw [es, ma, frame_slot s yf h.cfit (by decide)]; exact h.valC)
    (by rw [es, es]; exact h.sep))
    fun b ⟨bm, bz, bk⟩ => ?_
  have gb (q : Reg) (hq : q ≠ .r0) : b.gpr q = a.gpr q := bk.gpr q (by simpa using hq)
  refine ⟨by rw [gb _ (by decide), a2, gz _ (by decide), h.r3], ?_, ?_, ⟨y.mem, yf, by rw [bm, es, es, ma]⟩, bz,
    ka.trans (bk.mono (by decide))⟩
  · rw [gb _ (by decide), a3, z1, gz _ (by decide), h.r2, BitVec.xor_comm]
  · rw [gb _ (by decide), alr, gz _ (by decide)]

end VG.Proof.Cast5.Arm
