module

import VerifiedGarbage.Proof.Blowfish.Blocks
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Impl.Blowfish.Arm
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Blowfish.Feistel
public import VerifiedGarbage.Proof.Blowfish.Arm.Run
public import VerifiedGarbage.Proof.Blowfish.Scan32
public import VerifiedGarbage.Proof.Blowfish.F
public import VerifiedGarbage.Proof.Scan.Arm

/-! ### `Blowfish.Arm.Cipher`, which this module and modules that import it used -/

section

/-! ### `Blowfish.Arm.F`, which only this module used -/

section

/-!
# Blowfish on ARMv7: F

`f_run`: F of xL (`r1`) into `lr`, one S-box at a time (`look_run`, `fAcc`).
A lookup reads the S-box's planes as 32 rows of eight words
(`Proof/Scan/Arm.lean`) and takes the entry from the words of the index's
row (`extract_run`, `exVal_eq`). The schedule, the halves, the working space
and the pointer into the P-array are restored from F's words of the working
space, which are all of memory it writes.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Impl.Scan.Arm (colReg rows)

/-- F's words of the working space at `r3`. -/
abbrev fRegion (s : State) : Region := ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 48, 32⟩

/-- What F needs: the schedule at `r0` readable, without wrapping around;
and F's words of the working space at `r3` writable, within the address
space and apart from the schedule. -/
structure LookEnv (s : State) : Prop where
  fit : (s.gpr .r0).toNat + 4168 ≤ 2 ^ 32
  rd : ∀ o, o + 4 ≤ 4168 → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0) + BitVec.ofNat 64 o) 4
  fitW : (s.gpr .r3).toNat + 80 ≤ 2 ^ 32
  wr : ∀ o, o + 4 ≤ 32 → InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 48 + BitVec.ofNat 64 o) 4
  sep : Region.Disjoint ⟨State.addr (s.gpr .r0), 4168⟩ (fRegion s)

/-- The registers F writes. -/
def fRegs : List Reg := [.lr, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem LookEnv.keep {s t : State} (E : LookEnv s) {rs : List Reg} (h : Keep rs s t)
    (h0 : Reg.r0 ∉ rs) (h3 : Reg.r3 ∉ rs) : LookEnv t := by
  refine ⟨by rw [h.gpr h0]; exact E.fit, fun o ho => ?_, by rw [h.gpr h3]; exact E.fitW, fun o ho => ?_, ?_⟩
  · rw [h.gpr h0, h.2.1, h.2.2.1]; exact E.rd o ho
  · rw [h.gpr h3, h.2.2.1]; exact E.wr o ho
  · rw [fRegion, h.gpr h0, h.gpr h3]; exact E.sep

/-! ## The index -/

/-- The index of lookup `j`: the top byte of xL shifted left by `8 j`. -/
theorem index_shift (x : BitVec 32) {j : Nat} (hj : j < 4) :
    (x <<< (8 * j)) >>> 24 = (quarter x j).setWidth 32 := by
  unfold quarter
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · rw [decide_eq_true h8, decide_eq_true (show 24 + i < 32 by omega_using [h8]),
      decide_eq_false (show ¬ 24 + i < 8 * j by omega_using [hj]), Bool.not_false, Bool.true_and, Bool.true_and,
      Bool.true_and, show 24 + i - 8 * j = 8 * (3 - j) + i by omega_using [hj]]
  · simp only [decide_eq_false h8, decide_eq_false (show ¬ 24 + i < 32 by omega_using [h8]), Bool.false_and]

/-! ## The entry, from the words of the index's row -/

/-- `selBits` for the index `32 a + b`: the 256 indices, as two ranges that
`decide` evaluates. -/
theorem selBits_split : ∀ a < 8, ∀ b < 32,
    ((1 : BitVec 32) &&& ~~~(BitVec.ofNat 32 (32 * a + b) >>> 2)) = (if (32 * a + b) / 4 % 2 = 0 then 1 else 0) ∧
    ((1 : BitVec 32) &&& BitVec.ofNat 32 (32 * a + b) >>> 2) = (if (32 * a + b) / 4 % 2 = 0 then 0 else 1) := by
  decide

/-- The selectors of a row's two words of a plane, from the index's bit 2. -/
theorem selBits : ∀ n < 256,
    ((1 : BitVec 32) &&& ~~~(BitVec.ofNat 32 n >>> 2)) = (if n / 4 % 2 = 0 then 1 else 0) ∧
    ((1 : BitVec 32) &&& BitVec.ofNat 32 n >>> 2) = (if n / 4 % 2 = 0 then 0 else 1) := fun n h => by
  have := selBits_split (n / 32) (by omega_using [h]) (n % 32) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod] at this

/-- `2 ^ (24 - 8 L)` for the index's low two bits `L`, as `extract` computes it. -/
def ilVal (i : BitVec 32) : BitVec 32 :=
  (1 + (1 &&& ~~~i) <<< 8 - (1 &&& ~~~i)) * (1 + (1 &&& ~~~(i >>> 1)) <<< 16 - (1 &&& ~~~(i >>> 1)))

/-- `ilVal` of the index `32 a + b`: the 256 indices, as two ranges that
`decide` evaluates. -/
theorem ilVal_split : ∀ a < 8, ∀ b < 32,
    ilVal (BitVec.ofNat 32 (32 * a + b)) = BitVec.ofNat 32 (2 ^ (24 - 8 * ((32 * a + b) % 4))) := by decide

theorem ilVal_ofNat : ∀ n < 256, ilVal (BitVec.ofNat 32 n) = BitVec.ofNat 32 (2 ^ (24 - 8 * (n % 4))) :=
  fun n h => by
    have := ilVal_split (n / 32) (by omega_using [h]) (n % 32) (Nat.mod_lt _ (by decide))
    rwa [Nat.div_add_mod] at this

/-- Byte `L` of a word is the top byte of its product with `2 ^ (24 - 8 L)`. -/
theorem top_byte (P : BitVec 32) {L : Nat} (hL : L < 4) :
    (P * BitVec.ofNat 32 (2 ^ (24 - 8 * L))) >>> 24 = (P.extractLsb' (8 * L) 8).setWidth 32 := by
  rw [show BitVec.ofNat 32 (2 ^ (24 - 8 * L)) = BitVec.twoPow 32 (24 - 8 * L) from
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, BitVec.toNat_twoPow]), BitVec.mul_twoPow_eq_shiftLeft]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · rw [decide_eq_true h8, decide_eq_true (show 24 + i < 32 by omega_using [h8]),
      decide_eq_false (show ¬ 24 + i < 24 - 8 * L by omega_using []), Bool.not_false, Bool.true_and, Bool.true_and,
      Bool.true_and, show 24 + i - (24 - 8 * L) = 8 * L + i by omega_using [hL]]
  · simp only [decide_eq_false h8, decide_eq_false (show ¬ 24 + i < 32 by omega_using [h8]), Bool.false_and]

/-- The entry, as `extract` computes it from the columns `a` and the index `i`. -/
def exVal (a : Nat → BitVec 32) (i : BitVec 32) : BitVec 32 :=
  ((a 1 * ((1 : BitVec 32) &&& i >>> 2) + a 0 * ((1 : BitVec 32) &&& ~~~(i >>> 2))) * ilVal i) >>> 24 |||
    ((a 3 * (((1 : BitVec 32) &&& ~~~(i >>> 2)) - (1 : BitVec 32)) + a 2 * (((1 : BitVec 32) &&& i >>> 2) - (1 : BitVec 32))) * ilVal i) >>> 24
      <<< 8 |||
    ((a 5 * ((1 : BitVec 32) &&& i >>> 2) + a 4 * ((1 : BitVec 32) &&& ~~~(i >>> 2))) * ilVal i) >>> 24 <<< 16 |||
    ((a 7 * (((1 : BitVec 32) &&& ~~~(i >>> 2)) - (1 : BitVec 32)) + a 6 * (((1 : BitVec 32) &&& i >>> 2) - (1 : BitVec 32))) * ilVal i) >>> 24
      <<< 24

theorem sel_lo (a b : BitVec 32) : b * 0 + a * 1 = a := by
  show b * 0#32 + a * 1#32 = a
  rw [BitVec.mul_zero, BitVec.mul_one, BitVec.zero_add]

theorem sel_hi (a b : BitVec 32) : b * 1 + a * 0 = b := by
  show b * 1#32 + a * 0#32 = b
  rw [BitVec.mul_zero, BitVec.mul_one, BitVec.add_zero]

theorem nsel_lo (w b : BitVec 32) : b * (1 - 1) + -w * (0 - 1) = w := by
  show b * (1#32 - 1#32) + -w * (0#32 - 1#32) = w
  rw [BitVec.sub_self, BitVec.mul_zero, BitVec.zero_add, BitVec.zero_sub, BitVec.neg_mul_neg, BitVec.mul_one]

theorem nsel_hi (w a : BitVec 32) : -w * (0 - 1) + a * (1 - 1) = w := by
  show -w * (0#32 - 1#32) + a * (1#32 - 1#32) = w
  rw [BitVec.sub_self, BitVec.mul_zero, BitVec.add_zero, BitVec.zero_sub, BitVec.neg_mul_neg, BitVec.mul_one]

/-- The entry from its bytes in the planes' words of the index's row. -/
theorem entry_of_words (m : Mem) (p : Addr) {j : Nat} (hj : j < 4) (x : Byte) :
    ((planeWord m p j 0 (x.toNat / 4)).extractLsb' (8 * (x.toNat % 4)) 8).setWidth 32 |||
      ((planeWord m p j 1 (x.toNat / 4)).extractLsb' (8 * (x.toNat % 4)) 8).setWidth 32 <<< 8 |||
      ((planeWord m p j 2 (x.toNat / 4)).extractLsb' (8 * (x.toNat % 4)) 8).setWidth 32 <<< 16 |||
      ((planeWord m p j 3 (x.toNat / 4)).extractLsb' (8 * (x.toNat % 4)) 8).setWidth 32 <<< 24 =
      sEntry (scheduleAt m p) j x := by
  have hb (b : Nat) : (planeWord m p j b (x.toNat / 4)).extractLsb' (8 * (x.toNat % 4)) 8 =
      m (p + BitVec.ofNat 64 (1024 * j + 256 * b + x.toNat)) := by
    rw [planeWord, ← Mem.readW_byte _ _ (Nat.mod_lt _ (by decide)), Offset.add_add]
    exact congrArg (fun n => m (p + BitVec.ofNat 64 n)) (by omega_arith)
  refine word_ext fun b hb4 => ?_
  rw [hb, hb, hb, hb]
  refine (byte_of_le4 _ _ _ _ hb4).trans ?_
  rw [sEntry_byte m p hj hb4]
  rcases (by omega_using [hb4] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The entry of the index `x`, from the columns after the rows: the words
of row `x / 8` of S-box `j`'s planes, negated in columns 2, 3, 6 and 7. -/
theorem exVal_eq (m : Mem) (p : Addr) {j : Nat} (hj : j < 4) (x : Byte) (a : Nat → BitVec 32)
    (ha : ∀ c < 8, a c = Scan.Arm.val c (planeWord m p j (c / 2) (2 * (x.toNat / 8) + c % 2))) :
    exVal a (x.setWidth 32) = sEntry (scheduleAt m p) j x := by
  have hx := x.isLt
  obtain ⟨n, hn⟩ : ∃ n, x.toNat = n := ⟨_, rfl⟩
  rw [hn] at hx ha
  obtain ex : x.setWidth 32 = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hn]
  obtain ⟨m0, m1⟩ := selBits n hx
  have a0 : a 0 = planeWord m p j 0 (2 * (n / 8)) := ha 0 (by decide)
  have a1 : a 1 = planeWord m p j 0 (2 * (n / 8) + 1) := ha 1 (by decide)
  have a2 : a 2 = -planeWord m p j 1 (2 * (n / 8)) := ha 2 (by decide)
  have a3 : a 3 = -planeWord m p j 1 (2 * (n / 8) + 1) := ha 3 (by decide)
  have a4 : a 4 = planeWord m p j 2 (2 * (n / 8)) := ha 4 (by decide)
  have a5 : a 5 = planeWord m p j 2 (2 * (n / 8) + 1) := ha 5 (by decide)
  have a6 : a 6 = -planeWord m p j 3 (2 * (n / 8)) := ha 6 (by decide)
  have a7 : a 7 = -planeWord m p j 3 (2 * (n / 8) + 1) := ha 7 (by decide)
  rw [← entry_of_words m p hj x, hn]
  unfold exVal
  rw [ex, ilVal_ofNat n hx, m0, m1, a0, a1, a2, a3, a4, a5, a6, a7]
  by_cases hb : n / 4 % 2 = 0
  · rw [ite_eq_left hb, ite_eq_left hb, sel_lo, sel_lo, nsel_lo, nsel_lo,
      top_byte _ (Nat.mod_lt _ (by decide)), top_byte _ (Nat.mod_lt _ (by decide)),
      top_byte _ (Nat.mod_lt _ (by decide)), top_byte _ (Nat.mod_lt _ (by decide)),
      show 2 * (n / 8) = n / 4 by omega_using [hb]]
  · rw [ite_eq_right hb, ite_eq_right hb, sel_hi, sel_hi, nsel_hi, nsel_hi,
      top_byte _ (Nat.mod_lt _ (by decide)), top_byte _ (Nat.mod_lt _ (by decide)),
      top_byte _ (Nat.mod_lt _ (by decide)), top_byte _ (Nat.mod_lt _ (by decide)),
      show 2 * (n / 8) + 1 = n / 4 by omega_using [hb]]

/-! ## The pieces of a lookup -/

/-- The address of a word of S-box `j`'s planes, as the rows read it: column
`c` of row `r` of group `g` is plane `c / 2`'s word `2 (8 g + r) + c % 2`. -/
theorem wordAddr_eq {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) {j g r c : Nat} (hj : j < 4) (hg : g < 4)
    (hr : r < 8) (hc : c < 8) :
    State.addr (S + BitVec.ofNat 32 (1024 * j) + BitVec.ofNat 32 (64 * g) + BitVec.ofNat 32 (wordOff r c)) =
      State.addr S + BitVec.ofNat 64 (1024 * j + 256 * (c / 2) + 4 * (2 * (8 * g + r) + c % 2)) := by
  unfold wordOff
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add, addr_add (by omega_arith)]
  exact congrArg (fun n => State.addr S + BitVec.ofNat 64 n) (by omega_arith)

/-- One of F's words read past a store to another. -/
theorem fslot_rw (m : Mem) (D : Addr) {i j : Nat} (x : BitVec 32) (h : j + 4 ≤ i ∨ i + 4 ≤ j) (hi : i < 4096)
    (hj : j < 4096) :
    (m.writeW (D + BitVec.ofNat 64 i) x).readW (D + BitVec.ofNat 64 j) 32 = m.readW (D + BitVec.ofNat 64 j) 32 :=
  Mem.readW_writeW_sep (Offset.sep D (d := j) (n := 4) (e := i) (k := 4) h (by omega_arith) (by omega_arith))
    (by decide)

/-- The entry, from the columns `a` and the index in the top byte of the
indices' word `X`. -/
theorem extract_run (u : State) {D : Addr} {X : BitVec 32} (a : Nat → BitVec 32)
    (h12 : State.addr (u.gpr .r12 + BitVec.ofNat 32 64) = D + BitVec.ofNat 64 16)
    (hin : InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 16) 4)
    (hX : u.mem.readW (D + BitVec.ofNat 64 16) 32 = X) (h3 : u.gpr .r3 = 1)
    (ha : ∀ c < 8, u.gpr (colReg c) = a c) :
    WP isa (.block extract) u fun t => t.gpr .r0 = exVal a (X >>> 24) ∧ t.mem = u.mem := by
  have a0 : u.gpr .r4 = a 0 := ha 0 (by decide)
  have a1 : u.gpr .r5 = a 1 := ha 1 (by decide)
  have a2 : u.gpr .r6 = a 2 := ha 2 (by decide)
  have a3 : u.gpr .r7 = a 3 := ha 3 (by decide)
  have a4 : u.gpr .r8 = a 4 := ha 4 (by decide)
  have a5 : u.gpr .r9 = a 5 := ha 5 (by decide)
  have a6 : u.gpr .r10 = a 6 := ha 6 (by decide)
  have a7 : u.gpr .r11 = a 7 := ha 7 (by decide)
  unfold extract
  brun [fOff, h12, hin, hX, h3, a0, a1, a2, a3, a4, a5, a6, a7]
  rfl

/-- The indices left, F so far and whether this is the third lookup (the
offset `Kv` of its S-box is 2048). -/
theorem combineHead_run (u : State) {D : Addr} {X Fo Kv : BitVec 32}
    (h12 : ∀ o, o < 32 → State.addr (u.gpr .r12 + BitVec.ofNat 32 (48 + o)) = D + BitVec.ofNat 64 o)
    (hin : ∀ {o : Nat}, o + 4 ≤ 32 → InRegions u.wr (D + BitVec.ofNat 64 o) 4)
    (hX : u.mem.readW (D + BitVec.ofNat 64 16) 32 = X) (hF : u.mem.readW (D + BitVec.ofNat 64 28) 32 = Fo)
    (hK : u.mem.readW (D + BitVec.ofNat 64 20) 32 = Kv) :
    WP isa (.block combineHead) u fun t =>
      t.mem = u.mem.writeW (D + BitVec.ofNat 64 16) (X <<< 8) ∧ t.gpr .r1 = Fo ∧ t.gpr .r2 = Kv ∧
        t.z = (Kv - BitVec.ofNat 32 2048 == 0#32) := by
  have hin' : ∀ {o : Nat}, o + 4 ≤ 32 → InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 o) 4 :=
    fun ho => region_in (hin ho)
  have hF' : ∀ w : BitVec 32, (u.mem.writeW (D + BitVec.ofNat 64 16) w).readW (D + BitVec.ofNat 64 28) 32 = Fo :=
    fun w => by rw [fslot_rw _ _ _ (by decide) (by decide) (by decide), hF]
  have hK' : ∀ w : BitVec 32, (u.mem.writeW (D + BitVec.ofNat 64 16) w).readW (D + BitVec.ofNat 64 20) 32 = Kv :=
    fun w => by rw [fslot_rw _ _ _ (by decide) (by decide) (by decide), hK]
  have a64 : State.addr (u.gpr .r12 + BitVec.ofNat 32 64) = D + BitVec.ofNat 64 16 := h12 16 (by decide)
  have a68 : State.addr (u.gpr .r12 + BitVec.ofNat 32 68) = D + BitVec.ofNat 64 20 := h12 20 (by decide)
  have a76 : State.addr (u.gpr .r12 + BitVec.ofNat 32 76) = D + BitVec.ofNat 64 28 := h12 28 (by decide)
  unfold combineHead
  brun [fOff, a64, a68, a76, hin, hin', hX, hF', hK']

/-- F so far to its word, and the next S-box's offset. -/
theorem combineTail_run (u : State) {D : Addr}
    (h12 : ∀ o, o < 32 → State.addr (u.gpr .r12 + BitVec.ofNat 32 (48 + o)) = D + BitVec.ofNat 64 o)
    (hin : ∀ {o : Nat}, o + 4 ≤ 32 → InRegions u.wr (D + BitVec.ofNat 64 o) 4) :
    WP isa (.block combineTail) u fun t =>
      t.mem = (u.mem.writeW (D + BitVec.ofNat 64 28) (u.gpr .r1)).writeW (D + BitVec.ofNat 64 20)
        (u.gpr .r2 + BitVec.ofNat 32 1024) ∧
      t.z = (u.gpr .r2 + BitVec.ofNat 32 1024 - BitVec.ofNat 32 4096 == 0#32) := by
  have a68 : State.addr (u.gpr .r12 + BitVec.ofNat 32 68) = D + BitVec.ofNat 64 20 := h12 20 (by decide)
  have a76 : State.addr (u.gpr .r12 + BitVec.ofNat 32 76) = D + BitVec.ofNat 64 28 := h12 28 (by decide)
  unfold combineTail
  brun [fOff, a68, a76, hin]

theorem off_step : ∀ j < 4, BitVec.ofNat 32 (1024 * j) + BitVec.ofNat 32 1024 = BitVec.ofNat 32 (1024 * (j + 1)) ∧
    (BitVec.ofNat 32 (1024 * j) + BitVec.ofNat 32 1024 - BitVec.ofNat 32 4096 == 0#32) = decide (j + 1 = 4) ∧
    (BitVec.ofNat 32 (1024 * j) - BitVec.ofNat 32 2048 == 0#32) = decide (j = 2) := by decide

/-! ## A lookup -/

/-- The address of F's words of the working space at `r3`. -/
scoped notation:max "fbase " s:max => State.addr (State.gpr s Reg.r3) + BitVec.ofNat 64 48

/-- The state of F from `s` with `j` lookups made: the schedule, the halves
and the pointer into the P-array in their words, xL shifted, the next
S-box's offset and F so far in theirs, and nothing else of memory written. -/
structure FAt (s : State) (j : Nat) (v : State) : Prop where
  r12 : v.gpr .r12 = s.gpr .r3
  fr : Frame [fRegion s] s.mem v.mem
  s0 : v.mem.readW (fbase s + BitVec.ofNat 64 0) 32 = s.gpr .r0
  s1 : v.mem.readW (fbase s + BitVec.ofNat 64 4) 32 = s.gpr .r1
  s2 : v.mem.readW (fbase s + BitVec.ofNat 64 8) 32 = s.gpr .r2
  s12 : v.mem.readW (fbase s + BitVec.ofNat 64 12) 32 = s.gpr .r12
  sx : v.mem.readW (fbase s + BitVec.ofNat 64 16) 32 = s.gpr .r1 <<< (8 * j)
  sk : v.mem.readW (fbase s + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 (1024 * j)
  sf : v.mem.readW (fbase s + BitVec.ofNat 64 28) 32 =
    if j = 0 then 0 else fAcc (scheduleAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r1) (j - 1)
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  sp : v.sp = s.sp

/-- A lookup: the next S-box's entry at xL's next byte, into F so far. -/
theorem look_run {s v : State} (E : LookEnv s) {j : Nat} (hj : j < 4) (hv : FAt s j v) :
    WP isa look v fun w => FAt s (j + 1) w ∧ w.z = decide (j + 1 = 4) := by
  have fit := E.fit
  have fitW := E.fitW
  have hfr := hv.fr
  have s0 := hv.s0
  have s1 := hv.s1
  have s2 := hv.s2
  have s12 := hv.s12
  have sx := hv.sx
  have sk := hv.sk
  have sf := hv.sf
  have sep := E.sep
  have hrd := hv.rd
  have hwr := hv.wr
  have v12 := hv.r12
  obtain ⟨D, hD⟩ : ∃ D, fbase s = D := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, scheduleAt s.mem (State.addr (s.gpr .r0)) = K := ⟨_, rfl⟩
  rw [fRegion, hD] at hfr sep
  rw [hD] at s0 s1 s2 s12 sx sk sf
  rw [hK] at sf
  have aS : ∀ o, o < 32 → State.addr (s.gpr .r3 + BitVec.ofNat 32 (48 + o)) = D + BitVec.ofNat 64 o :=
    fun o ho => by rw [addr_add (by omega_arith), ← hD, Offset.add_add]
  have a48 : State.addr (s.gpr .r3 + BitVec.ofNat 32 48) = D + BitVec.ofNat 64 0 := aS 0 (by decide)
  have a52 : State.addr (s.gpr .r3 + BitVec.ofNat 32 52) = D + BitVec.ofNat 64 4 := aS 4 (by decide)
  have a56 : State.addr (s.gpr .r3 + BitVec.ofNat 32 56) = D + BitVec.ofNat 64 8 := aS 8 (by decide)
  have a60 : State.addr (s.gpr .r3 + BitVec.ofNat 32 60) = D + BitVec.ofNat 64 12 := aS 12 (by decide)
  have a64 : State.addr (s.gpr .r3 + BitVec.ofNat 32 64) = D + BitVec.ofNat 64 16 := aS 16 (by decide)
  have a68 : State.addr (s.gpr .r3 + BitVec.ofNat 32 68) = D + BitVec.ofNat 64 20 := aS 20 (by decide)
  have a72 : State.addr (s.gpr .r3 + BitVec.ofNat 32 72) = D + BitVec.ofNat 64 24 := aS 24 (by decide)
  have a76 : State.addr (s.gpr .r3 + BitVec.ofNat 32 76) = D + BitVec.ofNat 64 28 := aS 28 (by decide)
  have inS : ∀ {o : Nat}, o + 4 ≤ 32 → InRegions s.wr (D + BitVec.ofNat 64 o) 4 :=
    fun ho => by rw [← hD]; exact E.wr _ ho
  have inS' : ∀ {o : Nat}, o + 4 ≤ 32 → InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 o) 4 :=
    fun ho => region_in (inS ho)
  -- The index.
  obtain ⟨x, hx⟩ : ∃ x : Byte, quarter (s.gpr .r1) j = x := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, x.toNat = n := ⟨_, rfl⟩
  obtain hn256 : n < 256 := by have := x.isLt; omega_using [hn, this]
  obtain hxn : (x.setWidth 32).toNat = n := by
    rw [BitVec.toNat_setWidth, hn]; exact Nat.mod_eq_of_lt (by omega_using [hn256])
  unfold look
  apply WP.seq
  unfold lookStart
  rw [WP.block_append_iff, WP.block_append_iff]
  have hA : WP isa (.block [.ldr .r0 .r12 (fOff + 16), .mov .r0 (.shifted .r0 .lsr 24)]) v fun u =>
      u.gpr .r0 = x.setWidth 32 ∧ u.mem = v.mem := by
    brun [fOff, v12, a64, inS', hrd, hwr, sx]
    rw [index_shift _ hj, hx]
  refine WP.mono (WP.keep [.r0] hA (by decide)) fun u ⟨⟨u0, um⟩, uk⟩ => ?_
  -- Its row's one-hot word, and the columns cleared.
  refine WP.mono (Scan.Arm.start_ok u (by rw [u0, hxn]; exact hn256))
    fun t ⟨t2, t3, tc, to, tm, trd, twr, tsp⟩ => ?_
  rw [u0, hxn] at t2
  obtain t12 : t.gpr .r12 = s.gpr .r3 := (to _ (by decide)).trans ((uk.gpr (by decide)).trans v12)
  obtain trd' : t.rd = s.rd := trd.trans (uk.2.1.trans hrd)
  obtain twr' : t.wr = s.wr := twr.trans (uk.2.2.1.trans hwr)
  obtain tm' : t.mem = v.mem := tm.trans um
  -- The S-box's pointer.
  have hB : WP isa (.block [.ldr .lr .r12 fOff, .ldr .r0 .r12 (fOff + 20), .dp .add .lr .lr (.reg .r0)]) t fun y =>
      y.gpr .lr = s.gpr .r0 + BitVec.ofNat 32 (1024 * j) ∧ y.mem = t.mem := by
    brun [fOff, t12, a48, a68, inS', trd', twr', tm', s0, sk]
  refine WP.mono (WP.keep [.r0, .lr] hB (by decide)) fun y ⟨⟨yl, ym⟩, yk⟩ => ?_
  obtain y12 : y.gpr .r12 = s.gpr .r3 := (yk.gpr (by decide)).trans t12
  obtain yrd : y.rd = s.rd := yk.2.1.trans trd'
  obtain ywr : y.wr = s.wr := yk.2.2.1.trans twr'
  obtain ym' : y.mem = v.mem := ym.trans tm'
  -- The rows.
  obtain pre : Scan.Arm.RowsPre wordOff 64 (fOff + 24) (n / 8) (s.gpr .r0 + BitVec.ofNat 32 (1024 * j)) y :=
    { hh := by omega_using [hn256]
      r2 := by rw [yk.gpr (by decide), t2]
      r3 := by rw [yk.gpr (by decide), t3]
      lr := yl
      cols := fun c hc => by
        rw [yk.gpr (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨Scan.Arm.colReg_ne_r0 c, Scan.Arm.colReg_ne_lr c⟩), tc c hc]
      hcnt := by decide
      slot := by rw [y12]; show InRegions y.wr (State.addr (s.gpr .r3 + BitVec.ofNat 32 72)) 4; rw [a72, ywr]; exact inS (by decide)
      hstride := by decide
      hoffs := fun r hr c hc => by unfold wordOff; omega_arith
      rd := fun g hg r hr c hc => by
        rw [wordAddr_eq fit hj hg hr hc, yrd, ywr]
        exact E.rd _ (by omega_arith)
      dis := fun g hg r hr c hc => by
        rw [wordAddr_eq fit hj hg hr hc, y12]
        show Region.Disjoint _ ⟨State.addr (s.gpr .r3 + BitVec.ofNat 32 72), 4⟩
        rw [a72]
        exact (sep.sub_left (Offset.sub_base _ (n := 4) (by omega_arith))).sub_right
          (Offset.sub_base _ (by decide)) }
  apply WP.seq
  refine WP.mono (Scan.Arm.rows_ok pre) fun z ⟨zc, zo, zfr, zrd, zwr, zsp⟩ => ?_
  rw [y12, ym'] at zfr
  obtain zfr : Frame [⟨D + BitVec.ofNat 64 24, 4⟩] v.mem z.mem := by rw [← a72]; exact zfr
  obtain z12 : z.gpr .r12 = s.gpr .r3 := (zo _ (by decide)).trans y12
  obtain zrd' : z.rd = s.rd := zrd.trans yrd
  obtain zwr' : z.wr = s.wr := zwr.trans ywr
  -- The words of the index's row.
  obtain za : ∀ c < 8, z.gpr (colReg c) =
      Scan.Arm.val c (planeWord s.mem (State.addr (s.gpr .r0)) j (c / 2) (2 * (n / 8) + c % 2)) := by
    intro c hc
    rw [zc c hc, Scan.Arm.wordAt, wordAddr_eq fit hj (by omega_using [hn256]) (by omega_arith) hc,
      show 8 * (n / 8 / 8) + n / 8 % 8 = n / 8 by omega_arith, ym', planeWord]
    exact congrArg _ (hfr.readW (r := ⟨State.addr (s.gpr .r0) +
      BitVec.ofNat 64 (1024 * j + 256 * (c / 2) + 4 * (2 * (n / 8) + c % 2)), 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sep.sub_left (Offset.sub_base _ (by omega_using [hj, hc, hn256]))) (by decide))
  -- F's words after the rows.
  have zsl {i : Nat} (hi : i + 4 ≤ 24 ∨ 28 ≤ i) (hi' : i < 4096) :
      z.mem.readW (D + BitVec.ofNat 64 i) 32 = v.mem.readW (D + BitVec.ofNat 64 i) 32 :=
    zfr.readW (r := ⟨D + BitVec.ofNat 64 i, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint D (by omega_using [hi]) (by omega_arith) (by decide)) (by decide)
  apply WP.seq
  rw [WP.block_append_iff]
  -- The entry.
  refine WP.mono (WP.keep [.r0, .r1, .r2, .r4, .r5, .r6, .r8, .r9, .r10, .lr] (extract_run z
    (fun c => Scan.Arm.val c (planeWord s.mem (State.addr (s.gpr .r0)) j (c / 2) (2 * (n / 8) + c % 2)))
    (by rw [z12]; exact a64) (by rw [zrd', zwr']; exact inS' (by decide))
    ((zsl (by decide) (by decide)).trans sx)
    ((zo _ (by decide)).trans ((yk.gpr (by decide)).trans t3)) za) (by decide)) fun p ⟨⟨p0, pm⟩, pk⟩ => ?_
  rw [index_shift _ hj, hx, ← hn, exVal_eq s.mem (State.addr (s.gpr .r0)) hj x _ (fun c _ => rfl), hK] at p0
  obtain p12 : p.gpr .r12 = s.gpr .r3 := (pk.gpr (by decide)).trans z12
  obtain pwr : p.wr = s.wr := pk.2.2.1.trans zwr'
  have aSp : ∀ o, o < 32 → State.addr (p.gpr .r12 + BitVec.ofNat 32 (48 + o)) = D + BitVec.ofNat 64 o :=
    fun o ho => by rw [p12]; exact aS o ho
  -- The indices left, and F so far.
  refine WP.mono (WP.keep [.r1, .r2] (combineHead_run p (X := s.gpr .r1 <<< (8 * j))
    (Fo := if j = 0 then 0 else fAcc K (s.gpr .r1) (j - 1)) (Kv := BitVec.ofNat 32 (1024 * j)) aSp
    (fun ho => by rw [pwr]; exact inS ho)
    (by rw [pm]; exact (zsl (by decide) (by decide)).trans sx)
    (by rw [pm]; exact (zsl (by decide) (by decide)).trans sf)
    (by rw [pm]; exact (zsl (by decide) (by decide)).trans sk)) (by decide))
    fun q ⟨⟨qm, q1, q2, qz⟩, qk⟩ => ?_
  obtain ⟨o1, o2, o3⟩ := off_step j hj
  rw [o3] at qz
  obtain q0 : q.gpr .r0 = sEntry K j x := (qk.gpr (by decide)).trans p0
  obtain q12 : q.gpr .r12 = s.gpr .r3 := (qk.gpr (by decide)).trans p12
  -- The S-box's entry into F.
  apply WP.seq
  have hC : WP isa (.ite .eq (.block [.dp .eor .r1 .r1 (.reg .r0)]) (.block [.dp .add .r1 .r1 (.reg .r0)])) q
      fun c => c.gpr .r1 = fAcc K (s.gpr .r1) j ∧ c.mem = q.mem ∧ Keep [.r1] q c := by
    have hsq : sEntry K j x = sq K (s.gpr .r1) j := by rw [sq, hx]
    refine WP.ite _ (by rw [eval_eq, qz]) (fun h => ?_) (fun h => ?_)
    · obtain e2 : j = 2 := of_decide_eq_true h
      refine WP.mono (WP.keep [.r1] (Q := fun c => c.gpr .r1 = q.gpr .r1 ^^^ q.gpr .r0 ∧ c.mem = q.mem)
        (by brun) (by decide)) fun c ⟨⟨c1, cm⟩, ck⟩ => ⟨?_, cm, ck⟩
      rw [c1, q1, q0, hsq, ← fAcc_step K (s.gpr .r1) hj _ (fun _ => rfl), ite_eq_right (by omega_using [e2]),
        ite_eq_right (by omega_using [e2]), ite_eq_left e2]
    · obtain e2 : ¬j = 2 := of_decide_eq_false h
      refine WP.mono (WP.keep [.r1] (Q := fun c => c.gpr .r1 = q.gpr .r1 + q.gpr .r0 ∧ c.mem = q.mem)
        (by brun) (by decide)) fun c ⟨⟨c1, cm⟩, ck⟩ => ⟨?_, cm, ck⟩
      rw [c1, q1, q0, hsq]
      by_cases e0 : j = 0
      · subst e0
        rw [ite_eq_left rfl]
        show 0#32 + sq K (s.gpr .r1) 0 = _
        rw [BitVec.zero_add]; rfl
      · rw [ite_eq_right e0, ← fAcc_step K (s.gpr .r1) hj _ (fun _ => rfl), ite_eq_right e0, ite_eq_right e2]
  refine WP.mono hC fun c ⟨c1, cm, ck⟩ => ?_
  obtain c12 : c.gpr .r12 = s.gpr .r3 := (ck.gpr (by decide)).trans q12
  obtain cwr : c.wr = s.wr := ck.2.2.1.trans (qk.2.2.1.trans pwr)
  refine WP.mono (WP.keep [.r2] (combineTail_run c (D := D) (fun o ho => by rw [c12]; exact aS o ho)
    (fun ho => by rw [cwr]; exact inS ho)) (by decide)) fun w ⟨⟨wm, wz⟩, wk⟩ => ?_
  rw [ck.gpr (r := .r2) (by decide), q2, o1, c1, cm, qm, pm] at wm
  rw [ck.gpr (r := .r2) (by decide), q2, o2] at wz
  -- The state after the lookup.
  obtain zf : Frame [⟨D, 32⟩] s.mem z.mem :=
    hfr.trans (zfr.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩)
  refine ⟨⟨(wk.gpr (by decide)).trans c12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    wk.2.1.trans (ck.2.1.trans (qk.2.1.trans (pk.2.1.trans zrd'))), wk.2.2.1.trans cwr,
    wk.2.2.2.trans (ck.2.2.2.trans (qk.2.2.2.trans (pk.2.2.2.trans (zsp.trans (yk.2.2.2.trans
      (tsp.trans (uk.2.2.2.trans hv.sp)))))))⟩, wz⟩
  · rw [fRegion, hD, wm]
    exact ((zf.writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  · rw [hD, wm]
    simp (disch := decide) only [fslot_rw]
    rw [zsl (by decide) (by decide), s0]
  · rw [hD, wm]
    simp (disch := decide) only [fslot_rw]
    rw [zsl (by decide) (by decide), s1]
  · rw [hD, wm]
    simp (disch := decide) only [fslot_rw]
    rw [zsl (by decide) (by decide), s2]
  · rw [hD, wm]
    simp (disch := decide) only [fslot_rw]
    rw [zsl (by decide) (by decide), s12]
  · rw [hD, wm]
    simp (disch := decide) only [fslot_rw]
    rw [Mem.readW_writeW_self32, ← BitVec.shiftLeft_add, Nat.mul_succ]
  · rw [hD, wm, Mem.readW_writeW_self32]
  · rw [hD, wm, hK]
    simp (disch := decide) only [fslot_rw]
    rw [Mem.readW_writeW_self32, ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel]

/-! ## F -/

theorem f_run {s : State} (E : LookEnv s) :
    WP isa Impl.Blowfish.Arm.f s fun t =>
      t.gpr .lr = Spec.Blowfish.f (scheduleAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r1) ∧
        Keep fRegs s t ∧ Frame [fRegion s] s.mem t.mem := by
  have fitW := E.fitW
  obtain ⟨D, hD⟩ : ∃ D, fbase s = D := ⟨_, rfl⟩
  have aS : ∀ o, o < 32 → State.addr (s.gpr .r3 + BitVec.ofNat 32 (48 + o)) = D + BitVec.ofNat 64 o :=
    fun o ho => by rw [addr_add (by omega_arith), ← hD, Offset.add_add]
  have a48 : State.addr (s.gpr .r3 + BitVec.ofNat 32 48) = D + BitVec.ofNat 64 0 := aS 0 (by decide)
  have a52 : State.addr (s.gpr .r3 + BitVec.ofNat 32 52) = D + BitVec.ofNat 64 4 := aS 4 (by decide)
  have a56 : State.addr (s.gpr .r3 + BitVec.ofNat 32 56) = D + BitVec.ofNat 64 8 := aS 8 (by decide)
  have a60 : State.addr (s.gpr .r3 + BitVec.ofNat 32 60) = D + BitVec.ofNat 64 12 := aS 12 (by decide)
  have a64 : State.addr (s.gpr .r3 + BitVec.ofNat 32 64) = D + BitVec.ofNat 64 16 := aS 16 (by decide)
  have a68 : State.addr (s.gpr .r3 + BitVec.ofNat 32 68) = D + BitVec.ofNat 64 20 := aS 20 (by decide)
  have a72 : State.addr (s.gpr .r3 + BitVec.ofNat 32 72) = D + BitVec.ofNat 64 24 := aS 24 (by decide)
  have a76 : State.addr (s.gpr .r3 + BitVec.ofNat 32 76) = D + BitVec.ofNat 64 28 := aS 28 (by decide)
  have inS : ∀ {o : Nat}, o + 4 ≤ 32 → InRegions s.wr (D + BitVec.ofNat 64 o) 4 :=
    fun ho => by rw [← hD]; exact E.wr _ ho
  have inS' : ∀ {o : Nat}, o + 4 ≤ 32 → InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 o) 4 :=
    fun ho => region_in (inS ho)
  unfold Impl.Blowfish.Arm.f
  apply WP.seq
  -- The schedule, the halves and the pointer to their words.
  have hS : WP isa (.block fStart) s fun u =>
      u.mem = ((((((s.mem.writeW (D + BitVec.ofNat 64 0) (s.gpr .r0)).writeW (D + BitVec.ofNat 64 4) (s.gpr .r1)).writeW
        (D + BitVec.ofNat 64 8) (s.gpr .r2)).writeW (D + BitVec.ofNat 64 12) (s.gpr .r12)).writeW
        (D + BitVec.ofNat 64 16) (s.gpr .r1)).writeW (D + BitVec.ofNat 64 20) 0#32).writeW
        (D + BitVec.ofNat 64 28) 0#32 ∧ u.gpr .r12 = s.gpr .r3 := by
    unfold fStart
    brun [fOff, a48, a52, a56, a60, a64, a68, a76, inS]
  refine WP.mono (WP.keep [.r0, .r12] hS (by decide)) fun u ⟨⟨um, u12⟩, uk⟩ => ?_
  obtain h₀ : FAt s 0 u := by
    refine ⟨u12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, uk.2.1, uk.2.2.1, uk.2.2.2⟩
    · rw [fRegion, hD, um]
      exact (((((((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
    all_goals rw [hD, um]
    all_goals simp (disch := decide) only [fslot_rw, Mem.readW_writeW_self32]
    · rw [Nat.mul_zero, BitVec.shiftLeft_zero]
    · rfl
  -- The lookups.
  have loop : WP isa (.loop look .ne) u (FAt s 4) := by
    refine WP.loop (M := isa) (fun n (v : State) => ∃ j, n = 4 - j ∧ j < 4 ∧ FAt s j v) ?_ 4 u
      ⟨0, rfl, by decide, h₀⟩
    rintro n v ⟨j, rfl, hj, hv⟩
    refine WP.mono (look_run E hj hv) fun w ⟨hw, wz⟩ => ?_
    rw [eval_ne, wz]
    by_cases he : j + 1 = 4
    · exact .inl ⟨by rw [decide_eq_true he]; rfl, he ▸ hw⟩
    · exact .inr ⟨by rw [decide_eq_false he]; rfl, 4 - (j + 1), by omega_using [hj], j + 1, rfl,
        by omega_using [hj, he], hw⟩
  apply WP.seq
  refine WP.mono loop fun v hv => ?_
  -- F, and the schedule, the halves, the working space and the pointer back.
  have s0 := hv.s0
  have s1 := hv.s1
  have s2 := hv.s2
  have s12 := hv.s12
  have sf := hv.sf
  have hrd := hv.rd
  have hwr := hv.wr
  have v12 := hv.r12
  rw [hD] at s0 s1 s2 s12 sf
  rw [ite_eq_right (by decide)] at sf
  have hE : WP isa (.block fEnd) v fun t =>
      t.gpr .lr = fAcc (scheduleAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r1) 3 ∧ t.gpr .r0 = s.gpr .r0 ∧
      t.gpr .r1 = s.gpr .r1 ∧ t.gpr .r2 = s.gpr .r2 ∧ t.gpr .r3 = s.gpr .r3 ∧ t.gpr .r12 = s.gpr .r12 ∧
      t.mem = v.mem := by
    unfold fEnd
    brun [fOff, v12, a48, a52, a56, a60, a76, inS', hrd, hwr, s0, s1, s2, s12, sf]
  refine WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r12, .lr] hE (by decide))
    fun t ⟨⟨tl, t0, t1, t2, t3, t12, tm⟩, tk⟩ => ?_
  refine ⟨by rw [tl, fAcc_three], ⟨fun r hr => ?_, tk.2.1.trans hrd, tk.2.2.1.trans hwr, tk.2.2.2.trans hv.sp⟩,
    by rw [tm]; exact hv.fr⟩
  simp only [fRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨hl, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hr
  cases r
  case r0 => exact t0
  case r1 => exact t1
  case r2 => exact t2
  case r3 => exact t3
  case r12 => exact t12
  all_goals first
    | exact absurd rfl hl
    | exact absurd rfl h4
    | exact absurd rfl h5
    | exact absurd rfl h6
    | exact absurd rfl h7
    | exact absurd rfl h8
    | exact absurd rfl h9
    | exact absurd rfl h10
    | exact absurd rfl h11

end VG.Proof.Blowfish.Arm

end

end


/-!
# Blowfish on ARMv7: the block function

`cipher_run`: `cipher up` takes the halves in `r1` and `r2` to their
encryption (`up`) or decryption under the schedule at `r0`, changing only
`r1`, `r2`, `r4`–`r12`, `lr`, the flags and F's words of the working space.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-- The P-array entry of round `m`. -/
def ord (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

/-- `pPtr`'s offset in the schedule after `i` rounds. -/
def pBase (up : Bool) (i : Nat) : Nat := if up then 4096 + 4 * i else 4160 - 4 * i

/-- The registers the block function writes. -/
def cRegs : List Reg := [.r1, .r2, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- What the block function needs: what F does (the schedule at `r0`
readable, and F's words of the working space at `r3` writable and apart from
it). -/
abbrev CipherEnv (s : State) : Prop := LookEnv s

/-- A P-array entry, in a memory that differs in F's words. -/
theorem pEntry_frame {s : State} (E : CipherEnv s) {m : Mem} (hf : Frame [fRegion s] s.mem m) {i : Nat}
    (hi : i < 18) :
    m.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4096 + 4 * i)) 32 =
      pEntry (scheduleAt s.mem (State.addr (s.gpr .r0))) i := by
  rw [pEntry_read _ _ hi]
  exact hf.readW (r := ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (4096 + 4 * i), 4⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact E.sep.sub_left (Offset.sub_base _ (by omega_using [hi]))) (by decide)

/-- The schedule, in a memory that differs in F's words. -/
theorem sched_frame {s : State} (E : CipherEnv s) {m : Mem} (hf : Frame [fRegion s] s.mem m) :
    scheduleAt m (State.addr (s.gpr .r0)) = scheduleAt s.mem (State.addr (s.gpr .r0)) :=
  scheduleAt_eq_of_frame _ hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact E.sep

/-- The address of the P-array entry of round `i`. -/
theorem addr_P {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) (up : Bool) {i : Nat} (hi : i < 16) :
    State.addr (S + BitVec.ofNat 32 (pBase up i) + BitVec.ofNat 32 (pAt up)) =
      State.addr S + BitVec.ofNat 64 (4096 + 4 * ord up i) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by cases up <;> simp [pBase, pAt] <;> omega_arith)]
  congr 2; cases up <;> simp [pBase, pAt, ord] <;> omega_using [hi]

/-- After `i` rounds from `s₀`. -/
structure CInv (s₀ : State) (up : Bool) (i : Nat) (u : State) : Prop where
  le : i ≤ 16
  p : u.gpr .r12 = s₀.gpr .r0 + BitVec.ofNat 32 (pBase up i)
  halves : (u.gpr .r1, u.gpr .r2) =
    iter (scheduleAt s₀.mem (State.addr (s₀.gpr .r0))) (ord up) i (s₀.gpr .r1, s₀.gpr .r2)
  keep : Keep cRegs s₀ u
  fr : Frame [fRegion s₀] s₀.mem u.mem

theorem round_head (u : State) (up : Bool) {P : BitVec 32} {a : Addr}
    (hp : State.addr (u.gpr .r12 + BitVec.ofNat 32 (pAt up)) = a)
    (hr : InRegions (u.rd ++ u.wr) a 4) (hP : u.mem.readW a 32 = P) :
    WP isa (.block [.ldr tmp pPtr (pAt up), .dp .eor xL xL (.reg tmp)]) u fun t =>
      t.gpr .r1 = u.gpr .r1 ^^^ P ∧ t.mem = u.mem := by
  have ho : pAt up < 4096 := by cases up <;> decide
  rw [← hp] at hr hP
  brun [ho, hr, hP]

theorem round_tail (u : State) (up : Bool) (S : BitVec 32) {i : Nat} (hi : i < 16)
    (h0 : u.gpr .r0 = S) (h12 : u.gpr .r12 = S + BitVec.ofNat 32 (pBase up i)) :
    WP isa (.block [.dp .eor xR xR (.reg fReg), .mov tmp (.reg xL), .mov xL (.reg xR), .mov xR (.reg tmp),
        .dp (if up then .add else .sub) pPtr pPtr (imm 4), .dp .sub tmp pPtr (.reg sch),
        .cmp tmp (imm (if up then pOff + 64 else pOff))]) u fun t =>
      t.gpr .r1 = u.gpr .r2 ^^^ u.gpr .lr ∧ t.gpr .r2 = u.gpr .r1 ∧
        t.gpr .r12 = S + BitVec.ofNat 32 (pBase up (i + 1)) ∧
        t.z = decide (i + 1 = 16) ∧ t.mem = u.mem := by
  cases up
  · brun [h0, h12, pOff]
    simp only [pBase, Bool.false_eq_true, ite_false]
    refine ⟨ofs_sub S (by omega_using [hi]), ?_⟩
    rw [ofs_sub S (by omega_using [hi]), ofs_diff, ofNat_sub_beq (by omega_using []) (by decide)]
    congr 1; apply propext; omega_using []
  · brun [h0, h12, pOff]
    simp only [pBase, ite_true]
    refine ⟨ofs_add S _ _, ?_⟩
    rw [ofs_add, ofs_diff, ofNat_sub_beq (by omega_using [hi]) (by decide)]
    congr 1; apply propext; omega_using []

theorem keep_reads {s t : State} {rs : List Reg} (k : Keep rs s t) : t.rd ++ t.wr = s.rd ++ s.wr := by
  rw [k.2.1, k.2.2.1]

theorem round_step {s₀ : State} (E : CipherEnv s₀) (up : Bool) {i : Nat} (hi : i < 16) {u : State}
    (I : CInv s₀ up i u) :
    WP isa (round up) u fun u' => CInv s₀ up (i + 1) u' ∧ u'.z = decide (i + 1 = 16) := by
  have fit := E.fit
  have ho : ord up i < 18 := by cases up <;> simp [ord] <;> omega_arith
  let K := scheduleAt s₀.mem (State.addr (s₀.gpr .r0))
  have u0 : u.gpr .r0 = s₀.gpr .r0 := I.keep.gpr (by decide)
  unfold round
  apply WP.seq
  refine WP.mono (WP.keep [.r1, .r9] (round_head u up (P := pEntry K (ord up i))
    (by rw [I.p, addr_P fit up hi]) (by rw [keep_reads I.keep]; exact E.rd _ (by omega_using [ho]))
    (pEntry_frame E I.fr ho)) (by cases up <;> decide)) fun v ⟨⟨v1, vm⟩, vk⟩ => ?_
  have kv : Keep cRegs s₀ v := I.keep.trans_sub vk (by decide)
  have Ev : LookEnv v := E.keep kv (by decide) (by decide)
  apply WP.seq
  refine WP.mono (f_run Ev) fun w ⟨w3, wk, wf⟩ => ?_
  rw [fRegion, kv.gpr (by decide), vm] at wf
  have w0 : w.gpr .r0 = s₀.gpr .r0 := by rw [wk.gpr (by decide), vk.gpr (by decide), u0]
  have w12 : w.gpr .r12 = s₀.gpr .r0 + BitVec.ofNat 32 (pBase up i) := by
    rw [wk.gpr (by decide), vk.gpr (by decide), I.p]
  refine WP.mono (WP.keep [.r1, .r2, .r9, .r12] (round_tail w up _ hi w0 w12) (by
    cases up <;> decide)) fun x ⟨⟨x1, x2, x12, xz, xm⟩, xk⟩ => ?_
  have hK : scheduleAt v.mem (State.addr (v.gpr .r0)) = K := by
    rw [vm, vk.gpr (by decide), u0]; exact sched_frame E I.fr
  refine ⟨⟨by omega_using [hi], x12, ?_, (kv.trans_sub wk (by decide)).trans_sub xk (by decide),
    by rw [xm]; exact I.fr.trans wf⟩, xz⟩
  · have w1 : w.gpr .r1 = u.gpr .r1 ^^^ pEntry K (ord up i) := by rw [wk.gpr (by decide), v1]
    have w2 : w.gpr .r2 = u.gpr .r2 := by rw [wk.gpr (by decide), vk.gpr (by decide)]
    rw [x1, x2, w3, hK, w1, w2, iter_succ, ← I.halves]
    simp only [roundStep]
    rw [BitVec.xor_comm, v1]

theorem cipher_start (s : State) (up : Bool) :
    WP isa (.block [.dp .add pPtr sch (imm (if up then pOff else pOff + 64))]) s fun t =>
      t.gpr .r12 = s.gpr .r0 + BitVec.ofNat 32 (pBase up 0) ∧ t.mem = s.mem := by
  cases up <;> brun [pOff, pBase]

theorem rounds_run {s : State} (E : CipherEnv s) (up : Bool) {u : State} (I : CInv s up 0 u) :
    WP isa (.loop (round up) .ne) u (CInv s up 16) := by
  refine WP.loop (M := isa) (Q := CInv s up 16)
    (fun (n : Nat) (v : State) => ∃ i, i < 16 ∧ n = 16 - i ∧ CInv s up i v) ?_ 16 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨i, hi, hn, J⟩
  refine WP.mono (round_step E up hi J) fun v' ⟨J', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : i + 1 = 16
  · left
    exact ⟨by rw [e]; rfl, e ▸ J'⟩
  · right
    exact ⟨by simp [e], n - 1, by omega_using [hi, hn], i + 1, by omega_using [hi, e], by omega_using [hn], J'⟩

/-- The addresses of the last P-array entries. -/
theorem addr_last {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) (up : Bool) :
    State.addr (S + BitVec.ofNat 32 (pBase up 16) + BitVec.ofNat 32 (pAt up)) =
        State.addr S + BitVec.ofNat 64 (4096 + 4 * ord up 16) ∧
      State.addr (S + BitVec.ofNat 32 (pBase up 16) + BitVec.ofNat 32 (4 - pAt up)) =
        State.addr S + BitVec.ofNat 64 (4096 + 4 * ord up 17) := by
  constructor <;>
  · rw [ofs_add, addr_add (by cases up <;> simp [pBase, pAt] <;> omega_using [fit])]
    congr 2; cases up <;> simp [pBase, pAt, ord]

theorem cipher_end (u : State) (up : Bool) {P₁₆ P₁₇ : BitVec 32} {a b : Addr}
    (ha : State.addr (u.gpr .r12 + BitVec.ofNat 32 (pAt up)) = a)
    (hb : State.addr (u.gpr .r12 + BitVec.ofNat 32 (4 - pAt up)) = b)
    (hra : InRegions (u.rd ++ u.wr) a 4) (hrb : InRegions (u.rd ++ u.wr) b 4)
    (h16 : u.mem.readW a 32 = P₁₆) (h17 : u.mem.readW b 32 = P₁₇) :
    WP isa (.block [.ldr tmp pPtr (pAt up), .dp .eor tmp xL (.reg tmp),
        .ldr xL pPtr (4 - pAt up), .dp .eor xL xL (.reg xR), .mov xR (.reg tmp)]) u fun t =>
      t.gpr .r1 = P₁₇ ^^^ u.gpr .r2 ∧ t.gpr .r2 = u.gpr .r1 ^^^ P₁₆ ∧ t.mem = u.mem := by
  have ho : pAt up < 4096 := by cases up <;> decide
  have ho' : 4 - pAt up < 4096 := by cases up <;> decide
  rw [← ha] at hra h16
  rw [← hb] at hrb h17
  brun [ho, ho', hra, hrb, h16, h17]

/-- The block function. -/
theorem cipher_run {s : State} (E : CipherEnv s) (up : Bool) :
    WP isa (cipher up) s fun t =>
      (t.gpr .r1, t.gpr .r2) =
        feistel (scheduleAt s.mem (State.addr (s.gpr .r0))) (ord up) (s.gpr .r1) (s.gpr .r2) ∧
      Keep cRegs s t ∧ Frame [fRegion s] s.mem t.mem := by
  have fit := E.fit
  unfold cipher
  apply WP.seq
  refine WP.mono (WP.keep [.r12] (cipher_start s up) (by cases up <;> decide))
    fun u ⟨⟨u12, um⟩, uk⟩ => ?_
  have I0 : CInv s up 0 u :=
    ⟨by decide, u12, by rw [uk.gpr (by decide), uk.gpr (by decide)]; rfl, uk.mono (by decide),
      by rw [um]; exact Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (rounds_run E up I0) fun v V => ?_
  obtain ⟨a16, a17⟩ := addr_last fit up
  have hrd := keep_reads V.keep
  let K := scheduleAt s.mem (State.addr (s.gpr .r0))
  have r16 : 4096 + 4 * ord up 16 + 4 ≤ 4168 := by cases up <;> decide
  have r17 : 4096 + 4 * ord up 17 + 4 ≤ 4168 := by cases up <;> decide
  have o16 : ord up 16 < 18 := by cases up <;> decide
  have o17 : ord up 17 < 18 := by cases up <;> decide
  refine WP.mono (WP.keep [.r1, .r2, .r9] (cipher_end v up (P₁₆ := pEntry K (ord up 16))
    (P₁₇ := pEntry K (ord up 17)) (a := State.addr (s.gpr .r0) + BitVec.ofNat 64 (4096 + 4 * ord up 16))
    (b := State.addr (s.gpr .r0) + BitVec.ofNat 64 (4096 + 4 * ord up 17)) (by rw [V.p]; exact a16) (by rw [V.p]; exact a17)
    (by rw [hrd]; exact E.rd _ r16) (by rw [hrd]; exact E.rd _ r17)
    (pEntry_frame E V.fr o16) (pEntry_frame E V.fr o17)) (by cases up <;> decide))
    fun t ⟨⟨t1, t2, tm⟩, tk⟩ => ?_
  refine ⟨?_, V.keep.trans_sub tk (by decide), by rw [tm]; exact V.fr⟩
  rw [t1, t2, feistel_eq, ← V.halves, BitVec.xor_comm]

end VG.Proof.Blowfish.Arm

end

end

/-!
# Blowfish on ARMv7: ECB

`ecb_correct`: every block becomes its encryption or decryption, one at a
time; our caller's registers are saved in the working space and restored.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-! ## Blocks in and out of the halves -/

theorem rev_byte (x : BitVec 32) {b : Nat} (hb : b < 4) :
    (rev x).extractLsb' (8 * b) 8 = x.extractLsb' (8 * (3 - b)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  exact rev_bit x hb hi

/-- The big-endian word at offset `o` of the block at `q`. -/
theorem rev_load (m : Mem) (q : Addr) {o : Nat} (ho : o ≤ 4) :
    rev (m.readW (q + BitVec.ofNat 64 o) 32) = decodeWord (blockAt m q) o := by
  refine word_ext fun b hb => ?_
  rw [rev_byte _ hb, decodeWord_byte _ _ hb, blockAt_getD _ _ (by omega_arith),
    ← Mem.readW_byte m _ (by omega_arith), Offset.add_add]

theorem sep_of_disjoint {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) :
    Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega_arith) (by simp only [Region.Contains]; omega_arith)

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

theorem inRegions_off {rs : List Region} {a : Addr} {N o n : Nat} (h : InRegions rs a N) (hon : o + n ≤ N) :
    InRegions rs (a + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  obtain e : a + BitVec.ofNat 64 o - r.base = (a - r.base) + BitVec.ofNat 64 o := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 o),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((a - r.base).toNat + o % 2 ^ 64) (2 ^ 64)
  have := Nat.mod_le o (2 ^ 64)
  omega_arith

theorem inRegions_pre {rs : List Region} {a : Addr} {N n : Nat} (h : InRegions rs a N) (hn : n ≤ N) :
    InRegions rs a n := by
  have := inRegions_off (o := 0) (n := n) h (by omega_arith)
  rwa [BitVec.add_zero] at this

/-- The block at the data pointer (in the working space) into the halves. -/
theorem loadBlock_run (u : State) {B P : BitVec 32} {Ba Pa : Addr} (hlr : u.gpr .r3 = B)
    (eB : State.addr (B + BitVec.ofNat 32 36) = Ba + BitVec.ofNat 64 36)
    (e0 : State.addr (P + BitVec.ofNat 32 0) = Pa) (e4 : State.addr (P + BitVec.ofNat 32 4) = Pa + BitVec.ofNat 64 4)
    (rB : InRegions (u.rd ++ u.wr) (Ba + BitVec.ofNat 64 36) 4)
    (r0 : InRegions (u.rd ++ u.wr) Pa 4) (r4 : InRegions (u.rd ++ u.wr) (Pa + BitVec.ofNat 64 4) 4)
    (hP : u.mem.readW (Ba + BitVec.ofNat 64 36) 32 = P) :
    WP isa (.block loadBlock) u fun t =>
      t.gpr .r1 = decodeWord (blockAt u.mem Pa) 0 ∧ t.gpr .r2 = decodeWord (blockAt u.mem Pa) 4 ∧
        t.mem = u.mem := by
  obtain l0 := rev_load u.mem Pa (o := 0) (by decide)
  obtain l4 := rev_load u.mem Pa (o := 4) (by decide)
  rw [BitVec.add_zero] at l0
  unfold loadBlock
  brun [hlr, ptrOff, eB, e0, e4, rB, r0, r4, hP, l0, l4]

/-- The halves to the block at the data pointer, the next block's pointer,
and the counter less one. -/
theorem storeBlock_run (u : State) {B P C : BitVec 32} {Ba Pa : Addr} (hlr : u.gpr .r3 = B)
    (eB : State.addr (B + BitVec.ofNat 32 36) = Ba + BitVec.ofNat 64 36)
    (eC : State.addr (B + BitVec.ofNat 32 40) = Ba + BitVec.ofNat 64 40)
    (e0 : State.addr (P + BitVec.ofNat 32 0) = Pa) (e4 : State.addr (P + BitVec.ofNat 32 4) = Pa + BitVec.ofNat 64 4)
    (wB : InRegions u.wr (Ba + BitVec.ofNat 64 36) 8)
    (w0 : InRegions u.wr Pa 8) (dj : Region.Disjoint ⟨Ba + BitVec.ofNat 64 36, 8⟩ ⟨Pa, 8⟩)
    (hP : u.mem.readW (Ba + BitVec.ofNat 64 36) 32 = P) (hC : u.mem.readW (Ba + BitVec.ofNat 64 40) 32 = C) :
    WP isa (.block storeBlock) u fun t =>
      t.mem = (((u.mem.writeW Pa (rev (u.gpr .r1))).writeW (Pa + BitVec.ofNat 64 4) (rev (u.gpr .r2))).writeW
          (Ba + BitVec.ofNat 64 36) (P + BitVec.ofNat 32 8)).writeW (Ba + BitVec.ofNat 64 40) (C - 1#32) ∧
        t.z = (C - 1#32 == 0#32) ∧ t.gpr .r3 = B ∧ t.gpr .r0 = u.gpr .r0 := by
  have s36 : Mem.Sep (Ba + BitVec.ofNat 64 40) 4 (Ba + BitVec.ofNat 64 36) 4 :=
    Offset.sep Ba (by decide) (by decide) (by decide)
  have sP : ∀ o, o ≤ 4 → Mem.Sep (Ba + BitVec.ofNat 64 40) 4 (Pa + BitVec.ofNat 64 o) 4 := fun o ho =>
    sep_of_disjoint ((dj.sub_left (Offset.sub Ba (d := 40) (n := 4) (e := 36) (k := 8) (by decide)
      (by decide))).sub_right (Offset.sub_base Pa (d := o) (n := 4) (k := 8) (by omega_arith)))
  have rB := inRegions_pre (n := 4) wB (by decide)
  have rC := inRegions_off (o := 4) (n := 4) wB (by decide)
  rw [Offset.add_add] at rC
  have r0 := inRegions_pre (n := 4) w0 (by decide)
  have r4 := inRegions_off (o := 4) (n := 4) w0 (by decide)
  unfold storeBlock countDown
  brun [hlr, ptrOff, cntOff, eB, eC, e0, e4, rB, rC, r0, r4, region_in (rs := u.rd) rB,
    region_in (rs := u.rd) rC, hP, hC]

/-- What the stores leave: the block's bytes, the pointer and the counter. -/
theorem stored_facts (m : Mem) (Ba Pa : Addr) (L R P C : BitVec 32)
    (dj : Region.Disjoint ⟨Ba + BitVec.ofNat 64 36, 8⟩ ⟨Pa, 8⟩) :
    let M := (((m.writeW Pa (rev L)).writeW (Pa + BitVec.ofNat 64 4) (rev R)).writeW
          (Ba + BitVec.ofNat 64 36) P).writeW (Ba + BitVec.ofNat 64 40) C
    M.readW (Ba + BitVec.ofNat 64 36) 32 = P ∧ M.readW (Ba + BitVec.ofNat 64 40) 32 = C ∧
      Frame [⟨Pa, 8⟩, ⟨Ba + BitVec.ofNat 64 36, 8⟩] m M ∧ blockAt M Pa = encodeBlock L R := by
  intro M
  obtain s36 : Mem.Sep (Ba + BitVec.ofNat 64 36) 4 (Ba + BitVec.ofNat 64 40) 4 :=
    Offset.sep Ba (by decide) (by decide) (by decide)
  refine ⟨by rw [Mem.readW_writeW_sep s36 (by decide), Mem.readW_writeW_self32],
    Mem.readW_writeW_self32 _ _ _, ?_, ?_⟩
  · have c0 : Region.Contains ⟨Pa, 8⟩ Pa (32 / 8) := Offset.contains_base Pa (d := 0) (n := 4) (k := 8)
      (by decide) (by decide) |> fun h => by rwa [BitVec.add_zero] at h
    obtain c4 : Region.Contains ⟨Pa, 8⟩ (Pa + BitVec.ofNat 64 4) (32 / 8) :=
      Offset.contains_base Pa (by decide) (by decide)
    obtain c36 : Region.Contains ⟨Ba + BitVec.ofNat 64 36, 8⟩ (Ba + BitVec.ofNat 64 36) (32 / 8) := by
      have := Offset.contains_base (Ba + BitVec.ofNat 64 36) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
      rwa [BitVec.add_zero] at this
    obtain c40 : Region.Contains ⟨Ba + BitVec.ofNat 64 36, 8⟩ (Ba + BitVec.ofNat 64 40) (32 / 8) := by
      have := Offset.contains_base (Ba + BitVec.ofNat 64 36) (d := 4) (n := 4) (k := 8) (by decide) (by decide)
      rwa [Offset.add_add] at this
    exact ((((Frame.refl _ m).writeW List.mem_cons_self _ c0).writeW List.mem_cons_self _ c4).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) _ c36).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ c40
  · refine blockAt_eq _ _ _ fun i hi => ?_
    obtain dk : ∀ o, o < 8 → Region.Disjoint ⟨Pa + BitVec.ofNat 64 o, 1⟩ ⟨Ba + BitVec.ofNat 64 36, 8⟩ :=
      fun o ho => (dj.sub_right (Offset.sub_base Pa (d := o) (n := 1) (k := 8) (by omega_arith))).symm
    obtain d36 := (dk i hi).sub_right (Offset.sub (e := 36) (k := 8) (d := 36) (n := 4) Ba (by decide) (by decide))
    obtain d40 := (dk i hi).sub_right (Offset.sub (e := 36) (k := 8) (d := 40) (n := 4) Ba (by decide) (by decide))
    simp only [M]
    rw [writeW32_other _ d40, writeW32_other _ d36, encodeBlock_getD _ _ hi]
    by_cases h4 : i < 4
    · rw [ite_eq_left h4, writeW32_other _ (Offset.disjoint Pa (d := i) (n := 1) (e := 4) (k := 4) (by omega_arith)
        (by omega_arith) (by decide)), st_byte _ _ _ h4, rev_byte _ h4]
    · rw [ite_eq_right h4, show i = 4 + (i - 4) by omega_arith, ← Offset.add_add, st_byte _ _ _ (by omega_arith),
        rev_byte _ (by omega_arith)]
      congr 2; omega_arith

/-! ## The loop -/

/-- A block's encryption (`up`) or decryption. -/
def blockOut (K : Schedule) (up : Bool) (b : Block) : Block :=
  if up then encryptBlock K b else decryptBlock K b

theorem blockOut_eq (K : Schedule) (up : Bool) (b : Block) :
    blockOut K up b = encodeBlock (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).1
      (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).2 := by
  cases up <;> rfl

/-- The block `b` of the data at `D`. -/
abbrev wAt (D : Addr) (b : Nat) : Addr := D + BitVec.ofNat 64 (8 * b)

/-- What ECB may assume: the schedule readable, the `n` blocks and the
working space writable, apart, none wrapping around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), 4168⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩, ⟨State.addr (s.gpr .r3), 256⟩]
  keyData : (⟨State.addr (s.gpr .r0), 4168⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩
  keyBuf : (⟨State.addr (s.gpr .r0), 4168⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 256⟩
  dataBuf : (⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 256⟩
  fitK : (s.gpr .r0).toNat + 4168 ≤ 2 ^ 32
  fitD : (s.gpr .r1).toNat + 8 * (s.gpr .r2).toNat ≤ 2 ^ 32
  fitB : (s.gpr .r3).toNat + 256 ≤ 2 ^ 32

/-- After `k` blocks from `s`. -/
structure EInv (s : State) (up : Bool) (k : Nat) (u : State) : Prop where
  le : k ≤ (s.gpr .r2).toNat
  r3 : u.gpr .r3 = s.gpr .r3
  r0 : u.gpr .r0 = s.gpr .r0
  ptr : u.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 32 = s.gpr .r1 + BitVec.ofNat 32 (8 * k)
  cnt : u.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 40) 32 =
    BitVec.ofNat 32 ((s.gpr .r2).toNat - k)
  saved : Spill.Saved u.mem (State.addr (s.gpr .r3)) s.gpr saved
  done : ∀ b < k, blockAt u.mem (wAt (State.addr (s.gpr .r1)) b) =
    blockOut (scheduleAt s.mem (State.addr (s.gpr .r0))) up (blockAt s.mem (wAt (State.addr (s.gpr .r1)) b))
  rest : ∀ b, k ≤ b → b < (s.gpr .r2).toNat →
    blockAt u.mem (wAt (State.addr (s.gpr .r1)) b) = blockAt s.mem (wAt (State.addr (s.gpr .r1)) b)
  frame : Frame [⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩, ⟨State.addr (s.gpr .r3), 256⟩] s.mem u.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem saved_slots : Spill.Slots 0 36 saved := by decide

theorem ecb_step {s : State} (h : EcbPre s) (up : Bool) {k : Nat} (hk : k < (s.gpr .r2).toNat) {u : State}
    (I : EInv s up k u) :
    WP isa (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock))) u fun u' =>
      EInv s up (k + 1) u' ∧ u'.z = (BitVec.ofNat 32 ((s.gpr .r2).toNat - (k + 1)) == 0#32) := by
  obtain ⟨hrd, hwr, kd, kb, db, fK, fD, fB⟩ := h
  obtain hrw : u.rd ++ u.wr = [⟨State.addr (s.gpr .r0), 4168⟩,
      ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩, ⟨State.addr (s.gpr .r3), 256⟩] := by
    rw [I.rd, I.wr, hrd, hwr]; rfl
  obtain dR : (⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩ : Region) ∈ u.wr := by
    rw [I.wr, hwr]; exact List.mem_cons_self
  obtain bR : (⟨State.addr (s.gpr .r3), 256⟩ : Region) ∈ u.wr := by
    rw [I.wr, hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  -- addresses
  obtain eB : State.addr (s.gpr .r3 + BitVec.ofNat 32 36) = State.addr (s.gpr .r3) + BitVec.ofNat 64 36 :=
    addr_add (by omega_arith)
  obtain eC : State.addr (s.gpr .r3 + BitVec.ofNat 32 40) = State.addr (s.gpr .r3) + BitVec.ofNat 64 40 :=
    addr_add (by omega_arith)
  obtain eP : State.addr (s.gpr .r1 + BitVec.ofNat 32 (8 * k)) = wAt (State.addr (s.gpr .r1)) k :=
    addr_add (by omega_arith)
  obtain e0 : State.addr (s.gpr .r1 + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 0) =
      wAt (State.addr (s.gpr .r1)) k := by rw [BitVec.add_zero, eP]
  obtain e4 : State.addr (s.gpr .r1 + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 4) =
      wAt (State.addr (s.gpr .r1)) k + BitVec.ofNat 64 4 := by
    rw [ofs_add, addr_add (by omega_arith), Offset.add_add]
  obtain wK : InRegions u.wr (wAt (State.addr (s.gpr .r1)) k) 8 :=
    ⟨_, dR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain wB : InRegions u.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 8 :=
    ⟨_, bR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain subK : Region.Sub ⟨wAt (State.addr (s.gpr .r1)) k, 8⟩ ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩ :=
    Offset.sub_base _ (by omega_arith)
  obtain subB : Region.Sub ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩ ⟨State.addr (s.gpr .r3), 256⟩ :=
    Offset.sub_base _ (by omega_arith)
  obtain dj : Region.Disjoint ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩ ⟨wAt (State.addr (s.gpr .r1)) k, 8⟩ :=
    ((db.sub_left subK).sub_right subB).symm
  -- the block in
  apply WP.seq
  refine WP.mono (WP.keep [.r1, .r2, .r12] (loadBlock_run u I.r3 eB e0 e4
    (region_in (inRegions_pre wB (by decide))) (region_in (inRegions_pre wK (by decide)))
    (region_in (inRegions_off (o := 4) (n := 4) wK (by decide))) I.ptr) (by decide))
    fun u₁ ⟨⟨l1, l2, lm⟩, lk⟩ => ?_
  -- the cipher
  obtain hK : scheduleAt u.mem (State.addr (s.gpr .r0)) = scheduleAt s.mem (State.addr (s.gpr .r0)) :=
    scheduleAt_eq_of_frame _ I.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kd
      · exact kb
  obtain CE : CipherEnv u₁ := by
    refine ⟨by rw [lk.gpr (by decide), I.r0]; exact fK, fun o ho => ?_, by rw [lk.gpr (by decide), I.r3]; omega_arith,
      fun o ho => ?_, ?_⟩
    · rw [keep_reads lk, hrw, lk.gpr (by decide), I.r0]
      exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [lk.gpr (by decide), I.r3, lk.2.2.1, Offset.add_add]
      exact ⟨_, bR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [fRegion, lk.gpr (by decide), lk.gpr (by decide), I.r0, I.r3]
      exact kb.sub_right (Offset.sub_base _ (by decide))
  apply WP.seq
  refine WP.mono (cipher_run CE up) fun u₂ ⟨c12, ck, cf⟩ => ?_
  rw [fRegion, lk.gpr (by decide), I.r3, lm] at cf
  -- the working space's pointer and counter, past F's words
  have cslot (o : Nat) (ho : o + 4 ≤ 48) : u₂.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 o) 32 =
      u.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 o) 32 :=
    cf.readW (r := ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl ho) (by omega_using [ho]) (by decide)) (by decide)
  -- the block out
  obtain k₂ : Keep cRegs u u₂ := (lk.trans ck).mono (by decide)
  refine WP.mono (WP.keep [.r1, .r2, .r11, .r12] (storeBlock_run u₂ (C := BitVec.ofNat 32 ((s.gpr .r2).toNat - k))
    (by rw [k₂.gpr (by decide), I.r3]) eB eC e0 e4 (by rw [k₂.2.2.1]; exact wB) (by rw [k₂.2.2.1]; exact wK) dj
    ((cslot 36 (by decide)).trans I.ptr) ((cslot 40 (by decide)).trans I.cnt)) (by decide))
    fun u₃ ⟨⟨sm, sz, slr, s0⟩, sk⟩ => ?_
  obtain ⟨M36, M40, MF, MB⟩ := stored_facts u₂.mem (State.addr (s.gpr .r3)) (wAt (State.addr (s.gpr .r1)) k)
    (u₂.gpr .r1) (u₂.gpr .r2) (s.gpr .r1 + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 8)
    (BitVec.ofNat 32 ((s.gpr .r2).toNat - k) - 1#32) dj
  rw [← sm] at M36 M40 MF MB
  obtain MF : Frame [⟨wAt (State.addr (s.gpr .r1)) k, 8⟩, ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩,
      ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 48, 32⟩] u.mem u₃.mem :=
    (cf.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)).trans (MF.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl))
  obtain hcnt : BitVec.ofNat 32 ((s.gpr .r2).toNat - k) - 1#32 = BitVec.ofNat 32 ((s.gpr .r2).toNat - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith
  obtain dOther : ∀ b, b < (s.gpr .r2).toNat → b ≠ k → ∀ r ∈ [(⟨wAt (State.addr (s.gpr .r1)) k, 8⟩ : Region),
      ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩, ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 48, 32⟩],
      (⟨wAt (State.addr (s.gpr .r1)) b, 8⟩ : Region).Disjoint r :=
    fun b hb hne r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      · exact (db.sub_left (Offset.sub_base _ (by omega_arith))).sub_right subB
      · exact (db.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by decide))
  obtain other : ∀ b, b < (s.gpr .r2).toNat → b ≠ k →
      blockAt u₃.mem (wAt (State.addr (s.gpr .r1)) b) = blockAt u.mem (wAt (State.addr (s.gpr .r1)) b) :=
    fun b hb hne => blockAt_frame MF (dOther b hb hne)
  obtain u₁r0 : u₁.gpr .r0 = s.gpr .r0 := by rw [lk.gpr (by decide), I.r0]
  refine ⟨⟨by omega_arith, slr, by rw [s0, k₂.gpr (by decide), I.r0], by rw [M36, ofs_add]; congr 2,
    by rw [M40, hcnt], ?_, fun b hb => ?_, fun b h1 h2 => ?_, ?_, ?_, ?_⟩, by rw [sz, hcnt]⟩
  · refine I.saved.frame saved_slots MF fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [BitVec.add_zero]
      exact (db.symm.sub_left (Region.sub_prefix (by decide))).sub_right subK
    · exact Offset.disjoint _ (by decide) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by decide) (by omega_arith) (by omega_arith)
  · by_cases hbk : b = k
    · subst hbk
      rw [lm, u₁r0, l1, l2] at c12
      rw [MB, blockOut_eq, ← I.rest b (by omega_arith) hk, ← hK, ← c12]
    · rw [other b (by omega_arith) hbk]; exact I.done b (by omega_arith)
  · rw [other b h2 (by omega_arith)]; exact I.rest b (by omega_arith) h2
  · refine I.frame.trans (MF.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, subK⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subB⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by decide)⟩
  · rw [sk.2.1, k₂.2.1, I.rd]
  · rw [sk.2.2.1, k₂.2.2.1, I.wr]


theorem saved_restorable : Spill.Restorable .r3 saved := by decide

theorem restore_eq : restore = saved.map (fun (p : Reg × Nat) => Instr.ldr p.1 .r3 p.2) := rfl
theorem save_eq (rest : List Instr) :
    save ++ rest = saved.map (fun p => Instr.str p.1 .r3 p.2) ++ rest := rfl

/-- Restoring our caller's registers from the working space at `r3`. -/
theorem restore_run {u : State} {g : Reg → BitVec 32}
    (fit : (u.gpr .r3).toNat + 36 ≤ 2 ^ 32)
    (hin : ∀ d, d + 4 ≤ 36 → InRegions (u.rd ++ u.wr) (State.addr (u.gpr .r3) + BitVec.ofNat 64 d) 4)
    (hsv : Spill.Saved u.mem (State.addr (u.gpr .r3)) g saved) :
    WP isa (.block restore) u fun t => (∀ r ∈ preserved, t.gpr r = g r) ∧ t.mem = u.mem := by
  rw [restore_eq]
  refine WP.mono (Spill.restore_block_ok saved_slots saved_restorable fit (fun d _ h => hin d h) hsv)
    fun t ⟨ht, _, hm, _⟩ => ⟨fun r hr => ?_, hm⟩
  have : r ∈ saved.map Prod.fst := by revert r; decide
  exact Spill.restored_reg ht this

theorem ecb_blocks (K : Schedule) (up : Bool) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, blockAt m' (wAt D b) = blockOut K up (blockAt m (wAt D b))) :
    blocksAt m' D n = Spec.Blowfish.ecb K (if up then .encrypt else .decrypt) (blocksAt m D n) := by
  simp only [blocksAt, Spec.Blowfish.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases up <;> rfl

/-- What ECB guarantees. -/
structure EcbPost (s : State) (up : Bool) (t : State) : Prop where
  regs : ∀ r ∈ preserved, t.gpr r = s.gpr r
  blocks : blocksAt t.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
    Spec.Blowfish.ecb (scheduleAt s.mem (State.addr (s.gpr .r0))) (if up then .encrypt else .decrypt)
      (blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)

theorem ecb_correct {s : State} (h : EcbPre s) (up : Bool) : WP isa (Impl.Blowfish.Arm.ecb up) s (EcbPost s up) := by
  have H := h
  obtain ⟨hrd, hwr, kd, kb, db, fK, fD, fB⟩ := H
  obtain bR : (⟨State.addr (s.gpr .r3), 256⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain subB : Region.Sub ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩ ⟨State.addr (s.gpr .r3), 256⟩ :=
    Offset.sub_base _ (by omega_arith)
  obtain wB : InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 8 :=
    ⟨_, bR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  unfold Impl.Blowfish.Arm.ecb
  apply WP.seq
  rw [save_eq]
  refine Spill.save_slots_ok saved_slots (by omega_arith) (fun d _ hd =>
    ⟨_, bR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) ?_
  let s₁ : State := { s with mem := Spill.saveMem s.mem (State.addr (s.gpr .r3)) s.gpr saved }
  obtain eB : State.addr (s.gpr .r3 + BitVec.ofNat 32 36) = State.addr (s.gpr .r3) + BitVec.ofNat 64 36 :=
    addr_add (by omega_arith)
  obtain eC : State.addr (s.gpr .r3 + BitVec.ofNat 32 40) = State.addr (s.gpr .r3) + BitVec.ofNat 64 40 :=
    addr_add (by omega_arith)
  obtain w36 : InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 4 := inRegions_pre wB (by decide)
  obtain w40 : InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 40) 4 := by
    have := inRegions_off (o := 4) (n := 4) wB (by decide); rwa [Offset.add_add] at this
  have g₁ : s₁.gpr = s.gpr := rfl
  refine WP.mono (WP.keep [.lr] (Q := fun u => u.mem = ((Spill.saveMem s.mem (State.addr (s.gpr .r3)) s.gpr saved).writeW (State.addr (s.gpr .r3) + BitVec.ofNat 64 36)
      (s.gpr .r1)).writeW (State.addr (s.gpr .r3) + BitVec.ofNat 64 40) (s.gpr .r2) ∧
      u.z = (s.gpr .r2 - 0#32 == 0#32)) (by brun [g₁, eB, eC, w36, w40, ptrOff, cntOff]) (by decide))
    fun u₀ ⟨⟨um, uz⟩, uk⟩ => ?_
  -- the loop's start
  obtain s36 : Mem.Sep (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 4 (State.addr (s.gpr .r3) + BitVec.ofNat 64 40) 4 :=
    Offset.sep _ (by decide) (by decide) (by decide)
  obtain F0 : Frame [⟨State.addr (s.gpr .r3), 256⟩] s.mem u₀.mem := by
    obtain f₁ : Frame [⟨State.addr (s.gpr .r3), 256⟩] s.mem s₁.mem :=
      (Spill.saveMem_frame s.mem _ s.gpr (L := 36) (by decide) saved (by decide)).sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    rw [um]
    exact (f₁.writeW List.mem_cons_self _ (Offset.contains_base _ (d := 36) (n := 4) (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (d := 40) (n := 4) (by decide) (by decide))
  obtain I0 : EInv s up 0 u₀ := by
    refine ⟨Nat.zero_le _, by rw [uk.gpr (by decide)], by rw [uk.gpr (by decide)], ?_, ?_, ?_, fun b hb => absurd hb (Nat.not_lt_zero _),
      fun b _ hb => blockAt_frame F0 fun r hr => ?_, F0.mono fun r hr => ?_, uk.2.1, uk.2.2.1⟩
    · rw [um, Mem.readW_writeW_sep s36 (by decide), Mem.readW_writeW_self32, Nat.mul_zero]; simp
    · rw [um, Mem.readW_writeW_self32, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · have sv := Spill.saveMem_saved (State.addr (s.gpr .r3)) s.gpr s.mem saved saved_slots
      refine sv.frame saved_slots (rs := [⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩]) ?_ fun r hr => ?_
      · rw [um]
        exact ((Frame.refl _ _).writeW List.mem_cons_self _
          (Offset.contains (e := 36) (k := 8) (d := 36) (n := 4) _ (by decide) (by decide) (by decide))).writeW
          List.mem_cons_self _ (Offset.contains (e := 36) (k := 8) (d := 40) (n := 4) _ (by decide) (by decide) (by decide))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact Offset.disjoint _ (by decide) (by decide) (by omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact (db.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact List.mem_cons_of_mem _ List.mem_cons_self
  -- the end
  obtain fin : ∀ u, EInv s up (s.gpr .r2).toNat u → WP isa (.block restore) u (EcbPost s up) := fun u I => by
    refine WP.mono (restore_run (u := u) (by rw [I.r3]; omega_arith) (fun d hd => ?_) (by rw [I.r3]; exact I.saved))
      fun t ⟨tr, tm⟩ =>
      ⟨tr, ecb_blocks _ _ _ _ _ _ fun b hb => by rw [tm]; exact I.done b hb⟩
    rw [I.rd, I.wr, hrd, hwr, I.r3]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  apply WP.seq
  refine WP.ite (s.gpr .r2 - 0#32 == 0#32) (by rw [eval_eq, uz]) (fun hz => ?_) (fun hz => ?_)
  · have hn : (s.gpr .r2).toNat = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz); simpa using this
    exact WP.block_nil (fin u₀ (by rw [hn]; exact I0))
  · have hn : 0 < (s.gpr .r2).toNat := by
      obtain h0 : s.gpr .r2 ≠ 0#32 := by intro e; rw [e] at hz; simp at hz
      have : (s.gpr .r2).toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq e)
      omega_arith
    refine WP.mono (WP.loop (M := isa) (Q := EInv s up (s.gpr .r2).toNat)
      (fun (m : Nat) (u : State) => ∃ k, k < (s.gpr .r2).toNat ∧ m = (s.gpr .r2).toNat - k ∧ EInv s up k u)
      ?_ _ u₀ ⟨0, hn, rfl, I0⟩) fin
    intro m u ⟨k, hk, hm, I⟩
    refine WP.mono (ecb_step h up hk I) fun u' ⟨I', zu⟩ => ?_
    rw [eval_ne, zu]
    by_cases e : k + 1 = (s.gpr .r2).toNat
    · left
      exact ⟨by rw [e, Nat.sub_self]; rfl, e ▸ I'⟩
    · right
      obtain nz : BitVec.ofNat 32 ((s.gpr .r2).toNat - (k + 1)) ≠ 0#32 := by
        intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_arith
      exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega_arith, k + 1, by omega_arith, rfl, I'⟩

end VG.Proof.Blowfish.Arm
