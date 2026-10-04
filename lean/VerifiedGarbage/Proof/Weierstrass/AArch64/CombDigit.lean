import VerifiedGarbage.Impl.Weierstrass.AArch64.Comb
import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits

/-!
# The comb on AArch64: digits and masks

Iteration `j` reads nibble `j` of the scalar from its table of bits by
Horner's rule (`nibble_ok`), turns it into the magnitude `|k_j - 8|`
(`magnitude_ok`), and sets `maskReg m` to all ones exactly for `m` that
magnitude, for `m = 0 … 8` (`masks_ok`); `digit_ok` is all three.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open CombCfg

/-- All ones if `b`, else zero. -/
def bmask (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

/-- `|k - 8|`, the magnitude of the digit of the nibble `k`. -/
def mag (k : Nat) : Nat := if 8 ≤ k then k - 8 else 8 - k

theorem mag_le {k : Nat} (h : k < 16) : mag k ≤ 8 := by unfold mag; split <;> omega

/-! ## The nibble -/

theorem shl2 {j : Nat} (hj : j < 2 ^ 62) : BitVec.ofNat 64 j <<< 2 = BitVec.ofNat 64 (4 * j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]
  omega

/-- `x16 = x0 + 4 x19`. -/
theorem combIndex_ok (s : State) {base : Addr} {size : Nat} (hs : Scr s base size) {j : Nat}
    (hj : j < 2 ^ 62) (hb : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block ([.lsl .x .x16 .x19 2, .add .x .x16 .x0 .x16] : List Instr)) s fun t =>
      t.gpr .x16 = off base (4 * j) ∧ Keeps [.x16] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (2 : Nat) < Size.x.bits from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    hb, shl2 hj, hs.x0, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem bool_ext (b : Bool) :
    (((if b then 1 else 0 : BitVec 8)).setWidth 32).setWidth 64 = BitVec.ofNat 64 b.toNat := by
  cases b <;> decide

/-- Horner's rule on four bits. -/
theorem horner (b0 b1 b2 b3 : Bool) :
    BitVec.ofNat 64 b3.toNat + BitVec.ofNat 64 b3.toNat + BitVec.ofNat 64 b2.toNat +
        (BitVec.ofNat 64 b3.toNat + BitVec.ofNat 64 b3.toNat + BitVec.ofNat 64 b2.toNat) +
        BitVec.ofNat 64 b1.toNat +
      (BitVec.ofNat 64 b3.toNat + BitVec.ofNat 64 b3.toNat + BitVec.ofNat 64 b2.toNat +
          (BitVec.ofNat 64 b3.toNat + BitVec.ofNat 64 b3.toNat + BitVec.ofNat 64 b2.toNat) +
        BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b0.toNat =
      BitVec.ofNat 64 (b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

/-- The nibble from its bits. -/
theorem nib_eq (k j : Nat) : nib k j = (k.testBit (4 * j)).toNat + 2 * (k.testBit (4 * j + 1)).toNat +
    4 * (k.testBit (4 * j + 2)).toNat + 8 * (k.testBit (4 * j + 3)).toNat := by
  have hb : ∀ i, (k.testBit (4 * j + i)).toNat = k / 16 ^ j / 2 ^ i % 2 := fun i => by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul,
      show (16 : Nat) ^ j = 2 ^ (4 * j) by rw [Nat.pow_mul], ← Nat.pow_add]
    rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ (4 * j + i)) with h | h <;> simp [h]
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  simp only [Nat.add_zero, Nat.pow_zero, Nat.div_one] at h0
  rw [h0, h1, h2, h3, nib]
  omega

/-- `x2` = nibble `j` of `k`, from the table of `k`'s bits at `d`. -/
theorem nibble_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : CombCfg)
    {k j N : Nat} (hj : 4 * j + 4 ≤ N) (hN : K.bits + N ≤ size) (hb4 : K.bits + 3 < 4096)
    (hx : s.gpr .x19 = BitVec.ofNat 64 j)
    (hbits : ∀ t < N, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (nibble K)) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (nib k j) ∧ Keeps [.x2, .x4, .x16] s t := by
  have hn := hs.nowrap
  have hsz := hs.enc
  rw [nibble, ← List.singleton_append (l := [Instr.add .x .x16 .x0 .x16, _, _, _, _, _, _, _, _, _, _]),
    show ([Instr.lsl .x .x16 .x19 2] : List Instr) ++ Instr.add .x .x16 .x0 .x16 ::
      [.ldrb .x2 .x16 (K.bits + 3), .add .x .x2 .x2 .x2, .ldrb .x4 .x16 (K.bits + 2),
      .add .x .x2 .x2 .x4, .add .x .x2 .x2 .x2, .ldrb .x4 .x16 (K.bits + 1),
      .add .x .x2 .x2 .x4, .add .x .x2 .x2 .x2, .ldrb .x4 .x16 K.bits, .add .x .x2 .x2 .x4] =
      ([.lsl .x .x16 .x19 2, .add .x .x16 .x0 .x16] : List Instr) ++
      [.ldrb .x2 .x16 (K.bits + 3), .add .x .x2 .x2 .x2, .ldrb .x4 .x16 (K.bits + 2),
      .add .x .x2 .x2 .x4, .add .x .x2 .x2 .x2, .ldrb .x4 .x16 (K.bits + 1),
      .add .x .x2 .x2 .x4, .add .x .x2 .x2 .x2, .ldrb .x4 .x16 K.bits, .add .x .x2 .x2 .x4] from rfl,
    WP.block_append_iff]
  refine WP.mono (combIndex_ok s hs (by omega) hx) fun a ⟨a16, ka⟩ => ?_
  have hr : ∀ i < 4, InRegions (a.rd ++ a.wr) (off base (K.bits + (4 * j + i))) 1 := fun i hi =>
    ⟨_, List.mem_append_right _ (ka.wr ▸ hs.wr), hs.contains (by omega) (by decide)⟩
  have he : ∀ i, a.gpr .x16 + BitVec.ofNat 64 (K.bits + i) = off base (K.bits + (4 * j + i)) :=
    fun i => by
      rw [a16, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact congrArg (off base) (by omega)
  have hv : ∀ i < 4, ((a.mem.read (off base (K.bits + (4 * j + i))) 1).setWidth 32).setWidth 64 =
      BitVec.ofNat 64 (k.testBit (4 * j + i)).toNat := fun i hi => by
    rw [read1_zext, ka.mem, hbits _ (by omega)]
    exact (bool_ext _).trans rfl
  have e0 := he 0
  have e1 := he 1
  have e2 := he 2
  have e3 := he 3
  simp only [Nat.add_zero] at e0
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  have r0 := hr 0 (by decide)
  have r1 := hr 1 (by decide)
  have r2 := hr 2 (by decide)
  have r3 := hr 3 (by decide)
  simp only [Nat.add_zero] at v0 r0
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bits, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, Nat.mod_one,
    show K.bits + 3 < 4096 * 1 by omega, show K.bits + 2 < 4096 * 1 by omega,
    show K.bits + 1 < 4096 * 1 by omega, show K.bits < 4096 * 1 by omega,
    and_self, e0, e1, e2, e3, r0, r1, r2, r3, v0, v1, v2, v3,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, ka.mem, ka.rd, ka.wr, ka.sp⟩⟩
  · rw [horner, nib_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, ite_false]
    exact ka.gpr r (by simpa using hr.2.2)

/-! ## The magnitude -/

private theorem mag_fact : ∀ n < 16,
    (BitVec.ofNat 64 n - BitVec.ofNat 64 8 ^^^
        (((0 : BitVec 16).setWidth 64 <<< (16 * 0)) - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63)) -
      (((0 : BitVec 16).setWidth 64 <<< (16 * 0)) - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63) =
      BitVec.ofNat 64 (mag n) := by
  decide +kernel

/-- `x2 = |k - 8|` from the nibble `k` in `x2`, and `x9 = 0`. -/
theorem magnitude_ok (s : State) {n : Nat} (hn : n < 16) (hx : s.gpr .x2 = BitVec.ofNat 64 n) :
    WP isa (.block magnitude) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (mag n) ∧ t.gpr .x9 = 0 ∧ Keeps [.x2, .x3, .x4, .x9] s t := by
  apply WP.of_runBlock
  simp only [magnitude, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show (8 : Nat) < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    show 16 * 0 < 64 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨mag_fact n hn, by decide, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-! ## The masks -/

private theorem lt_fact : ∀ a < 9, ∀ m < 8,
    (BitVec.ofNat 64 a - BitVec.ofNat 64 (m + 1)) >>> 63 -
      (BitVec.ofNat 64 a - BitVec.ofNat 64 (m + 2)) >>> 63 = bmask (decide (a = m + 1)) := by
  decide +kernel

private theorem ends_fact : ∀ a < 9,
    (BitVec.ofNat 64 a - BitVec.ofNat 64 8) >>> 63 - BitVec.ofNat 64 1 = bmask (decide (a = 8)) ∧
    0 - (BitVec.ofNat 64 a - BitVec.ofNat 64 1) >>> 63 = bmask (decide (a = 0)) := by
  decide +kernel

/-- The masks, from the magnitude `a ≤ 8` in `x2` and `x9 = 0`. -/
theorem masks_ok (s : State) {a : Nat} (ha : a < 9) (hx : s.gpr .x2 = BitVec.ofNat 64 a)
    (h9 : s.gpr .x9 = 0) :
    WP isa (.block masks) s fun t =>
      (∀ m ≤ 8, t.gpr (maskReg m) = bmask (decide (a = m))) ∧ Keeps maskRegs s t := by
  have l := lt_fact a ha
  apply WP.of_runBlock
  simp only [masks, maskRegs, maskReg, List.range, List.range.loop,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.getD_cons_zero, List.getD_cons_succ,
    Nat.reduceAdd, Nat.reduceLT, ↓reduceIte,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show (63 : Nat) < 64 from by decide, show ∀ k < 9, k < 4096 from fun k hk => by omega,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, h9, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun m hm => ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, ite_true, ite_false,
        reduceCtorEq] <;>
      first
      | exact (ends_fact a ha).1
      | exact (ends_fact a ha).2
      | exact l _ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

/-- The digit's masks: the masks of `|k_j - 8|` for nibble `j` of `k`. -/
theorem digit_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : CombCfg)
    {k j N : Nat} (hj : 4 * j + 4 ≤ N) (hN : K.bits + N ≤ size) (hb4 : K.bits + 3 < 4096)
    (hx : s.gpr .x19 = BitVec.ofNat 64 j)
    (hbits : ∀ t < N, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (digit K)) s fun t =>
      (∀ m ≤ 8, t.gpr (maskReg m) = bmask (decide (mag (nib k j) = m))) ∧
      Keeps (.x2 :: .x4 :: .x9 :: .x16 :: maskRegs) s t := by
  rw [digit, List.append_assoc, WP.block_append_iff]
  refine WP.mono (nibble_ok hs K hj hN hb4 hx hbits) fun a ⟨a2, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (magnitude_ok a (nib_lt k j) a2) fun b ⟨b2, b9, kb⟩ => ?_
  refine WP.mono (masks_ok b (Nat.lt_succ_of_le (mag_le (nib_lt k j))) b2 b9) fun t ⟨tm, kt⟩ =>
    ⟨tm, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩

end VG.Proof.Weierstrass.AArch64
