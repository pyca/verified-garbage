module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Words.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.TCB.RISCV64.Isa
import all Init.Data.Nat.Bitwise.Basic

/-!
# RISC-V: words of argument buffers, a byte at a time

Untrusted: everything here is checked by Lean. The effect of the sequences
of `Impl/Words/RISCV64.lean`, each as one equation of the final state, with
the writes kept folded (`State.write`), so that callers read registers
through them with `RegUpd`:
* `loadBE32_ok`: the big-endian word `beWord` (the bytes in the order of
  FIPS 180-4's `parseBlock` and SM3's and SHA-1's), zero-extended;
* `loadLE32_ok`: the little-endian word `readW`, zero-extended;
* `storeLE32_ok`: the low word of a register, written as `writeW`;
* `li32_ok`: a constant loaded by `li32`;

and `rotr_shifts`, a rotation as two word shifts.
-/

@[expose] public section

namespace VG.RISCV64.ByteLoad

open VG.Impl.Words.RISCV64

/-- The big-endian word of the bytes at `p + off`, …, `p + off + 3`. -/
def beWord (m : Mem) (p : Addr) (off : Nat) : BitVec 32 :=
  m (p + BitVec.ofNat 64 off) ++ m (p + BitVec.ofNat 64 (off + 1)) ++
    m (p + BitVec.ofNat 64 (off + 2)) ++ m (p + BitVec.ofNat 64 (off + 3))

/-! ## Bit vectors -/

set_option linter.unusedSimpArgs false in
theorem be_bytes (b0 b1 b2 b3 : BitVec 8) :
    b0.setWidth 64 <<< 24 ||| b1.setWidth 64 <<< 16 ||| b2.setWidth 64 <<< 8 ||| b3.setWidth 64 =
      (b0 ++ b1 ++ b2 ++ b3 : BitVec 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h8 : i < 8 <;> by_cases h16 : i < 16 <;> by_cases h24 : i < 24 <;>
    by_cases h32 : i < 32 <;>
    simp (disch := omega) only [h8, h16, h24, h32, BitVec.getLsbD_of_ge, decide_true, decide_false,
      Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or,
      Bool.not_true, Bool.not_false, ite_true, ite_false, hi, Nat.sub_sub, Nat.reduceAdd,
      show i - 8 < 64 by omega, show i - 16 < 64 by omega, show i - 24 < 64 by omega,
      show (i - 8 < 8) ↔ i < 16 by omega, show (i - 16 < 8) ↔ i < 24 by omega]

set_option linter.unusedSimpArgs false in
theorem le_bytes (b0 b1 b2 b3 : BitVec 8) :
    b0.setWidth 64 ||| b1.setWidth 64 <<< 8 ||| b2.setWidth 64 <<< 16 ||| b3.setWidth 64 <<< 24 =
      (b3 ++ b2 ++ b1 ++ b0 : BitVec 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h8 : i < 8 <;> by_cases h16 : i < 16 <;> by_cases h24 : i < 24 <;>
    by_cases h32 : i < 32 <;>
    simp (disch := omega) only [h8, h16, h24, h32, BitVec.getLsbD_of_ge, decide_true, decide_false,
      Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or,
      Bool.not_true, Bool.not_false, ite_true, ite_false, hi, Nat.sub_sub, Nat.reduceAdd,
      show i - 8 < 64 by omega, show i - 16 < 64 by omega, show i - 24 < 64 by omega,
      show (i - 8 < 8) ↔ i < 16 by omega, show (i - 16 < 8) ↔ i < 24 by omega]

/-- Byte `k` of a register's low word, as a right shift leaves it. -/
theorem byte_shift (x : BitVec 64) (k : Nat) (hk : k < 4) :
    (x >>> (8 * k)).setWidth 8 = (x.setWidth 32).extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb']
  simp [hi, show 8 * k + i < 32 by omega]

/-- The low word of a constant `li32` loads. -/
theorem li32_val (w : BitVec 32) : (hi20 w ++ (0 : BitVec 12)) + BitVec.ofInt 32 (lo12 w) = w := by
  apply BitVec.eq_of_toNat_eq
  have hw := w.isLt
  unfold hi20 lo12
  rw [BitVec.toNat_add, BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, show (0 : BitVec 12).toNat = 0 from rfl, Nat.or_zero,
    Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceAdd]
  split
  · rw [BitVec.toNat_ofInt]; omega
  · rw [BitVec.toNat_ofInt]; omega

theorem lo12_imm (w : BitVec 32) : imm12 (lo12 w) := by
  unfold lo12 imm12; split <;> omega

/-- A word rotated right by `r < 32`, as `srliw`, `slliw` and `xor` (or `or`)
compute it in the low word: the two shifts' bits do not overlap. -/
theorem rotr_shifts (x : BitVec 32) {r : Nat} (h : r < 32) :
    x >>> r ^^^ x <<< (32 - r) = x.rotateRight r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt h]
  by_cases hr : i < 32 - r
  · simp [hr, hi]
  · simp [hr, hi, BitVec.getLsbD_of_ge x (r + i) (by omega)]

/-! ## Memory -/

/-- Four byte writes at consecutive addresses are a word's. -/
theorem write4 (m : Mem) (a : Addr) (v : BitVec 32) :
    (((m.write a 1 (v.extractLsb' 0 8)).write (a + 1) 1 (v.extractLsb' 8 8)).write (a + 2) 1
      (v.extractLsb' 16 8)).write (a + 3) 1 (v.extractLsb' 24 8) = m.writeW a v := by
  funext x
  simp only [Mem.write, Mem.writeW]
  have e1 : x - (a + 1) = (x - a) - 1 := by bv_omega
  have e2 : x - (a + 2) = (x - a) - 2 := by bv_omega
  have e3 : x - (a + 3) = (x - a) - 3 := by bv_omega
  rw [e1, e2, e3]
  generalize x - a = y
  rcases (show y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ 4 ≤ y.toNat by bv_omega) with rfl | rfl | rfl | rfl | h
  · simp
  · simp
  · simp
  · simp
  · have h1 : ¬ (y - 1).toNat < 1 := by bv_omega
    have h2 : ¬ (y - 2).toNat < 1 := by bv_omega
    have h3 : ¬ (y - 3).toNat < 1 := by bv_omega
    simp only [h1, h2, h3, show ¬ y.toNat < 1 by omega, show ¬ y.toNat < 4 by omega, ite_false]

/-- `write4` at the offsets of `storeLE32`. -/
theorem write4_off (m : Mem) (p : Addr) (off : Nat) (v : BitVec 32) :
    (((m.write (p + BitVec.ofNat 64 off) 1 (v.extractLsb' 0 8)).write
      (p + BitVec.ofNat 64 (off + 1)) 1 (v.extractLsb' 8 8)).write
      (p + BitVec.ofNat 64 (off + 2)) 1 (v.extractLsb' 16 8)).write
      (p + BitVec.ofNat 64 (off + 3)) 1 (v.extractLsb' 24 8) =
    m.writeW (p + BitVec.ofNat 64 off) v := by
  have e : ∀ k, p + BitVec.ofNat 64 (off + k) = p + BitVec.ofNat 64 off + BitVec.ofNat 64 k := by
    intro k; rw [BitVec.ofNat_add, BitVec.add_assoc]
  rw [e 1, e 2, e 3]
  exact write4 m _ v

/-- A one-byte read. -/
theorem read_one (m : Mem) (a : Addr) : (m.read a 1).setWidth 64 = (m a).setWidth 64 := by
  show ((0#0 : BitVec 0) ++ m a).setWidth 64 = _
  rw [BitVec.zero_width_append]; rfl

/-- A little-endian word, from its bytes at the offsets of `loadLE32`. -/
theorem readW_bytes (m : Mem) (p : Addr) (off : Nat) :
    m.readW (p + BitVec.ofNat 64 off) 32 =
      m (p + BitVec.ofNat 64 (off + 3)) ++ m (p + BitVec.ofNat 64 (off + 2)) ++
        m (p + BitVec.ofNat 64 (off + 1)) ++ m (p + BitVec.ofNat 64 off) := by
  have e : ∀ k, p + BitVec.ofNat 64 off + BitVec.ofNat 64 k = p + BitVec.ofNat 64 (off + k) := by
    intro k; rw [BitVec.ofNat_add, BitVec.add_assoc]
  show ((((0#0 : BitVec 0) ++ m (p + BitVec.ofNat 64 off + 1 + 1 + 1)) ++
    m (p + BitVec.ofNat 64 off + 1 + 1)) ++ m (p + BitVec.ofNat 64 off + 1) ++
    m (p + BitVec.ofNat 64 off)).setWidth 32 = _
  rw [BitVec.zero_width_append, ← e 3, ← e 2, ← e 1, BitVec.add_assoc (p + _) 1 1,
    BitVec.add_assoc (p + _) (1 + 1) 1]
  rfl

/-- Every byte of a 4-byte access within a region. -/
theorem contains_byte {r : Region} {p : Addr} {off : Nat} (h : r.Contains (p + BitVec.ofNat 64 off) 4)
    {k : Nat} (hk : k < 4) : r.Contains (p + BitVec.ofNat 64 (off + k)) 1 := by
  refine h.byte ?_
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  omega

/-- Every byte of a 4-byte access within the regions. -/
theorem in_byte {rs : List Region} {p : Addr} {off : Nat} (h : InRegions rs (p + BitVec.ofNat 64 off) 4)
    {k : Nat} (hk : k < 4) : InRegions rs (p + BitVec.ofNat 64 (off + k)) 1 := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, contains_byte hc hk⟩

/-! ## The sequences -/

variable {s : State}

theorem loadBE32_ok {d tmp n : Reg} {off : Nat} (hdn : d ≠ n) (htn : tmp ≠ n) (hdt : d ≠ tmp)
    (ho : off + 3 < 2048) (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 4) :
    WP isa (.block (loadBE32 d tmp n off)) s (· =
      (s.write tmp ((s.mem (s.gpr n + BitVec.ofNat 64 (off + 3))).setWidth 64)).write d
        ((beWord s.mem (s.gpr n) off).setWidth 64)) := by
  have h0 := in_byte h (k := 0) (by decide)
  have h1 := in_byte h (k := 1) (by decide)
  have h2 := in_byte h (k := 2) (by decide)
  have h3 := in_byte h (k := 3) (by decide)
  rw [Nat.add_zero] at h0
  apply WP.of_runBlock
  simp only [loadBE32, runBlock_cons, runStep_some, runBlock_nil,
    exec_load_b (show off < 2048 by omega), exec_load_b (show off + 1 < 2048 by omega),
    exec_load_b (show off + 2 < 2048 by omega), exec_load_b (show off + 3 < 2048 by omega),
    exec_shift_d (show 24 < 64 by decide), exec_shift_d (show 16 < 64 by decide),
    exec_shift_d (show 8 < 64 by decide), exec_logic, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, h0, h1, h2, h3, hdt, Ne.symm hdt, Ne.symm hdn, Ne.symm htn,
    ite_true, ite_false, Option.some.injEq, exists_eq_left', read_one]
  rw [beWord, ← be_bytes]
  simp only [State.write, State.mk.injEq, and_true]
  funext r
  by_cases hr : r = d
  · simp [hr]
  · by_cases hr' : r = tmp <;> simp [hr, hr']

theorem loadLE32_ok {d tmp n : Reg} {off : Nat} (hdn : d ≠ n) (htn : tmp ≠ n) (hdt : d ≠ tmp)
    (ho : off + 3 < 2048) (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 4) :
    WP isa (.block (loadLE32 d tmp n off)) s (· =
      (s.write tmp ((s.mem (s.gpr n + BitVec.ofNat 64 (off + 3))).setWidth 64 <<< 24)).write d
        ((s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 32).setWidth 64)) := by
  have h0 := in_byte h (k := 0) (by decide)
  have h1 := in_byte h (k := 1) (by decide)
  have h2 := in_byte h (k := 2) (by decide)
  have h3 := in_byte h (k := 3) (by decide)
  rw [Nat.add_zero] at h0
  apply WP.of_runBlock
  simp only [loadLE32, runBlock_cons, runStep_some, runBlock_nil,
    exec_load_b (show off < 2048 by omega), exec_load_b (show off + 1 < 2048 by omega),
    exec_load_b (show off + 2 < 2048 by omega), exec_load_b (show off + 3 < 2048 by omega),
    exec_shift_d (show 24 < 64 by decide), exec_shift_d (show 16 < 64 by decide),
    exec_shift_d (show 8 < 64 by decide), exec_logic, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, h0, h1, h2, h3, hdt, Ne.symm hdt, Ne.symm hdn, Ne.symm htn,
    ite_true, ite_false, Option.some.injEq, exists_eq_left', read_one]
  rw [readW_bytes, ← le_bytes]
  simp only [State.write, State.mk.injEq, and_true]
  funext r
  by_cases hr : r = d
  · simp [hr]
  · by_cases hr' : r = tmp <;> simp [hr, hr']

theorem storeLE32_ok {v tmp n : Reg} {off : Nat} (htv : tmp ≠ v) (htn : tmp ≠ n)
    (ho : off + 3 < 2048) (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 4) :
    WP isa (.block (storeLE32 v tmp n off)) s (· =
      { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr v).setWidth 32) }.write
        tmp (s.gpr v >>> 24)) := by
  have h0 := in_byte h (k := 0) (by decide)
  have h1 := in_byte h (k := 1) (by decide)
  have h2 := in_byte h (k := 2) (by decide)
  have h3 := in_byte h (k := 3) (by decide)
  rw [Nat.add_zero] at h0
  apply WP.of_runBlock
  simp only [storeLE32, runBlock_cons, runStep_some, runBlock_nil,
    exec_store_b (show off < 2048 by omega), exec_store_b (show off + 1 < 2048 by omega),
    exec_store_b (show off + 2 < 2048 by omega), exec_store_b (show off + 3 < 2048 by omega),
    exec_shift_d (show 24 < 64 by decide), exec_shift_d (show 16 < 64 by decide),
    exec_shift_d (show 8 < 64 by decide), RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, h0, h1, h2, h3, Ne.symm htv, Ne.symm htn,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  have b0 : (s.gpr v).setWidth 8 = ((s.gpr v).setWidth 32).extractLsb' 0 8 :=
    byte_shift (s.gpr v) 0 (by decide)
  have b1 : (s.gpr v >>> 8).setWidth 8 = ((s.gpr v).setWidth 32).extractLsb' 8 8 :=
    byte_shift (s.gpr v) 1 (by decide)
  have b2 : (s.gpr v >>> 16).setWidth 8 = ((s.gpr v).setWidth 32).extractLsb' 16 8 :=
    byte_shift (s.gpr v) 2 (by decide)
  have b3 : (s.gpr v >>> 24).setWidth 8 = ((s.gpr v).setWidth 32).extractLsb' 24 8 :=
    byte_shift (s.gpr v) 3 (by decide)
  rw [b0, b1, b2, b3, write4_off]
  simp only [State.write, State.mk.injEq, and_true]
  funext r
  by_cases hr : r = tmp <;> simp [hr]

/-- `li32`'s `addiw`, whose immediate is encodable. -/
theorem exec_addiw_lo12 {d n : Reg} (w : BitVec 32) :
    exec (.addiw d n (lo12 w)) s =
      some (s.write d (sext32 ((s.gpr n).setWidth 32 + BitVec.ofInt 32 (lo12 w)))) :=
  exec_addiw (lo12_imm w)

theorem li32_ok {d : Reg} (w : BitVec 32) :
    WP isa (.block (li32 d w)) s (· = s.write d (sext32 w)) := by
  apply WP.of_runBlock
  simp only [li32, runBlock_cons, runStep_some, runBlock_nil, exec_lui, exec_addiw (lo12_imm w),
    RegUpd.gpr_write_self, lo32_sext, li32_val, RegUpd.write_write, Option.some.injEq,
    exists_eq_left']

end VG.RISCV64.ByteLoad
