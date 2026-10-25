module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Words.RISCV64.Word64
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.TCB.RISCV64.Isa
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Impl.Words.RISCV64
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# RISC-V: 64-bit words of argument buffers, a byte at a time

Untrusted: everything here is checked by Lean. The effect of the sequences
of `Impl/Words/RISCV64/Word64.lean`, each as one equation of the final state,
with the writes kept folded (`State.write`), as in `ByteLoad.lean`:
* `loadBE64_ok`: the big-endian word `be64` (the bytes in the order of
  FIPS 180-4's `parseBlock` for SHA-512);
* `loadLE64b_ok`: the little-endian word `readW`;
* `storeLE_ok`: the low `w` bytes of a register, little-endian, and
  `storeLE64_ok`, all eight of them as `writeW`;
* `li64_ok`: a constant loaded by `li64`.
-/

@[expose] public section

namespace VG.RISCV64.ByteLoad

open VG.Impl.Words.RISCV64 VG.WriteBytes

/-- The 64-bit word whose bytes, most significant first, are at `p + off + o 0`,
…, `p + off + o 7`. -/
def bytes64 (m : Mem) (p : Addr) (off : Nat) (o : Nat → Nat) : BitVec 64 :=
  m (p + BitVec.ofNat 64 (off + o 0)) ++ m (p + BitVec.ofNat 64 (off + o 1)) ++
    m (p + BitVec.ofNat 64 (off + o 2)) ++ m (p + BitVec.ofNat 64 (off + o 3)) ++
    m (p + BitVec.ofNat 64 (off + o 4)) ++ m (p + BitVec.ofNat 64 (off + o 5)) ++
    m (p + BitVec.ofNat 64 (off + o 6)) ++ m (p + BitVec.ofNat 64 (off + o 7))

/-- The big-endian word at `p + off`. -/
abbrev be64 (m : Mem) (p : Addr) (off : Nat) : BitVec 64 := bytes64 m p off id

/-- The low `w` bytes of `x`, least significant first, as `storeLE` stores
them. -/
def leBytes (w : Nat) (x : BitVec 64) : List Byte :=
  (List.range w).map fun j => (x >>> (8 * j)).setWidth 8

/-! ## Bit vectors -/

/-- One step of `loadBytes64`: shift what is loaded left by a byte, and `or`
the next byte in. -/
theorem append_byte {n : Nat} (x : BitVec n) (b : BitVec 8) (h : n + 8 ≤ 64) :
    x.setWidth 64 <<< 8 ||| b.setWidth 64 = (x ++ b).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h8 : i < 8
  · simp [h8, hi]
  · by_cases hn : i - 8 < n
    · simp [h8, hi, hn, BitVec.getLsbD_of_ge b i (by omega), show i - 8 < 64 by omega]
    · simp [h8, hi, BitVec.getLsbD_of_ge b i (by omega), BitVec.getLsbD_of_ge x (i - 8) (by omega)]

/-- A byte of a register, as a right shift leaves it. -/
theorem byte_extract (x : BitVec 64) (j : Nat) :
    (x >>> (8 * j)).setWidth 8 = x.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, hi]

/-- The value `li64` loads. -/
theorem li64_val (v : BitVec 64) :
    sext32 (hiAdj v) <<< 32 + sext32 (v.setWidth 32) = v := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  simp only [sext32, hiAdj, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_signExtend,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_and,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_toNat,
    show BitVec.toNat (1 : BitVec 32) = 1 from rfl, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceSub,
    decide_eq_true_eq, ge_iff_le]
  split <;> split <;> omega

/-! ## Memory -/

/-- A little-endian doubleword, from its bytes. -/
theorem readW64_bytes (m : Mem) (p : Addr) (off : Nat) :
    m.readW (p + BitVec.ofNat 64 off) 64 = bytes64 m p off (7 - ·) := by
  have e : ∀ k, p + BitVec.ofNat 64 off + BitVec.ofNat 64 k = p + BitVec.ofNat 64 (off + k) := by
    intro k; rw [BitVec.ofNat_add, BitVec.add_assoc]
  simp only [bytes64, Nat.reduceSub, Nat.add_zero, ← e]
  simp only [Mem.readW, Mem.read, BitVec.add_assoc, BitVec.reduceAdd]
  rw [BitVec.zero_width_append]
  rfl

/-- Every byte of an `n`-byte access within a region. -/
theorem contains_byte' {r : Region} {p : Addr} {off n : Nat} (h : r.Contains (p + BitVec.ofNat 64 off) n)
    {k : Nat} (hk : k < n) : r.Contains (p + BitVec.ofNat 64 (off + k)) 1 := by
  refine h.byte ?_
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  omega

/-- Every byte of an `n`-byte access within the regions. -/
theorem in_byte' {rs : List Region} {p : Addr} {off n : Nat}
    (h : InRegions rs (p + BitVec.ofNat 64 off) n) {k : Nat} (hk : k < n) :
    InRegions rs (p + BitVec.ofNat 64 (off + k)) 1 := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, contains_byte' hc hk⟩

/-! ## The sequences -/

variable {s : State}

theorem loadBytes64_ok {d tmp n : Reg} {off : Nat} {o : Nat → Nat} (hdn : d ≠ n) (htn : tmp ≠ n)
    (hdt : d ≠ tmp) (ho : ∀ k < 8, off + o k < 2048)
    (h : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 (off + o k)) 1) :
    WP isa (.block (loadBytes64 d tmp n off o)) s (· =
      (s.write tmp ((s.mem (s.gpr n + BitVec.ofNat 64 (off + o 7))).setWidth 64)).write d
        (bytes64 s.mem (s.gpr n) off o)) := by
  apply WP.of_runBlock
  simp only [loadBytes64, runBlock_cons, runStep_some, runBlock_nil,
    exec_load_b (ho 0 (by decide)), exec_load_b (ho 1 (by decide)), exec_load_b (ho 2 (by decide)),
    exec_load_b (ho 3 (by decide)), exec_load_b (ho 4 (by decide)), exec_load_b (ho 5 (by decide)),
    exec_load_b (ho 6 (by decide)), exec_load_b (ho 7 (by decide)),
    exec_shift_d (show 8 < 64 by decide), exec_logic, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, h 0 (by decide), h 1 (by decide), h 2 (by decide),
    h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), hdt,
    Ne.symm hdt, Ne.symm hdn, Ne.symm htn, ite_true, ite_false, Option.some.injEq,
    exists_eq_left', read_one]
  simp (disch := omega) only [append_byte]
  simp only [State.write, State.mk.injEq, and_true]
  funext r
  by_cases hr : r = d
  · simp [hr, bytes64]
  · by_cases hr' : r = tmp <;> simp [hr, hr', Ne.symm hdt]

theorem loadBE64_ok {d tmp n : Reg} {off : Nat} (hdn : d ≠ n) (htn : tmp ≠ n) (hdt : d ≠ tmp)
    (ho : off + 7 < 2048) (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    WP isa (.block (loadBE64 d tmp n off)) s (· =
      (s.write tmp ((s.mem (s.gpr n + BitVec.ofNat 64 (off + 7))).setWidth 64)).write d
        (be64 s.mem (s.gpr n) off)) :=
  loadBytes64_ok hdn htn hdt (fun k hk => by simp only [id]; omega)
    (fun k hk => in_byte' h (by simp only [id]; omega))

theorem loadLE64b_ok {d tmp n : Reg} {off : Nat} (hdn : d ≠ n) (htn : tmp ≠ n) (hdt : d ≠ tmp)
    (ho : off + 7 < 2048) (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    WP isa (.block (loadLE64b d tmp n off)) s (· =
      (s.write tmp ((s.mem (s.gpr n + BitVec.ofNat 64 off)).setWidth 64)).write d
        (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64)) := by
  rw [readW64_bytes]
  refine WP.mono (loadBytes64_ok hdn htn hdt (fun k hk => by omega)
    (fun k hk => in_byte' h (by omega))) fun s' e => ?_
  rw [e, Nat.sub_self, Nat.add_zero]

theorem leBytes_length (w : Nat) (x : BitVec 64) : (leBytes w x).length = w := by simp [leBytes]

theorem take_leBytes_succ {w k : Nat} (x : BitVec 64) (hk : k < w) :
    (leBytes w x).take (k + 1) = (leBytes w x).take k ++ [(x >>> (8 * k)).setWidth 8] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [leBytes_length]; exact hk)]
  simp [leBytes]

/-- The first `k` steps of `storeLE`. -/
theorem storeLE_prefix {v tmp n : Reg} {off w : Nat} (htv : tmp ≠ v) (htn : tmp ≠ n)
    (hw8 : w ≤ 8) (ho : off + w ≤ 2048) (h : ∀ j < w, InRegions s.wr (s.gpr n + BitVec.ofNat 64 (off + j)) 1) :
    ∀ k ≤ w, WP isa (.block ((List.range k).flatMap fun j =>
        [.shift .srl .d tmp v (8 * j), .store .b tmp n (off + j)])) s (· =
      { s with mem := writeBytes s.mem (s.gpr n + BitVec.ofNat 64 off) ((leBytes w (s.gpr v)).take k) }.write
        tmp (if k = 0 then s.gpr tmp else s.gpr v >>> (8 * (k - 1)))) := by
  intro k hk
  induction k with
  | zero =>
    refine WP.block_nil ?_
    simp only [List.take_zero, writeBytes_nil, ite_true]
    exact (write_self _ _).symm
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ e => ?_
    subst e
    have hin := h k (by omega)
    apply WP.of_runBlock
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, runBlock_cons, runStep_some,
      exec_shift_d (show 8 * k < 64 by omega), RegUpd.gpr_write,
      Ne.symm htv, ite_false, RegUpd.write_write]
    rw [exec_store_b (show off + k < 2048 by omega) (by
      simp only [RegUpd.gpr_write, Ne.symm htn, ite_false, RegUpd.wr_write]; exact hin)]
    simp only [RegUpd.gpr_write, Ne.symm htn, ite_true, ite_false, runStep_some, runBlock_nil,
      Option.some.injEq, exists_eq_left', RegUpd.mem_write, RegUpd.write_mem]
    rw [take_leBytes_succ _ (by omega), writeBytes_snoc _ _ _ _ (by
      simp only [List.length_take, leBytes_length]; omega), writeW_byte]
    simp only [List.length_take, leBytes_length, Nat.min_eq_left (show k ≤ w by omega),
      Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    rw [show s.gpr n + BitVec.ofNat 64 off + BitVec.ofNat 64 k = s.gpr n + BitVec.ofNat 64 (off + k) by
      rw [BitVec.ofNat_add, BitVec.add_assoc]]

theorem storeLE_ok {v tmp n : Reg} {off w : Nat} (htv : tmp ≠ v) (htn : tmp ≠ n) (hw : 0 < w)
    (hw8 : w ≤ 8) (ho : off + w ≤ 2048) (h : ∀ j < w, InRegions s.wr (s.gpr n + BitVec.ofNat 64 (off + j)) 1) :
    WP isa (.block (storeLE w v tmp n off)) s (· =
      { s with mem := writeBytes s.mem (s.gpr n + BitVec.ofNat 64 off) (leBytes w (s.gpr v)) }.write
        tmp (s.gpr v >>> (8 * (w - 1)))) := by
  refine WP.mono (storeLE_prefix htv htn hw8 ho h w (Nat.le_refl _)) fun s' e => ?_
  rw [e, List.take_of_length_le (by rw [leBytes_length]), ite_eq_right_of_eq_false _ _ (by simp; omega)]

/-- A doubleword write is a write of its bytes, least significant first. -/
theorem writeW64_leBytes (m : Mem) (a : Addr) (x : BitVec 64) :
    m.writeW a x = writeBytes m a (leBytes 8 x) := by
  rw [Mem.writeW, write_eq_writeBytes]
  simp only [leBytes, byte_extract]
  rfl

theorem storeLE64_ok {v tmp n : Reg} {off : Nat} (htv : tmp ≠ v) (htn : tmp ≠ n)
    (ho : off + 8 ≤ 2048) (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8) :
    WP isa (.block (storeLE 8 v tmp n off)) s (· =
      { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr v) }.write
        tmp (s.gpr v >>> 56)) := by
  refine WP.mono (storeLE_ok htv htn (by decide) (by decide) ho fun j hj => in_byte' h hj)
    fun s' e => ?_
  rw [e, writeW64_leBytes]

theorem li64_ok {d tmp : Reg} (hdt : d ≠ tmp) (v : BitVec 64) :
    WP isa (.block (li64 d tmp v)) s (· = (s.write tmp (sext32 (v.setWidth 32))).write d v) := by
  apply WP.of_runBlock
  simp only [li64, li32, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec_lui, exec_addiw (lo12_imm _), exec_shift_d (show 32 < 64 by decide),
    exec_add, RegUpd.gpr_write, hdt, Ne.symm hdt, ite_true, ite_false,
    lo32_sext, li32_val, Option.some.injEq, exists_eq_left']
  rw [li64_val]
  simp only [RegUpd.write_write]
  rw [RegUpd.write_comm (s := s) hdt, RegUpd.write_write]

end VG.RISCV64.ByteLoad
