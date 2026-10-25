module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Words.RISCV64.Word64
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.TCB.RISCV64.Isa
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Impl.Words.RISCV64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Mem

/-!
# RISC-V: 64-bit words of argument buffers, a byte at a time

Untrusted: everything here is checked by Lean. The effect of the sequences
of `Impl/Words/RISCV64/Word64.lean`, each as one equation of the final state,
with the writes kept folded (`State.write`), as in `ByteLoad.lean`:
* `loadBE64_ok`: the big-endian word `be64` (the bytes in the order of
  FIPS 180-4's `parseBlock` for SHA-512);
* `li64_ok`: a constant loaded by `li64`.

The little-endian words of `Impl/Words64/RISCV64.lean` have their lemmas in
`Proof/Framework/RISCV64/Words64.lean`.
-/

@[expose] public section

namespace VG.RISCV64.ByteLoad

open VG.Impl.Words.RISCV64 VG.WriteBytes

/-- The big-endian 64-bit word of the bytes at `p + off`, …, `p + off + 7`. -/
def be64 (m : Mem) (p : Addr) (off : Nat) : BitVec 64 :=
  m (p + BitVec.ofNat 64 off) ++ m (p + BitVec.ofNat 64 (off + 1)) ++
    m (p + BitVec.ofNat 64 (off + 2)) ++ m (p + BitVec.ofNat 64 (off + 3)) ++
    m (p + BitVec.ofNat 64 (off + 4)) ++ m (p + BitVec.ofNat 64 (off + 5)) ++
    m (p + BitVec.ofNat 64 (off + 6)) ++ m (p + BitVec.ofNat 64 (off + 7))

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

theorem loadBE64_ok {d tmp n : Reg} {off : Nat} (hdn : d ≠ n) (htn : tmp ≠ n) (hdt : d ≠ tmp)
    (ho : off + 7 < 2048) (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    WP isa (.block (loadBE64 d tmp n off)) s (· =
      (s.write tmp ((s.mem (s.gpr n + BitVec.ofNat 64 (off + 7))).setWidth 64)).write d
        (be64 s.mem (s.gpr n) off)) := by
  have hb : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 (off + k)) 1 :=
    fun k hk => in_byte' h hk
  have h0 := hb 0 (by decide)
  rw [Nat.add_zero] at h0
  apply WP.of_runBlock
  simp only [loadBE64, runBlock_cons, runStep_some, runBlock_nil,
    exec_load_b (show off < 2048 by omega), exec_load_b (show off + 1 < 2048 by omega),
    exec_load_b (show off + 2 < 2048 by omega), exec_load_b (show off + 3 < 2048 by omega),
    exec_load_b (show off + 4 < 2048 by omega), exec_load_b (show off + 5 < 2048 by omega),
    exec_load_b (show off + 6 < 2048 by omega), exec_load_b (show off + 7 < 2048 by omega),
    exec_shift_d (show 8 < 64 by decide), exec_logic, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, h0, hb 1 (by decide), hb 2 (by decide), hb 3 (by decide),
    hb 4 (by decide), hb 5 (by decide), hb 6 (by decide), hb 7 (by decide), hdt,
    Ne.symm hdt, Ne.symm hdn, Ne.symm htn, ite_true, ite_false, Option.some.injEq,
    exists_eq_left', read_one]
  simp (disch := omega) only [append_byte]
  simp only [State.write, State.mk.injEq, and_true]
  funext r
  by_cases hr : r = d
  · simp [hr, be64]
  · by_cases hr' : r = tmp <;> simp [hr, hr', Ne.symm hdt]

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
