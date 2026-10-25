module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Words64.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import all Init.Data.Nat.Bitwise.Basic

/-!
# RISC-V: doublewords of argument buffers, a byte at a time

Untrusted: everything here is checked by Lean. The effect of the sequences
of `Impl/Words64/RISCV64.lean`, each as the final state, up to the values
left in their temporaries:
* `loadLE64_ok`: the little-endian doubleword `readW`;
* `storeLE64_ok`: a register, written as `writeW`;
* `movImm64_ok`: a 64-bit constant.
-/

@[expose] public section

namespace VG.RISCV64.Words64

open VG.Impl.Words.RISCV64 VG.Impl.Words64.RISCV64

/-! ## Bit vectors -/

/-- Byte `i` of two words joined into a doubleword. -/
theorem join_byte (x y : BitVec 32) {i : Nat} (hi : i < 8) :
    (x.setWidth 64 <<< 32 ||| y.setWidth 64).extractLsb' (8 * i) 8 =
      if i < 4 then y.extractLsb' (8 * i) 8 else x.extractLsb' (8 * (i - 4)) 8 := by
  ext j hj
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  split
  · simp only [BitVec.getElem_extractLsb']
    simp (disch := omega) [show 8 * i + j < 32 by omega, show 8 * i + j < 64 by omega]
  · simp only [BitVec.getElem_extractLsb']
    simp (disch := omega) [show ¬ 8 * i + j < 32 by omega, show 8 * i + j < 64 by omega,
      show 8 * i + j - 32 = 8 * (i - 4) + j by omega]
    intro; omega

/-- A 64-bit constant from the sign-extended words `li32` leaves. -/
theorem movImm64_val (v : BitVec 64) :
    sext32 (v.extractLsb' 32 32) <<< 32 ||| (sext32 (v.extractLsb' 0 32) <<< 32) >>> 32 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb']
  by_cases h : i < 32
  · simp (disch := omega) [h, hi, show 32 + i < 64 by omega]
  · simp (disch := omega) [h, hi, show ¬ 32 + i < 64 by omega, show i - 32 < 64 by omega]
    intro; omega

/-! ## Memory -/

/-- A little-endian doubleword is its two words. -/
theorem readW64_split (m : Mem) (a : Addr) :
    m.readW a 64 = (m.readW (a + BitVec.ofNat 64 4) 32).setWidth 64 <<< 32 |||
      (m.readW a 32).setWidth 64 := by
  show m.read a 8 = _
  refine Mem.read_eq_of_bytes fun i hi => ?_
  rw [join_byte _ _ hi]
  split
  · exact Mem.readW_byte m a ‹_›
  · rw [← Mem.readW_byte m _ (by omega), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 3; omega

theorem toNat_sub_add4 (x a : Addr) :
    (x - (a + BitVec.ofNat 64 4)).toNat = ((x - a).toNat + (2 ^ 64 - 4)) % 2 ^ 64 := by
  rw [show x - (a + BitVec.ofNat 64 4) = (x - a) + BitVec.ofNat 64 (2 ^ 64 - 4) by bv_omega,
    BitVec.toNat_add, BitVec.toNat_ofNat]

/-- A doubleword written as its two words. -/
theorem writeW64_split (m : Mem) (a : Addr) (v : BitVec 64) :
    (m.writeW a (v.setWidth 32)).writeW (a + BitVec.ofNat 64 4) ((v >>> 32).setWidth 32) =
      m.writeW a v := by
  funext x
  simp only [Mem.writeW, Mem.write, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq, toNat_sub_add4]
  have ht := (x - a).isLt
  generalize (x - a).toNat = t at *
  by_cases h4 : t < 4
  · simp only [show ¬ (t + (2 ^ 64 - 4)) % 2 ^ 64 < 4 by omega, h4, show t < 8 by omega, ↓reduceIte]
    ext j hj
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
    simp only [show 8 * t + j < 32 by omega, decide_true, Bool.true_and]
  · by_cases h8 : t < 8
    · simp only [show (t + (2 ^ 64 - 4)) % 2 ^ 64 = t - 4 by omega, show t - 4 < 4 by omega, h8,
        ↓reduceIte]
      ext j hj
      simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
        show 8 * (t - 4) + j < 32 by omega, decide_true, Bool.true_and,
        show 32 + (8 * (t - 4) + j) = 8 * t + j by omega]
    · simp only [show ¬ (t + (2 ^ 64 - 4)) % 2 ^ 64 < 4 by omega, h4, h8, ↓reduceIte]

/-- The second word of a doubleword access. -/
theorem in_hi {rs : List Region} {p : Addr} {off : Nat} (h : InRegions rs (p + BitVec.ofNat 64 off) 8) :
    InRegions rs (p + BitVec.ofNat 64 (off + 4)) 4 := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  rw [BitVec.ofNat_add, ← BitVec.add_assoc,
    show p + BitVec.ofNat 64 off + BitVec.ofNat 64 4 - r.base =
      (p + BitVec.ofNat 64 off - r.base) + BitVec.ofNat 64 4 by bv_omega,
    BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((p + BitVec.ofNat 64 off - r.base).toNat + 4 % 2 ^ 64) (2 ^ 64)
  omega

/-- The first word of a doubleword access. -/
theorem in_lo {rs : List Region} {a : Addr} (h : InRegions rs a 8) : InRegions rs a 4 := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, by simp only [Region.Contains] at hc ⊢; omega⟩

/-! ## The sequences -/

variable {s : State}

/-- `s'` is `s` with `d` set to `v` and only `t₁` and `t₂` changed besides. -/
structure Upd3 (s s' : State) (d t₁ t₂ : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → r ≠ t₁ → r ≠ t₂ → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem loadLE64_ok {d tmp tmp2 n : Reg} {off : Nat} (hdn : d ≠ n) (htn : tmp ≠ n) (hdt : d ≠ tmp)
    (h2n : tmp2 ≠ n) (h2t : tmp2 ≠ tmp) (hd2 : d ≠ tmp2)
    (ho : off + 7 < 2048) (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    WP isa (.block (loadLE64 d tmp tmp2 n off)) s fun s' =>
      Upd3 s s' d tmp tmp2 (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64) := by
  unfold loadLE64
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ByteLoad.loadLE32_ok hdn htn hdt (by omega) (in_lo h)) fun s₁ e₁ => ?_
  subst e₁
  have hn₁ : ((s.write tmp ((s.mem (s.gpr n + BitVec.ofNat 64 (off + 3))).setWidth 64 <<< 24)).write d
      ((s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 32).setWidth 64)).gpr n = s.gpr n := by
    simp only [RegUpd.gpr_write, Ne.symm hdn, Ne.symm htn, ite_false]
  refine WP.mono (ByteLoad.loadLE32_ok h2n htn h2t (by omega) (by
    rw [hn₁, RegUpd.rd_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.wr_write]; exact in_hi h))
    fun s₂ e₂ => ?_
  subst e₂
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 32 < 64 by decide),
    exec_logic, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, RegUpd.mem_write, ite_true, ite_false, hdt, hd2, Ne.symm hd2, h2t,
      Ne.symm hdn, Ne.symm htn]
    rw [readW64_split, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.or_comm]
  · simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]

theorem storeLE64_ok {v tmp tmp2 n : Reg} {off : Nat} (htv : tmp ≠ v) (htn : tmp ≠ n)
    (h2t : tmp2 ≠ tmp) (h2n : tmp2 ≠ n) (ho : off + 7 < 2048)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8) :
    WP isa (.block (storeLE64 v tmp tmp2 n off)) s fun s' =>
      (∀ r, r ≠ tmp → r ≠ tmp2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr v) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold storeLE64
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ByteLoad.storeLE32_ok htv htn (by omega) (in_lo h)) fun s₁ e₁ => ?_
  subst e₁
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 32 < 64 by decide),
    RegUpd.gpr_write, Ne.symm htv, ite_false, RegUpd.write_write, Option.some.injEq, exists_eq_left']
  refine WP.mono (ByteLoad.storeLE32_ok (v := tmp) h2t h2n (by omega) (by
    simp only [RegUpd.gpr_write, Ne.symm htn, ite_false, RegUpd.wr_write]; exact in_hi h))
    fun s₂ e₂ => ?_
  subst e₂
  refine ⟨fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, h1, h2, ite_false]
  · simp only [RegUpd.gpr_write, Ne.symm htn, ite_true, ite_false, RegUpd.mem_write]
    show (s.mem.writeW _ _).writeW _ _ = _
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, writeW64_split]

theorem movImm64_ok {d tmp : Reg} (hdt : d ≠ tmp) (v : BitVec 64) :
    WP isa (.block (movImm64 d tmp v)) s fun s' =>
      s'.gpr d = v ∧ (∀ r, r ≠ d → r ≠ tmp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold movImm64
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ByteLoad.li32_ok _) fun s₁ e₁ => ?_
  subst e₁
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 32 < 64 by decide),
    RegUpd.gpr_write_self, RegUpd.write_write, Option.some.injEq, exists_eq_left']
  refine WP.mono (ByteLoad.li32_ok _) fun s₂ e₂ => ?_
  subst e₂
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 32 < 64 by decide),
    exec_logic, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, ite_true, ite_false, hdt, Ne.symm hdt, movImm64_val]
  · simp only [RegUpd.gpr_write, h1, h2, ite_false]

end VG.RISCV64.Words64
