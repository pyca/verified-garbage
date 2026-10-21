module

public import VerifiedGarbage.Impl.Mont.X86.CombTable
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Public index doubling for the four additional comb columns. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

private theorem doubled : ∀ i < 4,
    BitVec.ofNat 32 (2^i) + BitVec.ofNat 32 (2^i) = BitVec.ofNat 32 (2^(i+1)) := by decide

theorem column_bound : ∀ i < 5, 2^i < 2^32 := by decide

theorem columnAdvance_ok {s : State} {base : Addr} {size i : Nat}
    (hs : Scr s base size) (hz : 32 ≤ size) (hi : i < 4) (h : w32 s.mem base 28 = 2^i) :
    WP isa VG.Impl.Mont.X86.Comb.columnAdvance s fun t =>
      Outside base 28 4 s.mem t.mem ∧ w32 t.mem base 28 = 2^(i+1) ∧
      t.gpr .esi = BitVec.ofNat 32 (2^(i+1)) ∧ Keeps [.esi] s t := by
  unfold VG.Impl.Mont.X86.Comb.columnAdvance
  refine wp_movS (readSrc_sc hs hz) fun u U _ => wp_addS rfl fun v V _ => ?_
  have reg : v.gpr .esi = BitVec.ofNat 32 (2^(i+1)) := by
    rw [V.gpr, U.gpr]
    have read : s.mem.readW (off base 28) 32 = BitVec.ofNat 32 (2^i) := by
      apply BitVec.eq_of_toNat_eq
      change w32 s.mem base 28 = _
      rw [h, BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt (column_bound i (by omega))).symm
    rw [read, doubled i hi]
  have K := U.keeps.trans V.keeps
  have hv := hs.of_keeps K (by decide)
  refine wp_storeS (hv.ea (d := 28) (by omega)) (hv.write hz) fun t M => WP.block_nil ?_
  refine ⟨?_, ?_, M.gpr ▸ reg, K.trans (M.keeps _)⟩
  · rw [M.mem, V.mem, U.mem]; exact writeW32_outside _ _ _ (by decide)
  · rw [M.mem, w32_write_self, reg, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (column_bound (i+1) (by omega))

theorem column_end : ∀ i < 4,
    (BitVec.ofNat 32 (2^(i+1)) - 16#32 == 0) = decide (i+1 = 4) := by decide

theorem column_index : ∀ i < 4, 0 < 2^(i+1) ∧ 2^(i+1) < 32 := by decide

end VG.Proof.Mont.X86.Comb
