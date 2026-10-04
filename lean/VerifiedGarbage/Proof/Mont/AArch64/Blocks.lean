import VerifiedGarbage.Proof.Mont.AArch64.Row

/-!
# Montgomery arithmetic on AArch64: the small blocks of a round

Each run symbolically once, for any registers: a register cleared
(`movz0_ok`) and a constant built (`const64_ok`).
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

/-- `r = 0`. -/
theorem movz0_ok (s : State) (r : Reg) :
    WP isa (.block [.movz .x r 0 0]) s fun s' => s'.gpr r = 0 ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  exact RegUpd.gpr_write_of_ne _ _ _ hq

/-- `r = v`. -/
theorem const64_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (const64 r v)) s fun t => t.gpr r = v ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [const64, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨movz_movk64' v, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r' hr
  have h : r' ≠ r := by simpa only [List.mem_singleton] using hr
  simp only [RegUpd.gpr_write_of_ne _ _ _ h]

end VG.Proof.Mont.AArch64
