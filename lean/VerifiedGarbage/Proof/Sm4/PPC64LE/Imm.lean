module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Linear
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# 64-bit constants on PPC64LE

`imm_ok`: `imm64 d v` (`lis` and `ori` of the high word, `sldi 32`, then
`oris` and `ori` of the low word) leaves `v` in `d` and changes nothing
else.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE
open VG.Impl.Aes.PPC64LE (imm64)

/-- The value `imm64 d v` builds, bit by bit, is `v`. -/
theorem imm64_val (v : BitVec 64) :
    ((((v.extractLsb' 48 16 ++ (0 : BitVec 16)).signExtend 64 ||| (v.extractLsb' 32 16).setWidth 64) <<< 32) |||
      (v.extractLsb' 16 16).setWidth 64 <<< 16) ||| (v.extractLsb' 0 16).setWidth 64 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  by_cases h1 : i < 16
  · simp [h1, show i < 32 by omega]
  by_cases h2 : i < 32
  · simp [h1, h2, show i - 16 < 16 by omega, show 16 + (i - 16) = i by omega, show i - 16 < 64 by omega]
  by_cases h3 : i < 48
  · simp [h1, h2, show i - 32 < 16 by omega, show 32 + (i - 32) = i by omega, show ¬ i - 16 < 16 by omega,
      show i - 32 < 32 by omega, show i - 32 < 64 by omega]
  · simp [h1, h2, show ¬ i - 32 < 16 by omega, show i - 32 < 64 by omega, show i - 32 - 16 < 16 by omega,
      show 48 + (i - 32 - 16) = i by omega, show ¬ i - 16 < 16 by omega, show i - 32 < 32 by omega]

theorem gpr_write_self (s : State) (d : Reg) (v : BitVec 64) : (s.write d v).gpr d = v := (Upd.write s d v).gpr

/-- `imm64 d v` leaves `v` in `d`. -/
theorem imm_ok (s : State) (d : Reg) (v : BitVec 64) :
    ∃ s', runBlock isa (imm64 d v) s = some s' ∧ s'.gpr d = v ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let v₁ := (v.extractLsb' 48 16 ++ (0 : BitVec 16)).signExtend 64
  let s₁ := s.write d v₁
  have u₁ := Upd.write s d v₁
  let v₂ := v₁ ||| (v.extractLsb' 32 16).setWidth 64
  have u₂ := Upd.write s₁ d v₂
  let v₃ := v₂ <<< 32
  have u₃ := Upd.write (s₁.write d v₂) d v₃
  let v₄ := v₃ ||| (v.extractLsb' 16 16).setWidth 64 <<< 16
  have u₄ := Upd.write ((s₁.write d v₂).write d v₃) d v₄
  let v₅ := v₄ ||| (v.extractLsb' 0 16).setWidth 64
  have u₅ := Upd.write (((s₁.write d v₂).write d v₃).write d v₄) d v₅
  refine ⟨_, ?_, u₅.gpr.trans (imm64_val v), fun r hr => ?_, u₅.mem.trans (u₄.mem.trans (u₃.mem.trans (u₂.mem.trans u₁.mem))),
    u₅.rd.trans (u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))),
    u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr)))⟩
  · simp only [imm64, runBlock_cons, exec_lis, exec_ori, exec_lsl (show 32 < 64 by decide), exec_oris, runStep_some,
      runBlock_nil, gpr_write_self]
    rfl
  · rw [u₅.other r hr, u₄.other r hr, u₃.other r hr, u₂.other r hr, u₁.other r hr]

end VG.Proof.Sm4.PPC64LE
