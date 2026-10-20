module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Public division iteration counter -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

theorem count_ok (s : State) :
    WP isa (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]) s fun t =>
      t.gpr .esi = s.gpr .esi - 1 ∧ t.zf = some (s.gpr .esi - 1 == 0) ∧
      t.mem = s.mem ∧ Keeps [.esi] s t := by
  refine wp_subS rfl fun u U _ => ?_
  refine wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨by rw [T.gpr, U.gpr], ?_, T.mem.trans U.mem, U.keeps.trans (T.keeps _)⟩
  rw [Z, U.gpr]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
end VG.Proof.Rsa.X86.Div
