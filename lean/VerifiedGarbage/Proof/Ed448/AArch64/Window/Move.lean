module

public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! A register move, without importing the verifier's final-reduction proofs. -/

@[expose] public section
namespace VG.Proof.Ed448.AArch64.Window
open VG VG.AArch64
open VG.Proof.X448.AArch64 (Keeps)

/-- `d := r`. -/
theorem mov_ok (d r : Reg) (s : State) :
    WP isa (.block [.addImm .x d r 0]) s fun t => t.gpr d = s.gpr r ∧ t.mem = s.mem ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, BitVec.add_zero, RegUpd.gpr_write_self,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r' hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

end VG.Proof.Ed448.AArch64.Window
