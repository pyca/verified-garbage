module

public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The private-result comparison becomes a branchless equality bit -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Rsa.X86.PrivChecked

theorem zeroTest_ok (s : State) :
    WP isa (.block zeroTest) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (s.gpr .ebp = 0)).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold zeroTest
  refine wp_movS rfl fun a A _ => ?_
  refine wp_subS rfl fun b B _ => ?_
  refine wp_orS rfl fun c C => ?_
  refine wp_shr (by decide) fun d D _ => ?_
  refine wp_logicS (.inr rfl) rfl fun t T => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem))),
    (((A.keeps.trans B.keeps).trans C.keeps).trans D.keeps).trans T.keeps⟩
  rw [T.gpr, D.gpr, C.gpr, B.gpr, A.gpr,
    B.other .ebp (by decide), A.other .ebp (by decide), ite_eq_right (by decide)]
  exact VG.Proof.Rsa.zero_test32 _

end VG.Proof.Rsa.X86.PrivChecked
