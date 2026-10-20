module

public import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.Domain
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Fixed local-frame accesses do not depend on the values stored in them. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem stackAddr_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.addSp .r12 0]) (fun s t => s.gpr .r12 = t.gpr .r12 ∧ s.sp = t.sp) := by
  have trace : RelCT isa (fun s t => s.sp = t.sp) (.block [.addSp .r12 0]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) : WP isa (.block [.addSp .r12 0]) s (fun t => t.gpr .r12 = s.sp) := by
    refine wp_stackAddr (by decide) fun t moved => WP.block_nil ?_
    simpa only [BitVec.add_zero] using moved.gpr
  have paired := (relCT_keep_sp trace (fun _ _ h => h)).wpDep (fun s t _ => ⟨wp s, wp t⟩)
  intro s t tr1 tr2 u v h e1 e2
  obtain ⟨leak, sp, a, b, eq, hu, hv⟩ := paired s t tr1 tr2 u v h e1 e2
  exact ⟨leak, hu.trans (eq.trans hv.symm), sp⟩

def LocalAddress (s t : State) : Prop := s.gpr .r12 = t.gpr .r12 ∧ s.sp = t.sp

theorem storeLocal_ct (r : Reg) (d : Nat) : RelCT isa LocalAddress
    (.block [.str r .r12 d]) LocalAddress := by
  apply single_ct (fun s t h => by simp only [addrs, h.1])
  intro s t u v h e1 e2
  by_cases fit : d < 4096
  · simp only [exec, fit, ite_true, State.store32] at e1 e2
    split at e1
    · split at e2
      · simp only [Option.some.injEq] at e1 e2
        subst u; subst v; exact h
      · cases e2
    · cases e1
  · simp only [exec, fit, ite_false] at e1
    cases e1

theorem loadLocal_ct (r : Reg) (d : Nat) (ne : r ≠ .r12) : RelCT isa LocalAddress
    (.block [.ldrSp r d]) LocalAddress := by
  apply single_ct (fun s t h => by simp only [addrs, h.2])
  intro s t u v h e1 e2
  by_cases fit : d < 4096
  · simp only [exec, fit, ite_true, State.load32] at e1 e2
    split at e1
    · split at e2
      · simp only [Option.map_some, Option.some.injEq] at e1 e2
        subst u; subst v
        exact ⟨by simpa only [State.setReg, Ne.symm ne, ite_false] using h.1, h.2⟩
      · cases e2
    · cases e1
  · simp only [exec, fit, ite_false] at e1
    cases e1


theorem prepareArgs_ct (slot : Nat) : RelCT isa (fun s t => s.sp = t.sp)
    (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs slot)) (fun _ _ => True) := by
  have stores : RelCT isa (fun s t => s.gpr .r12 = t.gpr .r12 ∧ s.sp = t.sp)
      (.block [.str .r4 .r12 8, .str .r6 .r12 12]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1
  change RelCT isa _ (.block
    ([.ldrSp .r4 slot, .ldrSp .r6 32] ++ [.addSp .r12 0] ++ [.str .r4 .r12 8, .str .r6 .r12 12])) _
  exact RelCT.block_append ((RelCT.block_append ((stackLoads_ct [(.r4, slot), (.r6, 32)]).seq stackAddr_ct)).seq stores)

theorem importArgs_ct (slot countSlot : Nat) : RelCT isa (fun s t => s.sp = t.sp)
    (.block (VG.Impl.Ffdh.Arm.Domain.importArgs slot countSlot)) (fun s t => s.sp = t.sp) :=
  stackLoads_ct [(.r4, slot), (.r6, countSlot)]

theorem powerArgs_ct (bs es ec : Nat) : RelCT isa (fun s t => s.sp = t.sp)
    (.block (VG.Impl.Ffdh.Arm.Domain.powerArgs bs es ec)) (fun s t => s.sp = t.sp) :=
  stackLoads_ct [(.r4, bs), (.r6, 32), (.r1, es), (.r2, ec)]

end VG.Proof.Ffdh.Arm
