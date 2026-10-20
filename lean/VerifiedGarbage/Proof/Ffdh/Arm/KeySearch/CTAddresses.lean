module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.RegistersCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Fixed stack loads and controller stores preserve public control
addresses while handling arbitrary secret register values. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Bignum.Arm

def ControlAddress (s t : State) : Prop := s.gpr .r4 = t.gpr .r4 ∧ s.sp = t.sp

theorem controlStore_ct (r : Reg) (d : Nat) : RelCT isa ControlAddress
    (.block [.str r .r4 d]) ControlAddress := by
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

theorem controlLoad_ct (r : Reg) (d : Nat) (ne : r ≠ .r4) : RelCT isa ControlAddress
    (.block [.ldrSp r d]) ControlAddress := by
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

private theorem zeroRegister_ct : RelCT isa ControlAddress (.block [.mov .r3 (.imm 0)]) ControlAddress := by
  have keep := registers_keep_ct (P := ControlAddress) [.r4] (code := .block [.mov .r3 (.imm 0)])
    (by apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
        intro s t _; exact Taint.agree_ofRegs (by simp))
    (by intro s t h r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1)
    (fun _ _ h => h.2)
    (by intro r hr i hi; simp only [List.mem_singleton] at hr; subst r
        simp only [instrs, List.mem_singleton] at hi; subst i; rfl) (by rfl)
  exact keep.mono (fun _ _ h => h) (fun _ _ h => ⟨h.1 .r4 (by simp), h.2⟩)

theorem entryCopy_ct (offset slot : Nat) : RelCT isa ControlAddress
    (.block [.ldrSp .r3 offset, VG.Impl.Ffdh.Arm.KeySearch.stf .r3 slot]) ControlAddress := by
  change RelCT isa _ (.block ([.ldrSp .r3 offset] ++ [.str .r3 .r4 (8 * slot)])) _
  exact RelCT.block_append ((controlLoad_ct .r3 offset (by decide)).seq (controlStore_ct .r3 (8 * slot)))

theorem entryZero_ct : RelCT isa ControlAddress
    (.block [.mov .r3 (.imm 0), VG.Impl.Ffdh.Arm.KeySearch.stf .r3 11]) ControlAddress :=
  RelCT.block_append (zeroRegister_ct.seq (controlStore_ct .r3 88))

end VG.Proof.Ffdh.Arm.KeySearch
