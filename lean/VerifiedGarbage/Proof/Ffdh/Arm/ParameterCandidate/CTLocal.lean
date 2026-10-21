module

public import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.RegistersCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Candidate argument snapshots expose addresses, regardless of the saved values. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm

theorem localStores_ct (stores : List (Reg × Nat)) : RelCT isa LocalAddress
    (.block (stores.map fun p => Instr.str p.1 .r12 p.2)) LocalAddress := by
  induction stores with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons p rest ih => exact RelCT.block_append ((storeLocal_ct p.1 p.2).seq ih)

theorem localCopy_ct (source target : Nat) : RelCT isa LocalAddress
    (.block [.ldrSp .r0 source, .str .r0 .r12 target]) LocalAddress :=
  RelCT.block_append ((loadLocal_ct .r0 source (by decide)).seq (storeLocal_ct .r0 target))

theorem localCopies_ct (copies : List (Nat × Nat)) : RelCT isa LocalAddress
    (.block (copies.flatMap fun p => [Instr.ldrSp .r0 p.1, Instr.str .r0 .r12 p.2])) LocalAddress := by
  induction copies with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons p rest ih => exact RelCT.block_append ((localCopy_ct p.1 p.2).seq ih)

theorem localZero_ct : RelCT isa LocalAddress (.block [.mov .r0 (.imm 0)]) LocalAddress := by
  have keep := registers_keep_ct (P := LocalAddress) [.r12] (code := .block [.mov .r0 (.imm 0)])
    (by apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
        intro s t _; exact Taint.agree_ofRegs (by simp))
    (by intro s t h r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1)
    (fun _ _ h => h.2)
    (by intro r hr i hi; simp only [List.mem_singleton] at hr; subst r
        simp only [instrs, List.mem_singleton] at hi; subst i; rfl) (by rfl)
  exact keep.mono (fun _ _ h => h) (fun _ _ h => ⟨h.1 .r12 (by simp), h.2⟩)

end VG.Proof.Ffdh.Arm.ParameterCandidate
