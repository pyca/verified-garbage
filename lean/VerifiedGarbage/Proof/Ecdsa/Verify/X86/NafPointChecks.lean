import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafAddShared

/-!
# ECDSA verification on x86 (32-bit): the checks of the NAF's table
-/

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Impl.Ecdsa.X86 VG.Proof.Weierstrass.X86 VG.Proof.Ecdsa.X86

def nafTableAddZeroQ : Prog isa := (.block (Jacobian.zeroTest nafK.M.n (Naf.twice nafK).z))
materialize_code nafTableAddZeroQ

theorem nafTableAddZeroQ_ct : ScratchCT nafTableAddZeroQ :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafTableAddCopyQ : Prog isa := (.block (copyPt nafK.M.n nafK.D (Naf.twice nafK)))
materialize_code nafTableAddCopyQ

theorem nafTableAddCopyQ_ct : ScratchCT nafTableAddCopyQ :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafTableAddHead : Prog isa := (fprog p256Comb.SP (jacHead nafK.S nafK.R (Naf.twice nafK)))
materialize_code nafTableAddHead

theorem nafTableAddHead_ct : ScratchCT nafTableAddHead :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafTableAddTail : Prog isa := (fprog p256Comb.SP (jacTail nafK.S nafK.R (Naf.twice nafK) nafK.D))
materialize_code nafTableAddTail

theorem nafTableAddTail_ct : ScratchCT nafTableAddTail :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

theorem nafTableAdd_checks : JacAddChecks nafK p256Comb.SP nafK.R (Naf.twice nafK) nafK.D :=
  nafAdd_checks nafTableAddZeroQ_ct nafTableAddCopyQ_ct nafTableAddHead_ct nafTableAddTail_ct

def nafTableDouble : Prog isa := fprog p256Comb.SP (dblJMul nafK.S nafK.P (Naf.twice nafK))
materialize_code nafTableDouble

def nafTableCopyFirst : Prog isa := .block (copyPt nafK.M.n (nafK.tblPt 1) nafK.P)
materialize_code nafTableCopyFirst

def nafTableCopyInit : Prog isa := .block (copyPt nafK.M.n nafK.R nafK.P)
materialize_code nafTableCopyInit

def nafTableInitCounter : Prog isa := .block [.mov .esi (.imm 1)]
materialize_code nafTableInitCounter

def nafTableCopyStep : Prog isa := .block (copyPt nafK.M.n nafK.R nafK.D)
materialize_code nafTableCopyStep

theorem nafTableCopyStep_ct : ScratchCT nafTableCopyStep :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafTableStore : Prog isa := .block (Naf.tableStore nafK)
materialize_code nafTableStore

def nafTableAdvance : Prog isa := .block [.alu .add .esi (.imm 1),.alu .cmp .esi (.imm 8)]
materialize_code nafTableAdvance

theorem nafTable_checks : NafTableChecks nafK p256Comb.SP := by
  refine ⟨?_,?_,?_,?_,nafTableAdd_checks,?_,?_,?_⟩

  · change ScratchCT nafTableDouble
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafTableCopyFirst
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafTableCopyInit
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafTableInitCounter
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · exact nafTableCopyStep_ct

  · change RegCT [.edi,.esi] nafTableStore
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change RegCT [.esi] nafTableAdvance
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86
