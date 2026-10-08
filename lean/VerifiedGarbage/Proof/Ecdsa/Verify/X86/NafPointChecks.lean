import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafPrepChecks
import VerifiedGarbage.Proof.Weierstrass.X86.NafTableTiming

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Impl.Ecdsa.X86 VG.Proof.Weierstrass.X86 VG.Proof.Ecdsa.X86

def nafK : WinCfg := Impl.Ecdsa.Verify.X86.Cfg.nafQ p256Comb

def nafTableAddZeroP : Prog isa := (.block (Jacobian.zeroTest nafK.M.n nafK.R.z))
materialize_code nafTableAddZeroP

def nafTableAddZeroQ : Prog isa := (.block (Jacobian.zeroTest nafK.M.n (Naf.twice nafK).z))
materialize_code nafTableAddZeroQ

def nafTableAddZeroH : Prog isa := (.block (Jacobian.zeroTest nafK.M.n nafK.S.t3))
materialize_code nafTableAddZeroH

def nafTableAddZeroR : Prog isa := (.block (Jacobian.zeroTest nafK.M.n nafK.S.t5))
materialize_code nafTableAddZeroR

def nafTableAddCopyP : Prog isa := (.block (copyPt nafK.M.n nafK.D nafK.R))
materialize_code nafTableAddCopyP

def nafTableAddCopyQ : Prog isa := (.block (copyPt nafK.M.n nafK.D (Naf.twice nafK)))
materialize_code nafTableAddCopyQ

def nafTableAddHead : Prog isa := (fprog p256Comb.SP (jacHead nafK.S nafK.R (Naf.twice nafK)))
materialize_code nafTableAddHead

def nafTableAddTail : Prog isa := (fprog p256Comb.SP (jacTail nafK.S nafK.R (Naf.twice nafK) nafK.D))
materialize_code nafTableAddTail

def nafTableAddDouble : Prog isa := (fprog p256Comb.SP (dblJMul nafK.S nafK.R nafK.D))
materialize_code nafTableAddDouble

def nafTableAddInfinity : Prog isa := (.block (Jacobian.infinity nafK nafK.D))
materialize_code nafTableAddInfinity

theorem nafTableAdd_checks : JacAddChecks nafK p256Comb.SP nafK.R (Naf.twice nafK) nafK.D := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩

  · change ScratchCT nafTableAddZeroP
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafTableAddZeroQ
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafTableAddZeroH
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafTableAddZeroR
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafTableAddCopyP
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafTableAddCopyQ
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafTableAddHead
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafTableAddTail
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafTableAddDouble
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafTableAddInfinity
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafDigitAddZeroP : Prog isa := (.block (Jacobian.zeroTest nafK.M.n nafK.R.z))
materialize_code nafDigitAddZeroP

def nafDigitAddZeroQ : Prog isa := (.block (Jacobian.zeroTest nafK.M.n nafK.E.z))
materialize_code nafDigitAddZeroQ

def nafDigitAddZeroH : Prog isa := (.block (Jacobian.zeroTest nafK.M.n nafK.S.t3))
materialize_code nafDigitAddZeroH

def nafDigitAddZeroR : Prog isa := (.block (Jacobian.zeroTest nafK.M.n nafK.S.t5))
materialize_code nafDigitAddZeroR

def nafDigitAddCopyP : Prog isa := (.block (copyPt nafK.M.n nafK.D nafK.R))
materialize_code nafDigitAddCopyP

def nafDigitAddCopyQ : Prog isa := (.block (copyPt nafK.M.n nafK.D nafK.E))
materialize_code nafDigitAddCopyQ

def nafDigitAddHead : Prog isa := (fprog p256Comb.SP (jacHead nafK.S nafK.R nafK.E))
materialize_code nafDigitAddHead

def nafDigitAddTail : Prog isa := (fprog p256Comb.SP (jacTail nafK.S nafK.R nafK.E nafK.D))
materialize_code nafDigitAddTail

def nafDigitAddDouble : Prog isa := (fprog p256Comb.SP (dblJMul nafK.S nafK.R nafK.D))
materialize_code nafDigitAddDouble

def nafDigitAddInfinity : Prog isa := (.block (Jacobian.infinity nafK nafK.D))
materialize_code nafDigitAddInfinity

theorem nafDigitAdd_checks : JacAddChecks nafK p256Comb.SP nafK.R nafK.E nafK.D := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩

  · change ScratchCT nafDigitAddZeroP
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafDigitAddZeroQ
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafDigitAddZeroH
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafDigitAddZeroR
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafDigitAddCopyP
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafDigitAddCopyQ
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafDigitAddHead
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafDigitAddTail
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafDigitAddDouble
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change ScratchCT nafDigitAddInfinity
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

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

  · change ScratchCT nafTableCopyStep
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change RegCT [.edi,.esi] nafTableStore
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

  · change RegCT [.esi] nafTableAdvance
    exact Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86
