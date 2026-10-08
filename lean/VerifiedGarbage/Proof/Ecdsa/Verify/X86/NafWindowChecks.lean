import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafPointChecks
import VerifiedGarbage.Proof.Weierstrass.X86.NafWindowTiming

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Impl.Ecdsa.X86 VG.Proof.Weierstrass.X86 VG.Proof.Ecdsa.X86

def nafRunRead : Prog isa := .block (Naf.digitRead nafK)
materialize_code nafRunRead

theorem nafRunRead_ct : RegCT [.edi,.esi] nafRunRead :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunLookup : Prog isa := .block (Naf.publicEntry nafK)
materialize_code nafRunLookup

theorem nafRunLookup_ct : RegCT [.edi,.ebx] nafRunLookup :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunSign : Prog isa := .block [.alu .cmp .ebx (.imm 128)]
materialize_code nafRunSign

theorem nafRunSign_ct : RegCT [.ebx] nafRunSign :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunAbs : Prog isa := .block [.mov .eax (.imm 256),.alu .sub .eax (.reg .ebx),.mov .ebx (.reg .eax)]
materialize_code nafRunAbs

theorem nafRunAbs_ct : RegCT [.ebx] nafRunAbs :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunNeg : Prog isa := opCode p256Comb.SP (.sub nafK.E.y nafK.zero nafK.E.y)
materialize_code nafRunNeg

theorem nafRunNeg_ct : ScratchCT nafRunNeg :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunCopy : Prog isa := .block (copyPt nafK.M.n nafK.R nafK.D)
materialize_code nafRunCopy

theorem nafRunCopy_ct : ScratchCT nafRunCopy :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunDouble : Prog isa := fprog p256Comb.SP (dblJMul nafK.S nafK.R nafK.D)
materialize_code nafRunDouble

theorem nafRunDouble_ct : ScratchCT nafRunDouble :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunDec : Prog isa := .block [.alu .sub .esi (.imm 1)]
materialize_code nafRunDec

theorem nafRunDec_ct : RegCT [.esi] nafRunDec :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunTest : Prog isa := .block [.alu .test .esi (.reg .esi)]
materialize_code nafRunTest

theorem nafRunTest_ct : RegCT [.esi] nafRunTest :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunInfinity : Prog isa := .block (Jacobian.infinity nafK nafK.R)
materialize_code nafRunInfinity

theorem nafRunInfinity_ct : ScratchCT nafRunInfinity :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunInitCounter : Prog isa := .block [.mov .esi (.imm 256)]
materialize_code nafRunInitCounter

theorem nafRunInitCounter_ct : RegCT [.esi] nafRunInitCounter :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

def nafRunFinish : Prog isa := Naf.finish nafK p256Comb.SP
materialize_code nafRunFinish

theorem nafRunFinish_ct : ScratchCT nafRunFinish :=
  Taint.constantTime (A:=sseTaint) _ (fun _ _ _ _ h => h) (by taint_decide)

theorem nafWindow_checks : NafWindowChecks nafK p256Comb.SP :=
  ⟨nafTable_checks,
    ⟨⟨nafRunRead_ct,⟨nafRunLookup_ct,nafRunSign_ct,nafRunAbs_ct,nafRunNeg_ct⟩,
      nafDigitAdd_checks,nafRunCopy_ct⟩,nafRunDouble_ct,nafRunDec_ct,nafRunTest_ct⟩,
    nafRunInfinity_ct,nafRunInitCounter_ct,nafRunFinish_ct⟩

end VG.Proof.Ecdsa.Verify.X86
