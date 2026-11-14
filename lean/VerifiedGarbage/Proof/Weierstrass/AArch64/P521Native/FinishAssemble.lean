module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishCounter
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishCopy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishProjective
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFixY
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishLookup
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAddCode
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishInverse
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishProducts
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishChecks
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Exact concatenation of the final independent machine-level phases. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native
open VG.Impl.Ecdsa.AArch64 (D RZ)

def finishFiveDoubles : Prog isa := .seq loop25 (.seq (.block outerBlock148) callNormalDouble)
def finishCheckCode : List Instr := config.checkRange (config.sl D)++config.checkNonzero (config.sl RZ)++
  VG.Impl.Ecdh.AArch64.Cfg.finish config

def finishStages : Prog isa := sequence [
  .block outerBlock144,finishFiveDoubles,.block finishCopyPoint,finishProjectiveMachine,
  .block finishCopyPoint,.block finishFixYCode,.block finishLookupCode,finishAddMachine,
  .block finishCopyPoint,finishInversePhase,finishProductsMachine,.block finishCheckCode]

theorem finish_partition149 : outerBlock149=finishCopyPoint++outerBlock149.drop 54 := by lit_decide

theorem finish_partition152 : outerBlock152=outerBlock152.take 53++finishCopyPoint++
    finishFixYCode++finishLookupCode++outerBlock152.drop (outerBlock152.length-4) := by lit_decide

theorem finish_partition166 : outerBlock166=outerBlock166.take 53++finishCopyPoint := by lit_decide

theorem finish_partition171 : outerBlock171=buildRestore++finishCheckCode := by
  exact finish_output_source

/-- Every contract proved for the separated final phases applies to the full
exact native finishAndWrite, with no removed checks or instructions. -/
theorem finish_stages_wp {s : State} {Q : State → Prop} (h : WP isa finishStages s Q) :
    WP isa finishAndWrite s Q := by
  simp only [finishAndWrite,sequence,List.foldr_cons,List.foldr_nil]
  rw [finish_partition149,finish_partition152,finish_partition166,finish_partition171]
  simp only [finishStages,finishFiveDoubles,finishProjectiveMachine,finishAddMachine,finishInversePhase,
    finishProductsMachine,sequence,List.foldr_cons,List.foldr_nil] at h
  simp only [VG.WP.seq_iff (M:=isa),VG.WP.block_append_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)] at h ⊢
  exact h

end VG.Proof.Weierstrass.AArch64.P521Native
