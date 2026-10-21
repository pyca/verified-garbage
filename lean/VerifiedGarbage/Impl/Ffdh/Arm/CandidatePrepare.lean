module

public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare

/-! Parameter search knows the candidate's leading bits. Only byte counts
congruent to one modulo eight can leave q's highest radix word empty. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.CandidatePrepare
open VG VG.Arm VG.Impl.Bignum.Arm

def choose : List Instr := [.dp .and .r1 .r6 (.imm 7), .cmp .r1 (.imm 1)]

def code : Prog isa := .seq (.block choose)
  (.ite .eq VG.Impl.Ffdh.Arm.prepare (NormalizedPrepare.code montOp))

end VG.Impl.Ffdh.Arm.CandidatePrepare
