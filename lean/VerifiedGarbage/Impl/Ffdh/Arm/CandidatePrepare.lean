module

public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedPrepare

/-! Parameter search knows the candidate's leading bits. Only byte counts
congruent to one modulo eight can leave q's highest radix word empty. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.CandidatePrepare
open VG VG.Arm

def choose : List Instr := [.dp .and .r1 .r6 (.imm 7), .cmp .r1 (.imm 1)]

/-- Both preparations' Montgomery products are `op`; their doublings are inline. -/
def code (op : Nat → Nat → Nat → Prog isa) : Prog isa := .seq (.block choose)
  (.ite .eq (SharedPrepare.code op VG.Impl.Bignum.Arm.doubleLoopMultiply)
    (NormalizedPrepare.code op VG.Impl.Bignum.Arm.doubleLoopMultiply))

end VG.Impl.Ffdh.Arm.CandidatePrepare
