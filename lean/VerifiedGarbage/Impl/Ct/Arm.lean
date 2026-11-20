module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Impl.Residue.ArmSel

/-! Bytewise comparison, saving the one callee-saved scratch register. -/

@[expose] public section

namespace VG.Impl.Ct.Arm
open VG.Arm

def step : List Instr := [
  .ldrb .r12 .r0 0, .ldrb .r4 .r2 0, .dp .eor .r12 .r12 (.reg .r4),
  .dp .orr .r3 .r3 (.reg .r12), .dp .add .r0 .r0 (.imm 1), .dp .add .r2 .r2 (.imm 1),
  .subs .r1 .r1 (.imm 1)]

def finish : Prog isa := .block [.dp .sub .r3 .r3 (.imm 1), .mov .r0 (.shifted .r3 .lsr 31)]

def equal : Prog isa :=
  .seq (.block [.mov .r3 (.imm 0), .cmp .r1 (.imm 0)])
    (.seq (.ite .eq (.block []) (.loop (.block step) .ne)) finish)

def body : Prog isa :=
  .seq (.block [.cmp .r1 (.reg .r3)]) (.ite .eq equal (.block [.mov .r0 (.imm 0)]))

def eq : Prog isa := .frame (.push [.r4]) body (.pop .r4 4)
end VG.Impl.Ct.Arm

namespace VG.Impl.Ct.Arm.Fn
open VG.Arm

/-- The words `eq` leaves secret: none (its frame saves only `r4`, which is
the caller's in both runs). -/
def eqWords : List Nat := []

/-- `vg_ct_eq` as emitted: `eq`, then its cleanup (`Impl/Residue/ArmSel.lean`):
of the 8 bytes below the stack pointer, where its frame saved `r4`, only the
words that the residue analysis (`Arm.rtaint`) finds may differ between two
runs zeroed (none), and the registers a callee may change, but its 32-bit
result, set to constants. -/
def eq : Prog isa := VG.Impl.Residue.Arm.scrubSel 32 8 eqWords VG.Impl.Ct.Arm.eq

end VG.Impl.Ct.Arm.Fn
