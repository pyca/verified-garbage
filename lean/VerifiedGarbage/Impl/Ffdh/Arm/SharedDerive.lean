module

public import VerifiedGarbage.Impl.Ffdh.Arm.SharedExchange

/-! An imported scalar's public value through the shared RSA Montgomery helper.

`vg_ffdh_derive_public`: x checked as `vg_ffdh_check_private` checks it
(zeros written and 2 returned otherwise, the one branch on x); then
`y = g^x mod p` over x's `x_len` bytes, as the exchange raises its peer value,
y's range as the acceptance (a power of the checked generator is in its
subgroup), y written (zeros unless accepted) and `3 − 2 flag` returned. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Impl.Ffdh.Arm.Domain

/-- `(y, y_len, domain, domain_len)` in r0–r3; `p_len`, x, `x_len` and the
scratch at 128, 132, 136 and 140 above the frame. -/
def entry : List Instr := [
  .addSp .r12 0, st .r0 4, st .r2 24, st .r3 28,
  .ldrSp .r3 128, st .r3 32, .ldrSp .r3 132, st .r3 40,
  .ldrSp .r3 136, st .r3 44, .ldrSp .r0 140, st .r0 0]

/-- `3 − 2 flag` from the flag in r0. -/
def status : List Instr := [.dp .add .r0 .r0 (.reg .r0), .mov .r3 (.imm 3), .dp .sub .r0 .r3 (.reg .r0)]

/-- The flag, zero on this path, masks y to zeros; 2 is returned. -/
def fail : Prog isa := .seq (.block Exchange.saveResult) (.seq Exchange.maskOutput (ret 2))

/-- `g^x mod p`, its range as the acceptance, y written and the status. -/
def tail (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt op 56 40 44)
    (.seq (VG.Impl.Ffdh.Arm.inRange 6) (.seq SharedExchange.finish (.block status)))

def main (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt op 24) (.seq (importAt 1 40 44)
    (.seq CheckPrivate.scalarRange (ifFlag (tail op) fail)))

def code (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  VG.Impl.Ffdh.Arm.framed (.seq (.block entry) (head (main op)))

end VG.Impl.Ffdh.Arm.SharedDerive
