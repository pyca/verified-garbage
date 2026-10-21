module

public import VerifiedGarbage.Impl.Bignum.Arm.CombExp
public import VerifiedGarbage.Impl.Bignum.Arm.ExpControls

/-! Cached key generation loads the public comb controls once per attempt. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Impl.Bignum.Arm

def load : List Instr := [.ldrSp .r1 16,.ldrSp .r2 20,.ldrSp .r4 52]

def metadata : List Instr :=
  [.ldr .r1 .r4 0,.ldr .r2 .r4 16,.ldr .r3 .r0 48,.mov .r3 (.shifted .r3 .lsl 4),
   .dp .add .r4 .r4 (.reg .r3),.dp .add .r4 .r4 (.imm 24)]

def save : List Instr := [.str .r1 .r0 136,.str .r2 .r0 204,.str .r4 .r0 232]

def args : Prog isa :=
  .seq (.block load) (.seq (.block expControls) (.seq (.block metadata) (.block save)))

def code (op : Nat→Nat→Nat→Prog isa) : Prog isa := .seq args (CombExp.phase op)

end VG.Impl.Ffdh.Arm.CachedPower
