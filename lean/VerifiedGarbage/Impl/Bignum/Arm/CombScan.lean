module

public import VerifiedGarbage.Impl.Bignum.Arm.WindowExp

/-! Every digit scans all 32 contiguous, read-only comb entries. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.CombScan
open VG VG.Arm VG.Impl.Bignum.Arm

def init : List Instr :=
  [.ldr .r12 .r0 232, .str .r12 .r0 220, .mov .r1 (.imm 0), .str .r1 .r0 228]

def next : List Instr :=
  [.ldr .r1 .r0 220, .ldr .r2 .r0 48, .dp .add .r1 .r1 (.shifted .r2 .lsl 3),
   .str .r1 .r0 220, .ldr .r1 .r0 228, .dp .add .r1 .r1 (.imm 1), .str .r1 .r0 228,
   .cmp .r1 (.imm 32)]

/-- The existing selection row hoists its mask outside its word loop. -/
def body : Prog isa :=
  .seq (.block (scanBit ++ scanArgs))
    (.seq selectRow (.seq (.block [.ldrSp .r0 0]) (.block next)))

def code : Prog isa := .seq (.block init) (.loop body .ne)

end VG.Impl.Bignum.Arm.CombScan
