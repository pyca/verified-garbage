module

public import VerifiedGarbage.Impl.Bignum.Arm.FiosFixed

/-! Public word counts select fixed scans at the common primality-test widths. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.FiosFast
open VG VG.Arm VG.Impl.Bignum.Arm

def choose (n : BitVec 32) : List Instr := [.cmp .lr (.imm n)]
def code : Prog isa :=
  .seq (.block (choose 16)) (.ite .eq (FiosFixed.code 16)
    (.seq (.block (choose 32)) (.ite .eq (FiosFixed.code 32) Fios.code)))
def round : Prog isa := .seq (.block Fios.args) (.seq code (.block roundFinish))

end VG.Impl.Bignum.Arm.FiosFast
