module

public import VerifiedGarbage.Impl.Bignum.Arm.FiosPipelined

/-! Public word counts select fixed scans at the common primality-test widths. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.FiosFast
open VG VG.Arm VG.Impl.Bignum.Arm

def choose (n : BitVec 32) : List Instr := [.cmp .lr (.imm n)]
def code : Prog isa :=
  .seq (.block (choose 16)) (.ite .eq (FiosPipelined.code 16)
    (.seq (.block (choose 32)) (.ite .eq (FiosPipelined.code 32)
      (.seq (.block (choose 64)) (.ite .eq (FiosPipelined.code 64)
        (.seq (.block (choose 128)) (.ite .eq (FiosPipelined.code 128) Fios.code)))))))
def round : Prog isa := .seq (.block Fios.args) (.seq code (.block roundFinish))

end VG.Impl.Bignum.Arm.FiosFast
