module
public import VerifiedGarbage.TCB.AArch64.Isa


/-! Share the arithmetic window while its square helper uses a different link lane. -/

@[expose] public section
namespace VG.Impl.Rsa.AArch64.WindowCall
open VG VG.AArch64

def save : List Instr := [.vop (.ins .d2 .v7 0 .x30)]
def restore : List Instr := [.umov .x .x30 .v7 0]
def call (name : String) (body : Prog isa) : Prog isa :=
  .seq (.block save) (.seq (.call name body) (.block restore))

end VG.Impl.Rsa.AArch64.WindowCall
