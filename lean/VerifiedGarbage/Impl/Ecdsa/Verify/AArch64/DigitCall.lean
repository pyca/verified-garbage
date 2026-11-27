module

public import VerifiedGarbage.TCB.AArch64.Isa

@[expose] public section
namespace VG.Impl.Ecdsa.Verify.AArch64
open VG VG.AArch64

/-- Keep the outer return link in a lane the digit arithmetic does not write. -/
def callDigits (name : String) (body : Prog isa) : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v31 1 .x30)])
    (.seq (.call name body) (.block [.umov .x .x30 .v31 1]))

end VG.Impl.Ecdsa.Verify.AArch64
