module

public import VerifiedGarbage.Impl.Bignum.Arm.ActivateWorkspace

/-! # Select a CRT workspace while keeping a stable main-workspace pointer

After importing the public modulus, its saved pointer slot (8) is reused
for the main workspace. Slot 0 tracks the workspace used by arithmetic.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def saveMain : List Instr := [.addSp .r12 8, .str .r0 .r12 0]
def selectChild (slot : Nat) : Prog isa :=
  .seq (.block [.ldr .r0 .r0 slot]) (.block activateWorkspace)
def selectMain : Prog isa := .seq (.block [.ldrSp .r0 8]) (.block activateWorkspace)

end VG.Impl.Bignum.Arm.Crt
