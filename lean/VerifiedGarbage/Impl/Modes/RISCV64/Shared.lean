module

public import VerifiedGarbage.Impl.Modes.RISCV64.Seq

/-!
# Shared cipher cores for RISC-V modes

The caller's return address waits after the original core's frame, outside
anything the core writes. The mode wipes these two additional slots along
with the rest of its frame. Calls may clobber every temporary register, so
both the callee and the reload compute their addresses from `sb`.
-/

@[expose] public section

namespace VG.Impl.Modes.RISCV64

open VG.RISCV64

/-- Address of the saved return address, using encodable immediates for
cores of up to 761 slots. -/
def returnAddr (slots : Nat) : List Instr :=
  if slots < 508 then
    [.addi .t6 sb 2032, .addi .t6 .t6 ((8 * slots : Int) - 2032)]
  else
    [.addi .t6 sb 2032, .addi .t6 .t6 2032, .addi .t6 .t6 ((8 * slots : Int) - 4064)]

/-- Call a core's body, preserving the caller's return address in slot
`slots`. The body keeps `sb` and its own return address. -/
def sharedCall (name : String) (body : Prog isa) (slots : Nat) : Prog isa :=
  .seq (.block (returnAddr slots ++ [.store .d .ra .t6 0]))
    (.seq (.call name body) (.block (returnAddr slots ++ [.load .d .ra .t6 0])))

/-- Name and share the preparation and batch code. Two slots keep the
frame aligned and hold the return address. -/
def Core.shared (c : Core) (prepareName : String) (cryptName : String) : Core :=
  { c with
    prepare := sharedCall prepareName c.prepare c.total
    crypt := sharedCall cryptName c.crypt c.total
    total := c.total + 2 }

end VG.Impl.Modes.RISCV64
