module

public import VerifiedGarbage.Impl.Modes.Arm.Seq

/-!
# Block cipher modes on ARMv7, one block at a time, from keys prepared once

A cipher whose ECB function prepares its keys in its working space at every
call (a bitsliced cipher's table of subkeys) may split that function in two
(`Keyed`): one that prepares the keys there, `keys(schedule = r0,
scratch = r1)` (or `keys(schedule = r0, rounds = r1, scratch = r2)` for a
cipher with a number of rounds), and one with the ECB function's arguments
that enciphers the blocks with the keys it finds there, and leaves them.

`seqK core keyed mode` is `seq core mode` (`Seq.lean`) for a core that takes
a working space, with the first called once, before the first block
(`keysStep`), and the second for each block (`Keyed.callStep`, in place of the
core's `callStep`): a mode whose every block needs the one before, and so
calls the cipher on one block at a time, then prepares the keys once in a
call rather than for every block. A call on no blocks prepares no keys.

The keys wait in the callee's working space, at the end of the mode's
scratch buffer, which nothing else writes; the preparation, like every
call, keeps `r4`–`r8` and `r11`.
-/

@[expose] public section

namespace VG.Impl.Modes.Arm

open VG.Arm

/-- The two functions that split the ECB function of a core which takes a
working space: their names and code. -/
structure Keyed where
  /-- The function that prepares the keys in the working space. -/
  keysName : String
  keysCode : Prog isa
  /-- The function that enciphers blocks with the keys in the working space. -/
  name : String
  code : Prog isa

/-- The call of the function that enciphers with the prepared keys, as
`Core.callStep` calls the ECB function of a core with a working space. -/
def Keyed.callStep (k : Keyed) : Prog isa := .frame (.push [.r12, .lr]) (.call k.name k.code) (.pop .r12 8)

namespace Core

variable (c : Core)

/-- The arguments of the keys' preparation: the schedule, the number of
rounds (if any), and the callee's working space. -/
def keysArgs : List Instr :=
  mov .r0 .r4 :: ((if c.rounds then [mov .r1 .r11] else []) ++
    [.dp .add c.dReg .r8 (.imm (BitVec.ofNat 32 c.csOff))])

/-- The keys prepared in the callee's working space. -/
def keysStep (k : Keyed) : Prog isa := .seq (.block c.keysArgs) (.call k.keysName k.keysCode)

/-- One block, enciphered with the prepared keys. -/
def bodyK (k : Keyed) (m : Mode) : Prog isa :=
  .seq (.block (c.opsCode m.pre ++ c.callArgs m.tgt)) (.seq k.callStep
    (.block (c.opsCode m.post ++ c.advance m)))

/-- The whole function, the keys prepared once if there are blocks. -/
def seqK (k : Keyed) (m : Mode) : Prog isa :=
  .seq (.block (c.save ++ c.setup)) (.seq (.ite .eq (.block []) (.seq (c.keysStep k) (.loop (c.bodyK k m) .ne)))
    (.block (c.finish m ++ restore)))

end Core

end VG.Impl.Modes.Arm
