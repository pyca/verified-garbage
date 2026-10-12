module

public import VerifiedGarbage.Impl.Argon2.Arm.HPrime

/-!
# Argon2 derivation on ARMv7: the frame

`vg_argon2` pushes its four register arguments (`r0`–`r3`) in a frame below
its fourteen stack arguments, so that all eighteen are consecutive words;
then the caller's `r4`–`r11` and its return address (with `r3`, keeping the
stack pointer 8-byte aligned) in a second frame; then a frame of `locals`
bytes, at which `r11` points for the whole derivation. Its arguments are then
at `[r11, #argOff i]`. The locals are:

* `[0, 64)`: H₀, followed by LE32(column) and LE32(lane): the 72-byte input
  of H′ for the first two blocks of each lane;
* the pass, lane, slice and index of the filling loops, and the one-based
  counter of the address block in `scratch`;
* the lane length (in blocks and in bytes) and the segment length;
* the byte count of H₀'s input (64 bits), and temporaries.

Every value in the locals but H₀, the random word and the reference block
is public.
-/

@[expose] public section

namespace VG.Impl.Argon2.Arm.Derive

/-- The size of the locals. -/
def locals : Nat := 144

/-- Where argument `i` is: above the locals and the saved registers. -/
def argOff (i : Nat) : Nat := locals + 40 + 4 * i

/-! ## The arguments -/

def kindArg : Nat := 0
def passwordArg : Nat := 1
def passwordLenArg : Nat := 2
def saltArg : Nat := 3
def saltLenArg : Nat := 4
def iterationsArg : Nat := 5
def memoryCostArg : Nat := 6
def lanesArg : Nat := 7
def secretArg : Nat := 9
def secretLenArg : Nat := 10
def adArg : Nat := 11
def adLenArg : Nat := 12
def memoryArg : Nat := 13
def blocksArg : Nat := 14
def scratchArg : Nat := 15
def outArg : Nat := 16
def outLenArg : Nat := 17

/-! ## The locals -/

def columnOff : Nat := 64
def laneWordOff : Nat := 68
def passOff : Nat := 72
def laneOff : Nat := 76
def sliceOff : Nat := 80
def indexOff : Nat := 84
def counterOff : Nat := 88
def laneLenOff : Nat := 92
def strideOff : Nat := 96
def segLenOff : Nat := 100
def countLoOff : Nat := 104
def countHiOff : Nat := 108
def j1Off : Nat := 112
def j2Off : Nat := 116
def refLaneOff : Nat := 120
def startOff : Nat := 124
def curOff : Nat := 128
def divisorOff : Nat := 132
def countOff : Nat := 136
def tmpOff : Nat := 140

end VG.Impl.Argon2.Arm.Derive
