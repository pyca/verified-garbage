module


/-!
# Argon2 derivation on PPC64LE: the frame

`vg_argon2` allocates a frame of `locals` bytes, at whose stack pointer `r30`
points for the whole derivation, and `r31` points to `scratch`. Above the
frame's 32-byte header, the frame holds:

* `[32, 96)`: H₀, followed by LE32(column) and LE32(lane): the 72-byte input
  of H′ for the first two blocks of each lane;
* the return address and the caller's `r28`–`r31`;
* the eight register arguments (the other ten are in the caller's Parameter
  Save Area, above the frame);
* the pass, lane, slice and index of the filling loops, and the one-based
  counter of the address block in `scratch`;
* the lane length (in blocks and in bytes) and the segment length;
* the byte count of H₀'s input, and temporaries.

Every value in the frame but H₀, the random word and the reference block
is public.
-/

@[expose] public section

namespace VG.Impl.Argon2.PPC64LE.Derive

/-- The size of the frame. -/
def locals : Nat := 336

/-- Where argument `i` is: in the frame for the register arguments, else in
the caller's Parameter Save Area (`sp + 32 + 8 * i` on entry). -/
def argOff (i : Nat) : Nat := if i < 8 then 144 + 8 * i else locals + 32 + 8 * i

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

def h0Off : Nat := 32
def columnOff : Nat := 96
def laneWordOff : Nat := 100
def lrOff : Nat := 104
def passOff : Nat := 208
def laneOff : Nat := 216
def sliceOff : Nat := 224
def indexOff : Nat := 232
def counterOff : Nat := 240
def laneLenOff : Nat := 248
def strideOff : Nat := 256
def segLenOff : Nat := 264
def countOff : Nat := 272
def j1Off : Nat := 280
def j2Off : Nat := 288
def refLaneOff : Nat := 296
def startOff : Nat := 304
def curOff : Nat := 312
def cntOff : Nat := 320
def tmpOff : Nat := 328

end VG.Impl.Argon2.PPC64LE.Derive
