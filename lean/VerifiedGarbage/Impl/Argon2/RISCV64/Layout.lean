module


/-!
# Argon2 derivation on RISC-V: the frame

`vg_argon2` allocates a frame of `locals` bytes, at whose stack pointer `s3`
points for the whole derivation; `s4` points to `scratch`, and `s0` 2048
bytes above that (H′ keeps all three, and `s1`
and `s2`, which memory initialization uses). The frame holds:

* `[0, 72)`: H₀, followed by LE32(column) and LE32(lane): the 72-byte input
  of H′ for the first two blocks of each lane;
* the return address and the caller's `s0`–`s4`;
* the eight register arguments (the other ten are on the caller's stack, at
  the stack pointer on entry, above the frame);
* the pass, lane, slice and index of the filling loops, and the one-based
  counter of the address block;
* the lane length (in blocks and in bytes) and the segment length;
* the byte count of H₀'s input, and temporaries.

Every value in the frame but H₀, the random word and the reference block
is public.
-/

@[expose] public section

namespace VG.Impl.Argon2.RISCV64.Derive

/-- The size of the frame, a multiple of 16. -/
def locals : Nat := 320

/-- Where argument `i` is: in the frame for the register arguments, else on
the caller's stack (`sp + 8 * (i - 8)` on entry). -/
def argOff (i : Nat) : Nat := if i < 8 then 120 + 8 * i else locals + 8 * (i - 8)

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

def h0Off : Nat := 0
def columnOff : Nat := 64
def laneWordOff : Nat := 68
def raOff : Nat := 72
def passOff : Nat := 184
def laneOff : Nat := 192
def sliceOff : Nat := 200
def indexOff : Nat := 208
def counterOff : Nat := 216
def laneLenOff : Nat := 224
def strideOff : Nat := 232
def segLenOff : Nat := 240
def countOff : Nat := 248
def j1Off : Nat := 256
def j2Off : Nat := 264
def refLaneOff : Nat := 272
def startOff : Nat := 280
def curOff : Nat := 288
def cntOff : Nat := 296
def tmpOff : Nat := 304

end VG.Impl.Argon2.RISCV64.Derive
