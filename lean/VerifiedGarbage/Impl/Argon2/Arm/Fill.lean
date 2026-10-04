import VerifiedGarbage.Impl.Argon2.Arm.MemoryInit
import VerifiedGarbage.Impl.Argon2.Arm.Compress
import VerifiedGarbage.Spec.Argon2.Contract

/-!
# Argon2 on ARMv7: filling the memory

The pass, lane, slice and index are in the locals (`r11`), so every register
but `r11` and `sp` is free within a block's update (`fillBlock`):

* the random word (J₁, J₂) is read from the previous block (data-dependent
  addressing) or from the cached address block in `scratch[6144, 7168)`,
  which two calls of `vg_argon2_compress` regenerate every 128 blocks of a
  segment (`scratch[0, 4096)` is G's working space, `[4096, 5120)` its output,
  `[5120, 6144)` the input block and `[7168, 8192)` the zero block);
* the reference lane is J₂ modulo the lane count (the fixed-time division), but
  the current lane in the first slice of the first pass;
* the reference column maps J₁ into the window of eligible blocks
  (RFC 9106 §3.4.2), with the high halves of products as in `addMul`
  (`mulHi`), choosing between the windows of the current lane and of another
  one with a mask rather than a branch;
* G of the previous and reference blocks goes to `scratch[4096, 5120)`, and is
  copied to the current block (first pass) or XORed into it.

Branches and addresses depend only on the public parameters and loop
position, but for the addresses of the previous block's first word (public:
its position is) and of the reference block, which data-dependent addressing
permits to leak.
-/

namespace VG.Impl.Argon2.Arm.Derive

open VG.Arm

/-! ## Block addresses -/

/-- `r0 := memory + 1024 · (r0 · laneLen + r1)`: block `r1` of lane `r0`. -/
def blockAddr : List Instr :=
  [ld .r2 laneLenOff, .mul .r0 .r0 .r2, .dp .add .r0 .r0 (.reg .r1), ld .r2 (argOff memoryArg),
    .dp .add .r0 .r2 (.shifted .r0 .lsl 10)]

/-- `r1 :=` the current column, `slice · segLen + index`. -/
def column : List Instr :=
  [ld .r0 sliceOff, ld .r2 segLenOff, .mul .r0 .r0 .r2, ld .r2 indexOff, .dp .add .r1 .r0 (.reg .r2)]

/-- `r1 :=` the column before `r1`, cyclically. -/
def prevColumn : Prog isa :=
  .seq (.block [.cmp .r1 (.imm 0)])
    (.seq (.ite .eq (.block [ld .r1 laneLenOff]) (.block [])) (.block [.dp .sub .r1 .r1 (.imm 1)]))

/-- `r0 :=` the address of the previous block. -/
def prevPointer : Prog isa :=
  .seq (.block column) (.seq prevColumn (.block (ld .r0 laneOff :: blockAddr)))

/-! ## The random word -/

/-- Z for data-dependent addressing: neither Argon2i nor Argon2id in the
first two slices of the first pass. `r1` is zero for Argon2i, `r2` for
Argon2id in those slices; `r12` and `r0` are whether each is not zero
(`((0 - x) | x) >> 31`), and their product is whether the addressing is
data-dependent, which `eor` with 1 makes zero. -/
def addressMode : List Instr :=
  [ld .r0 (argOff kindArg), .dp .eor .r1 .r0 (.imm 1), .dp .eor .r2 .r0 (.imm 2), ld .r3 passOff,
    .dp .orr .r2 .r2 (.reg .r3), ld .r3 sliceOff, .dp .orr .r2 .r2 (.shifted .r3 .lsr 1),
    .mov .r3 (.imm 0), .dp .sub .r12 .r3 (.reg .r1), .dp .orr .r12 .r12 (.reg .r1),
    .mov .r12 (.shifted .r12 .lsr 31), .dp .sub .r0 .r3 (.reg .r2), .dp .orr .r0 .r0 (.reg .r2),
    .mov .r0 (.shifted .r0 .lsr 31), .dp .and .r12 .r12 (.reg .r0), .dp .eor .r12 .r12 (.imm 1),
    .cmp .r12 (.imm 0)]

/-- Data-dependent addressing: J₁, J₂ are the first word of the previous block. -/
def dependentWord : Prog isa :=
  .seq prevPointer
    (.block [.ldr .r1 .r0 0, st j1Off .r1, .ldr .r1 .r0 4, st j2Off .r1])

/-- `r2 := scratch + d` -/
def scratchAt (d : Nat) : List Instr := [ld .r2 (argOff scratchArg), .dp .add .r2 .r2 (.imm (BitVec.ofNat 32 d))]

/-- Zero `scratch[d, d + 1024)`. -/
def clearAt (d : Nat) : List Instr :=
  scratchAt d ++ .mov .r0 (.imm 0) :: (List.range 256).map fun k => .str .r0 .r2 (4 * k)

/-- The words of the address-generation input block (its other words are
zero): pass, lane, slice, blocks, passes, type and counter (§3.4.1.2). -/
def addressHeader : List Instr :=
  scratchAt 5120 ++
  [ld .r0 passOff, .str .r0 .r2 0, ld .r0 laneOff, .str .r0 .r2 8, ld .r0 sliceOff, .str .r0 .r2 16,
    ld .r0 (argOff blocksArg), .str .r0 .r2 24, ld .r0 (argOff iterationsArg), .str .r0 .r2 32,
    ld .r0 (argOff kindArg), .str .r0 .r2 40, ld .r0 counterOff, .str .r0 .r2 48]

def compressName : String := Spec.Argon2.compressApi.name

/-- `compress(r0, r1, r2, r3)`. -/
def compressCall : Prog isa := .call compressName Impl.Argon2.Arm.compress

/-- G(`scratch + x`, `scratch + y`) to `scratch + out`. -/
def stage (x y out : Nat) : Prog isa :=
  .seq (.block [ld .r3 (argOff scratchArg), .dp .add .r0 .r3 (.imm (BitVec.ofNat 32 x)),
      .dp .add .r1 .r3 (.imm (BitVec.ofNat 32 y)), .dp .add .r2 .r3 (.imm (BitVec.ofNat 32 out))])
    compressCall

/-- The address block: G(0, G(0, input)). -/
def addressCalls : Prog isa :=
  .seq (.block (clearAt 5120 ++ clearAt 7168 ++ addressHeader))
    (.seq (stage 7168 5120 4096) (stage 7168 4096 6144))

/-- `r0 :=` the counter of the address block for the index; Z if it is the
cached one. -/
def cacheCheck : List Instr :=
  [ld .r0 indexOff, .mov .r0 (.shifted .r0 .lsr 7), .dp .add .r0 .r0 (.imm 1), ld .r1 counterOff,
    .cmp .r0 (.reg .r1)]

/-- J₁, J₂: word `index mod 128` of the address block. -/
def cacheWord : List Instr :=
  [ld .r0 indexOff, .dp .and .r0 .r0 (.imm 127), ld .r1 (argOff scratchArg),
    .dp .add .r0 .r1 (.shifted .r0 .lsl 3), .dp .add .r0 .r0 (.imm 6144),
    .ldr .r1 .r0 0, st j1Off .r1, .ldr .r1 .r0 4, st j2Off .r1]

/-- Data-independent addressing, regenerating the address block when the
index enters a new group of 128. -/
def addressCache : Prog isa :=
  .seq (.block cacheCheck)
    (.seq (.ite .eq (.block []) (.seq (.block [st counterOff .r0]) addressCalls)) (.block cacheWord))

def randomSource : Prog isa := .seq (.block addressMode) (.ite .eq dependentWord addressCache)

/-! ## The reference block -/

/-- The reference lane: J₂ mod lanes, or the current lane in the first slice of
the first pass. -/
def refLane : Prog isa :=
  .seq (.block ([ld .r1 j2Off, ld .r2 (argOff lanesArg)] ++ Divide.code ++
      [st refLaneOff .r0, ld .r0 passOff, ld .r1 sliceOff, .dp .orr .r0 .r0 (.reg .r1), .cmp .r0 (.imm 0)]))
    (.ite .eq (.block [ld .r0 laneOff, st refLaneOff .r0]) (.block []))

/-- Where the window starts: 0 in the first pass, else the next slice (0 after
the last one). -/
def refStart : Prog isa :=
  .seq (.block [.mov .r0 (.imm 0), st startOff .r0, ld .r1 passOff, .cmp .r1 (.imm 0)])
    (.ite .eq (.block [])
      (.seq (.block [ld .r1 sliceOff, .cmp .r1 (.imm 3)])
        (.ite .eq (.block [])
          (.block [ld .r0 sliceOff, .dp .add .r0 .r0 (.imm 1), ld .r2 segLenOff, .mul .r0 .r0 .r2,
            st startOff .r0]))))

/-- `r0 :=` the blocks before the current segment that a reference may use:
`slice · segLen` in the first pass, three segments after it. -/
def countBase : Prog isa :=
  .seq (.block [ld .r1 passOff, .cmp .r1 (.imm 0)])
    (.ite .eq (.block [ld .r0 sliceOff, ld .r2 segLenOff, .mul .r0 .r0 .r2])
      (.block [ld .r0 laneLenOff, ld .r2 segLenOff, .dp .sub .r0 .r0 (.reg .r2)]))

/-- The window's size: `base + index - 1` blocks in the current lane, `base`
(less one at index 0) in another one, chosen by a mask. `((0 - x) | x) >> 31`
is whether `x` is not zero, and less one, all ones if it is zero. -/
def countSelect : List Instr :=
  [ld .r2 indexOff, .dp .add .r1 .r0 (.reg .r2), .dp .sub .r1 .r1 (.imm 1),
    .mov .r3 (.imm 0), .dp .sub .r3 .r3 (.reg .r2), .dp .orr .r3 .r3 (.reg .r2), .mov .r3 (.shifted .r3 .lsr 31),
    .dp .sub .r3 .r3 (.imm 1), .dp .add .r0 .r0 (.reg .r3),
    ld .r2 refLaneOff, ld .r3 laneOff, .dp .eor .r2 .r2 (.reg .r3),
    .mov .r3 (.imm 0), .dp .sub .r3 .r3 (.reg .r2), .dp .orr .r3 .r3 (.reg .r2), .mov .r3 (.shifted .r3 .lsr 31),
    .dp .sub .r2 .r3 (.imm 1),
    .dp .eor .r1 .r1 (.reg .r0), .dp .and .r1 .r1 (.reg .r2), .dp .eor .r0 .r0 (.reg .r1), st countOff .r0]

/-- `r0 := count - 1 - ⌊count · ⌊J₁² / 2³²⌋ / 2³²⌋`. -/
def relative : List Instr :=
  [ld .r4 j1Off] ++ mulHi .r4 .r4 .r0 .r1 .r2 .r3 .r12 ++ [ld .r5 countOff, .mov .r6 (.reg .r2)] ++
    mulHi .r5 .r6 .r0 .r1 .r2 .r3 .r12 ++ [.dp .sub .r0 .r5 (.imm 1), .dp .sub .r0 .r0 (.reg .r2)]

/-- `r0 := (start + r0) mod laneLen`, by one masked subtraction. -/
def wrap : List Instr :=
  [ld .r2 startOff, .dp .add .r0 .r0 (.reg .r2), ld .r2 laneLenOff, .mov .r3 (.imm 0),
    .subs .r0 .r0 (.reg .r2), .adc .r3 .r3 (.imm 0), .dp .sub .r3 .r3 (.imm 1), .dp .and .r3 .r3 (.reg .r2),
    .dp .add .r0 .r0 (.reg .r3)]

/-- The reference block's address, to `[r11, #tmpOff]`. -/
def refPointer : List Instr := [.mov .r1 (.reg .r0), ld .r0 refLaneOff] ++ blockAddr ++ [st tmpOff .r0]

/-- The current block's address, to `[r11, #curOff]`. -/
def curPointer : List Instr := column ++ ld .r0 laneOff :: blockAddr ++ [st curOff .r0]

def reference : Prog isa :=
  .seq refLane (.seq refStart (.seq countBase
    (.block (countSelect ++ relative ++ wrap ++ refPointer ++ curPointer))))

/-! ## The new block -/

/-- G(previous, reference) to `scratch[4096, 5120)`. -/
def fillCompress : Prog isa :=
  .seq prevPointer
    (.seq (.block [ld .r1 tmpOff, ld .r3 (argOff scratchArg), .dp .add .r2 .r3 (.imm 4096)]) compressCall)

/-- 32-bit word `k` from `r1` to `r3`, XORed into the old one if `xorOld`. -/
def writeWord (xorOld : Bool) (k : Nat) : List Instr :=
  .ldr .r0 .r1 (4 * k) ::
    ((if xorOld then [.ldr .r2 .r3 (4 * k), .dp .eor .r0 .r0 (.reg .r2)] else []) ++
      [.str .r0 .r3 (4 * k)])

def writeBlock (xorOld : Bool) : List Instr := (List.range 256).flatMap (writeWord xorOld)

/-- The new block to the current one: copied in the first pass, XORed later. -/
def fillWrite : Prog isa :=
  .seq (.block [ld .r1 (argOff scratchArg), .dp .add .r1 .r1 (.imm 4096), ld .r3 curOff, ld .r0 passOff,
      .cmp .r0 (.imm 0)])
    (.ite .eq (.block (writeBlock false)) (.block (writeBlock true)))

def fillBlock : Prog isa := .seq randomSource (.seq reference (.seq fillCompress fillWrite))

/-! ## The loops -/

/-- `[r11, #d] += 1`, compared with `[r11, #o]`. -/
def advance (d o : Nat) : List Instr :=
  [ld .r0 d, .dp .add .r0 .r0 (.imm 1), st d .r0, ld .r1 o, .cmp .r0 (.reg .r1)]

/-- `[r11, #d] += 1`, compared with `v`. -/
def advanceImm (d : Nat) (v : BitVec 32) : List Instr :=
  [ld .r0 d, .dp .add .r0 .r0 (.imm 1), st d .r0, .cmp .r0 (.imm v)]

/-- `[r11, #d] := v` -/
def setLocal (d : Nat) (v : BitVec 32) : List Instr := [.mov .r0 (.imm v), st d .r0]

/-- The first index of a segment: 2 in the first slice of the first pass
(whose first two blocks are initialized), else 0; and a new address block. -/
def segmentStart : Prog isa :=
  .seq (.block (setLocal counterOff 0 ++ [ld .r0 passOff, ld .r1 sliceOff, .dp .orr .r0 .r0 (.reg .r1),
      .cmp .r0 (.imm 0)]))
    (.ite .eq (.block (setLocal indexOff 2)) (.block (setLocal indexOff 0)))

def segment : Prog isa :=
  .seq segmentStart
    (.seq (.block [ld .r0 indexOff, ld .r1 segLenOff, .cmp .r0 (.reg .r1)])
      (.ite .eq (.block []) (.loop (.seq fillBlock (.block (advance indexOff segLenOff))) .ne)))

def lanesLoop : Prog isa :=
  .seq (.block (setLocal laneOff 0))
    (.loop (.seq segment (.block (advance laneOff (argOff lanesArg)))) .ne)

def slicesLoop : Prog isa :=
  .seq (.block (setLocal sliceOff 0)) (.loop (.seq lanesLoop (.block (advanceImm sliceOff 4))) .ne)

def passesLoop : Prog isa :=
  .seq (.block (setLocal passOff 0))
    (.loop (.seq slicesLoop (.block (advance passOff (argOff iterationsArg)))) .ne)

end VG.Impl.Argon2.Arm.Derive
