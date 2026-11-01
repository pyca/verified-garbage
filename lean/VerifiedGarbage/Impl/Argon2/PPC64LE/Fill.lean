module

public import VerifiedGarbage.Impl.Argon2.PPC64LE.Compress
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Impl.Argon2.PPC64LE.Initial

/-!
# Argon2 on PPC64LE: filling the memory

The pass, lane, slice and index are in the frame (`r30`), so every register
but `r30`, `r31` and the saved `r28`, `r29` is free within a block's update
(`fillBlock`):

* the random word (J₁, J₂) is read from the previous block (data-dependent
  addressing) or from the cached address block in `scratch[6144, 7168)`,
  which two calls of `vg_argon2_compress` regenerate every 128 blocks of a
  segment (`scratch[0, 4096)` is G's working space, `[4096, 5120)` its output,
  `[5120, 6144)` the input block and `[7168, 8192)` the zero block);
* the reference lane is J₂ modulo the lane count (the fixed-time division), but
  the current lane in the first slice of the first pass;
* the reference column maps J₁ into the window of eligible blocks
  (RFC 9106 §3.4.2), with the high halves of 64-bit products, choosing
  between the windows of the current lane and of another one with a mask
  rather than a branch;
* G of the previous and reference blocks goes to `scratch[4096, 5120)`, and is
  copied to the current block (first pass) or XORed into it.

Branches and addresses depend only on the public parameters and loop
position, but for the addresses of the previous block's first word (public:
its position is) and of the reference block, which data-dependent addressing
permits to leak.
-/

@[expose] public section

namespace VG.Impl.Argon2.PPC64LE.Derive

open VG.PPC64LE

/-! ## Block addresses -/

/-- `r3 := memory + 1024 · (r3 · laneLen + r4)`: block `r4` of lane `r3`. -/
def blockAddr : List Instr :=
  [ld .r5 laneLenOff, .mul .r3 .r3 .r5, .add .r3 .r3 .r4, .lsl .r3 .r3 10, lda .r5 memoryArg,
    .add .r3 .r5 .r3]

/-- `r4 :=` the current column, `slice · segLen + index`. -/
def column : List Instr :=
  [ld .r3 sliceOff, ld .r5 segLenOff, .mul .r3 .r3 .r5, ld .r5 indexOff, .add .r4 .r3 .r5]

/-- `r4 :=` the column before `r4`, cyclically. -/
def prevColumn : Prog isa :=
  .seq (.ite (.zero .d .r4) (.block [ld .r4 laneLenOff]) (.block [])) (.block [.subi .r4 .r4 1])

/-- `r3 :=` the address of the previous block. -/
def prevPointer : Prog isa :=
  .seq (.block column) (.seq prevColumn (.block (ld .r3 laneOff :: blockAddr)))

/-! ## The random word -/

/-- `d := 1` if `n ≠ 0`, else 0 (`((0 - n) | n) >> 63`, for `n < 2⁶³`), with
`t` a temporary. -/
def nonzero (d n t : Reg) : List Instr :=
  [.li t 0, .sub t t n, .logic .or t t n, .lsr .d d t 63]

/-- `r8` is 1 for data-dependent addressing: neither Argon2i nor Argon2id in
the first two slices of the first pass. `r4` is zero for Argon2i, `r5` for
Argon2id in those slices. -/
def addressMode : List Instr :=
  [ldw .r3 kindArg, .li .r4 1, .logic .xor .r4 .r3 .r4, .li .r5 2, .logic .xor .r5 .r3 .r5,
    ld .r6 passOff, .logic .or .r5 .r5 .r6, ld .r6 sliceOff, .lsr .d .r6 .r6 1,
    .logic .or .r5 .r5 .r6] ++ nonzero .r8 .r4 .r7 ++ nonzero .r6 .r5 .r7 ++
    ([.logic .and .r8 .r8 .r6] : List Instr)

/-- Data-dependent addressing: J₁, J₂ are the first doubleword of the
previous block. -/
def dependentWord : Prog isa :=
  .seq prevPointer
    (.block [.load .w .r4 .r3 0, st j1Off .r4, .load .w .r4 .r3 4, st j2Off .r4])

/-- Zero `scratch[d, d + 1024)`. -/
def clearAt (d : Nat) : List Instr :=
  .li .r3 0 :: (List.range 128).map fun k => .store .d .r3 .r31 (d + 8 * k)

/-- The doublewords of the address-generation input block (its other
doublewords are zero): pass, lane, slice, blocks, passes, type and counter
(§3.4.1.2). -/
def addressHeader : List Instr :=
  [ld .r3 passOff, .store .d .r3 .r31 5120, ld .r3 laneOff, .store .d .r3 .r31 5128,
    ld .r3 sliceOff, .store .d .r3 .r31 5136, lda .r3 blocksArg, .store .d .r3 .r31 5144,
    ldw .r3 iterationsArg, .store .d .r3 .r31 5152, ldw .r3 kindArg, .store .d .r3 .r31 5160,
    ld .r3 counterOff, .store .d .r3 .r31 5168]

def compressName : String := "vg_argon2_compress"

/-- `compress(r3, r4, r5, r6)`. -/
def compressCall : Prog isa := .call compressName Impl.Argon2.PPC64LE.compress

/-- G(`scratch + x`, `scratch + y`) to `scratch + out`. -/
def stage (x y out : Nat) : Prog isa :=
  .seq (.block [.addi .r3 .r31 x, .addi .r4 .r31 y, .addi .r5 .r31 out, HPrime.mov .r6 .r31])
    compressCall

/-- The address block: G(0, G(0, input)). -/
def addressCalls : Prog isa :=
  .seq (.block (clearAt 5120 ++ clearAt 7168 ++ addressHeader))
    (.seq (stage 7168 5120 4096) (stage 7168 4096 6144))

/-- `r3 :=` the counter of the address block for the index; `r4` is zero if
it is the cached one. -/
def cacheCheck : List Instr :=
  [ld .r3 indexOff, .lsr .d .r3 .r3 7, .addi .r3 .r3 1, ld .r4 counterOff, .sub .r4 .r3 .r4]

/-- J₁, J₂: doubleword `index mod 128` of the address block. -/
def cacheWord : List Instr :=
  [ld .r3 indexOff, .li .r4 127, .logic .and .r3 .r3 .r4, .lsl .r3 .r3 3, .add .r3 .r31 .r3,
    .load .w .r4 .r3 6144, st j1Off .r4, .load .w .r4 .r3 6148, st j2Off .r4]

/-- Data-independent addressing, regenerating the address block when the
index enters a new group of 128. -/
def addressCache : Prog isa :=
  .seq (.block cacheCheck)
    (.seq (.ite (.zero .d .r4) (.block []) (.seq (.block [st counterOff .r3]) addressCalls))
      (.block cacheWord))

def randomSource : Prog isa :=
  .seq (.block addressMode) (.ite (.nonzero .d .r8) dependentWord addressCache)

/-! ## The reference block -/

/-- The reference lane: J₂ mod lanes, or the current lane in the first slice of
the first pass. -/
def refLane : Prog isa :=
  .seq (.block ([ld .r4 j2Off, ldw .r5 lanesArg] ++ Divide.code ++
      [st refLaneOff .r7, ld .r3 passOff, ld .r4 sliceOff, .logic .or .r3 .r3 .r4]))
    (.ite (.zero .d .r3) (.block [ld .r3 laneOff, st refLaneOff .r3]) (.block []))

/-- Where the window starts: 0 in the first pass, else the next slice (0 after
the last one). -/
def refStart : Prog isa :=
  .seq (.block [.li .r3 0, st startOff .r3, ld .r4 passOff])
    (.ite (.zero .d .r4) (.block [])
      (.seq (.block [ld .r4 sliceOff, .subi .r4 .r4 3])
        (.ite (.zero .d .r4) (.block [])
          (.block [ld .r3 sliceOff, .addi .r3 .r3 1, ld .r5 segLenOff, .mul .r3 .r3 .r5,
            st startOff .r3]))))

/-- `r3 :=` the blocks before the current segment that a reference may use:
`slice · segLen` in the first pass, three segments after it. -/
def countBase : Prog isa :=
  .seq (.block [ld .r4 passOff])
    (.ite (.zero .d .r4) (.block [ld .r3 sliceOff, ld .r5 segLenOff, .mul .r3 .r3 .r5])
      (.block [ld .r3 laneLenOff, ld .r5 segLenOff, .sub .r3 .r3 .r5]))

/-- The window's size: `base + index - 1` blocks in the current lane, `base`
(less one at index 0) in another one, chosen by a mask: `nonzero` less one
is all ones for zero. -/
def countSelect : List Instr :=
  [ld .r5 indexOff, .add .r4 .r3 .r5, .subi .r4 .r4 1] ++ nonzero .r6 .r5 .r6 ++
  [.subi .r6 .r6 1, .add .r3 .r3 .r6, ld .r5 refLaneOff, ld .r6 laneOff, .logic .xor .r5 .r5 .r6] ++
  nonzero .r6 .r5 .r6 ++
  [.subi .r5 .r6 1, .logic .xor .r4 .r4 .r3, .logic .and .r4 .r4 .r5, .logic .xor .r3 .r3 .r4,
    st cntOff .r3]

/-- `r3 := count - 1 - ⌊count · ⌊J₁² / 2³²⌋ / 2³²⌋`. -/
def relative : List Instr :=
  [ld .r4 j1Off, .mul .r4 .r4 .r4, .lsr .d .r4 .r4 32, ld .r5 cntOff, .mul .r4 .r5 .r4,
    .lsr .d .r4 .r4 32, .subi .r3 .r5 1, .sub .r3 .r3 .r4]

/-- `r3 := (start + r3) mod laneLen`, by one masked subtraction. -/
def wrap : List Instr :=
  [ld .r4 startOff, .add .r3 .r3 .r4, ld .r4 laneLenOff, .sub .r5 .r3 .r4, .lsr .d .r6 .r5 63,
    .mul .r6 .r6 .r4, .add .r3 .r5 .r6]

/-- The reference block's address, to `[r30 + tmpOff]`. -/
def refPointer : List Instr := [HPrime.mov .r4 .r3, ld .r3 refLaneOff] ++ blockAddr ++ [st tmpOff .r3]

/-- The current block's address, to `[r30 + curOff]`. -/
def curPointer : List Instr := column ++ ld .r3 laneOff :: blockAddr ++ [st curOff .r3]

def reference : Prog isa :=
  .seq refLane (.seq refStart (.seq countBase
    (.block (countSelect ++ relative ++ wrap ++ refPointer ++ curPointer))))

/-! ## The new block -/

/-- G(previous, reference) to `scratch[4096, 5120)`. -/
def fillCompress : Prog isa :=
  .seq prevPointer
    (.seq (.block [ld .r4 tmpOff, .addi .r5 .r31 4096, HPrime.mov .r6 .r31]) compressCall)

/-- Doubleword `k` from `r4` to `r6`, XORed into the old one if `xorOld`. -/
def writeWord (xorOld : Bool) (k : Nat) : List Instr :=
  .load .d .r3 .r4 (8 * k) ::
    ((if xorOld then [.load .d .r5 .r6 (8 * k), .logic .xor .r3 .r3 .r5] else []) ++
      ([.store .d .r3 .r6 (8 * k)] : List Instr))

def writeBlock (xorOld : Bool) : List Instr := (List.range 128).flatMap (writeWord xorOld)

/-- The new block to the current one: copied in the first pass, XORed later. -/
def fillWrite : Prog isa :=
  .seq (.block [.addi .r4 .r31 4096, ld .r6 curOff, ld .r3 passOff])
    (.ite (.zero .d .r3) (.block (writeBlock false)) (.block (writeBlock true)))

def fillBlock : Prog isa := .seq randomSource (.seq reference (.seq fillCompress fillWrite))

/-! ## The loops -/

/-- `[r30 + d] += 1`, and `r4 :=` its difference with the bound `o`, which
`load` reads into `r4`. -/
def advanceBy (d : Nat) (load : Instr) : List Instr :=
  [ld .r3 d, .addi .r3 .r3 1, st d .r3, load, .sub .r4 .r3 .r4]

/-- `[r30 + d] += 1`, and `r4 :=` its difference with `v`. -/
def advanceImm (d v : Nat) : List Instr :=
  [ld .r3 d, .addi .r3 .r3 1, st d .r3, .subi .r4 .r3 v]

/-- `[r30 + d] := v` -/
def setLocal (d v : Nat) : List Instr := [.li .r3 v, st d .r3]

/-- The first index of a segment: 2 in the first slice of the first pass
(whose first two blocks are initialized), else 0; and a new address block. -/
def segmentStart : Prog isa :=
  .seq (.block (setLocal counterOff 0 ++ [ld .r3 passOff, ld .r4 sliceOff, .logic .or .r3 .r3 .r4]))
    (.ite (.zero .d .r3) (.block (setLocal indexOff 2)) (.block (setLocal indexOff 0)))

def segment : Prog isa :=
  .seq segmentStart
    (.seq (.block [ld .r3 indexOff, ld .r4 segLenOff, .sub .r4 .r3 .r4])
      (.ite (.zero .d .r4) (.block [])
        (.loop (.seq fillBlock (.block (advanceBy indexOff (ld .r4 segLenOff)))) (.nonzero .d .r4))))

def lanesLoop : Prog isa :=
  .seq (.block (setLocal laneOff 0))
    (.loop (.seq segment (.block (advanceBy laneOff (ldw .r4 lanesArg)))) (.nonzero .d .r4))

def slicesLoop : Prog isa :=
  .seq (.block (setLocal sliceOff 0))
    (.loop (.seq lanesLoop (.block (advanceImm sliceOff 4))) (.nonzero .d .r4))

def passesLoop : Prog isa :=
  .seq (.block (setLocal passOff 0))
    (.loop (.seq slicesLoop (.block (advanceBy passOff (ldw .r4 iterationsArg)))) (.nonzero .d .r4))

end VG.Impl.Argon2.PPC64LE.Derive
