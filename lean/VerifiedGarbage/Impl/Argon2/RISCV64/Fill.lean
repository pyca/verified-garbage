module

public import VerifiedGarbage.Impl.Argon2.RISCV64.Compress
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Impl.Argon2.RISCV64.Initial

/-!
# Argon2 on RISC-V: filling the memory

The PPC64LE code (`Impl/Argon2/PPC64LE/Fill.lean`) with its registers renamed
and the scratch rearranged, since offsets are below 2048: they are from `s4`,
the rounded `scratch`, and `s0 = scratch + 2048`. The pass, lane, slice and
index are in the frame (`s3`), so every register but `s0`, `s3`, `s4` and
the saved `s1`, `s2` is free within a block's update (`fillBlock`):

* the random word (J₁, J₂) is read from the previous block (data-dependent
  addressing) or from the cached address block in `scratch[2048, 3072)`,
  which two calls of `vg_argon2_compress` regenerate every 128 blocks of a
  segment (`scratch[0, 1024)` is G's output, `[1024, 2048)` the input block,
  `[3072, 4096)` the zero block and `[4096, 6184)` G's working space);
* the reference lane is J₂ modulo the lane count (the fixed-time division), but
  the current lane in the first slice of the first pass;
* the reference column maps J₁ into the window of eligible blocks
  (RFC 9106 §3.4.2), with the high halves of 64-bit products, choosing
  between the windows of the current lane and of another one with a mask
  rather than a branch;
* G of the previous and reference blocks goes to `scratch[0, 1024)`, and is
  copied to the current block (first pass) or XORed into it.

Branches and addresses depend only on the public parameters and loop
position, but for the addresses of the previous block's first word (public:
its position is) and of the reference block, which data-dependent addressing
permits to leak.
-/

@[expose] public section

namespace VG.Impl.Argon2.RISCV64.Derive

open VG.RISCV64

/-! ## Block addresses -/

/-- `a0 := memory + 1024 · (a0 · laneLen + a1)`: block `a1` of lane `a0`. -/
def blockAddr : List Instr :=
  [ld .a2 laneLenOff, .mul .a0 .a0 .a2, .add .a0 .a0 .a1, .shift .sll .d .a0 .a0 10, lda .a2 memoryArg,
    .add .a0 .a2 .a0]

/-- `a1 :=` the current column, `slice · segLen + index`. -/
def column : List Instr :=
  [ld .a0 sliceOff, ld .a2 segLenOff, .mul .a0 .a0 .a2, ld .a2 indexOff, .add .a1 .a0 .a2]

/-- `a1 :=` the column before `a1`, cyclically. -/
def prevColumn : Prog isa :=
  .seq (.ite (.zero .a1) (.block [ld .a1 laneLenOff]) (.block [])) (.block [.addi .a1 .a1 (-1)])

/-- `a0 :=` the address of the previous block. -/
def prevPointer : Prog isa :=
  .seq (.block column) (.seq prevColumn (.block (ld .a0 laneOff :: blockAddr)))

/-! ## The random word -/

/-- `d := 1` if `n ≠ 0`, else 0 (`((0 - n) | n) >> 63`, for `n < 2⁶³`), with
`t` a temporary. -/
def nonzero (d n t : Reg) : List Instr :=
  [.li t 0, .sub t t n, .logic .or t t n, .shift .srl .d d t 63]

/-- `a5` is 1 for data-dependent addressing: neither Argon2i nor Argon2id in
the first two slices of the first pass. `a1` is zero for Argon2i, `a2` for
Argon2id in those slices. -/
def addressMode : List Instr :=
  [ldw .a0 kindArg, .li .a1 1, .logic .xor .a1 .a0 .a1, .li .a2 2, .logic .xor .a2 .a0 .a2,
    ld .a3 passOff, .logic .or .a2 .a2 .a3, ld .a3 sliceOff, .shift .srl .d .a3 .a3 1,
    .logic .or .a2 .a2 .a3] ++ nonzero .a5 .a1 .a4 ++ nonzero .a3 .a2 .a4 ++
    ([.logic .and .a5 .a5 .a3] : List Instr)

/-- Data-dependent addressing: J₁, J₂ are the first doubleword of the
previous block. -/
def dependentWord : Prog isa :=
  .seq prevPointer
    (.block [.load .w .a1 .a0 0, st j1Off .a1, .load .w .a1 .a0 4, st j2Off .a1])

/-- Zero `scratch[d, d + 1024)`. -/
def clearAt (b : Reg) (d : Nat) : List Instr :=
  .li .a0 0 :: (List.range 128).map fun k => .store .d .a0 b (d + 8 * k)

/-- The doublewords of the address-generation input block (its other
doublewords are zero): pass, lane, slice, blocks, passes, type and counter
(§3.4.1.2). -/
def addressHeader : List Instr :=
  [ld .a0 passOff, .store .d .a0 .s4 1024, ld .a0 laneOff, .store .d .a0 .s4 1032,
    ld .a0 sliceOff, .store .d .a0 .s4 1040, lda .a0 blocksArg, .store .d .a0 .s4 1048,
    ldw .a0 iterationsArg, .store .d .a0 .s4 1056, ldw .a0 kindArg, .store .d .a0 .s4 1064,
    ld .a0 counterOff, .store .d .a0 .s4 1072]

def compressName : String := "vg_argon2_compress"

/-- `a3 :=` G's working space, `scratch + 4096`. -/
def gScratch : List Instr := [.addi .a3 .s0 1024, .addi .a3 .a3 1024]

/-- `compress(a0, a1, a2, a3)`. -/
def compressCall : Prog isa := .call compressName Impl.Argon2.RISCV64.compress

/-- G(`x`, `y`) to `out`, each a register and an offset. -/
def stage (x : Reg × Nat) (y : Reg × Nat) (out : Reg × Nat) : Prog isa :=
  .seq (.block ([.addi .a0 x.1 x.2, .addi .a1 y.1 y.2, .addi .a2 out.1 out.2] ++ gScratch))
    compressCall

/-- The address block: G(0, G(0, input)). -/
def addressCalls : Prog isa :=
  .seq (.block (clearAt .s4 1024 ++ clearAt .s0 1024 ++ addressHeader))
    (.seq (stage (.s0, 1024) (.s4, 1024) (.s4, 0)) (stage (.s0, 1024) (.s4, 0) (.s0, 0)))

/-- `a0 :=` the counter of the address block for the index; `a1` is zero if
it is the cached one. -/
def cacheCheck : List Instr :=
  [ld .a0 indexOff, .shift .srl .d .a0 .a0 7, .addi .a0 .a0 1, ld .a1 counterOff, .sub .a1 .a0 .a1]

/-- J₁, J₂: doubleword `index mod 128` of the address block. -/
def cacheWord : List Instr :=
  [ld .a0 indexOff, .li .a1 127, .logic .and .a0 .a0 .a1, .shift .sll .d .a0 .a0 3, .add .a0 .s0 .a0,
    .load .w .a1 .a0 0, st j1Off .a1, .load .w .a1 .a0 4, st j2Off .a1]

/-- Data-independent addressing, regenerating the address block when the
index enters a new group of 128. -/
def addressCache : Prog isa :=
  .seq (.block cacheCheck)
    (.seq (.ite (.zero .a1) (.block []) (.seq (.block [st counterOff .a0]) addressCalls))
      (.block cacheWord))

def randomSource : Prog isa :=
  .seq (.block addressMode) (.ite (.nonzero .a5) dependentWord addressCache)

/-! ## The reference block -/

/-- The reference lane: J₂ mod lanes, or the current lane in the first slice of
the first pass. -/
def refLane : Prog isa :=
  .seq (.block ([ld .a1 j2Off, ldw .a2 lanesArg] ++ Divide.code ++
      [st refLaneOff .a4, ld .a0 passOff, ld .a1 sliceOff, .logic .or .a0 .a0 .a1]))
    (.ite (.zero .a0) (.block [ld .a0 laneOff, st refLaneOff .a0]) (.block []))

/-- Where the window starts: 0 in the first pass, else the next slice (0 after
the last one). -/
def refStart : Prog isa :=
  .seq (.block [.li .a0 0, st startOff .a0, ld .a1 passOff])
    (.ite (.zero .a1) (.block [])
      (.seq (.block [ld .a1 sliceOff, .addi .a1 .a1 (-3)])
        (.ite (.zero .a1) (.block [])
          (.block [ld .a0 sliceOff, .addi .a0 .a0 1, ld .a2 segLenOff, .mul .a0 .a0 .a2,
            st startOff .a0]))))

/-- `a0 :=` the blocks before the current segment that a reference may use:
`slice · segLen` in the first pass, three segments after it. -/
def countBase : Prog isa :=
  .seq (.block [ld .a1 passOff])
    (.ite (.zero .a1) (.block [ld .a0 sliceOff, ld .a2 segLenOff, .mul .a0 .a0 .a2])
      (.block [ld .a0 laneLenOff, ld .a2 segLenOff, .sub .a0 .a0 .a2]))

/-- The window's size: `base + index - 1` blocks in the current lane, `base`
(less one at index 0) in another one, chosen by a mask: `nonzero` less one
is all ones for zero. -/
def countSelect : List Instr :=
  [ld .a2 indexOff, .add .a1 .a0 .a2, .addi .a1 .a1 (-1)] ++ nonzero .a3 .a2 .a3 ++
  [.addi .a3 .a3 (-1), .add .a0 .a0 .a3, ld .a2 refLaneOff, ld .a3 laneOff, .logic .xor .a2 .a2 .a3] ++
  nonzero .a3 .a2 .a3 ++
  [.addi .a2 .a3 (-1), .logic .xor .a1 .a1 .a0, .logic .and .a1 .a1 .a2, .logic .xor .a0 .a0 .a1,
    st cntOff .a0]

/-- `a0 := count - 1 - ⌊count · ⌊J₁² / 2³²⌋ / 2³²⌋`. -/
def relative : List Instr :=
  [ld .a1 j1Off, .mul .a1 .a1 .a1, .shift .srl .d .a1 .a1 32, ld .a2 cntOff, .mul .a1 .a2 .a1,
    .shift .srl .d .a1 .a1 32, .addi .a0 .a2 (-1), .sub .a0 .a0 .a1]

/-- `a0 := (start + a0) mod laneLen`, by one masked subtraction. -/
def wrap : List Instr :=
  [ld .a1 startOff, .add .a0 .a0 .a1, ld .a1 laneLenOff, .sub .a2 .a0 .a1, .shift .srl .d .a3 .a2 63,
    .mul .a3 .a3 .a1, .add .a0 .a2 .a3]

/-- The reference block's address, to `[s3 + tmpOff]`. -/
def refPointer : List Instr := [HPrime.mov .a1 .a0, ld .a0 refLaneOff] ++ blockAddr ++ [st tmpOff .a0]

/-- The current block's address, to `[s3 + curOff]`. -/
def curPointer : List Instr := column ++ ld .a0 laneOff :: blockAddr ++ [st curOff .a0]

def reference : Prog isa :=
  .seq refLane (.seq refStart (.seq countBase
    (.block (countSelect ++ relative ++ wrap ++ refPointer ++ curPointer))))

/-! ## The new block -/

/-- G(previous, reference) to `scratch[0, 1024)`. -/
def fillCompress : Prog isa :=
  .seq prevPointer
    (.seq (.block ([ld .a1 tmpOff, HPrime.mov .a2 .s4] ++ gScratch)) compressCall)

/-- Doubleword `k` from `a1` to `a3`, XORed into the old one if `xorOld`. -/
def writeWord (xorOld : Bool) (k : Nat) : List Instr :=
  .load .d .a0 .a1 (8 * k) ::
    ((if xorOld then [.load .d .a2 .a3 (8 * k), .logic .xor .a0 .a0 .a2] else []) ++
      ([.store .d .a0 .a3 (8 * k)] : List Instr))

def writeBlock (xorOld : Bool) : List Instr := (List.range 128).flatMap (writeWord xorOld)

/-- The new block to the current one: copied in the first pass, XORed later. -/
def fillWrite : Prog isa :=
  .seq (.block [HPrime.mov .a1 .s4, ld .a3 curOff, ld .a0 passOff])
    (.ite (.zero .a0) (.block (writeBlock false)) (.block (writeBlock true)))

def fillBlock : Prog isa := .seq randomSource (.seq reference (.seq fillCompress fillWrite))

/-! ## The loops -/

/-- `[s3 + d] += 1`, and `a1 :=` its difference with the bound `o`, which
`load` reads into `a1`. -/
def advanceBy (d : Nat) (load : Instr) : List Instr :=
  [ld .a0 d, .addi .a0 .a0 1, st d .a0, load, .sub .a1 .a0 .a1]

/-- `[s3 + d] += 1`, and `a1 :=` its difference with `v`. -/
def advanceImm (d v : Nat) : List Instr :=
  [ld .a0 d, .addi .a0 .a0 1, st d .a0, .addi .a1 .a0 (-(v : Int))]

/-- `[s3 + d] := v` -/
def setLocal (d v : Nat) : List Instr := [.li .a0 v, st d .a0]

/-- The first index of a segment: 2 in the first slice of the first pass
(whose first two blocks are initialized), else 0; and a new address block. -/
def segmentStart : Prog isa :=
  .seq (.block (setLocal counterOff 0 ++ [ld .a0 passOff, ld .a1 sliceOff, .logic .or .a0 .a0 .a1]))
    (.ite (.zero .a0) (.block (setLocal indexOff 2)) (.block (setLocal indexOff 0)))

def segment : Prog isa :=
  .seq segmentStart
    (.seq (.block [ld .a0 indexOff, ld .a1 segLenOff, .sub .a1 .a0 .a1])
      (.ite (.zero .a1) (.block [])
        (.loop (.seq fillBlock (.block (advanceBy indexOff (ld .a1 segLenOff)))) (.nonzero .a1))))

def lanesLoop : Prog isa :=
  .seq (.block (setLocal laneOff 0))
    (.loop (.seq segment (.block (advanceBy laneOff (ldw .a1 lanesArg)))) (.nonzero .a1))

def slicesLoop : Prog isa :=
  .seq (.block (setLocal sliceOff 0))
    (.loop (.seq lanesLoop (.block (advanceImm sliceOff 4))) (.nonzero .a1))

def passesLoop : Prog isa :=
  .seq (.block (setLocal passOff 0))
    (.loop (.seq slicesLoop (.block (advanceBy passOff (ldw .a1 iterationsArg)))) (.nonzero .a1))

end VG.Impl.Argon2.RISCV64.Derive
