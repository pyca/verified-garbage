module

public import VerifiedGarbage.Impl.Sm4.Arm.Ecb
public import VerifiedGarbage.Impl.Sm4.Planes
public import VerifiedGarbage.Spec.Sm4.Prepared

/-!
# SM4 round keys prepared once, and eight-block batches, on ARMv7

The callable preparation and cipher share ECB's working-space layout.
Preparation writes the bitsliced keys once; each cipher call preserves them.
-/

@[expose] public section

namespace VG.Impl.Sm4.Arm

open VG.Arm VG.Impl.Aes.Arm

/-- Prepare the round keys in the direction selected by `r1`. -/
def prepareKeys : Prog isa :=
  .seq (.block (saveRegs .r2 ++ [movR sb .r2, movR .r12 .r0, movR .r3 .r1]))
    (.seq keysAny (.block ([movR .r12 sb] ++ restoreRegs .r12)))

/-- Transform the eight blocks in the working space, retaining its key table. -/
def cryptPrepared : Prog isa :=
  .seq (.block (saveRegs .r0 ++ [movR sb .r0]))
    (.seq crypt8 (.block ([movR .r12 sb] ++ restoreRegs .r12)))

/-! ## The layout -/

/-- The direction of the specification. -/
def ofSpecDir : Spec.Sm4.Direction → Dir
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- The round key of the table's entry `e`, for the round keys `k` in the
order of the direction. -/
def keyEntry (k : Spec.Sm4.Schedule) : Dir → Nat → Spec.Sm4.Word
  | .encrypt, e => k.getD e 0
  | .decrypt, e => k.getD (31 - e) 0

/-- The word of slot `w` of the table: plane `w % 8` of its entry. -/
def preparedWord (k : Spec.Sm4.Schedule) (d : Dir) (w : Nat) : BitVec 32 :=
  Impl.Sm4.planeOf32 (keyEntry k d ((w - tableSlot) / 8)) ((w - tableSlot) % 8)

/-- The table's slots, as bytes. -/
def layout : Spec.Sm4.Prepared.Layout where
  table := [(4 * tableSlot, 4 * (tableEnd - tableSlot))]
  encode k d i := (preparedWord k (ofSpecDir d) (i / 4)).extractLsb' (8 * (i % 4)) 8
  buf := 4 * tailSlot
  blocks := 8
  prepScratch := [(0, 4 * slots)]
  cryptScratch := [(0, 4 * tableSlot), (4 * savedSlot, 4 * (slots - savedSlot))]
  size := 4 * slots

end VG.Impl.Sm4.Arm
