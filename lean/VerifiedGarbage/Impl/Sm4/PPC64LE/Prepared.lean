module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.Ecb
public import VerifiedGarbage.Impl.Sm4.Planes
public import VerifiedGarbage.Spec.Sm4.Contract

/-!
# SM4's round keys prepared once, and batches under them, on PPC64LE

`vg_sm4_prepare_keys` and `vg_sm4_crypt_prepared`
(`Proof/Sm4/Prepared.lean`): ECB's two halves (`Ecb.lean`) as functions of
the working space, for the modes. As on AArch64
(`Impl/Sm4/AArch64/Prepared.lean`):

* `prepareKeys(schedule = r3, decrypt = r4, ws = r5, ws_len = r6)` saves
  the callee-saved registers in their slots (384–401), sets the masks of
  the round keys' planes, builds the table of bitsliced round keys in the
  order `decrypt` selects (public) and restores the registers.
* `cryptPrepared(ws = r3, ws_len = r4)` saves the registers the same way and
  transforms the sixteen blocks of the tail buffer (`crypt16`) under the
  table and the masks.

The working space is ECB's 402 slots (`slots`). The table and the masks
are what `vg_sm4_crypt_prepared` reads of the preparation (`layout`): each
plane of a round key is a 64-bit word whose bit `16 i + b` is bit `j` of the
key's byte `i` (`planeOf`), for every block `b`.
-/

@[expose] public section

namespace VG.Impl.Sm4.PPC64LE

open VG.PPC64LE VG.Impl.Aes.PPC64LE

/-- `vg_sm4_prepare_keys`: the table of the direction `r4` selects. Each
direction's table is the code a branch skips (its `ite`'s first branch), not
the code a conditional branch jumps over (the second branch, here empty):
the unrolled tables are longer than a conditional branch reaches. -/
def prepareKeys : Prog isa :=
  .seq (.block ([movR sb .r5] ++ saveRegs ++ setSlots keyMasks))
    (.seq (.seq (.ite (.nonzero .d .r4) (keys .decrypt) (.block [])) (.ite (.zero .d .r4) (keys .encrypt) (.block [])))
      (.block restoreRegs))

/-- `vg_sm4_crypt_prepared`: the sixteen blocks of the tail buffer. -/
def cryptPrepared : Prog isa :=
  .seq (.block ([movR sb .r3] ++ saveRegs ++ slotAddr .r11 tableEnd)) (.seq crypt16 (.block restoreRegs))

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

/-- The word of slot `w` of the working space that the preparation writes:
a mask of the round keys' planes, or plane `w % 8` of the table's entry. -/
def preparedWord (k : Spec.Sm4.Schedule) (d : Dir) (w : Nat) : BitVec 64 :=
  if w < tableSlot then (keyMasks.find? (·.1 = w)).elim 0 (·.2)
  else Impl.Sm4.planeOf (keyEntry k d ((w - tableSlot) / 8)) ((w - tableSlot) % 8)

end VG.Impl.Sm4.PPC64LE
