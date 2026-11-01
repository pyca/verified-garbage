module

public import VerifiedGarbage.Impl.Sm4.RISCV64.Ecb
public import VerifiedGarbage.Impl.Sm4.Planes
public import VerifiedGarbage.Spec.Sm4.Contract

/-!
# SM4's round keys prepared once, and batches under them, on RISC-V

`vg_sm4_prepare_keys` and `vg_sm4_crypt_prepared`
(`Proof/Sm4/Prepared.lean`): ECB's two halves (`Ecb.lean`) as functions of
the working space, for the modes, as on PPC64LE
(`Impl/Sm4/PPC64LE/Prepared.lean`):

* `prepareKeys(schedule = a0, decrypt = a1, ws = a2, ws_len = a3)` saves
  the callee-saved registers in their slots (384–395), sets the masks (of
  the round keys' planes and of the transposes), builds the table of bitsliced round keys in the
  order `decrypt` selects (public) and restores the registers.
* `cryptPrepared(ws = a0, ws_len = a1)` saves the registers the same way,
  sets the transposes' masks and transforms the sixteen blocks of the tail
  buffer (`crypt16`) under the table.

The working space is ECB's 396 slots (`slots`). The table and the masks
of the round keys' planes are what the preparation writes for
`vg_sm4_crypt_prepared` (`layout`): each plane of a round key is a 64-bit
word whose bit `16 i + b` is bit `j` of the key's byte `i` (`planeOf`), for
every block `b`.
-/

@[expose] public section

namespace VG.Impl.Sm4.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64

/-- `vg_sm4_prepare_keys`: the table of the direction `a1` selects. -/
def prepareKeys : Prog isa :=
  .seq (.block ([movR sb .a2] ++ saveRegs ++ setSlots (keyMasks ++ bsKs)))
    (.seq (.seq (.ite (.nonzero .a1) (keys .decrypt) (.block [])) (.ite (.zero .a1) (keys .encrypt) (.block [])))
      (.block restoreRegs))

/-- `vg_sm4_crypt_prepared`: the sixteen blocks of the tail buffer. -/
def cryptPrepared : Prog isa :=
  .seq (.block ([movR sb .a0] ++ saveRegs ++ setSlots bsKs ++ slotAddr .a0 tableEnd))
    (.seq crypt16 (.block restoreRegs))

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

end VG.Impl.Sm4.RISCV64
