module

public import VerifiedGarbage.Impl.Camellia.PPC64LE.Ecb
public import VerifiedGarbage.Impl.Camellia.KeyOrder
public import VerifiedGarbage.Spec.Camellia.Prepared

/-!
# Camellia's subkeys prepared once, and batches under them, on PPC64LE

`vg_camellia_prepare_keys` and `vg_camellia_crypt_prepared`
(`Spec/Camellia/Prepared.lean`): ECB's two halves (`Ecb.lean`) as functions
of the working space, for the modes, as on AArch64
(`Impl/Camellia/AArch64/Prepared.lean`).

* `prepareKeys(schedule = r3, rounds = r4, decrypt = r5, ws = r6, ws_len = r7)`
  saves the callee-saved registers in their slots (368–385), sets the
  masks of the layers, builds the table of bitsliced subkeys for 18 or 24
  rounds in the order `decrypt` selects (both public) and restores the
  registers.
* `cryptPrepared(rounds = r3, ws = r4, ws_len = r5)` saves the registers
  the same way, sets `r7` to the address of the postwhitening's entry for
  that many rounds, and transforms the eight blocks of the tail buffer
  (`crypt8`) under the table and the masks.

The working space is ECB's 414 slots (`slots`). The table and the masks are
what `vg_camellia_crypt_prepared` reads of the preparation (`layout`): each
plane of a subkey is a 64-bit word, bit `8 c + b` of plane `j` being bit `j`
of byte `bytePos c` of the subkey (`keyPlane`), for every block `b`.
-/

@[expose] public section

namespace VG.Impl.Camellia.PPC64LE

open VG.PPC64LE VG.Impl.Aes.PPC64LE

/-- `vg_camellia_prepare_keys`: the table of the direction `r5` selects. -/
def prepareKeys : Prog isa :=
  .seq (.block ([movR sb .r6] ++ saveRegs ++ setSlots layerMasks ++ ([.subi t0 .r4 18] : List Instr)))
    (.seq (.ite (.zero .d .r5) (keys .encrypt) (keys .decrypt)) (.block restoreRegs))

/-- `vg_camellia_crypt_prepared`: the eight blocks of the tail buffer. -/
def cryptPrepared : Prog isa :=
  .seq (.block ([movR sb .r4] ++ saveRegs ++ ([.subi t0 .r3 18] : List Instr)))
    (.seq (.ite (.zero .d t0) (.block (endAddr 3)) (.block (endAddr 4))) (.seq crypt8 (.block restoreRegs)))

/-! ## The layout -/

/-- The direction of the specification. -/
def ofSpecDir : Spec.Camellia.Direction → Dir
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- The schedule's word in the table's entry `e`, for `g` groups of six
rounds and the words `w` in the order encryption uses them: the stored
order for encryption; for decryption `kw3, kw4`, the words between `kw2`
and `kw3` from the last back to the first, then `kw1, kw2` (as `keys`). -/
def keyEntry (w : List (BitVec 64)) (g : Nat) : Dir → Nat → BitVec 64
  | .encrypt, e => w.getD e 0
  | .decrypt, e => w.getD (if e < 2 then 8 * g + e else if e < 8 * g then 8 * g + 1 - e else e - 8 * g) 0

/-- The word of slot `k` of the working space that the preparation writes
for `rounds` rounds: a mask of the layers, or plane `(k - keySlot) % 8` of
the table's entry. -/
def preparedWord (rounds : Nat) (w : List (BitVec 64)) (d : Dir) (k : Nat) : BitVec 64 :=
  if k < keySlot then (layerMasks.find? (·.1 = k)).elim 0 (·.2)
  else keyPlane (keyEntry w (rounds / 6) d ((k - keySlot) / 8)) ((k - keySlot) % 8)

/-- The masks' slots and the table's, as byte ranges. -/
def layout : Spec.Camellia.Prepared.Layout where
  table rounds := [(8 * evenSlot, 40), (8 * keySlot, 64 * (8 * (rounds / 6) + 2))]
  encode rounds w d i := (preparedWord rounds w (ofSpecDir d) (i / 8)).extractLsb' (8 * (i % 8)) 8
  buf := 8 * tailSlot
  blocks := 8
  prepScratch := [(0, 8 * slots)]
  cryptScratch := [(0, 8 * evenSlot), (8 * (m3Slot + 1), 8 * (keySlot - m3Slot - 1)),
    (8 * savedSlot, 8 * (tailSlot + 16 - savedSlot))]
  size := 8 * slots

end VG.Impl.Camellia.PPC64LE
