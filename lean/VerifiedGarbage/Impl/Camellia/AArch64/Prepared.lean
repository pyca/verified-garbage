module

public import VerifiedGarbage.Impl.Camellia.AArch64.Ecb
public import VerifiedGarbage.Impl.Camellia.KeyOrder
public import VerifiedGarbage.Spec.Camellia.Prepared

/-!
# Camellia's subkeys prepared once, and batches under them, on AArch64

`vg_camellia_prepare_keys` and `vg_camellia_crypt_prepared`
(`Spec/Camellia/Prepared.lean`): ECB's two halves (`Ecb.lean`) as functions
of the working space, for the modes, which call them (`Ctr.lean`).

* `prepareKeys(schedule = x0, rounds = x1, decrypt = x2, ws = x3, ws_len = x4)`
  saves the callee-saved registers in their slots (368–377), sets the
  masks of the layers, builds the table of bitsliced subkeys for 18 or 24
  rounds in the order `decrypt` selects (both public) and restores the
  registers.
* `cryptPrepared(rounds = x0, ws = x1, ws_len = x2)` saves the registers
  the same way, sets `x4` to the address of the postwhitening's entry for
  that many rounds, and transforms the eight blocks of the tail buffer
  (`crypt8`) under the table and the masks.

The working space is ECB's 406 slots (`slots`). The table and the masks are
what `vg_camellia_crypt_prepared` reads of the preparation (`layout`): each
plane of a subkey is a 64-bit word, bit `8 c + b` of plane `j` being bit `j`
of byte `bytePos c` of the subkey (`keyPlane`), for every block `b`.
-/

@[expose] public section

namespace VG.Impl.Camellia.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

/-- `vg_camellia_prepare_keys`: the table of the direction `x2` selects. -/
def prepareKeys : Prog isa :=
  .seq (.block ([movR sb .x3] ++ saveRegs ++ setSlots layerMasks ++ ([.subImm .x t0 .x1 18] : List Instr)))
    (.seq (.ite (.zero .x .x2) (keys .encrypt) (keys .decrypt)) (.block restoreRegs))

/-- `vg_camellia_crypt_prepared`: the eight blocks of the tail buffer. -/
def cryptPrepared : Prog isa :=
  .seq (.block ([movR sb .x1] ++ saveRegs ++ ([.subImm .x t0 .x0 18] : List Instr)))
    (.seq (.ite (.zero .x t0) (.block (endAddr 3)) (.block (endAddr 4))) (.seq crypt8 (.block restoreRegs)))

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

/-! ## The calls -/

/-- Before a call: the return address, `sb`, the two registers the modes
keep for the core (`x23`, `x24`) and the number of rounds (in `r`) to
`v28`, `v27`, `v29`, `v30` and `v26`, which neither function writes. -/
def keepHeadWith (r : Reg) : List Instr :=
  [.vop (.dup .d2 .v28 .x30), .vop (.dup .d2 .v27 sb), .vop (.dup .d2 .v29 .x23), .vop (.dup .d2 .v30 .x24),
   .vop (.dup .d2 .v26 r)]

/-- `keepHeadWith`, with the number of rounds in `x4`, where the core keeps
it. -/
def keepHead : List Instr := keepHeadWith .x4

/-- After it: the five registers back, the number of rounds to `x4`. -/
def keepTail : List Instr :=
  [.umov .x sb .v27 0, .umov .x .x30 .v28 0, .umov .x .x23 .v29 0, .umov .x .x24 .v30 0, .umov .x .x4 .v26 0]

/-- The value of `decrypt` for a direction. -/
def dirFlagOf : Dir → Nat
  | .encrypt => 0
  | .decrypt => 1

/-- A call of `vg_camellia_prepare_keys` for the direction `d`, with the
schedule in `x0`, the number of rounds in `x1` (and in `x4` after it) and
the working space at `sb`, of `slots` words. -/
def prepareCall (d : Dir) : Prog isa :=
  .seq (.block (keepHeadWith .x1 ++ [.movz .x .x2 (BitVec.ofNat 16 (dirFlagOf d)) 0, movR .x3 sb,
      .movz .x .x4 (BitVec.ofNat 16 slots) 0]))
    (.seq (.call (Spec.Camellia.Prepared.prepareApi layout).name prepareKeys) (.block keepTail))

/-- A call of `vg_camellia_crypt_prepared` on the working space at `sb`, for
the number of rounds in `x4`. -/
def cryptCall : Prog isa :=
  .seq (.block (keepHead ++ [movR .x0 .x4, movR .x1 sb, .movz .x .x2 (BitVec.ofNat 16 slots) 0]))
    (.seq (.call (Spec.Camellia.Prepared.cryptApi layout).name cryptPrepared) (.block keepTail))

end VG.Impl.Camellia.AArch64
