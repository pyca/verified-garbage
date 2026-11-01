module

public import VerifiedGarbage.Impl.Sm4.AArch64.Ecb
public import VerifiedGarbage.Impl.Sm4.Planes
public import VerifiedGarbage.Spec.Sm4.Contract

/-!
# SM4's round keys prepared once, and batches under them, on AArch64

`vg_sm4_prepare_keys` and `vg_sm4_crypt_prepared`
(`Proof/Sm4/Prepared.lean`): ECB's two halves (`Ecb.lean`) as functions of
the working space, for the modes, which call them (`Ctr.lean`).

* `prepareKeys(schedule = x0, decrypt = x1, ws = x2, ws_len = x3)` saves
  the callee-saved registers in their slots (384–393), sets the masks of
  the round keys' planes, builds the table of bitsliced round keys in the
  order `decrypt` selects (public) and restores the registers.
* `cryptPrepared(ws = x0, ws_len = x1)` saves the registers the same way and
  transforms the sixteen blocks of the tail buffer (`crypt16`) under the
  table and the masks.

The working space is ECB's 396 slots (`slots`). The table and the masks
are what `vg_sm4_crypt_prepared` reads of the preparation (`layout`): each
plane of a round key is a 64-bit word whose bit `16 i + b` is bit `j` of the
key's byte `i` (`planeOf`), for every block `b`.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

/-- `vg_sm4_prepare_keys`: the table of the direction `x1` selects. -/
def prepareKeys : Prog isa :=
  .seq (.block ([movR sb .x2] ++ saveRegs ++ setSlots keyMasks))
    (.seq (.ite (.zero .x .x1) (keys .encrypt) (keys .decrypt)) (.block restoreRegs))

/-- `vg_sm4_crypt_prepared`: the sixteen blocks of the tail buffer. -/
def cryptPrepared : Prog isa :=
  .seq (.block ([movR sb .x0] ++ saveRegs ++ slotAddr .x3 tableEnd)) (.seq crypt16 (.block restoreRegs))

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

/-! ## The calls -/

/-- Before a call: the return address, `sb` and the two registers the modes
keep for the core (`x23`, `x24`) to `v28`, `v27`, `v29` and `v30`, which
neither function writes. -/
def keepHead : List Instr :=
  [.vop (.dup .d2 .v28 .x30), .vop (.dup .d2 .v27 sb), .vop (.dup .d2 .v29 .x23), .vop (.dup .d2 .v30 .x24)]

/-- After it: the four registers back. -/
def keepTail : List Instr :=
  [.umov .x sb .v27 0, .umov .x .x30 .v28 0, .umov .x .x23 .v29 0, .umov .x .x24 .v30 0]

/-- The value of `decrypt` for a direction. -/
def dirFlagOf : Dir → Nat
  | .encrypt => 0
  | .decrypt => 1

/-- A call of `vg_sm4_prepare_keys` for the direction `d`, with the schedule
in `x0` and the working space at `sb`, of `slots` words. -/
def prepareCall (d : Dir) : Prog isa :=
  .seq (.block (keepHead ++ [.movz .x .x1 (BitVec.ofNat 16 (dirFlagOf d)) 0, movR .x2 sb,
      .movz .x .x3 (BitVec.ofNat 16 slots) 0]))
    (.seq (.call "vg_sm4_prepare_keys" prepareKeys) (.block keepTail))

/-- A call of `vg_sm4_crypt_prepared` on the working space at `sb`. -/
def cryptCall : Prog isa :=
  .seq (.block (keepHead ++ [movR .x0 sb, .movz .x .x1 (BitVec.ofNat 16 slots) 0]))
    (.seq (.call "vg_sm4_crypt_prepared" cryptPrepared) (.block keepTail))

end VG.Impl.Sm4.AArch64
