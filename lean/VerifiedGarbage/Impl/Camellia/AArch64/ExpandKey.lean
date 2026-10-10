import VerifiedGarbage.Impl.Camellia.AArch64.Ecb
import VerifiedGarbage.Impl.Camellia.KeyOrder

/-!
# The Camellia key schedule on AArch64

`expandKey(key = x0, key_len = x1, schedule = x2, scratch = x3)`:
`vg_camellia_expand_key` with its working space in the scratch buffer
(`Layers.lean`, moved to `x5`), which the artifact allocates on the stack.
As on x86-64 (`Impl/Camellia/X86_64/ExpandKey.lean`):

* `KA` and `KB` (RFC 3713 §2.2) take three pairs of rounds with the
  constants `Sigma1 … Sigma6` as subkeys (their planes stored as a table
  from immediates), which the bitsliced rounds of ECB run on eight copies
  of the 128-bit value; the XORs between the pairs are on the plain words.
* The words are kept as ECB loads them, little-endian words of the
  big-endian bytes, in the tail buffer's slots: `KL`, `KR`, the running
  value, `KA`, `KB`, two words each.
* The subkeys are then halves of rotations of `KL`, `KR`, `KA` and `KB` as
  128-bit numbers, computed on their byte-swapped words, and stored
  byte-swapped, in the order of `Spec.Camellia.scheduleWords`.

Only `x0` (the key, then the running value's slots), `x1` (the table, then
the round key's entry), `x2`, `x3` (the key's length), `x4` (the pairs
left), `x5` and the branches' tests hold public values; no address and no
branch depends on anything else.
-/

namespace VG.Impl.Camellia.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64 VG.Impl.Camellia

def klSlot : Nat := tailSlot
def krSlot : Nat := tailSlot + 2
def wSlot : Nat := tailSlot + 4
def kaSlot : Nat := tailSlot + 6
def kbSlot : Nat := tailSlot + 8

/-- The planes of the constant `x` to the entry at `kp`, and on to the next. -/
def sigmaOne (x : BitVec 64) : List Instr :=
  (List.range 8).flatMap (fun j => imm t0 (keyPlane x j) ++ ([.str .x t0 kp (8 * j)] : List Instr)) ++
  ([.addImm .x kp kp 64] : List Instr)

/-- Load the key: `KL`, and `KR` by the key's length (in `x3`). -/
def loadKey : Prog isa :=
  .seq (.block [.ldr .x t0 .x0 0, stS klSlot t0, .ldr .x t0 .x0 8, stS (klSlot + 1) t0,
      .subImm .x t1 .x3 16])
    (.ite (.zero .x t1) (.block [.movz .x t0 0 0, stS krSlot t0, stS (krSlot + 1) t0])
      (.seq (.block [.ldr .x t0 .x0 16, stS krSlot t0, .subImm .x t1 .x3 24])
        (.ite (.zero .x t1)
          (.block [.movz .x u7 0 0, .subImm .x u7 u7 1, eorR t0 t0 u7, stS (krSlot + 1) t0])
          (.block [.ldr .x t0 .x0 24, stS (krSlot + 1) t0]))))

/-- The word at `[x0 + d]` in all eight lanes, bitsliced. -/
def spread (d : Nat) : List Instr :=
  ([.ldr .x (q 0) .x0 d] : List Instr) ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++ toBs

/-- `w := w ^ x`, for the two words at slots `w` and `x`. -/
def xorWords (w x : Nat) : List Instr :=
  [ldS t0 x, ldS t1 w, eorR t0 t0 t1, stS w t0, ldS t0 (x + 1), ldS t1 (w + 1), eorR t0 t0 t1,
    stS (w + 1) t0]

/-- Copy the two words at slot `x` to slot `w`. -/
def copyWords (w x : Nat) : List Instr :=
  [ldS t0 x, stS w t0, ldS t0 (x + 1), stS (w + 1) t0]

/-- Two rounds on the running value (at `x0`), with the next two entries of the table. -/
def pairPlain : List Instr :=
  spread 8 ++ storeHalf d2Slot ++ spread 0 ++ storeHalf d1Slot ++
  round 0 d2Slot ++ round 8 d1Slot ++ fromBs ++ [stS wSlot (q 0)] ++
  loadHalf d2Slot ++ fromBs ++ [stS (wSlot + 1) (q 0), .addImm .x kp kp 128]

/-- `KA` and `KB`: the running value starts as `KL ^ KR`; after the first
pair `KL` is XORed in, after the second it is `KA`, and `KA ^ KR` goes on;
after the third it is `KB`. `x4` counts the pairs down from 3. -/
def kaKb : Prog isa :=
  .seq (.block (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++
      ([.movz .x .x4 3 0, movR .x0 sb, .addImm .x .x0 .x0 (8 * wSlot)] : List Instr)))
    (.loop (.seq (.block (pairPlain ++ [lsrI t1 .x4 1]))
      (.seq (.ite (.nonzero .x t1)
          (.seq (.block [.subImm .x t1 .x4 3])
            (.ite (.zero .x t1) (.block (xorWords wSlot klSlot))
              (.block (copyWords kaSlot wSlot ++ xorWords wSlot krSlot))))
          (.block (copyWords kbSlot wSlot)))
        (.block [.subImm .x .x4 .x4 1]))) (.nonzero .x .x4))

/-- The 128-bit values' registers: high and low words, as numbers. -/
def hiReg : Nat → Reg | 0 => .x6 | 1 => .x8 | 2 => .x10 | _ => .x12
def loReg : Nat → Reg | 0 => .x7 | 1 => .x9 | 2 => .x11 | _ => .x13

/-- `KL`, `KR`, `KA`, `KB` (`0 … 3`), byte-swapped into their registers. -/
def loadValues : List Instr :=
  [klSlot, krSlot, kaSlot, kbSlot].zipIdx.flatMap fun (k, v) =>
    [ldS (hiReg v) k, .rev (hiReg v) (hiReg v), ldS (loReg v) (k + 1), .rev (loReg v) (loReg v)]

/-- Store word `i` of the schedule: the high (`hi`) or low half of value `v`
rotated left by `r` bits, byte-swapped. -/
def subkey (i v r : Nat) (hi : Bool) : List Instr :=
  let (a, b) := if (r < 64) = hi then (hiReg v, loReg v) else (loReg v, hiReg v)
  let r' := r % 64
  (if r' = 0 then [movR t0 a] else [.lsl .x t0 a r', .lsr .x t1 b (64 - r'), orrR t0 t0 t1]) ++
  ([.rev t0 t0, .str .x t0 .x2 (8 * i)] : List Instr)

def storeSubkeys (ks : List (Nat × Nat × Bool)) : List Instr :=
  ks.zipIdx.flatMap fun ((v, r, hi), i) => subkey i v r hi

def expandKey : Prog isa :=
  .seq (.block ([movR sb .x3, movR .x3 .x1] ++ saveRegs ++ setSlots layerMasks ++ tableSetup ++
      sigmas.flatMap sigmaOne))
    (.seq loadKey
      (.seq (.block tableSetup)
        (.seq kaKb
          (.seq (.block (loadValues ++ ([.subImm .x t0 .x3 16] : List Instr)))
            (.seq (.ite (.zero .x t0) (.block (storeSubkeys subkeys128)) (.block (storeSubkeys subkeys256)))
              (.block restoreRegs))))))

end VG.Impl.Camellia.AArch64
