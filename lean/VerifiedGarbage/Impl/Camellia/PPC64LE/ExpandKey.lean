module

public import VerifiedGarbage.Impl.Camellia.PPC64LE.Ecb
public import VerifiedGarbage.Impl.Camellia.KeyOrder

/-!
# The Camellia key schedule on PPC64LE

`expandKey(key = r3, key_len = r4, schedule = r5, scratch = r6)`:
`vg_camellia_expand_key` with its working space in the scratch buffer
(`Layers.lean`, moved to `r8`), which the artifact allocates on the stack.
As on AArch64 and x86-64 (`Impl/Camellia/X86_64/ExpandKey.lean`):

* `KA` and `KB` (RFC 3713 §2.2) take three pairs of rounds with the
  constants `Sigma1 … Sigma6` as subkeys (their planes stored as a table
  from immediates), which the bitsliced rounds of ECB run on eight copies
  of the 128-bit value; the XORs between the pairs are on the plain words.
* The words are kept as ECB loads them, little-endian words of the
  big-endian bytes, in the tail buffer's slots: `KL`, `KR`, the running
  value, `KA`, `KB`, two words each.
* The subkeys are then halves of rotations of `KL`, `KR`, `KA` and `KB` as
  128-bit numbers, computed on their byte-swapped words, and stored
  byte-swapped (`ldbrx` and `stdbrx`, indexed by `r12`), in the order of
  `Spec.Camellia.scheduleWords`.

Only `r3` (the key, then the running value's slots), `r4` (the table, then
the round key's entry), `r5`, `r6` (the key's length), `r7` (the pairs
left), `r8`, `r12` and the branches' tests hold public values; no address and no
branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Camellia.PPC64LE

open VG.PPC64LE VG.Impl.Aes.PPC64LE VG.Impl.Camellia

def klSlot : Nat := tailSlot
def krSlot : Nat := tailSlot + 2
def wSlot : Nat := tailSlot + 4
def kaSlot : Nat := tailSlot + 6
def kbSlot : Nat := tailSlot + 8

/-- The planes of the constant `x` to the entry at `kp`, and on to the next. -/
def sigmaOne (x : BitVec 64) : List Instr :=
  (List.range 8).flatMap (fun j => imm64 t0 (keyPlane x j) ++ ([.store .d t0 kp (8 * j)] : List Instr)) ++
  ([.addi kp kp 64] : List Instr)

/-- Load the key: `KL`, and `KR` by the key's length (in `r6`). -/
def loadKey : Prog isa :=
  .seq (.block [.load .d t0 .r3 0, stS klSlot t0, .load .d t0 .r3 8, stS (klSlot + 1) t0,
      .subi t1 .r6 16])
    (.ite (.zero .d t1) (.block [.li t0 0, stS krSlot t0, stS (krSlot + 1) t0])
      (.seq (.block [.load .d t0 .r3 16, stS krSlot t0, .subi t1 .r6 24])
        (.ite (.zero .d t1)
          (.block [.li u7 0, .subi u7 u7 1, xorR t0 t0 u7, stS (krSlot + 1) t0])
          (.block [.load .d t0 .r3 24, stS (krSlot + 1) t0]))))

/-- The word at `[r3 + d]` in all eight lanes, bitsliced. -/
def spread (d : Nat) : List Instr :=
  ([.load .d (q 0) .r3 d] : List Instr) ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++ toBs

/-- `w := w ^ x`, for the two words at slots `w` and `x`. -/
def xorWords (w x : Nat) : List Instr :=
  [ldS t0 x, ldS t1 w, xorR t0 t0 t1, stS w t0, ldS t0 (x + 1), ldS t1 (w + 1), xorR t0 t0 t1,
    stS (w + 1) t0]

/-- Copy the two words at slot `x` to slot `w`. -/
def copyWords (w x : Nat) : List Instr :=
  [ldS t0 x, stS w t0, ldS t0 (x + 1), stS (w + 1) t0]

/-- Two rounds on the running value (at `r3`), with the next two entries of the table. -/
def pairPlain : List Instr :=
  spread 8 ++ storeHalf d2Slot ++ spread 0 ++ storeHalf d1Slot ++
  round 0 d2Slot ++ round 8 d1Slot ++ fromBs ++ [stS wSlot (q 0)] ++
  loadHalf d2Slot ++ fromBs ++ [stS (wSlot + 1) (q 0), .addi kp kp 128]

/-- `KA` and `KB`: the running value starts as `KL ^ KR`; after the first
pair `KL` is XORed in, after the second it is `KA`, and `KA ^ KR` goes on;
after the third it is `KB`. `r7` counts the pairs down from 3. -/
def kaKb : Prog isa :=
  .seq (.block (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++
      ([.li .r7 3, .addi .r3 sb (8 * wSlot)] : List Instr)))
    (.loop (.seq (.block (pairPlain ++ [shrI t1 .r7 1]))
      (.seq (.ite (.nonzero .d t1)
          (.seq (.block [.subi t1 .r7 3])
            (.ite (.zero .d t1) (.block (xorWords wSlot klSlot))
              (.block (copyWords kaSlot wSlot ++ xorWords wSlot krSlot))))
          (.block (copyWords kbSlot wSlot)))
        (.block [.subi .r7 .r7 1]))) (.nonzero .d .r7))

/-- The 128-bit values' registers: high and low words, as numbers. -/
def hiReg (v : Nat) : Reg := q (2 * v)
def loReg (v : Nat) : Reg := q (2 * v + 1)

/-- `KL`, `KR`, `KA`, `KB` (`0 … 3`), byte-swapped into their registers. -/
def loadValues : List Instr :=
  [klSlot, krSlot, kaSlot, kbSlot].zipIdx.flatMap fun (k, v) =>
    [.li .r12 (8 * k), .loadRev .d (hiReg v) sb .r12, .li .r12 (8 * (k + 1)), .loadRev .d (loReg v) sb .r12]

/-- Store word `i` of the schedule: the high (`hi`) or low half of value `v`
rotated left by `r` bits, byte-swapped. -/
def subkey (i v r : Nat) (hi : Bool) : List Instr :=
  let (a, b) := if (r < 64) = hi then (hiReg v, loReg v) else (loReg v, hiReg v)
  let r' := r % 64
  (if r' = 0 then [movR t0 a] else [.lsl t0 a r', .lsr .d t1 b (64 - r'), orR t0 t0 t1]) ++
  ([.li .r12 (8 * i), .storeRev .d t0 .r5 .r12] : List Instr)

def storeSubkeys (ks : List (Nat × Nat × Bool)) : List Instr :=
  ks.zipIdx.flatMap fun ((v, r, hi), i) => subkey i v r hi

def expandKey : Prog isa :=
  .seq (.block ([movR sb .r6, movR .r6 .r4] ++ saveRegs ++ setSlots layerMasks ++ tableSetup ++
      sigmas.flatMap sigmaOne))
    (.seq loadKey
      (.seq (.block tableSetup)
        (.seq kaKb
          (.seq (.block (loadValues ++ ([.subi t0 .r6 16] : List Instr)))
            (.seq (.ite (.zero .d t0) (.block (storeSubkeys subkeys128)) (.block (storeSubkeys subkeys256)))
              (.block restoreRegs))))))

end VG.Impl.Camellia.PPC64LE
