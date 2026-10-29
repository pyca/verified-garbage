module

public import VerifiedGarbage.Impl.Camellia.RISCV64.Ecb
public import VerifiedGarbage.Impl.Camellia.KeyOrder
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# The Camellia key schedule on RISC-V

`expandKey(key = a0, key_len = a1, schedule = a2, scratch = a3)`:
`vg_camellia_expand_key` with its working space in the scratch buffer
(`Layers.lean`, moved to `a5`), which the artifact allocates on the stack.
As on PPC64LE (`Impl/Camellia/PPC64LE/ExpandKey.lean`):
* `KA` and `KB` (RFC 3713 §2.2) take three pairs of rounds with the
  constants `Sigma1 … Sigma6` as subkeys (their planes stored as a table
  from immediates), which the bitsliced rounds of ECB run on eight copies
  of the 128-bit value; the XORs between the pairs are on the plain words.
* The words are kept as ECB loads them, little-endian words of the
  big-endian bytes, in the tail buffer's slots: `KL`, `KR`, the running
  value, `KA`, `KB`, two words each. The key's bytes are copied there one
  at a time, as the contract states no alignment for it.
* The subkeys are then halves of rotations of `KL`, `KR`, `KA` and `KB` as
  128-bit numbers, computed on their words read big-endian (`loadBE64`), and
  stored big-endian a byte at a time (`storeBE`), in the order of
  `Spec.Camellia.scheduleWords`.

Only `a0` (the key, then the running value's slots), `a1` (the table, then
the round key's entry), `a2`, `a3` (the key's length), `a4` (the pairs
left), `a5` and the branches' tests hold public values; no address and no
branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Camellia.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64 VG.Impl.Camellia VG.Impl.Words.RISCV64

def klSlot : Nat := tailSlot
def krSlot : Nat := tailSlot + 2
def wSlot : Nat := tailSlot + 4
def kaSlot : Nat := tailSlot + 6
def kbSlot : Nat := tailSlot + 8

/-- The planes of the constant `x` to the entry at `kp`, and on to the next. -/
def sigmaOne (x : BitVec 64) : List Instr :=
  (List.range 8).flatMap (fun j =>
    Words64.RISCV64.movImm64 t0 t1 (keyPlane x j) ++ ([.store .d t0 kp (8 * j)] : List Instr)) ++
  ([.addi kp kp 64] : List Instr)

/-- Load the key: `KL`, and `KR` by the key's length (in `a3`). -/
def loadKey : Prog isa :=
  .seq (.block (copyBytes t0 .a0 sb 0 (8 * klSlot) 16 ++ ([.addi t1 .a3 (-16)] : List Instr)))
    (.ite (.zero t1) (.block [.li t0 0, stS krSlot t0, stS (krSlot + 1) t0])
      (.seq (.block (copyBytes t0 .a0 sb 16 (8 * krSlot) 8 ++ ([.addi t1 .a3 (-24)] : List Instr)))
        (.ite (.zero t1)
          (.block [ldS t0 krSlot, notR t0, stS (krSlot + 1) t0])
          (.block (copyBytes t0 .a0 sb 24 (8 * (krSlot + 1)) 8)))))

/-- The word at `[a0 + d]` in all eight lanes, bitsliced. -/
def spread (d : Nat) : List Instr :=
  ([.load .d (q 0) .a0 d] : List Instr) ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++ toBs

/-- `w := w ^ x`, for the two words at slots `w` and `x`. -/
def xorWords (w x : Nat) : List Instr :=
  [ldS t0 x, ldS t1 w, xorR t0 t0 t1, stS w t0, ldS t0 (x + 1), ldS t1 (w + 1), xorR t0 t0 t1,
    stS (w + 1) t0]

/-- Copy the two words at slot `x` to slot `w`. -/
def copyWords (w x : Nat) : List Instr :=
  [ldS t0 x, stS w t0, ldS t0 (x + 1), stS (w + 1) t0]

/-- Two rounds on the running value (at `a0`), with the next two entries of the table. -/
def pairPlain : List Instr :=
  spread 8 ++ storeHalf d2Slot ++ spread 0 ++ storeHalf d1Slot ++
  round 0 d2Slot ++ round 8 d1Slot ++ fromBs ++ [stS wSlot (q 0)] ++
  loadHalf d2Slot ++ fromBs ++ [stS (wSlot + 1) (q 0), .addi kp kp 128]

/-- `KA` and `KB`: the running value starts as `KL ^ KR`; after the first
pair `KL` is XORed in, after the second it is `KA`, and `KA ^ KR` goes on;
after the third it is `KB`. `a4` counts the pairs down from 3. -/
def kaKb : Prog isa :=
  .seq (.block (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++
      ([.li .a4 3, .addi .a0 sb ((8 * wSlot : Nat) : Int)] : List Instr)))
    (.loop (.seq (.block (pairPlain ++ [shrI t1 .a4 1]))
      (.seq (.ite (.nonzero t1)
          (.seq (.block [.addi t1 .a4 (-3)])
            (.ite (.zero t1) (.block (xorWords wSlot klSlot))
              (.block (copyWords kaSlot wSlot ++ xorWords wSlot krSlot))))
          (.block (copyWords kbSlot wSlot)))
        (.block [.addi .a4 .a4 (-1)]))) (.nonzero .a4))

/-- The 128-bit values' registers: high and low words, as numbers. -/
def hiReg (v : Nat) : Reg := q (2 * v)
def loReg (v : Nat) : Reg := q (2 * v + 1)

/-- `KL`, `KR`, `KA`, `KB` (`0 … 3`), read big-endian into their registers. -/
def loadValues : List Instr :=
  [klSlot, krSlot, kaSlot, kbSlot].zipIdx.flatMap fun (k, v) =>
    loadBE64 (hiReg v) t0 sb (8 * k) ++ loadBE64 (loReg v) t0 sb (8 * (k + 1))

/-- Store word `i` of the schedule: the high (`hi`) or low half of value `v`
rotated left by `r` bits, big-endian. -/
def subkey (i v r : Nat) (hi : Bool) : List Instr :=
  let (a, b) := if (r < 64) = hi then (hiReg v, loReg v) else (loReg v, hiReg v)
  let r' := r % 64
  (if r' = 0 then [movR t0 a] else [shlI t0 a r', shrI t1 b (64 - r'), orR t0 t0 t1]) ++
  storeBE 8 t0 t1 .a2 (8 * i)

def storeSubkeys (ks : List (Nat × Nat × Bool)) : List Instr :=
  ks.zipIdx.flatMap fun ((v, r, hi), i) => subkey i v r hi

def expandKey : Prog isa :=
  .seq (.block ([movR sb .a3, movR .a3 .a1] ++ saveRegs ++ setSlots allMasks ++ tableSetup ++
      sigmas.flatMap sigmaOne))
    (.seq loadKey
      (.seq (.block tableSetup)
        (.seq kaKb
          (.seq (.block (loadValues ++ ([.addi t0 .a3 (-16)] : List Instr)))
            (.seq (.ite (.zero t0) (.block (storeSubkeys subkeys128)) (.block (storeSubkeys subkeys256)))
              (.block restoreRegs))))))

end VG.Impl.Camellia.RISCV64
