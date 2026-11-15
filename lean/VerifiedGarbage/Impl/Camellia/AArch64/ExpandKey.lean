module

public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Core
public import VerifiedGarbage.Impl.Camellia.KeyOrder

/-!
# The Camellia key schedule on AArch64

`expandKey(key = x0, key_len = x1, schedule = x2, scratch = x3)`:
`vg_camellia_expand_key` with its working space in the scratch buffer
(`Layers.lean`, moved to `x5`), which the artifact allocates on the stack.

* `KA` and `KB` (RFC 3713 §2.2) are one chain of three pairs of rounds with
  the constants `Sigma1 … Sigma6` as subkeys, each round needing the one
  before, so nothing is gained by running eight copies of it bitsliced, as
  the ECB code runs eight blocks: these are the single-block core's rounds
  (`Serial/Core.lean`), the halves in `x6` and `x7`, with the constant an
  immediate (`fConst`). The S-box is in the table registers `v16`–`v31`,
  loaded by immediates (`Impl.Tbl.AArch64.loadTable`), and the eight bytes
  of a round's word select from it with `tbl`, whose time does not depend on
  its data.
* `KL`, `KR`, `KA` and `KB` are kept as the key is loaded, little-endian
  words of the big-endian bytes, in the tail buffer's slots, two words
  each. `KB` is computed only for a key of 24 or 32 bytes, whose subkeys
  alone use it.
* The subkeys are then halves of rotations of `KL`, `KR`, `KA` and `KB` as
  128-bit numbers, computed on their byte-swapped words, and stored
  byte-swapped, in the order of `Spec.Camellia.scheduleWords`.

Only `x0` (the key), `x2`, `x3` (the key's length), `x5`, the rounds' masks
(`x13`–`x15`) and the branches' tests hold public values; no address and no
branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Camellia.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64 VG.Impl.Camellia

def klSlot : Nat := tailSlot
def krSlot : Nat := tailSlot + 2
def kaSlot : Nat := tailSlot + 6
def kbSlot : Nat := tailSlot + 8

/-- Load the key: `KL`, and `KR` by the key's length (in `x3`). -/
def loadKey : Prog isa :=
  .seq (.block [.ldr .x t0 .x0 0, stS klSlot t0, .ldr .x t0 .x0 8, stS (klSlot + 1) t0,
      .subImm .x t1 .x3 16])
    (.ite (.zero .x t1) (.block [.movz .x t0 0 0, stS krSlot t0, stS (krSlot + 1) t0])
      (.seq (.block [.ldr .x t0 .x0 16, stS krSlot t0, .subImm .x t1 .x3 24])
        (.ite (.zero .x t1)
          (.block [.movz .x u7 0 0, .subImm .x u7 u7 1, eorR t0 t0 u7, stS (krSlot + 1) t0])
          (.block [.ldr .x t0 .x0 24, stS (krSlot + 1) t0]))))

/-- `b ^= F(a, x)`: the single-block core's round (`Serial.f`) on the
halves `a` and `b`, with the constant `x` as its subkey. -/
def fConst (a b : Reg) (x : BitVec 64) : List Instr :=
  imm .x8 x ++ ([.logic .eor .x .x10 a .x8] : List Instr) ++ Serial.substitute ++ Serial.linear ++
    ([.logic .eor .x b b .x10] : List Instr)

/-- Two rounds on the halves, with the constants `x` and `y`. -/
def pairConst (x y : BitVec 64) : List Instr := fConst .x6 .x7 x ++ fConst .x7 .x6 y

/-- XOR the value at slots `k` and `k + 1`, byte-swapped, into the halves. -/
def xorValue (k : Nat) : List Instr :=
  Serial.loadBE .x8 (8 * k) ++ ([.logic .eor .x .x6 .x6 .x8] : List Instr) ++
    Serial.loadBE .x8 (8 * (k + 1)) ++ ([.logic .eor .x .x7 .x7 .x8] : List Instr)

/-- Store the halves, byte-swapped, as the value at slots `k` and `k + 1`. -/
def storeValue (k : Nat) : List Instr :=
  [.rev .x8 .x6, stS k .x8, .rev .x8 .x7, stS (k + 1) .x8]

/-- `KA`, from `KL` and `KR` in their slots; the halves are left holding it. -/
def ka : List Instr :=
  Serial.loadBE .x6 (8 * klSlot) ++ Serial.loadBE .x7 (8 * (klSlot + 1)) ++ xorValue krSlot ++
    pairConst Spec.Camellia.sigma1 Spec.Camellia.sigma2 ++ xorValue klSlot ++
    pairConst Spec.Camellia.sigma3 Spec.Camellia.sigma4 ++ storeValue kaSlot

/-- `KB`, from `KA` in the halves and `KR` in its slots. -/
def kb : List Instr :=
  xorValue krSlot ++ pairConst Spec.Camellia.sigma5 Spec.Camellia.sigma6 ++ storeValue kbSlot

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
  .seq (.block ([movR sb .x3, movR .x3 .x1] ++ saveRegs))
    (.seq loadKey
      (.seq (.block (([.subImm .x t0 .x3 16] : List Instr) ++
          Impl.Tbl.AArch64.loadTable (fun k => Spec.Camellia.sbox1Table.getD k 0) ++
          Serial.quarterConstants ++ Serial.maskConstants ++ ka))
        (.seq (.ite (.zero .x t0) (.block (loadValues ++ storeSubkeys subkeys128))
            (.block (kb ++ (loadValues ++ storeSubkeys subkeys256))))
          (.block restoreRegs))))

end VG.Impl.Camellia.AArch64
