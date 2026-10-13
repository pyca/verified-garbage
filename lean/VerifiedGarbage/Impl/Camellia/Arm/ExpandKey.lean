module

public import VerifiedGarbage.Impl.Camellia.Arm.Ecb
public import VerifiedGarbage.Impl.Camellia.KeyOrder
public import VerifiedGarbage.Impl.Camellia.Planes32

/-!
# The Camellia key schedule on ARMv7

`expandKey(key = r0, key_len = r1, schedule = r2, scratch = r3)`:
`vg_camellia_expand_key` with its working space in the scratch buffer
(`Layers.lean`, moved to `r8`), which the artifact allocates on the stack.
As on the 64-bit targets (`Impl/Camellia/AArch64/ExpandKey.lean`):

* `KA` and `KB` (RFC 3713 §2.2) take three pairs of rounds with the
  constants `Sigma1 … Sigma6` as subkeys (their planes stored as a table
  from immediates), which the bitsliced rounds of ECB run on eight copies
  of the 128-bit value; the XORs between the pairs are on the plain words.
* The words are kept as ECB loads them, little-endian words of the
  big-endian bytes, in the tail buffer's slots: `KL`, `KR`, the running
  value, `KA`, `KB`, four words each. The pairs left are counted in slot
  616, the key's length and the schedule's pointer wait in slots 628 and
  627.
* The subkeys are then halves of rotations of `KL`, `KR`, `KA` and `KB` as
  128-bit numbers, computed on their byte-swapped words, and stored
  byte-swapped, in the order of `Spec.Camellia.scheduleWords`.

Only `r0` (the key), `r1` (its length), `r2` (the schedule), `kp`, the
slots holding them and the count, and the branches' tests hold public
values; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Aes.Arm VG.Impl.Camellia

/-- The values' slots: `KL`, `KR`, the running value, `KA`, `KB`. -/
def klSlot : Nat := tailSlot
def krSlot : Nat := tailSlot + 4
def wSlot : Nat := tailSlot + 8
def kaSlot : Nat := tailSlot + 12
def kbSlot : Nat := tailSlot + 16
def cntSlot : Nat := grpSlot

/-- The planes of the constant `x` to entry `e` of the table. -/
def sigmaOne (e : Nat) (x : BitVec 64) : List Instr :=
  (List.range 16).flatMap fun k => imm32 t0 (keyPlane32 x (k / 8) (k % 8)) ++ [stS (keySlot + 16 * e + k) t0]

/-- `w := w ^ x`, for the four words at slots `w` and `x`. -/
def xorWords (w x : Nat) : List Instr :=
  (List.range 4).flatMap fun k => [ldS t0 (x + k), ldS t1 (w + k), eorR t0 t0 t1, stS (w + k) t0]

/-- Copy the four words at slot `x` to slot `w`. -/
def copyWords (w x : Nat) : List Instr := (List.range 4).flatMap fun k => [ldS t0 (x + k), stS (w + k) t0]

/-- Load the key: `KL`, and `KR` by the key's length (in `r1`). -/
def loadKey : Prog isa :=
  .seq (.block ((List.range 4).flatMap (fun k => [.ldr t0 .r0 (4 * k), stS (klSlot + k) t0]) ++
      [.cmp .r1 (.imm 16)]))
    (.ite .eq (.block ([.mov t0 (.imm 0)] ++ (List.range 4).map fun k => stS (krSlot + k) t0))
      (.seq (.block [.ldr t0 .r0 16, stS krSlot t0, .ldr t0 .r0 20, stS (krSlot + 1) t0, .cmp .r1 (.imm 24)])
        (.ite .eq
          (.block [.mov u7 (.imm 0), .dp .sub u7 u7 (.imm 1), .ldr t0 .r0 16, eorR t0 t0 u7,
            stS (krSlot + 2) t0, .ldr t0 .r0 20, eorR t0 t0 u7, stS (krSlot + 3) t0])
          (.block [.ldr t0 .r0 24, stS (krSlot + 2) t0, .ldr t0 .r0 28, stS (krSlot + 3) t0]))))

/-- Two rounds on the running value, with the next two entries of the table:
each of its words in all eight lanes, bitsliced, the rounds, and lane 0's
words back. -/
def pairPlain : List Instr :=
  (List.range 4).flatMap (fun w =>
    [ldS (q 0) (wSlot + w)] ++ (List.range 7).map (fun i => movR (q (i + 1)) (q 0)) ++ ortho ++
      (List.range 8).map (fun j => stS (stateSlot w j) (q j))) ++
  round 0 d1Slot d2Slot ++ round 16 d2Slot d1Slot ++
  (List.range 4).flatMap (fun w =>
    (List.range 8).map (fun j => ldS (q j) (stateSlot w j)) ++ ortho ++ [stS (wSlot + w) (q 0)]) ++
  [.dp .add kp kp (.imm 128)]

/-- `KA` and `KB`: the running value starts as `KL ^ KR`; after the first
pair `KL` is XORed in, after the second it is `KA`, and `KA ^ KR` goes on;
after the third it is `KB`. The count goes down from 3 in its slot. -/
def kaKb : Prog isa :=
  .seq (.block (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++ [.mov t0 (.imm 3), stS cntSlot t0]))
    (.loop (.seq (.block (pairPlain ++ [ldS t0 cntSlot, .mov t1 (lsrOp t0 1), .cmp t1 (.imm 0)]))
      (.seq (.ite .ne
          (.seq (.block [.cmp t0 (.imm 3)])
            (.ite .eq (.block (xorWords wSlot klSlot))
              (.block (copyWords kaSlot wSlot ++ xorWords wSlot krSlot))))
          (.block (copyWords kbSlot wSlot)))
        (.block [ldS t0 cntSlot, .subs t0 t0 (.imm 1), stS cntSlot t0]))) .ne)

/-- `KL`, `KR`, `KA`, `KB` (`0 … 3`): their slots. -/
def valSlot : Nat → Nat | 0 => klSlot | 1 => krSlot | 2 => kaSlot | _ => kbSlot

/-- The four values' words, byte-swapped into numbers in place. -/
def revValues : List Instr :=
  [0, 1, 2, 3].flatMap fun v => (List.range 4).flatMap fun k =>
    [ldS t0 (valSlot v + k), .rev t0 t0, stS (valSlot v + k) t0]

/-- Word `o` (0–3, the most significant first) of value `v` rotated left by
`r` bits, into `t0`. -/
def rotWord (v r o : Nat) : List Instr :=
  let n := r / 32
  let s := r % 32
  if s = 0 then [ldS t0 (valSlot v + (o + n) % 4)]
  else [ldS t0 (valSlot v + (o + n) % 4), ldS t1 (valSlot v + (o + n + 1) % 4),
    .mov t0 (.shifted t0 .lsl s), .dp .orr t0 t0 (lsrOp t1 (32 - s))]

/-- Store subkey `i` of the schedule (at `r2`): the high (`hi`) or low half
of value `v` rotated left by `r` bits, byte-swapped. -/
def subkey (i v r : Nat) (hi : Bool) : List Instr :=
  [0, 1].flatMap fun k =>
    rotWord v r ((if hi then 0 else 2) + k) ++ [.rev t0 t0, .str t0 .r2 (8 * i + 4 * k)]

def storeSubkeys (ks : List (Nat × Nat × Bool)) : List Instr :=
  ks.zipIdx.flatMap fun ((v, r, hi), i) => subkey i v r hi

def expandKey : Prog isa :=
  .seq (.block (saveRegs .r3 ++ [movR sb .r3, stS dSlot .r2, stS nSlot .r1] ++
      (sigmas.zipIdx.flatMap fun (x, e) => sigmaOne e x)))
    (.seq loadKey
      (.seq (.block [slotAddr kp keySlot])
        (.seq kaKb
          (.seq (.block (revValues ++ [ldS .r2 dSlot, ldS t0 nSlot, .cmp t0 (.imm 16)]))
            (.seq (.ite .eq (.block (storeSubkeys subkeys128)) (.block (storeSubkeys subkeys256)))
              (.block ([movR .r12 sb] ++ restoreRegs .r12)))))))

end VG.Impl.Camellia.Arm
