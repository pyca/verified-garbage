module

public import VerifiedGarbage.Impl.Camellia.X86.Ecb
public import VerifiedGarbage.Impl.Camellia.KeyOrder
public import VerifiedGarbage.Impl.Camellia.Planes32

/-!
# The Camellia key schedule on x86 (32-bit)

`expandKey(key, key_len, schedule, scratch)`, cdecl (the arguments at
`[esp + 4]` … `[esp + 16]`): `vg_camellia_expand_key` with its working
space in the scratch buffer (`Layers.lean`, moved to `edi`), which the
artifact allocates on the stack. As on ARMv7
(`Impl/Camellia/Arm/ExpandKey.lean`):

* `KA` and `KB` (RFC 3713 §2.2) take three pairs of rounds with the
  constants `Sigma1 … Sigma6` as subkeys (their planes stored as a table
  from immediates), which the bitsliced rounds of ECB run on eight copies
  of the 128-bit value; the XORs between the pairs are on the plain words.
* The words are kept as ECB loads them, little-endian words of the
  big-endian bytes, in the tail buffer's slots: `KL`, `KR`, the running
  value, `KA`, `KB`, four words each. The pairs left are counted in slot
  654; the key's length and the schedule's pointer are read from the
  arguments.
* The subkeys are then halves of rotations of `KL`, `KR`, `KA` and `KB` as
  128-bit numbers, computed on their byte-swapped words, and stored
  byte-swapped, in the order of `Spec.Camellia.scheduleWords`.

Only the pointers, the key's length, `kp`, the count and its slot, and the
branches' tests hold public values; no address and no branch depends on
anything else.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86

open VG.X86 VG.Impl.Aes.X86 VG.Impl.Camellia

/-- The values' slots: `KL`, `KR`, the running value, `KA`, `KB`. -/
def klSlot : Nat := tailSlot
def krSlot : Nat := tailSlot + 4
def wSlot : Nat := tailSlot + 8
def kaSlot : Nat := tailSlot + 12
def kbSlot : Nat := tailSlot + 16
def cntSlot : Nat := grpSlot

/-- The planes of the constant `x` to entry `e` of the table. -/
def sigmaOne (e : Nat) (x : BitVec 64) : List Instr :=
  (List.range 16).flatMap fun k => [movI .eax (keyPlane32 x (k / 8) (k % 8)), st (keySlot + 16 * e + k) .eax]

/-- `w := w ^ x`, for the four words at slots `w` and `x`. -/
def xorWords (w x : Nat) : List Instr :=
  (List.range 4).flatMap fun k => [movS .eax (x + k), xorS .eax (w + k), st (w + k) .eax]

/-- Copy the four words at slot `x` to slot `w`. -/
def copyWords (w x : Nat) : List Instr := (List.range 4).flatMap fun k => [movS .eax (x + k), st (w + k) .eax]

/-- Load the key (at `ecx`): `KL`, and `KR` by the key's length. -/
def loadKey : Prog isa :=
  .seq (.block ([.mov .ecx (.mem (argOp 0))] ++
      (List.range 4).flatMap (fun k => [.mov .eax (.mem (at_ .ecx (4 * k))), st (klSlot + k) .eax]) ++
      [.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 16)]))
    (.ite .e (.block ([movI .eax 0] ++ (List.range 4).map fun k => st (krSlot + k) .eax))
      (.seq (.block [.mov .eax (.mem (at_ .ecx 16)), st krSlot .eax, .mov .eax (.mem (at_ .ecx 20)),
          st (krSlot + 1) .eax, .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 24)])
        (.ite .e
          (.block [.mov .eax (.mem (at_ .ecx 16)), notR .eax, st (krSlot + 2) .eax,
            .mov .eax (.mem (at_ .ecx 20)), notR .eax, st (krSlot + 3) .eax])
          (.block [.mov .eax (.mem (at_ .ecx 24)), st (krSlot + 2) .eax, .mov .eax (.mem (at_ .ecx 28)),
            st (krSlot + 3) .eax]))))

/-- The running value's words in all eight lanes, to the planes of the halves. -/
def bcast : List Instr :=
  (List.range 4).flatMap fun w =>
    [movS .eax (wSlot + w)] ++ (List.range 8).map (fun b => st b .eax) ++ ortho ++
      (List.range 8).flatMap (fun j => [movS .eax j, st (stateSlot w j) .eax])

/-- Lane 0's words back from the planes. -/
def unbcast : List Instr :=
  (List.range 4).flatMap fun w =>
    (List.range 8).flatMap (fun j => [movS .eax (stateSlot w j), st j .eax]) ++ ortho ++
      [movS .eax 0, st (wSlot + w) .eax]

/-- Two rounds on the running value, with the next two entries of the table. -/
def pairPlain : List Instr :=
  bcast ++ (round 0 d1Slot d2Slot ++ round 16 d2Slot d1Slot) ++ (unbcast ++ [addI kp 128])

/-- `KA` and `KB`: the running value starts as `KL ^ KR`; after the first
pair `KL` is XORed in, after the second it is `KA`, and `KA ^ KR` goes on;
after the third it is `KB`. The count goes down from 3 in its slot. -/
def kaKb : Prog isa :=
  .seq (.block (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++ [movI .eax 3, st cntSlot .eax]))
    (.loop (.seq (.block (pairPlain ++ [movS .eax cntSlot, movR .ebx .eax, shrI .ebx 1, .alu .cmp .ebx (.imm 0)]))
      (.seq (.ite .ne
          (.seq (.block [.alu .cmp .eax (.imm 3)])
            (.ite .e (.block (xorWords wSlot klSlot))
              (.block (copyWords kaSlot wSlot ++ xorWords wSlot krSlot))))
          (.block (copyWords kbSlot wSlot)))
        (.block [movS .eax cntSlot, subI .eax 1, st cntSlot .eax]))) .ne)

/-- `KL`, `KR`, `KA`, `KB` (`0 … 3`): their slots. -/
def valSlot : Nat → Nat | 0 => klSlot | 1 => krSlot | 2 => kaSlot | _ => kbSlot

/-- The four values' words, byte-swapped into numbers in place. -/
def revValues : List Instr :=
  [0, 1, 2, 3].flatMap fun v => (List.range 4).flatMap fun k =>
    [movS .eax (valSlot v + k), .bswap .eax, st (valSlot v + k) .eax]

/-- Word `o` (0–3, the most significant first) of value `v` rotated left by
`r` bits, into `eax`: a left shift by `s` is a rotation by `32 - s` with
the bits that wrapped around masked off. -/
def rotWord (v r o : Nat) : List Instr :=
  let n := r / 32
  let s := r % 32
  if s = 0 then [movS .eax (valSlot v + (o + n) % 4)]
  else [movS .eax (valSlot v + (o + n) % 4), movS .ebx (valSlot v + (o + n + 1) % 4), rorI .eax (32 - s),
    andI .eax (BitVec.allOnes 32 <<< s), shrI .ebx (32 - s), .alu .or .eax (.reg .ebx)]

/-- Store subkey `i` of the schedule (at `edx`): the high (`hi`) or low half
of value `v` rotated left by `r` bits, byte-swapped. -/
def subkey (i v r : Nat) (hi : Bool) : List Instr :=
  [0, 1].flatMap fun k =>
    rotWord v r ((if hi then 0 else 2) + k) ++ [.bswap .eax, .store (at_ .edx (8 * i + 4 * k)) .eax]

def storeSubkeys (ks : List (Nat × Nat × Bool)) : List Instr :=
  ks.zipIdx.flatMap fun ((v, r, hi), i) => subkey i v r hi

def expandKey : Prog isa :=
  .seq (.block (saveRegs 3 ++ (sigmas.zipIdx.flatMap fun (x, e) => sigmaOne e x)))
    (.seq loadKey
      (.seq (.block (kpAt keySlot))
        (.seq kaKb
          (.seq (.block (revValues ++ [.mov .edx (.mem (argOp 2)), .mov .eax (.mem (argOp 1)),
              .alu .cmp .eax (.imm 16)]))
            (.seq (.ite .e (.block (storeSubkeys subkeys128)) (.block (storeSubkeys subkeys256)))
              (.block restoreRegs))))))

end VG.Impl.Camellia.X86
