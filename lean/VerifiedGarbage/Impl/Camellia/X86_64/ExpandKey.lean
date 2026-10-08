import VerifiedGarbage.Impl.Camellia.X86_64.Ecb
import VerifiedGarbage.Spec.Camellia

/-!
# The Camellia key schedule on x86-64

`expandKey(key = rdi, key_len = rsi, schedule = rdx, scratch = rcx)`:
`vg_camellia_expand_key` with its working space in the scratch buffer
(`Layers.lean`, moved to `r9`), which the artifact allocates on the stack.

`KA` and `KB` (RFC 3713 §2.2) take three pairs of rounds with the constants
`Sigma1 … Sigma6` as subkeys (their planes immediates in the code), which
the bitsliced rounds of ECB run, on eight copies of the 128-bit value (the
two halves as one block); the XORs between the pairs are on the plain words. The words are kept as ECB loads
them, little-endian words of the big-endian bytes, in the tail buffer's
slots: `KL`, `KR`, the running value, `KA`, `KB`, two words each.
The subkeys are then halves of rotations of `KL`, `KR`, `KA` and `KB` as
128-bit numbers, computed on their byte-swapped words, and stored
byte-swapped, in the order of `Spec.Camellia.scheduleWords`.

Only `rdi`, `rsi` (the key length, then the table), `rdx` and `r9` hold
public values, and `r8` counts the pairs; no address and no branch depends
on anything else.
-/

namespace VG.Impl.Camellia.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

def klSlot : Nat := tailSlot
def krSlot : Nat := tailSlot + 2
def wSlot : Nat := tailSlot + 4
def kaSlot : Nat := tailSlot + 6
def kbSlot : Nat := tailSlot + 8

/-- The byte of a half that position `c` of a plane holds (as `toBs` lays out a half). -/
def bytePos (c : Nat) : Nat := c / 2 + 4 * (c % 2)

/-- Plane `j` of the subkey `x` in every lane, as the table holds it: bit
`8 c + b` is bit `j` of byte `bytePos c` of `x`, the most significant first. -/
def keyPlane (x : BitVec 64) (j : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 64).foldl
    (fun acc p => acc + if x.getLsbD (56 - 8 * bytePos (p / 8) + j) then 2 ^ p else 0) 0)

/-- The subkeys of the pairs. -/
def sigmas : List (BitVec 64) :=
  [Spec.Camellia.sigma1, Spec.Camellia.sigma2, Spec.Camellia.sigma3, Spec.Camellia.sigma4,
    Spec.Camellia.sigma5, Spec.Camellia.sigma6]

/-- The planes of the constant `x` to the entry at `rsi`, and on to the next. -/
def sigmaOne (x : BitVec 64) : List Instr :=
  (List.range 8).flatMap (fun j => [.movImm64 .rax (keyPlane x j), .store (slotAt .rsi j) .rax]) ++
  [.alu .add .rsi (.imm 64)]

/-- Load the key: `KL`, and `KR` by the key's length (in `rsi`). -/
def loadKey : Prog isa :=
  .seq (.block [.mov .rax (.mem (at_ .rdi 0)), st klSlot .rax, .mov .rax (.mem (at_ .rdi 8)),
      st (klSlot + 1) .rax, .alu .cmp .rsi (.imm 16)])
    (.ite .e (.block [.mov32 .rax (.imm 0), st krSlot .rax, st (krSlot + 1) .rax])
      (.seq (.block [.mov .rax (.mem (at_ .rdi 16)), st krSlot .rax, .alu .cmp .rsi (.imm 24)])
        (.ite .e (.block [.alu .xor .rax (.imm 0xFFFFFFFF), st (krSlot + 1) .rax])
          (.block [.mov .rax (.mem (at_ .rdi 24)), st (krSlot + 1) .rax]))))

/-- The word at slot `k` in all eight lanes, bitsliced. -/
def spread (k : Nat) : List Instr :=
  [movS (q 0) k] ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++ toBs

/-- `w := w ^ x`, for the two words at slots `w` and `x`. -/
def xorWords (w x : Nat) : List Instr :=
  [movS .rax x, xorS .rax w, st w .rax, movS .rax (x + 1), xorS .rax (w + 1), st (w + 1) .rax]

/-- Copy the two words at slot `x` to slot `w`. -/
def copyWords (w x : Nat) : List Instr :=
  [movS .rax x, st w .rax, movS .rax (x + 1), st (w + 1) .rax]

/-- Two rounds on the running value, with the next two entries of the table. -/
def pairPlain : List Instr :=
  spread (wSlot + 1) ++ storeHalf d2Slot ++ spread wSlot ++ storeHalf d1Slot ++
  round 0 d2Slot ++ round 8 d1Slot ++ fromBs ++ [st wSlot (q 0)] ++
  loadHalf d2Slot ++ fromBs ++ [st (wSlot + 1) (q 0), .alu .add kp (.imm 128)]

/-- `KA` and `KB`: the running value starts as `KL ^ KR`; after the first
pair `KL` is XORed in, after the second it is `KA`, and `KA ^ KR` goes on;
after the third it is `KB`. `r8` counts the pairs down from 3. -/
def kaKb : Prog isa :=
  .seq (.block (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++ [.movImm64 .r8 3]))
    (.loop (.seq (.block pairPlain)
      (.seq (.block [.alu .cmp .r8 (.imm 2)])
        (.seq (.ite .ae
          (.seq (.block [.alu .cmp .r8 (.imm 3)])
            (.ite .e (.block (xorWords wSlot klSlot))
              (.block (copyWords kaSlot wSlot ++ xorWords wSlot krSlot))))
          (.block (copyWords kbSlot wSlot)))
          (.block [.alu .sub .r8 (.imm 1)])))) .ne)

/-- The 128-bit values' registers: high and low words, as numbers. -/
def hiReg : Nat → Reg | 0 => .rax | 1 => .rcx | 2 => .r10 | _ => .r12
def loReg : Nat → Reg | 0 => .rbx | 1 => .rbp | 2 => .r11 | _ => .r13

/-- `KL`, `KR`, `KA`, `KB` (`0 … 3`), byte-swapped into their registers. -/
def loadValues : List Instr :=
  [klSlot, krSlot, kaSlot, kbSlot].zipIdx.flatMap fun (k, v) =>
    [movS (hiReg v) k, .bswap (hiReg v), movS (loReg v) (k + 1), .bswap (loReg v)]

/-- Store word `i` of the schedule: the high (`hi`) or low half of value `v`
rotated left by `r` bits, byte-swapped. -/
def subkey (i v r : Nat) (hi : Bool) : List Instr :=
  let (a, b) := if (r < 64) = hi then (hiReg v, loReg v) else (loReg v, hiReg v)
  let r' := r % 64
  [movR t0 a] ++
  (if r' = 0 then [] else [.shift .shl t0 r', movR t1 b, .shift .shr t1 (64 - r'), .alu .or t0 (.reg t1)]) ++
  [.bswap t0, .store (at_ .rdx (8 * i)) t0]

def KL : Nat := 0
def KR : Nat := 1
def KA : Nat := 2
def KB : Nat := 3

/-- The subkeys of a key of 16 bytes (RFC 3713 §2.2), in the stored order:
value, rotation and half of each. -/
def subkeys128 : List (Nat × Nat × Bool) :=
  [(KL, 0, true), (KL, 0, false),
   (KA, 0, true), (KA, 0, false), (KL, 15, true), (KL, 15, false), (KA, 15, true), (KA, 15, false),
   (KA, 30, true), (KA, 30, false),
   (KL, 45, true), (KL, 45, false), (KA, 45, true), (KL, 60, false), (KA, 60, true), (KA, 60, false),
   (KL, 77, true), (KL, 77, false),
   (KL, 94, true), (KL, 94, false), (KA, 94, true), (KA, 94, false), (KL, 111, true), (KL, 111, false),
   (KA, 111, true), (KA, 111, false)]

/-- The subkeys of a key of 24 or 32 bytes, in the stored order. -/
def subkeys256 : List (Nat × Nat × Bool) :=
  [(KL, 0, true), (KL, 0, false),
   (KB, 0, true), (KB, 0, false), (KR, 15, true), (KR, 15, false), (KA, 15, true), (KA, 15, false),
   (KR, 30, true), (KR, 30, false),
   (KB, 30, true), (KB, 30, false), (KL, 45, true), (KL, 45, false), (KA, 45, true), (KA, 45, false),
   (KL, 60, true), (KL, 60, false),
   (KR, 60, true), (KR, 60, false), (KB, 60, true), (KB, 60, false), (KL, 77, true), (KL, 77, false),
   (KA, 77, true), (KA, 77, false),
   (KR, 94, true), (KR, 94, false), (KA, 94, true), (KA, 94, false), (KL, 111, true), (KL, 111, false),
   (KB, 111, true), (KB, 111, false)]

def storeSubkeys (ks : List (Nat × Nat × Bool)) : List Instr :=
  ks.zipIdx.flatMap fun ((v, r, hi), i) => subkey i v r hi

def expandKey : Prog isa :=
  .seq (.block ([movR .r9 .rcx] ++ saveRegs ++ setMasks layerMasks ++ [st dataSlot .rsi] ++
      [movR .rsi sb, .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * keySlot)))] ++
      sigmas.flatMap sigmaOne ++ [movS .rsi dataSlot]))
    (.seq loadKey
      (.seq (.block [movR kp sb, .alu .add kp (.imm (BitVec.ofNat 32 (8 * keySlot)))])
        (.seq kaKb
          (.seq (.block (loadValues ++ [movS t0 dataSlot, .alu .cmp t0 (.imm 16)]))
            (.seq (.ite .e (.block (storeSubkeys subkeys128)) (.block (storeSubkeys subkeys256)))
              (.block restoreRegs))))))

end VG.Impl.Camellia.X86_64
