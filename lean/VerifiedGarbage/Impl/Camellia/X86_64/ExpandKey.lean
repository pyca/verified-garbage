import VerifiedGarbage.Impl.Camellia.X86_64.Ecb
import VerifiedGarbage.Spec.Camellia
import VerifiedGarbage.Impl.Camellia.KeyOrder

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

/-- The planes of the constant `x` to the entry at `rsi`, and on to the next. -/
def sigmaOne (x : BitVec 64) : List Instr :=
  (List.range 8).flatMap (fun j => [.movImm64 .rax (keyPlane x j), .store (slotAt .rsi j) .rax]) ++
  ([.alu .add .rsi (.imm 64)] : List Instr)

/-- Load the key: `KL`, and `KR` by the key's length (in `rsi`). -/
def loadKey : Prog isa :=
  .seq (.block [.mov .rax (.mem (at_ .rdi 0)), st klSlot .rax, .mov .rax (.mem (at_ .rdi 8)),
      st (klSlot + 1) .rax, .alu .cmp .rsi (.imm 16)])
    (.ite .e (.block [.mov32 .rax (.imm 0), st krSlot .rax, st (krSlot + 1) .rax])
      (.seq (.block [.mov .rax (.mem (at_ .rdi 16)), st krSlot .rax, .alu .cmp .rsi (.imm 24)])
        (.ite .e (.block [.alu .xor .rax (.imm 0xFFFFFFFF), st (krSlot + 1) .rax])
          (.block [.mov .rax (.mem (at_ .rdi 24)), st (krSlot + 1) .rax]))))

/-- The word at `[rdi + d]` in all eight lanes, bitsliced. -/
def spread (d : Nat) : List Instr :=
  ([.mov (q 0) (.mem (at_ .rdi d))] : List Instr) ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++ toBs

/-- `w := w ^ x`, for the two words at slots `w` and `x`. -/
def xorWords (w x : Nat) : List Instr :=
  [movS .rax x, xorS .rax w, st w .rax, movS .rax (x + 1), xorS .rax (w + 1), st (w + 1) .rax]

/-- Copy the two words at slot `x` to slot `w`. -/
def copyWords (w x : Nat) : List Instr :=
  [movS .rax x, st w .rax, movS .rax (x + 1), st (w + 1) .rax]

/-- Two rounds on the running value (at `rdi`), with the next two entries of the table. -/
def pairPlain : List Instr :=
  spread 8 ++ storeHalf d2Slot ++ spread 0 ++ storeHalf d1Slot ++
  round 0 d2Slot ++ round 8 d1Slot ++ fromBs ++ [st wSlot (q 0)] ++
  loadHalf d2Slot ++ fromBs ++ [st (wSlot + 1) (q 0), .alu .add kp (.imm 128)]

/-- `KA` and `KB`: the running value starts as `KL ^ KR`; after the first
pair `KL` is XORed in, after the second it is `KA`, and `KA ^ KR` goes on;
after the third it is `KB`. `r8` counts the pairs down from 3. -/
def kaKb : Prog isa :=
  .seq (.block (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++ ([.movImm64 .r8 3, movR .rdi sb,
      .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * wSlot)))] : List Instr)))
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
  ([.bswap t0, .store (at_ .rdx (8 * i)) t0] : List Instr)

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
