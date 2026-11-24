module

public import VerifiedGarbage.Impl.Aes.X86.Ctr32
public import VerifiedGarbage.Impl.Camellia.KeyOrder

/-!
# The Camellia key schedule on x86 (32-bit)

`expandKey table mid(key, key_len, schedule, scratch)`, cdecl (the arguments
at `[esp + 4]` … `[esp + 16]`): `vg_camellia_expand_key` with its working
space in the scratch buffer, which the artifact allocates on the stack,
moved to `edi`. The callee-saved registers are saved in it (`savedSlot`).

* The address of the static `table`, which `mid` reads, is taken first, and
  waits in `edx`.
* The values are four words each, at their slots: `KL` and `KR` (RFC 3713
  §2.2) are loaded from the key (`loadKey`), little-endian words of the
  big-endian bytes.
* `KA` and `KB` take three pairs of rounds with the constants `Sigma1 …
  Sigma6` as subkeys: the block `mid`, which each implementation has of its
  own (`AesNiExpandKey.lean`, `SseExpandKey.lean`), for what it has in the
  slots before the values and after the saved registers.
* The subkeys are then halves of rotations of `KL`, `KR`, `KA` and `KB` as
  128-bit numbers, computed on their byte-swapped words, and stored
  byte-swapped, in the order of `Spec.Camellia.scheduleWords`.

Only the pointers, the key's length, the static's address and the branches'
tests are public; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86

open VG.X86 VG.Impl.Aes.X86 VG.Impl.Camellia

/-- The values' slots: `KL`, `KR`, `KA`, `KB`. -/
def klSlot : Nat := 72
def krSlot : Nat := 76
def kaSlot : Nat := 84
def kbSlot : Nat := 88

/-- The callee-saved registers' slots, after the values'. -/
def savedSlot : Nat := 92

/-- The callee-saved registers, and their slots from `j`. -/
def savedRegsAt (j : Nat) : List (Reg × Nat) := [(.ebx, j), (.esi, j + 1), (.edi, j + 2), (.ebp, j + 3)]

/-- Load the scratch buffer's address (argument `k`) to `edi`, saving the
registers in the slots from `j` there first. -/
def saveRegsAt (j k : Nat) : List Instr :=
  [.mov .eax (.mem (argOp k))] ++ (savedRegsAt j).map (fun (r, i) => .store (slotAt .eax i) r) ++ [movR .edi .eax]

/-- Restore the registers from the slots from `j` (`edi`, the base, last). -/
def restoreRegsAt (j : Nat) : List Instr := [movS .ebx j, movS .esi (j + 1), movS .ebp (j + 3), movS .edi (j + 2)]

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

/-- The whole function, after the table's address is in `edx`. -/
def expandKeyMain (mid : List Instr) : Prog isa :=
  .seq (.block (saveRegsAt savedSlot 3))
    (.seq loadKey
      (.seq (.block mid)
        (.seq (.block (revValues ++ [.mov .edx (.mem (argOp 2)), .mov .eax (.mem (argOp 1)),
            .alu .cmp .eax (.imm 16)]))
          (.seq (.ite .e (.block (storeSubkeys subkeys128)) (.block (storeSubkeys subkeys256)))
            (.block (restoreRegsAt savedSlot))))))

def expandKey (table : String) (mid : List Instr) : Prog isa :=
  .seq (.frame (.symPush .eax table) (.block []) (.pop .ecx 1))
    (.seq (.block [.mov .edx (.reg .eax)]) (expandKeyMain mid))

end VG.Impl.Camellia.X86
