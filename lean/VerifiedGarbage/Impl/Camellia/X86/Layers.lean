module

public import VerifiedGarbage.Impl.Camellia.X86.Sbox
public import VerifiedGarbage.Impl.Aes.X86.Ctr32

/-!
# The layers of bitsliced Camellia on x86 (32-bit)

As on ARMv7 (`Impl/Camellia/Arm/Layers.lean`): eight blocks at a time, on
32-bit planes. Each of the four big-endian 32-bit words of the eight
blocks is eight planes, bit `8 i + b` of plane `j` of word `w` being bit
`j` of byte `i` (from the most significant) of word `w` of block `b`; a
64-bit half (`D1`: words 0 and 1, `D2`: words 2 and 3) is sixteen planes,
its left 32 bits in planes 0–7 and its right 32 bits in planes 8–15. The
P-function is, on each plane, XORs of the left and right planes with each
other rotated by 0, 8 or 16 bits; FL and FLINV's rotation by one bit takes
each plane to the next, and plane 7 to plane 0 rotated by 8. `SBOX2`,
`SBOX3` and `SBOX4` are `SBOX1` with a rotation of the output or input
byte, a masked exchange of neighbouring planes in the bytes that use them.

With only five free registers, every plane lives in the scratch buffer at
`edi`, in 4-byte slots: the S-box's planes (0–7) and spills (8–31); the
left word's S-box output during a round (32–39); the planes of `D1`
(40–55) and `D2` (56–71); the tail buffer (72–103, eight blocks), through
which every group is copied; the table of the bitsliced subkeys, sixteen
planes each, in the order the rounds use them (104–647); the callee-saved
registers `ebx`, `esi`, `edi` and `ebp` (648–651); the data pointer and the
blocks left (652, 653); the address of the end of the current group's
rounds (654); and the callee-saved registers of
`vg_camellia_crypt_prepared` (655–658), which ECB calls. The modes keep
their own state after them. The
subkey's entry is at `kp` (`esi`). The rounds write only below the tail
buffer, the transposes only below the table.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86

open VG.X86 VG.Impl.Aes.X86

/-- The subkeys' pointer. -/
def kp : Reg := .esi

/-- `op d, [kp + 4 k]`. -/
def ldK (d : Reg) (k : Nat) : Instr := .mov d (.mem (slotAt kp k))
def orS (d : Reg) (k : Nat) : Instr := .alu .or d (.mem (slotAt sb k))

/-! ## Slots -/

/-- The left word's S-box output. -/
def ylSlot : Nat := 32
def d1Slot : Nat := 40
def d2Slot : Nat := 56
/-- Plane `j` of word `w` (0–3) of the state: `D1`'s words, then `D2`'s. -/
def stateSlot (w j : Nat) : Nat := d1Slot + 8 * w + j
def tailSlot : Nat := 72
/-- Word `w` of block `b` of the tail buffer. -/
def tailAt (b w : Nat) : Nat := tailSlot + 4 * b + w
def keySlot : Nat := tailSlot + 32
/-- After the table of 34 subkeys. -/
def savedSlot : Nat := keySlot + 16 * 34
def dSlot : Nat := savedSlot + 4
def nSlot : Nat := dSlot + 1
def grpSlot : Nat := nSlot + 1

/-- The number of slots: the group's end's, `vg_camellia_crypt_prepared`'s
saved registers, and more, to a whole number of 8-byte words. -/
def slots : Nat := grpSlot + 18

/-- `vg_camellia_crypt_prepared`'s saved registers, after the group's end,
so that ECB's survive its calls. -/
def cryptSavedSlot : Nat := grpSlot + 1

/-- The callee-saved registers, and their slots from `j`. -/
def savedRegsAt (j : Nat) : List (Reg × Nat) := [(.ebx, j), (.esi, j + 1), (.edi, j + 2), (.ebp, j + 3)]

def savedRegs : List (Reg × Nat) := savedRegsAt savedSlot

/-- Load the scratch buffer's address (argument `k`) to `edi`, saving the
registers in the slots from `j` there first. -/
def saveRegsAt (j k : Nat) : List Instr :=
  [.mov .eax (.mem (argOp k))] ++ (savedRegsAt j).map (fun (r, i) => .store (slotAt .eax i) r) ++ [movR .edi .eax]

def saveRegs (k : Nat) : List Instr := saveRegsAt savedSlot k

/-- Restore the registers from the slots from `j` (`edi`, the base, last). -/
def restoreRegsAt (j : Nat) : List Instr := [movS .ebx j, movS .esi (j + 1), movS .ebp (j + 3), movS .edi (j + 2)]

def restoreRegs : List Instr := restoreRegsAt savedSlot

/-! ## A round -/

/-- The half's word at slot `d` with the planes at word `off` of `kp`, to
slots `0 … 7`. -/
def loadKeyed (d off : Nat) : List Instr :=
  (List.range 8).flatMap fun j => [movS .eax (d + j), .alu .xor .eax (.mem (slotAt kp (off + j))), st j .eax]

/-- In the byte of the mask `m`, plane `j` takes plane `j - 1` (cyclically):
the byte is rotated left by one bit. -/
def rotUp (m : BitVec 32) : List Instr :=
  [movS .ecx 7] ++
  ((List.range 7).reverse.flatMap fun i =>
    [movS .eax (i + 1), movR .ebx .eax, xorS .ebx i, andI .ebx m, xorR .eax .ebx, st (i + 1) .eax]) ++
  [movS .eax 0, movR .ebx .eax, xorR .ebx .ecx, andI .ebx m, xorR .eax .ebx, st 0 .eax]

/-- In the byte of the mask `m`, plane `j` takes plane `j + 1` (cyclically):
the byte is rotated right by one bit. -/
def rotDown (m : BitVec 32) : List Instr :=
  [movS .ecx 0] ++
  ((List.range 7).flatMap fun i =>
    [movS .eax i, movR .ebx .eax, xorS .ebx (i + 1), andI .ebx m, xorR .eax .ebx, st i .eax]) ++
  [movS .eax 7, movR .ebx .eax, xorR .ebx .ecx, andI .ebx m, xorR .eax .ebx, st 7 .eax]

/-- The left word (`t1 … t4` in bytes 0–3): `SBOX4`'s input (`t4`) is
rotated; `SBOX2`'s (`t2`) and `SBOX3`'s (`t3`) outputs. -/
def inSelL : List Instr := rotUp 0xFF000000
def outSelL : List Instr := rotUp 0x0000FF00 ++ rotDown 0x00FF0000

/-- The right word (`t5 … t8`): `SBOX4`'s input (`t7`); `SBOX2`'s (`t5`)
and `SBOX3`'s (`t6`) outputs. -/
def inSelR : List Instr := rotUp 0x00FF0000
def outSelR : List Instr := rotUp 0x000000FF ++ rotDown 0x0000FF00

/-- The left word of the half at slot `src` with the subkey's left planes
(word `off` of `kp`), and its input selection. -/
def preL (off src : Nat) : List Instr := loadKeyed src off ++ inSelL

/-- The left word's output selection, its planes to slots 32–39, then the
right word with the subkey's right planes, and its input selection. -/
def midLR (off src : Nat) : List Instr :=
  outSelL ++ (List.range 8).flatMap (fun j => [movS .eax j, st (ylSlot + j) .eax]) ++
    loadKeyed (src + 8) (off + 8) ++ inSelR

/-- Plane `j` of the P-function, from the left word's plane in slot
`32 + j` (into `eax`) and the right word's in slot `j` (into `ebx`), XORed
into the half at slot `dst`. -/
def pPlane (dst j : Nat) : List Instr :=
  [movS .eax (ylSlot + j), movS .ebx j, xorR .eax .ebx, movR .ecx .ebx, rorI .ecx 16, xorR .eax .ecx,
   xorR .ebx .eax, movR .ecx .eax, rorI .ecx 8, xorR .ebx .ecx, movR .ecx .ebx, rorI .ecx 16, xorR .eax .ecx,
   xorS .eax (dst + j), st (dst + j) .eax, xorS .ebx (dst + 8 + j), st (dst + 8 + j) .ebx]

/-- The right word's output selection, the P-function, and the XOR into
the half at slot `dst`. -/
def postP (dst : Nat) : List Instr := outSelR ++ (List.range 8).flatMap (pPlane dst)

/-- A round: `D_dst ^= F(D_src, k)`, the subkey's planes at word `off` of `kp`. -/
def round (off src dst : Nat) : List Instr :=
  preL off src ++ sboxCode ++ midLR off src ++ sboxCode ++ postP dst

/-! ## FL and FLINV -/

/-- Plane `j` of `x2 ^= (x1 & k1) <<< 1`: the right word's plane `j` (at
slot `d + 8 + j`) takes the AND of the left word's and the subkey's (word
`off` of `kp`) plane `j - 1`, and plane 0 that of plane 7 rotated by a
byte. -/
def flRotStep (d off j : Nat) : List Instr :=
  let i := (j + 7) % 8
  [ldK .eax (off + i), andS .eax (d + i)] ++ (if j = 0 then [rorI .eax 8] else []) ++
    [xorS .eax (d + 8 + j), st (d + 8 + j) .eax]

def flRot (d off : Nat) : List Instr := (List.range 8).flatMap (flRotStep d off)

/-- Plane `j` of `x1 ^= x2 | k2`. -/
def flOrStep (d off j : Nat) : List Instr :=
  [ldK .eax (off + 8 + j), orS .eax (d + 8 + j), xorS .eax (d + j), st (d + j) .eax]

def flOr (d off : Nat) : List Instr := (List.range 8).flatMap (flOrStep d off)

/-- FL on the half at slot `d`, the subkey at word `off` of `kp`. -/
def flCode (d off : Nat) : List Instr := flRot d off ++ flOr d off

/-- FLINV on the half at slot `d`. -/
def flinvCode (d off : Nat) : List Instr := flOr d off ++ flRot d off

/-- FLINV on `D2` with the subkey at the entry after `kp`'s, FL on `D1` with
`kp`'s, and on to the next entries. -/
def flLayer : List Instr := flinvCode d2Slot 16 ++ flCode d1Slot 0 ++ [addI kp 128]

end VG.Impl.Camellia.X86
