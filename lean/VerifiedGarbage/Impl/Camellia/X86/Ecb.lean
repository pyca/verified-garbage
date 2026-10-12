import VerifiedGarbage.Impl.Camellia.X86.Layers

/-!
# Camellia ECB, bitsliced, on x86 (32-bit)

`ecb dir(schedule, rounds, data, n, scratch)`, cdecl (the arguments at
`[esp + 4]` … `[esp + 20]`): `vg_camellia_ecb_encrypt` and
`vg_camellia_ecb_decrypt` with their working space in the scratch buffer
(`Layers.lean` has its layout), which the artifact allocates on the stack.

* The callee-saved registers are saved in the scratch buffer, whose address
  moves to `edi`.
* For 18 rounds or 24 (three groups of six rounds or four), the code that
  follows is written out for that number of groups, so the position of the
  postwhitening's subkeys in the table is a constant.
* The subkeys are bitsliced into the table at slot 104, in the order the
  rounds use them: the stored order for encryption; for decryption the
  order RFC 3713 §2.3.3 swaps them into, `kw3, kw4`, then the subkeys
  between `kw2` and `kw3` from the last back to the first, then `kw1,
  kw2`. Decryption then runs the same rounds as encryption.
* Each group of up to eight blocks is copied to the tail buffer, bitsliced
  and whitened, run through groups of six rounds with FL and FLINV between
  them, whitened again and stored back with its halves swapped, and copied
  back. The rounds use every register, so the data pointer and the blocks
  left wait in their slots, stored again after each copy (the analysis of
  constant time forgets what the buffer holds after a store through
  another pointer than `edi`).

Only the pointers, `rounds`, `n`, and what is computed from them (the
copies' pointers and counts, `kp`, the loop tests, and the slots holding
them) are public; no address and no branch depends on anything else.
-/

namespace VG.Impl.Camellia.X86

open VG.X86 VG.Impl.Aes.X86

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

/-! ## The subkeys -/

/-- `kp := ` the address of slot `k`. -/
def kpAt (k : Nat) : List Instr := [movR kp .edi, addI kp (BitVec.ofNat 32 (4 * k))]

/-- Plane `j` of the subkey's word in slot 0, to word `w` of the entry at
`kp`: bit `j` of each byte, masked into `ebx` and spread over its byte by
three shifted XORs (their bits never overlap), through `edx`. -/
def keyPlane (w j : Nat) : List Instr :=
  [movS .ebx 0] ++ (if j = 0 then [] else [shrI .ebx j]) ++
  [andI .ebx 0x01010101, movR .edx .ebx, rorI .edx 31, xorR .ebx .edx, movR .edx .ebx, rorI .edx 30,
   xorR .ebx .edx, movR .edx .ebx, rorI .edx 28, xorR .ebx .edx, .store (slotAt kp (8 * w + j)) .ebx]

/-- Bitslice the subkey at `[ecx + d]` (its bytes the most significant
first, so that a little-endian load puts byte `i` at bits `8 i … 8 i + 7`)
into the entry at `kp`, and step `kp` to the next entry. -/
def keyOne (d : Nat) : List Instr :=
  (List.range 2).flatMap (fun w => [.mov .eax (.mem (at_ .ecx (d + 4 * w))), st 0 .eax] ++
    (List.range 8).flatMap (keyPlane w)) ++ [addI kp 64]

/-- Encryption's table, for `g` groups: the `8 g + 2` subkeys in order. -/
def encKeys (g : Nat) : Prog isa :=
  .seq (.block ([.mov .ecx (.mem (argOp 0))] ++ kpAt keySlot ++ [movI .ebp (BitVec.ofNat 32 (8 * g + 2))]))
    (.loop (.block (keyOne 0 ++ [addI .ecx 8, subI .ebp 1])) .ne)

/-- Decryption's table, for `g` groups: `kw3, kw4` (words `8 g`, `8 g + 1`),
words `8 g - 1` down to 2, then `kw1, kw2`. -/
def decKeys (g : Nat) : Prog isa :=
  .seq (.block ([.mov .ecx (.mem (argOp 0))] ++ kpAt keySlot ++ [addI .ecx (BitVec.ofNat 32 (64 * g))] ++
      keyOne 0 ++ keyOne 8 ++ [subI .ecx 8, movI .ebp (BitVec.ofNat 32 (8 * g - 2))]))
    (.seq (.loop (.block (keyOne 0 ++ [subI .ecx 8, subI .ebp 1])) .ne)
      (.block ([subI .ecx 8] ++ keyOne 0 ++ keyOne 8)))

def keys (dir : Dir) (g : Nat) : Prog isa :=
  match dir with | .encrypt => encKeys g | .decrypt => decKeys g

/-! ## Eight blocks, in the tail buffer -/

/-- Word `w` of the eight blocks (in the tail buffer) to its planes. -/
def toBsWord (w : Nat) : List Instr :=
  (List.range 8).flatMap (fun b => [movS .eax (tailAt b w), st b .eax]) ++ ortho ++
  (List.range 8).flatMap (fun j => [movS .eax j, st (stateSlot w j) .eax])

/-- XOR the 32 words at `kp` into the state's planes: those of `D1` then
`D2`, or (`swap`) of `D2` then `D1`. -/
def whiten (swap : Bool) : List Instr :=
  (List.range 32).flatMap fun i =>
    let k := d1Slot + (if swap then (i + 16) % 32 else i)
    [movS .eax k, .alu .xor .eax (.mem (slotAt kp i)), st k .eax]

/-- Bitslice both halves and whiten them (`kw1` for `D1`, `kw2` for `D2`);
`kp` is left at the first round's entry. -/
def head : List Instr :=
  (List.range 4).flatMap toBsWord ++ kpAt keySlot ++ whiten false ++ [addI kp 128]

/-- Two rounds: `D2 ^= F(D1, k)`, `D1 ^= F(D2, k')`; Z when `kp` reaches the
group's end (loaded from its slot: the analysis of constant time takes a
comparison with a memory operand as secret). -/
def pairBody : List Instr :=
  round 0 d1Slot d2Slot ++ round 16 d2Slot d1Slot ++
  [addI kp 128, movS .eax grpSlot, .alu .cmp .eax (.reg kp)]

/-- Z when `kp` is at the postwhitening's entry, `8 g` entries into the table. -/
def atEnd (g : Nat) : List Instr :=
  [movR .eax kp, subR .eax .edi, .alu .cmp .eax (.imm (BitVec.ofNat 32 (4 * keySlot + 512 * g)))]

/-- Six rounds, then FL and FLINV unless they were the last; Z when `kp` is
at the postwhitening's entry, as the test `e` finds it. -/
def groupBodyWith (e : List Instr) : Prog isa :=
  .seq (.block [movR .eax kp, addI .eax 384, st grpSlot .eax])
    (.seq (.loop (.block pairBody) .ne)
      (.seq (.block e) (.seq (.ite .ne (.block flLayer) (.block [])) (.block e))))

/-- The groups for `g` groups, the end's offset an immediate. -/
def groupBody (g : Nat) : Prog isa := groupBodyWith (atEnd g)

/-- Output word `w` of the eight blocks (to the tail buffer), from the
planes of `D2` (words 0 and 1) or `D1` (words 2 and 3). -/
def fromBsWord (w : Nat) : List Instr :=
  (List.range 8).flatMap (fun j => [movS .eax (stateSlot ((w + 2) % 4) j), st j .eax]) ++ ortho ++
  (List.range 8).flatMap (fun b => [movS .eax b, st (tailAt b w) .eax])

/-- The postwhitening (`kw3` for `D2`, `kw4` for `D1`), and the halves back
to the blocks, swapped. -/
def tail : List Instr := whiten true ++ (List.range 4).flatMap fromBsWord

/-- The eight blocks of the tail buffer, in place, for `g` groups. -/
def crypt8 (g : Nat) : Prog isa := .seq (.block head) (.seq (.loop (groupBody g) .ne) (.block tail))

/-- The postwhitening's entry, `8 g` entries into the table, for the `6 g`
rounds of argument 1 (public), to its slot: its offset is `4 keySlot + 1536`
plus `(rounds - 18) & 4` rotated left by 7, which is 0 for 18 rounds and 512
for 24. -/
def setEnd : List Instr :=
  [.mov .edx (.mem (argOp 1)), subI .edx 18, andI .edx 4, rorI .edx 25,
    addI .edx (BitVec.ofNat 32 (4 * keySlot + 1536)), addR .edx .edi, st endSlot .edx]

/-- Z when `kp` is at the postwhitening's entry, from its slot. -/
def atEndS : List Instr := [movS .eax endSlot, .alu .cmp .eax (.reg kp)]

/-- The eight blocks of the tail buffer, in place, for 18 rounds or 24 (in
argument 1) with one copy of the rounds: the modes' (ECB keeps a copy for
each, which measured faster on some CPUs). -/
def crypt8R : Prog isa :=
  .seq (.block setEnd) (.seq (.block head) (.seq (.loop (groupBodyWith atEndS) .ne) (.block tail)))

/-! ## The groups -/

/-- Copy `ecx` blocks from `edx` to `ebx` (through `eax`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .edx 0)), .store (at_ .ebx 0) .eax, .mov .eax (.mem (at_ .edx 4)),
      .store (at_ .ebx 4) .eax, .mov .eax (.mem (at_ .edx 8)), .store (at_ .ebx 8) .eax,
      .mov .eax (.mem (at_ .edx 12)), .store (at_ .ebx 12) .eax, addI .edx 16, addI .ebx 16, subI .ecx 1]) .ne

/-- `ecx := min(ebp, 8)`, the blocks of this group. -/
def countR : Prog isa :=
  .seq (.block [movR .ecx .ebp, .alu .cmp .ebp (.imm 8)]) (.ite .b (.block []) (.block [movI .ecx 8]))

/-- The data pointer and the blocks left from their slots to `esi` and `ebp`,
and the blocks of this group to `ecx`. -/
def groupCount : Prog isa := .seq (.block [movS .esi dSlot, movS .ebp nSlot]) countR

/-- `r := ` the tail buffer's address. -/
def tailAddr (r : Reg) : List Instr := [movR r .edi, addI r (BitVec.ofNat 32 (4 * tailSlot))]

/-- The group's blocks to the tail buffer, and the data pointer and the
blocks left back to their slots. -/
def copyIn : Prog isa :=
  .seq groupCount (.seq (.block ([movR .edx .esi] ++ tailAddr .ebx))
    (.seq copyBlocks (.block [st dSlot .esi, st nSlot .ebp])))

/-- The tail buffer back to the group's blocks. -/
def copyOut : Prog isa := .seq groupCount (.seq (.block (tailAddr .edx ++ [movR .ebx .esi])) copyBlocks)

/-- On to the next group, the data pointer and the blocks left (still in
`esi` and `ebp`) back to their slots (Z set when none are left). -/
def advance : Prog isa :=
  .seq countR (.block [addI .esi 128, subR .ebp .ecx, st dSlot .esi, st nSlot .ebp])

/-- Eight blocks, or the last one to seven. -/
def group (g : Nat) : Prog isa := .seq copyIn (.seq (crypt8 g) (.seq copyOut advance))

/-- The table and the groups, for `g` groups of six rounds. -/
def body (dir : Dir) (g : Nat) : Prog isa :=
  .seq (keys dir g)
    (.seq (.block [.mov .eax (.mem (argOp 2)), st dSlot .eax, .mov .eax (.mem (argOp 3)), st nSlot .eax,
        .alu .test .eax (.reg .eax)])
      (.ite .e (.block []) (.loop (group g) .ne)))

/-- The whole function, for 18 rounds or 24. -/
def ecb (dir : Dir) : Prog isa :=
  .seq (.block (saveRegs 4 ++ [.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 18)]))
    (.seq (.ite .e (body dir 3) (body dir 4)) (.block restoreRegs))

end VG.Impl.Camellia.X86
