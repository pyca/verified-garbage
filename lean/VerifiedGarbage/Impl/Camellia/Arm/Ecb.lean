module

public import VerifiedGarbage.Impl.Camellia.Arm.Layers

/-!
# Camellia ECB, bitsliced, on ARMv7

`ecb dir(schedule = r0, rounds = r1, data = r2, n = r3, scratch = [sp])`:
`vg_camellia_ecb_encrypt` and `vg_camellia_ecb_decrypt` with their working
space in the scratch buffer (`Layers.lean` has its layout), which the
artifact allocates on the stack and passes as a stack argument.

* The callee-saved registers are saved, the scratch buffer moves to `r8`,
  the schedule's pointer to `r12`, the data pointer to `r1` and `n` to
  `r2`, which the subkeys' bitslicing leaves alone.
* The subkeys are bitsliced into the table at slot 72, in the order the
  rounds use them: the stored order for encryption; for decryption the
  order RFC 3713 §2.3.3 swaps them into, `kw3, kw4`, then the subkeys
  between `kw2` and `kw3` from the last back to the first, then `kw1,
  kw2`. Decryption then runs the same rounds as encryption.
* Each group of up to eight blocks is copied to the tail buffer, bitsliced
  and whitened, run through groups of six rounds with FL and FLINV between
  them, whitened again and stored back with its halves swapped, and copied
  back; the data pointer and the blocks left wait in their slots during
  the rounds, which use every register.

Only the pointers, `rounds`, `n`, and what is computed from them (the
copies' pointers and counts, `kp`, the loop tests, and the slots holding
them) are public; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Aes.Arm

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

/-! ## The subkeys -/

/-- `r := ` the address of slot `k`. -/
def slotAddr (r : Reg) (k : Nat) : Instr := .dp .add r sb (.imm (BitVec.ofNat 32 (4 * k)))

/-- Plane `j` of the subkey's word in `q 4`, to word `w` of the entry at
`kp`: bit `j` of each byte, masked into `q 5` by `t1 = 0x01010101` and
spread over its byte by three shifted XORs (their bits never overlap). -/
def keyPlane (w j : Nat) : List Instr :=
  [.dp .and (q 5) t1 (if j = 0 then .reg (q 4) else lsrOp (q 4) j), .dp .eor (q 5) (q 5) (rorOp (q 5) 31),
   .dp .eor (q 5) (q 5) (rorOp (q 5) 30), .dp .eor (q 5) (q 5) (rorOp (q 5) 28), .str (q 5) kp (4 * (8 * w + j))]

/-- The planes of the word in `q 4` to words `8 w …` of the entry at `kp`. -/
def keyPlanes (w : Nat) : List Instr := imm32 t1 0x01010101 ++ (List.range 8).flatMap (keyPlane w)

/-- Bitslice the subkey at `[r12 + d]` (its bytes the most significant
first, so that a little-endian load puts byte `i` at bits `8 i … 8 i + 7`)
into the entry at `kp`, and step `kp` to the next entry. -/
def keyOne (d : Nat) : List Instr :=
  (List.range 2).flatMap (fun w => .ldr (q 4) .r12 (d + 4 * w) :: keyPlanes w) ++ [.dp .add kp kp (.imm 64)]

/-- `kp := ` the table. -/
def tableSetup : List Instr := [slotAddr kp keySlot]

/-- What depends on the number of groups `g`: the subkeys the loop
bitslices in `lr`, and for decryption `r12` at `kw3`. -/
def groupConsts : Dir → Nat → List Instr
  | .encrypt, g => [.mov .lr (.imm (BitVec.ofNat 32 (8 * g + 2)))]
  | .decrypt, g => [.dp .add .r12 .r12 (.imm (BitVec.ofNat 32 (64 * g))), .mov .lr (.imm (BitVec.ofNat 32 (8 * g - 2)))]

/-- Encryption's table: the `lr` subkeys from `r12`, in order. -/
def encKeys : Prog isa :=
  .seq (.block tableSetup)
    (.loop (.block (keyOne 0 ++ [.dp .add .r12 .r12 (.imm 8), .subs .lr .lr (.imm 1)])) .ne)

/-- Decryption's table, for `g` groups, `r12` at word `8 g` and `lr = 8 g - 2`:
`kw3, kw4` (words `8 g`, `8 g + 1`), words `8 g - 1` down to 2, then
`kw1, kw2`. -/
def decKeys : Prog isa :=
  .seq (.block (tableSetup ++ keyOne 0 ++ keyOne 8 ++ [.dp .sub .r12 .r12 (.imm 8)]))
    (.seq (.loop (.block (keyOne 0 ++ [.dp .sub .r12 .r12 (.imm 8), .subs .lr .lr (.imm 1)])) .ne)
      (.block ([.dp .sub .r12 .r12 (.imm 8)] ++ keyOne 0 ++ keyOne 8)))

/-- The address of the postwhitening's entry, to `lr`: the table's last two
entries, `kw3` and `kw4` in the order the rounds use them, are before `kp`. -/
def endAddr : List Instr := [.dp .sub .lr kp (.imm 128)]

/-- The table for 18 rounds (Z set) or 24, and the postwhitening's address
in `lr`: the branches set only `groupConsts`, and one copy of the loops
builds either table. -/
def keys (dir : Dir) : Prog isa :=
  .seq (.ite .eq (.block (groupConsts dir 3)) (.block (groupConsts dir 4)))
    (.seq (match dir with | .encrypt => encKeys | .decrypt => decKeys) (.block endAddr))

/-! ## Eight blocks, in the tail buffer -/

/-- Word `w` of the eight blocks (in the tail buffer, at `r12`) to its planes. -/
def toBsWord (w : Nat) : List Instr :=
  (List.range 8).map (fun b => .ldr (q b) u7 (4 * (4 * b + w))) ++ ortho ++
  (List.range 8).map (fun j => stS (stateSlot w j) (q j))

/-- XOR the 32 words at `kp` into the state's planes: those of `D1` then
`D2`, or (`swap`) of `D2` then `D1`. -/
def whiten (swap : Bool) : List Instr :=
  (List.range 32).flatMap fun i =>
    let k := d1Slot + (if swap then (i + 16) % 32 else i)
    [ldS t1 k, .ldr t0 kp (4 * i), eorR t1 t1 t0, stS k t1]

/-- Bitslice both halves and whiten them (`kw1` for `D1`, `kw2` for `D2`);
`kp` is left at the first round's entry. -/
def head : List Instr :=
  slotAddr u7 tailSlot :: (List.range 4).flatMap toBsWord ++ [slotAddr kp keySlot] ++ whiten false ++
    [.dp .add kp kp (.imm 128)]

/-- Two rounds: `D2 ^= F(D1, k)`, `D1 ^= F(D2, k')`; Z when `kp` reaches the
group's end (in its slot). -/
def pairBody : List Instr :=
  round 0 d1Slot d2Slot ++ round 16 d2Slot d1Slot ++
  [.dp .add kp kp (.imm 128), ldS t0 grpSlot, .cmp kp (.reg t0)]

/-- Z when `kp` is at the postwhitening's entry. -/
def atEnd : List Instr := [ldS t0 endSlot, .cmp kp (.reg t0)]

/-- Six rounds, then FL and FLINV unless they were the last; Z when `kp` is
at the postwhitening's entry. -/
def groupBody : Prog isa :=
  .seq (.block [.dp .add t0 kp (.imm 384), stS grpSlot t0])
    (.seq (.loop (.block pairBody) .ne)
      (.seq (.block atEnd) (.seq (.ite .ne (.block flLayer) (.block [])) (.block atEnd))))

/-- Output word `w` of the eight blocks (to the tail buffer, through `sb`,
whose stores keep the analysis of constant time's public slots), from the
planes of `D2` (words 0 and 1) or `D1` (words 2 and 3). -/
def fromBsWord (w : Nat) : List Instr :=
  (List.range 8).map (fun j => ldS (q j) (stateSlot ((w + 2) % 4) j)) ++ ortho ++
  (List.range 8).map (fun b => stS (tailAt b w) (q b))

/-- The postwhitening (`kw3` for `D2`, `kw4` for `D1`), and the halves back
to the blocks, swapped. -/
def tail : List Instr := whiten true ++ (List.range 4).flatMap fromBsWord

/-- The eight blocks of the tail buffer, in place. -/
def crypt8 : Prog isa := .seq (.block head) (.seq (.loop groupBody .ne) (.block tail))

/-! ## The groups -/

/-- Copy `r3` blocks from `r0` to `r12` (through `t0`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.ldr t0 .r0 0, .str t0 .r12 0, .ldr t0 .r0 4, .str t0 .r12 4,
      .ldr t0 .r0 8, .str t0 .r12 8, .ldr t0 .r0 12, .str t0 .r12 12,
      .dp .add .r0 .r0 (.imm 16), .dp .add .r12 .r12 (.imm 16), .subs .r3 .r3 (.imm 1)]) .ne

/-- `r3 := min(r2, 8)`, the blocks of this group. -/
def groupCount : Prog isa :=
  .seq (.block [.mov t0 (lsrOp .r2 3), .cmp t0 (.imm 0)])
    (.ite .ne (.block [.mov .r3 (.imm 8)]) (.block [movR .r3 .r2]))

/-- The group's blocks (at `r1`) to the tail buffer. -/
def copyIn : Prog isa := .seq groupCount (.seq (.block [movR .r0 .r1, slotAddr .r12 tailSlot]) copyBlocks)

/-- The tail buffer back to the group's blocks. -/
def copyOut : Prog isa := .seq groupCount (.seq (.block [slotAddr .r0 tailSlot, movR .r12 .r1]) copyBlocks)

/-- The eight blocks of the tail buffer, with the data pointer, the blocks
left and the postwhitening's address in their slots meanwhile: the rounds
use every register, and store only through `sb`, which keeps the slots'
values public for the analysis of constant time (a store through another
pointer would forget them, so the copies keep these values in `r1`, `r2`
and `lr`). -/
def cryptSaved : Prog isa :=
  .seq (.block [stS dSlot .r1, stS nSlot .r2, stS endSlot .lr])
    (.seq crypt8 (.block [ldS .r1 dSlot, ldS .r2 nSlot, ldS .lr endSlot]))

/-- On to the next group, or none left (Z set). -/
def advance : Prog isa := .seq groupCount (.block [.dp .add .r1 .r1 (.imm 128), .subs .r2 .r2 (.reg .r3)])

/-- Eight blocks, or the last one to seven. -/
def group : Prog isa := .seq copyIn (.seq cryptSaved (.seq copyOut advance))

/-- The whole function: the table for 18 or 24 rounds, then the groups. -/
def ecb (dir : Dir) : Prog isa :=
  .seq (.block ([.ldrSp .r12 0] ++ saveRegs .r12 ++
      [movR sb .r12, movR .r12 .r0, .cmp .r1 (.imm 18), movR .r1 .r2, movR .r2 .r3]))
    (.seq (keys dir)
      (.seq (.block [.cmp .r2 (.imm 0)])
        (.seq (.ite .eq (.block []) (.loop group .ne)) (.block ([movR .r12 sb] ++ restoreRegs .r12)))))

end VG.Impl.Camellia.Arm
