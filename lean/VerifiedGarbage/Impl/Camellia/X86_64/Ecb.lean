import VerifiedGarbage.Impl.Camellia.X86_64.Layers
import VerifiedGarbage.Impl.Aes.X86_64.Ctr32

/-!
# Camellia ECB, bitsliced, on x86-64

`ecb dir(schedule = rdi, rounds = rsi, data = rdx, n = rcx, scratch = r8)`:
`vg_camellia_ecb_encrypt` and `vg_camellia_ecb_decrypt` with their working
space in the scratch buffer (`Layers.lean` has its layout), which the
artifact allocates on the stack.

* The scratch buffer moves to `r9` and `n` to `r8`, the callee-saved registers are saved, the masks set.
* The subkeys are bitsliced into the table at slot 96, in the order the
  rounds use them: the stored order for encryption; for decryption the
  order RFC 3713 §2.3.3 swaps them into, `kw3, kw4`, then the subkeys
  between `kw2` and `kw3` from the last back to the first, then `kw1,
  kw2`. Decryption then runs the same rounds as encryption.
* Each group of eight blocks (or the last one to seven, copied to the tail
  buffer and back): both halves bitsliced, the prewhitening, groups of six
  rounds with FL and FLINV between them, the postwhitening, and the halves
  stored back swapped.

Only `rdi` and `rsi` (pointers into the schedule and the table, and the
round key's entry), `rdx` (the data), `r8` (the blocks left), `r9` and
`r15` during the key setup, and the copies' pointers and counts hold public
values; no address and no branch depends on anything else.
-/

namespace VG.Impl.Camellia.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

/-! ## The subkeys -/

/-- Bitslice the subkey at `[rdi + d]` into the entry at `rsi`, and step
`rsi` to the next entry. -/
def keyOne (d : Nat) : List Instr :=
  [.mov (q 0) (.mem (at_ .rdi d))] ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++
  toBs ++ (List.range 8).map (fun j => .store (slotAt .rsi j) (q j)) ++
  [.alu .add .rsi (.imm 64)]

/-- `rsi := ` the table, and the address of the postwhitening's entry
(`8 g` entries on, `g` the number of groups of six rounds) to `endSlot`. -/
def tableSetup (g : Nat) : List Instr :=
  [movR .rsi sb, .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * keySlot))),
   movR t0 .rsi, .alu .add t0 (.imm (BitVec.ofNat 32 (512 * g))), st endSlot t0]

/-- Encryption's table, for `g` groups: the `8 g + 2` subkeys in order. -/
def encKeys (g : Nat) : Prog isa :=
  .seq (.block (tableSetup g ++ [.movImm64 t1 (BitVec.ofNat 64 (8 * g + 2))]))
    (.loop (.block (keyOne 0 ++ [.alu .add .rdi (.imm 8), .alu .sub t1 (.imm 1)])) .ne)

/-- Decryption's table, for `g` groups: `kw3, kw4` (words `8 g`, `8 g + 1`),
words `8 g - 1` down to 2, then `kw1, kw2`. -/
def decKeys (g : Nat) : Prog isa :=
  .seq (.block (tableSetup g ++ [.alu .add .rdi (.imm (BitVec.ofNat 32 (64 * g)))] ++
      keyOne 0 ++ keyOne 8 ++ [.alu .sub .rdi (.imm 8), .movImm64 t1 (BitVec.ofNat 64 (8 * g - 2))]))
    (.seq (.loop (.block (keyOne 0 ++ [.alu .sub .rdi (.imm 8), .alu .sub t1 (.imm 1)])) .ne)
      (.block ([.alu .sub .rdi (.imm 8)] ++ keyOne 0 ++ keyOne 8)))

def keys (dir : Dir) (g : Nat) : Prog isa :=
  match dir with | .encrypt => encKeys g | .decrypt => decKeys g

/-! ## Eight blocks -/

/-- Load half `h` (0 for `D1`, 1 for `D2`) of the eight blocks at `rdx`. -/
def loadWords (h : Nat) : List Instr := (List.range 8).map fun b => .mov (q b) (.mem (at_ .rdx (16 * b + 8 * h)))

/-- Store the eight words to half `h` of the blocks at `rdx`. -/
def storeWords (h : Nat) : List Instr := (List.range 8).map fun b => .store (at_ .rdx (16 * b + 8 * h)) (q b)

/-- The prewhitening, after `D1` is bitsliced into the state: `D1 ^= kw1`
into the state and its slots, `D2 ^= kw2` in its slots. -/
def whiten : List Instr :=
  keyXor 0 ++ storeHalf d1Slot ++
  ((List.range 8).flatMap fun j => [movS t0 (d2Slot + j), .alu .xor t0 (.mem (keyAt (8 + j))), st (d2Slot + j) t0])

/-- Bitslice both halves, `D2` to its slots and `D1` into the state, and
whiten them with the first two entries; `kp` is left at the first round's. -/
def head : List Instr :=
  loadWords 1 ++ toBs ++ storeHalf d2Slot ++ loadWords 0 ++ toBs ++
  [movR kp sb, .alu .add kp (.imm (BitVec.ofNat 32 (8 * keySlot)))] ++ whiten ++
  [.alu .add kp (.imm 128)]

/-- Two rounds: `D2 ^= F(D1, k)`, `D1 ^= F(D2, k')`, with the state holding
`D1` before and after; loops until `kp` reaches `rdi`. -/
def pairBody : List Instr :=
  round 0 d2Slot ++ round 8 d1Slot ++ [.alu .add kp (.imm 128), .alu .cmp kp (.reg .rdi)]

/-- Six rounds, then FL and FLINV unless they were the last; loops until
`kp` is at the postwhitening's entry. -/
def groupBody : Prog isa :=
  .seq (.block [movR .rdi kp, .alu .add .rdi (.imm 384)])
    (.seq (.loop (.block pairBody) .ne)
      (.seq (.block [.alu .cmp kp (.mem (slotAt sb endSlot))])
        (.seq (.ite .ne (.block flLayer) (.block []))
          (.block [.alu .cmp kp (.mem (slotAt sb endSlot))]))))

/-- The postwhitening, and the halves back to the blocks, swapped: `D2`
to the left halves, `D1` to the right. -/
def tail : List Instr :=
  keyXor 8 ++ fromBs ++ storeWords 1 ++ loadHalf d2Slot ++ keyXor 0 ++ fromBs ++ storeWords 0

/-- The eight blocks at `rdx`, in place. -/
def crypt8 : Prog isa := .seq (.block head) (.seq (.loop groupBody .ne) (.block tail))

/-! ## The groups -/

/-- The tail buffer's address, in `r`. -/
def tailAddr (r : Reg) : List Instr := [movR r sb, .alu .add r (.imm (BitVec.ofNat 32 (8 * tailSlot)))]

/-- Copy `rcx` blocks from `rax` to `rbx` (through `rbp`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.mov .rbp (.mem (at_ .rax 0)), .store (at_ .rbx 0) .rbp,
      .mov .rbp (.mem (at_ .rax 8)), .store (at_ .rbx 8) .rbp,
      .alu .add .rax (.imm 16), .alu .add .rbx (.imm 16), .alu .sub .rcx (.imm 1)]) .ne

/-- The last `r8 < 8` blocks to the tail buffer, which `rdx` then points to. -/
def copyIn : Prog isa :=
  .seq (.block ([st dataSlot .rdx, movR .rax .rdx] ++ tailAddr .rbx ++ [movR .rcx .r8]))
    (.seq copyBlocks (.block (tailAddr .rdx)))

/-- And back to the data. -/
def copyOut : Prog isa :=
  .seq (.block (tailAddr .rax ++ [movS .rbx dataSlot, movR .rcx .r8]))
    (.seq copyBlocks (.block [movS .rdx dataSlot]))

/-- Eight blocks, or the last one to seven (and none left: ZF set). -/
def group : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 8)])
    (.seq (.ite .b copyIn (.block []))
      (.seq crypt8
        (.seq (.block [.alu .cmp .r8 (.imm 8)])
          (.ite .b (.seq copyOut (.block [.alu .sub .r8 (.reg .r8)]))
            (.block [.alu .add .rdx (.imm 128), .alu .sub .r8 (.imm 8)])))))

/-- The whole function: the table for 18 or 24 rounds, then the groups. -/
def ecb (dir : Dir) : Prog isa :=
  .seq (.block ([movR .r9 .r8, movR .r8 .rcx] ++ saveRegs ++ setMasks layerMasks ++ [.alu .cmp .rsi (.imm 18)]))
    (.seq (.ite .e (keys dir 3) (keys dir 4))
      (.seq (.block [.alu .test .r8 (.reg .r8)])
        (.seq (.ite .e (.block []) (.loop group .ne)) (.block restoreRegs))))

end VG.Impl.Camellia.X86_64
