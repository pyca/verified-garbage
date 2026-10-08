import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Impl.Idea.Key

/-!
# IDEA on baseline x86-64

## ⊙ without branches

`mulCode` computes `rdx := rax ⊙ rdx` on the low 16 bits of each, using
only `rax` and `rdx`: each operand `x` becomes `((x - 1) & 0xffff) + 1`, its
residue in `1 … 2¹⁶` (0 stands for 2¹⁶); `mul` (whose timing does not depend
on its operands) gives the product `p ≤ 2³²`; and since `2¹⁶ ≡ -1`,
`p ≡ lo - hi` modulo 2¹⁶ + 1 for `lo = p & 0xffff`, `hi = p >> 16`, which
the code corrects to `0 … 2¹⁶` by adding `2¹⁶ + 1` times the sign bit of the
64-bit difference: no branch, no division.

## `vg_idea_expand_key` (`key = rdi`, `schedule = rsi`)

Every subkey is a 16-bit window of the key rotated left by a multiple of 25
bits, so each quadword of the schedule (four subkeys) is a fixed bit
permutation of the key's two quadwords: `expandWord q` assembles quadword
`q` from the key in memory, a group of bits with the same rotation at a
time (`mov`, `ror`, `and` with a mask, `xor`), and stores it.

## `vg_idea_invert_key` (`schedule = rdi`, `inverse = rsi`)

Each decryption subkey is a copy, the negation or the ⊙-inverse of an
encryption subkey (`invOp`). The inverse of `a` is `a ^ (2¹⁶ - 1)`: fifteen
iterations of `t := (t ⊙ t) ⊙ a` from `t = a`, a loop with a public count.

## `vg_idea_ecb` (`schedule = rdi`, `data = rsi`, `n = rdx`, scratch `rcx`)

Each block is loaded into `r8`–`r11` (one 16-bit word each, a byte at a time), run through
the eight rounds (unrolled) and the output transformation, and stored;
`rbx` holds a round's `t₀`, and `rbp` counts the blocks left. `rbx` and
`rbp` are saved in the scratch buffer (two quadwords, on the stack) and
restored. Subkeys are read with 64-bit loads at their own offsets, of which
the code uses the low 16 bits (or, for the last three, shifts).

The only branches are on `n` and the loop counts.
-/

namespace VG.Impl.Idea.X86_64

open VG.X86_64 VG.Impl.Idea

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-! ## ⊙ -/

/-- `rdx := rax ⊙ rdx` (low 16 bits of each; the result zero-extended),
clobbering `rax`. -/
def mulCode : List Instr := [
  .alu .sub .rax (.imm 1), .alu .and .rax (.imm 0xffff), .alu .add .rax (.imm 1),
  .alu .sub .rdx (.imm 1), .alu .and .rdx (.imm 0xffff), .alu .add .rdx (.imm 1),
  .mul .rdx,
  .mov .rdx (.reg .rax), .alu .and .rdx (.imm 0xffff), .shift .shr .rax 16,
  .alu .sub .rdx (.reg .rax),
  .mov .rax (.reg .rdx), .shift .shr .rax 63,
  .alu .add .rdx (.reg .rax), .shift .shl .rax 16, .alu .add .rdx (.reg .rax),
  .alu .and .rdx (.imm 0xffff)]

/-! ## Key expansion -/

/-- The source (quadword, bit) of bit `p` of schedule quadword `q`. -/
def expandSrc (q p : Nat) : Nat × Nat := keyLoc (keyBit (4 * q + p / 16) (p % 16))

/-- The rotation right that moves source bit `t` to `p`. -/
def rot (t p : Nat) : Nat := (t + 64 - p) % 64

/-- The groups of bits of quadword `q` with the same source quadword and
rotation: `(j, rotation, mask)`, in order of first bit. -/
def expandGroups (q : Nat) : List (Nat × Nat × Nat) :=
  (List.range 64).foldl (fun gs p =>
    let (j, t) := expandSrc q p
    let r := rot t p
    if gs.any (fun g => g.1 = j ∧ g.2.1 = r) then
      gs.map fun g => if g.1 = j ∧ g.2.1 = r then (g.1, g.2.1, g.2.2 ||| 2 ^ p) else g
    else gs ++ [(j, r, 2 ^ p)]) []

/-- One group into `rdx`, masked, then into `rax` (the first by `mov`). -/
def groupCode (first : Bool) (g : Nat × Nat × Nat) : List Instr :=
  [.mov .rdx (.mem (at_ .rdi (8 * g.1)))] ++
  (if g.2.1 = 0 then [] else [.shift .ror .rdx g.2.1]) ++
  [.movImm64 .rcx (BitVec.ofNat 64 g.2.2), .alu .and .rdx (.reg .rcx),
   if first then .mov .rax (.reg .rdx) else .alu .xor .rax (.reg .rdx)]

/-- Schedule quadword `q` into `rax`. -/
def expandWord (q : Nat) : List Instr :=
  (expandGroups q).zipIdx.flatMap fun (g, k) => groupCode (k = 0) g

def expandKey : Prog isa :=
  .block ((List.range 13).flatMap fun q => expandWord q ++ [.store (at_ .rsi (8 * q)) .rax])

/-! ## Inversion -/

inductive Op | copy | neg | inv
  deriving DecidableEq, Repr

/-- Decryption subkey `n`: the operation, and the encryption subkey it
applies to (`Spec.Idea.invertKey`). -/
def invOp (n : Nat) : Op × Nat :=
  let r := n / 6
  let e := 6 * (8 - r)
  let ends := r = 0 ∨ r = 8
  match n % 6 with
  | 0 => (.inv, e)
  | 1 => (.neg, if ends then e + 1 else e + 2)
  | 2 => (.neg, if ends then e + 2 else e + 1)
  | 3 => (.inv, e + 3)
  | 4 => (.copy, 6 * (7 - r) + 4)
  | _ => (.copy, 6 * (7 - r) + 5)

/-- Encryption subkey `k` into the low 16 bits of `r` (above them, other
bits): a load at its offset, or, for the last three, at 96 and a shift. -/
def loadKey (r : Reg) (k : Nat) : List Instr :=
  if k ≤ 48 then [.mov r (.mem (at_ .rdi (2 * k)))]
  else [.mov r (.mem (at_ .rdi 96)), .shift .shr r (16 * (k - 48))]

/-- `t := (t ⊙ t) ⊙ a` with `t = r9`, `a = r8`, and the count in `rcx`. -/
def invStep : List Instr :=
  [.mov .rax (.reg .r9), .mov .rdx (.reg .r9)] ++ mulCode ++
  [.mov .rax (.reg .rdx), .mov .rdx (.reg .r8)] ++ mulCode ++
  [.mov .r9 (.reg .rdx), .alu .sub .rcx (.imm 1)]

/-- Decryption subkey `n` into `rdx`, zero-extended. -/
def invWord (n : Nat) : Prog isa :=
  match invOp n with
  | (.copy, k) => .block (loadKey .rdx k ++ [.alu .and .rdx (.imm 0xffff)])
  | (.neg, k) => .block (loadKey .r11 k ++
      [.mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .r11), .alu .and .rdx (.imm 0xffff)])
  | (.inv, k) => .seq (.block (loadKey .r8 k ++ [.mov .r9 (.reg .r8), .mov32 .rcx (.imm 15)]))
      (.seq (.loop (.block invStep) .ne) (.block [.mov .rdx (.reg .r9)]))

/-- Decryption subkey `n` into its place in `r10`. -/
def invPlace (n : Nat) : List Instr :=
  if n % 4 = 0 then [.mov .r10 (.reg .rdx)]
  else [.shift .shl .rdx (16 * (n % 4)), .alu .or .r10 (.reg .rdx)]

/-- Decryption subkeys `4q … 4q + 3`, stored. -/
def invQuad (q : Nat) : Prog isa :=
  (List.range 4).foldr (fun i rest => .seq (invWord (4 * q + i)) (.seq (.block (invPlace (4 * q + i))) rest))
    (.block [.store (at_ .rsi (8 * q)) .r10])

def invertKey : Prog isa :=
  (List.range 13).foldr (fun q rest => .seq (invQuad q) rest) (.block [])

/-! ## ECB -/

/-- `r := r ⊙ subkey` (at offset `d` from `rdi`). -/
def mulKey (r : Reg) (d : Nat) : List Instr :=
  [.mov .rax (.reg r), .mov .rdx (.mem (at_ .rdi d))] ++ mulCode ++ [.mov r (.reg .rdx)]

/-- `r := r ⊞ subkey` (at offset `d` from `rdi`), zero-extended. -/
def addKey (r : Reg) (d : Nat) : List Instr :=
  [.mov .rdx (.mem (at_ .rdi d)), .alu .add r (.reg .rdx), .alu .and r (.imm 0xffff)]

/-- Round `j` (0–7), its subkeys at `rdi + 12 j`, on `r8`–`r11`. -/
def round (j : Nat) : List Instr :=
  let o := 12 * j
  mulKey .r8 o ++ mulKey .r11 (o + 6) ++ addKey .r9 (o + 2) ++ addKey .r10 (o + 4) ++
  [.mov .rax (.reg .r8), .alu .xor .rax (.reg .r10), .mov .rdx (.mem (at_ .rdi (o + 8)))] ++
  mulCode ++
  [.mov .rbx (.reg .rdx),
   .mov .rax (.reg .r9), .alu .xor .rax (.reg .r11), .alu .add .rax (.reg .rbx),
   .mov .rdx (.mem (at_ .rdi (o + 10)))] ++
  mulCode ++
  [.alu .add .rbx (.reg .rdx), .alu .and .rbx (.imm 0xffff),
   .alu .xor .r8 (.reg .rdx), .alu .xor .r10 (.reg .rdx),
   .alu .xor .r9 (.reg .rbx), .alu .xor .r11 (.reg .rbx),
   .mov .rax (.reg .r9), .mov .r9 (.reg .r10), .mov .r10 (.reg .rax)]

/-- Word `k` of the block at `rsi` into `r`, big-endian (through `rax`). -/
def loadWord (r : Reg) (k : Nat) : List Instr :=
  [.movzx8 r (at_ .rsi (2 * k)), .shift .shl r 8, .movzx8 .rax (at_ .rsi (2 * k + 1)),
   .alu .or r (.reg .rax)]

/-- The block at `rsi` into `r8`–`r11`, one big-endian word each. -/
def load : List Instr :=
  loadWord .r8 0 ++ loadWord .r9 1 ++ loadWord .r10 2 ++ loadWord .r11 3

/-- The output transformation (subkeys 48–51 in the quadword at 96), with
the middle words exchanged back: `r9` gets `X₂ ⊞ Z₅₁`, `r10` `X₃ ⊞ Z₅₀`. -/
def output : List Instr :=
  mulKey .r8 96 ++
  [.mov .rax (.reg .r11), .mov .rdx (.mem (at_ .rdi 96)), .shift .shr .rdx 48] ++ mulCode ++
  [.mov .r11 (.reg .rdx),
   .mov .rdx (.mem (at_ .rdi 96)), .shift .shr .rdx 16, .alu .add .r10 (.reg .rdx),
   .alu .and .r10 (.imm 0xffff),
   .mov .rdx (.mem (at_ .rdi 96)), .shift .shr .rdx 32, .alu .add .r9 (.reg .rdx),
   .alu .and .r9 (.imm 0xffff)]

/-- The word in `r` to word `k` of the block at `rsi`, big-endian (through `rax`). -/
def storeWord (r : Reg) (k : Nat) : List Instr :=
  [.store8 (at_ .rsi (2 * k + 1)) r, .mov .rax (.reg r), .shift .shr .rax 8,
   .store8 (at_ .rsi (2 * k)) .rax]

/-- `r8, r10, r9, r11` (Y₁ … Y₄) to the block at `rsi`. -/
def store : List Instr :=
  storeWord .r8 0 ++ storeWord .r10 1 ++ storeWord .r9 2 ++ storeWord .r11 3

def cryptBlock : List Instr :=
  load ++ (List.range 8).flatMap round ++ output ++ store

def ecb : Prog isa :=
  .seq (.block [.alu .test .rdx (.reg .rdx)])
    (.ite .e (.block [])
      (.seq (.block [.store (at_ .rcx 0) .rbx, .store (at_ .rcx 8) .rbp, .mov .rbp (.reg .rdx)])
        (.seq (.loop (.block (cryptBlock ++ [.alu .add .rsi (.imm 8), .alu .sub .rbp (.imm 1)])) .ne)
          (.block [.mov .rbx (.mem (at_ .rcx 0)), .mov .rbp (.mem (at_ .rcx 8))]))))

end VG.Impl.Idea.X86_64
