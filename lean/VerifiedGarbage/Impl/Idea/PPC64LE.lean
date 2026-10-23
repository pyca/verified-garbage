module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Idea.Key

/-!
# IDEA on PPC64LE

The same algorithms as on x86-64 (`Impl/Idea/X86_64.lean`), with `r0`
holding the mask `0xffff` and `r11`, `r12` ⊙'s working registers.

## ⊙ without branches

`mulCode` computes `r12 := r11 ⊙ r12` on the low 16 bits of each, using
only `r11` and `r12`: each operand `x` becomes `((x - 1) & 0xffff) + 1`, its
residue in `1 … 2¹⁶` (0 stands for 2¹⁶); `mulld` (whose timing does not
depend on its operands; see `TCB/PPC64LE/Isa.lean`) gives the product
`p ≤ 2³²`; and since `2¹⁶ ≡ -1`, `p ≡ lo - hi` modulo 2¹⁶ + 1 for
`lo = p & 0xffff`, `hi = p >> 16`, which the code corrects to `0 … 2¹⁶` by
adding `2¹⁶ + 1` times the sign bit of the 64-bit difference: no branch,
no division.

## `vg_idea_expand_key` (`key = r3`, `schedule = r4`)

Every subkey is a 16-bit window of the key rotated left by a multiple of 25
bits, so each doubleword of the schedule (four subkeys) is a fixed bit
permutation of the key's two doublewords: `expandWord q` assembles
doubleword `q` in `r10` from the key in memory, a group of bits with the
same rotation at a time (`ld`, `rotrdi`, `and` with a mask built in `r11`,
`xor`), and it is stored.

## `vg_idea_invert_key` (`schedule = r3`, `inverse = r4`)

Each decryption subkey is a copy, the negation or the ⊙-inverse of an
encryption subkey (`invOp`). The inverse of `a` (`r6`) is `a ^ (2¹⁶ - 1)`:
fifteen iterations of `t := (t ⊙ t) ⊙ a` from `t = a` (`r7`), a loop with a
public count (`r5`). Four subkeys are assembled in `r8` and stored.

## `vg_idea_ecb` (`schedule = r3`, `data = r4`, `n = r5`)

Each block is loaded into `r6`–`r9` (one 16-bit word each, a byte at a
time), run through the eight rounds (unrolled) and the output
transformation, and stored; `r10` holds a round's `t₀`, and `r5` counts the
blocks left. Subkeys are read with 32-bit loads at their own offsets, of
which the code uses the low 16 bits (the last, with a load at 100, shifted).

Only volatile registers are used, and no stack. The only branches are on
`n` and the loop counts.
-/

@[expose] public section

namespace VG.Impl.Idea.PPC64LE

open VG.PPC64LE VG.Impl.Idea

/-! ## ⊙ -/

/-- `r12 := r11 ⊙ r12` (low 16 bits of each; the result zero-extended),
clobbering `r11`, with the mask `0xffff` in `r0`. -/
def mulCode : List Instr := [
  .subi .r11 .r11 1, .logic .and .r11 .r11 .r0, .addi .r11 .r11 1,
  .subi .r12 .r12 1, .logic .and .r12 .r12 .r0, .addi .r12 .r12 1,
  .mul .r11 .r11 .r12,
  .logic .and .r12 .r11 .r0, .lsr .d .r11 .r11 16,
  .sub .r12 .r12 .r11,
  .lsr .d .r11 .r12 63,
  .add .r12 .r12 .r11, .lsl .r11 .r11 16, .add .r12 .r12 .r11,
  .logic .and .r12 .r12 .r0]

/-- `r0 := 0xffff`. -/
def setMask : List Instr := [.li .r0 0, .ori .r0 .r0 0xffff]

/-! ## Key expansion -/

/-- `d := v` for a 64-bit constant: the high word with `lis` and `ori`,
shifted up by `sldi`, then the low word with `oris` and `ori`. -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
   .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

/-- One group into `r12`, masked (by `r11`) into `r10` (the first) or into
`r12` and then XORed into `r10`. -/
def groupCode (first : Bool) (g : Nat × Nat × Nat) : List Instr :=
  ([.load .d .r12 .r3 (8 * g.1)] : List Instr) ++
  (if g.2.1 = 0 then [] else [.rotr .d .r12 .r12 g.2.1]) ++
  movImm64 .r11 (BitVec.ofNat 64 g.2.2) ++
  (if first then [.logic .and .r10 .r12 .r11]
   else [.logic .and .r12 .r12 .r11, .logic .xor .r10 .r10 .r12])

/-- Schedule doubleword `q` into `r10`. -/
def expandWord (q : Nat) : List Instr :=
  (expandGroups q).zipIdx.flatMap fun (g, k) => groupCode (k = 0) g

def expandKey : Prog isa :=
  .block ((List.range 13).flatMap fun q => expandWord q ++ ([.store .d .r10 .r4 (8 * q)] : List Instr))

/-! ## Inversion -/

/-- Encryption subkey `k` into the low 16 bits of `r` (above them, other
bits): a 32-bit load at its offset, or, for the last, at 100 and a shift. -/
def loadKey (r : Reg) (k : Nat) : List Instr :=
  if k ≤ 50 then [.load .w r .r3 (2 * k)] else [.load .w r .r3 100, .lsr .d r r 16]

/-- `r := r` (`or r, s, s`). -/
def mov (d s : Reg) : Instr := .logic .or d s s

/-- `t := (t ⊙ t) ⊙ a` with `t = r7`, `a = r6`, and the count in `r5`. -/
def invStep : List Instr :=
  ([mov .r11 .r7, mov .r12 .r7] : List Instr) ++ mulCode ++
  ([mov .r11 .r12, mov .r12 .r6] : List Instr) ++ mulCode ++
  ([mov .r7 .r12, .subi .r5 .r5 1] : List Instr)

/-- Decryption subkey `n` into `r12`, zero-extended. -/
def invWord (n : Nat) : Prog isa :=
  match invOp n with
  | (.copy, k) => .block (loadKey .r12 k ++ ([.logic .and .r12 .r12 .r0] : List Instr))
  | (.neg, k) => .block (loadKey .r9 k ++
      ([.li .r12 0, .sub .r12 .r12 .r9, .logic .and .r12 .r12 .r0] : List Instr))
  | (.inv, k) => .seq (.block (loadKey .r6 k ++ ([mov .r7 .r6, .li .r5 15] : List Instr)))
      (.seq (.loop (.block invStep) (.nonzero .d .r5)) (.block [mov .r12 .r7]))

/-- Decryption subkey `n` into its place in `r8`. -/
def invPlace (n : Nat) : List Instr :=
  if n % 4 = 0 then [mov .r8 .r12]
  else [.lsl .r12 .r12 (16 * (n % 4)), .logic .or .r8 .r8 .r12]

/-- Decryption subkeys `4q … 4q + 3`, stored. -/
def invQuad (q : Nat) : Prog isa :=
  (List.range 4).foldr (fun i rest => .seq (invWord (4 * q + i)) (.seq (.block (invPlace (4 * q + i))) rest))
    (.block [.store .d .r8 .r4 (8 * q)])

def invertKey : Prog isa :=
  .seq (.block setMask) ((List.range 13).foldr (fun q rest => .seq (invQuad q) rest) (.block []))

/-! ## ECB -/

/-- `r := r ⊙ subkey` (the 32-bit word at offset `d` from `r3`). -/
def mulKey (r : Reg) (d : Nat) : List Instr :=
  ([mov .r11 r, .load .w .r12 .r3 d] : List Instr) ++ mulCode ++ ([mov r .r12] : List Instr)

/-- `r := r ⊞ subkey` (the 32-bit word at offset `d` from `r3`), zero-extended. -/
def addKey (r : Reg) (d : Nat) : List Instr :=
  [.load .w .r12 .r3 d, .add r r .r12, .logic .and r r .r0]

/-- Round `j` (0–7), its subkeys at `r3 + 12 j`, on `r6`–`r9`. -/
def round (j : Nat) : List Instr :=
  let o := 12 * j
  mulKey .r6 o ++ mulKey .r9 (o + 6) ++ addKey .r7 (o + 2) ++ addKey .r8 (o + 4) ++
  ([.logic .xor .r11 .r6 .r8, .load .w .r12 .r3 (o + 8)] : List Instr) ++
  mulCode ++
  ([mov .r10 .r12, .logic .xor .r11 .r7 .r9, .add .r11 .r11 .r10,
   .load .w .r12 .r3 (o + 10)] : List Instr) ++
  mulCode ++
  ([.add .r10 .r10 .r12, .logic .and .r10 .r10 .r0,
   .logic .xor .r6 .r6 .r12, .logic .xor .r8 .r8 .r12,
   .logic .xor .r7 .r7 .r10, .logic .xor .r9 .r9 .r10,
   mov .r11 .r7, mov .r7 .r8, mov .r8 .r11] : List Instr)

/-- Word `k` of the block at `r4` into `r`, big-endian (through `r11`). -/
def loadWord (r : Reg) (k : Nat) : List Instr :=
  [.lbz r .r4 (2 * k), .lsl r r 8, .lbz .r11 .r4 (2 * k + 1), .logic .or r r .r11]

/-- The block at `r4` into `r6`–`r9`, one big-endian word each. -/
def load : List Instr :=
  loadWord .r6 0 ++ loadWord .r7 1 ++ loadWord .r8 2 ++ loadWord .r9 3

/-- The output transformation (subkeys 48–51), with the middle words
exchanged back: `r8` gets `X₃ ⊞ Z₄₉`, `r7` `X₂ ⊞ Z₅₀`. -/
def output : List Instr :=
  mulKey .r6 96 ++
  ([mov .r11 .r9, .load .w .r12 .r3 100, .lsr .d .r12 .r12 16] : List Instr) ++ mulCode ++
  ([mov .r9 .r12] : List Instr) ++ addKey .r8 98 ++ addKey .r7 100

/-- The word in `r` to word `k` of the block at `r4`, big-endian (through `r11`). -/
def storeWord (r : Reg) (k : Nat) : List Instr :=
  [.stb r .r4 (2 * k + 1), .lsr .d .r11 r 8, .stb .r11 .r4 (2 * k)]

/-- `r6, r8, r7, r9` (Y₁ … Y₄) to the block at `r4`. -/
def store : List Instr :=
  storeWord .r6 0 ++ storeWord .r8 1 ++ storeWord .r7 2 ++ storeWord .r9 3

def cryptBlock : List Instr :=
  load ++ (List.range 8).flatMap round ++ output ++ store

def ecb : Prog isa :=
  .seq (.block setMask)
    (.ite (.zero .d .r5) (.block [])
      (.loop (.block (cryptBlock ++ ([.addi .r4 .r4 8, .subi .r5 .r5 1] : List Instr)))
        (.nonzero .d .r5)))

end VG.Impl.Idea.PPC64LE
