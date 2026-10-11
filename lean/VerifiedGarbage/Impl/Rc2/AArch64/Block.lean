module

public import VerifiedGarbage.Impl.Rc2.AArch64.Lookup

/-! # RC2 block encryption and decryption on baseline AArch64

The four words are kept zero-extended in `x19`–`x22`, and `x9` holds
`0xffff` for masking them. A mix computes `a & b` and `c & ~a` (`bic`) from
the neighbouring words in parallel, adds them and the key word, masks the
sum and rotates it with two shifts: seven instructions in sequence from the
word that the previous mix wrote.
-/

@[expose] public section

namespace VG.Impl.Rc2.AArch64

open VG.AArch64

def wordReg (i : Nat) : Reg := #[Reg.x19, .x20, .x21, .x22][i % 4]!

def blockSave : List Instr :=
  (List.range 4).map fun i => .str .x (wordReg i) .x2 (8 * i)

def blockRestore : List Instr :=
  (List.range 4).map fun i => .ldr .x (wordReg i) .x2 (8 * i)

def unpackWord (i : Nat) : List Instr :=
  [rr (wordReg i) .x8, .lsr .x (wordReg i) (wordReg i) (16 * i)] ++
    mask (wordReg i) 16

def blockLoad : List Instr :=
  [imm .x9 65535, .ldr .x .x8 .x1 0] ++ (List.range 4).flatMap unpackWord

/-- Rotate the (zero-extended) word in `r` left by `s` bits. -/
def rotate16 (r : Reg) (s : Nat) : List Instr :=
  [.lsl .x .x8 r s, .lsr .x r r (16 - s), .logic .orr .x r r .x8, .logic .and .x r r .x9]

/-- `a & b` into `x6` and `c & ~a` into `x7` (`a`, `b`, `c` the words
before `i`), and the key word `j` into `x4`. -/
def mixInputs (j i : Nat) : List Instr :=
  ([.logic .and .x .x6 (wordReg (i + 3)) (wordReg (i + 2)),
   .bicRor .x .x7 (wordReg (i + 1)) (wordReg (i + 3)) 0] : List Instr) ++ loadKey j

def addInputs (r : Reg) : List Instr :=
  [.add .x r r .x4, .add .x r r .x6, .add .x r r .x7, .logic .and .x r r .x9]

def subInputs (r : Reg) : List Instr :=
  [.sub .x r r .x4, .sub .x r r .x6, .sub .x r r .x7, .logic .and .x r r .x9]

def adjust (sub : Bool) (r : Reg) : List Instr :=
  [if sub then .sub .x r r .x8 else .add .x r r .x8, .logic .and .x r r .x9]

def mix (j i : Nat) : List Instr :=
  mixInputs j i ++ addInputs (wordReg i) ++ rotate16 (wordReg i) (Spec.Rc2.rotation i)

def reverseMix (j i : Nat) : List Instr :=
  rotate16 (wordReg i) (16 - Spec.Rc2.rotation i) ++ mixInputs j i ++ subInputs (wordReg i)

def mash (direction : Spec.Rc2.Direction) (i : Nat) : List Instr :=
  [rr .x8 (wordReg (i + 3))] ++ keyLookup ++ adjust (direction == .decrypt) (wordReg i)

def round (direction : Spec.Rc2.Direction) (j : Nat) : List Instr :=
  match direction with
  | .encrypt => (List.range 4).flatMap (fun i => mix (4 * j + i) i) ++
      (if j = 4 ∨ j = 10 then (List.range 4).flatMap (mash .encrypt) else [])
  | .decrypt => [3, 2, 1, 0].flatMap (fun i => reverseMix (4 * (15 - j) + i) i) ++
      (if j = 4 ∨ j = 10 then [3, 2, 1, 0].flatMap (mash .decrypt) else [])

def packWord (i : Nat) : List Instr :=
  [.ror .x .x3 (wordReg i) (64 - 16 * i), .logic .orr .x .x8 .x8 .x3]

def blockStore : List Instr :=
  [rr .x8 (wordReg 0)] ++ [1, 2, 3].flatMap packWord ++ ([.str .x .x8 .x1 0] : List Instr)

def blockCode (direction : Spec.Rc2.Direction) : List Instr :=
  blockSave ++ blockLoad ++ (List.range 16).flatMap (round direction) ++ blockStore ++ blockRestore

def encryptBlock : Prog isa := .block (blockCode .encrypt)
def decryptBlock : Prog isa := .block (blockCode .decrypt)

end VG.Impl.Rc2.AArch64
