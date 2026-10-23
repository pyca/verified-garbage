module

public import VerifiedGarbage.Impl.Rc2.PPC64LE.Lookup
public import VerifiedGarbage.Spec.Rc2

/-! # RC2 block encryption and decryption on PPC64LE

`vg_rc2_{en,de}crypt_block(schedule = r3, data = r4, scratch = r5)`. The
four words are kept zero-extended in `r6`–`r9`. A mix computes `a & b` and
`c & ~a` (as `c XOR (a & c)`) from the neighbouring words, adds them and the
key word, masks the sum to 16 bits and rotates it with two shifts. A key
word at a public index is read with `lwz` at its offset (offset 124 and a
shift for the last), and the sum's high bits are discarded. A mash looks up
the key word at the secret index by a scan of the schedule (`keyLookup`).
Only volatile registers are used, and no stack: the working space is not
used.
-/

@[expose] public section

namespace VG.Impl.Rc2.PPC64LE

open VG.PPC64LE

def wordReg (i : Nat) : Reg := #[Reg.r6, .r7, .r8, .r9][i % 4]!

/-- The block at `r4`, a doubleword, into the four words. -/
def blockLoad : List Instr :=
  [.load .d .r11 .r4 0, .lsl .r6 .r11 48, .lsr .d .r6 .r6 48, .lsl .r7 .r11 32, .lsr .d .r7 .r7 48,
   .lsl .r8 .r11 16, .lsr .d .r8 .r8 48, .lsr .d .r9 .r11 48]

/-- The four words to the block at `r4`, a doubleword. -/
def blockStore : List Instr :=
  [.lsl .r11 .r7 16, .logic .or .r11 .r11 .r6, .lsl .r12 .r8 32, .logic .or .r11 .r11 .r12,
   .lsl .r12 .r9 48, .logic .or .r11 .r11 .r12, .store .d .r11 .r4 0]

/-- Key word `j` (and, but for `j = 63`, the next one above it) into `r12`. -/
def loadKey (j : Nat) : List Instr :=
  if j < 63 then [.load .w .r12 .r3 (2 * j)] else [.load .w .r12 .r3 124, .lsr .w .r12 .r12 16]

/-- Rotate the (zero-extended) word in `r` left by `s` bits, through `r0`. -/
def rotate16 (r : Reg) (s : Nat) : List Instr :=
  [.lsl .r0 r s, .lsr .d r r (16 - s), .logic .or r r .r0] ++ mask r 16

/-- `a & b` into `r10`, `c & ~a` into `r11` (`a`, `b`, `c` the words before
`i`), and key word `j` into `r12`. -/
def mixInputs (j i : Nat) : List Instr :=
  ([.logic .and .r10 (wordReg (i + 3)) (wordReg (i + 2)),
    .logic .and .r11 (wordReg (i + 3)) (wordReg (i + 1)),
    .logic .xor .r11 (wordReg (i + 1)) .r11] : List Instr) ++ loadKey j

def addInputs (r : Reg) : List Instr :=
  ([.add r r .r12, .add r r .r10, .add r r .r11] : List Instr) ++ mask r 16

def subInputs (r : Reg) : List Instr :=
  ([.sub r r .r12, .sub r r .r10, .sub r r .r11] : List Instr) ++ mask r 16

def mix (j i : Nat) : List Instr :=
  mixInputs j i ++ addInputs (wordReg i) ++ rotate16 (wordReg i) (Spec.Rc2.rotation i)

def reverseMix (j i : Nat) : List Instr :=
  rotate16 (wordReg i) (16 - Spec.Rc2.rotation i) ++ mixInputs j i ++ subInputs (wordReg i)

/-- `q := 2 (w & 63)` for the word `w` before `i`. -/
def mashIndex (i : Nat) : List Instr := [.lsl .r10 (wordReg (i + 3)) 58, .lsr .d .r10 .r10 57]

def adjust (sub : Bool) (r : Reg) : List Instr :=
  [if sub then .sub r r .r11 else .add r r .r11] ++ mask r 16

def mash (direction : Spec.Rc2.Direction) (i : Nat) : Prog isa :=
  .seq (.block (mashIndex i)) (.seq keyLookup (.block (adjust (direction == .decrypt) (wordReg i))))

/-- The order of the words in a round. -/
def order (direction : Spec.Rc2.Direction) : List Nat :=
  match direction with
  | .encrypt => List.range 4
  | .decrypt => [3, 2, 1, 0]

def mashRound (direction : Spec.Rc2.Direction) : Prog isa :=
  (order direction).foldr (fun i rest => .seq (mash direction i) rest) (.block [])

def mixRound (direction : Spec.Rc2.Direction) (j : Nat) : List Instr :=
  match direction with
  | .encrypt => (List.range 4).flatMap (fun i => mix (4 * j + i) i)
  | .decrypt => [3, 2, 1, 0].flatMap (fun i => reverseMix (4 * (15 - j) + i) i)

def round (direction : Spec.Rc2.Direction) (j : Nat) : Prog isa :=
  .seq (.block (mixRound direction j)) (if j = 4 ∨ j = 10 then mashRound direction else .block [])

def rounds (direction : Spec.Rc2.Direction) : Prog isa :=
  (List.range 16).foldr (fun j rest => .seq (round direction j) rest) (.block [])

def blockCode (direction : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block blockLoad) (.seq (rounds direction) (.block blockStore))

def encryptBlock : Prog isa := blockCode .encrypt
def decryptBlock : Prog isa := blockCode .decrypt

end VG.Impl.Rc2.PPC64LE
