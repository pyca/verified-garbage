module

public import VerifiedGarbage.Impl.Aes.Arm.Linear

/-!
# Bitsliced AES on ARMv7, two blocks at a time

The round keys (`keyFront`), the cipher (`encrypt2`) and its inverse
(`decrypt2`) on two blocks in `q 0 … q 7`, word `c` of block `b` in
`q (2 c + b)`.

A round key is bitsliced once, its 16 bytes in both blocks' places: eight
words, in the form `j mod 4` of its round `j` (`Linear.lean`), one after
another in the scratch buffer up to the last, at byte `lastKey`. All but the
first have `{63}` added to every byte: ShiftRows and MixColumns take a state
of equal bytes to itself, so that stands for the constants of the S-boxes
(`Sbox.lean`), which the code leaves out, and of the inverse ones.

The rounds go from form to form, so four of them are the loops' bodies. The
numbers of rounds are 10, 12 and 14: a body can end after two rounds too. The
last round key of 10 or 14 rounds is in form 2, and the blocks' words are
taken to or from it by `sr2Words`, where the transpose is done.

During the rounds the pointer to the round keys is in slot `kpSlot`; the
registers the layers leave it are few. Decryption needs the first round key's
address too, in slot `fkSlot`. Only these pointers decide the branches.
-/

@[expose] public section

namespace VG.Impl.Aes.Arm

open VG.Arm

/-- The last round key's place in the scratch buffer, in bytes. -/
def lastKey : Nat := 672

/-! ## Slots -/

def kpSlot : Nat := 31
/-- The first round key's address. -/
def fkSlot : Nat := 47

/-! ## Round keys -/

/-- Word `c` of a round key. -/
def kw (c : Nat) : Reg := q (2 * c + 1)

/-- The round key at `r12`. -/
def keyLoad : List Instr := (List.range 4).map fun c => .ldr (kw c) .r12 (4 * c)

/-- `{63}` added to its bytes. -/
def key63 : List Instr :=
  imm32 t0 0x63636363 ++ (List.range 4).map fun c => eorR (kw c) (kw c) t0

/-- Row `r` moved `r` columns further: rows 2 and 3 two columns, rows 1 and
3 one. -/
def keyRot1 : List Instr :=
  ([0, 1] : List Nat).flatMap (fun c =>
    [eorR t0 (kw c) (kw (c + 2)), .mov t0 (lsrOp t0 16), .dp .eor (kw c) (kw c) (rorOp t0 16),
     .dp .eor (kw (c + 2)) (kw (c + 2)) (rorOp t0 16)]) ++
  imm32 t1 0xFF00FF00 ++
  ([eorR (q 0) (kw 0) (kw 3), andR (q 0) (q 0) t1] : List Instr) ++
  ([3, 2, 1] : List Nat).flatMap (fun c =>
    [eorR t0 (kw c) (kw (c - 1)), andR t0 t0 t1, eorR (kw c) (kw c) t0]) ++
  ([eorR (kw 0) (kw 0) (q 0)] : List Instr)

/-- Row `r` moved `2 r` columns further. -/
def keyRot2 : List Instr :=
  imm32 t1 0xFF00FF00 ++ ([0, 1] : List Nat).flatMap fun c =>
    [eorR t0 (kw c) (kw (c + 2)), andR t0 t0 t1, eorR (kw c) (kw c) t0, eorR (kw (c + 2)) (kw (c + 2)) t0]

/-- The words to slices, in both blocks' places: the index bits of slices 2
and 1 of the bits exchanged with those of the columns, after which a word has
two slices, in its even and its odd bits. -/
def keySpread : List Instr :=
  imm32 t1 (idxMask 2) ++ swapMove (kw 0) (kw 2) 4 ++ swapMove (kw 1) (kw 3) 4 ++
  imm32 t1 (idxMask 1) ++ swapMove (kw 0) (kw 1) 2 ++ swapMove (kw 2) (kw 3) 2 ++
  imm32 t1 (idxMask 0) ++ (List.range 4).flatMap fun n =>
    [andR (q (2 * n)) (kw n) t1, eorR (kw n) (kw n) (q (2 * n)),
     .dp .eor (q (2 * n)) (q (2 * n)) (rorOp (q (2 * n)) 31), .dp .eor (kw n) (kw n) (lsrOp (kw n) 1)]

/-- The slices to the round key at `kp`. -/
def keyStore : List Instr := (List.range 8).map fun j => .str (q j) kp (4 * j)

/-- Bitslice round key `j`, at `r12`, to `kp`; the low four bits of `lr` hold
`j + 1`. -/
def keyFront : Prog isa :=
  .seq (.block (keyLoad ++ ([.dp .and t0 .lr (.imm 15), .cmp t0 (.imm 1)] : List Instr)))
    (.seq (.ite .ne (.block key63) (.block []))
      (.seq (.block [.dp .and t0 .lr (.imm 1), .cmp t0 (.imm 0)])
        (.seq (.ite .eq (.block keyRot1) (.block []))
          (.seq (.block [.dp .sub t0 .lr (.imm 1), .dp .and t0 t0 (.imm 2), .cmp t0 (.imm 0)])
            (.seq (.ite .ne (.block keyRot2) (.block [])) (.block (keySpread ++ keyStore)))))))

/-! ## AddRoundKey -/

/-- `d j` := `s j` with the round key `off` bytes after `kp` added. -/
def addKey (off : Nat) (d s : Nat → Reg) : List Instr :=
  (List.range 8).flatMap fun j => [.ldr t0 kp (off + 4 * j), eorR (d j) (s j) t0]

def ldKp : List Instr := [ldS kp kpSlot]

/-- The round keys' pointer, and whether the last round key is `off` bytes
after it. -/
def testLast (off : Nat) : List Instr :=
  [ldS kp kpSlot, .dp .sub t0 kp (.reg sb), .cmp t0 (.imm (BitVec.ofNat 32 (lastKey - off)))]

/-! ## The cipher -/

/-- To slices, and the first round key. -/
def encStart : List Instr := ortho ++ ([stS kpSlot kp] : List Instr) ++ addKey 0 q q

/-- Round 1 of the four, and SubBytes of round 2. -/
def encTop : List Instr :=
  subBytes ++ mixColumns 1 ++ ldKp ++ addKey 32 q q ++ subBytes ++ testLast 64

/-- If round 2 is not the last, the rest of it, round 3, and SubBytes of round 4. -/
def encMid : List Instr :=
  mixColumns 2 ++ addKey 64 q q ++ subBytes ++ mixColumns 3 ++ ldKp ++ addKey 96 q q ++
  subBytes ++ testLast 128

/-- If round 4 is not the last, the rest of it, and on to the next four. -/
def encEnd : List Instr :=
  mixColumns 0 ++ addKey 128 q q ++ ([.dp .add kp kp (.imm 128), stS kpSlot kp] : List Instr)

/-- The last round key, as the second of the four or the fourth, and back to
blocks. -/
def encLast2 : List Instr := addKey 64 q p ++ ortho ++ sr2Words
def encLast4 : List Instr := addKey 128 q p ++ ortho

def encBody : Prog isa :=
  .seq (.block encTop) (.ite .eq (.block encLast2)
    (.seq (.block encMid) (.ite .eq (.block encLast4) (.block encEnd))))

/-- Encrypt the two blocks, with `kp` at the first round key. -/
def encrypt2 : Prog isa := .seq (.block encStart) (.loop encBody .ne)

/-! ## The inverse cipher -/

/-- Whether the number of rounds is 2 more than a multiple of 4. -/
def decTest : List Instr :=
  [.dp .sub t0 kp (.reg sb), .dp .and t0 t0 (.imm 64), .cmp t0 (.imm 0)]

/-- To slices, and the last round key. -/
def decStart : List Instr :=
  ortho ++ ([.dp .add kp sb (.imm (BitVec.ofNat 32 lastKey)), stS kpSlot kp] : List Instr) ++ addKey 0 q q

/-- Whether the number of round keys left is a multiple of 4. -/
def decHead : List Instr :=
  [ldS kp kpSlot, ldS t0 fkSlot, .dp .sub t0 kp (.reg t0), .dp .and t0 t0 (.imm 64), .cmp t0 (.imm 0)]

/-- The round keys' pointer two round keys back. -/
def kpBack : List Instr := [ldS kp kpSlot, .dp .sub kp kp (.imm 64), stS kpSlot kp]

/-- Two rounds, of forms 3 and 2. -/
def decHi : List Instr :=
  invSubBytes ++ kpBack ++ addKey 32 p p ++ invMixColumns 3 ++
  invSubBytes ++ ldKp ++ addKey 0 p p ++ invMixColumns 2

/-- A round of form 1, InvSubBytes of the next, and whether its round key is
the first. -/
def decLo : List Instr :=
  invSubBytes ++ kpBack ++ addKey 32 p p ++ invMixColumns 1 ++
  invSubBytes ++ ([ldS kp kpSlot, ldS t0 fkSlot, .cmp kp (.reg t0)] : List Instr)

def decEnd : List Instr := addKey 0 p p ++ invMixColumns 0

/-- The first round key, and back to blocks. -/
def decLast : List Instr := addKey 0 q p ++ ortho

def decBody : Prog isa :=
  .seq (.block decHead) (.seq (.ite .eq (.block decHi) (.block []))
    (.seq (.block decLo) (.ite .eq (.block decLast) (.block decEnd))))

/-- Decrypt the two blocks, with `kp` at the first round key, whose address is
also in slot `fkSlot`. -/
def decrypt2 : Prog isa :=
  .seq (.block decTest) (.seq (.ite .ne (.block sr2Words) (.block []))
    (.seq (.block decStart) (.loop decBody .ne)))

end VG.Impl.Aes.Arm
