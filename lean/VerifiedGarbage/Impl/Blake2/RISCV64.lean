module

public import VerifiedGarbage.Spec.Blake2
public import VerifiedGarbage.Impl.Words64.RISCV64

/-!
# BLAKE2 compression function: RISC-V implementation

`vg_blake2{b,s}_compress(state = a0, blocks = a1, n = a2, t = a3, last = a4, scratch = a5)`,
for words of `w` bits (64 for BLAKE2b, 32 for BLAKE2s) and the parameters `P`
(`Spec.Blake2.b` or `Spec.Blake2.s`). The structure of the PPC64LE
implementation (`VG.Impl.Blake2.PPC64LE`), for RV64I, which has no rotation
and faults on misaligned accesses:

* `scratch` is rounded up to a multiple of 8 (it has room to spare), so the
  words kept there take aligned accesses. The state and the blocks are
  argument buffers, whose alignment the contract does not state: the
  prologue copies the hash value, a byte at a time, to `scratch` (`hOff`),
  where the blocks update it, and the epilogue copies it back; each block is
  copied to `scratch` (`mOff`) before its rounds. Aligned blocks use native
  word loads; other blocks use byte loads. The `G`s read their message words
  from scratch.
* The sixteen words of the work vector `v` live in registers throughout
  (`wreg`); the rounds are fully unrolled. A rotation right by `r` is a
  right shift by `r` into `s6` and a left shift by `w - r`, combined by `or`
  (`rot`); for BLAKE2s, the 32-bit forms (`srliw`, `slliw`), which read the
  low words. `add` and `xor` act on all 64 bits: a 32-bit word of BLAKE2s
  is the low 32 bits of its register, which the word shifts and stores read.
* `s0`–`s6` are callee-saved: they are saved in `scratch` and restored at
  the end; `s7`–`s11` are never written.
* The offset counter and the final block flag are kept in `scratch`:
  `loOff` is the low 64 bits of the counter of the current block, `hiOff`
  the bits above (the carries out of the low word, which only BLAKE2b uses:
  its counter is 128 bits), and `fOff` the flag word, all ones if
  `last ≠ 0` (a 32-bit argument, whose upper half is not relied on) and
  zero otherwise, computed without a branch.
* Advancing the counter by the block size `2 ^ k` wraps its low word exactly
  when the new low word is below `2 ^ k`, i.e. when its `k`-th and higher
  bits are zero: the carry is `((lo >> k) - 1) >> 63`, again without a branch.
* The only branches are on `n`, and every address is `state`, `blocks`
  (advanced by the block size) or `scratch` plus a constant, so only the
  pointers and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Blake2.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (loadLE32 storeLE32 li32)
open VG.Impl.Words64.RISCV64 (loadLE64 storeLE64 movImm64)

/-- The operand size of the shifts of words of `w` bits. -/
def sz (w : Nat) : Size := if w = 64 then .d else .w

/-- The width of the loads and stores of words of `w` bits. -/
def wd (w : Nat) : Width := if w = 64 then .d else .w

/-- The size of a word in bytes. -/
def ws (w : Nat) : Nat := w / 8

/-- The log₂ of the block size, `16 · ws w`. -/
def lbb (w : Nat) : Nat := if w = 64 then 7 else 6

/-- The register holding word `k` of the work vector. -/
def wreg (k : Nat) : Reg :=
  [.a3, .a4, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4, .s5].getD k .a3

/-- The temporary. -/
def T : Reg := .t6
/-- The temporary of the rotations. -/
def RT : Reg := .s6
/-- The scratch space, rounded up to a multiple of 8. -/
def SB : Reg := .a5

/-! ## The layout of `scratch` -/

def loOff : Nat := 56
def hiOff : Nat := 64
def fOff : Nat := 72
/-- The hash value. -/
def hOff : Nat := 80
/-- The current block. -/
def mOff : Nat := 144

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.s0, 0), (.s1, 8), (.s2, 16), (.s3, 24), (.s4, 32), (.s5, 40), (.s6, 48)]

/-- `d :=` the little-endian word of `w` bits at `off(n)`, a byte at a time,
through `tmp` and `tmp2`. -/
def ldLE (w : Nat) (d tmp tmp2 n : Reg) (off : Nat) : List Instr :=
  if w = 64 then loadLE64 d tmp tmp2 n off else loadLE32 d tmp n off

/-- Store the word of `w` bits in `v` at `off(n)`, a byte at a time, through
`tmp` and `tmp2`. -/
def stLE (w : Nat) (v tmp tmp2 n : Reg) (off : Nat) : List Instr :=
  if w = 64 then storeLE64 v tmp tmp2 n off else storeLE32 v tmp n off

/-- `d := v` for a constant of `w` bits, through `T`. -/
def movImm (w : Nat) (d : Reg) (v : BitVec 64) : List Instr :=
  if w = 64 then movImm64 d T v else li32 d (v.setWidth 32)

section
variable {w : Nat} (P : Spec.Blake2.Params w)

/-! ## The rounds -/

/-- `d := d ⋙ r` on words of `w` bits, through `RT`. -/
def rot (d : Reg) (r : Nat) : List Instr :=
  [.shift .srl (sz w) RT d r, .shift .sll (sz w) d d (w - r), .logic .or d d RT]

/-- `G` (RFC 7693 §3.1) on the words in `a, b, c, d`, with the message words
`j` and `k` of the block. -/
def g (a b c d : Reg) (j k : Nat) : List Instr :=
  [.load (wd w) T SB (mOff + ws w * j), .add a a b, .add a a T, .logic .xor d d a] ++
  rot (w := w) d P.R1 ++ [.add c c d, .logic .xor b b c] ++ rot (w := w) b P.R2 ++
  [.load (wd w) T SB (mOff + ws w * k), .add a a b, .add a a T, .logic .xor d d a] ++
  rot (w := w) d P.R3 ++ [.add c c d, .logic .xor b b c] ++ rot (w := w) b P.R4

/-- `G(v, x, y, z, u, m[s[2i]], m[s[2i+1]])` of round `r` (the `i`-th `G` of the
round). -/
def gAt (r i x y z u : Nat) : Prog isa :=
  .block (g P (wreg x) (wreg y) (wreg z) (wreg u) (Spec.Blake2.sigmaAt r (2 * i))
    (Spec.Blake2.sigmaAt r (2 * i + 1)))

/-- Round `r` (RFC 7693 §3.2). -/
def round (r : Nat) : Prog isa :=
  .seq (gAt P r 0 0 4 8 12) <| .seq (gAt P r 1 1 5 9 13) <| .seq (gAt P r 2 2 6 10 14) <|
  .seq (gAt P r 3 3 7 11 15) <| .seq (gAt P r 4 0 5 10 15) <| .seq (gAt P r 5 1 6 11 12) <|
  .seq (gAt P r 6 2 7 8 13) (gAt P r 7 3 4 9 14)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (round P n)

/-! ## One block -/

/-- Word `j` of the block at `a1` to `scratch`. -/
def cpBlk (j : Nat) (aligned : Bool := false) : List Instr :=
  (if aligned then [.load (wd w) T .a1 (ws w * j)]
   else ldLE w T (wreg 0) (wreg 1) .a1 (ws w * j)) ++ ([.store (wd w) T SB (mOff + ws w * j)] : List Instr)

/-- Copy a block using native loads when its address is aligned, retaining
byte loads for arbitrary input alignment. The scratch buffer is aligned. -/
def copyBlock : Prog isa :=
  .seq (.block [.logicImm .and T .a1 (Int.ofNat (ws w - 1))])
    (.ite (.zero T)
      (.block ((List.range 16).flatMap fun j => cpBlk (w := w) j true))
      (.block ((List.range 16).flatMap (cpBlk (w := w)))))

/-- Load words `0 … n-1` of the hash value into words `0 … n-1` of the work vector. -/
def lds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (lds n) (.block [.load (wd w) (wreg n) SB (hOff + ws w * n)])

/-- Words `8 … n+7` of the work vector: the IV. -/
def ivs : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (ivs n) (.block (movImm w (wreg (n + 8)) ((P.IV.toList.getD n 0).setWidth 64)))

/-- The high word of the offset counter into `T`: BLAKE2b's is at `hiOff`,
BLAKE2s's the upper half of the low 64 bits. -/
def hiW : List Instr :=
  if w = 64 then [.load .d T SB hiOff] else [.load .d T SB loOff, .shift .srl .d T T 32]

/-- The low word of the offset counter into word 12. -/
def ctrLo : List Instr := [.load .d T SB loOff, .logic .xor (wreg 12) (wreg 12) T]

/-- The high word of the offset counter (in `T`, from `hiW`) into word 13, and
the final block flag into word 14. -/
def ctrHi : List Instr :=
  [.logic .xor (wreg 13) (wreg 13) T, .load .d T SB fOff, .logic .xor (wreg 14) (wreg 14) T]

/-- XOR the two halves of the work vector into words `0 … n-1` of the hash
value: `h[i] := h[i] ^ v[i] ^ v[i + 8]`. -/
def fin : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (fin n) (.block [.load (wd w) T SB (hOff + ws w * n),
      .logic .xor T T (wreg n), .logic .xor T T (wreg (n + 8)),
      .store (wd w) T SB (hOff + ws w * n)])

/-- Advance to the next block and its offset counter (the carry out of the
low word into the high word), and decrement the count of blocks. The work
vector is dead: words 0–2 are temporaries. -/
def advance : List Instr :=
  [.addi .a1 .a1 (16 * ws w),
   .load .d (wreg 0) SB loOff, .addi (wreg 0) (wreg 0) (16 * ws w), .store .d (wreg 0) SB loOff,
   .shift .srl .d (wreg 1) (wreg 0) (lbb w), .addi (wreg 1) (wreg 1) (-1),
   .shift .srl .d (wreg 1) (wreg 1) 63,
   .load .d (wreg 2) SB hiOff, .add (wreg 2) (wreg 2) (wreg 1), .store .d (wreg 2) SB hiOff,
   .addi .a2 .a2 (-1)]

/-- Initialize the work vector (RFC 7693 §3.2). -/
def init : Prog isa :=
  .seq (lds (w := w) 8) <| .seq (ivs P 8) <| .seq (.block ctrLo) <|
  .seq (.block (hiW (w := w))) (.block ctrHi)

def body : Prog isa :=
  .seq (copyBlock (w := w)) <| .seq (init P) <|
  .seq (rounds P P.r) <| .seq (fin (w := w) 8) (.block (advance (w := w)))

/-! ## The whole function -/

/-- Word `k` of the hash value to `scratch`. -/
def cpIn (k : Nat) : List Instr :=
  ldLE w T (wreg 0) (wreg 1) .a0 (ws w * k) ++ ([.store (wd w) T SB (hOff + ws w * k)] : List Instr)

/-- Word `k` of the hash value back from `scratch`. -/
def cpOut (k : Nat) : List Instr :=
  .load (wd w) T SB (hOff + ws w * k) :: stLE w T (wreg 0) (wreg 1) .a0 (ws w * k)

def save : List Instr := saved.map fun (r, d) => .store .d r SB d
def restore : List Instr := saved.map fun (r, d) => .load .d r SB d

/-- Round `scratch` up, save the registers, keep the counter (its high word
starts at 0) and the flag word: with `z` the zero-extended low word of
`last`, `0 - ((z | (0 - z)) >> 63)`; and copy the hash value. -/
def setup : List Instr :=
  [.addi SB SB 7, .logicImm .and SB SB (-8)] ++ save ++
  [.store .d .a3 SB loOff, .li T 0, .store .d T SB hiOff,
   .shift .sll .d .a4 .a4 32, .shift .srl .d .a4 .a4 32, .sub .a3 T .a4, .logic .or .a4 .a4 .a3,
   .shift .srl .d .a4 .a4 63, .sub .a4 T .a4, .store .d .a4 SB fOff] ++
  (List.range 8).flatMap (cpIn (w := w))

/-- Copy the hash value back, and restore the registers. -/
def epilogue : List Instr := (List.range 8).flatMap (cpOut (w := w)) ++ restore

def compress : Prog isa :=
  .seq (.block (setup (w := w)))
    (.seq (.ite (.zero .a2) (.block []) (.loop (body P) (.nonzero .a2))) (.block (epilogue (w := w))))

end

end VG.Impl.Blake2.RISCV64
