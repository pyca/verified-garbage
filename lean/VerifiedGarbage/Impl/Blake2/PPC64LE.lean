module

public import VerifiedGarbage.Spec.Blake2
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# BLAKE2 compression function: PPC64LE implementation

`vg_blake2{b,s}_compress(state = r3, blocks = r4, n = r5, t = r6, last = r7, scratch = r8)`,
for words of `w` bits (64 for BLAKE2b, 32 for BLAKE2s) and the parameters `P`
(`Spec.Blake2.b` or `Spec.Blake2.s`). The same structure as the AArch64
implementation (`VG.Impl.Blake2.AArch64`).

* The sixteen words of the work vector `v` live in registers throughout
  (`wreg`); the rounds are fully unrolled, and each `G` loads its two
  message words from the block (little-endian loads, as BLAKE2 is
  little-endian) into the temporary `r0` as it adds them.
* The registers are 64 bits, and `add` and `xor` act on all of them: a
  32-bit word of BLAKE2s is the low 32 bits of its register, which the
  rotations of words (`rotrwi`) and the stores of words read.
* `r14`–`r23` are nonvolatile: they are saved in `scratch[0, 80)` and
  restored at the end; `r24`–`r31` are never written (the streaming
  functions keep their own values in `r26`–`r31` across a call).
* The offset counter and the final block flag are kept in `scratch`:
  `scratch[80, 88)` is the low 64 bits of the counter of the current block,
  `scratch[88, 96)` the bits above (the carries out of the low word, which
  only BLAKE2b uses: its counter is 128 bits), and `scratch[96, 104)` the
  flag word, all ones if `last ≠ 0` (a 32-bit argument, whose upper half is
  not relied on) and zero otherwise, computed without a branch.
* Advancing the counter by the block size `2 ^ k` wraps its low word exactly
  when the new low word is below `2 ^ k`, i.e. when its `k`-th and higher
  bits are zero: the carry is `((lo >> k) - 1) >> 63`, again without a branch.
* The only branches are on `n`, and every address is `state`, `blocks`
  (advanced by the block size) or `scratch` plus a constant, so only the
  pointers and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Blake2.PPC64LE

open VG.PPC64LE

/-- The operand size of words of `w` bits. -/
def sz (w : Nat) : Size := if w = 64 then .d else .w

/-- The size of a word in bytes. -/
def ws (w : Nat) : Nat := w / 8

/-- The log₂ of the block size, `16 · ws w`. -/
def lbb (w : Nat) : Nat := if w = 64 then 7 else 6

/-- The register holding word `k` of the work vector. -/
def wreg (k : Nat) : Reg :=
  [.r6, .r7, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22,
    .r23].getD k .r6

/-- The temporary. -/
def T : Reg := .r0

/-! ## The layout of `scratch` -/

def loOff : Nat := 80
def hiOff : Nat := 88
def fOff : Nat := 96

/-- The nonvolatile registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r14, 0), (.r15, 8), (.r16, 16), (.r17, 24), (.r18, 32), (.r19, 40), (.r20, 48), (.r21, 56),
    (.r22, 64), (.r23, 72)]

/-- `d := v` for a constant of `w` bits: for a doubleword, the high word with
`lis` and `ori`, shifted up by `sldi`, then the low word with `oris` and
`ori`; for a word, `lis` and `ori`, which leave it in the low 32 bits. -/
def movImm (w : Nat) (d : Reg) (v : BitVec 64) : List Instr :=
  if w = 64 then
    [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
     .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]
  else [.lis d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

section
variable {w : Nat} (P : Spec.Blake2.Params w)

/-! ## The rounds -/

/-- `G` (RFC 7693 §3.1) on the words in `a, b, c, d`, with the message words
`j` and `k` of the block. -/
def g (a b c d : Reg) (j k : Nat) : List Instr := [
  .load (sz w) T .r4 (ws w * j),
  .add a a b, .add a a T, .logic .xor d d a, .rotr (sz w) d d P.R1,
  .add c c d, .logic .xor b b c, .rotr (sz w) b b P.R2,
  .load (sz w) T .r4 (ws w * k),
  .add a a b, .add a a T, .logic .xor d d a, .rotr (sz w) d d P.R3,
  .add c c d, .logic .xor b b c, .rotr (sz w) b b P.R4]

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

/-- Load words `0 … n-1` of the state into words `0 … n-1` of the work vector. -/
def lds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (lds n) (.block [.load (sz w) (wreg n) .r3 (ws w * n)])

/-- Words `8 … n+7` of the work vector: the IV. -/
def ivs : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (ivs n) (.block (movImm w (wreg (n + 8)) ((P.IV.toList.getD n 0).setWidth 64)))

/-- The high word of the offset counter into `T`: BLAKE2b's is `scratch[88, 96)`,
BLAKE2s's the upper half of the low 64 bits. -/
def hiW : List Instr :=
  if w = 64 then [.load .d T .r8 hiOff] else [.load .d T .r8 loOff, .lsr .d T T 32]

/-- The low word of the offset counter into word 12. -/
def ctrLo : List Instr := [.load .d T .r8 loOff, .logic .xor (wreg 12) (wreg 12) T]

/-- The high word of the offset counter (in `T`, from `hiW`) into word 13, and
the final block flag into word 14. -/
def ctrHi : List Instr :=
  [.logic .xor (wreg 13) (wreg 13) T, .load .d T .r8 fOff, .logic .xor (wreg 14) (wreg 14) T]

/-- XOR the two halves of the work vector into words `0 … n-1` of the state:
`h[i] := h[i] ^ v[i] ^ v[i + 8]`. -/
def fin : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (fin n) (.block [.load (sz w) T .r3 (ws w * n),
      .logic .xor T T (wreg n), .logic .xor T T (wreg (n + 8)),
      .store (sz w) T .r3 (ws w * n)])

/-- Advance to the next block and its offset counter (the carry out of the
low word into the high word), and decrement the count of blocks. The work
vector is dead: `r6`, `r7` and `r9` are temporaries. -/
def advance : List Instr :=
  [.addi .r4 .r4 (16 * ws w),
   .load .d .r6 .r8 loOff, .addi .r6 .r6 (16 * ws w), .store .d .r6 .r8 loOff,
   .lsr .d .r7 .r6 (lbb w), .subi .r7 .r7 1, .lsr .d .r7 .r7 63,
   .load .d .r9 .r8 hiOff, .add .r9 .r9 .r7, .store .d .r9 .r8 hiOff,
   .subi .r5 .r5 1]

/-- Initialize the work vector (RFC 7693 §3.2). -/
def init : Prog isa :=
  .seq (lds (w := w) 8) <| .seq (ivs P 8) <| .seq (.block ctrLo) <|
  .seq (.block (hiW (w := w))) (.block ctrHi)

def body : Prog isa :=
  .seq (init P) <| .seq (rounds P P.r) <| .seq (fin (w := w) 8) (.block (advance (w := w)))

/-! ## The whole function -/

def save : List Instr := saved.map fun (r, d) => .store .d r .r8 d
def restore : List Instr := saved.map fun (r, d) => .load .d r .r8 d

/-- Keep the counter in `scratch` (its high word starts at 0) and the flag
word: with `z` the zero-extended low word of `last`, `0 - ((z | (0 - z)) >> 63)`. -/
def setup : List Instr :=
  [.store .d .r6 .r8 loOff, .li T 0, .store .d T .r8 hiOff,
   .rotr .w .r7 .r7 0, .sub .r6 T .r7, .logic .or .r7 .r7 .r6,
   .lsr .d .r7 .r7 63, .sub .r7 T .r7, .store .d .r7 .r8 fOff]

def compress : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite (.zero .d .r5) (.block []) (.loop (body P) (.nonzero .d .r5))) (.block restore))

end

end VG.Impl.Blake2.PPC64LE
