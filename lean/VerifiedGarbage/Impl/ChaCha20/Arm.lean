module

public import VerifiedGarbage.TCB.Arm.Isa

/-!
# ChaCha20 block function: 32-bit ARM implementation

`vg_chacha20_block(state = r0, buf = r1)`.

`buf` (256 bytes) is laid out as:

* `[0, 64)`: the output, word `k` at `4k`;
* `[64, 80)`: home slots for words 8–11, word `k` at `64 + 4(k - 8)`;
* `[80, 116)`: the saved `r4`–`r11` and `lr`;
* `[116, 120)`: `state`, the pointer.

There are only 13 registers besides `buf`'s, so during the rounds words 0–7
and 12–15 live in fixed registers (`wreg`) and words 8–11 (the third row)
take turns in `lr`: between two quarter rounds on different words of that
row, the one is stored to its slot and the other loaded (`swap`). A column
round takes them in the order 8, 9, 10, 11 and a diagonal round in the order
11, 10, 9, 8, so that only three of a round's four quarter rounds are
followed by a swap. The ten double rounds are fully unrolled.

ARM's second operand can be rotated for free (`add a, a, b, ror #25`), so
the rotations of a quarter round are folded into the instructions that use
their results (`qr`): a word of the second row is kept rotated left by 7 in
its register (the word is the register rotated right by 25) and one of the
fourth row rotated left by 8 (right by 24), which is what the last rotations
of a quarter round leave, and the other two rotations are applied as
operands. A quarter round is then four additions and four exclusive-ors. The
words are loaded as they are, so the first column round takes its operands
without a rotation (`columns 0 0`), and the rotations left after the last
round are those of the operands of the additions of the input state
(`addWord`).

The input state is read from `state` twice, to load the registers and to
add it to the rounds' result, so the pointer, whose register (`r0`) holds
word 0 during the rounds, is kept in `buf`.

Every address is `r1` or `state` plus a constant, and there are no branches,
so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.Arm

open VG.Arm

/-- Offsets in `buf`: output word `k`, home slot of word `k` (8–11), and the
pointer `state`. -/
def outOff (k : Nat) : Nat := 4 * k
def slotOff (k : Nat) : Nat := 64 + 4 * (k - 8)
def ptrOff : Nat := 116

/-- The register holding word `k` whenever it is in a register. -/
def wreg : Nat → Reg
  | 0 => .r0 | 1 => .r2 | 2 => .r3 | 3 => .r4
  | 4 => .r5 | 5 => .r6 | 6 => .r7 | 7 => .r8
  | 8 => .lr | 9 => .lr | 10 => .lr | 11 => .lr
  | 12 => .r9 | 13 => .r10 | 14 => .r11 | _ => .r12

/-- `r` rotated right by `k`, as a second operand (`r` itself for `k = 0`). -/
def rop (r : Reg) (k : Nat) : Op2 := if k = 0 then .reg r else .shifted r .ror k

/-- The quarter round (RFC 8439 §2.1) on `a`, `b`, `c`, `d`, where the words
`b` and `d` are their registers rotated right by `br` and `dr`; it leaves
them as their registers rotated right by 25 and 24. A rotation left by `k`
is a rotation right by `32 - k`, and the rotation of an exclusive-or is
applied where the result is next used. -/
def qr (a b c d : Reg) (br dr : Nat) : List Instr := [
  .dp .add a a (rop b br), .dp .eor d a (rop d dr),
  .dp .add c c (.shifted d .ror 16), .dp .eor b c (rop b br),
  .dp .add a a (.shifted b .ror 20), .dp .eor d a (.shifted d .ror 16),
  .dp .add c c (.shifted d .ror 24), .dp .eor b c (.shifted b .ror 20)]

/-- `QUARTERROUND(x, y, z, w)` (RFC 8439 §2.2). -/
def quarter (x y z w br dr : Nat) : Prog isa :=
  .block (qr (wreg x) (wreg y) (wreg z) (wreg w) br dr)

/-- Store word `i` (in `lr`) to its slot and load word `j`. -/
def swap (i j : Nat) : Prog isa := .block [.str .lr .r1 (slotOff i), .ldr .lr .r1 (slotOff j)]

/-- A column round, on second and fourth rows rotated by `br` and `dr`.
Starts with word 8 in `lr` and ends with word 11 there. -/
def columns (br dr : Nat) : Prog isa :=
  .seq (quarter 0 4 8 12 br dr) <| .seq (swap 8 9) <| .seq (quarter 1 5 9 13 br dr) <|
  .seq (swap 9 10) <| .seq (quarter 2 6 10 14 br dr) <| .seq (swap 10 11) (quarter 3 7 11 15 br dr)

/-- A diagonal round, its quarter rounds in the order of their third-row
words 11, 10, 9, 8 (they are on different words, so any order gives the
same). Starts with word 11 in `lr` and ends with word 8 there. -/
def diagonals : Prog isa :=
  .seq (quarter 1 6 11 12 25 24) <| .seq (swap 11 10) <| .seq (quarter 0 5 10 15 25 24) <|
  .seq (swap 10 9) <| .seq (quarter 3 4 9 14 25 24) <| .seq (swap 9 8) (quarter 2 7 8 13 25 24)

/-- `inner_block` (RFC 8439 §2.3.1): a column round and a diagonal round.
Starts and ends with word 8 in `lr`. -/
def doubleRound (br dr : Nat) : Prog isa := .seq (columns br dr) diagonals

/-- `n` double rounds, on rows rotated as a quarter round leaves them. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (doubleRound 25 24)

/-- The callee-saved registers we use (`r4`–`r11` and `lr`), and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r4, 80), (.r5, 84), (.r6, 88), (.r7, 92), (.r8, 96), (.r9, 100), (.r10, 104),
   (.r11, 108), (.lr, 112)]

/-- What the prologue stores: the callee-saved registers and `state`. -/
def kept : List (Reg × Nat) := saved ++ [(.r0, ptrOff)]

def save : List Instr := kept.map fun (r, d) => .str r .r1 d
def restore : List Instr := saved.map fun (r, d) => .ldr r .r1 d

/-- The order in which the words are loaded: words 9–11, which go through
`lr` to their slots, before word 8, which stays there, and word 0 last, as
its register holds `state`. -/
def loadOrder (i : Nat) : Nat := [9, 10, 11, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 0].getD i 0

/-- Load word `k` of the input state into its register (and store words
9–11 to their slots). -/
def loadWord (k : Nat) : List Instr :=
  .ldr (wreg k) .r0 (4 * k) :: if 9 ≤ k ∧ k ≤ 11 then [.str (wreg k) .r1 (slotOff k)] else []

def load : List Instr := (List.range 16).flatMap fun i => loadWord (loadOrder i)

/-- The rotation right that gives word `k` from its register after a quarter
round on it. -/
def pend (k : Nat) : Nat := if 4 ≤ k ∧ k < 8 then 25 else if 12 ≤ k then 24 else 0

/-- Whether word `k` is in memory when the input state is added: word 0,
whose register is the temporary, and the third row. -/
def inMem (k : Nat) : Bool := k == 0 || (8 ≤ k && k ≤ 11)

/-- Where it is then: word 0 in its place in the output, the others in
their slots. -/
def rawOff (k : Nat) : Nat := if k = 0 then outOff 0 else slotOff k

/-- The order in which the input state is added: the words in registers
first, which frees `r2` for the words in memory. -/
def addOrder (i : Nat) : Nat := [1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 0, 8, 9, 10, 11].getD i 0

/-- Add word `k` of the input state (at `lr`) to word `k` of the rounds'
result, into the output. -/
def addWord (k : Nat) : List Instr :=
  .ldr .r0 .lr (4 * k) ::
  if inMem k then [.ldr .r2 .r1 (rawOff k), .dp .add .r0 .r2 (.reg .r0), .str .r0 .r1 (outOff k)]
  else [.dp .add (wreg k) .r0 (rop (wreg k) (pend k)), .str (wreg k) .r1 (outOff k)]

/-- Word 8 to its slot, `state` into `lr`, word 0 to the output, and the
input state added. -/
def finish : List Instr :=
  ([.str .lr .r1 (slotOff 8), .ldr .lr .r1 ptrOff, .str .r0 .r1 (outOff 0)] : List Instr) ++
  (List.range 16).flatMap fun i => addWord (addOrder i)

def block : Prog isa :=
  .seq (.block (save ++ load))
    (.seq (doubleRound 0 0) (.seq (rounds 9) (.block (finish ++ restore))))

end VG.Impl.ChaCha20.Arm
