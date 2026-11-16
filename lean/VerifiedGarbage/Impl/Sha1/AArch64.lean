module

public import VerifiedGarbage.Spec.Sha1
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-1 compression function: AArch64 implementation

`vg_sha1_compress(state = x0, blocks = x1, n = x2, scratch = x3)`.

* The working variables `a … e` live in `w4`–`w8`; the fully unrolled rounds
  rename them: in round `t`, variable `k` is in `var t k`.
* The message schedule's 16-word window is in registers (`wregs`: `x12`–`x17`
  and `x19`–`x28`), `Wₜ` replacing `Wₜ₋₁₆`: nothing of it is in memory, and
  `scratch` is not used. Two words of the block are loaded at once: after
  the byte reversal of the doubleword the second is in its low half, and
  the first is shifted down from its high half.
* `Kₜ` stays in a register for the 20 rounds that share it.
* The callee-saved registers `x19`–`x28` are kept in lanes of `v18`–`v22`,
  from which they are restored at the end. A lane is as public as the
  register kept in it (the lane taint analysis), which what is loaded from
  memory never is.
* `x0`–`x3` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sha1.AArch64

open VG.AArch64
open VG.Spec.Sha1 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.x4, .x5, .x6, .x7, .x8]

/-- The register holding working variable `k` (`a = 0, …, e = 4`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 5 - t % 5) % 5) .x4

/-- The register holding `Kₜ`. -/
def KR : Reg := .x9

/-- Temporaries. -/
def T1 : Reg := .x11
def T2 : Reg := .x10

/-- The registers of the schedule's window. -/
def wregs : List Reg :=
  [.x12, .x13, .x14, .x15, .x16, .x17, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

/-- The register of `Wₜ` (its low half), which held `Wₜ₋₁₆`. -/
def wreg (t : Nat) : Reg := wregs.getD (t % 16) .x12

/-- The callee-saved registers the schedule uses, and the lanes that keep
the caller's values. -/
def saves : List (Reg × VReg × Nat) :=
  [(.x19, .v18, 0), (.x20, .v18, 1), (.x21, .v19, 0), (.x22, .v19, 1), (.x23, .v20, 0), (.x24, .v20, 1),
   (.x25, .v21, 0), (.x26, .v21, 1), (.x27, .v22, 0), (.x28, .v22, 1)]

/-- Leave `Kₜ` in `KR`, which holds it already unless `t` is the first of
the 20 rounds that share it. -/
def kcode (t : Nat) : List Instr :=
  if t % 20 = 0 then [
    .movz .w KR ((K t).extractLsb' 0 16) 0,
    .movk .w KR ((K t).extractLsb' 16 16) 1]
  else []

/-- `wreg t := Wₜ` for `t ≥ 16`, from `Wₜ₋₁₆` there:
`ROTL¹(((Wₜ₋₁₆ ⊕ Wₜ₋₁₄) ⊕ Wₜ₋₈) ⊕ Wₜ₋₃)`, `ROTL¹` a rotation right by 31. The
first 16 words are the block's. -/
def schedule (t : Nat) : List Instr :=
  let w := wreg t
  if t < 16 then []
  else [
    .logic .eor .w w w (wreg (t + 2)),
    .logic .eor .w w w (wreg (t + 8)),
    .logic .eor .w w w (wreg (t + 13)),
    .ror .w w w 31]

/-- The logical functions of §4.1.1. -/
inductive Fn | ch | parity | maj
  deriving DecidableEq

/-- The function `fₜ` of round `t`. -/
def fn (t : Nat) : Fn :=
  if t < 20 then .ch else if t < 40 then .parity else if t < 60 then .maj else .parity

/-- `T1 := f(b, c, d)` (using `T2` as well for `Maj`). -/
def fcode (f : Fn) (b c d : Reg) : List Instr :=
  match f with
  | .ch => -- `Ch(b, c, d)`, as `((c ⊕ d) ∧ b) ⊕ d`
    [.logic .eor .w T1 c d, .logic .and .w T1 T1 b, .logic .eor .w T1 T1 d]
  | .parity => [.logic .eor .w T1 b c, .logic .eor .w T1 T1 d]
  | .maj => -- `Maj(b, c, d)`, as `((b ∨ c) ∧ d) ∨ (b ∧ c)`
    [.logic .orr .w T1 b c, .logic .and .w T1 T1 d, .logic .and .w T2 b c,
      .logic .orr .w T1 T1 T2]

/-- The rest of a round, with `f(b, c, d)` in `T1`, `Wₜ` in `w` and `Kₜ` in
`KR`: `T = ROTL⁵(a) + f + e + Kₜ + Wₜ` is accumulated in `e`'s register (the
new `a`), and `b` becomes `ROTL³⁰(b)`. `ROTLⁿ` is a rotation right by
`32 - n`. -/
def sum (a b e w : Reg) : List Instr := [
  .ror .w T2 a 27,
  .add .w e e w,
  .add .w e e KR,
  .add .w e e T1,
  .add .w e e T2,
  .ror .w b b 2]

/-- Round `t`, with `Wₜ` in `wreg t` and `Kₜ` in `KR`. -/
def round (t : Nat) : List Instr :=
  fcode (fn t) (var t 1) (var t 2) (var t 3) ++ sum (var t 0) (var t 1) (var t 4) (wreg t)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (kcode n ++ (schedule n ++ round n)))

/-- Words `2i` and `2i + 1` of the block, most significant octet first, into
their registers: the doubleword's octets reversed leave the second in the
low half of its register and the first in the high half. -/
def loadPair (i : Nat) : List Instr :=
  [.ldr .x (wreg (2 * i + 1)) .x1 (8 * i), .rev (wreg (2 * i + 1)) (wreg (2 * i + 1)),
    .lsr .x (wreg (2 * i)) (wreg (2 * i + 1)) 32]

/-- The block's 16 words into the window. -/
def loadBlock : List Instr := (List.range 8).flatMap loadPair

/-- Load the hash value (`80 % 5 = 0`, so the variables are in the same
registers after the 80 rounds). -/
def load : List Instr := (List.range 5).map fun k => .ldr .w (var 0 k) .x0 (4 * k)

/-- Temporaries for the hash value while adding it in (the window's first
registers among them, whose words are used). -/
def tmp : List Reg := [.x9, .x10, .x11, .x12, .x13]

/-- Add the hash value into the working variables (loading all of it before
storing any of it), and store the result. -/
def update : List Instr :=
  (List.range 5).map (fun k => .ldr .w (tmp.getD k .x9) .x0 (4 * k)) ++
  (List.range 5).map (fun k => .add .w (var 0 k) (var 0 k) (tmp.getD k .x9)) ++
  (List.range 5).map (fun k => .str .w (var 0 k) .x0 (4 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1]

/-- One block. -/
def body : Prog isa := .seq (.block (loadBlock ++ load)) (.seq (rounds 80) (.block (update ++ advance)))

/-- Keep the callee-saved registers in their lanes. -/
def enter : List Instr := saves.map fun k => .vop (.ins .d2 k.2.1 k.2.2 k.1)

/-- Restore the callee-saved registers. -/
def leave : List Instr := saves.map fun k => .umov .x k.1 k.2.1 k.2.2

def compress : Prog isa :=
  .ite (.zero .x .x2) (.block [])
    (.seq (.block enter) (.seq (.loop body (.nonzero .x .x2)) (.block leave)))

end VG.Impl.Sha1.AArch64
