module

public import VerifiedGarbage.Spec.Sha1
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# SHA-1 compression function: PPC64LE implementation

`vg_sha1_compress(state = r3, blocks = r4, n = r5, scratch = r6)`.

The same structure as the AArch64 implementation (`Impl/Sha1/AArch64.lean`):
* The working variables `a … e` live in `r7`–`r11`; the fully unrolled rounds
  rename them: in round `t`, variable `k` is in `var t k`.
* The message schedule is a 16-word window in `scratch[0..64)`; the block's
  words are loaded big-endian (`lwbrx`).
* Besides the volatile registers (`r0`, `r3`–`r12`), `r14`–`r17` are used:
  they are saved in `scratch[64..96)` first and restored last. `r14` holds
  `Kₜ`, set when it changes (every 20 rounds), and `r15`–`r17` hold the last
  three words of the message schedule, in rotation: `Wₜ` is in `wreg t`,
  which held `Wₜ₋₃`, the first term of `Wₜ`, so `Wₜ` is computed in place.
  With `r3`–`r6` holding the arguments, that leaves two temporaries (`r12`,
  `r0`) besides the working variables, so a round adds its terms into `e`'s
  register one at a time: `Wₜ` first, then `f(b, c, d)` (`Maj` also using
  `T0`), `Kₜ` and `ROTL⁵(a)`.
* The arithmetic is on whole registers: only their low 32 bits are the
  words, as the rotations (`rotrwi`, which reads the low word) and the
  stores (`stw`) use only those.
* `r3`–`r6` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sha1.PPC64LE

open VG.PPC64LE
open VG.Spec.Sha1 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.r7, .r8, .r9, .r10, .r11]

/-- The register holding working variable `k` (`a = 0, …, e = 4`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 5 - t % 5) % 5) .r7

/-- Temporaries. -/
def T0 : Reg := .r12
def T1 : Reg := .r0

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- The nonvolatile registers used, in the order they are saved. -/
def saved (i : Nat) : Reg := [.r14, .r15, .r16, .r17].getD i .r14

/-- The register holding `Kₜ`. -/
def Kr : Reg := saved 0

/-- The register holding `Wₜ` (and `Wₜ₋₃` before it). -/
def wreg (t : Nat) : Reg := saved (1 + t % 3)

/-- Leave `Wₜ` in `wreg t` and in its slot. The operations are in the order
of the specification, starting from `Wₜ₋₃` in `wreg t`; `ROTL¹` is a
rotation right by 31. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .li T1 (4 * t),
    .loadRev .w (wreg t) .r4 T1,
    .store .w (wreg t) .r6 (slot t)]
  else [
    -- Wₜ₋₃ ⊕ Wₜ₋₈ ⊕ Wₜ₋₁₄ ⊕ Wₜ₋₁₆
    .load .w T0 .r6 (slot (t + 8)),
    .logic .xor (wreg t) (wreg t) T0,
    .load .w T0 .r6 (slot (t + 2)),
    .logic .xor (wreg t) (wreg t) T0,
    .load .w T0 .r6 (slot t),
    .logic .xor (wreg t) (wreg t) T0,
    .rotr .w (wreg t) (wreg t) 31,
    .store .w (wreg t) .r6 (slot t)]

/-- Set `Kr` to `Kₜ` where it changes, at rounds 0, 20, 40 and 60. -/
def kset (t : Nat) : List Instr :=
  if t % 20 = 0 then [.lis Kr ((K t).extractLsb' 16 16), .ori Kr Kr ((K t).extractLsb' 0 16)]
  else []

/-- The logical functions of §4.1.1. -/
inductive Fn | ch | parity | maj
  deriving DecidableEq

/-- The function `fₜ` of round `t`. -/
def fn (t : Nat) : Fn :=
  if t < 20 then .ch else if t < 40 then .parity else if t < 60 then .maj else .parity

/-- `T1 := f(b, c, d)` (using `T0` as well for `Maj`). -/
def fcode (f : Fn) (b c d : Reg) : List Instr :=
  match f with
  | .ch => -- `Ch(b, c, d)`, as `((c ⊕ d) ∧ b) ⊕ d`
    [.logic .xor T1 c d, .logic .and T1 T1 b, .logic .xor T1 T1 d]
  | .parity => [.logic .xor T1 b c, .logic .xor T1 T1 d]
  | .maj => -- `Maj(b, c, d)`, as `((b ∨ c) ∧ d) ∨ (b ∧ c)`
    [.logic .or T1 b c, .logic .and T1 T1 d, .logic .and T0 b c, .logic .or T1 T1 T0]

/-- Round `t`, with `Wₜ` in `wreg t` and `Kₜ` in `Kr`: `T = ROTL⁵(a) + f + e + Kₜ + Wₜ`
is added up in `e`'s register (the new `a`), as `e + Wₜ + f + Kₜ + ROTL⁵(a)`,
and `b` becomes `ROTL³⁰(b)`. `ROTLⁿ` is a rotation right by `32 - n`. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3; let e := var t 4
  ([.add e e (wreg t)] : List Instr) ++ fcode (fn t) b c d ++
  ([.add e e T1,
    .add e e Kr,
    .rotr .w T1 a 27,
    .add e e T1,
    .rotr .w b b 2] : List Instr)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (kset n ++ schedule n ++ round n))

/-- Load the hash value (`80 % 5 = 0`, so the variables are in the same
registers after the 80 rounds). -/
def load : List Instr := (List.range 5).map fun k => .load .w (var 0 k) .r3 (4 * k)

/-- Add the hash value into the working variables, one word at a time
through `T0` (loading all of it before storing any of it), and store the
result. -/
def update : List Instr :=
  (List.range 5).flatMap (fun k => [.load .w T0 .r3 (4 * k), .add (var 0 k) (var 0 k) T0]) ++
  (List.range 5).map (fun k => .store .w (var 0 k) .r3 (4 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addi .r4 .r4 64, .subi .r5 .r5 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 80) (.block (update ++ advance)))

/-- Save `r14`–`r17` in `scratch[64..96)`. -/
def save : List Instr := (List.range 4).flatMap fun i => [.store .d (saved i) .r6 (64 + 8 * i)]

/-- Restore `r14`–`r17`. -/
def restore : List Instr := (List.range 4).flatMap fun i => [.load .d (saved i) .r6 (64 + 8 * i)]

/-- The blocks. -/
def blocks : Prog isa := .ite (.zero .d .r5) (.block []) (.loop body (.nonzero .d .r5))

def compress : Prog isa := .seq (.block save) (.seq blocks (.block restore))

end VG.Impl.Sha1.PPC64LE
