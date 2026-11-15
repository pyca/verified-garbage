module

public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Impl.Sha256.AArch64.Sha2

/-!
# SHA-256 compression function: AArch64 implementation

`vg_sha256_compress(state = x0, blocks = x1, n = x2, scratch = x3)`.

* The working variables `a … h` live in `w4`–`w11`; the fully unrolled rounds
  rename them: in round `t`, variable `k` is in `var t k`.
* The message schedule is a 16-word window in `scratch[0..64)`; its last
  two words also stay in registers (`wreg`), so that `Wₜ₋₂` is not loaded.
* The rotations of `Σ₀`, `Σ₁`, `σ₀` and `σ₁` are the rotated operand of
  `eor`, three instructions for each function.
* `Maj(a, b, c)` is `((b ⊕ c) ∧ (a ⊕ b)) ⊕ b`, and `a ⊕ b` is the next
  round's `b ⊕ c` (`mreg`).
* `Kₜ` is read from the table of the constants the code carries (`ldrqTbl`,
  the static `VG_SHA256_K` of the implementation with the SHA-2
  instructions, whose address is in `x15`): four constants by one load into
  `v16`, each then moved to a general register (`umov`).
* Only caller-saved registers are used (`x0`–`x17`, `v16`), so nothing is
  saved.
* `x0`–`x3` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sha256.AArch64

open VG.AArch64
open VG.Spec.Sha256 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11]

/-- The register holding working variable `k` (`a = 0, …, h = 7`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 8 - t % 8) % 8) .x4

/-- A temporary: `Kₜ`, the functions of the round, and words of the schedule. -/
def T : Reg := .x12

/-- `a ⊕ b` of round `t`, which is the `b ⊕ c` of round `t + 1`: so
`mreg (t + 1)` holds `b ⊕ c` in round `t`. Until round `t` computes it,
`mreg t` is a temporary of the schedule. -/
def mreg (t : Nat) : Reg := if t % 2 = 0 then .x13 else .x14

/-- The address of the table of the constants. -/
def KT : Reg := .x15

/-- `Wₜ` in round `t`: the two registers hold the last two words of the
schedule. -/
def wreg (t : Nat) : Reg := if t % 2 = 0 then .x16 else .x17

/-- The constants of four rounds. -/
def KV : VReg := .v16

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- Leave `Wₜ` in `wreg t` and in its slot. For `t ≥ 16`, `wreg t` holds
`Wₜ₋₂`; the sum is `((Wₜ₋₁₆ + σ₁(Wₜ₋₂)) + σ₀(Wₜ₋₁₅)) + Wₜ₋₇`. -/
def schedule (t : Nat) : List Instr :=
  let w := wreg t
  let u := mreg t
  if t < 16 then [
    .ldr .w w .x1 (4 * t),
    .rev32 w w,
    .str .w w .x3 (slot t)]
  else [
    -- u := σ₁(Wₜ₋₂)
    .lsr .w u w 10,
    .logicRor .eor .w u u w 17,
    .logicRor .eor .w u u w 19,
    -- w := Wₜ₋₁₆ + u, T := Wₜ₋₁₅
    .ldr .w w .x3 (slot t),
    .ldr .w T .x3 (slot (t + 1)),
    .add .w w w u,
    -- u := σ₀(Wₜ₋₁₅)
    .lsr .w u T 3,
    .logicRor .eor .w u u T 7,
    .logicRor .eor .w u u T 18,
    .add .w w w u,
    -- w := w + Wₜ₋₇
    .ldr .w T .x3 (slot (t + 9)),
    .add .w w w T,
    .str .w w .x3 (slot t)]

/-- `T := Kₜ`: the constants of rounds `t` to `t + 3` are loaded into `KV`
in the first of them (`t` a multiple of 4). -/
def kload (t : Nat) : List Instr :=
  (if t % 4 = 0 then [.ldrqTbl KV KT (16 * (t / 4)) Sha2.kName Sha2.kTable] else []) ++
    ([.umov .w T KV (t % 4)] : List Instr)

/-- Round `t`, with `Wₜ` in `wreg t`, `Kₜ` in `T` and `b ⊕ c` in
`mreg (t + 1)`. `Wₜ` and `Kₜ`, which do not depend on the round before,
are added first. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  let k := mreg t; let m := mreg (t + 1); let w := wreg t
  [ -- h := h + Wₜ + Kₜ
    .add .w h h w,
    .add .w h h T,
    -- h := h + Σ₁(e)
    .ror .w T e 6,
    .logicRor .eor .w T T e 11,
    .logicRor .eor .w T T e 25,
    .add .w h h T,
    -- h := h + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g; now h is T₁
    .logic .eor .w T f g,
    .logic .and .w T T e,
    .logic .eor .w T T g,
    .add .w h h T,
    -- e' := d + T₁
    .add .w d d h,
    -- h := h + Σ₀(a)
    .ror .w T a 2,
    .logicRor .eor .w T T a 13,
    .logicRor .eor .w T T a 22,
    .add .w h h T,
    -- h := h + Maj(a, b, c), as ((b ⊕ c) ∧ (a ⊕ b)) ⊕ b; now h = a' = T₁ + T₂
    .logic .eor .w k a b,
    .logic .and .w m m k,
    .logic .eor .w m m b,
    .add .w h h m]

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ kload n ++ round n))

/-- Load the hash value (`64 % 8 = 0`, so the variables are in the same
registers after the 64 rounds), and `b ⊕ c` for round 0. -/
def load : List Instr :=
  (List.range 8).map (fun k => .ldr .w (var 0 k) .x0 (4 * k)) ++
    ([.logic .eor .w (mreg 1) (var 0 1) (var 0 2)] : List Instr)

/-- Temporaries for the hash value while adding it in. -/
def tmp : List Reg := [.x12, .x13, .x14, .x16]

/-- Add the hash value into the working variables (loading all of it before
storing any of it), and store the result. -/
def update : List Instr :=
  (List.range 4).map (fun k => .ldr .w (tmp.getD k .x12) .x0 (4 * k)) ++
  (List.range 4).map (fun k => .add .w (var 0 k) (var 0 k) (tmp.getD k .x12)) ++
  (List.range 4).map (fun k => .ldr .w (tmp.getD k .x12) .x0 (4 * (k + 4))) ++
  (List.range 4).map (fun k => .add .w (var 0 (k + 4)) (var 0 (k + 4)) (tmp.getD k .x12)) ++
  (List.range 8).map (fun k => .str .w (var 0 k) .x0 (4 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 64) (.block (update ++ advance)))

/-- The blocks, with the address of the table of the constants in `KT`. -/
def compress : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.seq (.block [.adrSym KT Sha2.kName]) (.loop body (.nonzero .x .x2)))

end VG.Impl.Sha256.AArch64
