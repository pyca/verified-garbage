module

public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-512 compression function: AArch64 implementation

`vg_sha512_compress(state = x0, blocks = x1, n = x2, scratch = x3)`.

* The working variables `a … h` live in `x4`–`x11`; the fully unrolled rounds
  rename them: in round `t`, variable `k` is in `var t k`.
* The message schedule is a 16-word window in `scratch[0..128)`; its last
  two words also stay in registers (`wreg`), so that `Wₜ₋₂` is not loaded,
  and `Wₜ₋₁₆` and `Wₜ₋₁₅`, next to each other in the window unless it wraps
  between them, are loaded by one `ldp`.
* The rotations of `Σ₀`, `Σ₁`, `σ₀` and `σ₁` are the rotated operand of
  `eor`, three instructions for each function.
* `Maj(a, b, c)` is `((b ⊕ c) ∧ (a ⊕ b)) ⊕ b`, and `a ⊕ b` is the next
  round's `b ⊕ c` (`mreg`).
* `Kₜ` is read from the table of the constants the code carries (`ldrqTbl`,
  the static `VG_SHA512_K`, whose address is in `x15`): two constants by one
  load into `v16`, each then moved to a general register (`umov`).
* Only caller-saved registers are used (`x0`–`x17`, `v16`), so nothing is
  saved.
* `x0`–`x3` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sha512.AArch64

open VG.AArch64
open VG.Spec.Sha512 (K)

/-- The bytes of `scratch` the compression function may use (its contract,
`Proof.Sha512.compressAArch64`, and that of each other implementation). The
streaming code gives it `scratch[0..scratchBytes)` and keeps its own data
after it. -/
abbrev scratchBytes : Nat := 640

/-- The registers holding the working variables. -/
def work : List Reg := [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11]

/-- The register holding working variable `k` (`a = 0, …, h = 7`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 8 - t % 8) % 8) .x4

/-- A temporary: the functions of the round, and words of the schedule. -/
def T : Reg := .x12

/-- `a ⊕ b` of round `t`, which is the `b ⊕ c` of round `t + 1`: so
`mreg (t + 1)` holds `b ⊕ c` in round `t`. Until round `t` computes it,
`mreg t` is a temporary of the schedule, and then holds `Kₜ`. -/
def mreg (t : Nat) : Reg := if t % 2 = 0 then .x13 else .x14

/-- The address of the table of the constants. -/
def KT : Reg := .x15

/-- `Wₜ` in round `t`: the two registers hold the last two words of the
schedule. -/
def wreg (t : Nat) : Reg := if t % 2 = 0 then .x16 else .x17

/-- The constants of two rounds. -/
def KV : VReg := .v16

/-- The name of the table of the constants (the static the implementation
with the SHA-512 instructions reads too, `Sha3.lean`). -/
def kTab : String := "VG_SHA512_K"

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 8 * (i % 16)

/-- Leave `Wₜ` in `wreg t` and in its slot. For `t ≥ 16`, `wreg t` holds
`Wₜ₋₂`; the sum is `((Wₜ₋₁₆ + σ₁(Wₜ₋₂)) + σ₀(Wₜ₋₁₅)) + Wₜ₋₇`. -/
def schedule (t : Nat) : List Instr :=
  let w := wreg t
  let u := mreg t
  if t < 16 then [
    .ldr .x w .x1 (8 * t),
    .rev w w,
    .str .x w .x3 (slot t)]
  else
    ([ -- u := σ₁(Wₜ₋₂)
      .lsr .x u w 6,
      .logicRor .eor .x u u w 19,
      .logicRor .eor .x u u w 61] : List Instr) ++
    -- w := Wₜ₋₁₆, T := Wₜ₋₁₅
    (if t % 16 = 15 then [.ldr .x w .x3 (slot t), .ldr .x T .x3 (slot (t + 1))]
      else [.ldp w T .x3 (slot t)]) ++
    ([.add .x w w u,
      -- u := σ₀(Wₜ₋₁₅)
      .lsr .x u T 7,
      .logicRor .eor .x u u T 1,
      .logicRor .eor .x u u T 8,
      .add .x w w u,
      -- w := w + Wₜ₋₇
      .ldr .x T .x3 (slot (t + 9)),
      .add .x w w T,
      .str .x w .x3 (slot t)] : List Instr)

/-- `mreg t := Kₜ`: the constants of rounds `t` and `t + 1` are loaded into
`KV` in the first of them (`t` even). -/
def kload (t : Nat) : List Instr :=
  (if t % 2 = 0 then [.ldrqTbl KV KT (8 * t) kTab Spec.Sha512.Ks] else []) ++
    ([.umov .x (mreg t) KV (t % 2)] : List Instr)

/-- Round `t`, with `Wₜ` in `wreg t`, `Kₜ` in `mreg t` and `b ⊕ c` in
`mreg (t + 1)`. The additions are in the order of the specification. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  let k := mreg t; let m := mreg (t + 1); let w := wreg t
  [ -- h := h + Σ₁(e)
    .ror .x T e 14,
    .logicRor .eor .x T T e 18,
    .logicRor .eor .x T T e 41,
    .add .x h h T,
    -- h := h + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g
    .logic .eor .x T f g,
    .logic .and .x T T e,
    .logic .eor .x T T g,
    .add .x h h T,
    -- h := h + Kₜ + Wₜ, which is T₁
    .add .x h h k,
    .add .x h h w,
    -- e' := d + T₁
    .add .x d d h,
    -- h := h + Σ₀(a)
    .ror .x T a 28,
    .logicRor .eor .x T T a 34,
    .logicRor .eor .x T T a 39,
    .add .x h h T,
    -- h := h + Maj(a, b, c), as ((b ⊕ c) ∧ (a ⊕ b)) ⊕ b; now h = a' = T₁ + T₂
    .logic .eor .x k a b,
    .logic .and .x m m k,
    .logic .eor .x m m b,
    .add .x h h m]

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ kload n ++ round n))

/-- Load the hash value (`80 % 8 = 0`, so the variables are in the same
registers after the 80 rounds), and `b ⊕ c` for round 0. -/
def load : List Instr :=
  (List.range 8).map (fun k => .ldr .x (var 0 k) .x0 (8 * k)) ++
    ([.logic .eor .x (mreg 1) (var 0 1) (var 0 2)] : List Instr)

/-- Temporaries for the hash value while adding it in. -/
def tmp : List Reg := [.x12, .x13, .x14, .x16]

/-- Add the hash value into the working variables (loading all of it before
storing any of it), and store the result. -/
def update : List Instr :=
  (List.range 4).map (fun k => .ldr .x (tmp.getD k .x12) .x0 (8 * k)) ++
  (List.range 4).map (fun k => .add .x (var 0 k) (var 0 k) (tmp.getD k .x12)) ++
  (List.range 4).map (fun k => .ldr .x (tmp.getD k .x12) .x0 (8 * (k + 4))) ++
  (List.range 4).map (fun k => .add .x (var 0 (k + 4)) (var 0 (k + 4)) (tmp.getD k .x12)) ++
  (List.range 8).map (fun k => .str .x (var 0 k) .x0 (8 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addImm .x .x1 .x1 128, .subImm .x .x2 .x2 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 80) (.block (update ++ advance)))

/-- The blocks, with the address of the table of the constants in `KT`. -/
def compress : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.seq (.block [.adrSym KT kTab]) (.loop body (.nonzero .x .x2)))

end VG.Impl.Sha512.AArch64
