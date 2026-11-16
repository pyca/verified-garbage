module

public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-512 compression function: AArch64 implementation

`vg_sha512_compress(state = x0, blocks = x1, n = x2, scratch = x3)`.

* The working variables `a … h` live in `x4`–`x11`; the fully unrolled rounds
  rename them: in round `t`, variable `k` is in `var t k`.
* The message schedule's 16-word window is in registers (`wregs`: `x12`–`x17`
  and `x19`–`x28`), `Wₜ` replacing `Wₜ₋₁₆`: nothing of it is in memory, and
  `scratch` is not used.
* The rotations of `Σ₀`, `Σ₁`, `σ₀` and `σ₁` are the rotated operand of
  `eor`, three instructions for each function.
* `Maj(a, b, c)` is `((b ⊕ c) ∧ (a ⊕ b)) ⊕ b`, and `a ⊕ b` is the next
  round's `b ⊕ c` (`mreg`).
* `Kₜ` is read from the table of the constants the code carries (`ldrTbl`,
  the static `VG_SHA512_K`, whose address is in `x3`).
* That leaves `x0` for a temporary: the pointers and the count are kept in
  lanes of `v16` and `v17`, and moved to `x0` where they are used, and the
  callee-saved registers `x19`–`x28` in lanes of `v18`–`v22`, from which they
  are restored at the end. A lane is as public as the register kept in it
  (the lane taint analysis), which what is loaded from memory never is.
* The pointers and the block count are public; no address and no branch
  depends on anything else.
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

/-- A temporary: the functions of the round and of the schedule, and the
pointers and the count where they are used. -/
def T : Reg := .x0

/-- `a ⊕ b` of round `t`, which is the `b ⊕ c` of round `t + 1`: so
`mreg (t + 1)` holds `b ⊕ c` in round `t`. -/
def mreg (t : Nat) : Reg := if t % 2 = 0 then .x1 else .x2

/-- The address of the table of the constants. -/
def KT : Reg := .x3

/-- The registers of the schedule's window. -/
def wregs : List Reg :=
  [.x12, .x13, .x14, .x15, .x16, .x17, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

/-- The register of `Wₜ`, which held `Wₜ₋₁₆`. -/
def wreg (t : Nat) : Reg := wregs.getD (t % 16) .x12

/-- The lanes of the address of the hash value (0) and of the block (1). -/
def PV : VReg := .v16

/-- The lane (0) of the number of blocks left. -/
def CV : VReg := .v17

/-- The callee-saved registers the schedule uses, and the lanes that keep
the caller's values. -/
def saves : List (Reg × VReg × Nat) :=
  [(.x19, .v18, 0), (.x20, .v18, 1), (.x21, .v19, 0), (.x22, .v19, 1), (.x23, .v20, 0), (.x24, .v20, 1),
   (.x25, .v21, 0), (.x26, .v21, 1), (.x27, .v22, 0), (.x28, .v22, 1)]

/-- The name of the table of the constants (the static the implementation
with the SHA-512 instructions reads too, `Sha3.lean`). -/
def kTab : String := "VG_SHA512_K"

/-- `mov d, #v` for a 64-bit constant: a `movz` and three `movk`s (the
streaming code's, `Stream.lean`). -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.movz .x d (v.extractLsb' 0 16) 0, .movk .x d (v.extractLsb' 16 16) 1,
   .movk .x d (v.extractLsb' 32 16) 2, .movk .x d (v.extractLsb' 48 16) 3]

/-- `wreg t := Wₜ` for `t ≥ 16`, from `Wₜ₋₁₆` there: the sum is
`((Wₜ₋₁₆ + σ₀(Wₜ₋₁₅)) + Wₜ₋₇) + σ₁(Wₜ₋₂)`. The first 16 words are the block's. -/
def schedule (t : Nat) : List Instr :=
  let w := wreg t; let w15 := wreg (t + 1); let w7 := wreg (t + 9); let w2 := wreg (t + 14)
  if t < 16 then []
  else [
    -- T := σ₀(Wₜ₋₁₅)
    .lsr .x T w15 7,
    .logicRor .eor .x T T w15 1,
    .logicRor .eor .x T T w15 8,
    .add .x w w T,
    -- T := σ₁(Wₜ₋₂)
    .lsr .x T w2 6,
    .logicRor .eor .x T T w2 19,
    .logicRor .eor .x T T w2 61,
    .add .x w w w7,
    .add .x w w T]

/-- `T := Kₜ`. -/
def kload (t : Nat) : List Instr := [.ldrTbl .x T KT (8 * t) kTab Spec.Sha512.Ks]

/-- Round `t`, with `Wₜ` in `wreg t`, `Kₜ` in `T` and `b ⊕ c` in
`mreg (t + 1)`. `Wₜ` and `Kₜ`, which do not depend on the round before, are
added to `h` first: the next round's `e` is then three additions after
`Σ₁(e)`. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  let k := mreg t; let m := mreg (t + 1); let w := wreg t
  [ -- h := h + Wₜ + Kₜ
    .add .x h h w,
    .add .x h h T,
    -- h := h + Σ₁(e)
    .ror .x T e 14,
    .logicRor .eor .x T T e 18,
    .logicRor .eor .x T T e 41,
    .add .x h h T,
    -- h := h + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g
    .logic .eor .x T f g,
    .logic .and .x T T e,
    .logic .eor .x T T g,
    .add .x h h T,
    -- e' := d + T₁ (`h` is T₁ now)
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

/-- The block's 16 words into the window, most significant octet first, and
the address of the next block into its lane. -/
def loadBlock : List Instr :=
  ([.umov .x T PV 1] : List Instr) ++
  (List.range 8).map (fun i => .ldp (wreg (2 * i)) (wreg (2 * i + 1)) T (16 * i)) ++
  wregs.map (fun r => .rev r r) ++
  ([.addImm .x T T 128, .vop (.ins .d2 PV 1 T)] : List Instr)

/-- Load the hash value (`80 % 8 = 0`, so the variables are in the same
registers after the 80 rounds), and `b ⊕ c` for round 0. -/
def load : List Instr :=
  ([.umov .x T PV 0] : List Instr) ++
  (List.range 4).map (fun i => .ldp (var 0 (2 * i)) (var 0 (2 * i + 1)) T (16 * i)) ++
  ([.logic .eor .x (mreg 1) (var 0 1) (var 0 2)] : List Instr)

/-- Add the hash value (loaded into the window's first registers, whose words
are used) into the working variables, and store the result. -/
def update : List Instr :=
  ([.umov .x T PV 0] : List Instr) ++
  (List.range 4).map (fun i => .ldp (wreg (2 * i)) (wreg (2 * i + 1)) T (16 * i)) ++
  (List.range 8).map (fun k => .add .x (var 0 k) (var 0 k) (wreg k)) ++
  (List.range 4).map (fun i => .stp (var 0 (2 * i)) (var 0 (2 * i + 1)) T (16 * i))

/-- Decrement the count, which stays in `T` for the loop's test. -/
def advance : List Instr := [.umov .x T CV 0, .subImm .x T T 1, .vop (.ins .d2 CV 0 T)]

/-- One block. -/
def body : Prog isa := .seq (.block (loadBlock ++ load)) (.seq (rounds 80) (.block (update ++ advance)))

/-- Keep the callee-saved registers, the pointers and the count in their
lanes, and put the address of the table of the constants in `KT`. -/
def enter : List Instr :=
  saves.map (fun k => .vop (.ins .d2 k.2.1 k.2.2 k.1)) ++
  ([.vop (.ins .d2 PV 0 .x0), .vop (.ins .d2 PV 1 .x1), .vop (.ins .d2 CV 0 .x2), .adrSym KT kTab] : List Instr)

/-- Restore the callee-saved registers, and leave in `x1` the address after
the blocks, as public as the address of the blocks was: our callers' taint
analysis, which follows no condition, reaches the next call with `x1` as
this one left it. -/
def leave : List Instr :=
  saves.map (fun k => .umov .x k.1 k.2.1 k.2.2) ++ ([.umov .x .x1 PV 1] : List Instr)

def compress : Prog isa :=
  .ite (.zero .x .x2) (.block [])
    (.seq (.block enter) (.seq (.loop body (.nonzero .x T)) (.block leave)))

end VG.Impl.Sha512.AArch64
