module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# GHASH: PPC64LE implementation

`vg_ghash(h = r3, y = r4, data = r5, n = r6, scratch = r7)`.

For each of the `n` blocks `X` at `data`, `Y := (Y ⊕ X) • H`, where `•` is
SP 800-38D Algorithm 1 bit by bit, as `Spec.Gcm.mul` defines it, as the
AArch64 implementation (`Impl/Gcm/AArch64.lean`) computes it:

* The blocks are big-endian: each 8-byte half is loaded with `ldbrx`. A
  128-bit value is kept in two registers, `hi` (the first eight bytes) and
  `lo`.
* `Y ⊕ X` is in `r8:r9`. Each step takes its most significant bit `xᵢ`
  (`srdi` by 63), turns it into the mask `m = 0 − xᵢ`, and shifts it left
  by one bit with `addc`/`adde` (doubling the low half, then the high half
  with its carry).
* `Z` (in `r10:r11`) accumulates `V & m`, so `Z := Z ⊕ V` exactly when
  `xᵢ = 1`.
* `V` (in `r12:r14`, starting at `H`) is shifted right by one bit, and the
  reduction constant `R` (the high half `0xE1 ‖ 0⁵⁶`, in `r16`) is XORed
  into it under the mask `0 − LSB₁(V)`.
* The 128 steps are a loop of `unroll` steps per iteration, counted down in
  `r17`; `r18` holds zero, and the masks are in `r0` and a temporary in
  `r15`. `Y` is written back to `y` after every block.
* The nonvolatile registers used, `r14`–`r18`, are saved in the first 40
  bytes of the scratch buffer (at `r7`, which the code does not write) on
  entry and restored from there on exit.
* `r3`–`r7` (the pointers and the block count) and `r17` are public; no
  address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Gcm.PPC64LE

open VG.PPC64LE

/-- `Y ⊕ X`, shifted left one bit per step. -/
def XH : Reg := .r8
def XL : Reg := .r9
/-- The product so far, `Z`. -/
def ZH : Reg := .r10
def ZL : Reg := .r11
/-- `V`. -/
def VH : Reg := .r12
def VL : Reg := .r14
/-- The masks `−xᵢ` and `−LSB₁(V)`. -/
def M : Reg := .r0
/-- A temporary. -/
def T : Reg := .r15
/-- The high half of `R`. -/
def RH : Reg := .r16
/-- The loop counter. -/
def CNT : Reg := .r17
/-- Zero. -/
def ZERO : Reg := .r18

/-- The scratch buffer, where the nonvolatile registers are saved. -/
def SCR : Reg := .r7

/-- The nonvolatile registers used, in the order they are saved. -/
def saved (i : Nat) : Reg := [.r14, .r15, .r16, .r17, .r18].getD i .r14

/-- Save them in the first 40 bytes of the scratch buffer. -/
def save : List Instr := (List.range 5).flatMap fun i => [.store .d (saved i) SCR (8 * i)]

/-- Restore them. -/
def restore : List Instr := (List.range 5).flatMap fun i => [.load .d (saved i) SCR (8 * i)]

/-- The high half of `R = 11100001 ‖ 0¹²⁰` (its low half is 0). -/
def rHigh : BitVec 64 := 0xE100000000000000

/-- Steps per iteration of the inner loop. -/
def unroll : Nat := 8

/-- One step `i` of Algorithm 1. -/
def step : List Instr := [
  -- M := −xᵢ, and X := X << 1
  .lsr .d T XH 63,
  .sub M ZERO T,
  .addc XL XL XL,
  .adde XH XH XH,
  -- Z := Z ⊕ (V ∧ M)
  .logic .and T VH M,
  .logic .xor ZH ZH T,
  .logic .and T VL M,
  .logic .xor ZL ZL T,
  -- M := −LSB₁(V)
  .lsl T VL 63,
  .lsr .d T T 63,
  .sub M ZERO T,
  -- V := (V >> 1) ⊕ (R ∧ M)
  .lsr .d VL VL 1,
  .lsl T VH 63,
  .logic .or VL VL T,
  .lsr .d VH VH 1,
  .logic .and M M RH,
  .logic .xor VH VH M]

/-- `unroll` steps, then the count. -/
def steps : List Instr :=
  (List.range unroll).flatMap (fun _ => step) ++ ([.subi CNT CNT 1] : List Instr)

/-- Load `Y ⊕ X`, `V := H`, `Z := 0`, `R`, zero and the count. -/
def load : List Instr := [
  .li ZERO 0, .li M 8,
  .loadRev .d XH .r4 ZERO,
  .loadRev .d T .r5 ZERO,
  .logic .xor XH XH T,
  .loadRev .d XL .r4 M,
  .loadRev .d T .r5 M,
  .logic .xor XL XL T,
  .loadRev .d VH .r3 ZERO,
  .loadRev .d VL .r3 M,
  .li ZH 0, .li ZL 0,
  .lis RH 0xE100, .lsl RH RH 32,
  .li CNT (128 / unroll)]

/-- Store `Z` as the new `Y`, advance to the next block and count it. -/
def store : List Instr := [
  .storeRev .d ZH .r4 ZERO,
  .li M 8,
  .storeRev .d ZL .r4 M,
  .addi .r5 .r5 16, .subi .r6 .r6 1]

/-- One block. -/
def body : Prog isa :=
  .seq (.block load) (.seq (.loop (.block steps) (.nonzero .d CNT)) (.block store))

def ghash : Prog isa :=
  .seq (.block save)
    (.seq (.ite (.zero .d .r6) (.block []) (.loop body (.nonzero .d .r6))) (.block restore))

end VG.Impl.Gcm.PPC64LE
