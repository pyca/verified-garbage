module

public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.Impl.Words.RISCV64.Word64
public import VerifiedGarbage.Impl.Words64.RISCV64

/-!
# SHA-512 compression function: RISC-V implementation

`vg_sha512_compress(state = a0, blocks = a1, n = a2, scratch = a3)`.

The structure of the SHA-256 implementation (`VG.Impl.Sha256.RISCV64`), on
whole 64-bit registers:
* The working variables `a … h` live in `t0`–`t6` and `a4`; the fully
  unrolled rounds rename them: in round `t`, variable `k` is in `var t k`.
* A rotation right by `r` is `srli` by `r` and `slli` by `64 - r`, whose bits
  do not overlap, so the three rotations of a `Σ` or `σ` are six shifts
  combined by `xor`.
* `Kₜ` is built by `li64` (`Impl/Words/RISCV64/Word64.lean`), from two 32-bit
  halves.
* The hash value (`state`, an array of `u64`) and the blocks are argument
  buffers, whose alignment the contract does not state, so they are read
  and written a byte at a time; the words of a block are big-endian.
* `scratch` is rounded up to a multiple of 8 (it has room to spare), so the
  16-word message schedule window in its first 128 bytes, and `s0`, the one
  callee-saved register used, saved at offset 128, take naturally aligned
  doubleword accesses.
* `a0`–`a3` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sha512.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64
open VG.Impl.Words64.RISCV64 (loadLE64 storeLE64)
open VG.Spec.Sha512 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4]

/-- The register holding working variable `k` (`a = 0, …, h = 7`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 8 - t % 8) % 8) .t0

/-- Temporaries; `T0` holds `Wₜ` at the start of each round. -/
def T0 : Reg := .a5
def T1 : Reg := .a6
def T2 : Reg := .a7
def T3 : Reg := .s0

/-- The rotation amounts whose constants `2 ^ (64 - r)` live in registers. -/
def rots : List Nat := [19, 61, 1, 8]

/-- The callee-saved registers holding the constants, in the order of `rots`. -/
def cregs : List Reg := [.s1, .s2, .s3, .s4]

/-- The register holding `2 ^ (64 - r)`. -/
def C (r : Nat) : Reg := cregs.getD (rots.idxOf r) .s1

/-- Round `scratch` up to a multiple of 8, save `s0`–`s10` in it, and load the constants. -/
def save : List Instr := [.addi .a3 .a3 7, .logicImm .and .a3 .a3 (-8)] ++
  ((Reg.s0 :: cregs).zipIdx.map fun (r, i) => .store .d r .a3 (128 + 8 * i)) ++
  rots.flatMap fun r => [.li (C r) 1, .shift .sll .d (C r) (C r) (64 - r)]

/-- Restore `s0`–`s10`. -/
def restore : List Instr := (Reg.s0 :: cregs).zipIdx.map fun (r, i) => .load .d r .a3 (128 + 8 * i)

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 8 * (i % 16)

/-- `d := x ⋙ r`'s right half, by `srli` (`hu = false`) or `mulhu` by `2 ^ (64 - r)`. -/
def shr (hu : Bool) (d x : Reg) (r : Nat) : Instr :=
  if hu then .mulhu d x (C r) else .shift .srl .d d x r

/-- `d := d ⊕ (x ⋙ r)`. -/
def xorRotr (hu : Bool) (d tmp x : Reg) (r : Nat) : List Instr :=
  [shr hu tmp x r, .logic .xor d d tmp, .mul tmp x (C r), .logic .xor d d tmp]

/-- `d := (x ⋙ r₁) ⊕ (x ⋙ r₂) ⊕ (x ⋙ r₃)` (a `Σ`), with `tmp` clobbered. -/
def xorRotrS (d tmp x : Reg) (r : Nat) : List Instr :=
  [.shift .srl .d tmp x r, .logic .xor d d tmp, .shift .sll .d tmp x (64 - r), .logic .xor d d tmp]

def bsig (_hu : Bool) (d tmp x : Reg) (r₁ r₂ r₃ : Nat) : List Instr :=
  [.shift .srl .d d x r₁, .shift .sll .d tmp x (64 - r₁), .logic .xor d d tmp] ++
    xorRotrS d tmp x r₂ ++ xorRotrS d tmp x r₃

/-- `d := (x ⋙ r₁) ⊕ (x ⋙ r₂) ⊕ (x ≫ r₃)` (a `σ`), with `tmp` clobbered. -/
def ssig (d tmp x : Reg) (r₁ r₂ r₃ : Nat) : List Instr :=
  [shr false d x r₁, .mul tmp x (C r₁), .logic .xor d d tmp] ++
    xorRotr false d tmp x r₂ ++ [.shift .srl .d tmp x r₃, .logic .xor d d tmp]

/-- Leave `Wₜ` in `T0` and in its slot. The additions are in the order of the
specification. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then loadBE64 T0 T1 .a1 (8 * t) ++ [.store .d T0 .a3 (slot t)]
  else
    -- T0 := σ₁(Wₜ₋₂)
    [.load .d T1 .a3 (slot (t + 14))] ++ ssig T0 T2 T1 19 61 6 ++
    -- T0 := T0 + Wₜ₋₇
    [.load .d T2 .a3 (slot (t + 9)), .add T0 T0 T2] ++
    -- T0 := T0 + σ₀(Wₜ₋₁₅)
    [.load .d T1 .a3 (slot (t + 1))] ++ ssig T2 T3 T1 1 8 7 ++ [.add T0 T0 T2] ++
    -- T0 := T0 + Wₜ₋₁₆
    [.load .d T2 .a3 (slot t), .add T0 T0 T2, .store .d T0 .a3 (slot t)]

/-- Round `t`, with `Wₜ` in `T0`. The additions are in the order of the
specification. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  -- h := h + Σ₁(e)
  bsig false T1 T2 e 14 18 41 ++ [.add h h T1,
    -- h := h + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g
    .logic .xor T1 f g, .logic .and T1 T1 e, .logic .xor T1 T1 g, .add h h T1] ++
  -- h := h + Kₜ + Wₜ, which is T₁
  li64 T1 T2 (K t) ++ [.add h h T1, .add h h T0,
    -- e' := d + T₁
    .add d d h] ++
  -- h := h + Σ₀(a)
  bsig true T1 T2 a 28 34 39 ++ [.add h h T1,
    -- h := h + Maj(a, b, c), as ((a ∨ b) ∧ c) ∨ (a ∧ b); now h = a' = T₁ + T₂
    .logic .or T1 a b, .logic .and T1 T1 c, .logic .and T2 a b, .logic .or T1 T1 T2,
    .add h h T1]

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- Load the hash value (`80 % 8 = 0`, so the variables are in the same
registers after the 80 rounds). -/
def load : List Instr := (List.range 8).flatMap fun k => loadLE64 (var 0 k) T0 T1 .a0 (8 * k)

/-- Add word `k` of the hash value into its working variable, and store the
result. -/
def updateW (k : Nat) : List Instr :=
  loadLE64 T0 T1 T2 .a0 (8 * k) ++ [.add (var 0 k) (var 0 k) T0] ++ storeLE64 (var 0 k) T0 T1 .a0 (8 * k)

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addi .a1 .a1 128, .addi .a2 .a2 (-1)]

/-- One block. -/
def body : Prog isa :=
  .seq (.block load) (.seq (rounds 80) (.block ((List.range 8).flatMap updateW ++ advance)))

/-- The blocks. -/
def blocks : Prog isa := .ite (.zero .a2) (.block []) (.loop body (.nonzero .a2))

def compress : Prog isa := .seq (.block save) (.seq blocks (.block restore))

end VG.Impl.Sha512.RISCV64
