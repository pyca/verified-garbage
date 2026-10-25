module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Multiword arithmetic in RISC-V code

Instruction sequences for numbers of several 64-bit words, which RISC-V
computes without a carry flag: the carry out of `d := d + x` is
`sltu c, d, x` (the sum wrapped around if and only if it is less than an
addend), and a 128-bit product is `mul` (its low word) and `mulhu` (its high
word). Their lemmas are in `Proof/Framework/RISCV64/Wide.lean`:
* `mulWide`: a product of two words, as two words;
* `add2`: a two-word number added to another, modulo `2¹²⁸`;
* `mulAdd`, `mulAddSmall`: a product added to a two-word number;
* `add3`: a two-word number added to a three-word one;
* `addW3`: a word added to a three-word number, into other registers.
-/

@[expose] public section

namespace VG.Impl.Words.RISCV64

open VG.RISCV64

/-- `lo + 2⁶⁴ hi := a · b`. `lo` is neither `a` nor `b`. -/
def mulWide (lo hi a b : Reg) : List Instr := [.mul lo a b, .mulhu hi a b]

/-- `lo + 2⁶⁴ hi += x + 2⁶⁴ y`, modulo `2¹²⁸`; `x` is clobbered (it holds
the carry). -/
def add2 (lo hi x y : Reg) : List Instr :=
  [.add lo lo x, .sltu x lo x, .add hi hi y, .add hi hi x]

/-- `lo + 2⁶⁴ hi += a · b`, through `t₁` and `t₂` (the product's words). -/
def mulAdd (lo hi t₁ t₂ a b : Reg) : List Instr := mulWide t₁ t₂ a b ++ add2 lo hi t₁ t₂

/-- `lo + 2⁶⁴ hi += a · b`, for a product less than `2⁶⁴`, through `t`. -/
def mulAddSmall (lo hi t a b : Reg) : List Instr :=
  [.mul t a b, .add lo lo t, .sltu t lo t, .add hi hi t]

/-- `w₀ + 2⁶⁴ w₁ + 2¹²⁸ w₂ += x₀ + 2⁶⁴ x₁`, modulo `2¹⁹²`; `x₀` and `x₁` are
clobbered (they hold the carries). -/
def add3 (w₀ w₁ w₂ x₀ x₁ : Reg) : List Instr :=
  [.add w₀ w₀ x₀, .sltu x₀ w₀ x₀, .add w₁ w₁ x₁, .sltu x₁ w₁ x₁, .add w₁ w₁ x₀,
    .sltu x₀ w₁ x₀, .add w₂ w₂ x₁, .add w₂ w₂ x₀]

/-- `d₀ + 2⁶⁴ d₁ + 2¹²⁸ d₂ := a₀ + 2⁶⁴ a₁ + 2¹²⁸ a₂ + t`, modulo `2¹⁹²`; `t` is
clobbered (it holds the carries). `d₀` is neither `a₁` nor `a₂`, and `d₁` is not
`a₂`. -/
def addW3 (d₀ d₁ d₂ a₀ a₁ a₂ t : Reg) : List Instr :=
  [.add d₀ a₀ t, .sltu t d₀ t, .add d₁ a₁ t, .sltu t d₁ t, .add d₂ a₂ t]

end VG.Impl.Words.RISCV64
