module

public import VerifiedGarbage.Impl.Bignum.X86.PublicRt
public import VerifiedGarbage.Impl.Bignum.X86.R2Words

/-! # Public RSA modulus precomputation on i686, at a width read at run time

`vg_rsa_public_precompute` without a copy per width: once the modulus is
checked, `pre_len` (argument 1) is overwritten with `n_len` (argument 3), the
argument from which `PublicRt`'s loops read the width `B = 8 ⌈n_len / 8⌉` of
every number, so that its pieces serve here: the numbers are at `256 + j B`
in the working space (`edi`), the modulus `M` number 0 and the power of two
number 4, and the range of `vg_rsa_mont_mul_at` from `256 + 5 B`.

`R² mod M`, for `R = 2^(8 B)`: number 4 set to `2^(10 B) mod M` by word
steps (`R2Words.run`), then two Montgomery squares, by calls of
`vg_rsa_mont_mul_at`, double the exponent of two above `R` each time, to
`R 2^(8 B) = R²`. Then `M` and `R² mod M` are copied to `pre`. Only the
public modulus and its length choose branches.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.PrecomputeFn
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Impl.Bignum.X86.PublicRt (argAt widthB slotPtr zero load invOff numOff)

def entry : List Instr :=
  [.mov .eax (.mem (PublicFn.argument 4))] ++ PublicFn.save ++ [.mov .edi (.reg .eax)]

def failure : Prog isa :=
  .seq (.block [.mov .esi (.mem (PublicFn.argument 0)),
    .mov .ecx (.mem (PublicFn.argument 1)), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .mov .eax (.imm 0)])
    (.loop (.block PublicFn.clearStep) .ne)

/-- Argument 1 set to `n_len`. -/
def setWidth : List Instr := [.mov .eax (.mem (argAt 0 3)), .store (argAt 0 1) .eax]

/-- Two Montgomery squares of number 4, `esi` counting them. -/
def squares : Prog isa :=
  .seq (.block [.mov .esi (.imm 2)])
    (.loop (.seq (PublicRt.mul 4 4 4 5) (.block [.alu .sub .esi (.imm 1)])) .ne)

/-- Number `j` to the words at `pre` (argument 0), `B` bytes into it when `hi`. -/
def copyOut (j : Nat) (hi : Bool) : Prog isa :=
  .seq (.block (slotPtr .esi j .ecx ++ .mov .ebp (.mem (argAt 0 0)) ::
      (if hi then [.alu .add .ebp (.reg .ecx)] else [])))
    (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 4)]) .ne)

/-- The modulus read, `-M⁻¹ mod 2³²` at 152, and number 4 set to `2^(10 B) mod M`. -/
def start : Prog isa :=
  .seq (load 0 2 3) <|
  .seq (.block (VG.Impl.Mont.X86.Dynamic.setupInverse numOff invOff)) R2Words.run

/-- `M` and `R² mod M` to `pre`, and 1 returned. -/
def finish : Prog isa :=
  .seq (copyOut 0 false) (.seq (copyOut 4 true) (.block [.mov .eax (.imm 1)]))

/-- `R² mod M` from the modulus and its length, and both to `pre`. -/
def compute : Prog isa := .seq start (.seq squares finish)

/-- The computation, once the modulus is known valid. -/
def valid : Prog isa := .seq (.block setWidth) compute

def body : Prog isa :=
  .seq (.block PublicFn.modulusArgs) (.seq (.block modulusCheck) (.ite .e valid failure))

def code : Prog isa := .seq (.block entry) (.seq body (.block PublicFn.restore))

end VG.Impl.Bignum.X86.PrecomputeFn
