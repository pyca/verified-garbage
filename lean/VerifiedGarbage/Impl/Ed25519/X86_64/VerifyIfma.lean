import VerifiedGarbage.Impl.Ed25519.X86_64.CombIfma
import VerifiedGarbage.Impl.Ed25519.X86_64.Verify

/-!
# Ed25519 verification's windows with AVX512_IFMA

`Ifma.windows` runs verification's windows (`windows`: those of `k` alone,
then those of both scalars, a byte at a time, high nibble first) with the
accumulated point `(X, Y, Z, T)` in the four lanes of `ymm0–ymm4`
throughout, as five limbs of 51 bits, rather than in slots 0–3:

* the four doublings of a window are `vdbl4`'s, as the comb's
  (`Ifma.combMultiply`);
* a nonzero digit's table entry, cached as `[Y - X, Y + X, 2dT, 2Z]` (the
  tables of `[j]A` and `-[j]B`, at bytes 5376 and 2048, are already in that
  form), is loaded a row of words at a time into `ymm11–ymm14` (`vrows`),
  split into the limbs of the lanes of `ymm5–ymm9` (`esplit`) and added with
  the comb's two four-lane products (`vadd`);
* the digits, the byte counter and the branches are `windows`'.

The point goes into the lanes once, before the windows (`vload`, which also
stores the constants), and back into slots 0–3 once, after them (`vstore`);
the windows and `vstore` run between Intel's MXCSR prologue and epilogue
(`withMx`), and nothing in them writes `r11`, which holds the saved MXCSR.
-/

namespace VG.Impl.Ed25519.X86_64.Ifma

open VG.X86_64
open VG.Impl.X25519.X86_64 (at_)
open VG.Impl.X25519.X86_64.Ifma (y)
open VG.Impl.Ed25519.X86_64 (tableAddr batchBegin batchTest digitHigh digitLow counterCmp)

/-- The four rows of the table entry at `rax` into `ymm11–ymm14`. -/
def vrows : List Instr :=
  (List.range 4).map fun j => .vmovdquLoad .l256 (y (11 + j)) (at_ .rax (32 * j))

/-- Entry `rbx - 1` of the table at byte `o` added to the point in the lanes, unless `rbx` is
zero. -/
def vaddDigit (o : Nat) : Prog isa :=
  .ite .ne (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr o ++ vrows ++ esplit ++ vadd))
    (.block [])

/-- A window of `k` alone. -/
def vwindowA (digit : List Instr) : Prog isa := .seq vdbl4 (.seq (.block digit) (vaddDigit 5376))

/-- A window of `k` and of `S`. -/
def vwindowAB (digitA digitB : List Instr) : Prog isa :=
  .seq (vwindowA digitA) (.seq (.block digitB) (vaddDigit 2048))

/-- A byte of `k` alone (bytes 63 down to 32). -/
def vbyteStepA : Prog isa :=
  .seq (.block batchBegin) (.seq (vwindowA (digitHigh 7952 0))
    (.seq (vwindowA (digitLow 7952 0)) (.block counterCmp)))

/-- A byte of `k` and of `S` (bytes 31 down to 0). -/
def vbyteStepAB : Prog isa :=
  .seq (.block batchBegin) (.seq (vwindowAB (digitHigh 7952 0) (digitHigh 7944 32))
    (.seq (vwindowAB (digitLow 7952 0) (digitLow 7944 32)) (.block batchTest)))

/-- The bytes of `k` alone that are left after `skipZero`. -/
def vwindowsA : Prog isa :=
  .seq (.block counterCmp) (.ite .ne (.loop vbyteStepA .ne) (.block []))

/-- Verification's windows with the point in the lanes, from slots 0–3 back to them. -/
def windows : Prog isa :=
  .seq (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload))
    (withMx (.seq vwindowsA (.seq (.loop vbyteStepAB .ne) (.block vstore))))

end VG.Impl.Ed25519.X86_64.Ifma
