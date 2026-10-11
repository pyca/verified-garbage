module

public import VerifiedGarbage.Impl.Ed25519.X86_64.CombIfma
public import VerifiedGarbage.Impl.Ed25519.X86_64.Verify

/-!
# Ed25519 verification's windows with AVX512_IFMA

`Ifma.windows` runs verification's windows (`windows`: a doubling and the digits at
each position, from the top) with the accumulated point `(X, Y, Z, T)` in the four lanes of
`ymm0–ymm4` throughout, as five limbs of 51 bits, rather than in slots 0–3:

* each doubling is `vdbl`, the comb's (`Ifma.combMultiply`);
* a nonzero digit's table entry, cached as `[Y - X, Y + X, 2dT, 2Z]` (the
  table of `±[j]A` at byte 5376 and the static of `∓[j]B` are already in that
  form), is loaded a row of words at a time into `ymm11–ymm14` (`vrows`),
  split into the limbs of the lanes of `ymm5–ymm9` (`esplit`) and added with
  the comb's two four-lane products (`vadd`);
* the digits, the counter and the branches are `windows'`.

The point goes into the lanes once, before the windows (`vload`, which also
stores the constants), and back into slots 0–3 once, after them (`vstore`);
the windows and `vstore` run between Intel's MXCSR prologue and epilogue
(`withMx`), and nothing in them writes `r11`, which holds the saved MXCSR.
-/

@[expose] public section

namespace VG.Impl.Ed25519.X86_64.Ifma

open VG.X86_64
open VG.Impl.X25519.X86_64 (at_)
open VG.Impl.X25519.X86_64.Ifma (y)
open VG.Impl.Ed25519.X86_64 (tableAddr baseAddr batchBegin batchTest digitAt skipTop)

/-- The four rows of the table entry at `rax` into `ymm11–ymm14`. -/
def vrows : List Instr :=
  (List.range 4).map fun j => .vmovdquLoad .l256 (y (11 + j)) (at_ .rax (32 * j))

/-- Entry `rbx - 1` of the table at byte `o` added to the point in the lanes, unless `rbx` is
zero. -/
def vaddDigit (o : Nat) : Prog isa :=
  .ite .ne (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr o ++ vrows ++ esplit ++ vadd))
    (.block [])

/-- `-[d]B`, entry `rbx - 1` of the static, added to the point in the lanes, unless `rbx` is
zero. -/
def vaddBase : Prog isa :=
  .ite .ne (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ baseAddr ++ vrows ++ esplit ++ vadd))
    (.block [])

/-- The digits at the counter's position added to the point in the lanes. -/
def vaddsAt : Prog isa :=
  .seq (.block (digitAt 0)) (.seq (vaddDigit 5376) (.seq (.block (digitAt 1)) vaddBase))

/-- The position below: the counter moved down, a doubling and its digits. -/
def vstepAt : Prog isa :=
  .seq (.block batchBegin) (.seq (.block vdbl) (.seq vaddsAt (.block batchTest)))

/-- Verification's windows with the point in the lanes, from slots 0–3 back to them. -/
def windows : Prog isa :=
  .seq (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload))
    (withMx (.seq (.loop skipTop .ne) (.seq vaddsAt (.seq (.block batchTest)
      (.seq (.ite .ne (.loop vstepAt .ne) (.block [])) (.block vstore))))))

end VG.Impl.Ed25519.X86_64.Ifma
