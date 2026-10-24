module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Generation.Init

/-! # Native FFDH key generation on PPC64LE: validation and rejection budgets

`vg_ffdh_key_generation_init(state = r3, p_len = r4)`: `p_len` is first
checked to be below `2^11` (its bits from 11 up zero), a branch on a public
value; then `r12 := lt 1025 − lt 64` (`Generation.lt`, sign bits of
differences), 1 exactly when `64 ≤ p_len ≤ 1024`; then both budgets 128,
the width and the first request `p_len`, and 1 returned, or zeros to the
four public words and 0 returned.
-/

@[expose] public section

namespace VG.Impl.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.Generation (lt clear)

/-- `r12 := p_len >> 11`, zero exactly for `p_len < 2^11`. -/
def high : List Instr := [.lsr .d .r12 .r4 11]

/-- With `p_len < 2^11`: `r12 := 1` exactly when `64 ≤ p_len ≤ 1024`, else 0. -/
def validate : List Instr := lt .r10 .r4 64 ++ lt .r11 .r4 1025 ++ [.sub .r12 .r11 .r10]

/-- Both budgets 128, the width and the first request `p_len`, and 1 returned. -/
def initializeState : List Instr := [
  .li .r9 128, .store .d .r9 .r3 0, .store .d .r9 .r3 8, .store .d .r4 .r3 16, .store .d .r4 .r3 24,
  .li .r3 1]

def init : Prog isa :=
  .seq (.block high)
    (.ite (.zero .d .r12)
      (.seq (.block validate) (.ite (.zero .d .r12) (.block clear) (.block initializeState)))
      (.block clear))

end VG.Impl.Ffdh.PPC64LE.KeyGeneration
