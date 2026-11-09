module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # `vg_dsa_parameter_search_init` on AArch64

`vg_dsa_parameter_search_init(state = x0, p_len = x1)`
(`VG.Spec.Dsa.parameterInit`): for a supported width `p_len` (128, 256 or
384, tested in turn), the seeds the search may reject (4096), `p_len`, the
entropy budget `32769 p_len` and the first tape's length `512 p_len`, and 1
returned; otherwise four zeros and 0 returned. `p_len` is public. -/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.ParameterSearch

open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- The four words for the width in `x1`, and 1 returned. -/
def initWords : List Instr := [
  movi .x9 4096, st .x9 .x0 0, st .x1 .x0 8, .lsl .x .x10 .x1 15, .add .x .x10 .x10 .x1, st .x10 .x0 16,
  .lsl .x .x10 .x1 9, st .x10 .x0 24, movi .x0 1]

/-- Zeros to the four words, and 0 returned. -/
def clear : List Instr := [
  movi .x9 0, st .x9 .x0 0, st .x9 .x0 8, st .x9 .x0 16, st .x9 .x0 24, movi .x0 0]

/-- `x9` zero exactly when `x1` is `n`. -/
def test (n : Nat) : List Instr := [.subImm .x .x9 .x1 n]

def init : Prog isa :=
  .seq (.block (test 128)) (.ite (.zero .x .x9) (.block initWords)
    (.seq (.block (test 256)) (.ite (.zero .x .x9) (.block initWords)
      (.seq (.block (test 384)) (.ite (.zero .x .x9) (.block initWords) (.block clear))))))

end VG.Impl.Dsa.AArch64.ParameterSearch
