module

public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy

/-!
# `k` lazy Montgomery squarings as a function (x86-64)

`vg_rsa_lazy_mont_sqr(ws, ws_len, o, a, k)` and `vg_rsa_lazy_mont_sqr_adx`
(`Spec.Rsa.Mont.sqrLazyContract`): the lazy multiplication's code with both
operands the same, in a loop, so that `k` squarings pay one call's entry and
exit. The first squaring reads `a`, the others `o`.

The ADX function enters as `vg_rsa_lazy_mont_mul_adx` would for `(o, a, a)`
(`slotsIn` saves header words 16–21 first), keeps the count of squarings done,
`k` and `o` in header words 19–21 (`sFn 3`–`sFn 5`), which it writes back
from `xmm4` and `xmm5` before it returns, and after each squaring points the
slots of `xA` and `xB` at `o`'s array. The baseline keeps them there too, saved
and written back the same way.
-/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.MontFn

open VG.X86_64 VG.Impl.Bignum.X86_64.Public

/-- `k` (in `r8`) into `r9`, and `a` (in `rcx`) into `r8`, as the second operand. -/
def sqrArgs : List Instr := [.mov .r9 (.reg .r8), .mov .r8 (.reg .rcx)]

/-- The count `0`, `k` and `o` into header words 19–21. -/
def sqrInit : List Instr :=
  [.mov32 .rax (.imm 0), .store (hdr (sFn 3)) .rax, .store (hdr (sFn 4)) .r9, .store (hdr (sFn 5)) .rdx]

/-- After a squaring: `o` in `rdx`, `rcx` and `r8`; the count plus one, ZF set
when it is `k`. -/
def sqrCount : List Instr :=
  [.mov .rdx (.mem (hdr (sFn 5))), .mov .rcx (.reg .rdx), .mov .r8 (.reg .rdx),
    .mov .rax (.mem (hdr (sFn 3))), .alu .add .rax (.imm 1), .store (hdr (sFn 3)) .rax,
    .alu .cmp .rax (.mem (hdr (sFn 4)))]

/-- After an ADX squaring: `sqrCount`, and the slots of `xA` and `xB` at `o`'s array. -/
def sqrNextAdx : List Instr :=
  [.mov .rax (.mem (hdr (sArr xO))), .store (hdr (sArr xA)) .rax, .store (hdr (sArr xB)) .rax] ++ sqrCount

/-- `vg_rsa_lazy_mont_sqr_adx`. -/
def sqrAdxLazy : Prog isa :=
  .seq (.block (zext ++ sqrArgs ++ saves ++ slotsIn ++ sqrInit))
    (.seq (.loop (.seq adxBodyLazy (.block sqrNextAdx)) .ne) (.block restore))

/-- The baseline's head: header words 18–21 into `xmm4` and `xmm5`. -/
def sqrSaveHdr : List Instr := [.movdquLoad .xmm4 (hdr (sFn 2)), .movdquLoad .xmm5 (hdr (sFn 4))]

/-- The baseline's tail: the callee-saved registers, and header words 18–21 back. -/
def sqrRestore : List Instr :=
  unsaves ++ ([.movdquStore (hdr (sFn 2)) .xmm4, .movdquStore (hdr (sFn 4)) .xmm5] : List Instr)

/-- `vg_rsa_lazy_mont_sqr`. -/
def sqrBaseLazy : Prog isa :=
  .seq (.block (zext ++ sqrArgs ++ saves ++ sqrSaveHdr ++ sqrInit))
    (.seq (.loop (.seq (.block basesR) (.seq (.seq zeroAccLoop (.seq rounds (.seq subMod selectAcc)))
      (.block sqrCount))) .ne) (.block sqrRestore))

end VG.Impl.Bignum.X86_64.MontFn
