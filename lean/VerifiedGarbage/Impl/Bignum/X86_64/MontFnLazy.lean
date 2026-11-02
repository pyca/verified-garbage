module

public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnAdx
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxLazy8

/-!
# Lazy Montgomery multiplication as a function (x86-64)

`vg_rsa_lazy_mont_mul(ws, ws_len, o, a, b)` (`Proof.Rsa.Mont.mulLazyContract`):
the baseline is `vg_rsa_mont_mul`'s code, whose subtraction of `m` when it
does not borrow leaves its result below `R` for any operands below `R`.
`vg_rsa_lazy_mont_mul_adx` is `vg_rsa_mont_mul_adx` with the tiles' final
subtraction of `m` masked by the reduction's top word (`Adx.lazy8`), in one
pass.
-/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.MontFn

open VG.X86_64 VG.Impl.Bignum.X86_64.Public

/-- `tiled` with the lazy final subtraction. -/
def tiledLazy : Prog isa :=
  .seq (.block [.alu .cmp .rcx (.reg .r8)])
    (.seq (.ite .e (AdxTiledSquare.rawSquareBare xA) (AdxTiledProduct.rawProductBare xA xB))
      (AdxTiledProduct.redcLazy xO))

/-- `adxBody` with the lazy tiles. -/
def adxBodyLazy : Prog isa :=
  .seq (.block alignTest)
    (.ite .e tiledLazy (.seq (.block basesR) (.seq zeroAccLoop (.seq rounds (.seq subMod selectAcc)))))

/-- `vg_rsa_lazy_mont_mul_adx`. -/
def mulAdxLazy : Prog isa :=
  .seq (.block (enter ++ slotsIn)) (.seq adxBodyLazy (.block restore))

end VG.Impl.Bignum.X86_64.MontFn
