module

public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnAdx

/-! # Prune the unused operation of an inlined Montgomery kernel

The operand indices are constants at an inline call site. Retain the
kernel's instructions and branch, but omit the branch it cannot take.
The separately callable Montgomery kernel remains unchanged.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86_64.MontFnSpecialized
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.MontFn

def tiled (a b : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .rcx (.reg .r8)])
    (.seq (.ite .e
      (if a = b then AdxTiledSquare.rawSquareBare xA else .block [])
      (if a = b then .block [] else AdxTiledProduct.rawProductBare xA xB))
      (AdxTiledProduct.redcFinish xO))

def body (a b : Nat) : Prog isa :=
  .seq (.block alignTest)
    (.ite .e (tiled a b)
      (.seq (.block basesR) (.seq zeroAccLoop (.seq rounds (.seq subMod selectAcc)))))

def mm (o a b : Nat) : Prog isa :=
  .seq (.block (args o a b))
    (.seq (.block (enter ++ slotsIn)) (.seq (body a b) (.block restore)))

end VG.Impl.Bignum.X86_64.MontFnSpecialized
