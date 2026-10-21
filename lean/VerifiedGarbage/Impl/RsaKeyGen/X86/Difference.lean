module

public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # Constant-time absolute difference of a candidate and the optional prime

Two native subtraction chains produce both directions. The first borrow
mask is retained in ESI and selects the nonnegative direction into `out`.
This reuses the verified native chains without candidate-dependent control.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Difference
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

def code (n out tmp a b : Nat) : Prog isa :=
  .seq (chainW .sbb n out a b) <|
  .seq (.block [.mov .esi (.reg .ecx)]) <|
  .seq (chainW .sbb n tmp b a) <|
  .seq (.block [.mov .ecx (.reg .esi)]) (selectsW n out tmp out)

end VG.Impl.RsaKeyGen.X86.Difference
