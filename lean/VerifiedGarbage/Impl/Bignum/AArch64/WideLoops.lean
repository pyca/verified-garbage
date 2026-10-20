module

public import VerifiedGarbage.Impl.Bignum.AArch64.DiagonalChain

@[expose] public section

namespace VG.Impl.Bignum.AArch64.WideLoops
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
def zero : Prog isa :=
 .seq (.block [mov .x16 .x8, .add .x .x14 .x12 .x12, .lsr .x .x14 .x14 3])
 (.seq (countLoop .x14 ((List.range 8).map (fun i => st .x7 .x16 (8*i)) ++ [.addImm .x .x16 .x16 64]))
  (.block [st .x7 .x16, st .x7 .x16 8]))
end VG.Impl.Bignum.AArch64.WideLoops

namespace VG.Impl.Bignum.AArch64.WideLoops
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
def diagonal : Prog isa := DiagonalChain.code

end VG.Impl.Bignum.AArch64.WideLoops
