module
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
@[expose] public section
namespace VG.Impl.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64

def readonlyDeU (L : KemLay) (i : Nat) : Prog isa :=
 .seq (L.ddLAt .x26 (32*L.du*i) L.du (KEM.yOff L i)) (Ntt16.Readonly.nttAt (KEM.yOff L i))
end VG.Impl.MlKem.AArch64.Optimized
