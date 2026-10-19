module

public import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
public import VerifiedGarbage.Impl.MlKem.AArch64.ReadonlyDecrypt
public import VerifiedGarbage.Impl.MlKem.AArch64.Dot
public import VerifiedGarbage.Impl.MlKem.AArch64.Encaps
public import VerifiedGarbage.Impl.MlKem.AArch64.Decaps

/-! # Paired sampling and fused polynomial products for AArch64 ML-KEM

The hardware-SHA3 path samples independent noise streams in pairs, retains
error polynomials at the end of scratch, and reduces a complete polynomial
dot product after accumulating its terms. Public and private key decoding
reuse the consumed first matrix row; decapsulation rebuilds the matrix
before re-encryption.
-/

@[expose] public section
namespace VG.Impl.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Dot VG.Impl.MlKem.AArch64.Noise

def decryptM (L : KemLay) : Prog isa :=
 seqs (((List.range L.k).map (readonlyDeU L)) ++ ((List.range L.k).map fun j => dec12At .x25 (384*j) (KEM.aOff L 0 j)) ++
 [dot (KEM.TP L) ((List.range L.k).map fun j => (KEM.aOff L 0 j,KEM.yOff L j)),
 Ntt16.Readonly.nttInvAt (KEM.TP L),L.ddLAt .x26 (32*L.du*L.k) L.dv (KEM.EP L),subAt (KEM.EP L) (KEM.TP L),ceAt (KEM.EP L) 1 .x28 KEM.MB])
def deStart (callee : Impl.Sha3.AArch64.Callee) (L : KemLay) : Prog isa :=
 seqs [.block (L.kemPrologue 3 [0,1,2,3]),decryptM L,
 hashWith callee .x28 KEM.ST KEM.WK 72 6 [⟨.x28,KEM.MB,32⟩,⟨.x25,768*L.k+32,32⟩]
 [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩],.block (copy32 .x25 (768*L.k) .x28 KEM.SB)]
end VG.Impl.MlKem.AArch64.Optimized
