module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Impl.MlKem.AArch64.Ops16
import VerifiedGarbage.Impl.MlKem.AArch64.Noise

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
open VG.Impl.MlKem.AArch64.Noise

/-- Row `i` of `u`: decoded and decompressed with 32 bits into `PP`, narrowed to 16 bits at
`yOff i` and transformed by `vg_mlkem16_ntt`. -/
def deU (L : KemLay) (i : Nat) : Prog isa :=
 seqs [L.ddLAt .x26 (32*L.du*i) L.du (KEM.PP L),Kem16.narrowAt (KEM.PP L) (KEM.yOff L i),
  Ntt16.Readonly.nttAtWithW (KEM.yOff L i) KEM.NS]
/-- `m = Compress₁(v - NTT⁻¹(ŝᵀ ∘ û))`, with `ŝ` and `û` stored with 16 bits: the dot product
and the inverse transform in 16 bits, widened into `PP` for the subtraction from `v`. -/
def decryptM (L : KemLay) : Prog isa :=
 seqs (((List.range L.k).map (deU L)) ++ ((List.range L.k).map fun j => Kem16.dec12WAt .x25 (384*j) (KEM.aOff L 0 j)) ++
 [Kem16.dotAt (KEM.TP L) ((List.range L.k).map fun j => (KEM.aOff L 0 j,KEM.yOff L j)),
 Ntt16.Readonly.nttInvAtWithW (KEM.TP L) KEM.NS,Kem16.widenAt (KEM.TP L) (KEM.PP L),
 L.ddLAt .x26 (32*L.du*L.k) L.dv (KEM.EP L),subAt (KEM.EP L) (KEM.PP L),ceAt (KEM.EP L) 1 .x28 KEM.MB])
def deStart (callee : Impl.Sha3.AArch64.Callee) (L : KemLay) : Prog isa :=
 seqs [.block (L.kemPrologue 3 [0,1,2,3]),decryptM L,
 hashWith callee .x28 KEM.ST KEM.WK 72 6 [⟨.x28,KEM.MB,32⟩,⟨.x25,768*L.k+32,32⟩]
 [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩],.block (copy32 .x25 (768*L.k) .x28 KEM.SB)]
end VG.Impl.MlKem.AArch64.Optimized
