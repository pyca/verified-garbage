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

def vRest (callee : Impl.Sha3.AArch64.Callee) (L : KemLay) (ek : Reg) (eo : Nat) (m : Reg) (mo : Nat) (ct : Reg) (co : Nat) : Prog isa :=
 seqs (((List.range L.k).map fun j => dec12At ek (eo+384*j) (KEM.aOff L 0 j)) ++
 [dot (KEM.TP L) ((List.range L.k).map fun j => (KEM.aOff L 0 j,KEM.yOff L j)),
 Ntt16.Readonly.nttInvAt (KEM.TP L),prfCbdWith callee (2*L.k) (KEM.EP L),addAt (KEM.TP L) (KEM.EP L),
 ddAt m mo 1 (KEM.EP L),addAt (KEM.TP L) (KEM.EP L),L.ceLAt (KEM.TP L) L.dv ct (co+32*L.du*L.k)])
def decryptM (L : KemLay) : Prog isa :=
 seqs (((List.range L.k).map (readonlyDeU L)) ++ ((List.range L.k).map fun j => dec12At .x25 (384*j) (KEM.aOff L 0 j)) ++
 [dot (KEM.TP L) ((List.range L.k).map fun j => (KEM.aOff L 0 j,KEM.yOff L j)),
 Ntt16.Readonly.nttInvAt (KEM.TP L),L.ddLAt .x26 (32*L.du*L.k) L.dv (KEM.EP L),subAt (KEM.EP L) (KEM.TP L),ceAt (KEM.EP L) 1 .x28 KEM.MB])
def deStart (callee : Impl.Sha3.AArch64.Callee) (L : KemLay) : Prog isa :=
 seqs [.block (L.kemPrologue 3 [0,1,2,3]),decryptM L,
 hashWith callee .x28 KEM.ST KEM.WK 72 6 [⟨.x28,KEM.MB,32⟩,⟨.x25,768*L.k+32,32⟩]
 [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩],.block (copy32 .x25 (768*L.k) .x28 KEM.SB)]
def kgRow (L : KemLay) (i : Nat) : Prog isa :=
 seqs [dot (KG.TP L) ((List.range L.k).map fun j => (KG.aOff L i j,KG.sOff L j)),
  addAt (KG.TP L) (noiseOff L i),kgEnc (KG.TP L) .x26 (384*i),
  kgEnc (KG.TP L) .x27 (384*L.k+384*i)]
def kgRest (callee : Impl.Sha3.AArch64.Callee) (L : KemLay) : Prog isa :=
 .seq (noiseAllWith Ntt16.Readonly.nttAtWith L true) (seqs (
  ((List.range L.k).map fun j => kgEnc (KG.sOff L j) .x27 (384*j)) ++
  ((List.range L.k).map fun i => kgRow L i) ++
  [L.kgEndWith callee]))
def uRow (L : KemLay) (ct : Reg) (co i : Nat) : Prog isa :=
 seqs [dot (KEM.TP L) ((List.range L.k).map fun j => (KEM.aOff L j i,KEM.yOff L j)),
  Ntt16.Readonly.nttInvAt (KEM.TP L),addAt (KEM.TP L) (noiseOff L i),L.ceLAt (KEM.TP L) L.du ct (co+32*L.du*i)]
def encryptRest (callee : Impl.Sha3.AArch64.Callee) (L : KemLay) (ek : Reg) (eo : Nat) (m : Reg) (mo : Nat) (ct : Reg) (co : Nat) : Prog isa :=
 .seq (noiseAllWith Ntt16.Readonly.nttAtWith L false) (seqs (((List.range L.k).map (uRow L ct co)) ++
  [vRest callee L ek eo m mo ct co]))
def enRest (callee : Impl.Sha3.AArch64.Callee) (L : KemLay) : Prog isa :=
 .seq (encryptRest callee L .x25 0 .x28 KEM.MB .x27 0) (.block L.kemEpilogue)
def deRest (callee : Impl.Sha3.AArch64.Callee) (L : KemLay) : Prog isa :=
 seqs [encryptRest callee L .x25 (384*L.k) .x28 KEM.MB .x28 (KEM.CB L),
  hashWith callee .x28 KEM.ST KEM.WK 136 0x1f [⟨.x25,768*L.k+64,32⟩,⟨.x26,0,L.ctLen⟩] [⟨.x28,KEM.JB,32⟩],
  L.deCmp,.block (deSel ++ L.kemEpilogue)]

def keyGenWith (c : Impl.Sha3.AArch64.Callee) (L : KemLay) : Prog isa :=
 .seq (L.kgAWith c) (.seq (Paired.matrix L true) (kgRest c L))
def encapsWith (c : Impl.Sha3.AArch64.Callee) (L : KemLay) : Prog isa :=
 .seq (L.enAWith c) (.seq (Paired.matrix L false) (enRest c L))
def decapsWith (c : Impl.Sha3.AArch64.Callee) (L : KemLay) : Prog isa :=
 .seq (deStart c L) (.seq (Paired.matrix L false) (deRest c L))

end VG.Impl.MlKem.AArch64.Optimized
