module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedDecode

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Spec.MlDsa

def positiveDecodeSecrets (P : Prims) (p : Params) : Prog isa :=
  .seq (seqR (fun r => positiveDecode P (.x25,skS1 p r) (sLen p) p.η p.η
    (5+2*p.k+2*p.ℓ+r)) 0 p.ℓ)
    (.seq (seqR (fun i => positiveDecode P (.x25,skS2 p i) (sLen p) p.η p.η
      (5+2*p.k+3*p.ℓ+i)) 0 p.k)
      (seqR (fun i => positiveDecode P (.x25,skT0 p i) 416 4095 4096
        (5+3*p.k+3*p.ℓ+i)) 0 p.k))

def positiveDecodeWith (c : VG.Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .seq (positiveDecodeSecrets P p)
    (shakeAtWith c [⟨.x25,32,32⟩,⟨.x27,0,32⟩,⟨.x26,0,64⟩] ⟨.x28,oMS,64⟩)

end VG.Impl.MlDsa.AArch64.Sign
