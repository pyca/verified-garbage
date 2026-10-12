module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MatrixMask
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejTwo

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Optimized

def expA4 (P : Prims) (p : Params) (g : Nat) : Prog isa :=
  .seq (seqR (seedSlot4 p (4*g)) 0 4)
    (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g)))
      (.seq (.block and24) (MatrixMask.code (aP (4*g)) 1024)))

def tail2 (p : Params) : Prog isa :=
  .seq (seqR (seedSlot4 p (4*(p.k*p.ℓ/4))) 0 2)
    (.seq (callAt "vg_mldsa_rej_ntt_poly2_sha3" ResidentRej.Two.code
      [(.x0,.ptr (sc oSA4)),(.x1,.ptr (aP (4*(p.k*p.ℓ/4)))),(.x2,.ptr (sc (oR4 p)))])
      (.seq (.block and24) (MatrixMask.code (aP (4*(p.k*p.ℓ/4))) 512)))

def expAll (P : Prims) (p : Params) : Prog isa :=
  .seq (seqR (expA4 P p) 0 (p.k*p.ℓ/4))
    (if p.k*p.ℓ%4=2 then tail2 p else
      seqR (expA P p) (4*(p.k*p.ℓ/4)) (p.k*p.ℓ%4))

def samples (P : Prims) (p : Params) : Prog isa :=
  .seq (.block (Impl.MlKem.AArch64.copy32 .x25 0 .x28 oSA))
    (.seq (expAll P p) (.seq (ballAt P (sc oSS) (.x27,0) p.ctildeLen p.τ (cP p))
      (.seq (.block and24) (MatrixMask.code (cP p) 256))))

end VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples
