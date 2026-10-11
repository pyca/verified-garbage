module

public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MatrixMask

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call

def matrixGroup (P : Prims) (p : Spec.MlDsa.Params) (g : Nat) : Prog isa :=
  .seq (seqR (fun j => .block (setSR p (4*g) j)) 0 4)
    (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g)))
      (.seq (.block and24) (Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (4*g)) 1024)))

def matrixTwo (cd : Prog isa) (p : Spec.MlDsa.Params) (e : Nat) : Prog isa :=
  .seq (seqR (fun j => .block (setSR p e j)) 0 2)
    (.seq (callAt "vg_mldsa_rej_ntt_poly2_sha3" cd
      [(.x0,.ptr (sc oSA4)),(.x1,.ptr (aP e)),(.x2,.ptr (sc (oR4 p)))])
      (.seq (.block and24) (Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP e) 512)))

def matrixWith (cd : Prog isa) (P : Prims) (p : Spec.MlDsa.Params) : Prog isa :=
  let e:=4*(p.k*p.ℓ/4)
  .seq (.block ((List.range 4).flatMap copySeed4))
    (.seq (seqR (matrixGroup P p) 0 (p.k*p.ℓ/4))
      (if p.k*p.ℓ%4=2 then matrixTwo cd p e else seqR (expA P p) e (p.k*p.ℓ%4)))

end VG.Impl.MlDsa.AArch64.KeyGen.Optimized
