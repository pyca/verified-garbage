module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejTwo

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call

def tail (p : Params) : Prog isa :=
  .seq (seqR (seedSlot4 p (4*(p.k*p.ℓ/4))) 0 2)
    (.seq (callAt "vg_mldsa_rej_ntt_poly2_sha3" Optimized.ResidentRej.Two.code
      [(.x0,.ptr (sc oRS4)),(.x1,.ptr (pS (5+4*p.k+3*p.ℓ+4*(p.k*p.ℓ/4)))),
        (.x2,.ptr (sc (oR4 p)))]) (.block and24))

def expandA (P : Prims) (p : Params) : Prog isa :=
  if p.k*p.ℓ%4=2 then
    .seq (.block (Impl.MlKem.AArch64.copy32 .x25 0 .x28 oRS))
      (.seq (seqR (sample4 P p) 0 (p.k*p.ℓ/4)) (tail p))
  else Sign.expandA P p

end VG.Impl.MlDsa.AArch64.Sign.CachedMatrix
