module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64
open VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

def canonicalizeZ (p : Params) (r : Nat) : Prog isa :=
  callAt "vg_mldsa_canonicalize_signed" VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize
    [(.x0,.ptr (yP p r))]

/-- Only the accepted response is converted for the existing signature packer. -/
def output (P : Prims) (p : Params) : Prog isa :=
  .seq (seqR (canonicalizeZ p) 0 p.ℓ) (VG.Impl.MlDsa.AArch64.Sign.output P p)

end VG.Impl.MlDsa.AArch64.Sign.Optimized
