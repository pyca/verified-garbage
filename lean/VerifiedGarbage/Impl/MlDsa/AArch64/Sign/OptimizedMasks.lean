import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Optimized

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

def maskR (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  .seq (.block (setKappa r)) (.seq (maskAt P p.γ₁ (yP p r)) (maskFinish p r))

def maskPairR (p : Params) (nm : String) (cd : Prog isa) (r : Nat) : Prog isa :=
  .seq (maskPairSeed r 0) (.seq (maskPairSeed r 1)
    (.seq (callAt nm cd [(.x0,.ptr (sc oMP)),(.x1,.imm p.γ₁),
      (.x2,.ptr (yP p r)),(.x3,.ptr (yP p (r+1))),(.x4,.ptr (sc (oR4 p)))])
      (.seq (maskFinish p r) (maskFinish p (r+1)))))

def masksPaired (P : Prims) (p : Params) (nm : String) (cd : Prog isa) : Prog isa :=
  .seq (seqR (fun j => maskPairR p nm cd (2*j)) 0 (p.ℓ/2))
    (seqR (maskR P p) (2*(p.ℓ/2)) (p.ℓ%2))

def masks (P : Prims) (p : Params) : Prog isa :=
  if P.pairedMask then masksPaired P p "vg_mldsa_expand_mask_pair_sha3" P.expandMaskPair
  else seqR (maskR P p) 0 p.ℓ

end VG.Impl.MlDsa.AArch64.Sign.Optimized
