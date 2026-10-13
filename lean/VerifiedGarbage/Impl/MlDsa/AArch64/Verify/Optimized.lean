module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontDot
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontProduct
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.AddSub
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.UseHintPack

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call
open VG.Impl.MlDsa.AArch64.Optimized

def forward (a : Ptr) : Prog isa :=
  callAt "vg_mldsa_ntt_positive" Ntt.staticNtt [(.x0,.ptr a)]

def inverse (a : Ptr) : Prog isa :=
  callAt "vg_mldsa_montgomery_inv_ntt" Inverse.staticCode [(.x0,.ptr a)]

def dot (p : Params) (r : Nat) : Prog isa :=
  callAt ("vg_mldsa_montgomery_dot"++toString p.ℓ) (MontDot.dot p.ℓ)
    [(.x0,.ptr (wP p)),(.x1,.ptr (aP (p.ℓ*r))),(.x2,.ptr (zP p 0))]

def product (p : Params) : Prog isa :=
  callAt "vg_mldsa_montgomery_product" MontProduct.code
    [(.x0,.ptr (tm2P p)),(.x1,.ptr (cP p)),(.x2,.ptr (tmP p))]

def subtract (p : Params) : Prog isa :=
  callAt "vg_mldsa_verify_sub" (AddSub.code true) [(.x0,.ptr (wP p)),(.x1,.ptr (tm2P p))]

def hintPack (p : Params) (r : Nat) : Prog isa :=
  callAt (if p.γ₂=261888 then "vg_mldsa_usehint_pack4" else "vg_mldsa_usehint_pack6") UseHintPack.prog
    [(.x0,.ptr ((bP p).1,(bP p).2+w1Len p*r)),(.x1,.ptr (hP p r)),
      (.x2,.ptr (wP p)),(.x3,.imm p.γ₂)]

def row (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  .seq (dot p r) (.seq (unpackT1At P (.x25,32+320*r) (tmP p))
    (.seq (forward (tmP p)) (.seq (product p) (.seq (subtract p)
      (.seq (inverse (wP p)) (hintPack p r))))))

def computeWith (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .seq (seqR (fun i=>forward (zP p i)) 0 p.ℓ) (.seq (forward (cP p))
    (.seq (seqR (row P p) 0 p.k)
      (.seq (shake256With c [⟨.x26,0,64⟩,⟨.x28,(bP p).2,p.k*w1Len p⟩] [⟨.x28,oCT,p.ctildeLen⟩])
        (cmpAnd (sc oCT) (.x27,0) p.ctildeLen))))

end VG.Impl.MlDsa.AArch64.Verify.Optimized
