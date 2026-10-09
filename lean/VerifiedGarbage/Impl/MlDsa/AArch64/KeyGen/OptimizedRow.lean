import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedDot

namespace VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call
variable (P : Prims)

def addAt (f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_keygen_add" P.add [(.x0,.ptr f),(.x1,.ptr g)]

def power2RoundAt (t t1 t0 : Ptr) : Prog isa :=
  callAt "vg_mldsa_keygen_power2round" P.power2Round [(.x0,.ptr t),(.x1,.ptr t1),(.x2,.ptr t0)]

def simpleBitPackAt (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_keygen_simple_bit_pack" P.simpleBitPack
    [(.x0,.ptr f),(.x1,.imm b),(.x2,.ptr out),(.x3,.imm len)]

def bitPackAt (f : Ptr) (a b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_keygen_bit_pack" P.bitPack
    [(.x0,.ptr f),(.x1,.imm a),(.x2,.imm b),(.x3,.ptr out),(.x4,.imm len)]

def packSecret (p : Spec.MlDsa.Params) (r : Nat) : Prog isa :=
  bitPackAt P (sP p r) p.η p.η (.x27,128+lenS p*r) (lenS p)

def row (p : Spec.MlDsa.Params) (i : Nat) : Prog isa :=
  .seq (dotRow p i) (.seq (addAt P (tP p) (sP p (p.ℓ+i)))
    (.seq (power2RoundAt P (tP p) (t1P p) (t0P p))
      (.seq (simpleBitPackAt P (t1P p) 1023 (.x26,32+320*i) 320)
        (bitPackAt P (t0P p) 4095 4096 (.x27,oT0 p+416*i) 416))))

end VG.Impl.MlDsa.AArch64.KeyGen.Optimized
