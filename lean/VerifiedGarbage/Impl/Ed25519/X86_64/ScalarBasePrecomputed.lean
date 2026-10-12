module

public import VerifiedGarbage.Impl.Ed25519.X86_64.Comb
public import VerifiedGarbage.Impl.Ed25519.X86_64.CombZmm
public import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase

/-! Fixed-base multiplication with a comb of precomputed, cached multiples of the base point. -/

@[expose] public section

namespace VG.Impl.Ed25519.X86_64
open VG.X86_64

/-- The scalar's bits, `[s]B` by the comb `comb`, and its encoding. -/
def scalarBaseEngineOf (fld : Arith) (comb : Prog isa) : Prog isa :=
  .seq (scalarBasePrepare fld) (.seq comb (pointEncode fld))

def scalarBasePrecomputedEngine (fld : Arith) : Prog isa := scalarBaseEngineOf fld (combMultiply fld)

def scalarBase_precomputed (fld : Arith) : Prog isa :=
  scalarBaseWith (scalarBasePrecomputedEngine fld)

/-- With BMI2's and ADX's field multiplications, and the comb's entries selected with AVX2
(`combSelectY`). -/
def scalarBase_adx : Prog isa :=
  scalarBaseWith (scalarBaseEngineOf VG.Impl.X25519.X86_64.adx
    (combMultiply VG.Impl.X25519.X86_64.adx combSelectY))

/-- With the comb of AVX512_IFMA in `zmm` registers (`Zmm.combMultiply`), and BMI2's and ADX's
field multiplications for the rest. -/
def scalarBase_ifma : Prog isa :=
  scalarBaseWith (scalarBaseEngineOf VG.Impl.X25519.X86_64.adx (Zmm.combMultiply VG.Impl.X25519.X86_64.adx))

end VG.Impl.Ed25519.X86_64
