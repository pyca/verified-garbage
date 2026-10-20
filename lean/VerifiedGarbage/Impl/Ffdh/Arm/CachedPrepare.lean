module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Impl.Bignum.Arm.PdImport

/-! Import RSA's canonical modulus/R² prefix and compute only the inverse word. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.CachedPrepare
open VG VG.Arm VG.Impl.Bignum.Arm

def source : List Instr := [.ldrSp .r4 52, .dp .add .r4 .r4 (.imm 24)]

def body : Prog isa := .seq PublicFn.prepare
  (.seq (.block source) (.seq pdImport precomputeInverse))

def code : Prog isa := .seq (.block (Domain.prepareArgs 24)) body

end VG.Impl.Ffdh.Arm.CachedPrepare
