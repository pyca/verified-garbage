module

public import VerifiedGarbage.Impl.Ed448.X86_64.Point64
public import VerifiedGarbage.Impl.X448.X86_64.Adx

/-! Ed448 field backends, shared by point operations and every caller. -/

@[expose] public section

namespace VG.Impl.Ed448.X86_64

open VG.X86_64

inductive FieldVariant where
  | scalar
  | adx
  deriving DecidableEq

namespace Point64

def doubleAdxFn : Prog isa := doubleFnWith Impl.X448.X86_64.adx
def addAdxFn : Prog isa := addFnWith Impl.X448.X86_64.adx

end Point64

namespace FieldVariant

def field : FieldVariant → Impl.X448.X86_64.Field
  | .scalar => Impl.X448.X86_64.baseline
  | .adx => Impl.X448.X86_64.adx

def suffix : FieldVariant → String
  | .scalar => ""
  | .adx => "_adx"

def features : FieldVariant → List String
  | .scalar => []
  | .adx => ["bmi2", "adx"]

def doubleFn : FieldVariant → Prog isa
  | .scalar => Point64.doubleFn
  | .adx => Point64.doubleAdxFn

def addFn : FieldVariant → Prog isa
  | .scalar => Point64.addFn
  | .adx => Point64.addAdxFn

def powName (v : FieldVariant) : String := "vg_gf448_r64_pow223" ++ v.suffix

def powFn : FieldVariant → Prog isa
  | .scalar => Impl.X448.X86_64.pow223Fn
  | .adx => Impl.X448.X86_64.pow223AdxFn

def calls (v : FieldVariant) : Point64.Ops :=
  ⟨.call ("vg_ed448_r64_point_double" ++ v.suffix) v.doubleFn,
   .call ("vg_ed448_r64_point_add_affine" ++ v.suffix) v.addFn⟩

def bodies (v : FieldVariant) : Point64.Ops := ⟨v.doubleFn, v.addFn⟩

end FieldVariant
end VG.Impl.Ed448.X86_64
