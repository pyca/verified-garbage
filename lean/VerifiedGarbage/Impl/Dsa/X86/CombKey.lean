module

public import VerifiedGarbage.Impl.Dsa.X86.CombGenerate
public import VerifiedGarbage.Impl.Dsa.X86.GenerateKey

/-! The retained-context derivation is internal to key generation. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Comb
open VG VG.X86

/-- Reserve the cdecl return-address slot for an inlined body. -/
def invoke (body : Prog isa) : Prog isa :=
  .frame (.alloc 4) body (.free 4)

def generateKey : Prog isa :=
  GenerateKey.codeWith (invoke checkParameters) (invoke deriveKey)

end VG.Impl.Dsa.X86.Comb
