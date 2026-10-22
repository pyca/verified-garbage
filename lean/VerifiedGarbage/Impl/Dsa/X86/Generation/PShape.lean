module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.QCandidate
public import VerifiedGarbage.Impl.Dsa.Generation.Layout

/-! Shape the final modulus-width suffix using the existing subgroup byte shaper. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86

def workspaceCopyArguments (source destination len : Nat) : List Instr :=
  [.mov .ebp (.reg .edi)] ++ qArguments source destination len

def shapeWorkspace (source destination len : Nat) : Prog isa :=
  .seq (.block (workspaceCopyArguments source destination len)) qShape

def pShape (digestLen count pLen : Nat) : Prog isa :=
  shapeWorkspace (Dsa.Generation.Layout.hashes + ((count + 1) * digestLen - pLen))
    Dsa.Generation.Layout.shaped pLen

end VG.Impl.Dsa.X86.Generation
