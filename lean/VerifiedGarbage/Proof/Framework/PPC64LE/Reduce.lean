module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.UnfoldStep
public meta import VerifiedGarbage.Proof.Framework.UnfoldStep

/-!
# PPC64LE: the model's functions on constructors, without their equation lemmas

Each `dsimproc` here unfolds a function of the model applied to arguments
given by their constructors (`unfoldStep?`): pass it to `simp` in place of
the function (`reduceExec` for `exec`). Unlike the function's equation lemmas, it realizes
nothing in the module that uses it.
-/

public meta section

namespace VG.PPC64LE

/-- `exec` unfolded on constructors (see `unfoldStep?`). -/
dsimproc reduceExec (exec _ _) := fun e => do
  let some e' ← unfoldStep? e | return .continue
  return .visit e'

end VG.PPC64LE
