module

public import VerifiedGarbage.Impl.Rsa.Arm.Recover

/-! Small public recovery candidates need modular additions, not another
Montgomery product. Reuse the existing workspace addition and scratch layout.
These pieces are not registered yet. -/

@[expose] public section
namespace VG.Impl.Rsa.Arm.RecoverScalar
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover

/-- Twice the square, still in Montgomery form. -/
def twice : Prog isa := seqs (addMod mXm mX mX aN aZ aW)

/-- Three times the square, still in Montgomery form. -/
def three : Prog isa := .seq twice (seqs (addMod mXm mXm mX aN aZ aW))

end VG.Impl.Rsa.Arm.RecoverScalar
