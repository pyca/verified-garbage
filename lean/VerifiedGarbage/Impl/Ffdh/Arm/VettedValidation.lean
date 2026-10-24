module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups

/-! Standard domains are validated by exact recognition before general arithmetic.
The fallback retains the original checks for all other parameters. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Impl.Ffdh.Arm.Domain

def body : Prog isa := .seq VG.Impl.Ffdh.Arm.VettedGroups.code
  (.seq testFlag (.ite .ne (ret 1) (head CheckDomain.main)))

def code : Prog isa := VG.Impl.Ffdh.Arm.framed
  (.seq (.block CheckDomain.entry) body)

end VG.Impl.Ffdh.Arm.VettedValidation
