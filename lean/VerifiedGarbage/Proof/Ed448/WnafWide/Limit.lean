module

import VerifiedGarbage.Proof.Framework.PowLit

public import VerifiedGarbage.Impl.Ed448.WnafWide

/-! The complete 57-byte scalar range, expressed without default power-instance changes. -/

@[expose] public section

namespace VG.Proof.Ed448.WnafWide

theorem scalarLimit_eq : Impl.Ed448.WnafWide.scalarLimit=(256:Nat)^57:=by decide +kernel

end VG.Proof.Ed448.WnafWide
