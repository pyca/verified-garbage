module

public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Rsa.Arm.KeyWs
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate

/-! # A candidate on ARMv7: pieces the taint analysis checks

`Cert c`: the piece `c` leaks only what the working space's registers
`r7`–`r9` determine.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate

/-- A piece the taint analysis checks with `r7`–`r9` public. -/
abbrev Cert (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r7, .r8, .r9]) c hc).isSome = true

end VG.Proof.Dsa.Arm.Prime
