module

public import VerifiedGarbage.Proof.Rsa.PrivCheckLogic32
import Batteries.Tactic.Alias
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Compatibility names for shared 32-bit private-result logic -/

@[expose] public section
namespace VG.Proof.Rsa.Arm

alias successBits_widen := VG.Proof.Rsa.successBits_widen
alias successBits_one := VG.Proof.Rsa.successBits_one
alias check_logic32 := VG.Proof.Rsa.check_logic32

end VG.Proof.Rsa.Arm
