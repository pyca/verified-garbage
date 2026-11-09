module

public import VerifiedGarbage.Proof.Rsa.X86.InvU
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.X86.State
import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # `inverse` on i686: one step is `invStep` -/

@[expose] public section

namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa (subMod halfMod)

/-- The bank at `j`: `(u, v, x₁, x₂)`. -/
def bank (m : Mem) (B : Addr) (w j : Nat) : Nat × Nat × Nat × Nat :=
  (num m B w j, num m B w (j + 1), num m B w (j + 2), num m B w (j + 3))

end VG.Proof.Rsa.X86.Keys
