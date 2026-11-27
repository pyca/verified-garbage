module
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.AArch64.Isa

import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.MlKem.AArch64.Basic

/-! # CBD2 contract and input representation -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd2

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev fP : Addr := s₀.gpr .x1
abbrev bR : Region := ⟨bP s₀, 128⟩
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) 128
/-- Coefficient `i` of the output. -/
def G (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((samplePolyCBD 2 (B s₀))[i]!).val
/-- Byte `j` of the input, as a number. -/
abbrev byte (j : Nat) : Nat := ((B s₀).getD j 0).toNat

end

end VG.Proof.MlKem.AArch64.Cbd2
