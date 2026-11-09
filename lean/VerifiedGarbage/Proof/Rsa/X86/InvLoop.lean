module

public import VerifiedGarbage.Proof.Rsa.X86.InvStep
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! # The inverse on i686: what it writes

`invArrs`, `invSlots`: the arrays and header words the inverse writes, and
`rtSlots`: the header words the batched inverse also uses as scratch.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa (invIter InvI)

/-- The arrays and header words the inverse writes. -/
abbrev invArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, aT1, aT2, aT3, aT4]
abbrev invSlots : List Nat := [sOdd, sB, sC]
/-- The header words from 16 to 96 that the batched inverse also uses as scratch. -/
abbrev rtSlots : List Nat := [16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96]

end VG.Proof.Rsa.X86.Keys
