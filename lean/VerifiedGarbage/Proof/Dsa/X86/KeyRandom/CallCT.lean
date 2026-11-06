module
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CTDefs
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Call

import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult
import VerifiedGarbage.Proof.Framework.Offset
import Batteries.Logic

/-!
# The callee's call leaks only what its contract allows (x86)

Two runs call `vg_dsa_derive_key` with the same public arguments, public domain
bytes and derivation status (`call_pub`), which its contract's constant time
covers (`call_ct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- The public domain bytes of the entry. -/
abbrev keyLeak (s₀ : State) : List Nat :=
  (rInput s₀).key.map (·.toNat)

end VG.Proof.Dsa.X86.KeyRandom
