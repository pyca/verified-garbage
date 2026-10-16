module

public import VerifiedGarbage.Impl.X25519.AArch64.Hybrid
public import VerifiedGarbage.Proof.Framework.AArch64.Interleave
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# X25519 on AArch64: the interleaved products are independent

Untrusted: everything here is checked by Lean. The scalar operations of an
iteration's first phase and the AdvSIMD products touch disjoint registers and
bytes (checked by evaluating their footprints), so their interleaving runs as
the one and then the other.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG VG.AArch64 VG.AArch64.Interleave
open VG.Impl.X25519.AArch64.Hybrid

theorem indeps_A : Indeps .x0 scalarA vectorA := indeps_of_check (by decide +kernel)

end VG.Proof.X25519.AArch64.Hybrid
