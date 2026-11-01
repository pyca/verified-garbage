module
-- separate module: the contract moved out of `Spec/Dsa/MontContext.lean`, beside the other DSA helpers' contracts

public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Impl.Dsa.HelperLayout
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Montgomery context setup at fixed offsets of a working space

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose.

A callable arithmetic helper for DSA. For an odd modulus above
one, it computes the inverse used by radix-2¹⁶ Montgomery arithmetic, the
integer one, and R² modulo the modulus, where R = 2^(64 n). The layout fixes
all offsets; each integer occupies `8 n` little-endian bytes except the
inverse, which occupies four. Only the declared scratch ranges may change.
The workspace address and length are public; the modulus is secret.
-/

@[expose] public section
namespace VG.Proof.Dsa.MontContext

open VG.Impl.Dsa.MontContext (Layout)
open VG.Proof.Dsa.ModPow (numAt Keeps)

/-- One mutable workspace, in 64-bit words. -/
def sig : Sig := Proof.Dsa.ModPow.sig

def setupContract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws wsLen m =>
      let M := numAt m ws L.modulus (8 * L.n)
      L.size ≤ 8 * wsLen.toNat ∧ M % 2 = 1 ∧ 1 < M)
    (post := fun ws wsLen m m' _ =>
      let M := numAt m ws L.modulus (8 * L.n)
      (M * numAt m' ws L.inverse 4 + 1) % 2 ^ 16 = 0 ∧
      numAt m' ws L.one (8 * L.n) = 1 ∧
      numAt m' ws L.rSquared (8 * L.n) = 2 ^ (128 * L.n) % M ∧
      Keeps ws wsLen.toNat L.scratch m m')
    (stack := stack)

end VG.Proof.Dsa.MontContext
