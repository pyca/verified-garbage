module

public import VerifiedGarbage.Spec.Dsa.ModPow

/-!
# Montgomery context setup at fixed offsets of a working space

**Trusted.** A callable arithmetic helper for DSA. For an odd modulus above
one, it computes the inverse used by radix-2¹⁶ Montgomery arithmetic, the
integer one, and R² modulo the modulus, where R = 2^(64 n). The layout fixes
all offsets; each integer occupies `8 n` little-endian bytes except the
inverse, which occupies four. Only the declared scratch ranges may change.
The workspace address and length are public; the modulus is secret.
-/

@[expose] public section
namespace VG.Spec.Dsa.MontContext
open VG.Spec.Dsa.ModPow (numAt Keeps rangesDoc)

structure Layout where
  /-- The modulus's width in 64-bit words. -/
  n : Nat
  modulus : Nat
  inverse : Nat
  one : Nat
  rSquared : Nat
  /-- Output ranges and other bytes the function may change. -/
  scratch : List (Nat × Nat)
  size : Nat

/-- One mutable workspace, in 64-bit words. -/
def sig : Sig := Spec.Dsa.ModPow.sig

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

def api (L : Layout) : Api where
  module := "dsa"
  name := s!"vg_dsa_context_{L.n}"
  sig := sig
  contracts := some fun A stack => setupContract L A stack
  summary := s!"Montgomery context setup for an odd modulus m above one: m occupies \
    {8 * L.n} little-endian bytes at offset {L.modulus}. Writes at offset {L.inverse} \
    a four-byte integer v satisfying (m*v + 1) mod 2^16 = 0; writes one at offset \
    {L.one} and 2^{128 * L.n} mod m at offset {L.rSquared}, each in {8 * L.n} \
    little-endian bytes. Only workspace ranges {rangesDoc L.scratch} may change.\n\n\
    Contract: `VG.Spec.Dsa.MontContext.setupContract`. Constant time but for the \
    workspace address and length."
  safety := [s!"`ws_len` must be at least {(L.size + 7) / 8}.",
    s!"The modulus at offset {L.modulus} must be odd and above one.",
    s!"The scratch ranges {rangesDoc L.scratch} may hold intermediate values, \
      which the caller must destroy if they are secret."]

end VG.Spec.Dsa.MontContext
