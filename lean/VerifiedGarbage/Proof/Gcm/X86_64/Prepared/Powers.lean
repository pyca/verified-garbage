module

public import VerifiedGarbage.Spec.Gcm.Prepared16

/-!
# The first `n` pairs of a prepared key context

`PowersN n`: pairs `0` to `n - 1` of `Spec.Gcm.PreparedPowersRepr`'s layout,
which is `PreparedPowersRepr` itself for `n = 24` and
`PreparedPowers16Repr` for `n = 8`, so that the loops are proven once for
the powers they read.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Stitch

open VG

/-- Pair `k`, for `k < n`, at byte `256 + 32 k`: the encoded `H^(2k+2)` then
`H^(2k+1)`, each a little-endian 128-bit word. -/
def PowersN (n : Nat) (m : Mem) (p : Addr) : Prop :=
  ∀ k < n,
    m.readW (p + BitVec.ofNat 64 (256 + 32 * k)) 128 =
      Spec.Gcm.preparedPower (Spec.Gcm.hpow (Spec.Gcm.ctxH m p) (2 * k + 2)) ∧
    m.readW (p + BitVec.ofNat 64 (272 + 32 * k)) 128 =
      Spec.Gcm.preparedPower (Spec.Gcm.hpow (Spec.Gcm.ctxH m p) (2 * k + 1))

theorem PowersN.of_repr {m : Mem} {p : Addr} (h : Spec.Gcm.PreparedPowersRepr m p) : PowersN 24 m p := h

theorem PowersN.of_repr16 {m : Mem} {p : Addr} (h : Spec.Gcm.PreparedPowers16Repr m p) : PowersN 8 m p := h

theorem PowersN.mono {n n' : Nat} {m : Mem} {p : Addr} (h : PowersN n m p) (hn : n' ≤ n) : PowersN n' m p :=
  fun k hk => h k (Nat.lt_of_lt_of_le hk hn)

end VG.Proof.Gcm.X86_64.Stitch
