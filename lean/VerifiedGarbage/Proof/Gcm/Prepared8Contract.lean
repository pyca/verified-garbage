module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Spec.Gcm.Prepared

/-!
# AES-GCM with eight prepared GHASH powers

Not trusted: a 384-byte key-context format for implementations that read only
the first eight prepared powers. The first 256 bytes are the existing key
context (`KeyRepr`'s layout: the key schedule, and the hash subkey at byte
240); the remaining 128 bytes hold 4 pairs, laid out exactly as the first 4
pairs of `PreparedPowersRepr` (bytes 256 through 383 of the 1024-byte
prepared format): pair `k` is `preparedPower(H^(2k+2))` then
`preparedPower(H^(2k+1))`, each stored little-endian. This is a storage
convention, not a change to GCM's field arithmetic (NIST SP 800-38D §6.3).
The 1024-byte prepared format (`Spec/Gcm/Prepared.lean`) is unchanged.
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec VG.Spec.Gcm

/-- The first 4 pairs of `PreparedPowersRepr`: pair `k`, at byte `256 + 32 k`,
contains the encoded `H^(2k+2)` then `H^(2k+1)`, each as a little-endian
128-bit word. The 4 pairs occupy bytes 256 through 383. -/
def PreparedPowers8Repr (m : Mem) (p : Addr) : Prop :=
  ∀ k < 4,
    m.readW (p + BitVec.ofNat 64 (256 + 32 * k)) 128 =
      preparedPower (hpow (ctxH m p) (2 * k + 2)) ∧
    m.readW (p + BitVec.ofNat 64 (272 + 32 * k)) 128 =
      preparedPower (hpow (ctxH m p) (2 * k + 1))

end VG.Proof.Gcm
