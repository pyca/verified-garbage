import VerifiedGarbage.Proof.Rsa.Checked

import VerifiedGarbage.Proof.RsaKeyGen.Generate

/- Proofs formerly in `VerifiedGarbage.Proof.RsaKeyGen.Checked`. -/
section

/-!
# RSA key generation: generated keys and the checked private operation

Every key `RsaKeyGen.generate` returns passes the key check `Rsa.checkKey`
(BoringSSL's `RSA_check_key`, `generate_checkKey`), so if its primes are
prime (which the generation tests only probably), the private operation
checked against `e` never fails its check, and is RSADP with `d`
(`generate_privateChecked`).
-/

namespace VG.Proof.RsaKeyGen

open VG.Spec
open VG.Spec.RsaKeyGen

open VG.Spec.Rsa (checkKey privateChecked os2ip i2osp)

/-- Every key `generate` returns passes `Rsa.checkKey`, as octets. -/
theorem generate_checkKey {bits e : Nat} {rand : Rand} {k : Key}
    (h : generate bits e rand = some (.ok k)) :
    checkKey (k.octets k.n) (k.octets k.e) (k.octets k.d) (k.octets k.p) (k.octets k.q)
      (k.octets k.dP) (k.octets k.dQ) (k.octets k.qInv) = true := by
  obtain ⟨_, _, _, _, _, _, _, ⟨_, hv, _⟩, _⟩ := VG.Proof.RsaKeyGen.generate_ok h
  exact hv

/-- For every key `generate` returns whose primes are prime, the private
operation checked against `e` never fails its check, and for every input
below `n` is RSADP with `d`. -/
theorem generate_privateChecked {bits e : Nat} {rand : Rand} {k : Key}
    (h : generate bits e rand = some (.ok k))
    (hp : (os2ip (k.octets k.p)).Prime) (hq : (os2ip (k.octets k.q)).Prime) (xB : List Byte) :
    privateChecked (k.octets k.n) (k.octets k.e) xB (k.octets k.p) (k.octets k.q)
        (k.octets k.dP) (k.octets k.dQ) (k.octets k.qInv) ≠ .fault ∧
      (os2ip xB < os2ip (k.octets k.n) →
        privateChecked (k.octets k.n) (k.octets k.e) xB (k.octets k.p) (k.octets k.q)
            (k.octets k.dP) (k.octets k.dQ) (k.octets k.qInv) =
          .ok (i2osp (os2ip xB ^ os2ip (k.octets k.d) % os2ip (k.octets k.n))
            (k.octets k.n).length)) :=
  ⟨VG.Proof.Rsa.privateChecked_ne_fault xB (VG.Proof.RsaKeyGen.generate_checkKey h) hp hq,
    fun hx => VG.Proof.Rsa.privateChecked_of_checkKey (VG.Proof.RsaKeyGen.generate_checkKey h) hp hq hx⟩

end VG.Proof.RsaKeyGen

end
