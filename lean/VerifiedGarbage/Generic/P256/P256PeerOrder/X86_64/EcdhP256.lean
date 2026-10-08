import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.Weierstrass.PeerOrder
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Verified

/-! P-256 ECDH with a persistent Jacobian accumulator and signed five-bit windows. -/
namespace VG.Generic.P256.P256PeerOrder.X86_64.EcdhP256

/-- The function of `Spec.Ecdh.P256.exchangeApi`, multiplying with BMI2 and ADX
(`adx`, `_adx`) or not: its `code`, proven (`hv`), with no instruction writing
`rsp` (`hsp`). -/
def exchange (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true) : Artifact :=
  { Spec.Ecdh.P256.exchangeApi with
    name := Spec.Ecdh.P256.exchangeApi.name ++ (if adx then "_adx" else "")
    target := X86_64.target
    doc := Spec.Ecdh.P256.exchangeApi.doc (notes := ["The peer's key is validated without branches, \
      with invalid peers replaced by the generator before multiplication. Field elements are four \
      64-bit words in Montgomery form, " ++ Proof.Ecdsa.X86_64.mulNote adx ++ ". The scalar is \
      recoded into 52 signed five-bit digits in `[-16, 15]`. A table of sixteen Jacobian points \
      with cached squared and cubed Z coordinates is built in scratch. Each digit is selected \
      by scanning the entire table with SSE2 (baseline) or AVX2 (`_adx`). The accumulator stays \
      in Jacobian coordinates through five doublings and one masked addition per remaining \
      digit. The peer-order proof excludes equal nonzero inputs to the incomplete addition \
      for valid scalars; infinity and opposite points are handled. Only the final x-coordinate \
      is converted using divsteps inversion of Z squared. Masks select the result or zeros \
      according to peer validity, scalar range and infinity checks. Callee-saved registers are \
      saved in scratch, and branches and addresses depend only on public data."])
    code
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P256.curve)
    (o : Proof.Weierstrass.HasPeerOrder Spec.P256.curve) : List Artifact := [
  exchange false Impl.Ecdh.X86_64.Window5.exchangeP256
    (Proof.Ecdh.X86_64.Secret.baseline_verified h.law h.inv o.order) (Code.all_of_allInstrs (by lit_decide)),
  exchange true Impl.Ecdh.X86_64.Window5.exchangeP256Adx
    (Proof.Ecdh.X86_64.Secret.adx_verified h.law h.inv o.order) (Code.all_of_allInstrs (by lit_decide))]

end VG.Generic.P256.P256PeerOrder.X86_64.EcdhP256
