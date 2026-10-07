import VerifiedGarbage.Variants.P256.X86_64.Law
import VerifiedGarbage.Proof.P256.PeerOrder
import VerifiedGarbage.Proof.Weierstrass.X86_64.SecretIface

/-! P-256's group law, inversion and arbitrary-peer order, isolated from the machine proofs. -/
namespace VG.Variants.P256Secret.X86_64.Law

def variant : Proof.Weierstrass.X86_64.HasSecretLawInv Spec.P256.curve :=
  { toHasLawInv := P256.X86_64.Law.variant, peerOrder := Proof.P256.peerOrder }

end VG.Variants.P256Secret.X86_64.Law
