import VerifiedGarbage.Proof.P256.PeerOrder

/-! Arbitrary-peer order for P-256, isolated from the machine proofs. -/
namespace VG.Variants.P256PeerOrder.X86_64.Order

def variant : Proof.Weierstrass.HasPeerOrder Spec.P256.curve :=
  ⟨Proof.P256.peerOrder⟩

end VG.Variants.P256PeerOrder.X86_64.Order
