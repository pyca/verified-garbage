module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan
public import VerifiedGarbage.Proof.Dsa.Generation.Contributions
import VerifiedGarbage.Proof.Dsa.Generation.StoredHashes
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Decode the stored p hashes as their radix contribution sum -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.Proof.Bignum VG.Proof.Dsa.Generation

theorem hash_prefix_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : X86_64.State}
    (hs : HashState p H (p.count + 1) s) (k : Nat) (hk : k ≤ p.count + 1) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off p.output ((p.count + 1 - k) * p.len)) (k * p.len)) =
      contributions (8 * p.len) (fun j => Spec.Dsa.decodeBE (p.digest H j)) k := by
  exact stored_hash_prefix_value s.mem p.output p.len p.count (p.digest H)
    (fun j hj => hs.hashes j hj) k hk

end VG.Proof.Dsa.X86_64.Generation
