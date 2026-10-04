import VerifiedGarbage.Proof.Weierstrass.X86_64.Words
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes

/-!
# Deterministic ECDSA on x86-64: big-endian numbers

The 32 bytes at an address, big-endian, from the `bswap`s of their four
words (`ofBytes_32`, from `Proof/Ecdsa/Rfc6979/Bytes.lean`, as `bswap` is
`byteRev64`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem ofBytes_32 (m : Mem) (q : Addr) :
    Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m q 32) =
      (bswap64 (m.readW q 64)).toNat * 2 ^ 192 +
        (bswap64 (m.readW (q + BitVec.ofNat 64 8) 64)).toNat * 2 ^ 128 +
        (bswap64 (m.readW (q + BitVec.ofNat 64 16) 64)).toNat * 2 ^ 64 +
        (bswap64 (m.readW (q + BitVec.ofNat 64 24) 64)).toNat :=
  Rfc6979.ofBytes_32 m q

end VG.Proof.Ecdsa.Rfc6979.X86_64
