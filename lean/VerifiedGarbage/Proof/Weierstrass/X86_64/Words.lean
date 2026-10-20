module
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.TCB.X86_64.Gpr

import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Short Weierstrass curves on x86-64: numbers as words, bits and bytes

`bswap` is `byteRev64`, so the encodings of `Proof/Weierstrass/Words.lean`
are what it loads and stores.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Proof.Weierstrass

theorem bswap64_eq (w : BitVec 64) : bswap64 w = byteRev64 w := rfl

/-- A byte-reversed word is the eight bytes big-endian. -/
theorem bswap64_ofBytes (m : Mem) (q : Addr) :
    (bswap64 (m.readW q 64)).toNat = Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt m q 8) :=
  byteRev64_ofBytes m q

end VG.Proof.Weierstrass.X86_64
