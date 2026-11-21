module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub.Out
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.P192.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.P224.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.P256.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.P384.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.P521.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP320r1.Verified
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP384r1.Verified
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.P192.Verified
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.P224.Verified
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.P384.Verified
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.P521.Verified
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Secp256k1.Verified
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Verified
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP256r1
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP320r1
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdh.Generic
public import VerifiedGarbage.Spec.Ecdh.P192
public import VerifiedGarbage.Spec.Ecdh.P224
public import VerifiedGarbage.Spec.Ecdh.P256
public import VerifiedGarbage.Spec.Ecdh.P384
public import VerifiedGarbage.Spec.Ecdh.P521
public import VerifiedGarbage.Spec.Ecdh.Secp256k1
import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP256r1.Lit
import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP320r1.Lit
import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP384r1.Lit
import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Lit
import VerifiedGarbage.Proof.Ecdh.PPC64LE.P192.Lit
import VerifiedGarbage.Proof.Ecdh.PPC64LE.P224.Lit
import VerifiedGarbage.Proof.Ecdh.PPC64LE.P384.Lit
import VerifiedGarbage.Proof.Ecdh.PPC64LE.P521.Lit
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Secp256k1.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDH on PPC64LE, without secret residue

For every curve, `vg_ecdh_<curve>`, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbedAll`), which clears the
volatile registers and the stack its frames used. Its postcondition reads
the memory on return only within `out` (`Proof/EcKey/PPC64LE/Scrub/Out.lean`).
Each takes the curve's group law (`Weierstrass.Law`), which its registration
file gives.
`verifiedScrubbedAll`'s side condition (`scrubSide`) is proved at each theorem, by
the kernel's evaluation of it when this module is built.
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub
open VG.Proof.Weierstrass (Law)

/-- `Spec.Ecdh.P192.exchangeApi`'s function as emitted
(`Impl.Ecdh.PPC64LE.Fn.p192Exchange`) meets its contract in constant time and
returns without secret residue. -/
theorem p192Exchange_scrubbed (hL : Law Spec.P192.curve) :
    VerifiedScrubbed PPC64LE.target Impl.Ecdh.PPC64LE.Fn.p192Exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P192.inst PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdh.P192.exchangeApi) {
      code := Impl.Ecdh.PPC64LE.exchangeP192
      verified := Proof.Ecdh.PPC64LE.P192.ecdh_verified hL }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Proof.EcKey.PPC64LE.Scrub.exchangeOut _ _ [])
    (by dsimp only; lit_decide)

/-- `Spec.Ecdh.P224.exchangeApi`'s function as emitted
(`Impl.Ecdh.PPC64LE.Fn.p224Exchange`) meets its contract in constant time and
returns without secret residue. -/
theorem p224Exchange_scrubbed (hL : Law Spec.P224.curve) :
    VerifiedScrubbed PPC64LE.target Impl.Ecdh.PPC64LE.Fn.p224Exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdh.P224.exchangeApi) {
      code := Impl.Ecdh.PPC64LE.exchangeP224
      verified := Proof.Ecdh.PPC64LE.P224.ecdh_verified hL }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Proof.EcKey.PPC64LE.Scrub.exchangeOut _ _ [])
    (by dsimp only; lit_decide)

/-- `Spec.Ecdh.P256.exchangeApi`'s function as emitted
(`Impl.Ecdh.PPC64LE.Fn.p256Exchange`) meets its contract in constant time and
returns without secret residue. -/
theorem p256Exchange_scrubbed (hL : Law Spec.P256.curve) :
    VerifiedScrubbed PPC64LE.target Impl.Ecdh.PPC64LE.Fn.p256Exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdh.P256.exchangeApi) {
      code := Impl.Ecdh.PPC64LE.exchangeP256
      verified := Proof.Ecdh.PPC64LE.ecdh_verified hL }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Proof.EcKey.PPC64LE.Scrub.exchangeOut _ _ [])
    (by dsimp only; lit_decide)

/-- `Spec.Ecdh.P384.exchangeApi`'s function as emitted
(`Impl.Ecdh.PPC64LE.Fn.p384Exchange`) meets its contract in constant time and
returns without secret residue. -/
theorem p384Exchange_scrubbed (hL : Law Spec.P384.curve) :
    VerifiedScrubbed PPC64LE.target Impl.Ecdh.PPC64LE.Fn.p384Exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdh.P384.exchangeApi) {
      code := Impl.Ecdh.PPC64LE.exchangeP384
      verified := Proof.Ecdh.PPC64LE.P384.ecdh_verified hL }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Proof.EcKey.PPC64LE.Scrub.exchangeOut _ _ [])
    (by dsimp only; lit_decide)

/-- `Spec.Ecdh.P521.exchangeApi`'s function as emitted
(`Impl.Ecdh.PPC64LE.Fn.p521Exchange`) meets its contract in constant time and
returns without secret residue. -/
theorem p521Exchange_scrubbed (hL : Law Spec.P521.curve) :
    VerifiedScrubbed PPC64LE.target Impl.Ecdh.PPC64LE.Fn.p521Exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdh.P521.exchangeApi) {
      code := Impl.Ecdh.PPC64LE.exchangeP521
      verified := Proof.Ecdh.PPC64LE.P521.ecdh_verified hL }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Proof.EcKey.PPC64LE.Scrub.exchangeOut _ _ [])
    (by dsimp only; lit_decide)

/-- `Spec.Ecdh.Secp256k1.exchangeApi`'s function as emitted
(`Impl.Ecdh.PPC64LE.Fn.secp256k1Exchange`) meets its contract in constant time
and returns without secret residue. -/
theorem secp256k1Exchange_scrubbed (hL : Law Spec.Secp256k1.curve) :
    VerifiedScrubbed PPC64LE.target Impl.Ecdh.PPC64LE.Fn.secp256k1Exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.Secp256k1.inst PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdh.Secp256k1.exchangeApi) {
      code := Impl.Ecdh.PPC64LE.exchangeSecp256k1
      verified := Proof.Ecdh.PPC64LE.Secp256k1.ecdh_verified hL }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Proof.EcKey.PPC64LE.Scrub.exchangeOut _ _ [])
    (by dsimp only; lit_decide)

/-- `Spec.Ecdh.BrainpoolP256r1.exchangeApi`'s function as emitted
(`Impl.Ecdh.PPC64LE.Fn.brainpoolp256r1Exchange`) meets its contract in
constant time and returns without secret residue. -/
theorem brainpoolp256r1Exchange_scrubbed (hL : Law Spec.BrainpoolP256r1.curve) :
    VerifiedScrubbed PPC64LE.target Impl.Ecdh.PPC64LE.Fn.brainpoolp256r1Exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP256r1.inst PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdh.BrainpoolP256r1.exchangeApi) {
      code := Impl.Ecdh.PPC64LE.exchangeBrainpoolP256r1
      verified := Proof.Ecdh.PPC64LE.BrainpoolP256r1.ecdh_verified hL }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Proof.EcKey.PPC64LE.Scrub.exchangeOut _ _ [])
    (by dsimp only; lit_decide)

/-- `Spec.Ecdh.BrainpoolP320r1.exchangeApi`'s function as emitted
(`Impl.Ecdh.PPC64LE.Fn.brainpoolp320r1Exchange`) meets its contract in
constant time and returns without secret residue. -/
theorem brainpoolp320r1Exchange_scrubbed (hL : Law Spec.BrainpoolP320r1.curve) :
    VerifiedScrubbed PPC64LE.target Impl.Ecdh.PPC64LE.Fn.brainpoolp320r1Exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP320r1.inst PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdh.BrainpoolP320r1.exchangeApi) {
      code := Impl.Ecdh.PPC64LE.exchangeBrainpoolP320r1
      verified := Proof.Ecdh.PPC64LE.BrainpoolP320r1.ecdh_verified hL }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Proof.EcKey.PPC64LE.Scrub.exchangeOut _ _ [])
    (by dsimp only; lit_decide)

/-- `Spec.Ecdh.BrainpoolP384r1.exchangeApi`'s function as emitted
(`Impl.Ecdh.PPC64LE.Fn.brainpoolp384r1Exchange`) meets its contract in
constant time and returns without secret residue. -/
theorem brainpoolp384r1Exchange_scrubbed (hL : Law Spec.BrainpoolP384r1.curve) :
    VerifiedScrubbed PPC64LE.target Impl.Ecdh.PPC64LE.Fn.brainpoolp384r1Exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP384r1.inst PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdh.BrainpoolP384r1.exchangeApi) {
      code := Impl.Ecdh.PPC64LE.exchangeBrainpoolP384r1
      verified := Proof.Ecdh.PPC64LE.BrainpoolP384r1.ecdh_verified hL }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Proof.EcKey.PPC64LE.Scrub.exchangeOut _ _ [])
    (by dsimp only; lit_decide)

/-- `Spec.Ecdh.BrainpoolP512r1.exchangeApi`'s function as emitted
(`Impl.Ecdh.PPC64LE.Fn.brainpoolp512r1Exchange`) meets its contract in
constant time and returns without secret residue. -/
theorem brainpoolp512r1Exchange_scrubbed (hL : Law Spec.BrainpoolP512r1.curve) :
    VerifiedScrubbed PPC64LE.target Impl.Ecdh.PPC64LE.Fn.brainpoolp512r1Exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst PPC64LE.abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdh.BrainpoolP512r1.exchangeApi) {
      code := Impl.Ecdh.PPC64LE.exchangeBrainpoolP512r1
      verified := Proof.Ecdh.PPC64LE.BrainpoolP512r1.ecdh_verified hL }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Proof.EcKey.PPC64LE.Scrub.exchangeOut _ _ [])
    (by dsimp only; lit_decide)

end VG.Proof.Ecdh.PPC64LE.Scrub
