module

import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Rsa.X86_64.PrivChecked
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCtx
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.Bignum.LazyMath
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
public import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
public import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
public import VerifiedGarbage.Proof.Bignum.X86_64.Copy
public import VerifiedGarbage.Proof.Bignum.X86_64.Csub
public import VerifiedGarbage.Proof.Bignum.X86_64.Double
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.PdExp
public import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
public import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
public import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
public import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
public import VerifiedGarbage.Proof.Bignum.X86_64.Row
public import VerifiedGarbage.Proof.Bignum.X86_64.Setup
public import VerifiedGarbage.Proof.Bignum.X86_64.Store
public import VerifiedGarbage.Proof.Bignum.X86_64.Valid
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivOutcome
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
import VerifiedGarbage.Proof.Rsa.X86_64.PrivOutcome
import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail

/-!
# The checked RSA private-key operation on x86-64

A generic file (see `TCB/Emit.lean`): `vg_rsa_private_checked`, calling an
implementation `v` of `vg_rsa_private_crt`, is emitted once for each
implementation (`Variants/RsaPrivateCrt/X86_64/`), named with its suffix
(e.g. `vg_rsa_private_checked_adx`), and needs its CPU features.

It uses 3256 bytes of stack: a frame of 3240 bytes, which holds the CRT's
result, the precomputed values of `n` and the stack arguments of its calls,
the return address of its calls, and that of their calls of Montgomery
multiplication, which uses no stack.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.X86_64.Rsa

open VG.Proof.Rsa.X86_64

/-- The names of the public operation the check calls. -/
def pcName (v : CrtImpl) : String := Spec.Rsa.publicPrecomputeApi.name ++ v.montSuffix
def pdName (v : CrtImpl) : String := v.pubOp.name

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.Rsa.privateCheckedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation computes the result `m` with `" ++
      v.name ++ "` into its frame, then `m^e mod n` with `" ++ pcName v ++ "` and `" ++ pdName v ++
      "`, which also checks `e`. It compares that with the input in constant time, and copies `m` to `out` \
      under a mask, which is clear unless the CRT and the public operation succeeded and the two match. \
      The result, 1, 2 or 0, is computed from the mask without a branch. Then it overwrites the frame's \
      copy of `m` with zeros."]
    code := Impl.Rsa.X86_64.PrivChecked.code v.name v.code (pcName v) v.pc (pdName v) v.pubOp.code
    stack := stackBytes
    verified := code_verified v _ _
    spSafe := code_spSafe v _ _
    features := v.features }]

end VG.Generic.RsaPrivateCrt.X86_64.Rsa
