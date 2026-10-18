module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPcCT
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.Framework.Registration

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

`vg_rsa_private_checked_precomputed`, calling `v`'s
`vg_rsa_private_crt_precomputed`, is emitted the same way. It uses 1208
bytes of stack: a frame of 1192 bytes, which holds the CRT's result and the
stack arguments of its calls, and the same return addresses.
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
    features := v.features },
  Spec.Rsa.privateCheckedPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation computes the result `m` with `" ++
      v.pcrtName ++ "` into its frame, then `m^e mod n` with `" ++ pdName v ++
      "` from the values of `n` at the start of `pre`, which also checks `e`. It compares that with the \
      input in constant time, and copies `m` to `out` under a mask, which is clear unless the CRT and the \
      public operation succeeded and the two match. The result, 1, 2 or 0, is computed from the mask without \
      a branch. Then it overwrites the frame's copy of `m` with zeros."]
    code := Impl.Rsa.X86_64.PrivCheckedPc.code v.pcrtName v.pcrt (pdName v) v.pubOp.code
    stack := stackBytesPc
    verified := codeP_verified v _
    spSafe := codeP_spSafe v _
    features := v.features }]

end VG.Generic.RsaPrivateCrt.X86_64.Rsa
