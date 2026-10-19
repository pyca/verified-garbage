module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecContract
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncContract
public import VerifiedGarbage.Impl.Rsa.X86_64.PrivChecked
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCtx
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
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
public import VerifiedGarbage.Proof.Framework.X86_64.CallSp
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
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
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivOutcome
import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail

/-!
# The callees of encryption and decryption

`vg_rsa_public_checked` is a `PubImpl` (`pubImpl`). For each implementation `c` of `vg_rsa_private_crt` (a variant of
`RsaPrivateCrt`), `vg_rsa_private_checked` calling it, as
`Generic/RsaPrivateCrt/X86_64/Rsa.lean` emits it, is a `PrivImpl`
(`privOf`): `privK` is its contract, and it uses its frame and two return
addresses of stack, since its callees' callees use none.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Proof.Rsa.X86_64

theorem pubChkK_eq : pubChkK = pubChkContract := rfl

/-- `vg_rsa_public_checked`, as encryption's callee. -/
def pubImpl : PubImpl where
  name := Spec.Rsa.publicCheckedApi.name
  code := Impl.Rsa.X86_64.Checked.publicChecked
  ok := pubChkK_eq ▸ publicChecked_correct
  ct := pubChkK_eq ▸ publicChecked_constantTime
  nosp := noSp_of (by decide +kernel)
  depth := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)

theorem privK_eq : privK = chkContract := rfl

/-- The name of `vg_rsa_private_checked` calling `c`. -/
def privName (c : CrtImpl) : String := Spec.Rsa.privateCheckedApi.name ++ c.suffix

/-- Its code, as `Generic/RsaPrivateCrt/X86_64/Rsa.lean` emits it. -/
def privCode (c : CrtImpl) : Prog isa :=
  Impl.Rsa.X86_64.PrivChecked.code c.name c.code (Spec.Rsa.publicPrecomputeApi.name ++ c.montSuffix)
    c.pc c.pubOp.name c.pubOp.code

theorem privCode_depth (c : CrtImpl) : (privCode c).x86_64Depth ≤ privStack := by
  simp only [privCode, Impl.Rsa.X86_64.PrivChecked.code, Impl.Rsa.X86_64.PrivChecked.body,
    Impl.Rsa.X86_64.PrivChecked.check, Impl.Rsa.X86_64.PrivChecked.tail, List.cons_append, List.nil_append,
    Impl.Bignum.X86_64.seqs, Code.x86_64Depth, x86_64Depth_noSp c.nosp, c.depth,
    x86_64Depth_noSp c.pcNosp, c.pcDepth, x86_64Depth_noSp c.pubOp.nosp, c.pubOp.depth]
  decide

/-- `vg_rsa_private_checked` calling `c`, as decryption's callee. -/
def privOf (c : CrtImpl) : PrivImpl where
  name := privName c
  code := privCode c
  ok := privK_eq ▸ code_correct c _ _
  ct := privK_eq ▸ code_constantTime c _ _
  spSafe := code_spSafe c _ _
  depth := privCode_depth c

end VG.Proof.RsaPkcs1Enc.X86_64
