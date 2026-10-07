import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecContract
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncContract
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

/-!
# The callees of encryption and decryption

`vg_rsa_public_checked` is a `PubImpl` (`pubImpl`). For each implementation `c` of `vg_rsa_private_crt` (a variant of
`RsaPrivateCrt`), `vg_rsa_private_checked` calling it, as
`Generic/RsaPrivateCrt/X86_64/Rsa.lean` emits it, is a `PrivImpl`
(`privOf`): `privK` is its contract, and it uses its frame and two return
addresses of stack, since its callees' callees use none.
-/

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
