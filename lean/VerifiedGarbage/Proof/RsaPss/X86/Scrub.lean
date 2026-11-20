module

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.RsaPss.X86.Inst
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Md5.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.RsaPss.X86.Inst
meta import VerifiedGarbage.Proof.Variants.Sha1.X86
meta import VerifiedGarbage.Proof.Variants.Sha256.X86
meta import VerifiedGarbage.Proof.Framework.QualifiedName
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Sha1.X86.Lit
meta import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Lit
meta import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
meta import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Md5.X86.Lit

/-!
# RSASSA-PSS on x86 (32-bit), without secret residue

`vg_rsa_pss_verify_precomputed`, with the tables of every hash function
(`Proof.Variants.Sha1.X86.variants`, `Proof.Variants.Sha256.X86.variants`),
which it calls indirectly, followed by the zeroing of the stack its
contract reserves and the tail that clears the registers
(`X86.Scrub.scrubFOf`): the functions it calls indirectly are its tables'
(`X86.Scrub.tablesCall`). Its postcondition reads no memory on return
(`X86.Scrub.PostOut`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Scrub

open VG.X86 VG.X86.Scrub
open VG.Proof.RsaPss.X86 (verify_ok)
open VG.Proof.MdHashTable.X86 (mvars)
open VG.Proof.HashTable.X86 (vars)

/-! ## Postconditions -/

theorem verifyOut (tsH tsG : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaPss.verifyPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) stack)
      (Spec.RsaPss.verifyPrecomputedMdTableSig.retBits 32) :=
  postOut_of_local (leak := some _) (ScrubAbi.plain.tables _ _) fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

/-! ## The registration -/

/-- The hash functions of the tables, as PSS's hash. -/
abbrev allMVars : List Proof.MdHashTable.X86.MVar :=
  mvars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants

/-- The hash functions of the tables, as MGF1's. -/
abbrev allVars : List Proof.HashTable.X86.TVar :=
  vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants

/-- `Spec.RsaPss.verifyPrecomputedMdTableApi`, with the tables of every hash
function and the baseline public-key operation. -/
def verifyReg (h : Proof.RsaPss.X86.Sg.OK allMVars allVars) :
    Registration Spec.RsaPss.verifyPrecomputedMdTableApi X86.target :=
  scrubFOf {
      suffix := qualifiedName "" []
      tables := [("hash", Proof.MdHashTable.X86.tables allMVars), ("mgf1", Proof.HashTable.X86.tables allVars)]
      code := Proof.RsaPss.X86.Vf.verifyCode allMVars allVars Proof.RsaPkcs1Sig.X86.Ver.baseline
      verified := verify_ok _ _ h Proof.RsaPkcs1Sig.X86.Ver.baseline
      spSafe := Proof.RsaPss.X86.Vf.code_sp h Proof.RsaPkcs1Sig.X86.Ver.baseline }
    (verifyOut _ _ _)

end VG.Proof.RsaPss.X86.Scrub
