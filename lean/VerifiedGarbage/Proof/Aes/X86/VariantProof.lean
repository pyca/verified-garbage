module

public import VerifiedGarbage.Proof.Aes.X86.Variant
meta import VerifiedGarbage.Proof.Aes.X86.Variant
public import VerifiedGarbage.Proof.Aes.X86.Ctr32
meta import VerifiedGarbage.Proof.Aes.X86.Ctr32
public import VerifiedGarbage.Proof.Aes.X86.ExpandKey
meta import VerifiedGarbage.Proof.Aes.X86.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Ctr32
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
public import VerifiedGarbage.Proof.Aes.X86.AesNi.CT
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Aes.X86.AesNi.Body
import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBranches
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyMemory
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyPost
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeySteps
import VerifiedGarbage.Proof.Aes.X86.AesNi.Loops
import VerifiedGarbage.Proof.Aes.X86.Keys
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Body
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.CT
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBranches
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyMemory
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyPost
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeySteps
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Loops
meta import VerifiedGarbage.Proof.Aes.X86.Keys
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Gcm.Spec

@[expose] public section

namespace VG.Impl.Aes.X86
materialize_code ctr32
materialize_code expandKey
end VG.Impl.Aes.X86

namespace VG.Proof.Aes.X86.Ctr32Impl
open VG.X86

def scalar : Ctr32Impl where
  callee := .scalar
  depth := by lit_decide
  stack := by lit_decide
  ok := ctr32_correct
  ct := ctr32_ct
  nosp := NoSp.of_all (by lit_decide)
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []
  expand := .scalar
  expandDepth := by lit_decide
  expandStack := by lit_decide
  expandOk := expandKey_correct
  expandCt := expandKey_ct
  expandNosp := NoSp.of_all (by lit_decide)
  expandSpSafe := Code.all_of_allInstrs (by lit_decide)

def aesni : Ctr32Impl where
  callee := .aesni
  depth := by lit_decide
  stack := by lit_decide
  ok := AesNi.ctr32_correct
  ct := AesNi.ctr32_ct
  nosp := NoSp.of_all (by lit_decide)
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_aesni"
  features := ["aes"]
  expand := .aesni
  expandDepth := by lit_decide
  expandStack := by lit_decide
  expandOk := AesNi.expandKey_correct ⟨AesNi.expand128_ok, AesNi.expand192_ok, AesNi.expand256_ok⟩
  expandCt := AesNi.expandKey_ct
  expandNosp := NoSp.of_all (by lit_decide)
  expandSpSafe := Code.all_of_allInstrs (by lit_decide)

end VG.Proof.Aes.X86.Ctr32Impl
