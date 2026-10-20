module

public import VerifiedGarbage.Proof.Aes.X86.Variant
public import VerifiedGarbage.Proof.Aes.X86.Ctr32
public import VerifiedGarbage.Proof.Aes.X86.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Ctr32
public import VerifiedGarbage.Proof.Aes.X86.AesNi.CT
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Aes.X86.Variant
meta import VerifiedGarbage.Proof.Aes.X86.Ctr32
meta import VerifiedGarbage.Proof.Aes.X86.ExpandKey
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Ctr32
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.CT
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified
public import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks

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
