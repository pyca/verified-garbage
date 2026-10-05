import VerifiedGarbage.Impl.Aes.X86.Callee
import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Aes.X86.ExpandKey
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Aes.X86.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.Variant`. -/
section

/-! Contracts and execution properties that every x86 AES variant supplies to callers. -/
namespace VG.Proof.Aes.X86
open VG.X86
structure Ctr32Impl where
  callee : Impl.Aes.X86.Ctr32
  depth : stackUse callee.code = 0
  stack : stackUse callee.code = 0
  ok : ∀ s, Proof.Aes.ctr32X86.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32X86.post s s'
  ct : ConstantTime isa Proof.Aes.ctr32X86.pre Proof.Aes.ctr32X86.pub callee.code
  nosp : NoSp callee.code
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  suffix : String
  features : List String
  expand : Impl.Aes.X86.ExpandKey
  expandDepth : stackUse expand.code = 0
  expandStack : stackUse expand.code = 0
  expandOk : ∀ s, Proof.Aes.expandKeyX86.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyX86.post s s'
  expandCt : ConstantTime isa Proof.Aes.expandKeyX86.pre Proof.Aes.expandKeyX86.pub expand.code
  expandNosp : NoSp expand.code
  expandSpSafe : expand.code.all (fun i => !isa.writesSp i) = true
end VG.Proof.Aes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.VariantProof`. -/
section

namespace VG.Impl.Aes.X86
materialize_code ctr32
materialize_code VG.Impl.Aes.X86.expandKey
end VG.Impl.Aes.X86

namespace VG.Proof.Aes.X86.Ctr32Impl
open VG.X86

def scalar : VG.Proof.Aes.X86.Ctr32Impl where
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

def aesni : VG.Proof.Aes.X86.Ctr32Impl where
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

end
