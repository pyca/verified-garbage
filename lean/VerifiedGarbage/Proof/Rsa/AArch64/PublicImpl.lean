import VerifiedGarbage.Proof.Rsa.AArch64.PdChecked

/-! # A precomputed public operation for verified RSA callers on AArch64 -/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

/-- An implementation of `vg_rsa_public_precomputed_checked`, with the
properties its callers need. The suffix and features propagate to callers. -/
structure PublicImpl where
  name : String
  code : Prog isa
  ok : ∀ s, pdContract.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ pdChkContract.post s s'
  ct : ConstantTime isa pdContract.pre pdContract.pub code
  keepsV : code.allInstrs keepsV = true
  spSafe : code.all (fun i => !isa.writesSp i) = true
  suffix : String
  features : List String

end VG.Proof.Rsa.AArch64
