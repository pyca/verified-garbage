import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl

/-! # A precomputed public operation for verified RSA callers -/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- An implementation of `vg_rsa_public_precomputed_checked`, with the
properties its callers need. The suffix and features propagate to callers. -/
structure PublicImpl where
  name : String
  code : Prog isa
  ok : ∀ s, pdContract.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ pdChkContract.post s s'
  ct : ConstantTime isa pdContract.pre pdContract.pub code
  nosp : NoSp code
  depth : code.depth = 0
  spSafe : code.all (fun i => !isa.writesSp i) = true
  mxSafe : code.allInstrs (fun i => !loadsMxcsr i) = true
  suffix : String
  features : List String

end VG.Proof.Rsa.X86_64
