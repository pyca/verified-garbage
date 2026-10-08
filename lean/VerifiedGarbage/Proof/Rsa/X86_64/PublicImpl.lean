import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig

/-! # A precomputed public operation for verified RSA callers -/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- An implementation of `vg_rsa_public_precomputed_checked`, with the
properties its callers need: it calls Montgomery multiplication, so its
callers keep the 8 bytes below `rsp` clear for the return address. The
suffix and features propagate to callers. -/
structure PublicImpl where
  name : String
  code : Prog isa
  ok : ∀ s, pdChkContract.clear.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ pdChkContract.post s s'
  ct : ConstantTime isa pdChkContract.clear.pre pdChkContract.pub code
  nosp : NoSp code
  depth : code.depth = 1
  spSafe : code.all (fun i => !isa.writesSp i) = true
  mxSafe : code.allInstrs (fun i => !loadsMxcsr i) = true
  suffix : String
  features : List String

/-- `NoSp` by evaluating the code. -/
theorem noSp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

end VG.Proof.Rsa.X86_64
