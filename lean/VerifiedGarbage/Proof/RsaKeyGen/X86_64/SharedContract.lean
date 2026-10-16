module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedFrame

/-! # Internal RSA candidate contract with room for the shared call -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64

def sharedCandPre (s : State) : Prop :=
  candPre s ∧ SharedEnv (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rsp) s

def sharedCandContract : Contract isa where
  pre := sharedCandPre
  post := candPost
  pub := candPub

end VG.Proof.RsaKeyGen.X86_64
