module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VVerified

/-!
# RSASSA-PSS verification on x86-64: `rsp`

`vg_rsa_pss_verify_precomputed` writes `rsp` only in its frame's push and
pop: each piece but the public operation's call is `Good`, and the call's
implementation writes `rsp` only as its own `spSafe` allows.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.Mgf1.X86_64 (seqs)
open VG.Proof.RsaOaep.X86_64 (Good block_good mgfXor_good selPrologueWith_good)
open VG.Proof.Rsa.X86_64 (PublicImpl)

/-- It writes `rsp` only in its frame's push and pop. -/
theorem ver_spSafe (v : PublicImpl) : (verify v.name v.code).all (fun i => !isa.writesSp i) = true := by
  simp only [verify, verifyBody, verifyMain, seqs, Code.all, emLen_good.all, anyArgs_good.all, posScan_good.all,
    posCheck_good.all, saltBack_good.all, mgfXor_good.all,
    (selPrologueWith_good pssLensH_good pssLensG_good 8 9).all, v.spSafe, Bool.and_true]
  rfl

end VG.Proof.RsaPss.X86_64
