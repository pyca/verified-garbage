module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SVerified

/-!
# RSASSA-PSS signing on x86-64: `rsp`

`vg_rsa_pss_sign` writes `rsp` only in its frame's push and pop: each piece
but the private-key operation's call is `Good`, and the call's
implementation writes `rsp` only as its own `spSafe` allows.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.Mgf1.X86_64 (seqs)
open VG.Proof.RsaOaep.X86_64 (Good block_good mgfXor_good selPrologueWith_good zeroOut_good clearEm_good)
open VG.Proof.RsaPkcs1Enc.X86_64 (PrivImpl)

/-- It writes `rsp` only in its frame's push and pop. -/
theorem sign_spSafe (v : PrivImpl) : (sign v.name v.code).all (fun i => !isa.writesSp i) = true := by
  simp only [sign, signBody, signMain, signEnc, signFail, seqs, Code.all, emLen_good.all, zeroOut_good.all,
    clearEm_good.all, mPrefix_good.all, hashM_good.all, putSalt_good.all, putH_good.all, mgfXor_good.all,
    (selPrologueWith_good pssLensH_good pssLensG_good 16 17).all, v.spSafe, Bool.and_true]
  rfl

end VG.Proof.RsaPss.X86_64
