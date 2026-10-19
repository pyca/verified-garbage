module
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTSetup

import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTReduce
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTReduce
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyMain
import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTLoads
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTLoads
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.CrtKeyParts
import VerifiedGarbage.Proof.Rsa.KeyParts
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyPhases
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyReduce
import VerifiedGarbage.Proof.Rsa.X86_64.KeyChecks
import VerifiedGarbage.Proof.Rsa.X86_64.KeyDbl
import VerifiedGarbage.Proof.Rsa.X86_64.KeyMod
import VerifiedGarbage.Proof.Rsa.X86_64.KeyPhases
import VerifiedGarbage.Proof.Rsa.X86_64.KeySteps
import VerifiedGarbage.Proof.Rsa.X86_64.KeyWide
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Rsa.CrtKeyParts
meta import VerifiedGarbage.Proof.Rsa.KeyParts
meta import VerifiedGarbage.Proof.Rsa.Octets
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyPhases
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyReduce
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTSetup
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyChecks
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyDbl
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyMod
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyPhases
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeySteps
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyWide

/-!
# `vg_rsa_check_crt_key` on x86-64: constant time of `main`

`reduceTop` from `KK` (`reduceTopK_ct`): its header loads from `rdi`, the
rest from the registers they pin, which are public (`w'` and `c` from the
lengths); then `main` as `vg_rsa_check_key`'s (`ckMain_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

/-- `main` is constant time from `M0`. -/
theorem ckMain_ct : RelCT isa (Two M0) Impl.Rsa.X86_64.CheckCrtKey.main fun _ _ => True := by
  rw [crtMain_eq]
  refine RelCT.seqs_append (by simp) (by simp [loadNum]) (RelCT.seq setupK_ct
    (RelCT.mono (P := Two KK) ?_ (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a.kp, h₁, h₂⟩) fun _ _ h => h))
  refine RelCT.seqs_append (by simp [loadNum]) (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum])
    (RelCT.seq (kk_app (by simp [loadNum]) (by simp [VG.Impl.Rsa.X86_64.Crt.eqCheck]) (kk_app (by simp [loadNum])
      (by simp [mulXR, VG.Impl.Rsa.X86_64.Crt.zeroAccs]) (kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PX ld_QR)
      mulXRK_ct) eqCheckK_ct) ?_)
  refine RelCT.seqs_append (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum])
    (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum]) (RelCT.seq
    (ckModChecks_ct (by decide) (by decide) (·.pl) (fun _ _ h => ⟨h.hPl, h.pl1, h.pl2⟩) ld_PM ld_DP
      (by taint_decide)) ?_)
  refine RelCT.seqs_append (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum]) (by simp [loadNum])
    (RelCT.seq (ckModChecks_ct (by decide) (by decide) (·.ql) (fun _ _ h => ⟨h.hQl, h.ql1, h.ql2⟩) ld_QM ld_DQ
      (by taint_decide)) ?_)
  refine RelCT.seqs_append (by simp [loadNum]) (by simp) (RelCT.seq
    (kk_app (by simp [loadNum]) (by simp [eqOne]) (kk_app (by simp [loadNum])
      (by simp [Impl.Rsa.X86_64.CheckCrtKey.reduceTop])
      (kk_app (by simp [loadNum]) (by simp [mulXR, VG.Impl.Rsa.X86_64.Crt.zeroAccs])
      (kk_app (by simp [loadNum]) (by simp [loadNum]) (kk_app (by simp [loadNum]) (by simp [ltMask])
      (kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PM ld_QI) ltXM) ld_QR) mulXRK_ct) reduceTopQK_ct)
      eqOneK_ct)
    ?_)
  exact outK_ct

end VG.Proof.Rsa.X86_64.Key
