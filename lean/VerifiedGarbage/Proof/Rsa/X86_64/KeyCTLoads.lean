module
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTDefs

import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTPieces
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTPieces
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
import VerifiedGarbage.Proof.Rsa.KeyParts
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyPhases
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyReduce
import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTSetup
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
# RSA key checking on x86-64: shared constant-time loads

Shared component loads, comparisons and result extraction from `KK`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

theorem kk_app {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) (h₁ : RelCT isa (Two KK) (seqs a) (Two KK))
    (h₂ : RelCT isa (Two KK) (seqs b) (Two KK)) : RelCT isa (Two KK) (seqs (a ++ b)) (Two KK) :=
  RelCT.seqs_append ha hb (RelCT.seq h₁ h₂)

theorem ld_D : RelCT isa (Two KK) (seqs (loadNum aX sD sDlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pd) (·.dl)
    (fun _ _ h => ⟨h.hD, h.hDl, h.srD, h.dl1, h.dl2⟩) (by taint_decide) (by taint_decide)

theorem ld_PX : RelCT isa (Two KK) (seqs (loadNum aX sP sPlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pp) (·.pl)
    (fun _ _ h => ⟨h.hP, h.hPl, h.srP, h.pl1, h.pl2⟩) (by taint_decide) (by taint_decide)

theorem ld_PM : RelCT isa (Two KK) (seqs (loadNum aM sP sPlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pp) (·.pl)
    (fun _ _ h => ⟨h.hP, h.hPl, h.srP, h.pl1, h.pl2⟩) (by taint_decide) (by taint_decide)

theorem ld_QR : RelCT isa (Two KK) (seqs (loadNum aR sQ sQlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pq) (·.ql)
    (fun _ _ h => ⟨h.hQ, h.hQl, h.srQ, h.ql1, h.ql2⟩) (by taint_decide) (by taint_decide)

theorem ld_QM : RelCT isa (Two KK) (seqs (loadNum aM sQ sQlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pq) (·.ql)
    (fun _ _ h => ⟨h.hQ, h.hQl, h.srQ, h.ql1, h.ql2⟩) (by taint_decide) (by taint_decide)

theorem ld_DP : RelCT isa (Two KK) (seqs (loadNum aX sDP sPlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pdp) (·.pl)
    (fun _ _ h => ⟨h.hDP, h.hPl, h.srDP, h.pl1, h.pl2⟩) (by taint_decide) (by taint_decide)

theorem ld_DQ : RelCT isa (Two KK) (seqs (loadNum aX sDQ sQlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pdq) (·.ql)
    (fun _ _ h => ⟨h.hDQ, h.hQl, h.srDQ, h.ql1, h.ql2⟩) (by taint_decide) (by taint_decide)

theorem ld_QI : RelCT isa (Two KK) (seqs (loadNum aX sQI sPlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pqi) (·.pl)
    (fun _ _ h => ⟨h.hQI, h.hPl, h.srQI, h.pl1, h.pl2⟩) (by taint_decide) (by taint_decide)

theorem ltXN : RelCT isa (Two KK) (seqs (ltMask aX aN)) (Two KK) := ltMaskK_ct (by decide) (by decide) (by taint_decide)

theorem ltXM : RelCT isa (Two KK) (seqs (ltMask aX aM)) (Two KK) := ltMaskK_ct (by decide) (by decide) (by taint_decide)

/-- The result, from `KK`. -/
theorem outK_ct : RelCT isa (Two KK)
    (.block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)) fun _ _ => True :=
  two_taint [.rdi] pins_kk (by taint_decide)

end VG.Proof.Rsa.X86_64.Key
