module

public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTSetup
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTSetup
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

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
