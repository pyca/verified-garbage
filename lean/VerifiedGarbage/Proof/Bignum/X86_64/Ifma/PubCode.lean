module
public import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma
public import VerifiedGarbage.Proof.Bignum.Amm52
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedMain
public import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked

import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubMain
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCode
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedChecked

/-! # `vg_rsa_public_precomputed_checked_ifma`: correctness -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma.Pub
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Bignum.X86_64.FoldedPublic
open VG.Proof.MlKem.X86_64

/-- `vg_rsa_public_precomputed_checked_ifma`: the code runs only for a valid `e`. -/
theorem checked_correct (M : Mont)
    (hmx : (seqs (phases M)).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : pdContract.pre s) :
    ∃ tr t, Exec isa (PubIfma.checked M.mm) s tr t ∧ abiPreserved s t ∧ pdChkContract.post s t := by
  refine guarded_correct (fun s h hv => codeWith_correct (PubIfma.rest M.mm) (fun hp => rest_ok M hp hmx) s h
      (by simpa only [eValid, eBytes] using hv))
    (fun _ h => pdGeom h) (fun s t hs h => (pdPre_same hs).symm ▸ h) ?_ ?_ s h
  · intro s t s' _ hs hv hp nB hl hpre
    simp only [pdContract, stackArg_same hs, hs.rdi, hs.rsi, hs.rdx, hs.rcx, hs.r8, hs.r9, hs.mem] at hp
    simp only [eValid, eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, ↓reduceIte]
    exact hp nB hl hpre
  · intro s s' h hv hb hax nB _ _
    simp only [eValid, eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, Bool.false_eq_true, ite_false, Spec.Rsa.written, hax]
    exact ⟨rfl, hb⟩

end VG.Proof.Bignum.X86_64.Ifma.Pub
