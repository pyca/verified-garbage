module
public import VerifiedGarbage.Proof.Rsa.Arm.RvSq2

import VerifiedGarbage.Proof.Rsa.Arm.RvCand3
import VerifiedGarbage.Proof.Rsa.Arm.RvCand2

/-! # `vg_rsa_recover_primes` on ARMv7: a candidate (`candBody_vp`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n sqIter sqStep sqStart)

/-- After the candidate `j`. -/
abbrev Cf (P : RP) (E : State → Prop) (j : Nat) : State → State → Prop :=
  St P E (fun σ => Aq P σ j P.c) Lq (fun σ => AWh P σ P.c) [wR] (fun σ => upd (Vq P σ j P.c) sCand (j + 1))
    (sCand :: LSq) P.w nArr

section
variable {P : RP}

theorem candBody_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (h101 : 101 < P.n) (hcl : P.c < 2 ^ 31) (hc0 : 0 < P.c)
    {E : State → Prop} {j : Nat} (hj : j < 100)
    (hE : ∀ σ, E σ → tv P σ ≤ P.c ∧ rv P σ < 2 ^ P.c) :
    VP (Cs P E j) candBody (fun σ s => Cf P E j σ s ∧ s.z = !(decide (j + 1 < 100) && !(sqst P σ j P.c).2.2)) := by
  simp only [candBody, seqs]
  refine VP.assoc (VP.seq (candSet_vp hn h101 hj) (VP.seq (expLoop_vp hn hcl hc0)
    (sqStart_vp hn (fun σ e => (hE σ e).2) (VP.seq (sqLoop_vp hn hcl hc0 (fun σ e => (hE σ e).1)) ?_))))
  refine (St.pcandNext (okb := fun σ => (sqst P σ j P.c).2.2) (by decide) (by decide) fun σ _ => ⟨?_, ?_⟩).mono
    (fun _ _ h => h) fun σ s ⟨h, z⟩ => ⟨St.mono h (fun x hx => ⟨hx, rfl⟩) (fun x hx => ⟨hx, rfl⟩) ?_, ?_⟩
  · simp [Vq, upd, sCand, sCnt, sK, sDone, sOk]; omega
  · simp [Vq, upd, sOk]
  · intro d hd
    refine ⟨hd, ?_⟩
    have : Vq P σ j P.c sCand = j := by simp [Vq, upd, sCand, sCnt, sK, sDone, sOk]
    rw [this]
  · have : Vq P σ j P.c sCand = j := by simp [Vq, upd, sCand, sCnt, sK, sDone, sOk]
    rw [z, this]

end

end VG.Proof.Rsa.Arm.Recover
