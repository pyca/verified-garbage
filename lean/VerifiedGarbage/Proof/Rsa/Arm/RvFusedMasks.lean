module

import VerifiedGarbage.Proof.Rsa.Arm.RvFusedFlags
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
meta import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
public import VerifiedGarbage.Proof.Rsa.Arm.RvSt
public import VerifiedGarbage.Proof.Rsa.RecoverExp

/-! Root detection masks for a fused exponent bit. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.RecoverFused
open VG.Proof.Rsa (b2n)

section
variable {P : RP} {E : State → Prop} {A AW V : State → Nat → Nat} {L LW LS : List Nat}

def fusedHitV (V : Nat → Nat) (dn ok bit e1 e2 : Bool) : Nat → Nat :=
  upd (upd (upd (upd V sTmp (b2n (!bit)))
    sLive (b2n (!dn && e1 && !bit)))
    sOk (b2n ((ok || (!dn && e1 && !bit)) && !bit)))
    sDone (b2n ((dn || e1 || e2) && !bit))

theorem St.pfusedHit {dn ok bit e1 e2 : State → Bool}
    (slots : sBit ∈ LS ∧ sDone ∈ LS ∧ sOk ∈ LS ∧ sE1 ∈ LS ∧ sE2 ∈ LS)
    (values : ∀ σ, E σ → V σ sBit = b2n (bit σ) ∧ V σ sDone = b2n (dn σ) ∧
      V σ sOk = b2n (ok σ) ∧ V σ sE1 = b2n (e1 σ) ∧ V σ sE2 = b2n (e2 σ)) :
    VP (St P E A L AW LW V LS P.w nArr) hit
      (St P E A L AW LW (fun σ => fusedHitV (V σ) (dn σ) (ok σ) (bit σ) (e1 σ) (e2 σ))
        ([sDone, sOk, sLive, sTmp] ++ LS) P.w nArr) := by
  simp only [hit, seqs]
  refine VP.seq (St.pflagNot (d := sTmp) (a := sBit) (x := bit) ⟨_, by taint_decide⟩ (by decide) (by aesop) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2)) ?_
  refine VP.seq (St.pflagNot (d := sLive) (a := sDone) (x := dn) ⟨_, by taint_decide⟩ (by decide) (by aesop) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2)) ?_
  refine VP.seq (St.pflagBin false (d := sLive) (a := sLive) (x := fun σ => !dn σ) (b := sE1) (y := e1) ⟨_, by taint_decide⟩ (by decide) (by aesop) (by aesop) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2)) ?_
  refine VP.seq (St.pflagBin false (d := sLive) (a := sLive) (x := fun σ => !dn σ && e1 σ) (b := sTmp) (y := fun σ => !bit σ) ⟨_, by taint_decide⟩ (by decide) (by aesop) (by aesop) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2)) ?_
  refine VP.seq (St.pflagBin true (d := sOk) (a := sOk) (x := ok) (b := sLive) (y := fun σ => !dn σ && e1 σ && !bit σ) ⟨_, by taint_decide⟩ (by decide) (by aesop) (by aesop) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2)) ?_
  refine VP.seq (St.pflagBin false (d := sOk) (a := sOk) (x := fun σ => ok σ || (!dn σ && e1 σ && !bit σ)) (b := sTmp) (y := fun σ => !bit σ) ⟨_, by taint_decide⟩ (by decide) (by aesop) (by aesop) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2)) ?_
  refine VP.seq (St.pflagBin true (d := sDone) (a := sDone) (x := dn) (b := sE1) (y := e1) ⟨_, by taint_decide⟩ (by decide) (by aesop) (by aesop) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2)) ?_
  refine VP.seq (St.pflagBin true (d := sDone) (a := sDone) (x := fun σ => dn σ || e1 σ) (b := sE2) (y := e2) ⟨_, by taint_decide⟩ (by decide) (by aesop) (by aesop) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2)) ?_
  refine (St.pflagBin false (d := sDone) (a := sDone) (x := fun σ => dn σ || e1 σ || e2 σ) (b := sTmp) (y := fun σ => !bit σ) ⟨_, by taint_decide⟩ (by decide) (by aesop) (by aesop) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2) (fun σ e => by dsimp [upd, sTmp, sLive, sDone, sOk, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2.1 | exact (values σ e).2.2.2.2)).mono (fun _ _ h => h) fun σ s h => h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) ?_
  intro d hd
  refine ⟨?_, ?_⟩
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    aesop
  · simp only [fusedHitV, upd]
    split_ifs <;> simp_all


def fusedTailV (V : Nat → Nat) (dn bit e1 e2 : Bool) : Nat → Nat :=
  upd (upd V sLive (b2n ((e1 || e2) && bit)))
    sDone (b2n (dn || ((e1 || e2) && bit)))

theorem St.pfusedTail {dn bit e1 e2 : State → Bool}
    (slots : sBit ∈ LS ∧ sDone ∈ LS ∧ sE1 ∈ LS ∧ sE2 ∈ LS)
    (values : ∀ σ, E σ → V σ sBit = b2n (bit σ) ∧ V σ sDone = b2n (dn σ) ∧
      V σ sE1 = b2n (e1 σ) ∧ V σ sE2 = b2n (e2 σ)) :
    VP (St P E A L AW LW V LS P.w nArr) tail
      (St P E A L AW LW (fun σ => fusedTailV (V σ) (dn σ) (bit σ) (e1 σ) (e2 σ))
        ([sDone, sLive] ++ LS) P.w nArr) := by
  simp only [tail, seqs]
  refine VP.seq (St.pflagBin true (d := sLive) (a := sE1) (b := sE2) (x := e1) (y := e2) ⟨_, by taint_decide⟩ (by decide) (by aesop) (by aesop) (fun σ e => by dsimp [upd, sLive, sDone, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2) (fun σ e => by dsimp [upd, sLive, sDone, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2)) ?_
  refine VP.seq (St.pflagBin false (d := sLive) (a := sLive) (b := sBit) (x := fun σ => e1 σ || e2 σ) (y := bit) ⟨_, by taint_decide⟩ (by decide) (by aesop) (by aesop) (fun σ e => by dsimp [upd, sLive, sDone, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2) (fun σ e => by dsimp [upd, sLive, sDone, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2)) ?_
  refine (St.pflagBin true (d := sDone) (a := sDone) (b := sLive) (x := dn) (y := fun σ => (e1 σ || e2 σ) && bit σ) ⟨_, by taint_decide⟩ (by decide) (by aesop) (by aesop) (fun σ e => by dsimp [upd, sLive, sDone, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2) (fun σ e => by dsimp [upd, sLive, sDone, sBit, sE1, sE2] <;> first | rfl | exact (values σ e).1 | exact (values σ e).2.1 | exact (values σ e).2.2.1 | exact (values σ e).2.2.2)).mono (fun _ _ h => h) fun σ s h => h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) ?_
  intro d hd
  refine ⟨by simp_all, ?_⟩
  simp only [fusedTailV, upd]
  split_ifs <;> simp_all

end
end VG.Proof.Rsa.Arm.Recover
