module

import VerifiedGarbage.Proof.Rsa.Arm.RvFusedBits
import VerifiedGarbage.Proof.Rsa.Arm.RvFusedByteRead
import VerifiedGarbage.Proof.Rsa.Arm.RvFusedCount
public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedState

/-! A byte advances the shared exponent evaluation by exactly eight bits. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.RecoverFused

def fusedMeta (P : RP) (j k : Nat) : Nat → Nat :=
  upd (upd (upd (upd (fun _ => 0) sCand j) sByte 0)
    sPtr (P.B.toNat + arr P.W wM + k - 1)) sBytes k

def fusedEval (P : RP) (j k : Nat) (σ : State) : VG.Proof.Rsa.Fused.State :=
  VG.Proof.Rsa.Fused.eval P.n (j + 2) (mv P σ / 2 ^ (8 * k))

abbrev FWI (P : RP) (E : State → Prop) (j k : Nat) : State → State → Prop :=
  FI P E j (fusedEval P j k) (fun _ => fusedMeta P j k)

theorem fused_eval_byte (P : RP) (j i : Nat) (σ : State) (hn : 1 < P.n) :
    VG.Proof.Rsa.Fused.bits P.n (j + 2) 8 (mv P σ / 2 ^ (8 * i) % 256)
      (fusedEval P j (i + 1) σ) = fusedEval P j i σ := by
  have powers : 2 ^ (8 * i) * 256 = (2 : Nat) ^ (8 * (i + 1)) := by
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, Nat.pow_add]
  have division : mv P σ / 2 ^ (8 * i) / 256 = mv P σ / 2 ^ (8 * (i + 1)) := by
    rw [Nat.div_div_eq_div_mul, powers]
  have result := VG.Proof.Rsa.Fused.eight_eval P.n (j + 2)
    (mv P σ / 2 ^ (8 * (i + 1))) (mv P σ / 2 ^ (8 * i) % 256) hn (Nat.mod_lt _ (by decide))
  rw [← division, Nat.div_add_mod', division] at result
  exact result

section
variable {P : RP} {E : State → Prop} {j i : Nat}

theorem fusedByte_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hj : j < 100)
    (sz : Sizes P) (nowrap : P.B.toNat + P.Z ≤ 2 ^ 32)
    (lengths : P.el + P.dl ≤ 2 * P.K) (hi : i < P.el + P.dl) :
    VP (FWI P E j (i + 1)) byte (fun σ s => FWI P E j i σ s ∧ s.z = decide (i = 0)) := by
  have wpos : 2 ≤ P.w := by simp only [RP.w]; omega
  have words : P.W = 2 * P.w + 2 := rfl
  have kw := sz.kw
  have fit := fitZ_W sz (show wM < 22 by decide)
  have stride : S P.W = 4 * (P.W + 2) := rfl
  have index : i < 4 * P.W := by omega
  simp only [byte, seqs]
  refine VP.seq ((St.pfusedByteRead index (by decide) (by decide) (fun σ _ => ?_)).mono
    (fun _ _ h => h) (G' := FI P E j (fusedEval P j (i + 1))
      (fun σ => upd (fusedMeta P j (i + 1)) sByte (mv P σ / 2 ^ (8 * i) % 256)))
    (fun σ s h => h.mono (fun k hk => ⟨hk, rfl⟩) (fun k hk => ⟨hk, rfl⟩) ?_)) ?_
  · change fusedV (fusedMeta P j (i + 1)) (fusedEval P j (i + 1) σ) sPtr = _
    dsimp [fusedV, fusedMeta, upd, sPtr, sDone, sOk, sBytes]
  · intro d hd
    refine ⟨List.mem_cons_of_mem _ hd, ?_⟩
    simp only [fusedSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine VP.seq ((fusedEight_vp hn hj (fun _ _ => by simp only [upd_self]; exact Nat.mod_lt _ (by decide))
    (fun _ _ => rfl)).mono (fun _ _ h => h)
      (G' := FI P E j (fusedEval P j i) (fun _ => fusedMeta P j (i + 1))) (fun σ s h => ?_)) ?_
  · simp only [upd_self, fused_eval_byte P j i, hn.2, upd_override] at h
    rw [upd_noop (A := fusedMeta P j (i + 1)) (j := sByte) (v := 0) rfl] at h
    exact h
  refine (St.pfusedByteTail (by decide) (by decide) (fun σ _ => ?_) (fun σ _ => ?_)).mono
    (fun _ _ h => h) fun σ s h => ⟨h.1.mono
      (A' := fun σ => fusedA P j (fusedEval P j i σ)) (L' := fusedKeep)
      (AW' := fun σ => fusedAW P σ) (LW' := [wM])
      (V' := fun σ => fusedV (fusedMeta P j i) (fusedEval P j i σ)) (LS' := fusedSlots)
      (fun k hk => ⟨hk, rfl⟩) (fun k hk => ⟨hk, rfl⟩) ?_, ?_⟩
  · change 1 ≤ fusedV (fusedMeta P j (i + 1)) (fusedEval P j i σ) sPtr ∧
      fusedV (fusedMeta P j (i + 1)) (fusedEval P j i σ) sPtr < 2 ^ 32
    dsimp [fusedV, fusedMeta, upd, sPtr, sDone, sOk, sBytes]
    have lower : 0 < arr P.W wM := by simp only [arr, hdr]; omega
    omega
  · change 1 ≤ fusedV (fusedMeta P j (i + 1)) (fusedEval P j i σ) sBytes ∧
      fusedV (fusedMeta P j (i + 1)) (fusedEval P j i σ) sBytes < 2 ^ 32
    dsimp [fusedV, fusedMeta, upd, sBytes, sDone, sOk]
    omega
  · intro d hd
    refine ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd), ?_⟩
    simp only [fusedSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp [byteTailV, fusedV, fusedMeta, upd, sDone, sOk, sCand, sByte, sPtr, sBytes]
    all_goals omega
  · simpa [fusedV, fusedMeta, upd, sBytes, sDone, sOk] using h.2

end
end VG.Proof.Rsa.Arm.Recover
