module

import VerifiedGarbage.Proof.Rsa.Arm.RvFusedBit
public import VerifiedGarbage.Proof.Rsa.RecoverFusedBytes
public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedSquare

/-! Compose the exact bit invariant through one whole exponent byte. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.RecoverFused

section
variable {P : RP} {E : State → Prop} {j : Nat} {st : State → VG.Proof.Rsa.Fused.State}
  {V : State → Nat → Nat}

theorem fusedBits_vp (k : Nat) (hn : P.n % 2 = 1 ∧ 1 < P.n) (hj : j < 100)
    (byte : ∀ σ, E σ → V σ sByte < 256) (cand : ∀ σ, E σ → V σ sCand = j) :
    VP (FI P E j st V) (seqs (List.replicate k bit))
      (FI P E j (fun σ => (VG.Proof.Rsa.Fused.byteBits P.n (j + 2) k (st σ) (V σ sByte)).1)
        (fun σ => upd (V σ) sByte (VG.Proof.Rsa.Fused.byteBits P.n (j + 2) k (st σ) (V σ sByte)).2)) := by
  induction k generalizing st V with
  | zero =>
    simp only [List.replicate_zero, seqs, VG.Proof.Rsa.Fused.byteBits]
    exact VP.block_nil fun σ s h => by simpa only [upd_noop rfl] using h
  | succ k ih =>
    cases k with
    | zero =>
      simp only [List.replicate_succ, List.replicate_zero, seqs, VG.Proof.Rsa.Fused.byteBits]
      exact fusedBit_vp hn hj byte cand
    | succ k =>
      simp only [List.replicate_succ, seqs]
      refine VP.seq (fusedBit_vp hn hj byte cand) ?_
      refine (ih (st := fun σ => fusedNext P j (V σ) (st σ))
        (V := fun σ => upd (V σ) sByte (2 * V σ sByte % 256))
        (fun _ _ => Nat.mod_lt _ (by decide))
        (fun σ e => by simpa only [upd_ne _ _ (show sCand ≠ sByte by decide)] using cand σ e)).mono
          (fun _ _ h => h) ?_
      intro σ s h
      simpa only [VG.Proof.Rsa.Fused.byteBits, upd_self, upd_override, fusedNext, fusedBit] using h

theorem fusedEight_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hj : j < 100)
    (byte : ∀ σ, E σ → V σ sByte < 256) (cand : ∀ σ, E σ → V σ sCand = j) :
    VP (FI P E j st V) (seqs (List.replicate 8 bit))
      (FI P E j (fun σ => VG.Proof.Rsa.Fused.bits P.n (j + 2) 8 (V σ sByte) (st σ))
        (fun σ => upd (V σ) sByte 0)) := by
  refine (fusedBits_vp 8 hn hj byte cand).mono (fun _ _ h => h) fun σ s h => ?_
  simpa only [VG.Proof.Rsa.Fused.byteBits_eight] using h

end
end VG.Proof.Rsa.Arm.Recover
