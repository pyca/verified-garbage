module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFusedByte
import VerifiedGarbage.Proof.Rsa.Arm.RvRest

/-! The public-width byte loop terminates at evaluation of the full exponent. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.RecoverFused

section
variable {P : RP} {E : State → Prop} {j : Nat}

theorem fusedByteLoop_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hj : j < 100)
    (sz : Sizes P) (nowrap : P.B.toNat + P.Z ≤ 2 ^ 32)
    (lengths : P.el + P.dl ≤ 2 * P.K) (positive : 0 < P.el + P.dl) :
    VP (FWI P E j (P.el + P.dl)) (.loop byte .ne) (FWI P E j 0) := by
  let I := fun n σ s => n ≤ P.el + P.dl ∧ FWI P E j n σ s
  have body : ∀ n, VP (I (n + 1)) byte (fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧
        (n = 0 → FWI P E j 0 σ s) ∧ (0 < n → I n σ s)) := by
    intro n
    refine VP.of_imp (p := n < P.el + P.dl) (fun _ _ h => by omega) fun hi => ?_
    refine (fusedByte_vp hn hj sz nowrap lengths hi).mono (fun _ _ h => h.2)
      fun σ s ⟨h, z⟩ => ⟨?_, ?_, ?_⟩
    · change some (!s.z) = some (decide (0 < n))
      rw [z]
      by_cases zero : n = 0 <;> simp [zero, Nat.pos_iff_ne_zero]
    · intro zero; simpa only [zero] using h
    · intro _; exact ⟨by omega, h⟩
  have loop := VP.loop body (P.el + P.dl - 1)
  rw [show P.el + P.dl - 1 + 1 = P.el + P.dl by omega] at loop
  exact loop.mono (fun _ _ h => ⟨Nat.le_refl _, h⟩) (fun _ _ h => h)

end
end VG.Proof.Rsa.Arm.Recover
