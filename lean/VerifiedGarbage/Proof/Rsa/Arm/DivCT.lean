module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Rsa.Arm.Div
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Rsa.Arm.DivContext

import VerifiedGarbage.Proof.Rsa.Arm.DivStepCT
import VerifiedGarbage.Proof.Rsa.Arm.DivInitCT
import VerifiedGarbage.Proof.Rsa.Arm.DivInit
import VerifiedGarbage.Proof.Rsa.Arm.DivStep
import VerifiedGarbage.Proof.Bignum.Arm.StageCT

/-! # Fixed-iteration division is constant-time for all secret array contents -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (ofNat_beq_zero)

def LoopReady (g : Geometry) (k : Nat) (s : State) : Prop :=
  Context g s ∧ s.gpr .r6 = BitVec.ofNat 32 k

theorem loop_ct {g : Geometry} {k : Nat} (positive : 0 < k) (bound : k < 2 ^ 32) :
    RelCT isa (fun s t => LoopReady g k s ∧ LoopReady g k t) (.loop step .ne) (fun _ _ => True) := by
  let I := fun j (s t : State) => 0 < j ∧ j < 2 ^ 32 ∧ LoopReady g j s ∧ LoopReady g j t
  have body : ∀ j, RelCT isa (I j) step fun s t => isa.eval .ne s = isa.eval .ne t ∧
      (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ l < j, I l s t) := by
    intro j s t tr1 tr2 u v h e1 e2
    obtain ⟨pos, lim, hs, ht⟩ := h
    obtain ⟨trace, _⟩ := step_ct s t tr1 tr2 u v ⟨hs.1, ht.1⟩ e1 e2
    obtain ⟨_, u', eu, cu, zu, hu, _, _, _⟩ := step_ok hs.1
    obtain ⟨_, v', ev, cv, zv, hv, _, _, _⟩ := step_ok ht.1
    obtain ⟨-, rfl⟩ := Exec.det e1 eu
    obtain ⟨-, rfl⟩ := Exec.det e2 ev
    have sub : BitVec.ofNat 32 j - 1 = BitVec.ofNat 32 (j - 1) :=
      BitVec.ofNat_sub_ofNat_of_le j 1 (by decide) (by omega)
    have countU : u.gpr .r6 = BitVec.ofNat 32 (j - 1) := by rw [cu, hs.2, sub]
    have countV : v.gpr .r6 = BitVec.ofNat 32 (j - 1) := by rw [cv, ht.2, sub]
    have zeroU : u.z = decide (j = 1) := by
      rw [zu, hs.2, sub, ofNat_beq_zero (by omega)]
      simp only [show j - 1 = 0 ↔ j = 1 by omega]
    have zeroV : v.z = decide (j = 1) := by
      rw [zv, ht.2, sub, ofNat_beq_zero (by omega)]
      simp only [show j - 1 = 0 ↔ j = 1 by omega]
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [zeroU, zeroV]
    · intro branch
      have ne : j ≠ 1 := by
        intro eq
        change some (!u.z) = some true at branch
        simp only [zeroU, eq, decide_true, Bool.not_true] at branch
        cases branch
      exact ⟨j - 1, by omega, by omega, by omega, ⟨hu, countU⟩, ⟨hv, countV⟩⟩
  exact (RelCT.loop I body k).mono (fun _ _ h => ⟨positive, bound, h⟩) (fun _ _ h => h)

theorem code_ct {g : Geometry} :
    RelCT isa (fun s t => Context g s ∧ Context g t) code (fun _ _ => True) := by
  have wp (s : State) (h : Context g s) : WP isa init s (LoopReady g (32 * g.n)) :=
    WP.mono (init_ok h) (fun _ h => ⟨h.2.2.2.1, h.2.2.1⟩)
  refine (pair_posts (init_ct (g := g)) wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  have pos := h.1.1.positive
  have bound := h.1.1.bound
  exact loop_ct (by omega) (by omega) s t tr1 tr2 u v h e1 e2

end VG.Proof.Rsa.Arm.Div
