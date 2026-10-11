import VerifiedGarbage.Proof.Blowfish.Arm.Lookup

/-!
# Blowfish on ARMv7: F

`f_run`: F of xL (`r1`) into `lr`, one S-box at a time (`fAcc`).
-/

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-- The registers F writes. -/
def fRegs : List Reg := .lr :: lookRegs

theorem combine_run (u : State) {j : Nat} (hj : j < 4) :
    WP isa (.block [combine j]) u fun t =>
      t.gpr .lr = (if j = 0 then u.gpr .r5 else if j = 2 then u.gpr .lr ^^^ u.gpr .r5
        else u.gpr .lr + u.gpr .r5) ∧ t.mem = u.mem := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    brun [combine]

/-- S-box `j`'s lookup, then its accumulation, from `fAcc … (j - 1)` (or
anything, for `j = 0`) in `lr`. -/
theorem step_run {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) {u : State} (k : Keep fRegs s₀ u)
    (hm : u.mem = s₀.mem) (h3 : 0 < j → u.gpr .lr = fAcc (scheduleAt s₀.mem (State.addr (s₀.gpr .r0)))
      (s₀.gpr .r1) (j - 1)) {Q : State → Prop}
    (hQ : ∀ t, t.gpr .lr = fAcc (scheduleAt s₀.mem (State.addr (s₀.gpr .r0))) (s₀.gpr .r1) j →
      Keep fRegs s₀ t → t.mem = s₀.mem → Q t) :
    WP isa (.seq (lookup j) (.block [combine j])) u Q := by
  have Eu : LookEnv u := E.keep k (by decide) (by decide)
  apply WP.seq
  refine WP.mono (lookup_run Eu hj) fun v ⟨v5, vk, vm⟩ => ?_
  refine WP.mono (WP.keep [.lr] (combine_run v hj) (by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide))
    fun t ⟨⟨t3, tm⟩, tk⟩ => hQ t ?_ ((k.trans vk).trans tk |>.mono (by decide)) (by rw [tm, vm, hm])
  have e0 : u.gpr .r0 = s₀.gpr .r0 := k.gpr (by decide)
  have e1 : u.gpr .r1 = s₀.gpr .r1 := k.gpr (by decide)
  rw [t3, v5, hm, e0, e1, vk.gpr (by decide)]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · rfl
  · rw [h3 (by decide)]; rfl
  · rw [h3 (by decide)]; rfl
  · rw [h3 (by decide)]; rfl

theorem f_run {s : State} (E : LookEnv s) :
    WP isa Impl.Blowfish.Arm.f s fun t =>
      t.gpr .lr = Spec.Blowfish.f (scheduleAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r1) ∧
        Keep fRegs s t ∧ t.mem = s.mem := by
  unfold Impl.Blowfish.Arm.f
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 0) (by decide) (Keep.refl _ _) rfl (fun h => absurd h (by decide))
    fun t0 h0 k0 m0 => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 1) (by decide) k0 m0 (fun _ => h0) fun t1 h1 k1 m1 => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 2) (by decide) k1 m1 (fun _ => h1) fun t2 h2 k2 m2 => ?_
  refine step_run E (j := 3) (by decide) k2 m2 (fun _ => h2) fun t3 h3 k3 m3 => ?_
  exact ⟨by rw [h3, fAcc_three], k3, m3⟩

end VG.Proof.Blowfish.Arm
