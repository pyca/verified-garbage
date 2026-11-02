module
public import VerifiedGarbage.Proof.MillerRabin.Arm.Pieces

import VerifiedGarbage.Proof.MillerRabin.Arm.Pieces2
import VerifiedGarbage.Proof.Rsa.Arm.RvBase
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

/-! # The Miller–Rabin round on ARMv7: a run of squarings

`SqS … q0 r st0 k`: a run of `q0` squarings from `st0` (`y` in `aY`, the
flag in `sF`), with the threshold `r` in `sR`, `k` of them left (in `sQ`):
`y` and the flag are `msqs … (q0 − k)` (`Proof/MillerRabin/Arm/Math.lean`).
One squaring goes from `k + 1` left to `k` (`sq_step`), and the loop from
`q0` to none (`sq_loop`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- The witness, Montgomery one and minus one, from `σ`. -/
abbrev xOf (P : MP) (σ : State) : Nat := numAt σ.mem (State.addr P.ws) P.w 5
abbrev oOf (P : MP) (σ : State) : Nat := numAt σ.mem (State.addr P.ws) P.w 9
abbrev mOf (P : MP) (σ : State) : Nat := numAt σ.mem (State.addr P.ws) P.w 10

/-- A piece whose precondition is never met. -/
theorem VP.of_false {F G : State → State → Prop} {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  ⟨fun σ s hs => absurd hs (h σ s), fun _ _ _ _ _ _ ⟨σ, _, h₁, _⟩ => absurd h₁ (h σ _)⟩

/-- A piece under a fact its stage implies. -/
theorem VP.of_imp {F G : State → State → Prop} {c : Prog isa} {p : Prop} (hp : ∀ σ s, F σ s → p)
    (h : p → VP F c G) : VP F c G :=
  ⟨fun σ s hs => (h (hp σ s hs)).wp σ s hs, fun s₁ s₂ t₁ t₂ s₁' s₂' hs e₁ e₂ =>
    match hs with
    | ⟨σ₁, σ₂, h₁, h₂⟩ => (h (hp _ _ h₁)).ct s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, h₁, h₂⟩ e₁ e₂⟩

/-- `y` and the flag after `n` squarings of the run. -/
abbrev sqst (P : MP) (q0 : Nat) (r : State → Nat) (st0 : State → Nat × Bool) (σ : State) (n : Nat) : Nat × Bool :=
  msqs (cOf P σ.mem) P.w (mOf P σ) (r σ) q0 (st0 σ) n

/-- The run's stage with `k` squarings left. -/
def SqS (P : MP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (V : State → Nat → Nat)
    (LS : List Nat) (q0 : Nat) (r : State → Nat) (st0 : State → Nat × Bool) (k : Nat) (σ s : State) : Prop :=
  k ≤ q0 ∧ St P E (fun σ => upd (A σ) aY (sqst P q0 r st0 σ (q0 - k)).1) (aY :: L)
    (fun σ => upd (upd (V σ) sF (sqst P q0 r st0 σ (q0 - k)).2.toNat) sQ k) LS σ s

section
variable {P : MP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat} {q0 : Nat} {r : State → Nat} {st0 : State → Nat × Bool}

theorem sqst_lt (hE : ∀ σ, E σ → In P σ) (h0 : ∀ σ, E σ → (st0 σ).1 < cOf P σ.mem) :
    ∀ σ, E σ → ∀ n, (sqst P q0 r st0 σ n).1 < cOf P σ.mem := by
  intro σ e n
  have := (hE σ e).c3
  cases n with
  | zero => exact h0 σ e
  | succ n => exact mm_lt (by omega)

/-- One squaring. -/
theorem sq_step (hE : ∀ σ, E σ → In P σ) (hYL : aY ∉ L) (hM : aM1 ∈ L) (hX : aX ∉ L) (h2 : 2 ∉ L) (h3 : 3 ∉ L)
    (hF : sF ∈ LS) (hQ : sQ ∈ LS) (hR : sR ∈ LS) (hE2 : sE2 ∉ LS) (hT : sT ∉ LS)
    (vM : ∀ σ, E σ → A σ aM1 = mOf P σ) (vR : ∀ σ, E σ → V σ sR = r σ) (rl : ∀ σ, E σ → r σ < 2 ^ 31)
    (hq0 : q0 < 2 ^ 31) (h0 : ∀ σ, E σ → (st0 σ).1 < cOf P σ.mem) (k : Nat) (fios : Bool := false) :
    VP (SqS P E A L V LS q0 r st0 (k + 1)) (sqStep (fios := fios)) fun σ s =>
      isa.eval .ne s = some (decide (0 < k)) ∧ (k = 0 → SqS P E A L V LS q0 r st0 0 σ s) ∧
        (0 < k → SqS P E A L V LS q0 r st0 k σ s) := by
  by_cases hk : k + 1 ≤ q0
  swap
  · exact VP.of_false fun σ s h => hk h.1
  have lt := sqst_lt (q0 := q0) (r := r) hE h0
  let A1 := fun σ => upd (A σ) aY (sqst P q0 r st0 σ (q0 - (k + 1))).1
  let V1 := fun σ => upd (upd (V σ) sF (sqst P q0 r st0 σ (q0 - (k + 1))).2.toNat) sQ (k + 1)
  let A2 := fun σ => upd (A1 σ) aY (mm (cOf P σ.mem) P.w (A1 σ aY) (A1 σ aY))
  let V3 := fun σ => upd (V1 σ) sE2 (if A2 σ aY = A2 σ aM1 then 1 else 0)
  have a1Y : ∀ σ, A1 σ aY = (sqst P q0 r st0 σ (q0 - (k + 1))).1 := fun σ => upd_self _ _ _
  have a2Y : ∀ σ, A2 σ aY = (sqst P q0 r st0 σ (q0 - k)).1 := fun σ => by
    show mm _ _ (A1 σ aY) (A1 σ aY) = _
    rw [a1Y, show q0 - k = q0 - (k + 1) + 1 by omega]
    rfl
  have a2M : ∀ σ, E σ → A2 σ aM1 = mOf P σ := fun σ e => by
    show upd (upd (A σ) aY _) aY _ aM1 = _
    rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), vM σ e]
  refine VP.mono (F := St P E A1 (aY :: L) V1 LS) ?_ (fun σ s h => h.2) (fun _ _ h => h)
  simp only [sqStep, seqs]
  refine VP.seq (G := St P E A2 (aY :: L) V1 LS) ?_
    (VP.seq (G := St P E A2 (aY :: L) V3 (sE2 :: LS)) ?_ ?_)
  -- `y²`.
  · exact St.psqY (fios := fios) hYL h2 h3 (fun σ e => by rw [a1Y]; exact lt σ e _)
  -- `y = −1`.
  · exact St.peqS eq2_taint List.mem_cons_self (List.mem_cons_of_mem _ hM) (by decide) (by decide)
      (fun h => (List.mem_cons.mp h).elim (fun e => absurd e (by decide)) hX) hT (by decide)
  -- The flag and the count.
  · have vQ : ∀ σ, E σ → V3 σ sQ = k + 1 := fun σ _ => by
      show upd (upd (upd (V σ) sF _) sQ (k + 1)) sE2 _ sQ = _
      rw [upd_ne _ _ (by decide), upd_self]
    have vR3 : ∀ σ, E σ → V3 σ sR = r σ := fun σ e => by
      show upd (upd (upd (V σ) sF _) sQ (k + 1)) sE2 _ sR = _
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), vR σ e]
    have vE : ∀ σ, E σ → V3 σ sE2 =
        (decide (mm (cOf P σ.mem) P.w (sqst P q0 r st0 σ (q0 - (k + 1))).1
          (sqst P q0 r st0 σ (q0 - (k + 1))).1 = mOf P σ)).toNat := fun σ e => by
      show upd (V1 σ) sE2 (if A2 σ aY = A2 σ aM1 then 1 else 0) sE2 = _
      rw [upd_self, a2M σ e]
      show (if mm _ _ (A1 σ aY) (A1 σ aY) = _ then 1 else 0) = _
      rw [a1Y]
      split <;> simp_all
    have vF : ∀ σ, E σ → V3 σ sF = (sqst P q0 r st0 σ (q0 - (k + 1))).2.toNat := fun σ _ => by
      show upd (upd (upd (V σ) sF _) sQ (k + 1)) sE2 _ sF = _
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]
    refine (St.psqFlag (k := k) (List.mem_cons_of_mem _ hQ) (List.mem_cons_of_mem _ hR) List.mem_cons_self
      (List.mem_cons_of_mem _ hF) vQ vR3 rl (by omega) vE vF).mono (fun _ _ h => h) fun σ s ⟨h, z⟩ => ?_
    have stage : SqS P E A L V LS q0 r st0 k σ s := by
      refine ⟨by omega, h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨?_, ?_⟩)⟩
      · rcases List.mem_cons.mp hi with rfl | hi'
        · rw [a2Y]; exact (upd_self _ _ _).symm
        · have : i ≠ aY := fun x => hYL (x ▸ hi')
          show upd (upd (A σ) aY _) aY _ i = upd (A σ) aY _ i
          rw [upd_ne _ _ this, upd_ne _ _ this, upd_ne _ _ this]
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))
      · have e : sqst P q0 r st0 σ (q0 - k) = msq (cOf P σ.mem) P.w (mOf P σ) (decide (r σ < k + 1))
            (sqst P q0 r st0 σ (q0 - (k + 1))) := by
          rw [show q0 - k = q0 - (k + 1) + 1 by omega]
          show msq _ _ _ (decide (r σ < q0 - (q0 - (k + 1)))) _ = _
          rw [show q0 - (q0 - (k + 1)) = k + 1 by omega]
        by_cases dQ : d = sQ
        · subst dQ; simp only [upd_self]
        · by_cases dF : d = sF
          · subst dF
            simp only [upd_ne _ _ dQ, upd_self, e, msq]
          · have dE : d ≠ sE2 := fun x => hE2 (x ▸ hd)
            simp only [V3, V1, upd_ne _ _ dQ, upd_ne _ _ dF, upd_ne _ _ dE]
    refine ⟨?_, fun h0 => h0 ▸ stage, fun _ => stage⟩
    show some (!s.z) = _
    rw [z]
    by_cases h0 : k = 0 <;> simp [h0] <;> omega

/-- The run. -/
theorem sq_loop (hE : ∀ σ, E σ → In P σ) (hYL : aY ∉ L) (hM : aM1 ∈ L) (hX : aX ∉ L) (h2 : 2 ∉ L) (h3 : 3 ∉ L)
    (hF : sF ∈ LS) (hQ : sQ ∈ LS) (hR : sR ∈ LS) (hE2 : sE2 ∉ LS) (hT : sT ∉ LS)
    (vM : ∀ σ, E σ → A σ aM1 = mOf P σ) (vR : ∀ σ, E σ → V σ sR = r σ) (rl : ∀ σ, E σ → r σ < 2 ^ 31)
    (hq0 : q0 < 2 ^ 31) (h0 : ∀ σ, E σ → (st0 σ).1 < cOf P σ.mem) (n : Nat) (fios : Bool := false) :
    VP (SqS P E A L V LS q0 r st0 (n + 1)) (sqLoop (fios := fios)) (SqS P E A L V LS q0 r st0 0) :=
  VP.loop (fun k => sq_step (fios := fios) hE hYL hM hX h2 h3 hF hQ hR hE2 hT vM vR rl hq0 h0 k) n

end

end VG.Proof.MillerRabin.Arm
