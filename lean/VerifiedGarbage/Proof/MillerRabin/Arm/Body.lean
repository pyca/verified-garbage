module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Loop
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The Miller–Rabin round on ARMv7: the body

From the state `σ` after the push (`In P σ`, `ws` in `r0`): the copies,
`y := 1`, the flag and the count (`prep_vp`), the `64 w − 1` bits, and the
flag into `r0` (`body_vp`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- The body's start. -/
def Start (P : MP) (σ s : State) : Prop := s = σ ∧ In P σ ∧ σ.gpr .r0 = P.ws

/-- The body's end: the flag in `r0`. -/
def Done (P : MP) (σ s : State) : Prop :=
  KS P σ (AL P (64 * P.w - 1) σ) LL (VL P (64 * P.w - 1) σ) LSL s ∧
    s.gpr .r0 = BitVec.ofNat 32 (fv P σ (64 * P.w - 1)).toNat

section
variable {P : MP}

/-- The arrays once copied. -/
def AP (P : MP) (σ : State) : Nat → Nat :=
  upd (upd (upd (upd (upd (fun _ => 0) aE (cOf P σ.mem)) aB (xOf P σ)) aOne (oOf P σ)) aM1 (mOf P σ)) aY (oOf P σ)

theorem prep_vp : VP (Start P) (seqs prep) (Lp P (64 * P.w - 1)) := by
  simp only [prep, seqs]
  let E := In P
  let A0 := fun σ : State => upd (fun _ : Nat => 0) aX (num σ.mem P.B P.W aX)
  let K0 := St P E A0 [aX] (fun _ _ => 0) []
  let A1 := fun σ => upd (A0 σ) aE (numAt σ.mem (State.addr P.ws) P.w 0)
  let A2 := fun σ => upd (A1 σ) aB (numAt σ.mem (State.addr P.ws) P.w aX)
  let A3 := fun σ => upd (A2 σ) aOne (numAt σ.mem (State.addr P.ws) P.w 9)
  let A4' := fun σ => upd (A3 σ) aM1 (numAt σ.mem (State.addr P.ws) P.w 10)
  let A5 := fun σ => upd (A4' σ) aY (A4' σ aOne)
  refine VP.seq (G := K0) ?_ (VP.seq (G := St P E A1 [aE, aX] (fun _ _ => 0) []) ?_
    (VP.seq (G := St P E A2 [aB, aE, aX] (fun _ _ => 0) []) ?_
    (VP.seq (G := St P E A3 [aOne, aB, aE, aX] (fun _ _ => 0) []) ?_
    (VP.seq (G := St P E A4' [aM1, aOne, aB, aE, aX] (fun _ _ => 0) []) ?_
    (VP.seq (G := St P E A5 (aY :: [aM1, aOne, aB, aE, aX]) (fun _ _ => 0) []) ?_ ?_)))))
  -- The context.
  · refine VP.taint [.r0] ctx_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨hs, pre, r0⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.1, h₂.1, h₁.2.2, h₂.2.2]
    · rw [hs]
      rw [← List.append_nil ctx]
      have k0 : KS P σ (A0 σ) [aX] (fun _ => 0) [] σ :=
        ⟨pre, rfl, rfl, rfl, Keep.refl _ _ _ _ _, fun j hj => by
          simp only [List.mem_singleton] at hj; subst hj; exact (upd_self _ _ _).symm,
          fun _ h => absurd h List.not_mem_nil, by decide, fun _ h => absurd h List.not_mem_nil⟩
      exact k0.ctx_ok r0 fun t ht hwt _ _ => WP.block_nil ⟨pre, ht, hwt⟩
  · exact St.pcopyClr cE_taint (by decide) (by decide) (by decide) (by decide)
  · exact St.pcopyClrL cB_taint (by decide) (by decide) (by decide) fun σ _ => by
      show upd (A0 σ) aE _ aX = _; rfl
  · exact St.pcopyClr cOne_taint (by decide) (by decide) (by decide) (by decide)
  · exact St.pcopyClr cM1_taint (by decide) (by decide) (by decide) (by decide)
  · exact St.pcopy yOne_taint (by decide) (by decide) (by decide)
  · refine St.pinit.mono (fun _ _ h => h) fun σ s h => ⟨by have := h.1.w4; omega, ?_⟩
    have pre := h.1
    rw [Nat.sub_self]
    refine h.mono (fun i hi => ⟨?_, ?_⟩) (fun d hd => ⟨by simpa using hd, ?_⟩)
    · exact (by decide : ∀ i ∈ LL, i ∈ aY :: [aM1, aOne, aB, aE, aX]) i hi
    · simp only [LL, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · show numAt σ.mem (State.addr P.ws) P.w 0 = cOf P σ.mem * 2 ^ 0 % P.R
        rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt pre.c_lt]
    · simp only [LSL, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · show 64 * P.w - 1 = 64 * P.w - 1 - 0; rfl
      · rfl

theorem body_vp : VP (Start P) body (Done P) := by
  simp only [body, seqs]
  refine prep_vp.seq (VP.seq (G := Lp P 0) ?_ ?_)
  · refine (VP.loop (I := fun k => Lp P k) (fun n => step_vp n) (64 * P.w - 2)).mono (fun σ s h => ?_)
      (fun _ _ h => h)
    have := h.2.2.1.pre.w4
    rw [show 64 * P.w - 2 + 1 = 64 * P.w - 1 by omega]
    exact h
  · refine VP.kv ret_taint (fun _ _ h => h.2.2.2) fun σ s ⟨_, e, h, hw⟩ => ?_
    refine h.ldr hw (d := sF) (by decide) (r := .r0) (by decide) fun t ht _ u => WP.block_nil ⟨?_, u.gpr⟩
    simpa using ht

end

end VG.Proof.MillerRabin.Arm
