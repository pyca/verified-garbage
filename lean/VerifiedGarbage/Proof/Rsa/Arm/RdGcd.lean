module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.RdTwos
public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw

import VerifiedGarbage.Proof.Rsa.Arm.InverseCT
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # `vg_rsa_recover_primes_det` on ARMv7: the GCD and the products

`gcd_vp`: after the halvings, `gcd(u, x / 2^k)` by `gcdOnly` (`1` where
`u = 1`), for an odd `u`; the step `g` of a product, with the product's
formula (`ProdF`; Appendix C.2's model calls it `prodStep`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Inv (Gk nk)
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr aW)
open VG.Proof.Rsa (sub32 b2n)

section
variable {P : RP}

/-! ## The GCD -/

/-- `gcd(u, x / 2^k)`, as the code computes it. -/
abbrev gV (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  if (ts P f σ (32 * P.w)).1 = 1 then 1 else Nat.gcd (ts P f σ (32 * P.w)).2.1 (ts P f σ (32 * P.w)).1

def AG (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (upd (upd (fun _ => 0) aOneN 1) aZN 0) aN P.n) aG (gV P f σ)
def AWG (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wX3 (ts P f σ (32 * P.w)).2.2
def VG' (P : RP) (σ : State) : Nat → Nat := upd (fun _ => 0) sOkDE (b2n (okDEv P σ))

abbrev LG : List Nat := [aG, aN, aZN, aOneN]

/-- After the GCD. -/
abbrev GS (P : RP) (E : State → Prop) (f : Nat × Nat × Nat → Nat × Nat × Nat) : State → State → Prop :=
  Dk P E (AG P f) LG (AWG P f) LWT (VG' P) [sOkDE] P.w nArr

theorem invArrs_eq : invArrs = [0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14] := rfl

theorem gcd_vp [InvLaw] {um : Bool} {f : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop}
    (hodd : ∀ σ, E σ → (ts P f σ (32 * P.w)).1 % 2 = 1) :
    VP (fun σ s => E σ ∧ TI P f σ (32 * P.w) s) (gcd um) (GS P E f) := by
  simp only [gcd, seqs]
  -- `[0] := x / 2^k`.
  let AC := fun σ => upd (AT P f σ (32 * P.w)) aGx (AT P f σ (32 * P.w) aX2)
  refine VP.seq (G := Dk P E AC (aGx :: LT) (fun σ => AWT P f σ (32 * P.w)) LWT (fun σ => VT P σ (32 * P.w)) LST
    P.w nArr) (VP.dctx gcdCopy_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ =>
      WP.mono (h.copy_w hw (o := aGx) (a := aX2) (by decide) (by decide) (by decide) (by decide))
        fun t ⟨ht, hwt, _, _⟩ => ⟨e, ht, hwt⟩) ?_
  -- `gcdOnly`: `[1] = gcd(x / 2^k, u)` where `u > 1`.
  let GI := fun σ s => Dk P E (fun σ => AT P f σ (32 * P.w)) [aU, aN, aZN, aOneN] (fun σ => AWT P f σ (32 * P.w))
    LWT (fun σ => VT P σ (32 * P.w)) LST P.w nArr σ s ∧
    (1 < (ts P f σ (32 * P.w)).1 → num s.mem P.B P.w aG1 =
      Nat.gcd (ts P f σ (32 * P.w)).2.1 (ts P f σ (32 * P.w)).1)
  refine VP.seq (G := GI) (VP.of_ct (fun σ₁ σ₂ s t tr1 tr2 u v h e1 e2 =>
    ⟨gcdOnly_ct s t tr1 tr2 u v trivial trivial
      ⟨by rw [h.1.2.2.r7, h.2.2.2.r7], by rw [h.1.2.2.r8, h.2.2.2.r8], by rw [h.1.2.2.r9, h.2.2.2.r9]⟩ e1 e2,
      trivial⟩) fun σ s ⟨e, h, hw⟩ => ?_) ?_
  · have sz := h.sizes
    have g : Gk s P.B P.Z P.w P.w nArr := ⟨hw.nowrap, hw.writable, hw.fits, hw.wpos, le_refl _, hw.wle, hw.r7,
      hw.r8, hw.r9⟩
    refine WP.mono (InvLaw.gcdK_ok g (by decide) (by decide)
      (by have := sz.sw; have := sz.w6a; simp only [S] at *; omega_arith)) fun t ⟨gt, k, r, v⟩ => ⟨⟨e, ?_, ?_⟩, ?_⟩
    · have fitI : ∀ j ∈ invArrs, arr P.w j + S P.w ≤ P.Z := fun j hj => fitZ_w sz (by
        rw [invArrs_eq] at hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      refine h.core k fitI (by decide) (by rw [r.gpr _ (by decide), h.r8]) r.sp r.rd r.wr (fun j hj => ?_)
        (by decide) (h.arrsW_w k (by rw [invArrs_eq]; decide) (by decide)) h.liveW_lt
        (h.sl_keep k (by decide)) h.ls_ok
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;>
        (rw [k.num (by rw [invArrs_eq]; decide) (by decide) (fit_w sz (by decide))]
         rw [h.arrs _ (by decide)]
         simp only [AC]; rd_ev)
    · exact hw.of (gt.r7.trans hw.r7.symm) (gt.r8.trans hw.r8.symm) (gt.r9.trans hw.r9.symm) r.wr
    · intro hu
      have o := hodd σ e
      have v0 : nk s.mem P.B P.w 0 P.w = (ts P f σ (32 * P.w)).2.1 := by
        have := h.arrs aGx (by decide); simp only [AC, upd_self] at this
        change num s.mem P.B P.w aGx = _; rw [this]
        simp only [AT]; rd_ev
      have vM : nk s.mem P.B P.w aM P.w = (ts P f σ (32 * P.w)).1 := by
        have := h.arrs aU (by decide); change num s.mem P.B P.w aU = _; rw [this]; simp only [AC, AT]; rd_ev
      rw [vM, v0] at v
      change nk t.mem P.B P.w 1 P.w = _
      rw [v o hu, Nat.gcd_comm]
  -- `u = 1`, and the GCD into `aG`.
  refine VP.dctx gcdPost_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, hg⟩ => ?_
  have h1 := h.addLive (j := aG1) (by decide)
  simp only [gcdPost]
  refine WP.seq (WP.mono (h1.eqS_w hw (d := sU1) (a := aU) (b := aOneN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s1 ⟨h2, hw2, _⟩ => ?_)
  refine WP.mono (h2.sel_w hw2 (o := aG) (a := aG1) (b := aOneN) (sl := sU1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rd_up; split <;> omega_using []) (by decide)) fun t ⟨ht, hwt, _⟩ => ⟨e, ?_, hwt⟩
  refine ht.mono (fun j hj => ?_) (fun j hj => ⟨hj, by simp only [AWG, AWT]⟩) (fun d hd => ?_)
  · simp only [LG, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · refine ⟨by decide, ?_⟩
      rw [upd_self]; rd_up
      simp only [AT, AG, gV]; rd_ev
      by_cases u1 : (ts P f σ (32 * P.w)).1 = 1
      · simp [u1]
      · have o := hodd σ e
        simp only [u1, ↓reduceIte]
        exact hg (by omega_using [u1, o])
    all_goals refine ⟨by decide, ?_⟩; simp only [AG, AT]; rd_ev
  · simp only [List.mem_singleton] at hd; subst hd
    exact ⟨by decide, by simp only [VG', VT]; rd_ev⟩

/-! ## Products -/

/-- The step of the products. -/
abbrev ProdF (P : RP) (g : Nat × Nat × Nat → Nat × Nat × Nat) : Prop :=
  ∀ y x a, g (y, x, a) = (y / 2, 2 * x % 2 ^ (32 * P.W), (a + if y % 2 = 0 then 0 else x) % 2 ^ (32 * P.W))

/-- `(y, x, a)` after `k` steps of a product. -/
abbrev pr (g : Nat × Nat × Nat → Nat × Nat × Nat) (y x : Nat) (k : Nat) : Nat × Nat × Nat := g^[k] (y, x, 0)

end

end VG.Proof.Rsa.Arm.RecoverDet
