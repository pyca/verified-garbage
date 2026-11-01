module

import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Ball
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.BallLoop
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Ball
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.BallLoop
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# ML-DSA on PPC64LE: `vg_mldsa_sample_in_ball`, constant time but for `c̃`, and `Verified`

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/BallCT.lean`). Two runs whose `c̃`
(the declared leak), `len`, `τ` (the low 32 bits of `r5`), pointers and stack
pointer agree (`Two`) leak the same: the prologue, the zeroing and the blocks
around the loop by the taint analysis, the sponge by `sponge_ct`, and the
loop, whose branches and addresses depend on the SHAKE256 output, by relating
the two runs iteration by iteration (`body_ct`): both are at the same
iteration with the same `i` and byte `j` (being those of the same output), so
each branch goes the same way, and each piece between the branches is
constant time in registers that hold the same values in both runs.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.Ball

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.PPC64LE (relct_noMem)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Spec.MlDsa (Zq q H IPoly n ofInt toRq)
open VG.Proof.MlDsa (coeffAt PolyIs)
open VG.Spec.Sha3 (bytesAt rates)

/-- Any code, by the taint analysis from the registers `rs`. -/
theorem taint_prog {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs rs)
    (fun a b hab => ⟨hsp a b hab, fun r hr => hP a b hab r (Taint.mem_ofRegs.mp hr)⟩) h

/-- `zx` depends only on the low 32 bits. -/
theorem zx_congr {x y : BitVec 64} (h : x.setWidth 32 = y.setWidth 32) : zx x = zx y :=
  BitVec.eq_of_toNat_eq (by rw [zx_toNat, zx_toNat, h])

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  p₁ : Pre σ₁
  p₂ : Pre σ₂
  sp : σ₁.sp = σ₂.sp
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  r4 : σ₁.gpr .r4 = σ₂.gpr .r4
  r5 : (σ₁.gpr .r5).setWidth 32 = (σ₂.gpr .r5).setWidth 32
  r6 : σ₁.gpr .r6 = σ₂.gpr .r6
  r7 : σ₁.gpr .r7 = σ₂.gpr .r7
  B : B σ₁ = B σ₂

section
variable {σ₁ σ₂ : State} (two : Two σ₁ σ₂)
include two

theorem Two.P_eq : spOf σ₂ = spOf σ₁ := by simp only [spOf, two.r3, two.r4, two.r6, two.r7]
theorem Two.X_eq : X σ₁ = X σ₂ := by simp only [X, two.B]
theorem Two.tau_eq : tau σ₁ = tau σ₂ := by simp only [tau, two.r5]
theorem Two.St_eq (t : Nat) : St σ₁ t = St σ₂ t := by simp only [St, i0, two.X_eq, two.tau_eq]
theorem Two.Xb_eq (t : Nat) : Xb σ₁ t = Xb σ₂ t := by simp only [Xb, two.X_eq]

theorem Two.bsp {t t' : Nat} {a b : State} (ha : BAt σ₁ t a) (hb : BAt σ₂ t' b) : a.sp = b.sp := by
  rw [ha.env.sp, hb.env.sp, two.sp]

/-! ## The loop -/

theorem body_ct {t : Nat} (ht : t < 264) :
    RelCT isa (fun a b => BAt σ₁ t a ∧ BAt σ₂ t b) bBody fun a b =>
      (BAt σ₁ (t + 1) a ∧ (a.gpr .r6 != 0) = decide (t + 1 ≠ 264)) ∧
      (BAt σ₂ (t + 1) b ∧ (b.gpr .r6 != 0) = decide (t + 1 ≠ 264)) := by
  have hp₁ := two.p₁.ok
  have hp₂ := two.p₂.ok
  have hτ₁ : tau σ₁ ≤ 256 := by have := two.p₁.tau_le; omega_arith
  have hτ₂ : tau σ₂ ≤ 256 := by have := two.p₂.tau_le; omega_arith
  have eP := two.P_eq
  refine relct_wp ?_ fun a b hab => ⟨body_ok hp₁ hτ₁ ht hab.1, body_ok hp₂ hτ₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => M1 σ₁ t a ∧ M1 σ₂ t b) (relct_wp (relct_noMem rfl) fun a b hab =>
    ⟨pieceA hp₁ hab.1, pieceA hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun _ _ => True) ?_ (relct_noMem rfl)
  refine RelCT.ite (fun a b h => by rw [eval_zero, eval_zero, h.1.z, h.2.z, two.St_eq]) (relct_noMem rfl) ?_
  have zb : ∀ {a b : State}, M1 σ₁ t a → M1 σ₂ t b → (a.gpr .r12 == 0) = false → (b.gpr .r12 == 0) = false :=
    fun ha hb e => by rw [hb.z, ← two.St_eq, ← ha.z]; exact e
  refine RelCT.seq (R := fun a b => T1 σ₁ t a ∧ T1 σ₂ t b) (relct_wp (taint_block [.r3]
      (fun a b h => two.bsp h.1.1.bat h.1.2.bat) (fun a b h r hr => by
        rw [List.mem_singleton] at hr; subst hr; rw [h.1.1.bat.r3, h.1.2.bat.r3, eP]) (by taint_decide))
    fun a b h => by
      have za : (a.gpr .r12 == 0) = false := by rw [eval_zero] at h; exact Option.some.inj h.2
      exact ⟨tryA hp₁ ht h.1.1 za, tryA hp₂ ht h.1.2 (zb h.1.1 h.1.2 za)⟩) ?_
  refine RelCT.ite (fun a b h => by rw [eval_zero, eval_zero, h.1.z, h.2.z, two.St_eq, two.Xb_eq]) ?_
    (relct_noMem rfl)
  refine taint_block [.r4, .r8, .r30] (fun a b h => two.bsp h.1.1.bat h.1.2.bat) (fun a b h r hr => ?_)
    (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.1.1.bat.r4, h.1.2.bat.r4, eP, two.St_eq]
  · rw [h.1.1.r8, h.1.2.r8, two.Xb_eq]
  · rw [h.1.1.bat.env.r30, h.1.2.bat.env.r30, eP]

theorem loop_ct :
    RelCT isa (fun a b => BAt σ₁ 0 a ∧ BAt σ₂ 0 b) (.loop bBody (.nonzero .d .r6)) fun a b =>
      BAt σ₁ 264 a ∧ BAt σ₂ 264 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := bBody) (c := .nonzero .d .r6)
    (Q := fun a b => BAt σ₁ 264 a ∧ BAt σ₂ 264 b)
    (fun n a b => ∃ t, t < 264 ∧ n = 264 - t ∧ BAt σ₁ t a ∧ BAt σ₂ t b) (fun n => ?_) 264)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 264 ∧ n = 264 - t ∧ BAt σ₁ t a ∧ BAt σ₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 264
  · by_cases hn : n = 264 - t
    · refine RelCT.mono (P := fun a b => BAt σ₁ t a ∧ BAt σ₂ t b) (body_ct two ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · rw [eval_nonzero, eval_nonzero, z₁, z₂]
      · have : t + 1 = 264 := by
          have e' : (a.gpr .r6 != 0) = false := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 264 := by
          have e' : (a.gpr .r6 != 0) = true := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨264 - (t + 1), by omega_arith, t + 1, by omega_arith, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The whole function -/

theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.PPC64LE.Sample.sampleInBall fun _ _ => True := by
  have hp₁ := two.p₁.ok
  have hp₂ := two.p₂.ok
  have eP := two.P_eq
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  have hτ₁ : tau σ₁ ≤ 256 := by have := two.p₁.tau_le; omega_arith
  have hτ₂ : tau σ₂ ≤ 256 := by have := two.p₂.tau_le; omega_arith
  have ez := zx_congr two.r5
  -- the prologue
  refine RelCT.seq (R := fun (a b : State) => (J0 (spOf σ₁) σ₁ a ∧ a.gpr .r27 = zx (σ₁.gpr .r5)) ∧
      (J0 (spOf σ₁) σ₂ b ∧ b.gpr .r27 = zx (σ₂.gpr .r5))) (relct_wp (pro_ball_ct
    (fun a b hab => by rw [hab.1, hab.2]; exact two.sp) fun a b hab => by rw [hab.1, hab.2]; exact two.r7)
    fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1]; exact pro_ball hp₁ rfl (by simp) rfl rfl
  · rw [hab.2]; exact pro_ball hp₂' two.r3.symm (by rw [← two.r4]; simp) two.r6.symm two.r7.symm
  -- the sponge
  refine RelCT.seq (R := fun (a b : State) => (∃ x, J6 136 272 (spOf σ₁) σ₁ x a ∧ x.gpr .r27 = zx (σ₁.gpr .r5)) ∧
      (∃ y, J6 136 272 (spOf σ₁) σ₂ y b ∧ y.gpr .r27 = zx (σ₂.gpr .r5)))
    (relct_wp (RelCT.mono (sponge_ct hp₁ hp₂' two.sp (by decide) (by decide)) (fun a b h => ⟨h.1.1, h.2.1⟩)
      fun _ _ h => h) fun a b hab =>
      ⟨WP.mono (sponge_ok hp₁ (by decide) (by decide) hab.1.1) fun _ x => ⟨_, x, hab.1.2⟩,
        WP.mono (sponge_ok hp₂' (by decide) (by decide) hab.2.1) fun _ x => ⟨_, x, hab.2.2⟩⟩) ?_
  -- the zeroing
  refine RelCT.seq (R := fun a b => ZDone σ₁ a ∧ ZDone σ₂ b) (relct_wp (taint_prog [.r30]
      (fun a b h => by
        obtain ⟨⟨x, ha, _⟩, ⟨y, hb, _⟩⟩ := h; rw [ha.j0.env.sp, hb.j0.env.sp, two.sp])
      (fun a b h r hr => by
        obtain ⟨⟨x, ha, _⟩, ⟨y, hb, _⟩⟩ := h
        rw [List.mem_singleton] at hr; subst hr; rw [ha.j0.env.r30, hb.j0.env.r30]) (by taint_decide))
    fun a b ⟨⟨x, ha, h₁⟩, ⟨y, hb, h₂⟩⟩ => ⟨zero_ok hp₁ ha h₁, zero_ok hp₂ (by rw [eP]; exact hb) h₂⟩) ?_
  -- the loop
  refine RelCT.seq (R := fun a b => BAt σ₁ 264 a ∧ BAt σ₂ 264 b) (RelCT.seq (R := fun a b => BAt σ₁ 0 a ∧ BAt σ₂ 0 b)
    (relct_wp (taint_block [.r27, .r30, .r31] (fun a b h => by rw [h.1.env.sp, h.2.env.sp, two.sp])
      (fun a b h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.r27, h.2.r27, ez]
        · rw [h.1.env.r30, h.2.env.r30, eP]
        · rw [h.1.env.r31, h.2.env.r31, eP]) (by taint_decide))
      fun a b h => ⟨setup_ok hp₁ hτ₁ h.1, setup_ok hp₂ hτ₂ h.2⟩) (loop_ct two)) ?_
  -- the end
  exact retEpi_ct (fun a b hab => two.bsp hab.1 hab.2) fun a b hab => by
    rw [hab.1.env.r31, hab.2.env.r31, eP]

end

/-! ## `Verified` -/

theorem pre_of {s : State} (h : (Proof.MlDsa.sampleInBallContract PPC64LE.abi 48).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, b1, b2, b3, f1, f2, f3, hb⟩ := h
  simp only [Proof.MlDsa.ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb
  exact ⟨⟨by rw [h1]; exact List.mem_singleton_self _, h2, d1, d2, d3, b1, b2, b3, (s.gpr .r4).isLt, f2, f3, h0⟩,
    by simp only [tau]; omega_arith⟩

theorem post_of {s₀ s : State}
    (h3 : s.gpr .r3 = (if (ballFold (tau s₀) (X s₀)).2 = 256 then 1 else 0))
    (hc : (ballFold (tau s₀) (X s₀)).2 = 256 → PolyIs s.mem (s₀.gpr .r6) (toRq (ballFold (tau s₀) (X s₀)).1)) :
    (Proof.MlDsa.sampleInBallContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, PPC64LE.abi, PPC64LE.argRegs]
  rw [h3]
  by_cases hf : (ballFold (tau s₀) (X s₀)).2 = 256
  · rw [ifT hf]
    obtain ⟨hred, hpoly⟩ := hc hf
    exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with ball := 272 }, by
      show Option.map toRq (Spec.MlDsa.sampleInBall (tau s₀) 272 (B s₀)) =
        some (Proof.MlDsa.polyAt s.mem (s₀.gpr .r6))
      rw [sampleInBall_some _ (by decide) hf]
      exact congrArg some hpoly.symm⟩⟩
  · rw [ifF hf]
    exact ⟨fun h1 => absurd h1 (by decide), .inr ⟨rfl, by
      show Option.map toRq (Spec.MlDsa.sampleInBall (tau s₀) 221 (B s₀)) = none
      rw [sampleInBall_none _ (B := 272) (by decide) (by decide) hf]; rfl⟩⟩

theorem leakBytes_inj : ∀ {a b : List Byte}, a.map (fun x => x.toNat) = b.map (fun x => x.toNat) → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, leakBytes_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 32 | .r5 => 39 | .r6 => 0x2000 | .r7 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.PPC64LE.Sample.Ball

namespace VG.Proof.MlDsa.PPC64LE.Sample

open VG VG.PPC64LE
open Ball

theorem sampleInBall_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Sample.sampleInBall (Proof.MlDsa.sampleInBallContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h3, hc, hpres⟩ := correct (pre_of hs)
    exact ⟨t, s', he, hpres, post_of h3 hc⟩
  · sig_pub [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hb, h3, h4, h5, h6, h7⟩ := hpub
    exact (all_ct ⟨pre_of h₁, pre_of h₂, hsp, h3, h4, h5, h6, h7, leakBytes_inj hb⟩ s₁ s₂ t₁ t₂ s₁' s₂'
      ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Sample
