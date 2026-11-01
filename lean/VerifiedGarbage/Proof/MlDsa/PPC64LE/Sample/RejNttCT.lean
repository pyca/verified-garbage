module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejNtt
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejNtt
meta import VerifiedGarbage.TCB.PPC64LE.Target
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
# ML-DSA on PPC64LE: `vg_mldsa_rej_ntt_poly`, constant time but for the seed, and `Verified`

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/RejNttCT.lean`). Two runs from
entry states whose seeds (the declared leak), pointers and stack pointers
agree leak the same (`all_ct`): the prologue and the blocks around the loop
by the taint analysis, the sponge by `sponge_ct`, and the loop, whose
branches and stores depend on the XOF output, by relating the two runs
iteration by iteration (`body_ct`): both are at the same iteration with the
same coefficients sampled and the same bytes to read, so each branch goes
the same way and each store goes to the same address.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejNtt

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.PPC64LE (relct_noMem)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Spec.MlDsa (Zq q G)
open VG.Proof.MlDsa (PolyIs)
open VG.Spec.Sha3 (bytesAt rates)

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  hp₁ : SpOk (spOf σ₁) σ₁
  hp₂ : SpOk (spOf σ₂) σ₂
  sp : σ₁.sp = σ₂.sp
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  r4 : σ₁.gpr .r4 = σ₂.gpr .r4
  r5 : σ₁.gpr .r5 = σ₂.gpr .r5
  B : B σ₁ = B σ₂

section
variable {σ₁ σ₂ : State} (h : Two σ₁ σ₂)
include h

theorem sp_eq : spOf σ₂ = spOf σ₁ := by simp only [spOf, h.r3, h.r4, h.r5]

theorem X_eq : X σ₁ = X σ₂ := by simp only [X, h.B]

theorem Lt_eq (t : Nat) : Lt σ₁ t = Lt σ₂ t := by simp only [Lt, X_eq h]

theorem V_eq (t : Nat) : V σ₁ t = V σ₂ t := by simp only [V, Xb, X_eq h]

theorem lsp {t t' : Nat} {a b : State} (ha : LAt σ₁ t a) (hb : LAt σ₂ t' b) : a.sp = b.sp := by
  rw [ha.env.sp, hb.env.sp, h.sp]

/-! ## The loop -/

theorem body_ct {t : Nat} (ht : t < 336) :
    RelCT isa (fun a b => LAt σ₁ t a ∧ LAt σ₂ t b) rnBody fun a b =>
      (LAt σ₁ (t + 1) a ∧ (a.gpr .r6 != 0) = decide (t + 1 ≠ 336)) ∧
      (LAt σ₂ (t + 1) b ∧ (b.gpr .r6 != 0) = decide (t + 1 ≠ 336)) := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine relct_wp ?_ fun a b hab => ⟨body_ok hp₁ ht hab.1, body_ok hp₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => M1 σ₁ t a ∧ M1 σ₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨pieceA hp₁ ht hab.1, pieceA hp₂ ht hab.2⟩) ?_
  · exact taint_block [.r3] (fun a b hab => lsp h hab.1 hab.2) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1.r3, hab.2.r3, h.r5]) (by taint_decide)
  refine RelCT.seq (R := fun a b => M2 σ₁ t a ∧ M2 σ₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨pieceB hp₁ ht hab.1, pieceB hp₂ ht hab.2⟩) (relct_noMem rfl)
  refine accept_ct (fun a b hab => lsp h hab.1.lat hab.2.lat) (fun a b hab => ?_) fun a b hab => ?_
  · rw [hab.1.r12, hab.2.r12, V_eq h, Lt_eq h]
  · rw [hab.1.lat.at'.r4, hab.2.lat.at'.r4, Lt_eq h, sp_eq h]

theorem loop_ct :
    RelCT isa (fun a b => LAt σ₁ 0 a ∧ LAt σ₂ 0 b) (.loop rnBody (.nonzero .d .r6)) fun a b =>
      LAt σ₁ 336 a ∧ LAt σ₂ 336 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rnBody) (c := .nonzero .d .r6)
    (Q := fun a b => LAt σ₁ 336 a ∧ LAt σ₂ 336 b)
    (fun n a b => ∃ t, t < 336 ∧ n = 336 - t ∧ LAt σ₁ t a ∧ LAt σ₂ t b) (fun n => ?_) 336)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 336 ∧ n = 336 - t ∧ LAt σ₁ t a ∧ LAt σ₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 336
  · by_cases hn : n = 336 - t
    · refine RelCT.mono (P := fun a b => LAt σ₁ t a ∧ LAt σ₂ t b) (body_ct h ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · rw [eval_nonzero, eval_nonzero, z₁, z₂]
      · have : t + 1 = 336 := by
          have e' : (a.gpr .r6 != 0) = false := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 336 := by
          have e' : (a.gpr .r6 != 0) = true := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨336 - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The whole function -/

theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.PPC64LE.Sample.rejNTT fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := sp_eq h
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  refine RelCT.seq (R := fun a b => J0 (spOf σ₁) σ₁ a ∧ J0 (spOf σ₁) σ₂ b) (relct_wp (pro_rn_ct
    (fun a b hab => by rw [hab.1, hab.2]; exact h.sp) fun a b hab => by rw [hab.1, hab.2]; exact h.r5)
    fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1]; exact WP.mono (pro_rn hp₁ rfl rfl rfl rfl) fun _ x => x.1
  · rw [hab.2]; exact WP.mono (pro_rn hp₂' h.r3.symm h.r4.symm h.r5.symm rfl) fun _ x => x.1
  refine RelCT.seq (R := fun a b => (∃ x, J6 168 1008 (spOf σ₁) σ₁ x a) ∧ (∃ y, J6 168 1008 (spOf σ₁) σ₂ y b))
    (relct_wp (sponge_ct hp₁ hp₂' h.sp (by decide) (by decide)) fun a b hab =>
      ⟨WP.mono (sponge_ok hp₁ (by decide) (by decide) hab.1) fun _ x => ⟨_, x⟩,
        WP.mono (sponge_ok hp₂' (by decide) (by decide) hab.2) fun _ x => ⟨_, x⟩⟩) ?_
  refine RelCT.seq (R := fun a b => LAt σ₁ 336 a ∧ LAt σ₂ 336 b) (RelCT.seq (R := fun a b => LAt σ₁ 0 a ∧ LAt σ₂ 0 b)
    (relct_wp (relct_noMem rfl) fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ =>
      ⟨lat0 hp₁ ha, lat0 hp₂ (by rw [eP]; exact hb)⟩) (loop_ct h)) ?_
  exact retEpi_ct (fun a b hab => lsp h hab.1 hab.2) fun a b hab => by
    rw [hab.1.env.r31, hab.2.env.r31]; exact h.r5

end

/-! ## `Verified` -/

theorem spOk_of {s : State} (h : (Proof.MlDsa.rejNTTContract PPC64LE.abi 48).pre s) : SpOk (spOf s) s := by
  sig_pre [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨by rw [h1]; exact List.mem_singleton_self _, h2, h3, h4, h5, h6, h7, h8, show (34 : Nat) < 2 ^ 64 by decide, h10, h11, h0⟩

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
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.PPC64LE.Sample.RejNtt

namespace VG.Proof.MlDsa.PPC64LE.Sample

open VG VG.PPC64LE
open VG.Proof.MlDsa.Sample
open RejNtt

theorem rejNTT_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Sample.rejNTT (Proof.MlDsa.rejNTTContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h3, hpoly, ha⟩ := correct (spOk_of hs)
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, PPC64LE.abi, PPC64LE.argRegs]
    rw [h3]
    by_cases hf : (rnFold [] (X s)).length = 256
    · rw [ifT hf]
      have hpi := hpoly hf
      exact ⟨fun _ => hpi.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejNTT := 1008 }, by
        show Spec.MlDsa.rejNTTPoly 1008 _ = _
        exact (rejNTT_some hf).trans (congrArg some hpi.2.symm)⟩⟩
    · rw [ifF hf]
      exact ⟨fun e => absurd e (by decide), .inr ⟨rfl, rejNTT_none (B := 1008) (by decide) (by decide) hf⟩⟩
  · sig_pub [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hb, h3, h4, h5⟩ := hpub
    exact (all_ct ⟨spOk_of h₁, spOk_of h₂, hsp, h3, h4, h5, leakBytes_inj hb⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩
      e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Sample
