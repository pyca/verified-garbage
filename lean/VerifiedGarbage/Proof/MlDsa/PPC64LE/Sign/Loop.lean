module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Checks
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# ML-DSA signing on PPC64LE: the rejection sampling loop

As on 32-bit ARM (`Proof/MlDsa/Arm/Sign/PhaseL.lean`). An iteration
(`iter_ok`) either continues, with the next iteration's head (`IL`), or ends
the loop (`XS`): with `r24 = 1` when it passed, as `signIteration` does
within `maxBounds` after the iterations before were rejected; with
`r24 = 0` when `signLoop` returns nothing within `minBounds` (its
`SampleInBall` did not finish, or it was the 814th rejected). So the loop
(`signLoop_ok`) ends in `XS`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of polyIs_keepW bytes_keepW
  Regs2 zx)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Impl.MlDsa.PPC64LE.KeyGen (callAt seqR)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (passF zF amat Rej ParamsOk signIteration_eqF signLoop_min_none signCommit_eq)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

theorem eval_nonzero_w (s : State) (r : Reg) : isa.eval (.nonzero .w r) s = some ((s.gpr r).setWidth 32 != 0) := by
  change VG.PPC64LE.eval (.nonzero .w r) s = _
  simp [VG.PPC64LE.eval, State.read, Size.bits]

/-! ## The loop of the specification -/

section
variable (p : Params) (σ : State)

/-- `signLoop`'s arguments for the function entered in `σ`: `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, `μ`, `ρ″`. -/
abbrev loopF (b : Bounds) (n κ : Nat) : Option (List Byte × List Poly × List (Vector Bool Spec.MlDsa.n)) :=
  signLoop p b (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) n κ

abbrev iterF (b : Bounds) (κ : Nat) : Option (List Byte × Option (List Poly × List (Vector Bool Spec.MlDsa.n))) :=
  signIteration p b (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) κ

end

section
variable {p : Params} {σ : State} {κ : Nat}

theorem iterF_eq (hp : ParamsOk p) (b : Bounds) :
    iterF p σ b κ = (sampleInBall p.τ b.ball (CTv p σ κ)).map fun c =>
      (CTv p σ κ, if passF p (Am p σ) (S1v p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ c then
        some ((List.range p.ℓ).map (zF p (S1v p σ) (rppOf p σ) κ c),
          (List.range p.k).map (Proof.MlDsa.Sign.hF p (Am p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ c)) else none) :=
  signIteration_eqF hp b _ _ _ _ _ _ κ

theorem cV_eq (h : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    sampleInBall p.τ maxBounds.ball (CTv p σ κ) = some (cV p σ κ) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  simp only [cV, hc, Option.getD_some]

theorem iter_rej (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome)
    (hf : ¬ PassV p σ κ) : iterF p σ maxBounds κ = some (CTv p σ κ, none) := by
  rw [iterF_eq hp, cV_eq h, Option.map_some, ifn hf]

theorem iter_pass (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome)
    (hf : PassV p σ κ) : iterF p σ maxBounds κ =
      some (CTv p σ κ, some ((List.range p.ℓ).map (Zv p σ κ), (List.range p.k).map (Hv p σ κ))) := by
  rw [iterF_eq hp, cV_eq h, Option.map_some, ifp hf]

theorem iter_none (h : sampleInBall p.τ minBounds.ball (CTv p σ κ) = none) : iterF p σ minBounds κ = none := by
  rw [iterF, Proof.MlDsa.Sign.signIteration_eq, signCommit_eq, h]; rfl

end

theorem loop_none_ball {p : Params} {σ : State} {t : Nat} (h : RejT p σ t)
    (hn : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none) : loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inr (by rw [Nat.zero_add]; exact iter_none hn))

theorem loop_none_exh {p : Params} {σ : State} (h : RejT p σ 814) : loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inl (by decide))

/-! ## `SampleInBall` -/

/-- After `SampleInBall`: the commitment, and `c` at `ĉ` if it succeeded. -/
structure IB (p : Params) (STK : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : ICd p STK t σ s
  r01 : (s.gpr .r3).setWidth 32 = 0 ∨ (s.gpr .r3).setWidth 32 = 1
  ok : (s.gpr .r3).setWidth 32 = 1 → PolyIs s.mem (SL p STK σ 0) (toRq (cV p σ (p.ℓ * t))) ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  bad : (s.gpr .r3).setWidth 32 = 0 → sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none

theorem ball_val {τ : Nat} {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => (sampleInBall τ b.ball x).map toRq) r out) (h1 : r = 1)
    (hm : (sampleInBall τ maxBounds.ball x).isSome) :
    out = toRq ((sampleInBall τ maxBounds.ball x).getD (Vector.replicate n 0)) := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
    have e1 := Proof.MlDsa.Sign.sampleInBall_mono (Nat.le_max_left b.ball maxBounds.ball) hc
    have e2 := Proof.MlDsa.Sign.sampleInBall_mono (Nat.le_max_right b.ball maxBounds.ball) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem ball_m {σ : State} : KeyGen.BallOk (slay2 p STK σ) sWb2 (sc oCT) (cLen p) p.τ cP (sc oPS) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hc : 0 < cLen p ∧ cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega
  exact ⟨⟨sptr_ok rfl (by decide), by csep hF⟩, ⟨sptr_ok rfl (by decide), by csep hF⟩,
    ⟨sptr_ok rfl (by decide), by csep hF⟩, show ix Reg.r31 ∈ sWb2 by decide, show ix Reg.r31 ∈ sWb2 by decide,
    by csep hF, by csep hF, by csep hF, hF.bp, ⟨hc.1, by omega, hF.tau⟩⟩

theorem ball_ok {t : Nat} {σ s : State} (h : ICd p STK t σ s) :
    WP isa (ballAt P (cLen p) p.τ cP) s (IB p STK σ t) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hc : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega
  have hb := h.1.w1b
  unfold ballAt
  refine ball_okX hP h.1.l.k.sc.site hS (ball_m hF) fun s' k' hred hout hmax => ?_
  have hct : bytesAt s.mem (lpa (slay2 p STK σ) (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t) := h.2
  rw [hct] at hout hmax
  refine ⟨⟨h.1.keep k' (by csep hF) (k'.cs .r25 (by decide)) (k'.cs .r27 (by decide)), ?_⟩, ?_,
    fun h1 => ⟨⟨hred h1, ball_val hout h1 (hmax h1)⟩, hmax h1⟩, fun h0 => ?_⟩
  · rw [bytes_keepW h.1.l.k.sc.site.ok k'.frame (by csep hF) (by decide) (by omega)]; exact h.2
  · rcases hout with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  · rcases hout with ⟨e, _⟩ | ⟨_, hn⟩
    · rw [h0] at e; cases e
    · exact Option.map_eq_none_iff.mp hn

end

end VG.Proof.MlDsa.PPC64LE.Sign
