module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseK
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseC
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on AArch64: the rejection sampling loop

`signLoop` and `signIteration` on the arguments of the function entered in
`σ` (`loopF`, `iterF`): an iteration is rejected and the loop continues
(`iter_rej`), or it passes (`iter_pass`), within `maxBounds`; or `signLoop`
returns nothing within `minBounds` (`iter_none`, `loop_none_ball`,
`loop_none_exh`): its `SampleInBall` did not finish, or it was the 814th
rejected. With the layout check of the loop (`lChk`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep wp_movz wp_nil)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem paramsOk {p : Params} (h : Ok3 p) : ParamsOk p := by
  rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

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
          (List.range p.k).map (hF p (Am p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ c)) else none) :=
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
  rw [iterF, signIteration_eq, signCommit_eq, h]; rfl

end

/-! ## The end of the loop -/

theorem loop_none_ball {p : Params} {σ : State} {t : Nat} (h : RejT p σ t)
    (hn : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none) : loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inr (by rw [Nat.zero_add]; exact iter_none hn))

theorem loop_none_exh {p : Params} {σ : State} (h : RejT p σ 814) : loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inl (by decide))

/-! ## An iteration -/

/-- What the end of an iteration needs of the layout. -/
def lChk (p : Params) : Bool :=
  inB (sgW p) (sc oCNT) 8 && inB (sgB p) (sc oCNT) 8 && ikChk p [(sc oCNT, 8)] && keepB (sgR p) (sgW p) [(sc oCNT, 8)] (sc oKAP) 8 &&
    keepB (sgR p) (sgW p) [(sc oCNT, 8)] (sc oCT) (cLen p) && famChk (sgR p) (sgW p) [(sc oCNT, 8)] (yBase p) p.ℓ &&
    famChk (sgR p) (sgW p) [(sc oCNT, 8)] 5 p.k && icwChk p [] p.k && keepB (sgR p) (sgW p) [] (sc oCT) (cLen p) &&
    keepB (sgR p) (sgW p) [] cP 1024 && ikChk p [] &&
    keepB (sgR p) (sgW p) [(sc oKAP, 8)] (sc oCNT) 8 && inB (sgW p) (sc oKAP) 8 && ikChk p [(sc oKAP, 8)]

theorem lChk_ok {p : Params} (h : Ok3 p) : lChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem one_sub_one : (1 : BitVec 64) - BitVec.ofNat 64 1 = 0 := by decide

theorem eval_w0 (s : State) : isa.eval (.nonzero .w .x0) s = some ((s.gpr .x0).setWidth 32 != 0) := rfl

/-! ## The loop -/

theorem eval_x9 (s : State) : isa.eval (.nonzero .x .x9) s = some (s.gpr .x9 != 0) := rfl

end VG.Proof.MlDsa.AArch64.Sign
