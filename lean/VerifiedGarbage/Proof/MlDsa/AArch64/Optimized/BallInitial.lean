module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallLoop
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFirst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFrame
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.BallLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlKem.AArch64.Sample
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
import VerifiedGarbage.Proof.MlKem.Bits
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.BallLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Sample
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
meta import VerifiedGarbage.Proof.MlKem.Bits
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MlDsa.AArch64.Sample.Ball`, which this module and modules that import it used -/

section

/-!
# ML-DSA on AArch64: `vg_mldsa_sample_in_ball`

Correctness: the prologue, the sponge (272 bytes of SHAKE256 of `c̃`), `c` set
to zeros, the loop (`BallLoop.lean`), which leaves what `bFold` computes, and
the end, which returns whether `i` reached 256. Constant time up to `c̃`, as
for `vg_mldsa_rej_ntt_poly` (`RejNttCT.lean`): the loop, whose branches and
addresses depend on the output, by `memTaint`, since both runs have the same
output and zeros in `c`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep only_write wp_nil wp_lsr ptr_add toNat_lsr agree_of)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H toRq n)
open VG.Proof.MlDsa (PolyIs coeffAt ballParams)
open VG.Spec.Sha3 (bytesAt)

/-- `τ`, the `u32` argument in `w2`. -/
abbrev tauOf (s : State) : Nat := ((s.gpr .x2).setWidth 32).toNat

/-- `vg_mldsa_sample_in_ball(ctilde = x0, len = x1, tau = w2, c = x3, scratch = x4) -> w0`,
with 16 bytes of stack below `sp`. -/
def sbK : Contract isa where
  pre s :=
    let ct : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let c : Region := ⟨s.gpr .x3, 1024⟩
    let scratch : Region := ⟨s.gpr .x4, 2048⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [ct] ∧ s.wr = [c, scratch] ∧ ct.Disjoint c ∧ ct.Disjoint scratch ∧
    c.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint ct ∧ stack.Disjoint c ∧
    stack.Disjoint scratch ∧ ((s.gpr .x1).toNat, tauOf s) ∈ ballParams
  post s s' :=
    (s'.gpr .x0).setWidth 32 =
        (if (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256 then 1 else 0) ∧
      ((ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256 →
        PolyIs s'.mem (s.gpr .x3)
          (toRq (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).1))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    (s₁.gpr .x2).setWidth 32 = (s₂.gpr .x2).setWidth 32 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    bytesAt s₁.mem (s₁.gpr .x0) (s₁.gpr .x1).toNat = bytesAt s₂.mem (s₂.gpr .x0) (s₂.gpr .x1).toNat

namespace Ball

theorem ballParams_le {len τ : Nat} (h : (len, τ) ∈ ballParams) : len ≤ 64 ∧ 39 ≤ τ ∧ τ ≤ 60 := by
  simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  omega_using [h]

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .x0, (σ.gpr .x1).toNat, σ.gpr .x4, σ.gpr .x3, ((σ.gpr .x2).setWidth 32).setWidth 64⟩

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H ((spOf σ).msg σ) 272

theorem X_length (σ : State) : (X σ).length = 272 := H_length _ _

section
variable {σ : State} (hp : sbK.pre σ)
include hp

theorem params : (σ.gpr .x1).toNat ≤ 64 ∧ 39 ≤ tauOf σ ∧ tauOf σ ≤ 60 :=
  ballParams_le hp.2.2.2.2.2.2.2.2.2

theorem spOk : SpOk (spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1, (σ.gpr .x1).isLt⟩

theorem pro_ok : WP isa (.block (pro .x4 .x3 (.addImm .w .x27 .x2 0) (mov .x4 .x1))) σ (J0 (spOf σ) σ) :=
  Sample.pro_ok (spOk hp) rfl rfl (by decide) rfl
    (fun s hs => ⟨_, rfl, only_write _ _ _ _, by
      simp only [State.write, State.read, ite_true, hs .x2 (by decide) (by decide)]
      congr 1
      exact BitVec.add_zero _⟩)
    (fun s hs => ⟨_, rfl, only_write _ _ _ _, by
      simp only [State.write, State.read, Size.bits, ite_true, BitVec.setWidth_eq, hs .x1 (by decide)
        (by decide) (by decide) (by decide), BitVec.add_zero]⟩)

/-- After the sponge, and `c` set to zeros. -/
structure Z (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  zero : ∀ i < 256, coeffAt s.mem (σ.gpr .x3) i = 0

theorem zero_ok {s : State} (h : J6 136 272 (spOf σ) σ s) : WP isa zeroPoly s (Z σ) :=
  WP.mono (zeroPoly_ok (fun i hi => inA (spOk hp) h.env.wr hi) h.env.x26) fun u ⟨k, z, f⟩ =>
    ⟨h.env.keepA (spOk hp) k f, by
      rw [MlKem.bytesAt_frame f (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (a_scr' (spOk hp) (by omega_using [])).symm) (by omega_using []), h.out,
        (H_eq _ _).symm], z⟩

theorem lpre {s : State} (h : Z σ s) : Ball.LPre (X σ) ((spOf σ).at' 840) (σ.gpr .x3) (tauOf σ) s :=
  ⟨fun p hp' => by rw [← h.out, MlKem.bytesAt_getD _ _ hp'],
    fun p hp' => by rw [at_add]; exact inScrRd (spOk hp) h.env.rd h.env.wr (by omega_using [hp']),
    inScrRd (spOk hp) h.env.rd h.env.wr (by omega_using []),
    fun i hi => inA (spOk hp) h.env.wr hi, (a_scr' (spOk hp) (by omega_using [])).symm,
    by rw [h.env.x25], h.env.x26, by rw [h.env.x27]; simp; omega_using [],
    by have := (params hp).2.2; omega_using [this], h.zero⟩

/-- After the loop. -/
structure LP (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  x10 : (s.gpr .x10).toNat = (ballFold (tauOf σ) (X σ)).2
  st : CStored s.mem (σ.gpr .x3) (ballFold (tauOf σ) (X σ)).1

omit hp in
theorem St_264 : Ball.St (X σ) (tauOf σ) 264 = ballFold (tauOf σ) (X σ) := by
  simp only [Ball.St, ballFold]; rw [List.take_of_length_le (by rw [List.length_drop, X_length])]

theorem loopP_ok {s : State} (h : Z σ s) : WP isa bLoop s (LP σ) :=
  WP.mono (Ball.loop_ok (X_length σ) (by have := (params hp).2.2; omega_using [this]) (lpre hp h)) fun u hu => by
    have x10 := hu.x10
    have st := hu.st
    rw [St_264] at x10 st
    exact ⟨h.env.keepA (spOk hp) hu.keep hu.frame, x10, st⟩

/-- The end: the postcondition, and the calling convention. -/
theorem end_ok {s : State} (h : LP σ s) :
    WP isa (.block (.lsr .x .x0 .x10 8 :: epi)) s fun s' => abiPreserved σ s' ∧ sbK.post σ s' := by
  refine wp_lsr (by decide) fun s₁ h₁ e₁ => ?_
  have hl : (ballFold (tauOf σ) (X σ)).2 ≤ 256 := bFold_le (by simp only [n]; omega_using []) _
  have v0 : (s₁.gpr .x0).toNat = if (ballFold (tauOf σ) (X σ)).2 = 256 then 1 else 0 := by
    rw [e₁, toNat_lsr, h.x10]
    split <;> simp only [Nat.reducePow] <;> omega_arith
  refine WP.mono (epi_ok (spOk hp) (h.env.keep h₁.keep h₁.mem)) fun s' ⟨abi, m, k⟩ => ⟨abi, ?_, fun hf => ?_⟩
  · rw [k.get .x0]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, v0]
    split <;> rfl
  · rw [m, h₁.mem]
    refine polyIs_of_coeffAt fun i hi => ?_
    rw [h.st i hi, getElem!_pos _ i hi, getElem!_pos _ i hi]
    simp only [toRq, Vector.getElem_map]

end

theorem correctWith (v : Proof.Sha3.AArch64.Permutation) (σ : State) (hp : sbK.pre σ) :
    ∃ t s', Exec isa (sampleInBallWith v.callee) σ t s' ∧ abiPreserved σ s' ∧ sbK.post σ s' :=
  WP.seq (WP.mono (pro_ok hp) fun _ h1 =>
    WP.seq (WP.mono (spongeWith_ok (v := v) (spOk hp) (rate := 136) (outlen := 272) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (zero_ok hp h2) fun _ h3 =>
        WP.seq (WP.mono (loopP_ok hp h3) fun _ h4 => end_ok hp h4))))

end Ball

end VG.Proof.MlDsa.AArch64.Sample

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H)
open VG.Proof.MlDsa (ballParams)
open VG.Spec.Sha3 (bytesAt)

namespace Ball

/-- The loop's regions. -/
abbrev lrd (σ : State) : List Region := [⟨(spOf σ).at' 840, 272⟩]
abbrev lwr (σ : State) : List Region := [polyR (σ.gpr .x3)]

theorem pub_eq {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂) : spOf σ₁ = spOf σ₂ := by
  rw [spOf, spOf, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1]

theorem X_eq {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂) : X σ₁ = X σ₂ := by
  simp only [X, Sp.msg]; rw [hq.2.2.2.2.2.2]

theorem loop_ct : RelCT isa (Rel2 sbK.pre sbK.pub Z) bLoop fun _ _ => True := by
  refine relMem lrd lwr [.x25, .x26, .x27]
    (fun σ₁ σ₂ _ _ hq => by simp [lrd, lwr, pub_eq hq, hq.2.2.2.1]) (fun σ s hp h => ?_)
    (fun σ s hp h => ?_) (fun σ₁ σ₂ s₁ s₂ p₁ p₂ hq h₁ h₂ => ?_) (by taint_decide)
  · rw [regions (spOk hp) h.env]
    refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
    · rcases mem2 hr with rfl | rfl
      · exact ⟨(spOf σ).scrR, by simp, 840, rfl, by simp⟩
      · exact ⟨polyR (σ.gpr .x3), by simp, 0, (Proof.MlKem.AArch64.ptr_zero _).symm, by simp⟩
    · rw [List.mem_singleton.mp hr, h.env.wr, (spOk hp).wr]
      exact ⟨polyR (σ.gpr .x3), by simp, 0, (Proof.MlKem.AArch64.ptr_zero _).symm, by simp⟩
  · have l := lpre hp h
    obtain ⟨t, u, e, -⟩ := Ball.loop_ok (X_length σ) (by have := (params hp).2.2; omega_using [this])
      (s₀ := s.withRegions (lrd σ) (lwr σ))
      ⟨l.buf, fun p hp' => Proof.MlKem.AArch64.in_rd (Proof.MlKem.AArch64.in_regions
        (List.mem_singleton_self _) (Offset.contains_base _ (by omega_using [hp']) (by omega_using [hp']))),
        ⟨⟨(spOf σ).at' 840, 272⟩, by simp, by simp [Region.Contains]⟩,
        fun i hi => Proof.MlKem.AArch64.in_regions (List.mem_singleton_self _) (coeff_contains _ hi),
        l.disj, l.x25, l.x26, l.x27, l.tau, l.zero⟩
    exact ⟨t, u, e⟩
  · refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.2.1], fun r hr => ?_, fun x hx => ?_⟩
    · rcases mem3 hr with rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, pub_eq hq]
    · obtain ⟨R, hR, hc⟩ := hx
      rcases mem2 hR with rfl | rfl
      · obtain ⟨p, hp', rfl⟩ := Proof.MlKem.AArch64.Sample.at_off hc
        rw [← MlKem.bytesAt_getD s₁.mem _ hp', h₁.out, pub_eq hq, ← MlKem.bytesAt_getD s₂.mem _ hp', h₂.out,
          X_eq hq]
      · rw [byte_zero h₁.zero hc, byte_zero h₂.zero (by rw [← hq.2.2.2.1]; exact hc)]

theorem ctWith (v : Proof.Sha3.AArch64.Permutation) : ConstantTime isa sbK.pre sbK.pub (sampleInBallWith v.callee) := by
  obtain ⟨hint, hhint⟩ := v.mldsaBallTaint
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono (Q := fun _ _ => True)
    (P := Rel2 sbK.pre sbK.pub fun σ s => s = σ)
    ?_ (fun s₁ s₂ h => ⟨s₁, s₂, h.1, h.2.1, h.2.2, rfl, rfl⟩) fun _ _ _ => trivial)
  refine RelCT.seq (relTaintStep (J' := fun σ => J0 (spOf σ) σ) [.x0, .x1, .x3, .x4]
    (fun σ s hp h => by subst h; exact pro_ok hp) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      subst h₁ h₂
      refine ⟨hq.2.2.2.2.2.1, fun r hr => ?_⟩
      rcases mem4 hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.2.1, hq.2.2.2.2.1]) (by taint_decide)) ?_
  refine RelCT.seq (vectorRelTaintStep (J' := fun σ => J6 136 272 (spOf σ) σ) [.x25, .x26, .x27, .x3, .x4]
    (fun σ s hp h => spongeWith_ok (v := v) (spOk hp) (by decide) (by decide) h) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.2.1], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, pub_eq hq]
      · rw [h₁.x3, h₂.x3, pub_eq hq]
      · exact toNat_inj h₁.x4 (by rw [h₂.x4, pub_eq hq])) hhint) ?_
  refine RelCT.seq (relTaintStep (J' := Z) [.x26] (fun σ s hp h => zero_ok hp h)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.2.1], fun r hr => by
      rw [List.mem_singleton.mp hr, h₁.env.x26, h₂.env.x26, pub_eq hq]⟩) (by taint_decide)) ?_
  refine RelCT.seq (relStep (J' := LP) (fun σ s hp h => loopP_ok hp h) loop_ct) ?_
  exact relTaint [.x25] (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.2.1],
    fun r hr => by rw [List.mem_singleton.mp hr, h₁.env.x25, h₂.env.x25, pub_eq hq]⟩) (by taint_decide)

end Ball

end VG.Proof.MlDsa.AArch64.Sample

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H)
open VG.Spec.Sha3 (bytesAt)

/-- A state satisfying the precondition. -/
def sbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 32 | .x2 => 39 | .x3 => 0x2000 | .x4 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem sampleInBall_verifiedWith (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target (Impl.MlDsa.AArch64.Sample.sampleInBallWith v.callee)
    (Proof.MlDsa.sampleInBallContract AArch64.abi 16) :=
  Verified.of_correct (Ball.correctWith v) (Ball.ctWith v)
    { pre := by sig_implies_pre [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, sbK,
        AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, sbK, AArch64.abi,
          AArch64.argRegs]
        dsimp only [sbK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with ball := 272 }, by
            show Option.map _ (Spec.MlDsa.sampleInBall _ 272 _) = _
            rw [sampleInBall_some _ (by decide) hf, hpoly]; rfl⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, by
              show Option.map _ (Spec.MlDsa.sampleInBall _ Spec.MlDsa.minBounds.ball _) = none
              rw [sampleInBall_none (B := 272) _ (by decide) (by decide) hf]; rfl⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, sbK, AArch64.abi,
          AArch64.argRegs] at h
        obtain ⟨hsp, hb, hx0, hx1, hx2, hx3, hx4⟩ := h
        exact ⟨hx0, hx1, hx2, hx3, hx4, hsp, VG.Proof.MlKem.map_toNat_inj hb⟩
      sat := by sig_implies_sat [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, sbK,
        AArch64.abi, AArch64.argRegs] [sbSat] using sbSat }

end VG.Proof.MlDsa.AArch64.Sample

end

end

/-! ## From `BallZero.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/BallSponge.lean`, which only this module imported.
section

/-! Retain the SHAKE continuation relation discarded by the original sampler
wrapper. This uses the existing squeeze contract without specifying an internal
state representation or assuming a particular cursor value. -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlKem.AArch64 (squeeze_callWith stk)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample (padded)
open VG.Spec.Sha3 (bytesAt stateAt rates shakeSuffix)

structure Resume (rate outlen : Nat) (P : Sp) (σ s : State) : Prop where
  first : J6 rate outlen P σ s
  pos : (s.gpr .x0).toNat ≤ rate
  next : ∀ d, Spec.Sha3.squeezeFrom rate (stateAt s.mem P.scr) (s.gpr .x0).toNat d =
    Spec.Sha3.squeezeFrom rate (padded rate shakeSuffix (P.msg σ)) outlen d

variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp
theorem call3Resume_ok (v : Proof.Sha3.AArch64.Permutation) {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2016) {s : State}
    (h : J5 rate outlen P σ s) :
    WP isa (.call ("vg_keccak_squeeze_scratch" ++ v.callee.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)) s (Resume rate outlen P σ) := by
  have hsp := h.env.sp
  have cw : Covers [⟨P.scr, 200⟩, ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩] s.wr :=
    cov_scr hp h.env.wr fun r hr => by
      rcases mem3 hr with rfl | rfl | rfl
      · exact ⟨0, (at_zero).symm, by simp⟩
      · exact ⟨840, rfl, by simp; omega_using [ho]⟩
      · exact ⟨200, rfl, by simp⟩
  refine squeeze_callWith v (st := P.scr) (out := P.at' 840) (sc := P.at' 200) h.x0 h.x1 h.x2 h.x3 h.x4 h.x5 hr
    (Nat.zero_le _)
    (by rw [← at_zero (P := P)]; exact disj_scr (.inl (by omega_using [])) (by omega_using []) (by omega_using [ho]))
    (by rw [← at_zero (P := P)]; exact disj_scr (.inl (by omega_using [])) (by omega_using []) (by omega_using []))
    (disj_scr (.inr (by omega_using [])) (by omega_using [ho]) (by omega_using []))
    (by rw [hsp]; exact hp.sp16) (by rw [stk, hsp]; exact hp.stk_scr.sub_right (sub_scr0 (by omega_using [])))
    (by rw [stk, hsp]; exact stk_scr' hp (by omega_using [ho])) (by rw [stk, hsp]; exact stk_scr' hp (by omega_using []))
    (cov_rd cw) cw fun s' hk hout hpos hresume => ⟨⟨Env.call hp h.env hk ?_, ?_⟩, hpos, ?_⟩
  · intro r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨0, 200, by rw [at_zero], by omega_using []⟩
    · exact .inl ⟨840, outlen, rfl, ho⟩
    · exact .inl ⟨200, 640, rfl, by omega_using []⟩
    · exact .inr rfl
  · rw [hout, h.st]
  · intro d
    rw [hresume d, h.st, Nat.zero_add]

/-- The sponge, from `J0`: `outlen` bytes of SHAKE at `scratch + 840`. -/
theorem spongeResume_ok (v : Proof.Sha3.AArch64.Permutation) {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2016) {s : State}
    (h : J0 P σ s) : WP isa (spongeWith v.callee rate outlen) s (Resume rate outlen P σ) :=
  WP.seq (WP.mono (blk1_ok hp (rate_lt hr) h) fun _ h1 =>
    WP.seq (WP.mono ((call1With_ok (v := v)) hp hr h1) fun _ h2 => WP.seq (WP.mono (blk2_ok hr h2) fun _ h3 =>
      WP.seq (WP.mono ((call2With_ok (v := v)) hp hr h3) fun _ h4 =>
        WP.seq (WP.mono (blk3_ok hr (by omega_using [ho]) h4) fun _ h5 => (call3Resume_ok (v := v)) hp hr ho h5)))))


end VG.Proof.MlDsa.AArch64.Optimized.Ball
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq VMem)
open VG.Impl.MlDsa.AArch64.Optimized.Ball (zeroWide)

def outputR (p : Addr) : Region := ⟨p,1024⟩

theorem zeroWide_ok {s : State} {p : Addr} (hp : s.gpr .x26 = p)
    (hw : ∀ i < 64, InRegions s.wr (wordAddr p i) 16) :
    WP isa zeroWide s fun t => RegKeep [] s t ∧
      Frame [outputR p] s.mem t.mem ∧ ∀ i < 64, t.mem.read (wordAddr p i) 16 = 0 := by
  unfold zeroWide
  rw [List.cons_append,WP.block_cons_iff]
  refine ⟨s.setV .v0 0,rfl,?_⟩
  have hz := VG.Proof.MlKem.AArch64.vupd_setV s .v0 0
  rw [List.nil_append,List.map_eq_flatMap]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k t => RegKeep [] s t ∧ t.v .v0 = 0 ∧ Frame [outputR p] s.mem t.mem ∧
      ∀ i < k, t.mem.read (wordAddr p i) 16 = 0)
    (fun k t hk ⟨ht,hv,hf,hvals⟩ => ?_) 64 (Nat.le_refl _) (s.setV .v0 0)
    ⟨RegKeep.vupd hz,hz.v,by rw [hz.mem]; exact Frame.refl _ _,
      fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
    fun t ⟨ht,_,hf,hvals⟩ => ⟨ht,hf,hvals⟩
  refine wp_strq (a := wordAddr p k) (by omega_using [hk])
    (by rw [ht.gpr .x26 (by simp),hp]; rfl)
    (by rw [ht.wr]; exact hw k hk) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact (ht.trans (RegKeep.vmem hu)).mono (by simp)
  · rw [hu.v]; exact hv
  · rw [hu.mem]
    exact hf.write (List.mem_singleton_self _) _ (Offset.contains_base p (by omega_using [hk]) (by omega_using [hk]))
  · intro i hi
    rw [hu.mem,hv]
    by_cases he : i = k
    · subst i; rw [read_write16]
    · have hsep : Mem.Sep (wordAddr p i) 16 (wordAddr p k) 16 :=
        Offset.sep p (d := 16*i) (e := 16*k) (n := 16) (k := 16) (by omega_using [he]) (by omega_using [hk, hi]) (by omega_using [hk])
      rw [Mem.read_write_sep hsep (by decide)]
      exact hvals i (by omega_using [hi, he])

/-- The SIMD clear preserves the complete calling-convention frame. -/
theorem zeroWide_coeffs {s : State} {p : Addr} (hp : s.gpr .x26 = p)
    (hw : ∀ i<64, InRegions s.wr (wordAddr p i) 16) :
    WP isa zeroWide s fun t => VG.Proof.MlKem.AArch64.Keep [] s t ∧
      Frame [VG.Proof.MlDsa.Sample.polyR p] s.mem t.mem ∧
      ∀ i<256, VG.Proof.MlDsa.coeffAt t.mem p i = 0 := by
  refine WP.mono (WP.preservedV (zeroWide_ok hp hw) (hc := by lit_decide))
    fun t ⟨⟨hk,hf,hz⟩,hv⟩ => ?_
  refine ⟨⟨hk.gpr,hk.rd,hk.wr,hk.sp,hv⟩,hf,fun i hi => ?_⟩
  have hword := hz (i/4) (by omega_using [hi])
  have hread : t.mem.read (p+BitVec.ofNat 64 (4*i)) 4 = 0 := by
    apply Mem.read_eq_of_bytes
    intro j hj
    have hbyte := Mem.extractLsb'_read t.mem (wordAddr p (i/4))
      (n := 16) (j := 4*(i%4)+j) (by omega_using [hj])
    rw [hword] at hbyte
    have ha : wordAddr p (i/4)+BitVec.ofNat 64 (4*(i%4)+j) =
        p+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j := by
      simp only [wordAddr,BitVec.add_assoc,← BitVec.ofNat_add]
      congr 2
      have := Nat.mod_add_div i 4
      omega_using []
    rw [ha] at hbyte
    simpa [BitVec.extractLsb'] using hbyte.symm
  simp only [VG.Proof.MlDsa.coeffAt,Mem.readW,hread]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallInitial.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlDsa.AArch64.Sample.Ball (spOf W St)

abbrev firstBytes (σ : State) := Spec.MlDsa.H ((spOf σ).msg σ) 136
abbrev tailBytes (σ : State) := Spec.Sha3.squeezeFrom 136
  (padded 136 Spec.Sha3.shakeSuffix ((spOf σ).msg σ)) 136 136

structure Initial (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  parser : Parser (spOf σ).a (ballFold (tauOf σ) (firstBytes σ)).1
    (ballFold (tauOf σ) (firstBytes σ)).2
    (W (firstBytes σ) >>> ((ballFold (tauOf σ) (firstBytes σ)).2-(256-tauOf σ))) s
  pos : (s.gpr .x0).toNat≤136
  next : Spec.Sha3.squeezeFrom 136 (stateAt s.mem (spOf σ).scr) (s.gpr .x0).toNat 136=tailBytes σ

 theorem initial_full_ok {σ s : State} (hp : sbK.pre σ) (h : Resume 136 136 (spOf σ) σ s) :
    WP isa (.seq Impl.MlDsa.AArch64.Optimized.Ball.zeroWide Impl.MlDsa.AArch64.Optimized.Ball.first)
      s (fun u => Initial σ u ∧ u.gpr .x0=s.gpr .x0) := by
  have ps := Sample.Ball.spOk hp
  have hl : (firstBytes σ).length=136 := H_length _ _
  refine WP.seq (WP.mono (zeroWide_coeffs h.first.env.x26 (fun i hi => ?_)) fun t ⟨kt,ft,hz⟩ => ?_)
  · rw [h.first.env.wr,ps.wr]
    exact in_regions (List.mem_cons_self ..) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
  have et := h.first.env.keepA ps kt ft
  have ot : bytesAt t.mem ((spOf σ).at' 840) 136=firstBytes σ := by
    rw [MlKem.bytesAt_frame ft (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (a_scr' ps (by decide)).symm) (by decide),h.first.out]
    exact (H_eq _ _).symm
  have st : stateAt t.mem (spOf σ).scr=stateAt s.mem (spOf σ).scr :=
    state_frame ft (fun r hr => by rw [List.mem_singleton.mp hr]; exact ps.a_scr.symm.sub_left (sub_scr0 (by decide)))
  refine WP.mono (first_ok (τ := tauOf σ) (b := (spOf σ).at' 840) hl (by rw [et.x25]) et.x26
    (by rw [et.x27]; simp [tauOf]; omega_using []) (by have := (Sample.Ball.params hp).2.2; omega_using [this])
    (inScrRd ps et.rd et.wr (by decide))
    (fun j hj => by rw [at_add]; exact inScrRd ps et.rd et.wr (by omega_using [hj]))
    (fun j hj => by rw [← ot,MlKem.bytesAt_getD _ _ hj])
    (fun j hj => inA ps et.wr hj) (a_scr' ps (by decide)).symm hz) fun u hu => ?_
  have eqfold : St (firstBytes σ) (tauOf σ) 128=ballFold (tauOf σ) (firstBytes σ) := by
    simp only [St,ballFold]
    rw [List.take_of_length_le (by rw [List.length_drop,hl])]
  refine ⟨⟨et.keepA ps hu.keep hu.frame,?_,?_,?_⟩,by rw [hu.keep.get .x0,kt.get .x0]⟩
  · simpa only [eqfold] using hu.parser
  · rw [hu.keep.get .x0,kt.get .x0]; exact h.pos
  · have su : stateAt u.mem (spOf σ).scr=stateAt t.mem (spOf σ).scr :=
      state_frame hu.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact ps.a_scr.symm.sub_left (sub_scr0 (by decide)))
    rw [su,st,hu.keep.get .x0,kt.get .x0]
    exact h.next 136
theorem initial_ok {σ s : State} (hp : sbK.pre σ) (h : Resume 136 136 (spOf σ) σ s) :
    WP isa (.seq Impl.MlDsa.AArch64.Optimized.Ball.zeroWide Impl.MlDsa.AArch64.Optimized.Ball.first)
      s (Initial σ) := WP.mono (initial_full_ok hp h) fun _ hh => hh.1
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end
