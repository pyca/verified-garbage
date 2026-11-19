module

public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Cmp
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Row
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Control
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Cmp
meta import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Row
meta import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Control
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.SampA
meta import VerifiedGarbage.Proof.MlDsa.Arm.Verify.SampA
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Piece
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Piece
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Call
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Samp
meta import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Norm
meta import VerifiedGarbage.Proof.MlKem.Arm.Loops
meta import VerifiedGarbage.Proof.MlKem.Arm.NttInv
meta import VerifiedGarbage.Proof.MlKem.Arm.RowSum
meta import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad

/-! ### `MlDsa.Arm.Verify.SampC`, which only this module used -/

section

/-!
# ML-DSA verification on 32-bit ARM: `c`, and the samplers

`c = SampleInBall(c̃)`, masked by its result (`ball_piece`); and the samplers
from the checks of the signature (`samples_piece`): after them (`VS4`), `Â`
and `c` are reduced, and `r11` is 1 if every sampler succeeded, with them
those of the standard for some bounds, and 0 if one fails within the least
bounds.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee BallOk ball_okS
  ball_tr polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD andMask_ok masked_poly taint7)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (and11 mask setB seqR sampled)
open VG.Impl.MlKem.Arm (copy)
open VG.Spec.MlDsa (Params toRq normRq rejNTTPoly minBounds Outcome sampleInBall)
open VG.Proof.MlDsa (HintIs PolyIs polyAt Reduced)
open VG.Proof.MlDsa.Verify (vZ vRho aSeed vCt)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers. -/
structure VS4 (p : Params) (STK : Nat) (σ s : State) : Prop where
  vb : VB p STK σ s
  red : ∀ r < p.k, ∀ s' < p.ℓ, Reduced s.mem (aA p STK σ r s')
  redC : Reduced s.mem ((vlay p STK σ).A 0 (oP 15))
  ok : ∃ q : Bool, s.gpr .r11 = flag q ∧
    (q = true → (∀ r < p.k, ∀ s' < p.ℓ,
      ∃ b : Nat, rejNTTPoly b (aSeed (pkOf p σ) r s') = some (polyAt s.mem (aA p STK σ r s'))) ∧
      ∃ b : Nat, (sampleInBall p.τ b (vCt p (sgOf p σ))).map toRq = some (polyAt s.mem ((vlay p STK σ).A 0 (oP 15)))) ∧
    (q = false → (∃ r < p.k, ∃ s' < p.ℓ, rejNTTPoly minBounds.rejNTT (aSeed (pkOf p σ) r s') = none) ∨
      sampleInBall p.τ minBounds.ball (vCt p (sgOf p σ)) = none)

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

omit hP hS in
theorem ball_m {σ : State} :
    BallOk (vlay p STK σ) vWb (.r6, 0) p.ctildeLen p.τ pC (sc oSS) := by
  have hk := hF.k
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ vWb by decide,
    show ix Reg.r7 ∈ vWb by decide, by vsep hF, by vsep hF, by vsep hF, hF.ball.1,
    ⟨by rcases hF.ct with e | e | e <;> omega_using [e], by rcases hF.ct with e | e | e <;> omega_using [e], hF.ball.2⟩⟩

theorem ball_ok {σ s : State} (h : VS p STK p.k 0 σ s) :
    WP isa (sampled (ballAt P (.r6, 0) p.ctildeLen p.τ pC) pC) s (VS4 p STK σ) := by
  have hk := hF.k; have hl := hF.l
  have hs := h.vb.vc.site
  have hL := hs.ok
  unfold sampled ballAt
  refine WP.seq (ball_okS hP.ball hs (by omega_using [hS]) (ball_m hF) fun s₃ k₃ hred hout => ?_)
  have eb : bytesAt s.mem (lpa (vlay p STK σ) (.r6, 0)) p.ctildeLen = vCt p (sgOf p σ) := by
    have := sig_slice h.vb.vc (o := 0) (l := p.ctildeLen) (by have := hF.sig; have := hF.hint; omega_arith)
    rw [List.drop_zero] at this
    exact this
  rw [eb] at hout
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  have kv₃ := h.vb.keep hF k₃ (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  have kA3 : ∀ r < p.k, ∀ s' < p.ℓ, polyAt s₃.mem (aA p STK σ r s') = polyAt s.mem (aA p STK σ r s') ∧
      (Reduced s.mem (aA p STK σ r s') → Reduced s₃.mem (aA p STK σ r s')) := fun r hr s' hs' =>
    ⟨polyAt_keepW hL k₃.frame (by vsep hF) (by decide) rfl, reduced_keepW hL k₃.frame (by vsep hF) (by decide) rfl⟩
  have h11₃ : s₃.gpr .r11 = s.gpr .r11 := k₃.cs .r11 (by decide) (by decide)
  refine WP.mono (andMask_ok kv₃.vc.site (a := pC) ⟨rfl, by vsep hF⟩ (show ix Reg.r7 ∈ vWb by decide) hr01)
    fun s₄ ⟨k₄, r₄, co⟩ => ?_
  obtain ⟨pi, p1, _⟩ := masked_poly hred co
  have kv₄ := (kv₃.r11 (s₃.gpr .r11 &&& s₃.gpr .r0)).keep hF k₄ (by vsep hF [vcChk]) (by vsep hF)
    (fun i hi => by vsep hF)
  have kA4 : ∀ r < p.k, ∀ s' < p.ℓ, polyAt s₄.mem (aA p STK σ r s') = polyAt s₃.mem (aA p STK σ r s') ∧
      (Reduced s₃.mem (aA p STK σ r s') → Reduced s₄.mem (aA p STK σ r s')) := fun r hr s' hs' =>
    ⟨polyAt_keepW hL k₄.frame (by vsep hF) (by decide) rfl, reduced_keepW hL k₄.frame (by vsep hF) (by decide) rfl⟩
  have dn : ∀ r s', s' < p.ℓ → (Dn p.k 0 r s' ↔ r < p.k) := fun r s' _ => by simp only [Dn]; omega_using []
  obtain ⟨q, hq, hok, hbad⟩ := h.ok
  refine ⟨kv₄, fun r hr s' hs' => (kA4 r hr s' hs').2 ((kA3 r hr s' hs').2 (h.red r s' hs' ((dn r s' hs').mpr hr))),
    pi.1, ⟨q && decide (s₃.gpr .r0 = 1), ?_, fun hq' => ⟨fun r hr s' hs' => ?_, ?_⟩, fun hq' => ?_⟩⟩
  · rw [r₄, h11₃, hq, flag_and01 q hr01]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
    obtain ⟨b, hb⟩ := hok hq'.1 r s' hs' ((dn r s' hs').mpr hr)
    exact ⟨b, by rw [(kA4 r hr s' hs').1, (kA3 r hr s' hs').1]; exact hb⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
    show ∃ b, _ = some (polyAt s₄.mem (lpa (vlay p STK σ) pC))
    rw [p1 hq'.2]
    rcases hout with ⟨_, b, hb⟩ | ⟨h0, _⟩
    · exact ⟨b.ball, hb⟩
    · rw [h0] at hq'; exact absurd hq'.2 (by decide)
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hq'
    rcases hq' with hq' | hq'
    · obtain ⟨r, s', hs', hd, hn⟩ := hbad hq'
      exact .inl ⟨r, (dn r s' hs').mp hd, s', hs', hn⟩
    · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
      · exact absurd h1 hq'
      · exact .inr (Option.map_eq_none_iff.mp hn)

omit hP hF hS in
theorem ballTail_taint : (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc (oP 15))))
    (VG.Taint.hintOf VG.Arm.taint (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc 0))))).isSome = true :=
  vAndMask_taint 15 (by decide)

theorem ball_piece : VPiece p STK (VS p STK p.k 0) (VS4 p STK) (sampled (ballAt P (.r6, 0) p.ctildeLen p.τ pC) pC) := by
  have hk := hF.k
  refine ⟨fun _ _ _ h => ball_ok hP hF hS h, ?_⟩
  unfold sampled ballAt
  refine RelCT.seq (R := VTwo p STK) ?_ (vtaint7 ballTail_taint)
  refine RelCT.mono (M := isa) (P := fun (x y : State) => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    bytesAt x.mem (lpa (vlay p STK σ) (.r6, 0)) p.ctildeLen = bytesAt y.mem (lpa (vlay p STK σ) (.r6, 0)) p.ctildeLen)
    (RelCT.exists_ fun σ => ?_) (fun _ _ ⟨σ₁, _, _, _, pub, h₁, h₂⟩ => ?_) fun _ _ h => h
  · have ok := fun x (hs : Site (vlay p STK σ) vWb STK x) => ball_okS hP.ball hs (by omega_using [hS])
      (name := "vg_mldsa_sample_in_ball") (ball_m hF (σ := σ)) (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
    exact (VG.Proof.MlDsa.Arm.KeyGen.RelCT.two (fun _ _ h => h.1)
      (ball_tr hP.ball (by omega_using [hS]) (ball_m hF) fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
      fun x hs => ok x hs).mono (fun _ _ h => h) fun x y h => ⟨σ, h⟩
  · refine ⟨σ₁, vc_twoL pub h₁.vb.vc h₂.vb.vc, ?_⟩
    show bytesAt _ ((vlay p STK σ₁).A 4 0) _ = bytesAt _ ((vlay p STK σ₁).A 4 0) _
    rw [sig_slice h₁.vb.vc (by have := hF.sig; have := hF.hint; omega_arith), pub.2.2.2.2.2.2.2.1, vlay_pub pub,
      sig_slice h₂.vb.vc (by have := hF.sig; have := hF.hint; omega_arith)]

/-! ## The samplers -/

omit hP hS in
theorem rho_piece :
    VPiece p STK (fun σ s => V2 p STK p.ℓ σ s ∧ flag (zOk p σ p.ℓ) ≠ 0) (VS p STK 0 0) (copy .r4 0 .r7 oSB 32) := by
  refine ⟨fun σ s _ ⟨h, hn⟩ => ?_, rel_of (vtaint4 (by native_taint_decide)) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
    ⟨σ₁, vc_twoL pub h₁.1.vc h₂.1.vc⟩⟩
  have hz : zOk p σ p.ℓ = true := by
    cases e : zOk p σ p.ℓ
    · rw [e] at hn; exact absurd rfl hn
    · rfl
  exact rho_ok hF ⟨h.vc, h.hint, h.z, hz⟩ (by rw [h.r11, hz]; rfl)

theorem samples_piece :
    VPiece p STK (fun σ s => V2 p STK p.ℓ σ s ∧ flag (zOk p σ p.ℓ) ≠ 0) (VS4 p STK) (samples P p) :=
  (rho_piece hF).seq ((rows_piece hP hF hS).seq (ball_piece hP hF hS))

end

end VG.Proof.MlDsa.Arm.Verify

end

end

/-!
# ML-DSA verification on 32-bit ARM: the kernel `vg_mldsa*_verify_with_cache`

After the samplers, the NTTs, the rows, the hash and the comparison
(`compute_piece`); what `r11` then says of `verifyMu` (`ke_out`); and the
whole body, piece by piece, for any parameter set of Table 1 and any verified
implementations of the primitives (`body_piece`): a malformed hint gives 0 at
once, a `z` too large 0 after the norms, and otherwise `r11` is the samplers'
result and the comparison of `c̃`. The kernel meets `verifyK`
(`withCache_correct`, `withCache_ct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv relStart hashLay hashLay_ptr)
open VG.Impl.MlKem.Arm (topEnd)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (seqR)
open VG.Spec.MlDsa (Params Bounds verifyMu minBounds toRq rejNTTPoly sampleInBall)
open VG.Proof.MlDsa (polyAt)
open VG.Proof.MlDsa.Verify (vZ vCt vHint aSeed common_bound verifyMu_rows verifyMu_norm verifyMu_hint_none
  verifyMu_rej_none verifyMu_ball_none verifyMu_mono bmax_left bmax_right normR_vZ_iff)
open VG.Proof.MlDsa.KeyGen (ifn)
open VG.Spec.Sha3 (bytesAt)

/-- A piece keeps a fact about the entry state. -/
theorem pieceFrame {Pre : State → Prop} {Pub : State → State → Prop} {I J : State → State → Prop} {c : Prog isa}
    (h : Piece Pre Pub I J c) (F : State → Prop) :
    Piece Pre Pub (fun σ s => I σ s ∧ F σ) (fun σ s => J σ s ∧ F σ) c :=
  ⟨fun σ s hp ⟨hs, hf⟩ => WP.mono (h.ok σ s hp hs) fun _ h' => ⟨h', hf⟩,
    RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, i₁.1, i₂.1⟩) fun _ _ h => h⟩

/-! ## The flags -/

theorem VC.flags {p : Params} {STK : Nat} {σ s : State} (h : VC p STK σ s) (a b : BitVec 32) :
    VC p STK σ (subFlags s a b) :=
  h.congr (fun _ _ => rfl) rfl rfl rfl rfl

theorem V1.flags {p : Params} {STK : Nat} {σ s : State} (h : V1 p STK σ s) {a b : BitVec 32} :
    V1 p STK σ (subFlags s a b) :=
  ⟨h.vc.flags a b, h.r11, h.hint⟩

theorem V2.flags {p : Params} {STK j : Nat} {σ s : State} (h : V2 p STK j σ s) {a b : BitVec 32} :
    V2 p STK j σ (subFlags s a b) :=
  ⟨h.vc.flags a b, h.hint, h.z, h.r11⟩

/-! ## After the samplers -/

theorem vs4_kx {p : Params} {STK : Nat} {σ s : State} (h : VS4 p STK σ s) : KX p STK 0 false 0 σ s := by
  obtain ⟨hh, e, hi⟩ := h.vb.hint
  exact ⟨fun r c => polyAt s.mem (aA p STK σ r c), polyAt s.mem ((vlay p STK σ).A 0 (oP 15)), hh, s.gpr .r11,
    h.vb.vc, e, hi, fun r hr c hc => ⟨h.red r hr c hc, rfl⟩,
    fun i hi => by rw [ifn (Nat.not_lt_zero i)]; exact h.vb.z i hi, ⟨h.redC, rfl⟩,
    fun _ h => absurd h (Nat.not_lt_zero _), rfl, h.ok⟩

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

theorem compute_piece : VPiece p STK (KX p STK 0 false 0) (KE p STK) (compute P p) := by
  unfold compute
  refine Piece.seq (J := KX p STK p.ℓ false 0) ?_ ((nttC_piece hP hF hS).seq
    (Piece.seq (J := KX p STK p.ℓ true p.k) ?_ ((vhash_piece hF).seq (cmp_piece hF))))
  · refine Piece.mono (Piece.seqR (I := fun j => KX p STK j false 0) p.ℓ 0
      fun j _ hj => nttZ_piece hP hF hS (by omega_using [hj])) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun r => KX p STK p.ℓ true r) p.k 0
      fun r _ hr => row_piece hP hF hS (by omega_using [hr])) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

end

/-! ## The result -/

/-- `verifyMu` of the inputs of a run from `σ`, with the bounds `b`. -/
abbrev vv (p : Params) (σ : State) (b : Bounds) : Option Bool := verifyMu p b (pkOf p σ) (muOf σ) (sgOf p σ)

/-- What the result `r` says of `verifyMu`, as `verifyContract` does. -/
abbrev VOut (p : Params) (σ : State) (r : BitVec 32) : Prop :=
  (r = 1 ∧ ∃ b, vv p σ b = some true) ∨ (r = 0 ∧ vv p σ minBounds ≠ some true)

/-- At the end, before the epilogue: the result in `r11`. -/
abbrev VFin (p : Params) (STK : Nat) (σ s : State) : Prop := VC p STK σ s ∧ VOut p σ (s.gpr .r11)

theorem false_ne {p : Params} {σ : State} {b : Bounds} (h : vv p σ b = some false) : vv p σ minBounds ≠ some true :=
  fun hm => by
    have e₁ := verifyMu_mono (bmax_left b minBounds).rejNTT (bmax_left b minBounds).ball h
    have e₂ := verifyMu_mono (bmax_right b minBounds).rejNTT (bmax_right b minBounds).ball hm
    rw [e₁] at e₂
    cases e₂

theorem ke_out {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (h : KE p STK σ s)
    (hz : zOk p σ p.ℓ = true) : VFin p STK σ s := by
  obtain ⟨A', cc, hh, R, vc, e, hl, ⟨q, hR, hok, hbad⟩, r11⟩ := h
  refine ⟨vc, ?_⟩
  rw [r11, hR, flag_and]
  cases q with
  | false =>
    refine .inr ⟨rfl, ?_⟩
    rcases hbad rfl with ⟨r, hr, c, hc, hn'⟩ | hn'
    · show verifyMu p minBounds _ _ _ ≠ some true
      rw [verifyMu_rej_none minBounds _ _ e hr hc hn']; nofun
    · show verifyMu p minBounds _ _ _ ≠ some true
      rw [verifyMu_ball_none minBounds _ _ e hn']; nofun
  | true =>
    obtain ⟨hA, hB⟩ := hok rfl
    obtain ⟨nA, hnA⟩ := common_bound (P := fun r n => ∀ c < p.ℓ, rejNTTPoly n (aSeed (pkOf p σ) r c) = some (A' r c))
      (fun _ _ _ hle h c hc => Proof.MlDsa.Verify.rejNTTPoly_mono hle (h c hc)) p.k fun r hr =>
        common_bound (P := fun c n => rejNTTPoly n (aSeed (pkOf p σ) r c) = some (A' r c))
          (fun _ _ _ hle h => Proof.MlDsa.Verify.rejNTTPoly_mono hle h) p.ℓ fun c hc => hA r hr c hc
    obtain ⟨bB, hbB⟩ := hB
    obtain ⟨c, hc, hc'⟩ := Option.map_eq_some_iff.mp hbB
    have ev := verifyMu_rows p ⟨0, 0, nA, bB⟩ (pkOf p σ) (muOf σ) (sgOf p σ) e hl hnA hc
    have ew : ((List.range p.k).flatMap fun r => Spec.MlDsa.simpleBitPack
        (Proof.MlDsa.Verify.w1Row p (pkOf p σ) (sgOf p σ) A' (Spec.MlDsa.ntt cc) hh r)
        ((Spec.MlDsa.q - 1) / (2 * p.γ₂) - 1)) = w1Enc p σ A' cc hh := rfl
    rw [decide_eq_true ((normR_vZ_iff hF.nb.2 p hF.g1 _).mpr (of_decide_eq_true hz)), hc', Bool.true_and, ew] at ev
    by_cases hE : Spec.MlDsa.H (muOf σ ++ w1Enc p σ A' cc hh) p.ctildeLen = vCt p (sgOf p σ)
    · exact .inl ⟨by rw [decide_eq_true hE]; rfl, ⟨_, ev.trans (congrArg some (beq_iff_eq.mpr hE.symm))⟩⟩
    · exact .inr ⟨by rw [decide_eq_false hE]; rfl,
        false_ne (ev.trans (congrArg some (beq_eq_false_iff_ne.mpr (Ne.symm hE))))⟩

theorem flag_ne {b : Bool} (h : flag b ≠ 0) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

theorem flag_eq {b : Bool} (h : flag b = 0) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

/-! ## The body -/

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

/-- The samplers and the rest, once `z` is small enough. -/
theorem inner_piece :
    VPiece p STK (V2 p STK p.ℓ) (VFin p STK) (ifOk (.seq (samples P p) (compute P p))) := by
  refine ifOk_piece (v := fun σ => flag (zOk p σ p.ℓ)) (fun _ _ _ h => h.r11) (fun σ₁ σ₂ _ _ pub => ?_)
    (fun _ _ _ _ h => h.flags) ?_ fun σ s _ h hv => ⟨h.vc, .inr ⟨h.r11.trans hv, ?_⟩⟩
  · have e : sgOf p σ₁ = sgOf p σ₂ := pub.2.2.2.2.2.2.2.1
    dsimp only [zOk]
    rw [e]
  · refine Piece.mono (pieceFrame ((samples_piece hP hF hS).seq (Piece.mono (compute_piece hP hF hS)
      (fun _ _ _ h => vs4_kx h) fun _ _ _ h => h)) fun σ => zOk p σ p.ℓ = true)
      (fun _ _ _ h => ⟨h, flag_ne h.2⟩) fun _ _ _ ⟨h, hz⟩ => ke_out hF h hz
  · obtain ⟨hh, e, -⟩ := h.hint
    refine verifyMu_norm minBounds _ _ e fun hn => ?_
    have := flag_eq hv
    rw [zOk, decide_eq_false_iff_not] at this
    exact this ((normR_vZ_iff hF.nb.2 p hF.g1 _).mp hn)

omit hP hF hS in
theorem v1_v2 {σ s : State} (h : V1 p STK σ s) (hv : flag (hintOf p σ).isSome ≠ 0) : V2 p STK 0 σ s := by
  cases e : hintOf p σ with
  | none => rw [e] at hv; exact absurd rfl hv
  | some hh =>
    refine ⟨h.vc, ⟨hh, e, h.hint hh e⟩, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
    rw [h.r11, e, show zOk p σ 0 = true from decide_eq_true fun _ h => absurd h (Nat.not_lt_zero _)]
    rfl

omit hP hF hS in
theorem v1_out {σ s : State} (h : V1 p STK σ s) (hv : flag (hintOf p σ).isSome = 0) : VFin p STK σ s := by
  refine ⟨h.vc, .inr ⟨h.r11.trans hv, ?_⟩⟩
  have e : hintOf p σ = none := Option.not_isSome_iff_eq_none.mp (by rw [flag_eq hv]; nofun)
  show verifyMu p minBounds _ _ _ ≠ some true
  rw [verifyMu_hint_none minBounds _ _ e]
  nofun

theorem body_piece : VPiece p STK (fun σ s => VC p STK σ s ∧ s.gpr .r11 = 1) (VFin p STK) (body P p) := by
  have hl := hF.l
  unfold body
  refine (hint_piece hP hF hS).seq (ifOk_piece (v := fun σ => flag (hintOf p σ).isSome) (fun _ _ _ h => h.r11)
    (fun σ₁ σ₂ _ _ pub => ?_) (fun _ _ _ _ h => h.flags) ?_ fun _ _ _ h hv => v1_out h hv)
  · have e : sgOf p σ₁ = sgOf p σ₂ := pub.2.2.2.2.2.2.2.1
    dsimp only [hintOf]
    rw [e]
  · refine Piece.seq (Piece.mono (Piece.seqR (I := fun j => V2 p STK j) p.ℓ 0
      fun j _ hj => zOne_piece hP hF hS (by omega_using [hj])) (fun _ _ _ h => v1_v2 h.1 h.2) fun _ _ _ h => ?_)
      (inner_piece hP hF hS)
    rwa [Nat.zero_add] at h

end

/-! ## The return -/

theorem vepi_ok {p : Params} {STK : Nat} {σ s : State} (h : VFin p STK σ s) :
    WP isa (.block topEnd) s fun s' => Arm.target.abiPreserved σ s' ∧ VOut p σ (s'.gpr .r0) := by
  obtain ⟨vc, hr⟩ := h
  have hs := vc.site
  have e0 : ∀ o, (hashLay (vlay p STK σ) s Kmu).A 0 o = (vlay p STK σ).A 0 o := fun o => by
    simp only [Lay.A, hashLay_ptr _ _ _ (show (0 : Nat) ≠ 1 by decide)]
  refine WP.mono (topEnd_ok (hs.ctx kmu) (by rw [e0]; exact vc.sav) (by rw [e0]; exact vc.lr))
    fun s' ⟨pr, r0, m', sp'⟩ => ⟨⟨pr, sp'.trans vc.sp⟩, ?_⟩
  rw [r0]
  exact hr

theorem vepi_piece {p : Params} {STK : Nat} :
    VPiece p STK (VFin p STK) (fun σ s => Arm.target.abiPreserved σ s ∧ VOut p σ (s.gpr .r0)) (.block topEnd) :=
  ⟨fun _ _ _ h => vepi_ok h, vrel7 (fun _ _ h => h.1) (by native_taint_decide)⟩

/-! ## The kernel -/

/-- The contract of `vg_mldsa*_verify_with_cache` with `STK` bytes of stack:
`VPre`, the result `verifyContract` states (`VOut`), and the public data `vPub`. -/
def verifyK (p : Params) (STK : Nat) : Contract isa where
  pre := VPre p STK
  post σ s := VOut p σ (s.gpr .r0)
  pub := vPub p

theorem withCache_piece {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat}
    (hS : S + 8 ≤ STK) :
    VPiece p STK (fun σ s => s = σ) (fun σ s => Arm.target.abiPreserved σ s ∧ VOut p σ (s.gpr .r0))
      (withCache P p) :=
  (vpro_piece hF (by omega_using [hS])).seq ((body_piece hP hF hS).seq vepi_piece)

theorem withCache_correct {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat}
    (hS : S + 8 ≤ STK) (σ : State) (hp : (verifyK p STK).pre σ) :
    ∃ t s', Exec isa (withCache P p) σ t s' ∧ abiPreserved σ s' ∧ (verifyK p STK).post σ s' := by
  obtain ⟨t, s', e, a, q⟩ := (withCache_piece hP hF hS).ok σ σ hp rfl
  exact ⟨t, s', e, a, q⟩

theorem withCache_ct {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat}
    (hS : S + 8 ≤ STK) : ConstantTime isa (verifyK p STK).pre (verifyK p STK).pub (withCache P p) :=
  relStart (withCache_piece hP hF hS).tr

end VG.Proof.MlDsa.Arm.Verify
