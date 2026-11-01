module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Cmp
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.SampC
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Row
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Cmp
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Final

/-!
# ML-DSA verification on PPC64LE: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

As on 32-bit ARM (`Proof/MlDsa/Arm/Verify/Top.lean`): the function, piece
by piece, for any parameter set of Table 1 and any verified implementations
of the primitives (`verify_piece`, `verify_verified`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Verify

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv relStart)
open VG.Impl.MlKem.PPC64LE (topEnd)
open VG.Impl.MlDsa.PPC64LE.Verify
open VG.Impl.MlDsa.PPC64LE.KeyGen (seqR)
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

/-! ## After the samplers -/

theorem vs4_kx {p : Params} {STK : Nat} {σ s : State} (h : VS4 p STK σ s) : KX p STK 0 false 0 σ s := by
  obtain ⟨hh, e, hi⟩ := h.vb.hint
  exact ⟨fun r c => polyAt s.mem (aA p STK σ r c), polyAt s.mem ((vlay p STK σ).A 0 (oP 15)), hh, s.gpr .r24,
    h.vb.vc, e, hi, fun r hr c hc => ⟨h.red r hr c hc, rfl⟩,
    fun i hi => by rw [ifn (Nat.not_lt_zero i)]; exact h.vb.z i hi, ⟨h.redC, rfl⟩,
    fun _ h => absurd h (Nat.not_lt_zero _), rfl, h.ok⟩

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

theorem compute_piece : VPiece p STK (KX p STK 0 false 0) (KE p STK) (compute P p) := by
  unfold compute
  refine Piece.seq (J := KX p STK p.ℓ false 0) ?_ ((nttC_piece hP hF hS).seq
    (Piece.seq (J := KX p STK p.ℓ true p.k) ?_ ((vhash_piece hF).seq (cmp_piece hF))))
  · refine Piece.mono (Piece.seqR (I := fun j => KX p STK j false 0) p.ℓ 0
      fun j _ hj => nttZ_piece hP hF hS (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun r => KX p STK p.ℓ true r) p.k 0
      fun r _ hr => row_piece hP hF hS (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

end

/-! ## The result -/

/-- `verifyMu` of the inputs of a run from `σ`, with the bounds `b`. -/
abbrev vv (p : Params) (σ : State) (b : Bounds) : Option Bool := verifyMu p b (pkOf p σ) (muOf σ) (sgOf p σ)

/-- What the result `r` says of `verifyMu`, as `verifyContract` does. -/
abbrev VOut (p : Params) (σ : State) (r : BitVec 64) : Prop :=
  (r = 1 ∧ ∃ b, vv p σ b = some true) ∨ (r = 0 ∧ vv p σ minBounds ≠ some true)

/-- At the end, before the epilogue: the result in `r24`. -/
abbrev VFin (p : Params) (STK : Nat) (σ s : State) : Prop := VC p STK σ s ∧ VOut p σ (s.gpr .r24)

theorem false_ne {p : Params} {σ : State} {b : Bounds} (h : vv p σ b = some false) : vv p σ minBounds ≠ some true :=
  fun hm => by
    have e₁ := verifyMu_mono (bmax_left b minBounds).rejNTT (bmax_left b minBounds).ball h
    have e₂ := verifyMu_mono (bmax_right b minBounds).rejNTT (bmax_right b minBounds).ball hm
    rw [e₁] at e₂
    cases e₂

theorem ke_out {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (h : KE p STK σ s)
    (hz : zOk p σ p.ℓ = true) : VFin p STK σ s := by
  obtain ⟨A', cc, hh, R, vc, e, hl, ⟨q, hR, hok, hbad⟩, r24⟩ := h
  refine ⟨vc, ?_⟩
  rw [r24, hR, flag_and]
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

theorem flag_eq {b : Bool} (h : flag b = 0) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

/-! ## The body -/

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

/-- The samplers and the rest, once `z` is small enough. -/
theorem inner_piece :
    VPiece p STK (V2 p STK p.ℓ) (VFin p STK) (ifOk (.seq (samples P p) (compute P p))) := by
  refine ifOk_piece (v := fun σ => flag (zOk p σ p.ℓ)) (fun _ _ _ h => h.r24) (fun σ₁ σ₂ _ _ pub => ?_)
    ?_ fun σ s _ h hv => ⟨h.vc, .inr ⟨h.r24.trans hv, ?_⟩⟩
  · have e : sgOf p σ₁ = sgOf p σ₂ := pub.2.2.2.2.2.2.2
    dsimp only [zOk]
    rw [e]
  · refine Piece.mono (pieceFrame ((samples_piece hP hF hS).seq (Piece.mono (compute_piece hP hF hS)
      (fun _ _ _ h => vs4_kx h) fun _ _ _ h => h)) fun σ => zOk p σ p.ℓ = true)
      (fun _ _ _ h => ⟨h, flag_ne.mp h.2⟩) fun _ _ _ ⟨h, hz⟩ => ke_out hF h hz
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
    rw [h.r24, e, show zOk p σ 0 = true from decide_eq_true fun _ h => absurd h (Nat.not_lt_zero _)]
    rfl

omit hP hF hS in
theorem v1_out {σ s : State} (h : V1 p STK σ s) (hv : flag (hintOf p σ).isSome = 0) : VFin p STK σ s := by
  refine ⟨h.vc, .inr ⟨h.r24.trans hv, ?_⟩⟩
  have e : hintOf p σ = none := Option.not_isSome_iff_eq_none.mp (by rw [flag_eq hv]; nofun)
  show verifyMu p minBounds _ _ _ ≠ some true
  rw [verifyMu_hint_none minBounds _ _ e]
  nofun

theorem body_piece : VPiece p STK (fun σ s => VC p STK σ s ∧ s.gpr .r24 = 1) (VFin p STK) (body P p) := by
  have hl := hF.l
  unfold body
  refine (hint_piece hP hF hS).seq (ifOk_piece (v := fun σ => flag (hintOf p σ).isSome) (fun _ _ _ h => h.r24)
    (fun σ₁ σ₂ _ _ pub => ?_) ?_ fun _ _ _ h hv => v1_out h hv)
  · have e : sgOf p σ₁ = sgOf p σ₂ := pub.2.2.2.2.2.2.2
    dsimp only [hintOf]
    rw [e]
  · refine Piece.seq (Piece.mono (Piece.seqR (I := fun j => V2 p STK j) p.ℓ 0
      fun j _ hj => zOne_piece hP hF hS (by omega)) (fun _ _ _ h => v1_v2 h.1 h.2) fun _ _ _ h => ?_)
      (inner_piece hP hF hS)
    rwa [Nat.zero_add] at h

end

/-! ## The return -/

theorem vepi_ok {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (h : VFin p STK σ s) :
    WP isa (.block topEnd) s fun s' =>
      PPC64LE.target.abiPreserved σ s' ∧ (Spec.MlDsa.verifyContract p PPC64LE.abi STK).post σ s' := by
  obtain ⟨vc, hr⟩ := h
  have hs := vc.site
  have hscr := hF.scr
  have hk := hF.k
  have hin : ∀ o, 840 ≤ o → o + 8 ≤ 912 → InRegions (s.rd ++ s.wr) (vScr σ + BitVec.ofNat 64 o) 8 :=
    fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := vlay p STK σ) (o := o) (l := 8) (hs.cw 0 (by decide) (by decide))
      (by rw [vlay_size0]; omega) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
  refine WP.mono (topEnd_ok hs.r31 vc.sav hin vc.pres)
    fun s' ⟨pr, lr, r3, _, sp', _, _⟩ => ⟨⟨pr, sp'.trans vc.sp, lr⟩, ?_⟩
  sig_post [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, PPC64LE.abi, PPC64LE.argRegs]
  rw [r3]
  rcases hr with ⟨e, h⟩ | ⟨e, h⟩ <;> rw [e]
  · exact .inl ⟨rfl, h⟩
  · exact .inr ⟨rfl, h⟩

theorem vepi_piece {p : Params} (hF : VFacts p) {STK : Nat} :
    VPiece p STK (VFin p STK)
      (fun σ s => PPC64LE.target.abiPreserved σ s ∧ (Spec.MlDsa.verifyContract p PPC64LE.abi STK).post σ s)
      (.block topEnd) :=
  ⟨fun _ _ _ h => vepi_ok hF h, vrel31 (fun _ _ h => h.1) (by taint_decide)⟩

/-! ## The function -/

theorem verify_piece {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat}
    (hS : S ≤ STK) (h48 : 48 ≤ STK) :
    VPiece p STK (fun σ s => s = σ)
      (fun σ s => PPC64LE.target.abiPreserved σ s ∧ (Spec.MlDsa.verifyContract p PPC64LE.abi STK).post σ s)
      (verify P p) :=
  (vpro_piece hF h48).seq ((body_piece hP hF hS).seq (vepi_piece hF))

/-- A state satisfying `verifyContract`'s precondition. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x10000 | _ => 0
  lr := 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x2000, 64⟩, ⟨0x3000, p.sigLen⟩]
  wr := [⟨0x10000, scrLen p⟩]

/-- `vg_mldsa*_verify` of the parameter set `p` meets its contract with `S`
bytes of stack, for any verified implementations `P` of the primitives it
calls with at most `S` bytes of stack, and `S` at least the 48 bytes the
sponge needs. The contract's satisfiability (`hsat`, by `verifySat`) is
evaluated once `S` is known. -/
theorem verify_verified {P : Prims} {S : Nat} (hP : VPrimsOk P S) (h48 : 48 ≤ S) (p : Spec.MlDsa.Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hsat : (Spec.MlDsa.verifyContract p PPC64LE.abi S).pre (verifySat p)) :
    Verified PPC64LE.target (verify P p) (Spec.MlDsa.verifyContract p PPC64LE.abi S) := by
  have hF := vfacts hp
  have hk := verify_piece hP hF (Nat.le_refl _) h48
  obtain ⟨n, rfl⟩ : ∃ n, S = n + 1 := ⟨S - 1, by omega⟩
  refine ⟨fun s hs => hk.ok s s (vpre_of hs) rfl, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_,
    ⟨verifySat p, hsat⟩⟩
  sig_pub [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, PPC64LE.abi, PPC64LE.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6⟩ := hpub
  obtain ⟨e12, e3⟩ := List.append_inj (Proof.MlDsa.KeyGen.leakBytes_inj hl)
    (by simp only [List.length_append, Proof.MlKem.bytesAt_length])
  obtain ⟨e1, e2⟩ := List.append_inj e12 (by simp only [Proof.MlKem.bytesAt_length])
  exact relStart hk.tr s₁ s₂ t₁ t₂ s₁' s₂' (vpre_of h₁) (vpre_of h₂) ⟨hsp, h3, h4, h5, h6, e1, e2, e3⟩ e₁ e₂

end VG.Proof.MlDsa.PPC64LE.Verify
