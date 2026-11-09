module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Cmp
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.SampC
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Row
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Kernel
import VerifiedGarbage.Proof.Framework.Offset
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
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv relStart reg)
open VG.Proof.MlDsa.PPC64LE (kSt kSt_gpr kSt_r14 kSt_r15 kSt_sp kSt_rd kSt_wr kSt_mem kernel_wp kernel_tr)
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

theorem compute_piece : CPiece p STK (KX p STK 0 false 0) (KE p STK) (compute P p) := by
  unfold compute
  refine Piece.seq (J := KX p STK p.ℓ false 0) ?_ ((nttC_piece hP hF hS).cache.seq
    (Piece.seq (J := KX p STK p.ℓ true p.k) ?_ ((vhash_piece hF).cache.seq (cmp_piece hF).cache)))
  · refine Piece.mono (Piece.seqR (I := fun j => KX p STK j false 0) p.ℓ 0
      fun j _ hj => (nttZ_piece hP hF hS (by omega)).cache) (fun _ _ _ h => h) fun _ _ _ h => ?_
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
    CPiece p STK (V2 p STK p.ℓ) (VFin p STK) (ifOk (.seq (samples P p) (compute P p))) := by
  refine ifOk_piece (v := fun σ => flag (zOk p σ p.ℓ)) (fun _ _ _ h => h.r24) (fun σ₁ σ₂ _ _ pub => ?_)
    ?_ fun σ s _ h hv => ⟨h.vc, .inr ⟨h.r24.trans hv, ?_⟩⟩
  · have e : sgOf p σ₁ = sgOf p σ₂ := pub.1.2.2.2.2.2.2.2
    dsimp only [zOk]
    rw [e]
  · refine Piece.mono (pieceFrame ((samples_piece hP hF hS).cache.seq (Piece.mono (compute_piece hP hF hS)
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

theorem body_piece : CPiece p STK (fun σ s => VC p STK σ s ∧ s.gpr .r24 = 1) (VFin p STK) (body P p) := by
  have hl := hF.l
  unfold body
  refine (hint_piece hP hF hS).cache.seq (ifOk_piece (v := fun σ => flag (hintOf p σ).isSome) (fun _ _ _ h => h.r24)
    (fun σ₁ σ₂ _ _ pub => ?_) ?_ fun _ _ _ h hv => v1_out h hv)
  · have e : sgOf p σ₁ = sgOf p σ₂ := pub.1.2.2.2.2.2.2.2
    dsimp only [hintOf]
    rw [e]
  · refine Piece.seq (Piece.mono (Piece.seqR (I := fun j => V2 p STK j) p.ℓ 0
      fun j _ hj => (zOne_piece hP hF hS (by omega)).cache) (fun _ _ _ h => v1_v2 h.1 h.2) fun _ _ _ h => ?_)
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
    CPiece p STK (fun σ s => s = σ)
      (fun σ s => PPC64LE.target.abiPreserved σ s ∧ (Spec.MlDsa.verifyContract p PPC64LE.abi STK).post σ s)
      (verify P p) :=
  (vpro_piece hF h48).cache.seq ((body_piece hP hF hS).seq (vepi_piece hF).cache)

/-! ## The kernel -/

/-- The precondition of `verifyWithCacheContract` with `K` bytes of stack. -/
structure KPre (p : Params) (K : Nat) (σ : State) : Prop where
  stk : K ≤ σ.sp.toNat
  rd : σ.rd = [reg (vPk σ) p.pkLen, reg (vMu σ) 64, reg (vSg σ) p.sigLen, reg (σ.gpr .r7) (σ.gpr .r8).toNat]
  wr : σ.wr = [reg (vScr σ) (scrLen p)]
  d_pc : (reg (vPk σ) p.pkLen).Disjoint (reg (vScr σ) (scrLen p))
  d_mc : (reg (vMu σ) 64).Disjoint (reg (vScr σ) (scrLen p))
  d_sc : (reg (vSg σ) p.sigLen).Disjoint (reg (vScr σ) (scrLen p))
  d_cx : (reg (vScr σ) (scrLen p)).Disjoint (reg (σ.gpr .r7) (σ.gpr .r8).toNat)
  b_p : (below σ.sp K).Disjoint (reg (vPk σ) p.pkLen)
  b_m : (below σ.sp K).Disjoint (reg (vMu σ) 64)
  b_s : (below σ.sp K).Disjoint (reg (vSg σ) p.sigLen)
  b_c : (below σ.sp K).Disjoint (reg (vScr σ) (scrLen p))
  b_x : (below σ.sp K).Disjoint (reg (σ.gpr .r7) (σ.gpr .r8).toNat)
  f_p : (vPk σ).toNat + p.pkLen ≤ 2 ^ 64
  f_m : (vMu σ).toNat + 64 ≤ 2 ^ 64
  f_s : (vSg σ).toNat + p.sigLen ≤ 2 ^ 64
  f_c : (vScr σ).toNat + scrLen p ≤ 2 ^ 64
  f_x : (σ.gpr .r7).toNat + (σ.gpr .r8).toNat ≤ 2 ^ 64
  polys : σ.gpr .r8 = 0 ∨ ((σ.gpr .r8).toNat = 4 * Spec.MlDsa.n * p.k ∧
    Proof.MlDsa.CachedPublicPolys p σ.mem (σ.gpr .r7) (pkOf p σ))

theorem kpre_of {p : Params} {k : Nat} {σ : State}
    (h : (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (k + 1)).pre σ) : KPre p (k + 1) σ := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, PPC64LE.abi,
    PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

section
variable {p : Params} {STK : Nat} {σ : State} (h : KPre p (STK + 96) σ)
include h

theorem KPre.fit : STK + 96 < 2 ^ 64 := by have := h.stk; have := σ.sp.isLt; omega

theorem KPre.b96 : Region.Sub (below σ.sp 96) (below σ.sp (STK + 96)) := below_sub (by omega) h.fit

theorem KPre.bSTK : Region.Sub (below (kSt .r7 .r8 σ).sp STK) (below σ.sp (STK + 96)) := by
  rw [kSt_sp]
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have := h.fit; have := h.stk
  bv_omega

/-- Bytes apart from the stack are as on entry, in the state verification starts in. -/
theorem KPre.bytes {a : Addr} {l : Nat} (hd : (below σ.sp (STK + 96)).Disjoint (reg a l)) (hl : l ≤ 2 ^ 64) :
    bytesAt (kSt .r7 .r8 σ).mem a l = bytesAt σ.mem a l :=
  Proof.MlKem.bytesAt_frame (kSt_mem σ) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact (hd.sub_left h.b96).symm) hl

theorem kSt_inputs : pkOf p (kSt .r7 .r8 σ) = pkOf p σ ∧ muOf (kSt .r7 .r8 σ) = muOf σ ∧
    sgOf p (kSt .r7 .r8 σ) = sgOf p σ := by
  simp only [pkOf, muOf, sgOf, vPk, vMu, vSg, kSt_gpr σ (show Reg.r3 ≠ .r14 by decide) (by decide),
    kSt_gpr σ (show Reg.r4 ≠ .r14 by decide) (by decide), kSt_gpr σ (show Reg.r5 ≠ .r14 by decide) (by decide)]
  exact ⟨h.bytes h.b_p (by have := h.f_p; omega), h.bytes h.b_m (by decide), h.bytes h.b_s (by have := h.f_s; omega)⟩

/-- The state verification starts in satisfies `CPre`. -/
theorem kSt_cpre : CPre p STK (kSt .r7 .r8 σ) := by
  have e3 := kSt_gpr (a := .r7) (b := .r8) σ (r := .r3) (by decide) (by decide)
  have e4 := kSt_gpr (a := .r7) (b := .r8) σ (r := .r4) (by decide) (by decide)
  have e5 := kSt_gpr (a := .r7) (b := .r8) σ (r := .r5) (by decide) (by decide)
  have e6 := kSt_gpr (a := .r7) (b := .r8) σ (r := .r6) (by decide) (by decide)
  have e14 : (kSt .r7 .r8 σ).gpr .r14 = σ.gpr .r7 := kSt_r14 σ
  have e15 : (kSt .r7 .r8 σ).gpr .r15 = σ.gpr .r8 := kSt_r15 σ
  have bs := h.bSTK
  have hstk : STK ≤ (kSt .r7 .r8 σ).sp.toNat := by
    rw [kSt_sp]; have := h.stk; have := h.fit; bv_omega
  refine ⟨⟨hstk, ⟨[reg (σ.gpr .r7) (σ.gpr .r8).toNat], ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_⟩ <;>
    simp only [vPk, vMu, vSg, vScr, e3, e4, e5, e6, e14, e15, kSt_rd, kSt_wr]
  · rw [h.rd]; rfl
  · exact h.wr
  · exact h.d_pc
  · exact h.d_mc
  · exact h.d_sc
  · exact h.b_p.sub_left bs
  · exact h.b_m.sub_left bs
  · exact h.b_s.sub_left bs
  · exact h.b_c.sub_left bs
  · exact h.f_p
  · exact h.f_m
  · exact h.f_s
  · exact h.f_c
  · rcases h.polys with h0 | ⟨hl, hc⟩
    · exact .inl h0
    · refine .inr ⟨hl, fun i hi => ?_⟩
      rw [kSt_inputs h |>.1]
      have hsub : Region.Sub (Proof.MlDsa.Verify.polyRegion (σ.gpr .r7 + BitVec.ofNat 64 (4 * Spec.MlDsa.n * i)))
          (reg (σ.gpr .r7) (σ.gpr .r8).toNat) :=
        Offset.sub_base _ (by rw [hl]; show 4 * 256 * i + 1024 ≤ 4 * 256 * p.k; omega)
      exact Proof.MlDsa.Verify.polyIs_frame (kSt_mem σ) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact (h.b_x.sub_left h.b96).symm.sub_left hsub) (hc i hi)
  · rw [h.rd]; simp
  · exact h.d_cx.symm
  · exact h.b_x.symm.sub_right bs

end

/-- The public data of two kernels' entry states give `cPub` of the states
verification starts in. -/
theorem kSt_cpub {p : Params} {STK : Nat} {σ₁ σ₂ : State} (h₁ : KPre p (STK + 96) σ₁) (h₂ : KPre p (STK + 96) σ₂)
    (hpub : (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (STK + 96)).pub σ₁ σ₂) :
    cPub p (kSt .r7 .r8 σ₁) (kSt .r7 .r8 σ₂) := by
  sig_pub [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, PPC64LE.abi,
    PPC64LE.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8⟩ := hpub
  obtain ⟨e12, e3⟩ := List.append_inj (Proof.MlDsa.KeyGen.leakBytes_inj hl)
    (by simp only [List.length_append, Proof.MlKem.bytesAt_length])
  obtain ⟨e1, e2⟩ := List.append_inj e12 (by simp only [Proof.MlKem.bytesAt_length])
  have g : ∀ {r : Reg}, r ≠ .r14 → r ≠ .r15 → σ₁.gpr r = σ₂.gpr r →
      (kSt .r7 .r8 σ₁).gpr r = (kSt .r7 .r8 σ₂).gpr r := fun a b e => by
    rw [kSt_gpr σ₁ a b, kSt_gpr σ₂ a b, e]
  obtain ⟨k₁, m₁, r₁⟩ := kSt_inputs h₁
  obtain ⟨k₂, m₂, r₂⟩ := kSt_inputs h₂
  refine ⟨⟨by rw [kSt_sp, kSt_sp, hsp], g (by decide) (by decide) h3, g (by decide) (by decide) h4,
    g (by decide) (by decide) h5, g (by decide) (by decide) h6, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [k₁, k₂]; exact e1
  · rw [m₁, m₂]; exact e2
  · rw [r₁, r₂]; exact e3
  · rw [kSt_r14, kSt_r14, h7]
  · rw [kSt_r15, kSt_r15, h8]

/-- A state that satisfies `verifyWithCacheContract`'s precondition, for the
contract's satisfiability: an empty cache. -/
def kSat (p : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x10000 | .r7 => 0x1000 | _ => 0
  lr := 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x2000, 64⟩, ⟨0x3000, p.sigLen⟩, ⟨0x1000, 0⟩]
  wr := [⟨0x10000, scrLen p⟩]

/-- `vg_mldsa*_verify_with_cache` of the parameter set `p` meets its
contract with `S + 96` bytes of stack (the 96 of its frames), for any
verified implementations `P` of the primitives it calls with at most `S`
bytes of stack, `S` at least the 48 bytes the sponge needs, and
verification's frames within `S` bytes. -/
theorem withCache_verified {P : Prims} {S : Nat} (hP : VPrimsOk P S) (h48 : 48 ≤ S)
    (p : Spec.MlDsa.Params) (hp3 : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hd : sdepth (verify P p) ≤ S)
    (hsat : (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (S + 96)).pre (kSat p)) :
    Verified PPC64LE.target (withCache P p) (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (S + 96)) := by
  have hF := vfacts hp3
  have hv := verify_piece hP hF (Nat.le_refl S) h48
  have body (σ : State) (hk : KPre p (S + 96) σ) := hv.ok _ _ (kSt_cpre hk) rfl
  have hd96 (σ : State) (hk : KPre p (S + 96) σ) : ∀ X ∈ σ.wr, (below σ.sp 96).Disjoint X := fun X hX => by
    rw [hk.wr] at hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl
    exact hk.b_c.sub_left hk.b96
  have hn (σ : State) (hk : KPre p (S + 96) σ) : sdepth (verify P p) + 96 < 2 ^ 64 := by have := hk.fit; omega
  refine ⟨fun σ hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨kSat p, hsat⟩⟩
  · have hk := kpre_of (k := S + 95) hs
    refine WP.mono (kernel_wp (a := .r7) (b := .r8) (by decide) (by decide) (by decide)
      (by have := hk.stk; omega) (hd96 σ hk) (hn σ hk)
      (R := fun _ r => (r.setWidth 32 = 1 ∧ ∃ b, vv p σ b = some true) ∨
        (r.setWidth 32 = 0 ∧ vv p σ Spec.MlDsa.minBounds ≠ some true))
      (WP.mono (body σ hk) fun s' ⟨ha, hq⟩ => ⟨ha, ?_⟩)) fun s' ⟨ha, hq⟩ => ⟨ha, ?_⟩
    · generalize hτ : kSt .r7 .r8 σ = τ at hq
      sig_post [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, PPC64LE.abi, PPC64LE.argRegs] at hq
      subst hτ
      obtain ⟨k₁, m₁, r₁⟩ := kSt_inputs hk
      simp only [pkOf, muOf, sgOf, vPk, vMu, vSg, kSt_gpr σ (show Reg.r3 ≠ .r14 by decide) (by decide),
        kSt_gpr σ (show Reg.r4 ≠ .r14 by decide) (by decide), kSt_gpr σ (show Reg.r5 ≠ .r14 by decide) (by decide)]
        at k₁ m₁ r₁
      rw [kSt_gpr σ (show Reg.r3 ≠ .r14 by decide) (by decide), kSt_gpr σ (show Reg.r4 ≠ .r14 by decide) (by decide),
        kSt_gpr σ (show Reg.r5 ≠ .r14 by decide) (by decide)] at hq
      rw [k₁, m₁, r₁] at hq
      exact hq
    · sig_post [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig,
        PPC64LE.abi, PPC64LE.argRegs]
      exact hq
  · have k₁ := kpre_of (k := S + 95) h₁
    have k₂ := kpre_of (k := S + 95) h₂
    refine (kernel_tr (a := .r7) (b := .r8) (by decide) (by decide) (by decide)
      (P := fun x y => KPre p (S + 96) x ∧ KPre p (S + 96) y ∧
        (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (S + 96)).pub x y)
      (fun x y ⟨_, _, hp⟩ => by
        sig_pub [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig,
          PPC64LE.abi, PPC64LE.argRegs] at hp
        exact hp.1)
      (fun x y ⟨a, b, _⟩ => ⟨by have := a.stk; omega, by have := b.stk; omega, hd96 x a, hd96 y b⟩) (hn s₁ k₁)
      (fun x y ⟨a, b, _⟩ => ⟨⟨_, body x a⟩, ⟨_, body y b⟩⟩)
      (RelCT.mono hv.tr (fun u v ⟨x, y, ⟨a, b, hp⟩, eu, ev⟩ => by
        subst eu ev; exact ⟨_, _, kSt_cpre a, kSt_cpre b, kSt_cpub a b hp, rfl, rfl⟩) fun _ _ h => h)
      s₁ s₂ t₁ t₂ s₁' s₂' ⟨k₁, k₂, hpub⟩ e₁ e₂).1

end VG.Proof.MlDsa.PPC64LE.Verify
