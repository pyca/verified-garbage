module

import VerifiedGarbage.Proof.MlKem.RISCV64.CmpSel
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.SampA
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.SampA
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Compute
import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Samp
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Site
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Compute
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Samp
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Site

/-! ### `MlDsa.RISCV64.Verify.Hash`, which only this module used -/

section

/-!
# ML-DSA verification on RISC-V: `c̃′`

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/Cmp.lean`):
`c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)` to `3072` (`vhash_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv hashLay hashLay_ptr
  hashS hashS_tr pieceS ix_ne1 shake31)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Impl.MlKem.RISCV64 (hash)
open VG.Spec.MlDsa (Params toRq ntt simpleBitPack)
open VG.Proof.MlDsa (HintIs PolyIs polyAt Reduced)
open VG.Proof.MlDsa.Verify (vZ zHat w1Row)
open VG.Spec.Sha3 (bytesAt)

/-- The buffers of the sponge: `mu` and `scratch`. -/
abbrev Kmu : Nat → Bool := fun i => i == 3

theorem kmu : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → Kmu i = true → Kmu j = true → i ∈ vWb ∨ j ∈ vWb :=
  fun i _ j _ hij _ _ hi hj => by
    simp only [Kmu, beq_iff_eq] at hi hj; omega

/-- `w1Encode(w′₁)` of rows `A'`, `cc` and `h`. -/
abbrev w1Enc (p : Params) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly)
    (h : List (Vector Bool Spec.MlDsa.n)) : List Byte :=
  (List.range p.k).flatMap fun r => simpleBitPack (w1Row p (pkOf p σ) (sgOf p σ) A' (ntt cc) h r) (w1Max p)

theorem flatMap_congr_mem' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem' fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- After the hash. -/
abbrev KF (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, KC5 p STK σ A' cc h R p.ℓ true p.k s ∧
    bytesAt s.mem ((vlay p STK σ).A 0 oCT) p.ctildeLen = Spec.MlDsa.H (muOf σ ++ w1Enc p σ A' cc h) p.ctildeLen

theorem vhPieces {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (hs : Site (vlay p STK σ) vWb STK s) :
    (∀ pc ∈ ([⟨.s9, 0, 64⟩, ⟨.s11, oB, p.k * w1Len p⟩] : List Impl.MlKem.RISCV64.Piece),
      PieceOk (hashLay (vlay p STK σ) s Kmu) ix s false pc) ∧
    PieceOk (hashLay (vlay p STK σ) s Kmu) ix s true (⟨.s11, oCT, p.ctildeLen⟩ : Impl.MlKem.RISCV64.Piece) := by
  have hk := hF.k
  obtain ⟨w1a, w1b⟩ := hF.w1
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (show oCT < 32768 by decide)
    (show p.ctildeLen < 2048 by rcases hF.ct with e | e | e <;> omega_using [e])
    (show 0 < p.ctildeLen by rcases hF.ct with e | e | e <;> omega_using [e])
    (by rcases hF.ct with e | e | e <;> vsep hF [hashLay, Lay.size, e]) (.inl rfl)
    fun _ => show ix Reg.s11 ∈ vWb by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl
  · exact pieceS hs rfl (show (0 : Nat) < 32768 by decide) (show 64 < 2048 by decide) (by decide)
      (by vsep hF [hashLay, Lay.size]) (.inr rfl) fun h => absurd h (by decide)
  · exact pieceS hs rfl (show oB < 32768 by decide) (show p.k * w1Len p < 2048 by omega_using [w1a]) w1b
      (by rcases hF.w1l with e | ⟨e, _⟩ <;> vsep hF [hashLay, Lay.size, e]) (.inl rfl) fun h => absurd h (by decide)

theorem B_bytes {p : Params} {STK : Nat} {σ : State} {A' cc h R nz nc} {s : State}
    (hk5 : KC5 p STK σ A' cc h R nz nc p.k s) :
    bytesAt s.mem ((vlay p STK σ).A 0 oB) (p.k * w1Len p) = w1Enc p σ A' cc h := by
  rw [Nat.mul_comm, Lay.A, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ oB (w1Len p) p.k]
  exact flatMap_congr_mem' fun r hr => hk5.rows r (List.mem_range.mp hr)

theorem vhash_ok {p : Params} (hF : VFacts p) {STK : Nat} {σ : State} {A' cc h R} {s : State}
    (hk5 : KC5 p STK σ A' cc h R p.ℓ true p.k s) :
    WP isa (hash 136 0x1f [⟨.s9, 0, 64⟩, ⟨.s11, oB, p.k * w1Len p⟩] [⟨.s11, oCT, p.ctildeLen⟩]) s
      (KF p STK σ) := by
  have hk := hF.k
  have hs := hk5.vc.site
  obtain ⟨hin, hq⟩ := vhPieces hF hs
  refine WP.mono (hashS hs kmu (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by simp) hin hq)
    fun s' ⟨k', o'⟩ => ⟨A', cc, h, R, hk5.keep hF k' ?_, ?_⟩
  · have : p.ctildeLen ≤ 64 := by rcases hF.ct with e | e | e <;> omega_using [e]
    k5chks hF (Nat.le_refl _)
  · have o₃ : bytesAt s'.mem ((vlay p STK σ).A 0 oCT) p.ctildeLen = _ := o'
    rw [o₃]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
      hashLay_ptr _ _ _ (ix_ne1 _)]
    have e1 : bytesAt s.mem ((vlay p STK σ).ptr (ix Reg.s9) + BitVec.ofNat 64 0) 64 = muOf σ :=
      hk5.vc.mu
    have e2 : bytesAt s.mem ((vlay p STK σ).ptr (ix Reg.s11) + BitVec.ofNat 64 oB) (p.k * w1Len p) =
        w1Enc p σ A' cc h := B_bytes hk5
    rw [e1, e2, shake31]
    exact (Proof.MlKem.shake256_eq _ _).symm

theorem vhash_piece {p : Params} (hF : VFacts p) {STK : Nat} :
    VPiece p STK (KX p STK p.ℓ true p.k) (KF p STK)
      (hash 136 0x1f [⟨.s9, 0, 64⟩, ⟨.s11, oB, p.k * w1Len p⟩] [⟨.s11, oCT, p.ctildeLen⟩]) :=
  ⟨fun _ _ _ ⟨_, _, _, _, h⟩ => vhash_ok hF h,
    rel_of (RelCT.exists_ fun σ => hashS_tr kmu (rate := 136) (sfx := 0x1f) (by decide) (by decide)
      (by simp) (fun s hs => (vhPieces hF (σ := σ) hs).1) (fun s hs => (vhPieces hF hs).2) fun _ _ h => h)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩⟩

end VG.Proof.MlDsa.RISCV64.Verify

end

end

/-! ### `MlDsa.RISCV64.Verify.SampC`, which the modules that import this one used -/

section

/-!
# ML-DSA verification on RISC-V: `c`, and the samplers

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/Top.lean`): `c = SampleInBall(c̃)`
to polynomial 15, its result ANDed into `s4` and `c` masked with it
(`ball_piece`); and every sampler, after the checks of the signature
(`samples_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee BallOk
  ball_tr polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD andMask_ok masked_poly taint31)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Impl.MlDsa.RISCV64.KeyGen (and24 mask setB seqR sampled)
open VG.Impl.MlKem.RISCV64 (copy)
open VG.Spec.MlDsa (Params toRq normRq rejNTTPoly minBounds Outcome sampleInBall)
open VG.Proof.MlDsa (HintIs PolyIs polyAt Reduced)
open VG.Proof.MlDsa.Verify (vZ vRho aSeed vCt)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers. -/
structure VS4 (p : Params) (STK : Nat) (σ s : State) : Prop where
  vb : VB p STK σ s
  red : ∀ r < p.k, ∀ s' < p.ℓ, Reduced s.mem (aA p STK σ r s')
  redC : Reduced s.mem ((vlay p STK σ).A 0 (oP 15))
  ok : ∃ q : Bool, s.gpr .s4 = flag q ∧
    (q = true → (∀ r < p.k, ∀ s' < p.ℓ,
      ∃ b : Nat, rejNTTPoly b (aSeed (pkOf p σ) r s') = some (polyAt s.mem (aA p STK σ r s'))) ∧
      ∃ b : Nat, (sampleInBall p.τ b (vCt p (sgOf p σ))).map toRq = some (polyAt s.mem ((vlay p STK σ).A 0 (oP 15)))) ∧
    (q = false → (∃ r < p.k, ∃ s' < p.ℓ, rejNTTPoly minBounds.rejNTT (aSeed (pkOf p σ) r s') = none) ∨
      sampleInBall p.τ minBounds.ball (vCt p (sgOf p σ)) = none)

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem ball_m {σ : State} :
    BallOk (vlay p STK σ) vWb (.s8, 0) p.ctildeLen p.τ pC (sc oSS) := by
  have hk := hF.k
  exact ⟨⟨vptr_ok rfl (by decide), by vsep hF⟩, ⟨vptr_ok rfl (by decide), by vsep hF⟩,
    ⟨vptr_ok rfl (by decide), by vsep hF⟩, show ix Reg.s11 ∈ vWb by decide,
    show ix Reg.s11 ∈ vWb by decide, by vsep hF, by vsep hF, by vsep hF, hF.ball.1,
    ⟨by rcases hF.ct with e | e | e <;> omega_using [e], by rcases hF.ct with e | e | e <;> omega_using [e], hF.ball.2⟩, by valsep, by valsep⟩

theorem vball_ok {σ s : State} (h : VS p STK p.k 0 σ s) :
    WP isa (sampled (ballAt P (.s8, 0) p.ctildeLen p.τ pC) pC) s (VS4 p STK σ) := by
  have hk := hF.k; have hl := hF.l
  have hs := h.vb.vc.site
  have hL := hs.ok
  unfold sampled ballAt
  refine WP.seq (KeyGen.ball_ok hP.ball hs hS (ball_m hF) fun s₃ k₃ hred hout => ?_)
  have eb : bytesAt s.mem (lpa (vlay p STK σ) (.s8, 0)) p.ctildeLen = vCt p (sgOf p σ) := by
    have := sig_slice h.vb.vc (o := 0) (l := p.ctildeLen) (by have := hF.sig; have := hF.hint; omega_arith)
    rw [List.drop_zero] at this
    exact this
  rw [eb] at hout
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  have kv₃ := h.vb.keep hF k₃ (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  have kA3 : ∀ r < p.k, ∀ s' < p.ℓ, polyAt s₃.mem (aA p STK σ r s') = polyAt s.mem (aA p STK σ r s') ∧
      (Reduced s.mem (aA p STK σ r s') → Reduced s₃.mem (aA p STK σ r s')) := fun r hr s' hs' =>
    ⟨polyAt_keepW hL k₃.frame (by vsep hF) (by decide) rfl, reduced_keepW hL k₃.frame (by vsep hF) (by decide) rfl⟩
  have h24₃ : s₃.gpr .s4 = s.gpr .s4 := k₃.cs .s4 (by decide)
  refine WP.mono (andMask_ok kv₃.vc.site (a := pC) ⟨vptr_ok rfl (by decide), by vsep hF⟩
    (by valsep) (show ix Reg.s11 ∈ vWb by decide) hr01) fun s₄ ⟨s₅, r₅, k₄, r₄, co⟩ => ?_
  obtain ⟨pi, p1, _⟩ := masked_poly hred co
  have kv₄ := (kv₃.regs2 r₅).keep hF k₄ (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  have kA4 : ∀ r < p.k, ∀ s' < p.ℓ, polyAt s₄.mem (aA p STK σ r s') = polyAt s₃.mem (aA p STK σ r s') ∧
      (Reduced s₃.mem (aA p STK σ r s') → Reduced s₄.mem (aA p STK σ r s')) := fun r hr s' hs' => by
    rw [← r₅.mem]
    exact ⟨polyAt_keepW hL k₄.frame (by vsep hF) (by decide) rfl, reduced_keepW hL k₄.frame (by vsep hF) (by decide) rfl⟩
  have dn : ∀ r s', s' < p.ℓ → (Dn p.k 0 r s' ↔ r < p.k) := fun r s' _ => by simp only [Dn]; omega_using []
  obtain ⟨q, hq, hok, hbad⟩ := h.ok
  refine ⟨kv₄, fun r hr s' hs' => (kA4 r hr s' hs').2 ((kA3 r hr s' hs').2 (h.red r s' hs' ((dn r s' hs').mpr hr))),
    pi.1, ⟨q && decide ((s₃.gpr .a0).setWidth 32 = 1), ?_, fun hq' => ⟨fun r hr s' hs' => ?_, ?_⟩, fun hq' => ?_⟩⟩
  · rw [r₄, h24₃, hq, flag_and01 q hr01]
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
theorem ballTail_taint : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) (.seq (.block and24) (mask (pS 15)))
    (VG.Taint.hintOf VG.RISCV64.taint (Taint.ofRegs [.s11]) (.seq (.block and24) (mask (sc 0))))).isSome = true :=
  vAndMask_taint 15 (by decide)

theorem ball_piece :
    VPiece p STK (VS p STK p.k 0) (VS4 p STK) (sampled (ballAt P (.s8, 0) p.ctildeLen p.τ pC) pC) := by
  have hk := hF.k
  refine ⟨fun _ _ _ h => vball_ok hP hF hS h, ?_⟩
  unfold sampled ballAt
  refine RelCT.seq (R := VTwo p STK) ?_ (vtaint31 ballTail_taint)
  refine RelCT.mono (M := isa) (P := fun (x y : State) => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    bytesAt x.mem (lpa (vlay p STK σ) (.s8, 0)) p.ctildeLen = bytesAt y.mem (lpa (vlay p STK σ) (.s8, 0)) p.ctildeLen)
    (RelCT.exists_ fun σ => ?_) (fun _ _ ⟨σ₁, _, _, _, pub, h₁, h₂⟩ => ?_) fun _ _ h => h
  · have ok := fun x (hs : Site (vlay p STK σ) vWb STK x) => KeyGen.ball_ok hP.ball hs hS
      (name := "vg_mldsa_sample_in_ball") (ball_m hF (σ := σ)) (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
    exact (VG.Proof.MlDsa.RISCV64.KeyGen.RelCT.two (fun _ _ h => h.1)
      (ball_tr hP.ball hS (ball_m hF) fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
      fun x hs => ok x hs).mono (fun _ _ h => h) fun x y h => ⟨σ, h⟩
  · refine ⟨σ₁, vc_twoL pub h₁.vb.vc h₂.vb.vc, ?_⟩
    show bytesAt _ ((vlay p STK σ₁).A 4 0) _ = bytesAt _ ((vlay p STK σ₁).A 4 0) _
    rw [sig_slice h₁.vb.vc (by have := hF.sig; have := hF.hint; omega_arith), pub.2.2.2.2.2.2.2.1, vlay_pub pub,
      sig_slice h₂.vb.vc (by have := hF.sig; have := hF.hint; omega_arith)]

/-! ## The samplers -/

omit hP hS in
theorem rho_piece :
    VPiece p STK (fun σ s => V2 p STK p.ℓ σ s ∧ flag (zOk p σ p.ℓ) ≠ 0) (VS p STK 0 0) (copy .s10 0 .s11 oSB 32) := by
  refine ⟨fun σ s _ ⟨h, hn⟩ => ?_, rel_of (vtaint4 (by taint_decide)) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
    ⟨σ₁, vc_twoL pub h₁.1.vc h₂.1.vc⟩⟩
  have hz : zOk p σ p.ℓ = true := flag_ne.mp hn
  exact rho_ok hF ⟨h.vc, h.hint, h.z, hz⟩ (by rw [h.s4, hz]; rfl)

theorem samples_piece :
    VPiece p STK (fun σ s => V2 p STK p.ℓ σ s ∧ flag (zOk p σ p.ℓ) ≠ 0) (VS4 p STK) (samples P p) :=
  (rho_piece hF).seq ((rows_piece hP hF hS).seq (ball_piece hP hF hS))

end

end VG.Proof.MlDsa.RISCV64.Verify

end

end

/-!
# ML-DSA verification on RISC-V: `c̃′ = c̃`

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/Cmp.lean`): `r24 ← 0` unless
`c̃′ = c̃`, without a branch (`cmp_piece`), by ML-KEM's loop comparing two
buffers (`Proof/MlKem/RISCV64/CmpSel.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv argOk arg_ok
  argOk_ne baseReg_of base_pres)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Impl.MlDsa.RISCV64.KeyGen (Ptr Arg)
open VG.Impl.MlKem.RISCV64 (cmpBody)
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-! ## A state that differs but in registers other than the layout's -/

theorem siteCongr {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s)
    (hr : ∀ r ∈ [Reg.s8, .s9, .s10, .s11], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Site L Wb STK s' :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, by rw [hsp]; exact h.p1, h.s1168, by rw [hsp]; exact h.spk,
    by rw [hsp]; exact h.al, h.al0,
    by rw [hr _ (by decide)]; exact h.s11, by rw [hr _ (by decide)]; exact h.s10,
    by rw [hr _ (by decide)]; exact h.s9, by rw [hr _ (by decide)]; exact h.s8,
    by rw [hwr]; exact h.cw, by rw [hrd, hwr]; exact h.cr⟩

theorem VC.congr {p : Params} {STK : Nat} {σ s s' : State} (h : VC p STK σ s)
    (hr : ∀ r ∈ preserved, r ≠ .s4 → r ≠ .s6 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VC p STK σ s' :=
  ⟨siteCongr h.site (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl <;> exact hr _ (by decide) (by decide) (by decide)) hsp hrd hwr,
    hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hp hs => by
      have : r ≠ .s4 ∧ r ≠ .s6 := ⟨fun e => by subst e; simp [savedTop] at hs,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr r hp this.1 this.2]; exact h.pres r hp hs,
    by rw [hm]; exact h.sav, by rw [hm]; exact h.pk, by rw [hm]; exact h.mu, by rw [hm]; exact h.sg, h.pre,
    by rw [hr .s3 (by decide) (by decide) (by decide)]; exact h.s3, by rw [hm]; exact h.cache⟩

/-! ## The comparison -/

theorem cmpPre_ok {a b : Ptr} (ha : argOk (.ptr a) = true) (hb : argOk (.ptr b) = true) {n : Nat} (hn : n < 2 ^ 31 - 2048)
    (s : State) :
    WP isa (.block (Arg.instrs .a0 (.ptr a) ++ Arg.instrs .a1 (.ptr b) ++ Arg.instrs .s6 (.imm n) ++
      ([.li .t2 0] : List Instr))) s fun s' =>
      s'.gpr .a0 = s.gpr a.1 + BitVec.ofNat 64 a.2 ∧ s'.gpr .a1 = s.gpr b.1 + BitVec.ofNat 64 b.2 ∧
      s'.gpr .s6 = BitVec.ofNat 64 n ∧ s'.gpr .t2 = 0 ∧ (∀ r ∈ preserved, r ≠ .s6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have pa := base_pres (baseReg_of ha)
  have pb := base_pres (baseReg_of hb)
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (arg_ok .a0 ha (argOk_ne (by decide) ha) s) fun s1 e1 => ?_
  refine WP.mono (arg_ok .a1 hb (argOk_ne (by decide) hb) s1) fun s2 e2 => ?_
  refine WP.mono (arg_ok .s6 (a := .imm n) (by simp only [argOk, decide_eq_true_eq]; exact hn)
    (fun _ e => by cases e) s2) fun s3 e3 => ?_
  subst e1 e2 e3
  mrun []
  have nb3 : b.1 ≠ .a0 := fun e => by rw [e] at pb; simp [preserved] at pb
  and_intros
  all_goals first
    | rfl
    | trivial
    | (intro r hr hs
       have h1 : r ≠ .t2 := fun e => by subst e; simp [preserved] at hr
       have h2 : r ≠ .a1 := fun e => by subst e; simp [preserved] at hr
       have h3 : r ≠ .a0 := fun e => by subst e; simp [preserved] at hr
       simp only [h1, h2, h3, hs, ite_false])
    | simp only [KeyGen.argVal, nb3, ite_false]

theorem shr63_eq : ∀ n < 256, (BitVec.ofNat 64 n - 1) >>> 63 = if n = 0 then (1 : BitVec 64) else 0 := by
  decide +kernel

theorem shr63_of {v : BitVec 64} (h : v.toNat < 256) : (v - 1) >>> 63 = if v = 0 then (1 : BitVec 64) else 0 := by
  have hv := shr63_eq v.toNat h
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hv
  rw [hv]
  by_cases e : v = 0
  · subst e; rfl
  · have e' : ¬ v.toNat = 0 := fun h' => e (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    simp only [e, e', ↓reduceIte]

theorem cmpPost_ok (s : State) :
    WP isa (.block [.addi .t2 .t2 (-1), .shift .srl .d .t2 .t2 63, .logic .and .s4 .s4 .t2]) s
      fun s' => s'.gpr .s4 = s.gpr .s4 &&& ((s.gpr .t2 - 1) >>> 63) ∧
        (∀ r ∈ preserved, r ≠ .s4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  mrun []
  and_intros
  all_goals first
    | rfl
    | trivial
    | (intro r hr hs
       have h1 : r ≠ .t2 := fun e => by subst e; simp [preserved] at hr
       simp only [h1, hs, ite_false])

/-- `s4 ← s4 ∧ (the `n` bytes at `a` and `b` are equal)`. -/
theorem cmpAnd_okS {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a b : Ptr} {n : Nat}
    (pa : PtrIn L a n) (pb : PtrIn L b n) (hn : 0 < n) (hn' : n < 2 ^ 31 - 2048) :
    WP isa (cmpAnd a b n) s fun s' =>
      s'.gpr .s4 = s.gpr .s4 &&& flag (decide (bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n)) ∧
      (∀ r ∈ preserved, r ≠ .s4 → r ≠ .s6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  have cr : Covers [⟨lpa L a, n⟩, ⟨lpa L b, n⟩] (s.rd ++ s.wr) :=
    Covers.cons (hs.crE pa) (Covers.cons (hs.crE pb) Covers.nil)
  unfold cmpAnd
  refine WP.seq (WP.mono (cmpPre_ok pa.1 pb.1 hn' s) fun s₁ ⟨g3, g4, g26, g12, cs, m, rd, wr, sp⟩ => ?_)
  rw [hs.base (baseReg_of pa.1)] at g3
  rw [hs.base (baseReg_of pb.1)] at g4
  refine WP.seq (wp_loop_nz (CmpInv (lpa L a) (lpa L b) n s₁) (N := n) hn
      (fun k hk s h => cmp_step (by omega_using [hn']) (by rw [rd, wr]; exact cr) hk h) (fun s₂ h => ?_)
    ⟨by rw [g3]; simp [lpa, Lay.A], by rw [g4]; simp [lpa, Lay.A], by rw [g26, Nat.sub_zero], fun _ _ _ => rfl,
      rfl, rfl, rfl, rfl, by rw [g12]; decide,
      by rw [g12]; exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩⟩)
  refine WP.mono (cmpPost_ok s₂) fun s' ⟨r24, rs, m', rd', wr', sp'⟩ => ⟨?_, fun r hr h24 h26 => ?_,
    m'.trans (h.mem.trans m), rd'.trans (h.rd.trans rd), wr'.trans (h.wr.trans wr), sp'.trans (h.sp.trans sp)⟩
  · have e24 : s₂.gpr .s4 = s.gpr .s4 := (h.cs .s4 (by decide) (by decide)).trans (cs .s4 (by decide) (by decide))
    rw [r24, shr63_of h.lt, e24]
    congr 1
    have key : s₂.gpr .t2 = 0 ↔ bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n := by
      rw [h.eq, m]
      constructor
      · intro he
        exact Proof.MlKem.bytesAt_eq (Proof.MlKem.bytesAt_length _ _ _) fun t ht => by
          rw [he t ht, Proof.MlKem.bytesAt_getElem]
      · intro he t ht
        have := congrArg (fun L : List Byte => L[t]!) he
        simp only [Proof.MlKem.bytesAt_getElem! _ _ ht] at this
        exact this
    by_cases e : s₂.gpr .t2 = 0
    · simp only [e, decide_eq_true (key.mp e), ↓reduceIte, flag]
    · simp only [e, decide_eq_false (fun h' => e (key.mpr h')), ↓reduceIte, flag, Bool.false_eq_true]
  · rw [rs r hr h24]
    exact (h.cs r hr h26).trans (cs r hr h26)

/-! ## After the comparison -/

/-- At the end of `compute`: `s4` is the samplers' result `R` and whether
`c̃′ = c̃`. -/
abbrev KE (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, VC p STK σ s ∧ hintOf p σ = some h ∧ h.length = p.k ∧ Gd p σ A' cc R ∧
    s.gpr .s4 = R &&& flag (decide (Spec.MlDsa.H (muOf σ ++ w1Enc p σ A' cc h) p.ctildeLen =
      Proof.MlDsa.Verify.vCt p (sgOf p σ)))

theorem cmp_ok {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (h : KF p STK σ s) :
    WP isa (cmpAnd (sc oCT) (.s8, 0) p.ctildeLen) s (KE p STK σ) := by
  obtain ⟨A', cc, hh, R, hk5, hb⟩ := h
  have hk := hF.k
  have hct := hF.ct
  have pa : PtrIn (vlay p STK σ) (sc oCT) p.ctildeLen := by
    refine ⟨vptr_ok rfl (by decide), ?_⟩; rcases hct with e | e | e <;> vsep hF [e]
  have pb : PtrIn (vlay p STK σ) (.s8, 0) p.ctildeLen := by
    refine ⟨vptr_ok rfl (by decide), ?_⟩; have := hF.sig; have := hF.hint; vsep hF
  refine WP.mono (cmpAnd_okS hk5.vc.site pa pb (by omega_using [hct]) (by omega_using [hct]))
    fun s' ⟨r24, rs, m, rd, wr, sp⟩ => ⟨A', cc, hh, R, hk5.vc.congr rs m sp rd wr, hk5.hh, hk5.hint.1, hk5.gd, ?_⟩
  have e4 : bytesAt s.mem (lpa (vlay p STK σ) (.s8, 0)) p.ctildeLen = Proof.MlDsa.Verify.vCt p (sgOf p σ) := by
    have := sig_slice hk5.vc (o := 0) (l := p.ctildeLen) (by have := hF.sig; have := hF.hint; omega_arith)
    rw [List.drop_zero] at this
    exact this
  have e0 : bytesAt s.mem (lpa (vlay p STK σ) (sc oCT)) p.ctildeLen = _ := hb
  rw [r24, e0, e4, hk5.s4]

theorem cmp_taint {n : Nat} (hn : n = 32 ∨ n = 48 ∨ n = 64) : ∃ hc, (VG.RISCV64.taint.check
    (Taint.ofRegs [.s8, .s9, .s10, .s11]) (cmpAnd (sc oCT) (.s8, 0) n) hc).isSome = true := by
  rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem cmp_piece {p : Params} (hF : VFacts p) {STK : Nat} :
    VPiece p STK (KF p STK) (KE p STK) (cmpAnd (sc oCT) (.s8, 0) p.ctildeLen) :=
  ⟨fun _ _ _ h => cmp_ok hF h, rel_of (vtaint4 (cmp_taint hF.ct).choose_spec)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩⟩

end VG.Proof.MlDsa.RISCV64.Verify
