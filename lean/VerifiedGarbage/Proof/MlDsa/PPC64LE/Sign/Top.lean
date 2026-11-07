module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Output
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlDsa.Sign.Loop
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Kernel
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Output
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA signing on PPC64LE: the function

As on 32-bit ARM (`Proof/MlDsa/Arm/Sign/Correct.lean`, `SignCT.lean`,
`Top.lean`). The function returns 1 with `Sign_internal`'s signature (within
`maxBounds`) in `sig`, or 0 when `Sign_internal` returns nothing within
`minBounds` (`sign_ok`): its `ExpandA` or its loop does not finish
(`signMu_min_A`, `signMu_min_L`), or an iteration passes (`signMu_max`). Two
runs whose entry states agree on what the contract makes public leak the same
(`sign_tr`): the prologue and the return only the pointers, `ExpandA` its seed
and results, the loop what `signLeakT` says, and the signature its hint.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relStart relInv reg)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Impl.MlDsa.PPC64LE.KeyGen (callAt seqR)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (aSeed amat ParamsOk)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## `Sign_internal` -/

section
variable {p : Params} {σ : State}

theorem seedE_ij {i j : Nat} (hj : j < p.ℓ) : seedE p σ (p.ℓ * i + j) = aSeed (rhoOf p σ) i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [seedE, e1, e2]

theorem expandA_max (hok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome) :
    expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)) :=
  Proof.MlDsa.Sign.expandA_some fun i hi j hj => by rw [← seedE_ij hj]; exact hok _ (ij_lt hi hj)

theorem signMu_min_A (h : ∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (seedE p σ e) = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  obtain ⟨e, he, hn⟩ := h
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega
  exact Proof.MlDsa.Sign.signMu_none_A (Proof.MlDsa.Sign.expandA_none
    ⟨e / p.ℓ, (Nat.div_lt_iff_lt_mul hl).mpr he, e % p.ℓ, Nat.mod_lt _ hl, hn⟩)

theorem signMu_min_L (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)))
    (hL : loopF p σ minBounds minBounds.sign 0 = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  cases e : expandA p minBounds (rhoOf p σ) with
  | none => exact Proof.MlDsa.Sign.signMu_none_A e
  | some A' =>
    have := Proof.MlDsa.Sign.expandA_mono (show minBounds.rejNTT ≤ maxBounds.rejNTT by decide) e
    rw [hA] at this
    obtain rfl := (Option.some.inj this).symm
    exact Proof.MlDsa.Sign.signMu_none_L e hL

theorem signMu_max (hp : ParamsOk p) (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ))) {t : Nat}
    (ht : t < 814) (hr : RejT p σ t) (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome)
    (hpass : PassV p σ (p.ℓ * t)) :
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (sigV p σ (p.ℓ * t)) :=
  Proof.MlDsa.Sign.signMu_some hA (Proof.MlDsa.Sign.signLoop_pass _ _ _ _ _ _ _ hr (show t < maxBounds.sign by
    show t < 1000; omega) (iter_pass hp hs hpass))

end

/-! ## Before the return -/

/-- What the return needs: the pointer to `scratch`, our caller's registers in it, and the registers
we preserve. -/
structure TF (p : Params) (STK : Nat) (σ s : State) : Prop where
  r31 : s.gpr .r31 = sScr σ
  sav : TopSaved s.mem (sScr σ) σ
  pres : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = σ.gpr r
  sp : s.sp = σ.sp
  inr : ∀ o, 840 ≤ o → o + 8 ≤ 912 → InRegions (s.rd ++ s.wr) (sScr σ + BitVec.ofNat 64 o) 8

theorem SC1.tf {p : Params} (hF : SFacts p) {STK : Nat} {σ s : State} (h : SC1 p STK σ s) : TF p STK σ s := by
  have hs := h.site
  have hscr := hF.scr
  exact ⟨hs.r31, h.sav, h.pres, h.sp, fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := slay1 p STK σ) (o := o)
    (l := 8) (hs.cw 0 (by decide) (by decide)) (by rw [slay1_size0]; omega) _ _
    ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)⟩

theorem SC2.tf {p : Params} (hF : SFacts p) {STK : Nat} {σ s : State} (h : SC2 p STK σ s) : TF p STK σ s := by
  have hs := h.site
  have hscr := hF.scr
  exact ⟨hs.r31, h.sav, h.pres, h.sp, fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := slay2 p STK σ) (o := o)
    (l := 8) (hs.cw 0 (by decide) (by decide)) (by rw [slay2_size0]; omega) _ _
    ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)⟩

/-- Before the return: `r24`, and the signature in `sig` if it is 1. -/
structure FS (p : Params) (STK : Nat) (σ s : State) : Prop where
  tf : TF p STK σ s
  r01 : s.gpr .r24 = 0 ∨ s.gpr .r24 = 1
  ok : s.gpr .r24 = 1 →
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (bytesAt s.mem (sSig σ) p.sigLen)
  bad : s.gpr .r24 = 0 → signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none

theorem r24_one {s : State} (h : s.gpr .r24 = 0 ∨ s.gpr .r24 = 1) (hne : s.gpr .r24 ≠ 0) : s.gpr .r24 = 1 := by
  rcases h with e | e
  · exact absurd e hne
  · exact e

/-! ## The stack of `ExpandA` -/

theorem relct_and {P Q₁ Q₂ : State → State → Prop} {c : Prog isa} (h₁ : RelCT isa P c Q₁)
    (h₂ : RelCT isa P c Q₂) : RelCT isa P c fun x y => Q₁ x y ∧ Q₂ x y := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, q₁⟩ := h₁ _ _ _ _ _ _ hp e₁ e₂
  exact ⟨ht, q₁, (h₂ _ _ _ _ _ _ hp e₁ e₂).2⟩


theorem sdepth_seqR {f : Nat → Prog isa} {B : Nat} (h : ∀ k, sdepth (f k) ≤ B) :
    ∀ n a, sdepth (seqR f a n) ≤ B
  | 0, _ => Nat.zero_le _
  | n + 1, a => by
    simp only [seqR, sdepth]
    exact Nat.max_le.mpr ⟨h a, sdepth_seqR h n (a + 1)⟩

theorem sdepth_expandA {P : Prims} {S : Nat} (hP : SPrimsOk P S) (p : Params) :
    sdepth (Impl.MlDsa.PPC64LE.Sign.expandA P p) ≤ S := by
  unfold Impl.MlDsa.PPC64LE.Sign.expandA
  simp only [sdepth, Impl.MlKem.PPC64LE.copy, Nat.zero_max]
  exact sdepth_seqR (fun e => by
    simp only [sampleE, rejAt, callAt, sdepth, Nat.zero_max, Nat.max_zero]
    exact hP.rejNTT.stack) _ _

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
  (hp : ParamsOk p)
include hP hF hS hp

theorem rest_ok {σ : State} (hpre : CPre p STK σ) {s : State} (h : IM p STK σ s) (fc : FC STK σ s) :
    WP isa (rest P p) s (FS p STK σ) := by
  have hA := expandA_max h.ok
  unfold rest
  refine WP.seq (WP.mono ((decode_piece hP hF hS).ok σ s hpre ⟨h, fc⟩) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (signLoop_ok hP hF hS hp hpre.1 h1.ik) fun s2 h2 => ?_)
  unfold ifOk ifOkElse
  refine WP.ite _ (eval_nonzero s2 .r24) (fun hb => ?_) fun hb => WP.block_nil ?_
  · have h1 := r24_one h2.r01 (by simpa using hb)
    obtain ⟨t, ht, hr, hs, hpass, hct, hz, hh⟩ := h2.pass h1
    refine WP.mono (output_ok hP hF hS ⟨h2.k, hz, hh, hpass, h1⟩ hct) fun s4 ⟨k4, hb4, h4⟩ =>
      ⟨k4.sc.tf hF, .inr h4, fun _ => ?_, fun h0 => absurd (h0.symm.trans h4) (by decide)⟩
    have e : (slay2 p STK σ).A 4 0 = sSig σ := by simp only [Lay.A, BitVec.add_zero]; rfl
    rw [← e, hb4]
    exact signMu_max hp hA ht hr hs hpass
  · have h0 : s2.gpr .r24 = 0 := by simpa using hb
    exact ⟨h2.k.sc.tf hF, .inl h0, fun h1 => absurd (h0.symm.trans h1) (by decide),
      fun _ => signMu_min_L hA (h2.fail h0)⟩

omit hP hS hp in
/-- The prologue, keeping `FC`. -/
theorem proC_ok (h48 : 48 ≤ STK) {σ : State} (hpre : CPre p STK σ) :
    WP isa (.block pro) σ fun s => (SC1 p STK σ s ∧ s.gpr .r24 = 1) ∧ FC STK σ s :=
  WP.mono (wp_frame (spro_ok hF h48 hpre.1) (by decide)) fun _ ⟨h₁, f₁⟩ =>
    ⟨h₁, FC.step (Frame.refl _ _) rfl rfl (Nat.zero_le _) (by have := hpre.1.stk; have := σ.sp.isLt; omega) f₁⟩

omit hp in
/-- `ExpandA`, keeping `FC`. -/
theorem expC_ok {σ s : State} (hpre : CPre p STK σ) (h : (SC1 p STK σ s ∧ s.gpr .r24 = 1) ∧ FC STK σ s) :
    WP isa (Impl.MlDsa.PPC64LE.Sign.expandA P p) s fun s' => IA p STK σ (p.k * p.ℓ) s' ∧ FC STK σ s' :=
  WP.mono (wp_frame (expandA_ok hP hF hS h.1.1 h.1.2)
    (by have := sdepth_expandA hP p; have := hpre.1.stk; have := σ.sp.isLt; omega))
    fun _ ⟨h₂, f₂⟩ => ⟨h₂, FC.step h.2 h.1.1.wr h.1.1.sp (Nat.le_trans (sdepth_expandA hP p) hS)
      (by have := hpre.1.stk; have := σ.sp.isLt; omega) f₂⟩

/-- Signing, with the cache of `CPre`. -/
theorem sign_ok {σ : State} (hpre : CPre p STK σ) (h48 : 48 ≤ STK) :
    WP isa (sign P p) σ fun s' =>
      PPC64LE.target.abiPreserved σ s' ∧ (Spec.MlDsa.signContract p PPC64LE.abi STK).post σ s' := by
  unfold sign
  refine WP.seq (WP.mono (proC_ok hF h48 hpre) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (expC_ok hP hF hS hpre h₁) fun s₂ ⟨h₂, f₂⟩ => ?_)
  refine WP.seq (WP.mono (show WP isa (ifOk (rest P p)) s₂ (FS p STK σ) from ?_) fun s₄ h₄ => ?_)
  · unfold ifOk ifOkElse
    refine WP.ite _ (eval_nonzero s₂ .r24) (fun hb => ?_) fun hb => WP.block_nil ?_
    · exact rest_ok hP hF hS hp hpre (h₂.im (r24_one h₂.r01 (by simpa using hb))) f₂
    · have h0 : s₂.gpr .r24 = 0 := by simpa using hb
      exact ⟨h₂.sc.tf hF, .inl h0, fun h1 => absurd (h0.symm.trans h1) (by decide),
        fun _ => signMu_min_A (h₂.bad h0)⟩
  · refine WP.mono (topEnd_ok h₄.tf.r31 h₄.tf.sav h₄.tf.inr h₄.tf.pres)
      fun s' ⟨pr, lr, r3, m', sp', _, _⟩ => ⟨⟨pr, sp'.trans h₄.tf.sp, lr⟩, ?_⟩
    sig_post [Spec.MlDsa.signContract, Spec.MlDsa.signSig, PPC64LE.abi, PPC64LE.argRegs]
    rw [r3, m']
    rcases h₄.r01 with h0 | h1
    · exact .inr ⟨by rw [h0]; rfl, h₄.bad h0⟩
    · exact .inl ⟨by rw [h1]; rfl, maxBounds, h₄.ok h1⟩

/-! ## Two runs -/

omit hP hF hS hp in
/-- Two runs whose `ExpandA` finished agree on what their loops leak. -/
theorem pub_leq {σ₁ σ₂ : State} (hpub : sPub p σ₁ σ₂)
    (hA₁ : expandA p maxBounds (rhoOf p σ₁) = some (amat p (Am p σ₁)))
    (hA₂ : expandA p maxBounds (rhoOf p σ₂) = some (amat p (Am p σ₂))) : LeakEq p 0 σ₁ σ₂ := by
  have e := hpub.2.2.2.2.2.2
  rw [Proof.MlDsa.Sign.signLeak_eq hA₁, Proof.MlDsa.Sign.signLeak_eq hA₂, pub_rho hpub] at e
  exact List.append_cancel_left e

omit hP hF hS hp in
theorem relct_nil {Q : State → State → Prop} {P : State → State → Prop} (h : ∀ x y, P x y → Q x y) :
    RelCT isa P (.block []) Q := by
  intro _ _ _ _ _ _ hr e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, h _ _ hr⟩

omit hP hF hS hp in
theorem hintIs_unique {m : Mem} {a : Addr} {h h' : Vector Bool n} (H : HintIs m a 1 [h]) (H' : HintIs m a 1 [h']) :
    h = h' := by
  apply Vector.ext
  intro j hj
  have e := H.2 0 (by decide) j hj
  have e' := H'.2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero, getElem!_pos h j hj, getElem!_pos h' j hj] at e e'
  rw [e] at e'
  revert e'
  cases h[j] <;> cases h'[j] <;> decide

omit hp in
/-- The two runs of the signature, from the end of the loop. -/
theorem outIf_tr :
    RelCT isa (OX p STK) (ifOk (output P p)) fun x y => Rel2 (SPre p STK) (sPub p) (SC2 p STK) x y := by
  unfold ifOk ifOkElse
  refine RelCT.ite (fun x y ⟨_, _, _, _, _, _, _, e, _⟩ => by rw [eval_nonzero, eval_nonzero, e]) ?_ ?_
  · refine liftG (Q₀ := fun _ _ => True) (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂, e24, hh⟩, hb⟩ => ?_)
      (RelCT.mono (output_tr hP hF hS) (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂, e24, hh⟩, hb⟩ => ?_) fun _ _ h => h)
    · have hx := r24_one h₁.r01 (by rw [eval_nonzero] at hb; simpa using hb)
      have hy := r24_one h₂.r01 (by rw [← e24]; rw [eval_nonzero] at hb; simpa using hb)
      obtain ⟨t₁, -, -, -, ps₁, ct₁, z₁, hh₁⟩ := h₁.pass hx
      obtain ⟨t₂, -, -, -, ps₂, ct₂, z₂, hh₂⟩ := h₂.pass hy
      exact ⟨_, _, output_ok hP hF hS ⟨h₁.k, z₁, hh₁, ps₁, hx⟩ ct₁, output_ok hP hF hS ⟨h₂.k, z₂, hh₂, ps₂, hy⟩ ct₂,
        fun x' y' a b _ => ⟨σ₁, σ₂, p₁, p₂, pub, a.1.sc, b.1.sc⟩⟩
    · have hx := r24_one h₁.r01 (by rw [eval_nonzero] at hb; simpa using hb)
      have hy := r24_one h₂.r01 (by rw [← e24]; rw [eval_nonzero] at hb; simpa using hb)
      obtain ⟨t₁, -, -, -, ps₁, ct₁, z₁, hh₁⟩ := h₁.pass hx
      obtain ⟨t₂, -, -, -, ps₂, ct₂, z₂, hh₂⟩ := h₂.pass hy
      obtain ⟨f, f₁, f₂⟩ := hh hx
      refine ⟨σ₁, σ₂, p.ℓ * t₁, p.ℓ * t₂, p₁, p₂, pub, ⟨⟨h₁.k, z₁, hh₁, ps₁, hx⟩, ct₁⟩,
        ⟨⟨h₂.k, z₂, hh₂, ps₂, hy⟩, ct₂⟩, fun i hi => ?_⟩
      have a₂ := hh₂ i hi
      rw [← SL_pub pub] at a₂
      exact (hintIs_unique (hh₁ i hi) (f₁ i hi)).trans (hintIs_unique (f₂ i hi) a₂)
  · exact relct_nil fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂, _⟩, _⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.k.sc, h₂.k.sc⟩

/-- `rest`, from runs whose `ExpandA` finished. -/
theorem rest_tr :
    RelCT isa (Rel2 (CPre p STK) (cPub p) fun σ s => IM p STK σ s ∧ FC STK σ s) (rest P p)
      fun x y => Rel2 (SPre p STK) (sPub p) (SC2 p STK) x y := by
  unfold rest
  have d := decode_piece hP hF hS (STK := STK)
  refine RelCT.seq (relInv d.ok d.tr) ?_
  refine RelCT.mono (P := RS p STK (LeakEq p 0) (ID p STK · p.ℓ p.k p.k)) ?_
    (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁.1, p₂.1, pub.1,
      pub_leq pub.1 (expandA_max h₁.ok) (expandA_max h₂.ok), h₁, h₂⟩) fun _ _ h => h
  refine RelCT.seq ?_ (outIf_tr hP hF hS)
  exact RelCT.mono (signLoop_tr hP hF hS hp) (fun x y h => h.mono fun _ _ h => h.ik) fun _ _ h => h

/-- Two runs whose entry states agree on the public data leak the same. -/
theorem sign_tr (h48 : 48 ≤ STK) :
    RelCT isa (Rel2 (CPre p STK) (cPub p) fun σ s => s = σ) (sign P p) fun _ _ => True := by
  unfold sign
  refine RelCT.seq (relInv (fun σ s hp e => by subst e; exact proC_ok hF h48 hp)
    (RelCT.mono (spro_piece hF h48).cache.tr (fun _ _ h => h) fun _ _ h => h)) ?_
  have ea : RelCT isa (Rel2 (CPre p STK) (cPub p) fun σ s => (SC1 p STK σ s ∧ s.gpr .r24 = 1) ∧ FC STK σ s)
      (Impl.MlDsa.PPC64LE.Sign.expandA P p) (RR p STK (IA p STK · (p.k * p.ℓ)) E24) :=
    RelCT.mono (expandA_tr hP hF hS) (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨⟨σ₁, σ₂, p₁.1, p₂.1, pub.1, i₁.1, i₂.1⟩, trivial⟩)
    fun _ _ h => h
  refine RelCT.seq (relct_and (relInv (fun σ s hp h => expC_ok hP hF hS hp h)
    (RelCT.mono ea (fun _ _ h => h) fun _ _ _ => trivial)) (RelCT.mono ea (fun _ _ h => h) fun _ _ h => h.2)) ?_
  refine RelCT.seq (Q := fun _ _ => True) (R := fun x y => Rel2 (SPre p STK) (sPub p) (SC1 p STK) x y ∨
      Rel2 (SPre p STK) (sPub p) (SC2 p STK) x y) ?_
    (relOr (srel1 (fun _ _ h => h) (by taint_decide)) (srel2 (fun _ _ h => h) (by taint_decide)))
  unfold ifOk ifOkElse
  refine RelCT.ite (fun x y ⟨_, e⟩ => by rw [eval_nonzero, eval_nonzero, e]) ?_ ?_
  · refine RelCT.mono (rest_tr hP hF hS hp) (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁, f₁⟩, ⟨h₂, f₂⟩⟩, e⟩, hb⟩ => ?_)
      fun _ _ h => .inr h
    have hx := r24_one h₁.r01 (by rw [eval_nonzero] at hb; simpa using hb)
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁.im hx, f₁⟩, ⟨h₂.im (r24_one h₂.r01 (by rw [← e, hx]; decide)), f₂⟩⟩
  · exact relct_nil fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁, _⟩, ⟨h₂, _⟩⟩, _⟩, _⟩ =>
      .inl ⟨σ₁, σ₂, p₁.1, p₂.1, pub.1, h₁.sc, h₂.sc⟩
end



/-! ## The kernel -/

/-- The precondition of `signWithCacheContract` with `K` bytes of stack. -/
structure KPre (p : Params) (K : Nat) (σ : State) : Prop where
  stk : K ≤ σ.sp.toNat
  rd : σ.rd = [reg (sSk σ) p.skLen, reg (sMu σ) 64, reg (sRnd σ) 32, reg (σ.gpr .r8) (σ.gpr .r9).toNat]
  wr : σ.wr = [reg (sSig σ) p.sigLen, reg (sScr σ) (scrLen p)]
  d_kg : (reg (sSk σ) p.skLen).Disjoint (reg (sSig σ) p.sigLen)
  d_kc : (reg (sSk σ) p.skLen).Disjoint (reg (sScr σ) (scrLen p))
  d_mg : (reg (sMu σ) 64).Disjoint (reg (sSig σ) p.sigLen)
  d_mc : (reg (sMu σ) 64).Disjoint (reg (sScr σ) (scrLen p))
  d_rg : (reg (sRnd σ) 32).Disjoint (reg (sSig σ) p.sigLen)
  d_rc : (reg (sRnd σ) 32).Disjoint (reg (sScr σ) (scrLen p))
  d_gc : (reg (sSig σ) p.sigLen).Disjoint (reg (sScr σ) (scrLen p))
  d_gx : (reg (sSig σ) p.sigLen).Disjoint (reg (σ.gpr .r8) (σ.gpr .r9).toNat)
  d_cx : (reg (sScr σ) (scrLen p)).Disjoint (reg (σ.gpr .r8) (σ.gpr .r9).toNat)
  b_k : (below σ.sp K).Disjoint (reg (sSk σ) p.skLen)
  b_m : (below σ.sp K).Disjoint (reg (sMu σ) 64)
  b_r : (below σ.sp K).Disjoint (reg (sRnd σ) 32)
  b_g : (below σ.sp K).Disjoint (reg (sSig σ) p.sigLen)
  b_c : (below σ.sp K).Disjoint (reg (sScr σ) (scrLen p))
  b_x : (below σ.sp K).Disjoint (reg (σ.gpr .r8) (σ.gpr .r9).toNat)
  f_k : (sSk σ).toNat + p.skLen ≤ 2 ^ 64
  f_m : (sMu σ).toNat + 64 ≤ 2 ^ 64
  f_r : (sRnd σ).toNat + 32 ≤ 2 ^ 64
  f_g : (sSig σ).toNat + p.sigLen ≤ 2 ^ 64
  f_c : (sScr σ).toNat + scrLen p ≤ 2 ^ 64
  f_x : (σ.gpr .r8).toNat + (σ.gpr .r9).toNat ≤ 2 ^ 64
  polys : σ.gpr .r9 = 0 ∨ ((σ.gpr .r9).toNat = 4 * n * (p.ℓ + 2 * p.k) ∧
    Proof.MlDsa.CachedSecretPolys p σ.mem (σ.gpr .r8) (skOf p σ))

theorem kpre_of {p : Params} {k : Nat} {σ : State}
    (h : (Proof.MlDsa.signWithCacheContract p PPC64LE.abi (k + 1)).pre σ) : KPre p (k + 1) σ := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, Spec.MlDsa.signSig, PPC64LE.abi,
    PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24⟩

section
variable {p : Params} {STK : Nat} {σ : State} (h : KPre p (STK + 96) σ)
include h

theorem KPre.fit : STK + 96 < 2 ^ 64 := by have := h.stk; have := σ.sp.isLt; omega

theorem KPre.b96 : Region.Sub (below σ.sp 96) (below σ.sp (STK + 96)) := below_sub (by omega) h.fit

theorem KPre.bSTK : Region.Sub (below (kSt .r8 .r9 σ).sp STK) (below σ.sp (STK + 96)) := by
  rw [kSt_sp]
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have := h.fit; have := h.stk
  bv_omega

/-- Bytes apart from the stack are as on entry, in the state signing starts in. -/
theorem KPre.bytes {a : Addr} {l : Nat} (hd : (below σ.sp (STK + 96)).Disjoint (reg a l)) (hl : l ≤ 2 ^ 64) :
    bytesAt (kSt .r8 .r9 σ).mem a l = bytesAt σ.mem a l :=
  Proof.MlKem.bytesAt_frame (kSt_mem σ) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact (hd.sub_left h.b96).symm) hl

theorem kSt_inputs : skOf p (kSt .r8 .r9 σ) = skOf p σ ∧ muOf (kSt .r8 .r9 σ) = muOf σ ∧
    rndOf (kSt .r8 .r9 σ) = rndOf σ := by
  simp only [skOf, muOf, rndOf, sSk, sMu, sRnd, kSt_gpr σ (show Reg.r3 ≠ .r14 by decide) (by decide),
    kSt_gpr σ (show Reg.r4 ≠ .r14 by decide) (by decide), kSt_gpr σ (show Reg.r5 ≠ .r14 by decide) (by decide)]
  exact ⟨h.bytes h.b_k (by have := h.f_k; omega), h.bytes h.b_m (by decide), h.bytes h.b_r (by decide)⟩

/-- The state signing starts in satisfies `CPre`. -/
theorem kSt_cpre : CPre p STK (kSt .r8 .r9 σ) := by
  have e3 := kSt_gpr (a := .r8) (b := .r9) σ (r := .r3) (by decide) (by decide)
  have e4 := kSt_gpr (a := .r8) (b := .r9) σ (r := .r4) (by decide) (by decide)
  have e5 := kSt_gpr (a := .r8) (b := .r9) σ (r := .r5) (by decide) (by decide)
  have e6 := kSt_gpr (a := .r8) (b := .r9) σ (r := .r6) (by decide) (by decide)
  have e7 := kSt_gpr (a := .r8) (b := .r9) σ (r := .r7) (by decide) (by decide)
  have e14 : (kSt .r8 .r9 σ).gpr .r14 = σ.gpr .r8 := kSt_r14 σ
  have e15 : (kSt .r8 .r9 σ).gpr .r15 = σ.gpr .r9 := kSt_r15 σ
  have bs := h.bSTK
  have hstk : STK ≤ (kSt .r8 .r9 σ).sp.toNat := by
    rw [kSt_sp]; have := h.stk; have := h.fit; bv_omega
  refine ⟨⟨hstk, ⟨[reg (σ.gpr .r8) (σ.gpr .r9).toNat], ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sSk, sMu, sRnd, sSig, sScr, e3, e4, e5, e6, e7, e14, e15, kSt_rd, kSt_wr]
  · rw [h.rd]; rfl
  · exact h.wr
  · exact h.d_kg
  · exact h.d_kc
  · exact h.d_mg
  · exact h.d_mc
  · exact h.d_rg
  · exact h.d_rc
  · exact h.d_gc
  · exact h.b_k.sub_left bs
  · exact h.b_m.sub_left bs
  · exact h.b_r.sub_left bs
  · exact h.b_g.sub_left bs
  · exact h.b_c.sub_left bs
  · exact h.f_k
  · exact h.f_m
  · exact h.f_r
  · exact h.f_g
  · exact h.f_c
  · rcases h.polys with h0 | ⟨hl, hc⟩
    · exact .inl h0
    · refine .inr ⟨hl, fun i hi => ?_⟩
      rw [kSt_inputs h |>.1]
      have hsub : Region.Sub (Proof.MlDsa.Verify.polyRegion (σ.gpr .r8 + BitVec.ofNat 64 (4 * n * i)))
          (reg (σ.gpr .r8) (σ.gpr .r9).toNat) :=
        Offset.sub_base _ (by rw [hl]; show 4 * 256 * i + 1024 ≤ 4 * 256 * (p.ℓ + 2 * p.k); omega)
      exact Proof.MlDsa.Verify.polyIs_frame (kSt_mem σ) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact (h.b_x.sub_left h.b96).symm.sub_left hsub) (hc i hi)
  · rw [h.rd]; simp
  · exact h.d_gx.symm
  · exact h.d_cx.symm
  · exact h.b_x.symm.sub_right bs

end

/-- The public data of two kernels' entry states give `cPub` of the states
signing starts in. -/
theorem kSt_cpub {p : Params} {STK : Nat} {σ₁ σ₂ : State} (h₁ : KPre p (STK + 96) σ₁) (h₂ : KPre p (STK + 96) σ₂)
    (hpub : (Proof.MlDsa.signWithCacheContract p PPC64LE.abi (STK + 96)).pub σ₁ σ₂) :
    cPub p (kSt .r8 .r9 σ₁) (kSt .r8 .r9 σ₂) := by
  sig_pub [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, Spec.MlDsa.signSig, PPC64LE.abi,
    PPC64LE.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9⟩ := hpub
  have g : ∀ {r : Reg}, r ≠ .r14 → r ≠ .r15 → σ₁.gpr r = σ₂.gpr r →
      (kSt .r8 .r9 σ₁).gpr r = (kSt .r8 .r9 σ₂).gpr r := fun a b e => by
    rw [kSt_gpr σ₁ a b, kSt_gpr σ₂ a b, e]
  obtain ⟨k₁, m₁, r₁⟩ := kSt_inputs h₁
  obtain ⟨k₂, m₂, r₂⟩ := kSt_inputs h₂
  refine ⟨⟨by rw [kSt_sp, kSt_sp, hsp], g (by decide) (by decide) h3, g (by decide) (by decide) h4,
    g (by decide) (by decide) h5, g (by decide) (by decide) h6, g (by decide) (by decide) h7, ?_⟩, ?_, ?_⟩
  · rw [k₁, m₁, r₁, k₂, m₂, r₂]; exact hl
  · rw [kSt_r14, kSt_r14, h8]
  · rw [kSt_r15, kSt_r15, h9]

/-- A state that satisfies `signWithCacheContract`'s precondition, for the
contract's satisfiability: an empty cache. -/
def kSat (p : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x8000 | .r5 => 0x9000 | .r6 => 0xA000 | .r7 => 0x10000 | .r8 => 0x1000 | _ => 0
  lr := 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x8000, 64⟩, ⟨0x9000, 32⟩, ⟨0x1000, 0⟩]
  wr := [⟨0xA000, p.sigLen⟩, ⟨0x10000, scrLen p⟩]

/-- `vg_mldsa*_sign_with_cache` of the parameter set `p` meets its contract
with `S + 96` bytes of stack (the 96 of its frames), for any verified
implementations `P` of the primitives it calls with at most `S` bytes of
stack whose samplers' results are public (`SPrimsOk`), `S` at least the 48
bytes the sponge needs, and signing's frames within `S` bytes. -/
theorem withCache_verified {P : Prims} {S : Nat} (hP : SPrimsOk P S) (h48 : 48 ≤ S)
    (p : Spec.MlDsa.Params) (hp3 : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hd : sdepth (sign P p) ≤ S)
    (hsat : (Proof.MlDsa.signWithCacheContract p PPC64LE.abi (S + 96)).pre (kSat p)) :
    Verified PPC64LE.target (withCache P p) (Proof.MlDsa.signWithCacheContract p PPC64LE.abi (S + 96)) := by
  have hF := sfacts hp3
  have hp : ParamsOk p := by rcases hp3 with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  have body (σ : State) (hk : KPre p (S + 96) σ) := sign_ok hP hF (Nat.le_refl S) hp (kSt_cpre hk) h48
  have hd96 (σ : State) (hk : KPre p (S + 96) σ) : ∀ X ∈ σ.wr, (below σ.sp 96).Disjoint X := fun X hX => by
    rw [hk.wr] at hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl
    · exact hk.b_g.sub_left hk.b96
    · exact hk.b_c.sub_left hk.b96
  have hn (σ : State) (hk : KPre p (S + 96) σ) : sdepth (sign P p) + 96 < 2 ^ 64 := by have := hk.fit; omega
  refine ⟨fun σ hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨kSat p, hsat⟩⟩
  · have hk := kpre_of (k := S + 95) hs
    refine WP.mono (kernel_wp (a := .r8) (b := .r9) (by decide) (by decide) (by decide)
      (by have := hk.stk; omega) (hd96 σ hk) (hn σ hk)
      (R := fun m r => Spec.MlDsa.Outcome (fun b => Spec.MlDsa.signMu p b (skOf p σ) (muOf σ) (rndOf σ))
        (r.setWidth 32) (bytesAt m (sSig σ) p.sigLen))
      (WP.mono (body σ hk) fun s' ⟨ha, hq⟩ => ⟨ha, ?_⟩)) fun s' ⟨ha, hq⟩ => ⟨ha, ?_⟩
    · generalize hτ : kSt .r8 .r9 σ = τ at hq
      sig_post [Spec.MlDsa.signContract, Spec.MlDsa.signSig, PPC64LE.abi, PPC64LE.argRegs] at hq
      subst hτ
      obtain ⟨k₁, m₁, r₁⟩ := kSt_inputs hk
      simp only [skOf, muOf, rndOf, sSk, sMu, sRnd, kSt_gpr σ (show Reg.r3 ≠ .r14 by decide) (by decide),
        kSt_gpr σ (show Reg.r4 ≠ .r14 by decide) (by decide), kSt_gpr σ (show Reg.r5 ≠ .r14 by decide) (by decide)]
        at k₁ m₁ r₁
      rw [kSt_gpr σ (show Reg.r3 ≠ .r14 by decide) (by decide), kSt_gpr σ (show Reg.r4 ≠ .r14 by decide) (by decide),
        kSt_gpr σ (show Reg.r5 ≠ .r14 by decide) (by decide), kSt_gpr σ (show Reg.r6 ≠ .r14 by decide) (by decide)]
        at hq
      rw [k₁, m₁, r₁] at hq
      exact hq
    · sig_post [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, Spec.MlDsa.signSig, PPC64LE.abi,
        PPC64LE.argRegs]
      exact hq
  · have k₁ := kpre_of (k := S + 95) h₁
    have k₂ := kpre_of (k := S + 95) h₂
    refine (kernel_tr (a := .r8) (b := .r9) (by decide) (by decide) (by decide)
      (P := fun x y => KPre p (S + 96) x ∧ KPre p (S + 96) y ∧
        (Proof.MlDsa.signWithCacheContract p PPC64LE.abi (S + 96)).pub x y)
      (fun x y ⟨_, _, hp⟩ => by
        sig_pub [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, Spec.MlDsa.signSig, PPC64LE.abi,
          PPC64LE.argRegs] at hp
        exact hp.1)
      (fun x y ⟨a, b, _⟩ => ⟨by have := a.stk; omega, by have := b.stk; omega, hd96 x a, hd96 y b⟩) (hn s₁ k₁)
      (fun x y ⟨a, b, _⟩ => ⟨⟨_, body x a⟩, ⟨_, body y b⟩⟩)
      (RelCT.mono (sign_tr hP hF (Nat.le_refl S) hp h48) (fun u v ⟨x, y, ⟨a, b, hp⟩, eu, ev⟩ => by
        subst eu ev; exact ⟨_, _, kSt_cpre a, kSt_cpre b, kSt_cpub a b hp, rfl, rfl⟩) fun _ _ h => h)
      s₁ s₂ t₁ t₂ s₁' s₂' ⟨k₁, k₂, hpub⟩ e₁ e₂).1

end VG.Proof.MlDsa.PPC64LE.Sign
