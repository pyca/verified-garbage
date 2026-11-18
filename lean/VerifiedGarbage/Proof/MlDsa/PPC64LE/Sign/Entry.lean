module

-- separate module: its proofs, generic over the kernel, build in parallel with those of the primitives, which `Inst` also imports
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Output
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Kernel
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Output
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! ### `MlDsa.PPC64LE.Sign.Top`, which only this module used -/

section

/-!
# ML-DSA signing on PPC64LE: the function

As on 32-bit ARM (`Proof/MlDsa/Arm/Sign/PhaseOCT.lean`, `SignCT.lean`,
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
  have hl : 0 < p.ℓ := by omega_using [hj]
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
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega_using [he]
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
    show t < 1000; omega_using [ht]) (iter_pass hp hs hpass))

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
    (l := 8) (hs.cw 0 (by decide) (by decide)) (by rw [slay1_size0]; omega_using [hscr, h₂]) _ _
    ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)⟩

theorem SC2.tf {p : Params} (hF : SFacts p) {STK : Nat} {σ s : State} (h : SC2 p STK σ s) : TF p STK σ s := by
  have hs := h.site
  have hscr := hF.scr
  exact ⟨hs.r31, h.sav, h.pres, h.sp, fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := slay2 p STK σ) (o := o)
    (l := 8) (hs.cw 0 (by decide) (by decide)) (by rw [slay2_size0]; omega_using [hscr, h₂]) _ _
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
    ⟨h₁, FC.step (Frame.refl _ _) rfl rfl (Nat.zero_le _) (by have := hpre.1.stk; have := σ.sp.isLt; omega_arith) f₁⟩

omit hp in
/-- `ExpandA`, keeping `FC`. -/
theorem expC_ok {σ s : State} (hpre : CPre p STK σ) (h : (SC1 p STK σ s ∧ s.gpr .r24 = 1) ∧ FC STK σ s) :
    WP isa (Impl.MlDsa.PPC64LE.Sign.expandA P p) s fun s' => IA p STK σ (p.k * p.ℓ) s' ∧ FC STK σ s' :=
  WP.mono (wp_frame (expandA_ok hP hF hS h.1.1 h.1.2)
    (by have := sdepth_expandA hP p; have := hpre.1.stk; have := σ.sp.isLt; omega_arith))
    fun _ ⟨h₂, f₂⟩ => ⟨h₂, FC.step h.2 h.1.1.wr h.1.1.sp (Nat.le_trans (sdepth_expandA hP p) hS)
      (by have := hpre.1.stk; have := σ.sp.isLt; omega_arith) f₂⟩

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

theorem KPre.fit : STK + 96 < 2 ^ 64 := by have := h.stk; have := σ.sp.isLt; omega_arith

theorem KPre.b96 : Region.Sub (below σ.sp 96) (below σ.sp (STK + 96)) := below_sub (by omega_using []) h.fit

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
  exact ⟨h.bytes h.b_k (by have := h.f_k; omega_using [this]), h.bytes h.b_m (by decide), h.bytes h.b_r (by decide)⟩

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
        Offset.sub_base _ (by rw [hl]; show 4 * 256 * i + 1024 ≤ 4 * 256 * (p.ℓ + 2 * p.k); omega_using [hi])
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
  have hn (σ : State) (hk : KPre p (S + 96) σ) : sdepth (sign P p) + 96 < 2 ^ 64 := by have := hk.fit; omega_using [hd, this]
  refine ⟨fun σ hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨kSat p, hsat⟩⟩
  · have hk := kpre_of (k := S + 95) hs
    refine WP.mono (kernel_wp (a := .r8) (b := .r9) (by decide) (by decide) (by decide)
      (by have := hk.stk; omega_using [this]) (hd96 σ hk) (hn σ hk)
      (R := fun m r => Spec.MlDsa.Outcome (fun b => Spec.MlDsa.signMu p b (skOf p σ) (muOf σ) (rndOf σ))
        (r.setWidth 32) (bytesAt m (sSig σ) p.sigLen))
      (WP.mono (body σ hk) fun s' ⟨ha, hq⟩ => ⟨ha, ?_⟩) (fun m m' _ fl h => by
        -- The pops lose the frames' bytes, which lie apart from the signature.
        have e : bytesAt m' (sSig σ) p.sigLen = bytesAt m (sSig σ) p.sigLen := List.map_congr_left fun i hi =>
          lost_byte fl (R := reg (sSig σ) p.sigLen) (hk.b_g.sub_left hk.b96).symm (List.mem_range.mp hi)
        rw [e]; exact h)) fun s' ⟨ha, hq⟩ => ⟨ha, ?_⟩
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
      (fun x y ⟨a, b, _⟩ => ⟨by have := a.stk; omega_using [this], by have := b.stk; omega_using [this], hd96 x a, hd96 y b⟩) (hn s₁ k₁)
      (fun x y ⟨a, b, _⟩ => ⟨⟨_, body x a⟩, ⟨_, body y b⟩⟩)
      (RelCT.mono (sign_tr hP hF (Nat.le_refl S) hp h48) (fun u v ⟨x, y, ⟨a, b, hp⟩, eu, ev⟩ => by
        subst eu ev; exact ⟨_, _, kSt_cpre a, kSt_cpre b, kSt_cpub a b hp, rfl, rfl⟩) fun _ _ h => h)
      s₁ s₂ t₁ t₂ s₁' s₂' ⟨k₁, k₂, hpub⟩ e₁ e₂).1

end VG.Proof.MlDsa.PPC64LE.Sign

end

end

/-!
# ML-DSA signing on PPC64LE: the entries

`entry n code p prepared` (`Impl/MlDsa/PPC64LE/Sign/Sign.lean`) calls the
kernel `code`, `vg_mldsa*_sign_with_cache` (`signWithCacheContract`), with
the cache at `sk + off` of `len` bytes: none (`vg_mldsa*_sign`, against
`signContract`, `sign_entry_verified`), or the polynomials a prepared private
key holds after its encoded key (`vg_mldsa*_sign_prepared`, against
`preparedSignContract`, `prepared_entry_verified`). Both contracts have the
key at `r3` in a region of `L` bytes and are otherwise the same (`EPre`);
the kernel's precondition holds of its entry state (`cs_kpre`), the bytes of
the inputs are those our caller gave (the entry's frame is on the stack), and
the result and signature are the kernel's (`entryS_wp`). Two runs leak the
same if their entry states agree on what the contract makes public
(`entryS_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (scrLen reg)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The preconditions of the entries, with the key in `L` bytes and `X`. -/
structure EPre (p : Params) (L K : Nat) (X : State → Prop) (σ : State) : Prop where
  stk : K ≤ σ.sp.toNat
  rd : σ.rd = [reg (sSk σ) L, reg (sMu σ) 64, reg (sRnd σ) 32]
  wr : σ.wr = [reg (sSig σ) p.sigLen, reg (sScr σ) (scrLen p)]
  d_kg : (reg (sSk σ) L).Disjoint (reg (sSig σ) p.sigLen)
  d_kc : (reg (sSk σ) L).Disjoint (reg (sScr σ) (scrLen p))
  d_mg : (reg (sMu σ) 64).Disjoint (reg (sSig σ) p.sigLen)
  d_mc : (reg (sMu σ) 64).Disjoint (reg (sScr σ) (scrLen p))
  d_rg : (reg (sRnd σ) 32).Disjoint (reg (sSig σ) p.sigLen)
  d_rc : (reg (sRnd σ) 32).Disjoint (reg (sScr σ) (scrLen p))
  d_gc : (reg (sSig σ) p.sigLen).Disjoint (reg (sScr σ) (scrLen p))
  b_k : (below σ.sp K).Disjoint (reg (sSk σ) L)
  b_m : (below σ.sp K).Disjoint (reg (sMu σ) 64)
  b_r : (below σ.sp K).Disjoint (reg (sRnd σ) 32)
  b_g : (below σ.sp K).Disjoint (reg (sSig σ) p.sigLen)
  b_c : (below σ.sp K).Disjoint (reg (sScr σ) (scrLen p))
  f_k : (sSk σ).toNat + L ≤ 2 ^ 64
  f_m : (sMu σ).toNat + 64 ≤ 2 ^ 64
  f_r : (sRnd σ).toNat + 32 ≤ 2 ^ 64
  f_g : (sSig σ).toNat + p.sigLen ≤ 2 ^ 64
  f_c : (sScr σ).toNat + scrLen p ≤ 2 ^ 64
  x : X σ

theorem epre_sign {p : Params} {k : Nat} {σ : State} (h : (signContract p PPC64LE.abi (k + 1)).pre σ) :
    EPre p p.skLen (k + 1) (fun _ => True) σ := by
  sig_pre [signContract, signSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, trivial⟩

theorem epre_prepared {p : Params} {k : Nat} {σ : State}
    (h : (Proof.MlDsa.preparedSignContract p PPC64LE.abi (k + 1)).pre σ) :
    EPre p (preparedSecretKeyBytes p) (k + 1) (fun σ => PreparedSecretKey p σ.mem (sSk σ)) σ := by
  sig_pre [Proof.MlDsa.preparedSignContract, Proof.MlDsa.preparedSignSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

theorem kpre_to {p : Params} {k : Nat} {σ : State} (h : KPre p (k + 1) σ) :
    (Proof.MlDsa.signWithCacheContract p PPC64LE.abi (k + 1)).pre σ := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, Spec.MlDsa.signSig, PPC64LE.abi,
    PPC64LE.argRegs]
  exact ⟨h.stk, h.rd, h.wr, h.d_kg, h.d_kc, h.d_mg, h.d_mc, h.d_rg, h.d_rc, h.d_gc, h.d_gx, h.d_cx, h.b_k, h.b_m,
    h.b_r, h.b_g, h.b_c, h.b_x, h.f_k, h.f_m, h.f_r, h.f_g, h.f_c, h.f_x, h.polys⟩

/-! ## The call -/

/-- The moves of an entry: `r8 ← r3 + off`, `r9 ← len`. -/
abbrev eMv (off len : Nat) : List Instr := [.addi .r8 .r3 off, .li .r9 len]

/-- The state after them. -/
def eF (off len : Nat) (u : State) : State :=
  (u.write .r8 (u.gpr .r3 + BitVec.ofNat 64 off)).write .r9 (BitVec.ofNat 64 len)

theorem eMv_ok {off len : Nat} (ho : off < 2 ^ 15) (hl : len < 2 ^ 15) (u : State) :
    WP isa (.block (eMv off len)) u (· = eF off len u) :=
  WP.cons (exec_addi (by decide) ho) (WP.cons (exec_li hl) (WP.block_nil rfl))

theorem eF_ok (off len : Nat) : MvOk (eF off len) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun u r hr => by
    have h8 : r ≠ .r8 := fun e => by subst e; simp [preserved] at hr
    have h9 : r ≠ .r9 := fun e => by subst e; simp [preserved] at hr
    simp only [eF, RegUpd.gpr_write_of_ne _ _ h8, RegUpd.gpr_write_of_ne _ _ h9]⟩

section
variable (p : Params) (off len : Nat)

/-- The regions the kernel is given. -/
abbrev rdC (σ : State) : List Region :=
  [reg (sSk σ) p.skLen, reg (sMu σ) 64, reg (sRnd σ) 32, reg (sSk σ + BitVec.ofNat 64 off) len]
abbrev wrC (σ : State) : List Region := [reg (sSig σ) p.sigLen, reg (sScr σ) (scrLen p)]

/-- The state the kernel starts in. -/
abbrev cs (σ : State) : State := (eF off len (eSt σ)).callEntry.withRegions (rdC p off len σ) (wrC p σ)

end

section
variable {p : Params} {off len : Nat}

theorem cs_gpr (σ : State) {r : Reg} (h0 : r ≠ .r0) (h8 : r ≠ .r8) (h9 : r ≠ .r9) (h11 : r ≠ .r11)
    (h12 : r ≠ .r12) : (cs p off len σ).gpr r = σ.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by simp [linkRegs, h0, h11, h12]), eF,
    RegUpd.gpr_write_of_ne _ _ h9, RegUpd.gpr_write_of_ne _ _ h8, eSt_gpr _ h0]

theorem cs_r8 (σ : State) : (cs p off len σ).gpr .r8 = σ.gpr .r3 + BitVec.ofNat 64 off := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), eF, RegUpd.gpr_write_of_ne _ _ (by decide),
    RegUpd.gpr_write_self, eSt_gpr _ (by decide)]

theorem cs_r9 (σ : State) : (cs p off len σ).gpr .r9 = BitVec.ofNat 64 len := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), eF, RegUpd.gpr_write_self]

theorem cs_sp (σ : State) : (cs p off len σ).sp = σ.sp - 48 := rfl

theorem cs_mem (σ : State) : Frame [below σ.sp 48] σ.mem (cs p off len σ).mem := eSt_mem σ

end

section
variable {p : Params} {L K off len : Nat} {X : State → Prop} {σ : State}
  (h : EPre p L (K + 1 + 48) X σ) (hL : p.skLen ≤ L) (hoff : off + len ≤ L) (hlen : len < 2 ^ 64)
  (hO : off < 2 ^ 64)
  (hc : len = 0 ∨ (len = 4 * n * (p.ℓ + 2 * p.k) ∧
    Proof.MlDsa.CachedSecretPolys p σ.mem (sSk σ + BitVec.ofNat 64 off) (skOf p σ)))
include h

theorem EPre.fit : K + 1 + 48 < 2 ^ 64 := by have := h.stk; have := σ.sp.isLt; omega_arith

theorem EPre.b48 : Region.Sub (below σ.sp 48) (below σ.sp (K + 1 + 48)) := below_sub (by omega_using []) h.fit

theorem EPre.bK : Region.Sub (below (σ.sp - 48) (K + 1)) (below σ.sp (K + 1 + 48)) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have := h.fit; have := h.stk
  bv_omega

/-- Bytes apart from the stack are as on entry, for the kernel. -/
theorem EPre.bytes {a : Addr} {l : Nat} (hd : (below σ.sp (K + 1 + 48)).Disjoint (reg a l)) (hl : l ≤ 2 ^ 64) :
    bytesAt (cs p off len σ).mem a l = bytesAt σ.mem a l :=
  Proof.MlKem.bytesAt_frame (cs_mem σ) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact (hd.sub_left h.b48).symm) hl

omit h in
include hL in
theorem EPre.subK : Region.Sub (reg (sSk σ) p.skLen) (reg (sSk σ) L) := by
  have := Offset.sub_base (sSk σ) (d := 0) (n := p.skLen) (k := L) (by omega_using [hL])
  rwa [BitVec.add_zero] at this

omit h in
include hoff in
theorem EPre.subX : Region.Sub (reg (sSk σ + BitVec.ofNat 64 off) len) (reg (sSk σ) L) := Offset.sub_base _ hoff

include hL in
theorem EPre.inputs : skOf p (cs p off len σ) = skOf p σ ∧ muOf (cs p off len σ) = muOf σ ∧
    rndOf (cs p off len σ) = rndOf σ := by
  simp only [skOf, muOf, rndOf, sSk, sMu, sRnd, cs_gpr σ (r := .r3) (by decide) (by decide) (by decide) (by decide)
    (by decide), cs_gpr σ (r := .r4) (by decide) (by decide) (by decide) (by decide) (by decide),
    cs_gpr σ (r := .r5) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact ⟨h.bytes (h.b_k.sub_right (EPre.subK hL)) (by have := h.f_k; simp only [sSk] at this; omega_using [hL, this]),
    h.bytes h.b_m (by decide),
    h.bytes h.b_r (by decide)⟩

include hL hoff hlen hc hO in
/-- The kernel's precondition holds of the state it starts in. -/
theorem cs_kpre : KPre p (K + 1) (cs p off len σ) := by
  have e3 := cs_gpr (p := p) (off := off) (len := len) σ (r := .r3) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have e4 := cs_gpr (p := p) (off := off) (len := len) σ (r := .r4) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have e5 := cs_gpr (p := p) (off := off) (len := len) σ (r := .r5) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have e6 := cs_gpr (p := p) (off := off) (len := len) σ (r := .r6) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have e7 := cs_gpr (p := p) (off := off) (len := len) σ (r := .r7) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have e9 : ((cs p off len σ).gpr .r9).toNat = len := by
    rw [cs_r9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  have sK : Region.Sub (reg (sSk σ) p.skLen) (reg (sSk σ) L) := EPre.subK hL
  have sX : Region.Sub (reg (sSk σ + BitVec.ofNat 64 off) len) (reg (sSk σ) L) := EPre.subX hoff
  have fk := h.f_k
  simp only [sSk] at fk
  have bK := h.bK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sSk, sMu, sRnd, sSig, sScr, e3, e4, e5, e6, e7, e9, cs_r8, cs_sp] at *
  · have := h.stk; have := h.fit; bv_omega
  · rfl
  · rfl
  · exact h.d_kg.sub_left sK
  · exact h.d_kc.sub_left sK
  · exact h.d_mg
  · exact h.d_mc
  · exact h.d_rg
  · exact h.d_rc
  · exact h.d_gc
  · exact (h.d_kg.sub_left sX).symm
  · exact (h.d_kc.sub_left sX).symm
  · exact (h.b_k.sub_left bK).sub_right sK
  · exact h.b_m.sub_left bK
  · exact h.b_r.sub_left bK
  · exact h.b_g.sub_left bK
  · exact h.b_c.sub_left bK
  · exact (h.b_k.sub_left bK).sub_right sX
  · omega_using [hL, fk]
  · exact h.f_m
  · exact h.f_r
  · exact h.f_g
  · exact h.f_c
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hO]
    exact Nat.le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) (by omega_using [hoff, fk])
  · rw [cs_r9]
    rcases hc with h0 | ⟨hl, hcc⟩
    · subst h0; exact .inl rfl
    · refine .inr ⟨hl, fun i hi => ?_⟩
      rw [(h.inputs hL).1]
      have hsub : Region.Sub (Proof.MlDsa.Verify.polyRegion (σ.gpr .r3 + BitVec.ofNat 64 off +
          BitVec.ofNat 64 (4 * n * i))) (reg (σ.gpr .r3 + BitVec.ofNat 64 off) len) :=
        Offset.sub_base _ (by rw [hl]; show 4 * 256 * i + 1024 ≤ 4 * 256 * (p.ℓ + 2 * p.k); omega_using [hi])
      exact Proof.MlDsa.Verify.polyIs_frame (cs_mem σ) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ((h.b_k.sub_left h.b48).sub_right sX).symm.sub_left hsub) (hcc i hi)

end

/-! ## The entries -/

section
variable {p : Params} {L K off len : Nat} {X : State → Prop} {name : String} {code : Prog isa}
  (hv : Verified PPC64LE.target code (Proof.MlDsa.signWithCacheContract p PPC64LE.abi (K + 1)))
  (hd : sdepth code ≤ K + 1) (hK : K + 1 + 48 < 2 ^ 64) (hL : p.skLen ≤ L) (hoff : off + len ≤ L) (ho : off < 2 ^ 15) (hl : len < 2 ^ 15)
  (hc : ∀ σ, EPre p L (K + 1 + 48) X σ → len = 0 ∨ (len = 4 * n * (p.ℓ + 2 * p.k) ∧
    Proof.MlDsa.CachedSecretPolys p σ.mem (sSk σ + BitVec.ofNat 64 off) (skOf p σ)))
include hv hd hK hL hoff ho hl hc

omit hv hd hK hL hoff ho hl hc in
theorem EPre.hd96 {σ : State} (h : EPre p L (K + 1 + 48) X σ) :
    ∀ R ∈ σ.wr, Region.Disjoint ⟨σ.sp - 48 + 32, 16⟩ R := fun R hR => by
  have hs : Region.Sub ⟨σ.sp - 48 + 32, 16⟩ (below σ.sp (K + 1 + 48)) := by
    intro x hx
    simp only [Region.Contains] at hx ⊢
    have := h.fit; have := h.stk
    bv_omega
  rw [h.wr] at hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl
  · exact h.b_g.sub_left hs
  · exact h.b_c.sub_left hs

omit hv hd hK ho hl hc in
theorem EPre.covers {σ : State} (h : EPre p L (K + 1 + 48) X σ) :
    Covers (rdC p off len σ ++ wrC p σ) (σ.rd ++ σ.wr) ∧ Covers (wrC p σ) σ.wr := by
  rw [h.rd, h.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨reg (sSk σ) L, by simp, 0, by simp, by simpa using hL⟩
    · exact ⟨reg (sMu σ) 64, by simp, 0, by simp, by simp⟩
    · exact ⟨reg (sRnd σ) 32, by simp, 0, by simp, by simp⟩
    · exact ⟨reg (sSk σ) L, by simp, off, rfl, hoff⟩
    · exact ⟨reg (sSig σ) p.sigLen, by simp, 0, by simp, by simp⟩
    · exact ⟨reg (sScr σ) (scrLen p), by simp, 0, by simp, by simp⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨reg (sSig σ) p.sigLen, by simp, 0, by simp, by simp⟩
    · exact ⟨reg (sScr σ) (scrLen p), by simp, 0, by simp, by simp⟩

/-- An entry: the kernel's result and signature, from the inputs our caller gave. -/
theorem entryS_wp {σ : State} (h : EPre p L (K + 1 + 48) X σ) :
    WP isa (entryCode (eMv off len) name code) σ fun s' => PPC64LE.target.abiPreserved σ s' ∧
      Outcome (fun b => signMu p b (skOf p σ) (muOf σ) (rndOf σ)) ((s'.gpr .r3).setWidth 32)
        (bytesAt s'.mem (sSig σ) p.sigLen) := by
  obtain ⟨cv, cw⟩ := h.covers hL hoff
  refine entry_wp (name := name) (F := eF off len) (R := fun m r => Outcome (fun b => signMu p b (skOf p σ) (muOf σ)
    (rndOf σ)) (r.setWidth 32) (bytesAt m (sSig σ) p.sigLen)) hv.1 (by omega_using [hd, hK]) (eMv_ok ho hl) (eF_ok off len)
    (by have := h.stk; omega_using [this]) h.hd96
    (kpre_to (cs_kpre h hL hoff (by omega_using [hl]) (by omega_using [ho]) (hc σ h))) cv cw (fun s' hq => ?_)
    fun m m' _ fl hR => by
      -- The pop loses the frame's bytes, which lie apart from the signature.
      obtain hs : Region.Sub (below σ.sp 48) (below σ.sp (K + 1 + 48)) := below_sub (by omega_using []) h.fit
      have e : bytesAt m' (sSig σ) p.sigLen = bytesAt m (sSig σ) p.sigLen := List.map_congr_left fun i hi =>
        lost_byte fl (R := reg (sSig σ) p.sigLen) (h.b_g.sub_left hs).symm (List.mem_range.mp hi)
      rw [e]; exact hR
  have q := hq
  generalize hτ : cs p off len σ = τ at q
  sig_post [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, Spec.MlDsa.signSig, PPC64LE.abi,
    PPC64LE.argRegs] at q
  subst hτ
  obtain ⟨k₁, m₁, r₁⟩ := h.inputs (off := off) (len := len) hL
  have e6 := cs_gpr (p := p) (off := off) (len := len) σ (r := .r6) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have e : (fun b => signMu p b (skOf p σ) (muOf σ) (rndOf σ)) = (fun b => signMu p b (skOf p (cs p off len σ))
      (muOf (cs p off len σ)) (rndOf (cs p off len σ))) := by rw [k₁, m₁, r₁]
  show Outcome _ _ (bytesAt s'.mem (σ.gpr .r6) p.sigLen)
  rw [e, ← e6]
  exact q

/-- Two runs of an entry leak the same if their entry states agree on the
inputs' leakage, the pointers and the stack pointer. -/
theorem entryS_tr {P : State → State → Prop}
    (hP : ∀ x y, P x y → EPre p L (K + 1 + 48) X x ∧ EPre p L (K + 1 + 48) X y ∧ x.sp = y.sp ∧
      (∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], x.gpr r = y.gpr r) ∧
      signLeak p (skOf p x) (muOf x) (rndOf x) = signLeak p (skOf p y) (muOf y) (rndOf y)) :
    RelCT isa P (entryCode (eMv off len) name code) fun _ _ => True := by
  refine entry_tr (name := name) (F := eF off len) (rd := rdC p off len) (wr := wrC p) hv.1 (by omega_using [hd, hK]) (eMv_ok ho hl) (eF_ok off len)
    hv.2.1 rfl (fun x y h => (hP x y h).2.2.1) (fun x ⟨y, hxy⟩ => ?_) (fun x y hxy => ?_)
  · have hx : EPre p L (K + 1 + 48) X x := by
      rcases hxy with h | h
      exacts [(hP x y h).1, (hP y x h).2.1]
    obtain ⟨cv, cw⟩ := hx.covers hL hoff
    exact ⟨by have := hx.stk; omega_using [this], hx.hd96,
      kpre_to (cs_kpre hx hL hoff (by omega_using [hl]) (by omega_using [ho]) (hc x hx)), cv, cw⟩
  · obtain ⟨hx, hy, hsp, hreg, hlk⟩ := hP x y hxy
    have g : ∀ {r : Reg}, r ∈ [Reg.r3, .r4, .r5, .r6, .r7] →
        (cs p off len x).gpr r = (cs p off len y).gpr r := fun {r} hr => by
      have : r ≠ .r0 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r11 ∧ r ≠ .r12 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [cs_gpr x this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2,
        cs_gpr y this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, hreg r hr]
    obtain ⟨k₁, m₁, r₁⟩ := hx.inputs (off := off) (len := len) hL
    obtain ⟨k₂, m₂, r₂⟩ := hy.inputs (off := off) (len := len) hL
    have e8 : (cs p off len x).gpr .r8 = (cs p off len y).gpr .r8 := by rw [cs_r8, cs_r8, hreg .r3 (by simp)]
    have e9 : (cs p off len x).gpr .r9 = (cs p off len y).gpr .r9 := by rw [cs_r9, cs_r9]
    have esp : (cs p off len x).sp = (cs p off len y).sp := by rw [cs_sp, cs_sp, hsp]
    have elk : signLeak p (skOf p (cs p off len x)) (muOf (cs p off len x)) (rndOf (cs p off len x)) =
        signLeak p (skOf p (cs p off len y)) (muOf (cs p off len y)) (rndOf (cs p off len y)) := by
      rw [k₁, m₁, r₁, k₂, m₂, r₂]; exact hlk
    have g3 := g (r := .r3) (by simp)
    have g4 := g (r := .r4) (by simp)
    have g5 := g (r := .r5) (by simp)
    have g6 := g (r := .r6) (by simp)
    have g7 := g (r := .r7) (by simp)
    show (Proof.MlDsa.signWithCacheContract p PPC64LE.abi (K + 1)).pub (cs p off len x) (cs p off len y)
    generalize cs p off len x = X' at *
    generalize cs p off len y = Y' at *
    sig_pub [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, Spec.MlDsa.signSig, PPC64LE.abi,
      PPC64LE.argRegs]
    exact ⟨esp, elk, g3, g4, g5, g6, g7, e8, e9⟩

end

/-! ## `vg_mldsa*_sign` and `vg_mldsa*_sign_prepared` -/

/-- A state that satisfies `signContract`'s precondition, for the contract's satisfiability. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x8000 | .r5 => 0x9000 | .r6 => 0xA000 | .r7 => 0x10000 | _ => 0
  lr := 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x8000, 64⟩, ⟨0x9000, 32⟩]
  wr := [⟨0xA000, p.sigLen⟩, ⟨0x10000, scrLen p⟩]

section
variable {p : Params} {K : Nat} {name : String} {code : Prog isa}
  (hv : Verified PPC64LE.target code (Proof.MlDsa.signWithCacheContract p PPC64LE.abi (K + 1)))
  (hd : sdepth code ≤ K + 1) (hK : K + 1 + 48 < 2 ^ 64)
include hv hd hK

/-- `vg_mldsa*_sign`: the kernel with no cache. -/
theorem sign_entry_verified (hsat : ∃ s, (signContract p PPC64LE.abi (K + 1 + 48)).pre s) :
    Verified PPC64LE.target (entry name code p false) (signContract p PPC64LE.abi (K + 1 + 48)) := by
  have hE (σ : State) (h : (signContract p PPC64LE.abi (K + 1 + 48)).pre σ) :
      EPre p p.skLen (K + 1 + 48) (fun _ => True) σ := epre_sign (k := K + 48) h
  refine ⟨fun σ hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · refine WP.mono (entryS_wp (name := name) hv hd hK (Nat.le_refl _) (off := 0) (len := 0) (by omega_using []) (by decide)
      (by decide) (fun _ _ => .inl rfl) (hE σ hs)) fun s' ⟨ha, hq⟩ => ⟨ha, ?_⟩
    sig_post [signContract, signSig, PPC64LE.abi, PPC64LE.argRegs]
    exact hq
  · refine (entryS_tr (name := name) (X := fun _ => True) hv hd hK (Nat.le_refl _) (off := 0) (len := 0) (by omega_using [])
      (by decide) (by decide) (fun _ _ => .inl rfl) (P := fun x y => (signContract p PPC64LE.abi (K + 1 + 48)).pre x ∧
        (signContract p PPC64LE.abi (K + 1 + 48)).pre y ∧ (signContract p PPC64LE.abi (K + 1 + 48)).pub x y)
      (fun x y ⟨a, b, c⟩ => ?_) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hpub⟩ e₁ e₂).1
    sig_pub [signContract, signSig, PPC64LE.abi, PPC64LE.argRegs] at c
    obtain ⟨hsp, hl, h3, h4, h5, h6, h7⟩ := c
    refine ⟨hE x a, hE y b, hsp, fun r hr => ?_, hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h3, h4, h5, h6, h7]

omit hv hd hK in
/-- The polynomials a prepared private key holds after its encoded key, as a cache. -/
theorem prepared_cache {m : Mem} {key : Addr} (h : PreparedSecretKey p m key) :
    Proof.MlDsa.CachedSecretPolys p m (key + BitVec.ofNat 64 p.skLen) (bytesAt m key p.skLen) := fun i hi => by
  have := Proof.MlDsa.polyStored_iff.mp (h i hi)
  rwa [BitVec.ofNat_add, ← BitVec.add_assoc] at this

/-- `vg_mldsa*_sign_prepared`: the kernel with the polynomials of a prepared private key. -/
theorem prepared_entry_verified (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    (hsat : ∃ s, (Proof.MlDsa.preparedSignContract p PPC64LE.abi (K + 1 + 48)).pre s) :
    Verified PPC64LE.target (entry name code p true)
      (Proof.MlDsa.preparedSignContract p PPC64LE.abi (K + 1 + 48)) := by
  have hE (σ : State) (h : (Proof.MlDsa.preparedSignContract p PPC64LE.abi (K + 1 + 48)).pre σ) :
      EPre p (preparedSecretKeyBytes p) (K + 1 + 48) (fun σ => PreparedSecretKey p σ.mem (sSk σ)) σ :=
    epre_prepared (k := K + 48) h
  have hL : p.skLen ≤ preparedSecretKeyBytes p := by simp only [preparedSecretKeyBytes]; omega_using []
  have hoff : p.skLen + 1024 * (p.ℓ + 2 * p.k) ≤ preparedSecretKeyBytes p := by
    simp only [preparedSecretKeyBytes]; show _ ≤ _ + 4 * 256 * _; omega_using []
  have ho : p.skLen < 2 ^ 15 := by rcases hp3 with rfl | rfl | rfl <;> decide
  have hl : 1024 * (p.ℓ + 2 * p.k) < 2 ^ 15 := by rcases hp3 with rfl | rfl | rfl <;> decide
  have hc : ∀ σ, EPre p (preparedSecretKeyBytes p) (K + 1 + 48) (fun σ => PreparedSecretKey p σ.mem (sSk σ)) σ →
      1024 * (p.ℓ + 2 * p.k) = 0 ∨ (1024 * (p.ℓ + 2 * p.k) = 4 * n * (p.ℓ + 2 * p.k) ∧
        Proof.MlDsa.CachedSecretPolys p σ.mem (sSk σ + BitVec.ofNat 64 p.skLen) (skOf p σ)) :=
    fun σ h => .inr ⟨by show _ = 4 * 256 * _; omega_using [], prepared_cache h.x⟩
  refine ⟨fun σ hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · refine WP.mono (entryS_wp (name := name) hv hd hK hL hoff ho hl hc (hE σ hs)) fun s' ⟨ha, hq⟩ => ⟨ha, ?_⟩
    sig_post [Proof.MlDsa.preparedSignContract, Proof.MlDsa.preparedSignSig, PPC64LE.abi, PPC64LE.argRegs]
    exact hq
  · refine (entryS_tr (name := name) hv hd hK hL hoff ho hl hc
      (P := fun x y => (Proof.MlDsa.preparedSignContract p PPC64LE.abi (K + 1 + 48)).pre x ∧
        (Proof.MlDsa.preparedSignContract p PPC64LE.abi (K + 1 + 48)).pre y ∧
        (Proof.MlDsa.preparedSignContract p PPC64LE.abi (K + 1 + 48)).pub x y)
      (fun x y ⟨a, b, c⟩ => ?_) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hpub⟩ e₁ e₂).1
    sig_pub [Proof.MlDsa.preparedSignContract, Proof.MlDsa.preparedSignSig, PPC64LE.abi, PPC64LE.argRegs] at c
    obtain ⟨hsp, hl, h3, h4, h5, h6, h7⟩ := c
    refine ⟨hE x a, hE y b, hsp, fun r hr => ?_, hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h3, h4, h5, h6, h7]

end

end VG.Proof.MlDsa.PPC64LE.Sign
