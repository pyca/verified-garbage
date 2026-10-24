module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Output
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlDsa.Sign.Loop
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
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
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relStart)
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

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
  (hp : ParamsOk p)
include hP hF hS hp

theorem rest_ok {σ : State} (hpre : SPre p STK σ) {s : State} (h : IM p STK σ s) :
    WP isa (rest P p) s (FS p STK σ) := by
  have hA := expandA_max h.ok
  unfold rest
  refine WP.seq (WP.mono ((decode_piece hP hF hS).ok σ s hpre h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (signLoop_ok hP hF hS hp hpre h1.ik) fun s2 h2 => ?_)
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


theorem sign_ok {σ : State} (hpre : SPre p STK σ) (h48 : 48 ≤ STK) :
    WP isa (sign P p) σ fun s' =>
      PPC64LE.target.abiPreserved σ s' ∧ (Spec.MlDsa.signContract p PPC64LE.abi STK).post σ s' := by
  unfold sign
  refine WP.seq (WP.mono (spro_ok hF h48 hpre) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (expandA_ok hP hF hS h₁.1 h₁.2) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (show WP isa (ifOk (rest P p)) s₂ (FS p STK σ) from ?_) fun s₄ h₄ => ?_)
  · unfold ifOk ifOkElse
    refine WP.ite _ (eval_nonzero s₂ .r24) (fun hb => ?_) fun hb => WP.block_nil ?_
    · exact rest_ok hP hF hS hp hpre (h₂.im (r24_one h₂.r01 (by simpa using hb)))
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
end

end VG.Proof.MlDsa.PPC64LE.Sign
