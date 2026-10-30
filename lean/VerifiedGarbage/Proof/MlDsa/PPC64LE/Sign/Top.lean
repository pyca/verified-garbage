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
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relStart relInv)
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

/-! ## Two runs -/

omit hP hF hS hp in
/-- Two runs whose `ExpandA` finished agree on what their loops leak. -/
theorem pub_leq {σ₁ σ₂ : State} (hpub : sPub p σ₁ σ₂)
    (hA₁ : expandA p maxBounds (rhoOf p σ₁) = some (amat p (Am p σ₁)))
    (hA₂ : expandA p maxBounds (rhoOf p σ₂) = some (amat p (Am p σ₂))) : LeakEq p 0 σ₁ σ₂ := by
  have e := Proof.MlDsa.Sign.signLeakT_congr p
    (by simp only [skOf, VG.Spec.Sha3.bytesAt, List.length_map, List.length_range]) hpub.2.2.2.2.2.2
  rw [Proof.MlDsa.Sign.signLeakT_eq hA₁, Proof.MlDsa.Sign.signLeakT_eq hA₂, pub_rho hpub] at e
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
    RelCT isa (Rel2 (SPre p STK) (sPub p) (IM p STK)) (rest P p)
      fun x y => Rel2 (SPre p STK) (sPub p) (SC2 p STK) x y := by
  unfold rest
  refine RelCT.mono (P := RS p STK (LeakEq p 0) (IM p STK)) ?_
    (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub,
      pub_leq pub (expandA_max h₁.ok) (expandA_max h₂.ok), h₁, h₂⟩) fun _ _ h => h
  refine RelCT.seq (pieceRS (decode_piece hP hF hS)) (RelCT.seq ?_ (outIf_tr hP hF hS))
  exact RelCT.mono (signLoop_tr hP hF hS hp) (fun x y h => h.mono fun _ _ h => h.ik) fun _ _ h => h

/-- Two runs whose entry states agree on the public data leak the same. -/
theorem sign_tr (h48 : 48 ≤ STK) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) fun σ s => s = σ) (sign P p) fun _ _ => True := by
  unfold sign
  refine RelCT.seq (relInv (spro_piece hF h48).ok (spro_piece hF h48).tr) ?_
  refine RelCT.seq (RelCT.mono (expandA_tr hP hF hS) (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (Q := fun _ _ => True) (R := fun x y => Rel2 (SPre p STK) (sPub p) (SC1 p STK) x y ∨
      Rel2 (SPre p STK) (sPub p) (SC2 p STK) x y) ?_
    (relOr (srel1 (fun _ _ h => h) (by taint_decide)) (srel2 (fun _ _ h => h) (by taint_decide)))
  unfold ifOk ifOkElse
  refine RelCT.ite (fun x y ⟨_, e⟩ => by rw [eval_nonzero, eval_nonzero, e]) ?_ ?_
  · refine RelCT.mono (rest_tr hP hF hS hp) (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, e⟩, hb⟩ => ?_)
      fun _ _ h => .inr h
    have hx := r24_one h₁.r01 (by rw [eval_nonzero] at hb; simpa using hb)
    exact ⟨σ₁, σ₂, p₁, p₂, pub, h₁.im hx, h₂.im (r24_one h₂.r01 (by rw [← e, hx]; decide))⟩
  · exact relct_nil fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, _⟩, _⟩ => .inl ⟨σ₁, σ₂, p₁, p₂, pub, h₁.sc, h₂.sc⟩
end

/-! ## The contract -/

/-- A state that satisfies `signContract`'s precondition, for the contract's satisfiability. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x8000 | .r5 => 0x9000 | .r6 => 0xA000 | .r7 => 0x10000 | _ => 0
  lr := 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x8000, 64⟩, ⟨0x9000, 32⟩]
  wr := [⟨0xA000, p.sigLen⟩, ⟨0x10000, scrLen p⟩]

/-- `vg_mldsa*_sign` of the parameter set `p` meets its contract with `S`
bytes of stack, for any verified implementations `P` of the primitives it
calls with at most `S` bytes of stack whose samplers' results are public
(`SPrimsOk`), and `S` at least the 48 bytes the sponge needs. The contract's
satisfiability (`hsat`, by `signSat`) is evaluated once `S` is known. -/
theorem sign_verified {P : Prims} {S : Nat} (hP : SPrimsOk P S) (h48 : 48 ≤ S)
    (p : Spec.MlDsa.Params) (hp3 : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hsat : (Spec.MlDsa.signContract p PPC64LE.abi S).pre (signSat p)) :
    Verified PPC64LE.target (sign P p) (Spec.MlDsa.signContract p PPC64LE.abi S) := by
  have hF := sfacts hp3
  have hp : ParamsOk p := by rcases hp3 with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  obtain ⟨n, rfl⟩ : ∃ n, S = n + 1 := ⟨S - 1, by omega⟩
  refine ⟨fun s hs => sign_ok hP hF (Nat.le_refl _) hp (spre_of hs) h48,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨signSat p, hsat⟩⟩
  sig_pub [Spec.MlDsa.signContract, Spec.MlDsa.signSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7⟩ := hpub
  exact relStart (sign_tr hP hF (Nat.le_refl _) hp h48) s₁ s₂ t₁ t₂ s₁' s₂' (spre_of h₁) (spre_of h₂)
    ⟨hsp, h3, h4, h5, h6, h7, hl⟩ e₁ e₂

end VG.Proof.MlDsa.PPC64LE.Sign
