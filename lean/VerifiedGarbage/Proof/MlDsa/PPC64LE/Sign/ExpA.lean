module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Control
public import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlDsa.KeyGen.Masked
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Control
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA signing on PPC64LE: `Â`

As on 32-bit ARM (`Proof/MlDsa/Arm/Sign/PhaseA.lean`): `ρ` to the seed `RS`,
then each entry `e` of `Â`: its two bytes to the seed, `RejNTTPoly` to its
slot, and its result ANDed into `r24` (`IA`: after `e` entries, either every
sampling so far finished within `maxBounds` and the slots hold the entries,
or one did not finish within `minBounds`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv taint31
  Regs2 Callee polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW setB_ok copyS zx zx_01 and24_ok)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Impl.MlDsa.PPC64LE.KeyGen (and24 setB seqR callAt)
open VG.Impl.MlKem.PPC64LE (copy)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (aSeed aF rejNTTPoly_mono)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `ρ`. -/
abbrev rhoOf (σ : State) : List Byte := (skOf p σ).take 32

/-- The seed of entry `e`. -/
abbrev seedE (σ : State) (e : Nat) : List Byte := aSeed (rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

/-- Entry `e` of `Â`, within `maxBounds`. -/
abbrev aVal (σ : State) (e : Nat) : Poly := aF maxBounds.rejNTT (rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

end

theorem aP_eq (p : Params) (e : Nat) : aP p (e / p.ℓ) (e % p.ℓ) = pS (aBase p + e) := by
  show sc (oP (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * (e / p.ℓ) + e % p.ℓ)) = sc (oP (5 + 4 * p.k + 3 * p.ℓ + e))
  rw [Nat.add_assoc _ (p.ℓ * _), Nat.div_add_mod]

/-- `ExpandA` after `e` entries. -/
structure IA (p : Params) (STK : Nat) (σ : State) (e : Nat) (s : State) : Prop where
  sc : SC1 p STK σ s
  rs : bytesAt s.mem ((slay1 p STK σ).A 0 oRS) 32 = rhoOf p σ
  r01 : s.gpr .r24 = 0 ∨ s.gpr .r24 = 1
  ok : s.gpr .r24 = 1 → (∀ e' < e, (rejNTTPoly maxBounds.rejNTT (seedE p σ e')).isSome) ∧
    ∀ e' < e, PolyIs s.mem ((slay1 p STK σ).A 0 (oP (aBase p + e'))) (aVal p σ e')
  bad : s.gpr .r24 = 0 → ∃ e' < e, rejNTTPoly minBounds.rejNTT (seedE p σ e') = none

/-- The result of `vg_mldsa_rej_ntt_poly`, if it succeeded within `maxBounds`. -/
theorem rej_val {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => rejNTTPoly b.rejNTT x) r out) (h1 : r = 1)
    (hm : (rejNTTPoly maxBounds.rejNTT x).isSome) : out = (rejNTTPoly maxBounds.rejNTT x).getD zero := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    have e1 := rejNTTPoly_mono (Nat.le_max_left b.rejNTT maxBounds.rejNTT) hb
    have e2 := rejNTTPoly_mono (Nat.le_max_right b.rejNTT maxBounds.rejNTT) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem integerToBytes_one {x : Nat} : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]

theorem aSeed_eq (ρ : List Byte) (i j : Nat) : aSeed ρ i j = ρ ++ [BitVec.ofNat 8 j, BitVec.ofNat 8 i] := by
  simp only [aSeed, integerToBytes_one, List.append_assoc]; rfl

theorem and24_01 {a x : BitVec 64} (ha : a = 0 ∨ a = 1) (hx : x.setWidth 32 = 0 ∨ x.setWidth 32 = 1) :
    (a &&& zx x = 0 ∨ a &&& zx x = 1) ∧ (a &&& zx x = 1 ↔ a = 1 ∧ x.setWidth 32 = 1) := by
  rcases ha with rfl | rfl <;> rcases hx with h | h <;> simp only [zx, h] <;> decide

/-- `r24` is the same in two runs. -/
abbrev E24 (x y : State) : Prop := x.gpr .r24 = y.gpr .r24

theorem wp_seqR {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => by rw [seqR, Nat.add_zero]; exact WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega]
    exact WP.seq (WP.mono (h a (Nat.le_refl _) (by omega) s hs) fun s' hs' =>
      wp_seqR n (a + 1) (fun k h₁ h₂ => h k (by omega) (by omega)) s' hs')

theorem rr_seqR {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (seqR f a n) (R (a + n))
  | 0, a, _ => by
    rw [seqR, Nat.add_zero]
    intro _ _ _ _ _ _ hr e₁ e₂
    rw [Exec.block_iff] at e₁ e₂
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    obtain ⟨rfl, rfl⟩ := e₁
    obtain ⟨rfl, rfl⟩ := e₂
    exact ⟨rfl, hr⟩
  | n + 1, a, h => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega)) (rr_seqR n (a + 1) fun k h₁ h₂ => h k (by omega) (by omega))

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem rnE_m {σ : State} {e : Nat} (he : e < p.k * p.ℓ) :
    KeyGen.RnOk (slay1 p STK σ) sWb1 (sc oRS) (pS (aBase p + e)) (sc oPS) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨⟨sptr_ok rfl (by decide), by ssep hF⟩, ⟨sptr_ok rfl (by slt hF), by ssep hF⟩,
    ⟨sptr_ok rfl (by decide), by ssep hF⟩, show ix Reg.r31 ∈ sWb1 by decide, show ix Reg.r31 ∈ sWb1 by decide,
    by ssep hF, by ssep hF, by ssep hF⟩

/-- The two bytes of the seed of entry `e`. -/
abbrev blkE (p : Params) (e : Nat) : List Instr := setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ)

omit hP hS in
theorem blkE_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (h : IA p STK σ e s) :
    WP isa (.block (blkE p e)) s fun s' =>
      (IA p STK σ e s' ∧ bytesAt s'.mem ((slay1 p STK σ).A 0 oRS) 34 = seedE p σ e) ∧ s'.gpr .r24 = s.gpr .r24 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hs := h.sc.site
  have hL := hs.ok
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  refine WP.block_append (WP.mono (setB_ok hs (q := sc (oRS + 32)) ⟨sptr_ok rfl (by decide), by ssep hF⟩
    (by decide) (by decide) (v := e % p.ℓ) (by omega)) fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁)
      (q := sc (oRS + 33)) ⟨sptr_ok rfl (by decide), by ssep hF⟩ (by decide) (by decide) (v := e / p.ℓ) (by omega))
      fun s₂ ⟨k₂, b₂⟩ => ?_)
  have sc₂ := (h.sc.keep k₁ (by ssep hF [sc1Chk])).keep k₂ (by ssep hF [sc1Chk])
  have rs₂ : bytesAt s₂.mem ((slay1 p STK σ).A 0 oRS) 32 = rhoOf p σ :=
    (bytes_keepW hL k₂.frame (i := 0) (o := oRS) (l := 32) (by ssep hF) (by decide) (by decide)).trans
      ((bytes_keepW hL k₁.frame (i := 0) (o := oRS) (l := 32) (by ssep hF) (by decide) (by decide)).trans h.rs)
  have h24₂ : s₂.gpr .r24 = s.gpr .r24 := by rw [k₂.cs .r24 (by decide), k₁.cs .r24 (by decide)]
  refine ⟨⟨⟨sc₂, rs₂, by rw [h24₂]; exact h.r01, fun h1 => ?_, fun h0 => h.bad (by rw [← h24₂]; exact h0)⟩, ?_⟩, h24₂⟩
  · obtain ⟨ok1, fam⟩ := h.ok (by rw [← h24₂]; exact h1)
    exact ⟨ok1, fun e' he' => polyIs_keepW hL k₂.frame (by ssep hF) (by decide) rfl
      (polyIs_keepW hL k₁.frame (by ssep hF) (by decide) rfl (fam e' he'))⟩
  · have b₁' := bytes_keepW hL k₂.frame (i := 0) (o := oRS + 32) (l := 1) (by ssep hF) (by decide) (by decide)
    rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, rs₂, seedE,
      aSeed_eq, List.append_assoc]
    refine congrArg _ ?_
    have e1 : bytesAt s₂.mem ((slay1 p STK σ).A 0 (oRS + 32)) 1 = [BitVec.ofNat 8 (e % p.ℓ)] := b₁'.trans b₁
    have e2 : bytesAt s₂.mem ((slay1 p STK σ).A 0 (oRS + 33)) 1 = [BitVec.ofNat 8 (e / p.ℓ)] := b₂
    simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add] at e1 e2 ⊢
    rw [e1, e2]; rfl

/-- Entry `e`'s call is done. -/
def JE (p : Params) (STK : Nat) (e : Nat) (σ s : State) : Prop :=
  ∃ s₀, IA p STK σ e s₀ ∧
    Kept ((slay1 p STK σ).RL [tri (pS (aBase p + e)) 1024, tri (sc oPS) 2048, (1, 0, STK)]) s₀ s ∧
    ((s.gpr .r3).setWidth 32 = 1 → Reduced s.mem ((slay1 p STK σ).A 0 (oP (aBase p + e)))) ∧
    Outcome (fun b => rejNTTPoly b.rejNTT (seedE p σ e)) ((s.gpr .r3).setWidth 32)
      (polyAt s.mem ((slay1 p STK σ).A 0 (oP (aBase p + e)))) ∧
    ((s.gpr .r3).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome)

theorem callE_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (h : IA p STK σ e s)
    (hs : bytesAt s.mem ((slay1 p STK σ).A 0 oRS) 34 = seedE p σ e) :
    WP isa (callAt "vg_mldsa_rej_ntt_poly" P.rejNTT (KeyGen.rnArgs (sc oRS) (pS (aBase p + e)) (sc oPS))) s
      fun s' => JE p STK e σ s' ∧ s'.gpr .r24 = s.gpr .r24 :=
  rn_okX hP h.sc.site hS (rnE_m hF he) fun s' k' hred hout hmax =>
    ⟨⟨s, h, k', hred, by rw [← hs]; exact hout, by rw [← hs]; exact hmax⟩, k'.cs .r24 (by decide)⟩

omit hP hS in
theorem andE_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (h : JE p STK e σ s) :
    WP isa (.block and24) s (IA p STK σ (e + 1)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  obtain ⟨s₃₀, h, k₃, hred, hout, hmax⟩ := h
  have hL := h.sc.site.ok
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  have sc₃ := h.sc.keep k₃ (by ssep hF [sc1Chk])
  have h24₃ : s.gpr .r24 = s₃₀.gpr .r24 := k₃.cs .r24 (by decide)
  refine WP.mono (and24_ok s) fun s₄ ⟨_, e24, r₄⟩ => ?_
  obtain ⟨a01, aeq⟩ := and24_01 (a := s.gpr .r24) (by rw [h24₃]; exact h.r01) hr01
  rw [h24₃] at a01 aeq
  refine ⟨sc₃.regs2 r₄, ?_, by rw [e24, h24₃]; exact a01, fun h1 => ?_, fun h0 => ?_⟩
  · rw [r₄.mem]
    exact (bytes_keepW hL k₃.frame (i := 0) (o := oRS) (l := 32) (by ssep hF) (by decide) (by decide)).trans h.rs
  · rw [e24, h24₃] at h1
    obtain ⟨hs1, hr1⟩ := aeq.mp h1
    obtain ⟨ok1, fam⟩ := h.ok hs1
    have hm := hmax hr1
    refine ⟨fun e' he' => ?_, fun e' he' => ?_⟩
    · rcases (by omega : e' < e ∨ e' = e) with he' | rfl
      exacts [ok1 e' he', hm]
    · rw [r₄.mem]
      rcases (by omega : e' < e ∨ e' = e) with he' | rfl
      · exact polyIs_keepW hL k₃.frame (by ssep hF) (by decide) rfl (fam e' he')
      · exact ⟨hred hr1, rej_val hout hr1 hm⟩
  · rw [e24, h24₃] at h0
    rcases h.r01 with e0 | e0
    · obtain ⟨e', he', hn⟩ := h.bad e0
      exact ⟨e', by omega, hn⟩
    · rcases hr01 with e1 | e1
      · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
        · rw [e1] at h1; cases h1
        · exact ⟨e, by omega, hn⟩
      · rw [e0] at h0; simp only [zx, e1] at h0; exact absurd h0 (by decide)

omit hP hF hS in
theorem sampleE_eq (e : Nat) : sampleE P p e = .seq (.block (blkE p e))
    (.seq (callAt "vg_mldsa_rej_ntt_poly" P.rejNTT (KeyGen.rnArgs (sc oRS) (pS (aBase p + e)) (sc oPS)))
      (.block and24)) := by
  unfold sampleE rejAt; rw [aP_eq]

theorem sampleE_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (h : IA p STK σ e s) :
    WP isa (sampleE P p e) s (IA p STK σ (e + 1)) := by
  rw [sampleE_eq]
  exact WP.seq (WP.mono (blkE_ok hF he h) fun s1 ⟨⟨h1, hs1⟩, _⟩ =>
    WP.seq (WP.mono (callE_ok hP hF hS he h1 hs1) fun s2 ⟨h2, _⟩ => andE_ok hF he h2))


/-! ## `ExpandA` -/

omit hP hS in
theorem sk_rho {σ s : State} (h : SC1 p STK σ s) : bytesAt s.mem ((slay1 p STK σ).A 2 0) 32 = rhoOf p σ := by
  have := hF.sk
  rw [rhoOf, ← h.sk, Proof.MlKem.bytesAt_take _ _ (by omega)]

omit hP hS in
theorem rho_ok {σ s : State} (h : SC1 p STK σ s) (h1 : s.gpr .r24 = 1) :
    WP isa (copy .r30 0 .r31 oRS 32) s fun s' => IA p STK σ 0 s' ∧ s'.gpr .r24 = 1 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine WP.mono (copyS h.site (sb := .r30) (so := 0) (db := .r31) (dO := oRS) (len := 32)
    ⟨sptr_ok rfl (by have := hF.sk; omega), by ssep hF⟩ ⟨sptr_ok rfl (by decide), by ssep hF⟩ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by ssep hF))
    fun s' ⟨k', b'⟩ => ?_
  have h24 : s'.gpr .r24 = 1 := by rw [k'.cs .r24 (by decide), h1]
  refine ⟨⟨h.keep k' (by ssep hF [sc1Chk]), ?_, .inr h24, fun _ => ⟨fun _ hd => absurd hd (by omega),
    fun _ hd => absurd hd (by omega)⟩, fun h0 => absurd (h0.symm.trans h24) (by decide)⟩, h24⟩
  show bytesAt s'.mem (lpa (slay1 p STK σ) (.r31, oRS)) 32 = _
  rw [b', show lpa (slay1 p STK σ) (.r30, 0) = (slay1 p STK σ).A 2 0 from rfl, sk_rho hF h]

theorem expandA_ok {σ s : State} (h : SC1 p STK σ s) (h1 : s.gpr .r24 = 1) :
    WP isa (expandA P p) s (IA p STK σ (p.k * p.ℓ)) := by
  unfold Impl.MlDsa.PPC64LE.Sign.expandA
  refine WP.seq (WP.mono (rho_ok hF h h1) fun s' h' => ?_)
  simpa using wp_seqR (I := fun e => IA p STK σ e) (p.k * p.ℓ) 0
    (fun e _ he _ hs => sampleE_ok hP hF hS (by omega) hs) s' h'.1

omit hP hF hS in
theorem blkE_taint : ∀ v < 8, ∀ w < 8, (VG.PPC64LE.taint.check (Taint.ofRegs [.r31])
    (.block (setB (sc (oRS + 32)) v ++ setB (sc (oRS + 33)) w)) (.block [])).isSome = true := by decide +kernel

omit hP hF hS in
theorem and24_taint : (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) (.block and24) (.block [])).isSome = true := by
  decide +kernel

theorem sampleE_tr {e : Nat} (he : e < p.k * p.ℓ) :
    RelCT isa (RR p STK (IA p STK · e) E24) (sampleE P p e) (RR p STK (IA p STK · (e + 1)) E24) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  rw [sampleE_eq]
  refine RelCT.seq (stepRR
    (J := fun σ s => IA p STK σ e s ∧ bytesAt s.mem ((slay1 p STK σ).A 0 oRS) 34 = seedE p σ e)
    (F := fun s s' => s'.gpr .r24 = s.gpr .r24) (E' := E24)
    (fun σ s _ h => blkE_ok hF he h)
    (RelCT.mono (srel1 (fun σ s h => h.sc) (blkE_taint _ (by omega) _ (by omega))) (fun _ _ h => h.1) fun _ _ h => h)
    fun x y x' y' hr fx fy _ => by show _ = _; rw [fx, fy]; exact hr.2) ?_
  refine RelCT.seq (stepRR (J := JE p STK e) (F := fun s s' => s'.gpr .r24 = s.gpr .r24)
    (E' := fun x y => E24 x y ∧ (x.gpr .r3).setWidth 32 = (y.gpr .r3).setWidth 32)
    (fun σ s _ h => callE_ok hP hF hS he h.1 h.2) ?_
    fun x y x' y' hr fx fy q => ⟨by show _ = _; rw [fx, fy]; exact hr.2, q⟩) ?_
  · refine RelCT.mono (RelCT.exists_ fun σ => rn_trRet hP (L := slay1 p STK σ) (Wb := sWb1) hS
      (name := "vg_mldsa_rej_ntt_poly") (rnE_m hF he)
      (Q := fun x y => Site (slay1 p STK σ) sWb1 STK x ∧ Site (slay1 p STK σ) sWb1 STK y ∧ x.sp = y.sp ∧
        bytesAt x.mem (lpa (slay1 p STK σ) (sc oRS)) 34 = bytesAt y.mem (lpa (slay1 p STK σ) (sc oRS)) 34)
      fun _ _ h => h) ?_ fun _ _ h => h
    rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁, b₁⟩, ⟨h₂, b₂⟩⟩, -⟩
    have T := sc1_twoL pub h₁.sc h₂.sc
    refine ⟨σ₁, T.1, T.2.1, T.2.2, ?_⟩
    show bytesAt x.mem ((slay1 p STK σ₁).A 0 oRS) 34 = bytesAt y.mem ((slay1 p STK σ₁).A 0 oRS) 34
    rw [b₁, slay1_pub pub, b₂, seedE, seedE, rhoOf, rhoOf, pub_rho pub]
  · refine stepRR (J := fun σ s => IA p STK σ (e + 1) s)
      (F := fun s s' => s'.gpr .r24 = s.gpr .r24 &&& zx (s.gpr .r3)) (Q₀ := fun _ _ => True)
      (fun σ s _ h => WP.conj (andE_ok hF he h) (WP.mono (and24_ok s) fun _ h => h.2.1))
      (RelCT.mono (srel1 (fun σ s h => ?_) and24_taint) (fun _ _ h => h.1) fun _ _ h => h)
      fun x y x' y' hr fx fy _ => ?_
    · obtain ⟨s₀, h, k, -⟩ := h
      exact h.sc.keep k (by ssep hF [sc1Chk])
    · show _ = _
      rw [fx, fy, hr.2.1]; simp only [zx, hr.2.2]

theorem expandA_tr :
    RelCT isa (RR p STK (fun σ s => SC1 p STK σ s ∧ s.gpr .r24 = 1) fun _ _ => True) (expandA P p)
      (RR p STK (IA p STK · (p.k * p.ℓ)) E24) := by
  unfold Impl.MlDsa.PPC64LE.Sign.expandA
  refine RelCT.seq (stepRR (J := fun σ s => IA p STK σ 0 s) (F := fun _ s' => s'.gpr .r24 = 1) (E' := E24)
    (fun σ s _ h => rho_ok hF h.1 h.2)
    (RelCT.mono (srel1p (fun σ s h => h.1) (by taint_decide)) (fun _ _ h => h.1) fun _ _ h => h)
    fun x y x' y' _ fx fy _ => by show _ = _; rw [fx, fy]) ?_
  simpa using rr_seqR (R := fun e => RR p STK (IA p STK · e) E24) (p.k * p.ℓ) 0
    fun e _ he => sampleE_tr hP hF hS (by omega)

end

end VG.Proof.MlDsa.PPC64LE.Sign
