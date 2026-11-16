module

public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Arith
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallRound
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-DSA verification on AArch64: what computing `w′₁` keeps

With the entries `A'` of `Â` and `c = c0` as the samplers left them, and `x24`
their result `q` (`SC`): what a write to `scratch` keeps of it (`SCChk`,
`scchks`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv multiplyNTT Bounds minBounds rejNTTPoly sampleInBall simpleBitPack d ofInt)
open VG.Proof.MlDsa (polyAt natPolyAt coeffAt Reduced PolyIs NatPolyIs HintIs)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Proof.MlDsa.Verify (zHat dotAcc t1Hat wRow w1Row vT1 aSeed)

/-- Where row `r` of `w1Encode(w′₁)` goes. -/
abbrev rowP (p : Params) (r : Nat) : Ptr := sc (oP (p.k * p.ℓ + 0) + w1Len p * r)

/-- What the samplers gave: `q` whether they succeeded, `Â = A'` and `c = c0` if so. -/
def Gd (p : Params) (σ : State) (A' : Nat → Nat → Poly) (c0 : Poly) (q : Bool) : Prop :=
  (q = true → (∀ r < p.k, ∀ c < p.ℓ, ∃ b : Bounds, rejNTTPoly b.rejNTT (aSeed (vPk p σ) r c) = some (A' r c)) ∧
      ∃ b : Bounds, (sampleInBall p.τ b.ball (ctOf p σ)).map toRq = some c0) ∧
    (q = false → (∃ r < p.k, ∃ c < p.ℓ, rejNTTPoly minBounds.rejNTT (aSeed (vPk p σ) r c) = none) ∨
      (sampleInBall p.τ minBounds.ball (ctOf p σ)).map toRq = none)

/-- While computing: `ẑ[i]` for `i < j` (`z[i]` after), `ĉ` if `cn` (`c` if not),
and the rows of `w′₁` before `r` packed. -/
structure SC (p : Params) (σ : State) (h : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → Poly) (c0 : Poly)
    (q : Bool) (j : Nat) (cn : Bool) (r : Nat) (s : State) : Prop where
  vc : VC p σ s
  hh : hintOf p σ = some h
  hint : HintIs s.mem (pa s (hP p 0)) p.k h
  nok : normOk p σ p.ℓ
  gd : Gd p σ A' c0 q
  a : ∀ r' < p.k, ∀ c < p.ℓ, PolyIs s.mem (pa s (aP (p.ℓ * r' + c))) (A' r' c)
  z : ∀ i < p.ℓ, PolyIs s.mem (pa s (zP p i))
    (if i < j then zHat p (vSig p σ) i else toRq (zOf p σ i))
  c : PolyIs s.mem (pa s (cP p)) (if cn then ntt c0 else c0)
  rows : ∀ r' < r, bytesAt s.mem (pa s (rowP p r')) (w1Len p) =
    simpleBitPack (w1Row p (vPk p σ) (vSig p σ) A' (ntt c0) h r') (w1Max p)
  x24 : s.gpr .x24 = flag (q = true)

abbrev SCx (p : Params) (j : Nat) (cn : Bool) (r : Nat) (σ s : State) : Prop :=
  ∃ h A' c0 q, SC p σ h A' c0 q j cn r s

/-- A piece that writes `ws` keeps `SC`. -/
structure SCChk (p : Params) (r : Nat) (ws : List (Ptr × Nat)) : Prop where
  vc : vcChk p ws = true
  hint : keepB (vR p) (vW p) ws (hP p 0) (1024 * p.k) = true
  a : ∀ r' < p.k, ∀ c < p.ℓ, keepB (vR p) (vW p) ws (aP (p.ℓ * r' + c)) 1024 = true
  z : ∀ i < p.ℓ, keepB (vR p) (vW p) ws (zP p i) 1024 = true
  c : keepB (vR p) (vW p) ws (cP p) 1024 = true
  rows : ∀ r' < r, keepB (vR p) (vW p) ws (rowP p r') (w1Len p) = true

theorem ar_lt {p : Params} {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) : p.ℓ * r + c < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show r + 1 ≤ p.k by omega_arith)
  rw [Nat.mul_succ, Nat.mul_comm p.ℓ p.k] at this
  omega_arith

theorem keepB_append {rbs wbs : List (Reg × Nat)} {ws₁ ws₂ : List (Ptr × Nat)} {q : Ptr} {l : Nat}
    (h₁ : keepB rbs wbs ws₁ q l = true) (h₂ : keepB rbs wbs ws₂ q l = true) :
    keepB rbs wbs (ws₁ ++ ws₂) q l = true := by
  simp only [keepB, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁.1, h₁.2, h₂.2⟩

theorem vcChk_append {p : Params} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : vcChk p ws₁ = true)
    (h₂ : vcChk p ws₂ = true) : vcChk p (ws₁ ++ ws₂) = true := by
  simp only [vcChk, Bool.and_eq_true] at *
  exact ⟨⟨⟨keepB_append h₁.1.1.1 h₂.1.1.1, keepB_append h₁.1.1.2 h₂.1.1.2⟩, keepB_append h₁.1.2 h₂.1.2⟩,
    keepB_append h₁.2 h₂.2⟩

/-- The checks of two pieces of writes, for both. -/
theorem SCChk.append {p : Params} {r : Nat} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : SCChk p r ws₁)
    (h₂ : SCChk p r ws₂) : SCChk p r (ws₁ ++ ws₂) :=
  ⟨vcChk_append h₁.vc h₂.vc, keepB_append h₁.hint h₂.hint,
    fun r' hr' c hc => keepB_append (h₁.a r' hr' c hc) (h₂.a r' hr' c hc), fun i hi => keepB_append (h₁.z i hi) (h₂.z i hi),
    keepB_append h₁.c h₂.c, fun r' hr' => keepB_append (h₁.rows r' hr') (h₂.rows r' hr')⟩

/-- A write to `scratch` keeps a region of another buffer, both in the layout. -/
theorem vkeepB_one_diff {p : Params} {r' : Reg} {o n o' l : Nat} (hne : r' ≠ .x28)
    (hq : inB (vR p ++ vW p) (r', o') l = true) (hi : inB (vR p ++ vW p) (.x28, o) n = true) :
    keepB (vR p) (vW p) [((.x28, o), n)] (r', o') l = true := by
  simp only [keepB, List.all_cons, List.all_nil, sepB_v hne (.inr rfl), hq, hi, Bool.and_self]

/-- A write to `scratch` keeps a region of `scratch` apart from it, both in the layout. -/
theorem vkeepB_one_same {p : Params} {o n o' l : Nat} (hq : o' + l ≤ scrLen p) (hi : o + n ≤ scrLen p)
    (h : o' + l ≤ o ∨ o + n ≤ o') : keepB (vR p) (vW p) [((.x28, o), n)] (.x28, o') l = true := by
  have hq' : inB (vR p ++ vW p) (.x28, o') l = true := (vinB_x28 p o' l).trans (decide_eq_true hq)
  have hi' : inB (vR p ++ vW p) (.x28, o) n = true := (vinB_x28 p o n).trans (decide_eq_true hi)
  simp only [keepB, List.all_cons, List.all_nil, sepB_same, hq', hi', Bool.and_true, Bool.true_and,
    Bool.or_eq_true, decide_eq_true_eq]
  exact h

/-- No writes. -/
theorem SCChk.nil {p : Params} (hF : VFacts p) {r : Nat} (hr : r ≤ p.k) : SCChk p r [] :=
  ⟨by vlayd, by vlayd, fun _ _ _ _ => by vlayd, fun _ _ => by vlayd, by vlayd, fun _ _ => by vlayd⟩

/-- A write to `scratch` apart from what `SC` holds, proved once for any region: each check is about
the write and one region. -/
theorem SCChk.x28 {p : Params} (hF : VFacts p) {r : Nat} (hr : r ≤ p.k) {o n : Nat}
    (h1 : o + n ≤ SV ∨ SV + 48 ≤ o) (h2 : o + n ≤ oP 0 ∨ oP (p.k * p.ℓ) ≤ o)
    (h3 : o + n ≤ oP (p.k * p.ℓ) ∨ oP (p.k * p.ℓ) + w1Len p * r ≤ o)
    (h4 : o + n ≤ oP (p.k * p.ℓ + 1) ∨ oP (p.k * p.ℓ + (1 + p.k + p.ℓ + 1)) ≤ o) (h5 : o + n ≤ scrLen p) :
    SCChk p r [((.x28, o), n)] := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hs := scr_eq p
  have hi : inB (vR p ++ vW p) (.x28, o) n = true := (vinB_x28 p o n).trans (decide_eq_true h5)
  have bx : ∀ {o' l : Nat}, o' + l ≤ scrLen p → (o' + l ≤ o ∨ o + n ≤ o') →
      keepB (vR p) (vW p) [((.x28, o), n)] (.x28, o') l = true :=
    fun h => vkeepB_one_same h h5
  have hw : w1Len p * r ≤ 1024 := by
    have := Nat.mul_le_mul_left (w1Len p) hr; rw [Nat.mul_comm (w1Len p) p.k] at this; have := hF.w1; omega_arith
  simp only [SV, oP] at h1 h2 h3 h4
  refine ⟨?_, bx ?_ ?_, fun r' hr' c hc => bx ?_ ?_, fun i hi' => bx ?_ ?_, bx ?_ ?_, fun r' hr' => bx ?_ ?_⟩
  · have hpk := hF.pk; have hsg := hF.sig
    simp only [vcChk, Bool.and_eq_true]
    exact ⟨⟨⟨bx (by rw [hs]; simp only [SV]; omega_arith) (by simp only [SV]; omega_arith),
      vkeepB_one_diff (by decide) ((vinB_x25 p 0 _).trans (decide_eq_true (Nat.le_of_eq (Nat.zero_add _)))) hi⟩,
      vkeepB_one_diff (by decide) ((vinB_x26 p 0 _).trans (decide_eq_true (Nat.le_of_eq (Nat.zero_add _)))) hi⟩,
      vkeepB_one_diff (by decide) ((vinB_x27 p 0 _).trans (decide_eq_true (Nat.le_of_eq (Nat.zero_add _)))) hi⟩
  all_goals simp only [oP]
  · rw [hs]; omega_arith
  · omega_arith
  · have := ar_lt hr' hc; rw [hs]; omega_arith
  · have := ar_lt hr' hc; omega_arith
  · rw [hs]; omega_arith
  · omega_arith
  · rw [hs]; omega_arith
  · omega_arith
  · rcases hF.wl with e | e <;> rw [e] at h3 hw ⊢ <;> rw [hs] <;> omega_arith
  · rcases hF.wl with e | e <;> rw [e] at h3 hw ⊢ <;> omega_arith

theorem SCChk.cons_x28 {p : Params} (hF : VFacts p) {r : Nat} (hr : r ≤ p.k) {o n : Nat} {ws : List (Ptr × Nat)}
    (h1 : o + n ≤ SV ∨ SV + 48 ≤ o) (h2 : o + n ≤ oP 0 ∨ oP (p.k * p.ℓ) ≤ o)
    (h3 : o + n ≤ oP (p.k * p.ℓ) ∨ oP (p.k * p.ℓ) + w1Len p * r ≤ o ∨ oP (p.k * p.ℓ) + 1024 ≤ o)
    (h4 : o + n ≤ oP (p.k * p.ℓ + 1) ∨ oP (p.k * p.ℓ + (1 + p.k + p.ℓ + 1)) ≤ o) (h5 : o + n ≤ scrLen p)
    (h : SCChk p r ws) : SCChk p r (((.x28, o), n) :: ws) := by
  have : w1Len p * r ≤ 1024 := by
    have := Nat.mul_le_mul_left (w1Len p) hr; rw [Nat.mul_comm (w1Len p) p.k] at this; have := hF.w1; omega_arith
  exact (SCChk.x28 hF hr h1 h2 (by omega_arith) h4 h5).append (ws₁ := [_]) h

/-- Proves an `SCChk` of writes to `scratch` by `SCChk.cons_x28`, with `hr : r ≤ p.k`. -/
tactic_template "scchks " hF:term:max hr:term:max : tactic => `(tactic| (
                   repeat' (first
                     | with_reducible exact VG.Proof.MlDsa.AArch64.Verify.SCChk.nil $hF $hr
                     | apply VG.Proof.MlDsa.AArch64.Verify.SCChk.cons_x28 $hF $hr)
                   all_goals (
                     have := ($hF).w1; have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).ct.2
                     try rw [VG.Proof.MlDsa.AArch64.KeyGen.scr_eq]
                     try simp only [VG.Impl.MlDsa.AArch64.KeyGen.oP, VG.Impl.MlDsa.AArch64.KeyGen.SV,
                       VG.Impl.MlDsa.AArch64.KeyGen.oSS, VG.Impl.MlDsa.AArch64.Verify.oCT]
                     omega_arith)))

/-! ## From the samplers -/

theorem seedOf_ar (p : Params) (σ : State) {r c : Nat} (hc : c < p.ℓ) :
    seedOf p σ (p.ℓ * r + c) = aSeed (vPk p σ) r c := by
  have hl : 0 < p.ℓ := by omega_arith
  rw [seedOf, Nat.mul_add_div hl, Nat.div_eq_of_lt hc, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]

theorem vb_sc {p : Params} {σ s : State} (hs : VB p σ s) : SCx p 0 false 0 σ s := by
  obtain ⟨h, hh, hH⟩ := hs.vz.hint
  obtain ⟨q, hq, h1, h0⟩ := hs.ok
  refine ⟨h, fun r c => polyAt s.mem (pa s (aP (p.ℓ * r + c))), polyAt s.mem (pa s (cP p)), q,
    ⟨hs.vz.vc, hh, hH, hs.nok, ⟨fun hq' => ⟨fun r hr c hc => ?_, (h1 hq').2⟩, fun hq' => ?_⟩,
      fun r hr c hc => ⟨hs.red _ (ar_lt hr hc), rfl⟩, fun i hi => by rw [ifn (Nat.not_lt_zero _)]; exact hs.vz.z i hi,
      ⟨hs.redC, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _), hq⟩⟩
  · obtain ⟨b, hb⟩ := (h1 hq').1 _ (ar_lt hr hc)
    exact ⟨b, by rw [← seedOf_ar p σ hc]; exact hb⟩
  · rcases h0 hq' with ⟨e, he, hn⟩ | hn
    · have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega_arith
      refine .inl ⟨e / p.ℓ, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he), e % p.ℓ, Nat.mod_lt _ hl, ?_⟩
      rw [← seedOf_ar p σ (Nat.mod_lt _ hl), Nat.div_add_mod]; exact hn
    · exact .inr hn

/-! ## A row -/

/-- `Σₛ Â[r, s] ẑ[s]`. -/
abbrev rDot (p : Params) (σ : State) (A' : Nat → Nat → Poly) (r : Nat) : Poly := dotAcc p (vSig p σ) A' r p.ℓ
/-- `t₁[r] · 2ᵈ`. -/
abbrev rU (p : Params) (σ : State) (r : Nat) : Poly := (vT1 (vPk p σ) r).map fun c => ofInt (c * 2 ^ d : Nat)

theorem hintRow_pa (p : Params) (s : State) (r : Nat) :
    pa s (hP p r) = pa s (hP p 0) + BitVec.ofNat 64 (1024 * r) := by
  have e : oP (p.k * p.ℓ + (1 + r)) = oP (p.k * p.ℓ + (1 + 0)) + 1024 * r := by simp only [oP]; omega_arith
  rw [show pa s (hP p r) = s.gpr .x28 + BitVec.ofNat 64 (oP (p.k * p.ℓ + (1 + r))) from rfl,
    show pa s (hP p 0) = s.gpr .x28 + BitVec.ofNat 64 (oP (p.k * p.ℓ + (1 + 0))) from rfl, e, BitVec.ofNat_add,
    BitVec.add_assoc]

end VG.Proof.MlDsa.AArch64.Verify
