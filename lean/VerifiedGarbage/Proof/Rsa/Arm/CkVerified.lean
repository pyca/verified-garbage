module

public import VerifiedGarbage.Proof.Rsa.Arm.KcBodyW
public import VerifiedGarbage.Proof.Rsa.Arm.KcCT
public import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
public import VerifiedGarbage.Proof.Rsa.Arm.KcTaintW
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Rsa.Arm.CkCorrect
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
import VerifiedGarbage.Proof.Rsa.Arm.CkTaint
import VerifiedGarbage.Proof.Rsa.Arm.CckVerified
public import VerifiedGarbage.Proof.Rsa.Arm.KcFnCT
public import VerifiedGarbage.Proof.Rsa.Arm.KcShape
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target

/-! # `vg_rsa_check_key` on ARMv7 is verified against the shared RSA contract -/

@[expose] public section

/-! ## The checks of a balanced RSA key on ARMv7: constant time

`keyBodyW_ct`: as `keyBody_ct`, two runs of `keyBodyW` related at every step
by what correctness says of each. Between its pieces each run is `StW`: some
`Stg` on a known list of live arrays, with `p`, `q` (and later `p - 1`, `q - 1`,
and the divisor of a division) of `w / 2` words, which is what the products
and divisions by words need (`KeyDiv.mulLo_ct`, `KeyDiv.divW_ct`); the other
pieces the taint analysis checks (`KcTaintW.lean`).
-/

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- `w / 2` words. -/
abbrev Bd (g : Geo) : Nat := 2 ^ (32 * (g.w / 2))

/-- From the start: the zero array, `p`, `q`, `dP` and `dQ` of `w / 2` words. -/
def M0 (g : Geo) (A : Nat → Nat) : Prop :=
  A aZ = 0 ∧ A aP < Bd g ∧ A aQ < Bd g ∧ A aDP < Bd g ∧ A aDQ < Bd g
/-- After the checks of `dP` and `dQ`: also `p - 1` and `q - 1`. -/
def M1 (g : Geo) (A : Nat → Nat) : Prop := M0 g A ∧ A aM1 < Bd g ∧ A aM2 < Bd g
/-- Before a division: also its divisor, with its top word not zero. -/
def MD (g : Geo) (A : Nat → Nat) : Prop := M1 g A ∧ A aVD < Bd g ∧ 2 ^ (32 * (g.w / 2 - 1)) ≤ A aVD

/-- A run between the pieces: `Stg` on the arrays `L`, its values `M`. -/
def StW (g : Geo) (σ : State) (L : List Nat) (M : (Nat → Nat) → Prop) (s : State) : Prop :=
  ∃ A c, Stg g σ A L c s ∧ M A

theorem M0_upd {g : Geo} {A : Nat → Nat} (h : M0 g A) {o : Nat} (z : Nat) (h1 : aZ ≠ o) (h2 : aP ≠ o)
    (h3 : aQ ≠ o) (h4 : aDP ≠ o := by decide) (h5 : aDQ ≠ o := by decide) : M0 g (upd A o z) := by
  obtain ⟨a, b, c, d, e⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [upd_ne _ _ h1]; exact a
  · rw [upd_ne _ _ h2]; exact b
  · rw [upd_ne _ _ h3]; exact c
  · rw [upd_ne _ _ h4]; exact d
  · rw [upd_ne _ _ h5]; exact e

theorem M1_upd {g : Geo} {A : Nat → Nat} (h : M1 g A) {o : Nat} (z : Nat) (h1 : aZ ≠ o) (h2 : aP ≠ o)
    (h3 : aQ ≠ o) (h4 : aM1 ≠ o) (h5 : aM2 ≠ o) (h6 : aDP ≠ o := by decide) (h7 : aDQ ≠ o := by decide) :
    M1 g (upd A o z) := by
  obtain ⟨m, d, e⟩ := h
  refine ⟨M0_upd m z h1 h2 h3 h6 h7, ?_, ?_⟩
  · rw [upd_ne _ _ h4]; exact d
  · rw [upd_ne _ _ h5]; exact e

theorem stg_c16 {g : Geo} {σ s : State} {A : Nat → Nat} {L : List Nat} {c : Bool} (h : Stg g σ A L c s) :
    slot s.mem g.B 16 = g.w := by
  simp only [slot, w32]; rw [h.cnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.ws.wle; omega)]

theorem StW.stg {g : Geo} {σ s : State} {L : List Nat} {M : (Nat → Nat) → Prop} (h : StW g σ L M s) :
    ∃ A live c, Stg g σ A live c s :=
  let ⟨A, c, hs, _⟩ := h
  ⟨A, L, c, hs⟩

theorem StW.ws {g : Geo} {σ s : State} {L : List Nat} {M : (Nat → Nat) → Prop} (h : StW g σ L M s) :
    Ws s g.B g.Z g.w nArr :=
  let ⟨_, _, hs, _⟩ := h
  hs.ws

theorem StW.mulPre {g : Geo} {σ s : State} {L : List Nat} {M : (Nat → Nat) → Prop} (h : StW g σ L M s)
    {x : Nat} (hx : x ∈ L) (hz : aZ ∈ L) (hM : ∀ A, M A → A aZ = 0 ∧ A x < Bd g) :
    VG.Proof.Rsa.Arm.KeyDiv.MulPre g.B g.Z g.w nArr x s := by
  obtain ⟨A, c, hs, hm⟩ := h
  refine ⟨hs.ws, stg_c16 hs, by rw [hs.arrs.get hx]; exact (hM A hm).2, ?_⟩
  have := hs.arrs.get hz
  rw [(hM A hm).1] at this
  exact this

theorem StW.divPre {g : Geo} {σ s : State} {L : List Nat} (h : StW g σ L (MD g) s) (hv : aVD ∈ L)
    (hz : aZ ∈ L) (hw6 : 6 ≤ g.w) : VG.Proof.Rsa.Arm.KeyDiv.DivPre g.B g.Z g.w nArr aVD s := by
  obtain ⟨A, c, hs, hm⟩ := h
  refine ⟨hs.ws, stg_c16 hs, by rw [hs.arrs.get hv]; exact hm.2.1,
    top_word_pos (k := g.w / 2 - 1) (n := g.w) (by omega) (hs.arrs.get hv)
      (by rw [show g.w / 2 - 1 + 1 = g.w / 2 by omega]; exact hm.2.1) hm.2.2, ?_⟩
  have := hs.arrs.get hz
  rw [hm.1.1.1] at this
  exact this

/-! ## Each piece, for one run -/

theorem stw_start {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) (hp : v.p < Bd g) (hq : v.q < Bd g)
    (hdp : v.dP < Bd g) (hdq : v.dQ < Bd g) : WP isa startW s (StW g s live0 (M0 g)) :=
  WP.mono (first_ok h) fun _ ht => ⟨_, _, ht, rfl, hp, hq, hdp, hdq⟩

theorem stw_mulLo {g : Geo} {σ s : State} {L : List Nat} {M : (Nat → Nat) → Prop} (h : StW g σ L M s)
    {o x y : Nat} (ho : o < nArr) (hx : x ∈ L) (hy : y ∈ L) (hz : aZ ∈ L) (hox : o ≠ x) (hoy : o ≠ y)
    (ho0 : o ≠ aZ) (hoV : o ≠ aVD) (hw : g.w % 2 = 0) (hw2 : 2 ≤ g.w)
    (hM : ∀ A, M A → A aZ = 0 ∧ A x < Bd g) (hMo : ∀ A z, M A → M (upd A o z)) :
    WP isa (VG.Impl.Rsa.Arm.KeyDiv.mulLo o x y) s (StW g σ (o :: L) M) := by
  obtain ⟨A, c, hs, hm⟩ := h
  exact WP.mono (hs.mulLo_ok ho hx hy hz (hM A hm).1 hox hoy ho0 hoV hw hw2 (hM A hm).2) fun _ ht =>
    ⟨_, c, ht, hMo _ _ hm⟩

theorem stw_eqA {g : Geo} {σ s : State} {L : List Nat} {M : (Nat → Nat) → Prop} (h : StW g σ L M s)
    {a b : Nat} (ha : a ∈ L) (hb : b ∈ L) (hW : aW ∉ L) : WP isa (seqs (eqA a b)) s (StW g σ L M) := by
  obtain ⟨A, c, hs, hm⟩ := h
  exact WP.mono (hs.eqA_ok ha hb hW) fun _ ht => ⟨_, _, ht, hm⟩

theorem stw_ltA {g : Geo} {σ s : State} {L : List Nat} {M : (Nat → Nat) → Prop} (h : StW g σ L M s)
    {a b : Nat} (ha : a ∈ L) (hb : b ∈ L) (hW : aW ∉ L) : WP isa (seqs (ltA a b)) s (StW g σ L M) := by
  obtain ⟨A, c, hs, hm⟩ := h
  exact WP.mono (hs.ltA_ok ha hb hW) fun _ ht => ⟨_, _, ht, hm⟩

/-- The list of arrays after `p - 1` and `q - 1`. -/
abbrev LA : List Nat := aM2 :: aM1 :: aVQ :: live0

theorem stw_chunkA {g : Geo} {σ s : State} (h : StW g σ (aVQ :: live0) (M0 g) s) :
    WP isa (seqs chunkA) s (StW g σ LA (M1 g)) := by
  obtain ⟨A, c, h1, hm⟩ := h
  obtain ⟨m0, mp, mq, md, me⟩ := hm
  unfold chunkA
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h1.eqA_ok (a := aVQ) (b := aN) (by decide) (by decide) (by decide)) fun t2 h2 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h2.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t3 h3 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h3.clrLow_ok (j := aM1) (by decide)) fun t4 h4 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h4.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t5 h5 => ?_
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h5.clrLow_ok (j := aM2) (by decide)) fun t6 h6 => ?_
  have hA0 : ∀ B : Nat → Nat, B = upd (upd (upd (upd A aM1 (A aP)) aM1 (2 * (upd A aM1 (A aP) aM1 / 2))) aM2
      (upd (upd A aM1 (A aP)) aM1 (2 * (upd A aM1 (A aP) aM1 / 2)) aQ)) aM2
      (2 * (upd (upd (upd A aM1 (A aP)) aM1 (2 * (upd A aM1 (A aP) aM1 / 2))) aM2
        (upd (upd A aM1 (A aP)) aM1 (2 * (upd A aM1 (A aP) aM1 / 2)) aQ) aM2 / 2)) →
      M1 g B := by
    rintro B rfl
    simp only [M1, M0, upd, ↓reduceIte]
    simp (disch := decide) only [show aZ ≠ aM2 by decide, show aZ ≠ aM1 by decide, show aP ≠ aM2 by decide,
      show aP ≠ aM1 by decide, show aQ ≠ aM2 by decide, show aQ ≠ aM1 by decide, show aM1 ≠ aM2 by decide,
      show aDP ≠ aM2 by decide, show aDP ≠ aM1 by decide, show aDQ ≠ aM2 by decide, show aDQ ≠ aM1 by decide,
      ↓reduceIte]
    omega
  exact WP.mono (h6.ltA_ok (a := aDP) (b := aM1) (by decide) (by decide) (by decide)) fun _ h7 =>
    ⟨_, _, h7, hA0 _ rfl⟩

/-- `[aVD] := fixT [d]`, the divisor of a division. -/
theorem stw_divSet {g : Geo} {σ s : State} {L : List Nat} (h : StW g σ L (M1 g) s) {d : Nat} (hd : d ∈ L)
    (hdV : d ≠ aVD) (hD : ∀ A, M1 g A → A d < Bd g) (hw2 : 2 ≤ g.w) :
    WP isa (seqs [copy aVD d, .block (VG.Impl.Rsa.Arm.KeyDiv.fixTop aVD)]) s (StW g σ (aVD :: L) (MD g)) := by
  obtain ⟨A, c, h0, hm⟩ := h
  rw [wp_seqs_cons (by ne_nil)]
  refine WP.mono (h0.copy_ok (o := aVD) (a := d) (by decide) hd (Ne.symm hdV)) fun t1 h1 => ?_
  have hD1 : upd A aVD (A d) aVD < 2 ^ (32 * (g.w / 2)) := by rw [upd_self]; exact hD A hm
  refine WP.mono (h1.fixTop_ok (m := aVD) (by simp) hD1 hw2) fun t2 h2 => ⟨_, _, h2, ?_⟩
  refine ⟨M1_upd (M1_upd hm _ (by decide) (by decide) (by decide) (by decide) (by decide)) _ (by decide)
    (by decide) (by decide) (by decide) (by decide), ?_, ?_⟩
  · rw [upd_self, upd_self]; exact VG.Proof.Rsa.fixT_lt (by omega) (hD A hm)
  · rw [upd_self, upd_self]; exact VG.Proof.Rsa.fixT_ge

/-- `[aVR] := [a] mod [aVD]`. -/
theorem stw_divW {g : Geo} {σ s : State} {L : List Nat} (h : StW g σ L (MD g) s) {a : Nat} (ha : a ∈ L)
    (hv : aVD ∈ L) (hz : aZ ∈ L) (hav : a ∉ [aVR, aVT, aY, aX]) (hw6 : 6 ≤ g.w)
    (hlive : ∀ j ∈ L, j = aVR ∨ j ∉ [aVR, aVT, aX, aY]) :
    WP isa (VG.Impl.Rsa.Arm.KeyDiv.divW a aVR aVD aVT aY aX) s (StW g σ (aVR :: L) (M1 g)) := by
  obtain ⟨A, c, h0, hm⟩ := h
  have := h0.divW_ok (a := a) (r := aVR) (m := aVD) (t := aVT) (nm := aY) (u := aX) ha hv hz hm.1.1.1
    (hr := by decide) (ht := by decide)
    (hnm := by decide) (hu := by decide) (hra := fun e => hav (by simp [e])) (hrt := by decide)
    (hru := by decide) (htu := by decide) (hmr := by decide) (hmt := by decide) (hmu := by decide)
    (hnr := by decide) (htn := by decide) (hnu := by decide) (hnm' := by decide) (hr0 := by decide)
    (ht0 := by decide) (hu0 := by decide) (hn0 := by decide) (hV := by decide) (hw6 := hw6)
    (hMl := hm.2.1) (hMg := hm.2.2) (hlive := hlive)
  exact WP.mono this fun _ ht => ⟨_, _, ht, M1_upd hm.1 _ (by decide) (by decide) (by decide) (by decide)
    (by decide)⟩

/-! ## Regrouping a list of programs -/

/-- `keyBodyW`, in the pieces of its proof of constant time. -/
abbrev partsW : List (List (Prog isa)) :=
  [[startW], [VG.Impl.Rsa.Arm.KeyDiv.mulLo aVQ aP aQ], chunkA, [VG.Impl.Rsa.Arm.KeyDiv.mulLo aA aDP aE],
    [copy aVD aM1, .block (VG.Impl.Rsa.Arm.KeyDiv.fixTop aVD)],
    [VG.Impl.Rsa.Arm.KeyDiv.divW aA aVR aVD aVT aY aX], chunkB, [VG.Impl.Rsa.Arm.KeyDiv.mulLo aA aDQ aE],
    [copy aVD aM2, .block (VG.Impl.Rsa.Arm.KeyDiv.fixTop aVD)],
    [VG.Impl.Rsa.Arm.KeyDiv.divW aA aVR aVD aVT aY aX], chunkC, [VG.Impl.Rsa.Arm.KeyDiv.mulLo aT aQ aQI],
    [copy aVD aP, .block (VG.Impl.Rsa.Arm.KeyDiv.fixTop aVD)],
    [VG.Impl.Rsa.Arm.KeyDiv.divW aT aVR aVD aVT aY aX], eqA aVR aOne ++ ltA aD aN,
    [copy aVD aM1, .block (VG.Impl.Rsa.Arm.KeyDiv.fixTop aVD)],
    [VG.Impl.Rsa.Arm.KeyDiv.divW aD aVR aVD aVT aY aX], eqA aVR aDP,
    [copy aVD aM2, .block (VG.Impl.Rsa.Arm.KeyDiv.fixTop aVD)],
    [VG.Impl.Rsa.Arm.KeyDiv.divW aD aVR aVD aVT aY aX], eqA aVR aDQ]

theorem keyBodyW_parts : keyBodyW = seqs partsW.flatten := by
  simp only [keyBodyW, crtChecksW, dChecksW, divK, partsW, chunkA, chunkB, chunkC, List.flatten_cons,
    List.flatten_nil, List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

/-! ## Both runs -/

section
variable {α : Type} {Pub : α → α → Prop} {gf : α → Geo} (hg : ∀ a₁ a₂, Pub a₁ a₂ → gf a₁ = gf a₂)
  (X : α → State → Prop)

/-- A run between the pieces. -/
def FW (L : List Nat) (M : Geo → (Nat → Nat) → Prop) (a : α) (σ : State) (_ : Vals) (s : State) : Prop :=
  (X a σ ∧ (gf a).w % 2 = 0 ∧ 6 ≤ (gf a).w) ∧ StW (gf a) σ L (M (gf a)) s

include hg

/-- A piece the taint analysis checks from `r7`–`r9`. -/
theorem wPieceB {c : Prog isa} {L L' : List Nat} {M M' : Geo → (Nat → Nat) → Prop}
    (hc : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) c hc).isSome = true)
    (hw : ∀ g σ s, g.w % 2 = 0 → 6 ≤ g.w → StW g σ L (M g) s → WP isa c s (StW g σ L' (M' g))) :
    RelCT isa (LiftB Pub (FW (gf := gf) X L M)) c (LiftB Pub (FW (gf := gf) X L' M')) :=
  pieceB [.r7, .r8, .r9] hc (fun _ _ _ _ _ _ _ _ p h₁ h₂ => ws_regs h₁.2.ws (by rw [hg _ _ p]; exact h₂.2.ws))
    fun _ _ _ _ ⟨x, h⟩ => WP.mono (hw _ _ _ x.2.1 x.2.2 h) fun _ h' => ⟨x, h'⟩

/-- A piece constant time from the same geometry in both runs. -/
theorem gPieceB {c : Prog isa} {Pre : Geo → State → Prop}
    (hc : ∀ g, RelCT isa (fun s t => Pre g s ∧ Pre g t) c fun _ _ => True)
    {F G : α → State → Vals → State → Prop} (hpre : ∀ a σ v s, F a σ v s → Pre (gf a) s)
    (hw : ∀ a σ v s, F a σ v s → WP isa c s (G a σ v)) : RelCT isa (LiftB Pub F) c (LiftB Pub G) := by
  intro s t tr₁ tr₂ s' t' ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ e₁ e₂
  have r := ((hc (gf a₁)).mono (P' := fun s t => F a₁ σ₁ v₁ s ∧ F a₂ σ₂ v₂ t)
    (fun _ _ h => ⟨hpre _ _ _ _ h.1, by rw [hg _ _ p]; exact hpre _ _ _ _ h.2⟩) fun _ _ h => h).wp
    (F₁ := G a₁ σ₁ v₁) (F₂ := G a₂ σ₂ v₂) (fun _ _ h => ⟨hw _ _ _ _ h.1, hw _ _ _ _ h.2⟩)
    s t tr₁ tr₂ s' t' ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, a₁, σ₁, v₁, a₂, σ₂, v₂, p, r.2.2.1, r.2.2.2⟩

/-- `mulLo o x y`. -/
theorem mulPieceB {o x y : Nat} {L : List Nat} {M : Geo → (Nat → Nat) → Prop}
    (T : VG.Proof.Rsa.Arm.KeyDiv.MulTaint o x y) (ho : o < nArr) (hxN : x < nArr) (hyN : y < nArr) (hx : x ∈ L) (hy : y ∈ L) (hz : aZ ∈ L)
    (hox : o ≠ x) (hoy : o ≠ y) (ho0 : o ≠ aZ) (hoV : o ≠ aVD)
    (hM : ∀ g A, M g A → A aZ = 0 ∧ A x < Bd g) (hMo : ∀ g A z, M g A → M g (upd A o z)) :
    RelCT isa (LiftB Pub (FW (gf := gf) X L M)) (VG.Impl.Rsa.Arm.KeyDiv.mulLo o x y)
      (LiftB Pub (FW (gf := gf) X (o :: L) M)) :=
  gPieceB hg (Pre := fun g s => (g.w % 2 = 0 ∧ 6 ≤ g.w) ∧ VG.Proof.Rsa.Arm.KeyDiv.MulPre g.B g.Z g.w nArr x s)
    (fun g => by
      by_cases hw : g.w % 2 = 0 ∧ 6 ≤ g.w
      · exact (VG.Proof.Rsa.Arm.KeyDiv.mulLo_ct T ho hxN hyN (by decide) hox hoy
          ho0 hw.1 (by omega)).mono (fun _ _ h => ⟨h.1.2, h.2.2⟩) fun _ _ h => h
      · exact RelCT.of_false fun _ _ h => hw h.1.1)
    (fun _ _ _ _ ⟨x', h⟩ => ⟨x'.2, h.mulPre hx hz (hM _)⟩)
    fun _ _ _ _ ⟨x', h⟩ => WP.mono (stw_mulLo h ho hx hy hz hox hoy ho0 hoV x'.2.1 (by omega) (hM _) (hMo _))
      fun _ h' => ⟨x', h'⟩

/-- `divW a aVR aVD aVT aY aX`. -/
theorem divWPieceB {a : Nat} {L : List Nat} (T : VG.Proof.Rsa.Arm.KeyDiv.DivTaint a aVR aVD aVT aY aX)
    (ha : a < nArr) (ha' : a ∈ L) (hv : aVD ∈ L) (hz : aZ ∈ L) (hav : a ∉ [aVR, aVT, aY, aX])
    (hlive : ∀ j ∈ L, j = aVR ∨ j ∉ [aVR, aVT, aX, aY]) :
    RelCT isa (LiftB Pub (FW (gf := gf) X L MD)) (VG.Impl.Rsa.Arm.KeyDiv.divW a aVR aVD aVT aY aX)
      (LiftB Pub (FW (gf := gf) X (aVR :: L) M1)) :=
  gPieceB hg (Pre := fun g s => 6 ≤ g.w ∧ VG.Proof.Rsa.Arm.KeyDiv.DivPre g.B g.Z g.w nArr aVD s)
    (fun g => by
      by_cases hw : 6 ≤ g.w
      · exact (VG.Proof.Rsa.Arm.KeyDiv.divW_ct T ha (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (fun e => hav (by simp [e])) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) hw).mono (fun _ _ h => ⟨h.1.2, h.2.2⟩) fun _ _ h => h
      · exact RelCT.of_false fun _ _ h => hw h.1.1)
    (fun _ _ _ _ ⟨x', h⟩ => ⟨x'.2.2, h.divPre hv hz x'.2.2⟩)
    fun _ _ _ _ ⟨x', h⟩ => WP.mono (stw_divW h ha' hv hz hav x'.2.2 hlive) fun _ h' => ⟨x', h'⟩

end


theorem stw_eqLt {g : Geo} {σ s : State} {L : List Nat} {M : (Nat → Nat) → Prop} (h : StW g σ L M s)
    (hW : aW ∉ L) {a b c d : Nat} (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hd : d ∈ L) :
    WP isa (seqs (eqA a b ++ ltA c d)) s (StW g σ L M) := by
  rw [wp_seqs_append (by unfold eqA; exact List.cons_ne_nil _ _) (by unfold ltA; exact List.cons_ne_nil _ _)]
  exact WP.mono (stw_eqA h ha hb hW) fun _ h' => stw_ltA h' hc hd hW

abbrev LB : List Nat := aVR :: aVD :: aA :: LA
abbrev LC : List Nat := aVR :: aVD :: aA :: LB
abbrev L4 : List Nat := aVR :: aVD :: aT :: LC
abbrev L5 : List Nat := aVR :: aVD :: L4
abbrev L6 : List Nat := aVR :: aVD :: L5

section
variable {α : Type} {Pub : α → α → Prop} {gf : α → Geo} (hg : ∀ a₁ a₂, Pub a₁ a₂ → gf a₁ = gf a₂)
  (X : α → State → Prop)
include hg

/-- `keyBodyW` is constant time, for a balanced key. -/
theorem keyBodyW_ct : RelCT isa (LiftB Pub fun a σ v s => s = σ ∧ X a σ ∧ BodyIn (gf a) v s ∧
      (gf a).w % 2 = 0 ∧ v.p < Bd (gf a) ∧ v.q < Bd (gf a) ∧ v.dP < Bd (gf a) ∧ v.dQ < Bd (gf a)) keyBodyW
    (LiftB Pub fun a σ _ t => X a σ ∧ ∃ A live c, Stg (gf a) σ A live c t) := by
  rw [keyBodyW_parts]
  refine RelCT.of_join (fun l hl => by
    simp only [partsW, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> ne_nil)
    (List.cons_ne_nil _ _) ?_
  simp only [partsW, List.map_cons, List.map_nil, seqs_single]
  refine RelCT.seq (R := LiftB Pub (FW (gf := gf) X live0 M0)) (pieceB [.r8, .r11] startW_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p h₁ h₂ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [h₁.2.2.1.r8, h₂.2.2.1.r8, hg _ _ p]
      · rw [h₁.2.2.1.r11, h₂.2.2.1.r11, hg _ _ p])
    fun a σ v s ⟨e, x, h, hw, hp, hq, hdp, hdq⟩ => by
      subst e
      have kb := h.kb
      exact WP.mono (stw_start h hp hq hdp hdq) fun t ht => ⟨⟨x, hw, by simp only [Geo.w]; omega⟩, ht⟩) ?_
  refine RelCT.seq (mulPieceB hg X VG.Proof.Rsa.Arm.KeyCheck.mulVQ_taint (L := live0) (M := M0) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ h => ⟨h.1, h.2.1⟩) fun _ _ z h => M0_upd h z (by decide) (by decide) (by decide)) ?_
  refine RelCT.seq (wPieceB hg X chunkA_taint (L := aVQ :: live0) (M := M0) (L' := LA) (M' := M1)
    fun _ _ _ _ _ h => stw_chunkA h) ?_
  -- `e dP mod (p - 1)`.
  refine RelCT.seq (mulPieceB hg X mulDP_taint (L := LA) (M := M1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ h => ⟨h.1.1, h.1.2.2.2.1⟩)
    fun _ _ z h => M1_upd h z (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  refine RelCT.seq (wPieceB hg X divSetM1_taint (L := aA :: LA) (M := M1) (L' := aVD :: aA :: LA) (M' := MD)
    fun _ _ _ _ hw6 h => stw_divSet h (d := aM1) (by decide) (by decide) (fun _ h => h.2.1) (by omega)) ?_
  refine RelCT.seq (divWPieceB hg X divA_taint (L := aVD :: aA :: LA) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) ?_
  refine RelCT.seq (wPieceB hg X chunkB_taint (L := LB) (M := M1) (L' := LB) (M' := M1)
    fun _ _ _ _ _ h => stw_eqLt h (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  -- `e dQ mod (q - 1)`.
  refine RelCT.seq (mulPieceB hg X mulDQ_taint (L := LB) (M := M1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ h => ⟨h.1.1, h.1.2.2.2.2⟩)
    fun _ _ z h => M1_upd h z (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  refine RelCT.seq (wPieceB hg X divSetM2_taint (L := aA :: LB) (M := M1) (L' := aVD :: aA :: LB) (M' := MD)
    fun _ _ _ _ hw6 h => stw_divSet h (d := aM2) (by decide) (by decide) (fun _ h => h.2.2) (by omega)) ?_
  refine RelCT.seq (divWPieceB hg X divA_taint (L := aVD :: aA :: LB) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) ?_
  refine RelCT.seq (wPieceB hg X chunkC_taint (L := LC) (M := M1) (L' := LC) (M' := M1)
    fun _ _ _ _ _ h => stw_eqLt h (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  -- `q qInv mod p`.
  refine RelCT.seq (mulPieceB hg X mulT_taint (L := LC) (M := M1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ h => ⟨h.1.1, h.1.2.2.1⟩)
    fun _ _ z h => M1_upd h z (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  refine RelCT.seq (wPieceB hg X divSetP_taint (L := aT :: LC) (M := M1) (L' := aVD :: aT :: LC) (M' := MD)
    fun _ _ _ _ hw6 h => stw_divSet h (d := aP) (by decide) (by decide) (fun _ h => h.1.2.1) (by omega)) ?_
  refine RelCT.seq (divWPieceB hg X divT_taint (L := aVD :: aT :: LC) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) ?_
  refine RelCT.seq (wPieceB hg X chunk2_taint (L := L4) (M := M1) (L' := L4) (M' := M1)
    fun _ _ _ _ _ h => stw_eqLt h (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  -- `d mod (p - 1)`.
  refine RelCT.seq (wPieceB hg X divSetM1_taint (L := L4) (M := M1) (L' := aVD :: L4) (M' := MD)
    fun _ _ _ _ hw6 h => stw_divSet h (d := aM1) (by decide) (by decide) (fun _ h => h.2.1) (by omega)) ?_
  refine RelCT.seq (divWPieceB hg X divD_taint (L := aVD :: L4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) ?_
  refine RelCT.seq (wPieceB hg X chunk3_taint (L := L5) (M := M1) (L' := L5) (M' := M1)
    fun _ _ _ _ _ h => stw_eqA h (by decide) (by decide) (by decide)) ?_
  -- `d mod (q - 1)`.
  refine RelCT.seq (wPieceB hg X divSetM2_taint (L := L5) (M := M1) (L' := aVD :: L5) (M' := MD)
    fun _ _ _ _ hw6 h => stw_divSet h (d := aM2) (by decide) (by decide) (fun _ h => h.2.2) (by omega)) ?_
  refine RelCT.seq (divWPieceB hg X divD_taint (L := aVD :: L5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) ?_
  exact (wPieceB hg X chunk4_taint (L := L6) (M := M1) (L' := L6) (M' := M1)
    fun _ _ _ _ _ h => stw_eqA h (by decide) (by decide) (by decide)).mono (fun _ _ h => h)
    fun _ _ h => LiftB.mono (fun _ _ _ _ ⟨x, h⟩ => ⟨x.1, h.stg⟩) h

end

end VG.Proof.Rsa.Arm.KeyCheck

namespace VG.Proof.Rsa.Arm.CheckKey
open VG VG.Arm VG.Proof.Rsa.Arm.KeyCheck VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.X25519.Arm (Rest)

theorem ck_body_ct : RelCT isa
    (LiftB (PubF 14) fun a σ v s => s = σ ∧ FnBase 14 12 insK a σ ∧ BodyIn (geo 12 a) v s ∧ v = vK a) keyBody
    (LiftB (PubF 14) fun a σ _ t => FnBase 14 12 insK a σ ∧ ∃ A live c, Stg (geo 12 a) σ A live c t) :=
  (keyBody_ct (Pub := PubF 14) (gf := geo 12) (fun _ _ p => p.geo_eq (by decide))
    (fun a σ => FnBase 14 12 insK a σ)).mono
    (fun _ _ h => LiftB.mono (fun _ _ _ _ ⟨e, x, b, _⟩ => ⟨e, x, b⟩) h)
    fun _ _ h => LiftB.mono (fun _ _ _ _ ⟨x, _, _, _, _, _, _, _, _, _, _, _, A, live, ht⟩ =>
      ⟨x, A, live, _, ht⟩) h

/-- After `shape`: where the checks started, and Z if the key is balanced. -/
def ShapeOut (a σ : State) (v : Vals) (t : State) : Prop :=
  FnBase 14 12 insK a σ ∧ BodyIn (geo 12 a) v σ ∧ v = vK a ∧ Rest [.r0, .r1, .r2, .r3] σ t ∧ t.mem = σ.mem ∧
    t.z = decide (Balanced 12 a)

theorem balanced_pub {a₁ a₂ : State} (p : PubF 14 a₁ a₂) : decide (Balanced 12 a₁) = decide (Balanced 12 a₂) := by
  simp only [Balanced]
  rw [p.args 3 (by decide), p.args 5 (by decide), p.args 7 (by decide), p.args 9 (by decide),
    p.geo_eq (iS := 12) (by decide)]

/-- `p` of a balanced key has `w / 2` words, as `q`. -/
theorem balanced_lt {a : State} (h : Balanced 12 a) :
    (vK a).p < Bd (geo 12 a) ∧ (vK a).q < Bd (geo 12 a) ∧ (vK a).dP < Bd (geo 12 a) ∧ (vK a).dQ < Bd (geo 12 a) := by
  obtain ⟨lp, lq, ld, le, he⟩ := h
  exact ⟨bytesV_lt (k := (stackArg a 3).toNat) (by omega), bytesV_lt (k := (stackArg a 5).toNat) (by omega),
    bytesV_lt (k := (stackArg a 7).toNat) (by omega), bytesV_lt (k := (stackArg a 9).toNat) (by omega)⟩

/-- Where the checks started, before `shape`. -/
abbrev XS (a t : State) : Prop := ∃ σ, FnBase 14 12 insK a σ ∧ Rest [.r0, .r1, .r2, .r3] σ t ∧ t.mem = σ.mem

theorem ck_bodyS_ct : RelCT isa
    (LiftB (PubF 14) fun a σ v s => s = σ ∧ FnBase 14 12 insK a σ ∧ BodyIn (geo 12 a) v s ∧ v = vK a)
    (keyBodyS 12 20 28 36)
    (LiftB (PubF 14) fun a σ _ t => FnBase 14 12 insK a σ ∧ ∃ A live c, Stg (geo 12 a) σ A live c t) := by
  unfold keyBodyS
  refine RelCT.seq (R := LiftB (PubF 14) ShapeOut) (pieceFB (nA := 14) (iS := 12) (ins := insK) [.r11] shape_taint
    (fun a σ v s ⟨e, b, _, _⟩ => by subst e; exact b.run)
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl
      rw [h₁.r11, h₂.r11, p.geo_eq (by decide)])
    fun a σ v s ⟨e, b, bi, ev⟩ => by
      subst e
      refine shape_ok b ?_ (by decide) fun t _ rt mt zt => ⟨b, bi, ev, rt, mt, zt⟩
      rw [bi.r11]
      exact BitVec.eq_of_toNat_eq (by simp [fK])) ?_
  refine RelCT.ite (fun s t ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ => by
    show some s.z = some t.z
    rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2, balanced_pub p]) ?_ ?_
  · refine (keyBodyW_ct (Pub := PubF 14) (gf := geo 12) (fun _ _ p => p.geo_eq (by decide)) XS).mono
      (fun s t ⟨⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩, hz⟩ => ?_)
      fun _ _ ⟨a₁, t₁, v₁, a₂, t₂, v₂, p, ⟨⟨σ₁, b₁, r₁, m₁⟩, A₁, l₁, c₁, u₁⟩, ⟨⟨σ₂, b₂, r₂, m₂⟩, A₂, l₂, c₂, u₂⟩⟩ =>
        ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, ⟨b₁, A₁, l₁, c₁, u₁.of_pre r₁ m₁⟩, ⟨b₂, A₂, l₂, c₂, u₂.of_pre r₂ m₂⟩⟩
    obtain ⟨b₁, bi₁, ev₁, r₁, m₁, z₁⟩ := h₁
    obtain ⟨b₂, bi₂, ev₂, r₂, m₂, z₂⟩ := h₂
    have hz' : s.z = true := Option.some.inj hz
    have B₁ : Balanced 12 a₁ := of_decide_eq_true (z₁ ▸ hz')
    have B₂ : Balanced 12 a₂ := of_decide_eq_true (by rw [← balanced_pub p]; exact z₁ ▸ hz')
    subst ev₁ ev₂
    exact ⟨a₁, s, _, a₂, t, _, p, ⟨rfl, ⟨σ₁, b₁, r₁, m₁⟩, bi₁.of_rest r₁ m₁, B₁.2.2.2.2, balanced_lt B₁⟩,
      ⟨rfl, ⟨σ₂, b₂, r₂, m₂⟩, bi₂.of_rest r₂ m₂, B₂.2.2.2.2, balanced_lt B₂⟩⟩
  · refine (keyBody_ct (Pub := PubF 14) (gf := geo 12) (fun _ _ p => p.geo_eq (by decide)) XS).mono
      (fun s t ⟨⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩, _⟩ =>
        ⟨a₁, s, v₁, a₂, t, v₂, p, ⟨rfl, ⟨σ₁, h₁.1, h₁.2.2.2.1, h₁.2.2.2.2.1⟩,
          h₁.2.1.of_rest h₁.2.2.2.1 h₁.2.2.2.2.1⟩,
          ⟨rfl, ⟨σ₂, h₂.1, h₂.2.2.2.1, h₂.2.2.2.2.1⟩, h₂.2.1.of_rest h₂.2.2.2.1 h₂.2.2.2.2.1⟩⟩)
      fun _ _ ⟨a₁, t₁, v₁, a₂, t₂, v₂, p, ⟨⟨σ₁, b₁, r₁, m₁⟩, _, _, _, _, _, _, _, _, _, _, _, A₁, l₁, u₁⟩,
        ⟨⟨σ₂, b₂, r₂, m₂⟩, _, _, _, _, _, _, _, _, _, _, _, A₂, l₂, u₂⟩⟩ =>
        ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, ⟨b₁, A₁, l₁, _, u₁.of_pre r₁ m₁⟩, ⟨b₂, A₂, l₂, _, u₂.of_pre r₂ m₂⟩⟩

theorem ck_contract_ct : ConstantTime isa (Spec.Rsa.checkKeyContract abi 0).pre
    (Spec.Rsa.checkKeyContract abi 0).pub VG.Impl.Rsa.Arm.CheckKey.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := ck_pre s hs
  have it := ck_pre t ht
  sig_pub [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hp
  have args : ∀ i < 14, stackArg s i = stackArg t i := fun i hi =>
    match i, hi with
    | 0, _ => a0 | 1, _ => a1 | 2, _ => a2 | 3, _ => a3 | 4, _ => a4 | 5, _ => a5
    | 6, _ => a6 | 7, _ => a7 | 8, _ => a8 | 9, _ => a9 | 10, _ => a10 | 11, _ => a11
    | 12, _ => a12 | 13, _ => a13
    | _ + 14, h => absurd h (by omega)
  rw [code_eq] at e1 e2
  exact (fn_ct (vf := vK) (by decide) (by decide) entry_taint restore_taint (fun σ _ => ck_hv σ)
    (fun _ h => ck_hA h) ck_bodyS_ct s t tr1 tr2 u v ⟨is, it, VG.Proof.Rsa.Arm.CheckCrtKey.pubF_of sp bytes p0 p1 p2 p3 args⟩ e1 e2).1

/-- A 64-byte modulus, one-byte exponents and factors, the working space at
`0x4000`, and the stack arguments at `0x8000`. -/
def ckSatState : State where
  gpr r := match r with
    | .r0 => 0x2000 | .r1 => 64 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x36 else if a = 0x8004 then 1 else if a = 0x8009 then 0x31
    else if a = 0x800C then 1 else if a = 0x8011 then 0x32 else if a = 0x8014 then 1
    else if a = 0x8019 then 0x33 else if a = 0x801C then 1 else if a = 0x8021 then 0x34
    else if a = 0x8024 then 1 else if a = 0x8029 then 0x35 else if a = 0x802C then 1
    else if a = 0x8031 then 0x40 else if a = 0x8034 then 0x20 else if a = 0x8035 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3600, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩,
    ⟨0x3500, 1⟩, ⟨0x8000, 56⟩]
  wr := [⟨0x4000, 8448⟩]

theorem ck_contract_sat : ∃ s, (Spec.Rsa.checkKeyContract abi 0).pre s := by
  sig_implies_sat [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr]
    [ckSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords]
    using ckSatState

/-- `vg_rsa_check_key`. -/
theorem check_key_verified :
    Verified target VG.Impl.Rsa.Arm.CheckKey.code (Spec.Rsa.checkKeyContract abi 0) :=
  ⟨ck_contract_correct, ck_contract_ct, ck_contract_sat⟩

/-- `vg_rsa_check_key_umaal`. -/
theorem check_key_umaal_verified :
    Verified target VG.Impl.Rsa.Arm.CheckKey.codeU (Spec.Rsa.checkKeyContract abi 0) :=
  VG.Proof.Bignum.Arm.umaalArithmetic_verified check_key_verified

end VG.Proof.Rsa.Arm.CheckKey
