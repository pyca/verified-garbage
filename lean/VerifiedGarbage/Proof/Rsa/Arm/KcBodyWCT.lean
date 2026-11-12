module

public import VerifiedGarbage.Proof.Rsa.Arm.KcBodyW
public import VerifiedGarbage.Proof.Rsa.Arm.KcCT
public import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
public import VerifiedGarbage.Proof.Rsa.Arm.KcTaintW
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # The checks of a balanced RSA key on ARMv7: constant time

`keyBodyW_ct`: as `keyBody_ct`, two runs of `keyBodyW` related at every step
by what correctness says of each. Between its pieces each run is `StW`: some
`Stg` on a known list of live arrays, with `p`, `q` (and later `p - 1`, `q - 1`,
and the divisor of a division) of `w / 2` words, which is what the products
and divisions by words need (`KeyDiv.mulLo_ct`, `KeyDiv.divW_ct`); the other
pieces the taint analysis checks (`KcTaintW.lean`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- `w / 2` words. -/
abbrev Bd (g : Geo) : Nat := 2 ^ (32 * (g.w / 2))

/-- From the start: the zero array, `p` and `q` of `w / 2` words. -/
def M0 (g : Geo) (A : Nat → Nat) : Prop := A aZ = 0 ∧ A aP < Bd g ∧ A aQ < Bd g
/-- After the checks of `dP` and `dQ`: also `p - 1` and `q - 1`. -/
def M1 (g : Geo) (A : Nat → Nat) : Prop := M0 g A ∧ A aM1 < Bd g ∧ A aM2 < Bd g
/-- Before a division: also its divisor, with its top word not zero. -/
def MD (g : Geo) (A : Nat → Nat) : Prop := M1 g A ∧ A aVD < Bd g ∧ 2 ^ (32 * (g.w / 2 - 1)) ≤ A aVD

/-- A run between the pieces: `Stg` on the arrays `L`, its values `M`. -/
def StW (g : Geo) (σ : State) (L : List Nat) (M : (Nat → Nat) → Prop) (s : State) : Prop :=
  ∃ A c, Stg g σ A L c s ∧ M A

theorem M0_upd {g : Geo} {A : Nat → Nat} (h : M0 g A) {o : Nat} (z : Nat) (h1 : aZ ≠ o) (h2 : aP ≠ o)
    (h3 : aQ ≠ o) : M0 g (upd A o z) := by
  obtain ⟨a, b, c⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [upd_ne _ _ h1]; exact a
  · rw [upd_ne _ _ h2]; exact b
  · rw [upd_ne _ _ h3]; exact c

theorem M1_upd {g : Geo} {A : Nat → Nat} (h : M1 g A) {o : Nat} (z : Nat) (h1 : aZ ≠ o) (h2 : aP ≠ o)
    (h3 : aQ ≠ o) (h4 : aM1 ≠ o) (h5 : aM2 ≠ o) : M1 g (upd A o z) := by
  obtain ⟨m, d, e⟩ := h
  refine ⟨M0_upd m z h1 h2 h3, ?_, ?_⟩
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

theorem stw_start {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) (hp : v.p < Bd g) (hq : v.q < Bd g) :
    WP isa startW s (StW g s live0 (M0 g)) :=
  WP.mono (first_ok h) fun _ ht => ⟨_, _, ht, rfl, hp, hq⟩

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

/-- The list of arrays after the checks of `dP`, `dQ` and `qInv < p`. -/
abbrev L2 : List Nat := aA :: aA :: aM2 :: aM1 :: aVQ :: live0

theorem stw_chunk1 {g : Geo} {σ s : State} (h : StW g σ (aVQ :: live0) (M0 g) s) :
    WP isa (seqs chunk1) s (StW g σ L2 (M1 g)) := by
  obtain ⟨A, c, h1, hm⟩ := h
  obtain ⟨m0, mp, mq⟩ := hm
  unfold chunk1
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
      ↓reduceIte]
    omega
  have M6 := hA0 _ rfl
  -- `dP`.
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h6.ltA_ok (a := aDP) (b := aM1) (by decide) (by decide) (by decide)) fun t7 h7 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h7.mulA_ok (y := aE) (x := aDP) (m := aM1) (k := 33) (by decide) (by decide) (by decide)
    (by decide) (by rw [M6.1.1]) mulIdx_m1 (by decide) (by decide) (by decide) (by decide) fun u _ => cnt33_ok u)
    fun t8 ⟨R₁, _, h8⟩ => ?_
  have M8 := M1_upd M6 (o := aA) R₁ (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h8.eqA_ok (a := aA) (b := aOne) (by decide) (by decide) (by decide)) fun t9 h9 => ?_
  -- `dQ`.
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h9.ltA_ok (a := aDQ) (b := aM2) (by decide) (by decide) (by decide)) fun t10 h10 => ?_
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h10.mulA_ok (y := aE) (x := aDQ) (m := aM2) (k := 33) (by decide) (by decide) (by decide)
    (by decide) (by rw [M8.1.1]) mulIdx_m2 (by decide) (by decide) (by decide) (by decide) fun u _ => cnt33_ok u)
    fun t11 ⟨R₂, _, h11⟩ => ?_
  have M11 := M1_upd M8 (o := aA) R₂ (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [wp_seqs_append (by ne_nil) (by ne_nil)]
  refine WP.mono (h11.eqA_ok (a := aA) (b := aOne) (by decide) (by decide) (by decide)) fun t12 h12 => ?_
  exact WP.mono (h12.ltA_ok (a := aQI) (b := aP) (by decide) (by decide) (by decide)) fun _ h13 =>
    ⟨_, _, h13, M11⟩

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

theorem exec_seq_inv {a b : Prog isa} {s s' : State} {tr : List Leak} (h : Exec isa (.seq a b) s tr s') :
    ∃ u tr₁ tr₂, tr = tr₁ ++ tr₂ ∧ Exec isa a s tr₁ u ∧ Exec isa b u tr₂ s' := by
  cases h with
  | seq e₁ e₂ => exact ⟨_, _, _, rfl, e₁, e₂⟩

theorem exec_seqs_append {l₂ : List (Prog isa)} (h₂ : l₂ ≠ []) :
    ∀ {l₁ : List (Prog isa)}, l₁ ≠ [] → ∀ {s : State} {tr s'},
      Exec isa (seqs (l₁ ++ l₂)) s tr s' → Exec isa (.seq (seqs l₁) (seqs l₂)) s tr s' := by
  intro l₁
  induction l₁ with
  | nil => intro h; exact absurd rfl h
  | cons c l ih =>
    intro _ s tr s' e
    rcases l with _ | ⟨d, l⟩
    · obtain ⟨x, l₂', rfl⟩ := List.exists_cons_of_ne_nil h₂
      exact e
    · obtain ⟨u, tr₁, tr₂, rfl, e₁, e₂⟩ := exec_seq_inv (a := c) (b := seqs ((d :: l) ++ l₂)) e
      obtain ⟨u', tr₃, tr₄, rfl, e₃, e₄⟩ := exec_seq_inv (ih (List.cons_ne_nil _ _) e₂)
      rw [← List.append_assoc]
      exact .seq (.seq e₁ e₃) e₄

theorem exec_seqs_join : ∀ {ls : List (List (Prog isa))}, (∀ l ∈ ls, l ≠ []) → ls ≠ [] → ∀ {s : State} {tr s'},
    Exec isa (seqs ls.flatten) s tr s' → Exec isa (seqs (ls.map seqs)) s tr s' := by
  intro ls
  induction ls with
  | nil => intro _ h; exact absurd rfl h
  | cons l rest ih =>
    intro h _ s tr s' e
    rcases rest with _ | ⟨l', rest⟩
    · rw [List.flatten_cons, List.flatten_nil, List.append_nil] at e
      exact e
    · rw [List.flatten_cons] at e
      have ne : (l' :: rest).flatten ≠ [] := by
        rw [List.flatten_cons]
        exact List.append_ne_nil_of_left_ne_nil (h l' (by simp)) _
      obtain ⟨u, tr₁, tr₂, rfl, e₁, e₂⟩ := exec_seq_inv (exec_seqs_append ne (h l (by simp)) e)
      exact .seq e₁ (ih (fun l hl => h l (List.mem_cons_of_mem _ hl)) (List.cons_ne_nil _ _) e₂)

theorem RelCT.of_join {P Q : State → State → Prop} {ls : List (List (Prog isa))} (h₁ : ∀ l ∈ ls, l ≠ [])
    (h₂ : ls ≠ []) (h : RelCT isa P (seqs (ls.map seqs)) Q) : RelCT isa P (seqs ls.flatten) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_seqs_join h₁ h₂ e₁) (exec_seqs_join h₁ h₂ e₂)

/-- `keyBodyW`, in the pieces of its proof of constant time. -/
abbrev partsW : List (List (Prog isa)) :=
  [[startW], [VG.Impl.Rsa.Arm.KeyDiv.mulLo aVQ aP aQ], chunk1, [VG.Impl.Rsa.Arm.KeyDiv.mulLo aT aQ aQI],
    [copy aVD aP, .block (VG.Impl.Rsa.Arm.KeyDiv.fixTop aVD)],
    [VG.Impl.Rsa.Arm.KeyDiv.divW aT aVR aVD aVT aY aX], eqA aVR aOne ++ ltA aD aN,
    [copy aVD aM1, .block (VG.Impl.Rsa.Arm.KeyDiv.fixTop aVD)],
    [VG.Impl.Rsa.Arm.KeyDiv.divW aD aVR aVD aVT aY aX], eqA aVR aDP,
    [copy aVD aM2, .block (VG.Impl.Rsa.Arm.KeyDiv.fixTop aVD)],
    [VG.Impl.Rsa.Arm.KeyDiv.divW aD aVR aVD aVT aY aX], eqA aVR aDQ]

theorem keyBodyW_parts : keyBodyW = seqs partsW.flatten := by
  simp only [keyBodyW, crtChecksW, dChecksW, divK, partsW, chunk1, List.flatten_cons, List.flatten_nil,
    List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

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

theorem seqs_single (c : Prog isa) : seqs [c] = c := rfl

theorem stw_eqLt {g : Geo} {σ s : State} {L : List Nat} {M : (Nat → Nat) → Prop} (h : StW g σ L M s)
    (hW : aW ∉ L) {a b c d : Nat} (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hd : d ∈ L) :
    WP isa (seqs (eqA a b ++ ltA c d)) s (StW g σ L M) := by
  rw [wp_seqs_append (by unfold eqA; exact List.cons_ne_nil _ _) (by unfold ltA; exact List.cons_ne_nil _ _)]
  exact WP.mono (stw_eqA h ha hb hW) fun _ h' => stw_ltA h' hc hd hW

abbrev L4 : List Nat := aVR :: aVD :: aT :: L2
abbrev L5 : List Nat := aVR :: aVD :: L4
abbrev L6 : List Nat := aVR :: aVD :: L5

section
variable {α : Type} {Pub : α → α → Prop} {gf : α → Geo} (hg : ∀ a₁ a₂, Pub a₁ a₂ → gf a₁ = gf a₂)
  (X : α → State → Prop)
include hg

/-- `keyBodyW` is constant time, for a balanced key. -/
theorem keyBodyW_ct : RelCT isa (LiftB Pub fun a σ v s => s = σ ∧ X a σ ∧ BodyIn (gf a) v s ∧
      (gf a).w % 2 = 0 ∧ v.p < Bd (gf a) ∧ v.q < Bd (gf a)) keyBodyW
    (LiftB Pub fun a σ _ t => X a σ ∧ ∃ A live c, Stg (gf a) σ A live c t) := by
  rw [keyBodyW_parts]
  refine RelCT.of_join (fun l hl => by
    simp only [partsW, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ne_nil)
    (List.cons_ne_nil _ _) ?_
  simp only [partsW, List.map_cons, List.map_nil, seqs_single]
  refine RelCT.seq (R := LiftB Pub (FW (gf := gf) X live0 M0)) (pieceB [.r8, .r11] startW_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p h₁ h₂ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [h₁.2.2.1.r8, h₂.2.2.1.r8, hg _ _ p]
      · rw [h₁.2.2.1.r11, h₂.2.2.1.r11, hg _ _ p])
    fun a σ v s ⟨e, x, h, hw, hp, hq⟩ => by
      subst e
      have kb := h.kb
      exact WP.mono (stw_start h hp hq) fun t ht => ⟨⟨x, hw, by simp only [Geo.w]; omega⟩, ht⟩) ?_
  refine RelCT.seq (mulPieceB hg X VG.Proof.Rsa.Arm.KeyCheck.mulVQ_taint (L := live0) (M := M0) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ h => ⟨h.1, h.2.1⟩) fun _ _ z h => M0_upd h z (by decide) (by decide) (by decide)) ?_
  refine RelCT.seq (wPieceB hg X chunk1_taint (L := aVQ :: live0) (M := M0) (L' := L2) (M' := M1)
    fun _ _ _ _ _ h => stw_chunk1 h) ?_
  refine RelCT.seq (mulPieceB hg X mulT_taint (L := L2) (M := M1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ h => ⟨h.1.1, h.1.2.2⟩)
    fun _ _ z h => M1_upd h z (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  -- `q qInv mod p`.
  refine RelCT.seq (wPieceB hg X divSetP_taint (L := aT :: L2) (M := M1) (L' := aVD :: aT :: L2) (M' := MD)
    fun _ _ _ _ hw6 h => stw_divSet h (d := aP) (by decide) (by decide) (fun _ h => h.1.2.1) (by omega)) ?_
  refine RelCT.seq (divWPieceB hg X divT_taint (L := aVD :: aT :: L2) (by decide) (by decide) (by decide)
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
