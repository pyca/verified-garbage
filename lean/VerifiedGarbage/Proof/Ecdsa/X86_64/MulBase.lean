import VerifiedGarbage.Proof.Ecdsa.X86_64.GMul
import VerifiedGarbage.Proof.Framework.X86_64.Spill

/-!
# `vg_<curve>_mul_base`'s body on x86-64

`Cfg.mulBaseBody`: the table of `k`'s bits (`bits_ok`), from the scalar in
`K`'s slot, then `[k]G` into `R` by the comb (`gMulComb_ok'`, `tcomb_ok`),
which reads `p` and zero and writes only its slots, `b R mod p` in `EM` and
the word past the table (`mulBaseBody_ok`): what `gMulK_ok` gives, from
`p`, zero and the curve's tables alone. `Cfg.mulBaseFn` runs it between
saving the callee-saved registers in `ACC`'s slot and restoring them
(`mulBaseFn_ok`).
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- `R = [k]G` for the `k` in `K`'s slot, with the table of its bits, from
`p`, zero and the comb's tables, for a curve whose comb has complete
additions (`jac = false`). -/
theorem mulBaseBody_ok (hc : BaseCfgOk c) (hC : Law c.C) (hT : CombTbls c) {d : CombData}
    (hcd : c.comb = some d) (hj : d.jac = false) {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : wordsVal s.mem base (c.sl MP) c.n = c.C.p) (hz : wordsVal s.mem base (c.sl ZERO) c.n = 0)
    (hTM : TblMem s (s.syms d.tsym) (c.combWords d))
    (hout : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base (s.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    WP isa c.mulBaseBody.inline s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul (wordsVal s.mem base (c.sl K) c.n) (G c.C)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : bitsAt c.n 0 + 64 * c.n ≤ size := bitsAt_le c h7 (j := 0) (by decide)
  show WP isa (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) c.gMulK.inline) s _
  -- The table of `k`'s bits.
  refine WP.seq (WP.mono_syms (bits_ok hs h0 (by omega) (sl_le c h7 (i := K) (by decide)) hsz
    (Or.inl (by have := sl_below_bits c (i := K) (by decide) 0 0 (.inl (by decide)); omega)))
    fun s₁ ⟨b₁, k₁, O₁⟩ sy₁ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n + 8)] s.mem s₁.mem := fun x hx =>
    O₁ x (by have := hx _ (List.mem_singleton_self _); dsimp only at this; omega)
  have hap : ∀ {i}, i < 45 → ∀ w ∈ [(bitsAt c.n 0, 64 * c.n + 8)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
    fun hi => apart_pad hi
  have hmp₁ : wordsVal s₁.mem base (c.sl MP) c.n = c.C.p :=
    (sv_unch U₁ h7 hn (i := MP) (by decide) (hap (by decide))).trans hmp
  have hz₁ : wordsVal s₁.mem base (c.sl ZERO) c.n = 0 :=
    (sv_unch U₁ h7 hn (i := ZERO) (by decide) (hap (by decide))).trans hz
  have hTM₁ : TblMem s₁ (s.syms d.tsym) (c.combWords d) :=
    hTM.of_unch (by rw [k₁.rd, k₁.wr]) U₁ (fun w hw => by
      rw [List.mem_singleton.mp hw]; have := bitsAt_le c h7 (j := 1) (by decide)
      rw [bitsAt_eq] at this ⊢; dsimp only; omega) hout
  have hgK : c.gMulK = c.gMul := by unfold Cfg.gMulK; rw [hcd]; simp only [hj, Bool.false_eq_true, ↓reduceIte]
  rw [hgK]
  unfold Cfg.gMul
  rw [hcd]
  refine WP.mono (gMulComb_ok' hc hcd hs₁ hmp₁ hz₁ (wordsVal_lt _ _ _ _) b₁ (by rw [sy₁]; exact hTM₁)
    (by rw [sy₁]; exact hout) fun s₂ hs₂ hM₂ hF =>
      tcomb_ok (tcombLay hc (hc.comb d hcd)) hC (hc.comb_am3 d hcd) hc.onG (tcombVals hc hC (hT d hcd).1)
        hc.p_lt hs₂ hM₂ hF false)
    fun s' ⟨K', U', M', L', R'⟩ => ⟨?_, ?_, M', L', R'⟩
  · refine (k₁.mono fun r hr => ?_).trans K'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
  · refine Unch.cover (U₁.trans U') fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · exact ⟨w, List.mem_append_right _ hw, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩

/-- `saveMem` of slots in `[o, o + L)` of `base` changes nothing else of the
working space. -/
theorem saveMem_unch (m : Mem) (base : Addr) (g : Reg → BitVec 64) {o L : Nat}
    (l : List (Reg × Nat)) (h : ∀ p ∈ l, o ≤ p.2 ∧ p.2 + 8 ≤ o + L) (hL : o + L < 2 ^ 64) :
    Unch base [(o, L)] m (Spill.saveMem m base g l) := by
  intro x hx
  refine Spill.saveMem_frame (r := ⟨base + BitVec.ofNat 64 o, L⟩) m base g l
    (fun p hp => Offset.contains base (h p hp).1 (h p hp).2 hL) x fun r hr hc => ?_
  rw [List.mem_singleton.mp hr] at hc
  have hx' := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  have := (Offset.lt_iff x base (d := o) (n := L) (by omega)).mp (by omega)
  simp only [ofs] at hx'
  omega

theorem mulBaseSaved_slots (h6 : 6 ≤ c.n) :
    ∀ p ∈ c.mulBaseSaved, c.sl ACC ≤ p.2 ∧ p.2 + 8 ≤ c.sl ACC + 8 * c.n := by
  intro p hp
  simp only [Cfg.mulBaseSaved, Cfg.saved, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem mulBaseSaved_spill (hc : BaseCfgOk c) : Spill.Slots c.mulBaseSaved := by
  have := sl_le c hc.n10 (i := ACC) (by decide)
  have hsz : size = 8192 := rfl
  refine ⟨fun p hp => ?_, ?_⟩
  · simp only [Cfg.mulBaseSaved, Cfg.saved, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
  · simp only [Cfg.mulBaseSaved, Cfg.saved, List.map_cons, List.map_nil, List.pairwise_cons,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil,
      false_implies, implies_true, and_true]
    omega

/-- `vg_<curve>_mul_base`, for a curve of at least six words (whose `ACC`
slot holds the six registers): the callee-saved registers kept (saved in
`ACC`'s slot and restored), and what its body gives (`mulBaseBody_ok`),
having written also `ACC`'s slot. -/
theorem mulBaseFn_ok (hc : BaseCfgOk c) (h6 : 6 ≤ c.n) (hC : Law c.C) (hT : CombTbls c) {d : CombData}
    (hcd : c.comb = some d) (hj : d.jac = false) {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : wordsVal s.mem base (c.sl MP) c.n = c.C.p) (hz : wordsVal s.mem base (c.sl ZERO) c.n = 0)
    (hTM : TblMem s (s.syms d.tsym) (c.combWords d))
    (hout : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base (s.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    WP isa c.mulBaseFn.inline s fun s' => (∀ r, r ∉ powClob c.n → s'.gpr r = s.gpr r) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.syms = s.syms ∧ Unch base (gW c ++ slW c [ACC]) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul (wordsVal s.mem base (c.sl K) c.n) (G c.C)) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hacc := sl_le c h7 (i := ACC) (by decide)
  have hsl := mulBaseSaved_slots (c := c) h6
  show WP isa (.seq (.block (Spill.saveCode .rdi c.mulBaseSaved)) (.seq c.mulBaseBody.inline
    (.block (Spill.restoreCode .rdi c.mulBaseSaved)))) s _
  -- Save.
  refine WP.seq (WP.mono_syms (Spill.save_ok .rdi c.mulBaseSaved s fun p hp => ?_)
    fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ sy₁ => ?_)
  · rw [hs.rdi]
    have := (hsl p hp).2
    exact ⟨_, hs.wr, Offset.contains_base base (by omega) (by omega)⟩
  rw [hs.rdi] at m₁
  have U₁ : Unch base (slW c [ACC]) s.mem s₁.mem := m₁ ▸ saveMem_unch _ _ _ _ hsl (by omega)
  have sv₁ : Spill.Saved s₁.mem base s.gpr c.mulBaseSaved :=
    m₁ ▸ Spill.saveMem_saved _ _ _ _ (mulBaseSaved_spill hc)
  have hs₁ : Scr s₁ base size := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hn⟩
  have hmp₁ : wordsVal s₁.mem base (c.sl MP) c.n = c.C.p :=
    (sv_unch U₁ h7 hn (i := MP) (by decide) (apart_slW (by decide))).trans hmp
  have hz₁ : wordsVal s₁.mem base (c.sl ZERO) c.n = 0 :=
    (sv_unch U₁ h7 hn (i := ZERO) (by decide) (apart_slW (by decide))).trans hz
  have hk₁ : wordsVal s₁.mem base (c.sl K) c.n = wordsVal s.mem base (c.sl K) c.n :=
    sv_unch U₁ h7 hn (i := K) (by decide) (apart_slW (by decide))
  have hTM₁ : TblMem s₁ (s₁.syms d.tsym) (c.combWords d) := by
    rw [sy₁]
    exact hTM.of_unch (by rw [rd₁, wr₁]) U₁ (fun w hw => by
      simp only [slW, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rw [hw]; dsimp only; omega) hout
  -- The body.
  refine WP.seq (WP.mono_syms (mulBaseBody_ok hc hC hT hcd hj hs₁ hmp₁ hz₁ hTM₁
    (by rw [sy₁]; exact hout)) fun s₂ ⟨K₂, U₂, M₂, L₂, R₂⟩ sy₂ => ?_)
  rw [hk₁] at R₂
  have sv₂ : Spill.Saved s₂.mem base s.gpr c.mulBaseSaved := fun p hp => by
    have := hsl p hp
    refine (U₂.word (d := p.2) (fun w hw => ?_) (by omega)).trans (sv₁ p hp)
    rcases apart_gW (c := c) (i := ACC) (by decide) (by decide) w hw with h | h <;> [left; right] <;> omega
  have rdi₂ : s₂.gpr .rdi = base := by rw [K₂.gpr _ (rdi_not_powClob _), g₁, hs.rdi]
  -- Restore.
  refine WP.mono_syms (Spill.restore_ok .rdi c.mulBaseSaved s.gpr s₂ (by
      simp [Cfg.mulBaseSaved, Cfg.saved]) (fun p hp => ?_) (by rw [rdi₂]; exact sv₂))
    fun s' ⟨gs, go, ms, rds, wrs⟩ sy' => ?_
  · rw [rdi₂, K₂.wr, wr₁]
    have := (hsl p hp).2
    exact ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base base (by omega) (by omega)⟩
  have hsv : c.mulBaseSaved.map Prod.fst = Cfg.saved.map Prod.fst := by
    simp [Cfg.mulBaseSaved, Cfg.saved]
  rw [hsv] at gs go
  refine ⟨fun r hr => ?_, gs, by rw [rds, K₂.rd, rd₁], by rw [wrs, K₂.wr, wr₁], ?_, ?_,
    by rw [ms]; exact M₂, by rw [ms]; exact L₂, ?_⟩
  · by_cases h : r ∈ Cfg.saved.map Prod.fst
    · exact gs r h
    · rw [go r h, K₂.gpr r hr, g₁]
  · rw [sy', sy₂, sy₁]
  · refine Unch.mono (ms ▸ U₁.trans U₂ : Unch base (slW c [ACC] ++ gW c) s.mem s'.mem) fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · exact List.mem_append_right _ hw
    · exact List.mem_append_left _ hw
  · have e : ∀ x, tmv c.C c.n base s' x = tmv c.C c.n base s₂ x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [ms]
    rw [e, e, e]; exact R₂

/-! ## `R = [k]G` in the signature and the public key: `gMulKC` -/

/-- What a call of `vg_<curve>_mul_base` needs of the curve: a comb, with
complete additions, at least six words (so that `ACC`'s slot holds the six
callee-saved registers), and products written out (the function calls no
other). -/
def MulBaseOk (c : Cfg) : Prop :=
  c.mulBase.isSome = true → ∃ d, c.comb = some d ∧ d.jac = false ∧ 6 ≤ c.n ∧ c.mulBaseFn.noCalls = true

/-- What `gMulKC` may write: `gMulK`'s, and `ACC`'s slot. -/
abbrev gWA (c : Cfg) : List (Nat × Nat) := gW c ++ slW c [ACC]

theorem apart_gWA {i : Nat} (hi : i < 45)
    (hl : i ∉ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM]) (ha : i ∉ [ACC]) :
    ∀ w ∈ gWA c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_gW hi hl) (apart_slW ha)

theorem fixedOk_gWA : FixedOk c (gWA c) :=
  FixedOk.append fixedOk_gW (fixedOk_slW (by decide))

theorem tbl_apart_gWA {j t : Nat} (hj : j = 1 ∨ j = 2) (ht : t < 64 * c.n)
    (hj1 : j ≠ 1 ∨ c.n ≠ 9 := by sl_or) :
    ∀ w ∈ gWA c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_gW hj ht hj1) (tbl_apart_slW (by decide) j t ht (.inl (by decide)))

theorem flag_unch_gWA {base : Addr} {m m' : Mem} (hu : Unch base (gWA c) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega)
  rcases apart_gWA (c := c) (i := FLAG) (by decide) (by decide) (by decide) w hw with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- `R = [k]G` for a secret `k`, after the setup and the tables (but `k`'s
if `vg_<curve>_mul_base` makes it): by its call, or inline (`gMulK_ok`). -/
theorem gMulKC_ok (hc : BaseCfgOk c) (hmb : MulBaseOk c) (hC : Law c.C) (hT : CombTbls c) {hs : Option Nat}
    {s₀ : State} (hp : Pre c s₀) {s : State} (hS : St₁ c hs s₀ (s₀.gpr .r8) s c.mulBase.isSome) :
    WP isa c.gMulKC.inline s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch (s₀.gpr .r8) (gWA c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem (s₀.gpr .r8) ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem (s₀.gpr .r8) x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RX)) (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RY))
        (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RZ)) (mul (kv c s₀) (G c.C)) := by
  unfold Cfg.gMulKC
  cases hm : c.mulBase with
  | none =>
    rw [hm] at hS
    exact WP.mono (gMulK_ok hc hC hT hp hS) fun s' ⟨K', U', M', L', R'⟩ =>
      ⟨K', U'.mono fun w hw => List.mem_append_left _ hw, M', L', R'⟩
  | some C =>
    obtain ⟨d, hcd, hj, h6, hnc⟩ := hmb (by rw [hm]; rfl)
    obtain ⟨hTM, hout⟩ := tbl_of hcd hp hS.rd hS.unch
    rw [← hS.syms] at hTM hout
    show WP isa c.mulBaseFn s _
    rw [← Code.inline_of_noCalls hnc]
    refine WP.mono (mulBaseFn_ok hc h6 hC hT hcd hj hS.scr hS.fixed.mp hS.fixed.zero hTM hout)
      fun s' ⟨g', _, rd', wr', _, U', M', L', R'⟩ => ⟨⟨g', rd', wr'⟩, U', M', L', ?_⟩
    rw [← hS.k]; exact R'

end VG.Proof.Ecdsa.X86_64
