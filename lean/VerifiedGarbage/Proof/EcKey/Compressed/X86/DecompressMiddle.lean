module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressFront
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Candidate
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Spec.EcKey.Compressed

import VerifiedGarbage.Proof.EcKey.Compressed.X86.Check
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Frame
import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Parity
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
import VerifiedGarbage.Proof.EcKey.Compressed.X86.SlotOps
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
import VerifiedGarbage.Proof.Ecdsa.X86.Layout
/-! # Coordinate recovery and final checks preserve the parsed encoding -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86/Select.lean`, which only this module imported.
section

/-! # Leave Montgomery form and choose between the two canonical roots -/

section

namespace VG.Proof.EcKey.Compressed.X86


open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86
open VG.Impl.Ecdh.X86 (QY W0)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

structure SelectPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkW c.MP' size c.C.p s'.mem base
  keep : Keeps clob s s'
  unch : Unch base (slWk c [QY, W0, TMP]) s.mem s'.mem
  lt : sv c base s' QY < c.C.p
  val : Fin.ofNat c.C.p (sv c base s' QY) =
    let y := toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
    if y.val % 2 = (s.mem.readW (off base (c.sl D)) 32).toNat % 2 then y else -y

theorem selectRoot_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONE = 1) (hZero : sv c base s ZERO = 0) :
    WP isa (Impl.EcKey.Compressed.X86.selectRoot c) s (SelectPost c base s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hY := sl_le c h7 (i := QY) (by decide)
  have hZ := sl_le c h7 (i := ZERO) (by decide)
  have hW := sl_le c h7 (i := W0) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  have hMP := sl_le c h7 (i := MP) (by decide)
  change WP isa (.seq (Mont.mulCall c.SP (c.sl QY) (c.sl ACC) (c.sl ONE))
    (.seq (Mont.subCall c.SP (c.sl W0) (c.sl ZERO) (c.sl QY))
      (.block (Impl.EcKey.Compressed.X86.parityMask c ++ sel (2 * c.n) (c.sl QY) (c.sl QY) (c.sl W0))))) s _
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) hc.fp h7 hs (o := QY) (a := ACC) (b := ONE)
    (by decide) (by decide) (by decide) (by rw [hOne]; omega))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have hM₁ := hM.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have normal : Fin.ofNat c.C.p (sv c base s₁ QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) :=
    toM_one_mul (unitMod_pow_two hc.p_odd (64 * c.n)) (by simpa only [hOne] using e₁)
  have normalVal : sv c base s₁ QY =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt lt₁] using congrArg Fin.val normal
  have zero₁ : sv c base s₁ ZERO = 0 :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hZero
  refine WP.seq (WP.mono (slSub_ok hc hs₁
    (o := W0) (a := ZERO) (b := QY) (by decide) (by decide) (by decide)
    (by rw [zero₁]; omega) lt₁) fun s₂ ⟨k₂, e₂⟩ => ?_)
  change sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p at e₂
  have hs₂ := k₂.scr hs₁
  have hM₂ := hM₁.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have y₂ : sv c base s₂ QY = sv c base s₁ QY :=
    sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  have negLt : sv c base s₂ W0 < c.C.p := by
    rw [e₂]
    exact Nat.mod_lt _ (by omega)
  have negVal : Fin.ofNat c.C.p (sv c base s₂ W0) = -(Fin.ofNat c.C.p (sv c base s₁ QY)) := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.neg_def]
    rw [show sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p from e₂,
      zero₁, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt lt₁]
  have U₁₂ : Unch base (slWk c [QY, W0, TMP]) s.mem s₂.mem :=
    unch_same (unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp))
      (unch_slots (MP'_n c) rfl k₂.unch (by simp) (by simp))
  have tag₂ : s₂.mem.readW (off base (c.sl D)) 32 = s.mem.readW (off base (c.sl D)) 32 :=
    VG.Proof.Ecdsa.X86.Unch.readW32 U₁₂ (fun w hw => by
      have := (apart_slWk (c := c) (l := [QY, W0, TMP]) (i := D) (by decide) (by decide) h7) w hw
      omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega) (by omega)) fun s₃ ⟨mask₃, k₃, m₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (sel_ok (decide (sv c base s₂ QY % 2 ≠ (s₂.mem.readW (off base (c.sl D)) 32).toNat % 2)) (2 * c.n) hs₃
    (by simpa only [mask32, decide_eq_true_eq] using mask₃)
    (by omega) (by omega) (by omega) (Or.inl (Nat.le_refl _))
    (by have := sl_apart c (i := QY) (j := W0) (by decide); omega)) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [show 4 * (2 * c.n) = 8 * c.n by omega] at O₄
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have hM₄ : ModOkW c.MP' size c.C.p s₄.mem base := modP_of hc (by
    rw [O₄.wordsVal (d := c.sl MP) (k := c.n)
      (sl_apart c (i := MP) (j := QY) (by decide)) (by omega), m₃]
    exact hM₂.val)
  have e₄' : sv c base s₄ QY =
      if sv c base s₂ QY % 2 ≠ (s₂.mem.readW (off base (c.sl D)) 32).toNat % 2 then
        sv c base s₂ W0 else sv c base s₂ QY := by
    simpa only [sv, wordsVal_eq_val32, m₃, decide_eq_true_eq] using e₄
  refine ⟨hs₄, hM₄, ?_, ?_, ?_, ?_⟩
  · exact (k₁.keeps.trans k₂.keeps).trans ((k₃.mono (by decide)).trans (k₄.mono (by decide)))
  · apply unch_same U₁₂
    rw [← m₃]
    exact (slot_frame (slots := [QY, W0, TMP]) (by simp) (by omega) O₄).mono
      (fun w hw => List.mem_append_left _ hw)
  · rw [e₄']
    split
    · exact negLt
    · rw [y₂]
      exact lt₁
  · change Fin.ofNat c.C.p (sv c base s₄ QY) =
      if (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (s.mem.readW (off base (c.sl D)) 32).toNat % 2 then _ else _
    rw [y₂, tag₂, normalVal] at e₄'
    by_cases hm : (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (s.mem.readW (off base (c.sl D)) 32).toNat % 2
    · rw [ite_eq_left hm]
      rw [ite_eq_right (not_not_intro hm)] at e₄'
      rw [e₄']
      exact Fin.ext (Nat.mod_eq_of_lt (toM _ _ _).isLt)
    · rw [ite_eq_right hm]
      rw [ite_eq_left hm] at e₄'
      rw [e₄', negVal, normal]

end VG.Proof.EcKey.Compressed.X86
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86
open VG.Impl.Ecdh.X86 (QY QYM R2P W0 W1 W2 W3)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.Impl.EcKey.Compressed (chooseRoot)

def keyRhs (c : Cfg) (s : State) : Spec.Weierstrass.Fe c.C :=
  let x := Fin.ofNat c.C.p (keyX c s)
  x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

def keyRoot (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :=
  chooseRoot (root (keyRhs c s)) ((s.mem (ptr s 1)).toNat % 2)

def CompressedAccept (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s : State) : Prop := CompressedPrefix c s ∧
  (keyRoot c root s * keyRoot c root s = keyRhs c s ∧
    (keyRoot c root s).val % 2 = (s.mem (ptr s 1)).toNat % 2)

instance (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :
    Decidable (CompressedAccept c root s) := inferInstanceAs (Decidable (_ ∧ (_ ∧ _)))

structure DecompressChecked (c : Cfg)
    (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s₀ : State) (s : State) : Prop where
  scr : Scr s (ptr s₀ 2) size
  saved : ∀ rd ∈ Cfg.saved, s.mem.readW (off (ptr s₀ 2) rd.2) 32 = s₀.gpr rd.1
  x : sv c (ptr s₀ 2) s E = keyX c s₀
  y : sv c (ptr s₀ 2) s QY = (keyRoot c root s₀).val
  flag : flagW c (ptr s₀ 2) s = mask32 (CompressedAccept c root s₀)
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressMiddle_ok {c : Cfg} (hc : CfgOk c)
    {root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C} (hroot : CandidateCorrect c root)
    {s₀ s : State} (F : DecompressFront c s₀ s) :
    WP isa (.seq (Impl.EcKey.Compressed.X86.rootCandidate c)
      (.seq (Impl.EcKey.Compressed.X86.selectRoot c)
        (Impl.EcKey.Compressed.X86.checkRoot c))) s (DecompressChecked c root s₀) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := F.scr.nowrap
  refine WP.seq (WP.mono (hroot _ s F.scr (modP_of hc F.fixed.mp) F.rhs_lt F.fixed.onep)
    fun s₁ C => ?_)
  have F₁ := F.frame hc C.keep C.unch (candidate_fixed hc) (by
    intro i hi
    have h : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 ∧ i ∉ candidateSlots := by decide
    exact candidate_apart hc (h i hi).1 (h i hi).2)
  have root₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c (ptr s₀ 2) s₁ ACC) = root (keyRhs c s₀) := by
    rw [C.val, F.rhs]; rfl
  refine WP.seq (WP.mono (selectRoot_ok hc F₁.scr (modP_of hc F₁.fixed.mp)
    F₁.fixed.one F₁.fixed.zero) fun s₂ S => ?_)
  have F₂ := F₁.frame hc (S.keep.mono (by decide)) S.unch
    (fixedOk_slWk (l := [QY, W0, TMP]) (by decide)) (by
      intro i hi
      have h : ∀ i ∈ [E, D, R2P, W2, FLAG], i ∉ [QY, W0, TMP] := by decide
      exact apart_slWk (by
        have H : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 := by decide
        exact H i hi) (h i hi))
  have y₂ : Fin.ofNat c.C.p (sv c (ptr s₀ 2) s₂ QY) = keyRoot c root s₀ := by
    rw [S.val, root₁, F₁.tag]
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
      (s₀.mem (ptr s₀ 1)).toNat < 2 ^ 32 from Nat.lt_trans (BitVec.isLt _) (by decide))]
    rfl
  have yval₂ : sv c (ptr s₀ 2) s₂ QY = (keyRoot c root s₀).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt S.lt] using congrArg Fin.val y₂
  refine WP.mono (checkRoot_ok hc F₂.scr (modP_of hc F₂.fixed.mp) S.lt
    F₂.rhs_lt F₂.r2 F₂.flag) fun s₃ K => ?_
  have F₃ := F₂.fixed.unch h7 hn
    (fixedOk_slWk (l := [QYM, W1, W3, TMP, FLAG]) (by decide)) K.unch
  have e₃ {i : Nat} (hi : i < 45) (hw : i ∉ [QYM, W1, W3, TMP, FLAG]) :
      sv c (ptr s₀ 2) s₃ i = sv c (ptr s₀ 2) s₂ i :=
    sv_unch K.unch h7 hn hi (apart_slWk hi hw)
  refine ⟨K.scr, F₃.saved,
    (e₃ (by decide) (by decide)).trans F₂.x,
    (e₃ (by decide) (by decide)).trans yval₂, ?_, (K.keep.1 _ (by decide)).trans F₂.esp,
    K.keep.2.1.trans F₂.rd, K.keep.2.2.trans F₂.wr⟩
  rw [K.flag, y₂, yval₂, F₂.rhs, F₂.tag]
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
    (s₀.mem (ptr s₀ 1)).toNat < 2 ^ 32 from Nat.lt_trans (BitVec.isLt _) (by decide))]
  simp only [mask32, CompressedAccept, keyRhs, and_assoc]

end VG.Proof.EcKey.Compressed.X86
