module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressFront
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Frame
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Candidate
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Select
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Check
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Spec.EcKey.Compressed

/-! # Coordinate recovery and final checks preserve the parsed encoding -/

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
