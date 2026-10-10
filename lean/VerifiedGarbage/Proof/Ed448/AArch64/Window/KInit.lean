import VerifiedGarbage.Proof.Ed448.AArch64.Window.KLoop
import VerifiedGarbage.Proof.Ed448.AArch64.Window.CopyK

/-!
# Ed448 verification on AArch64: the windows

Untrusted: everything here is checked by Lean. `kInit`: `Q` (slots 3–5) the
neutral point, 1 in slot 20 and the counter at 57 (`kInit_ok`); then the
loop over the challenge's bytes (`kWindows_ok`).
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC)
open VG.Impl.X448.AArch64.Base (constSlot limb)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt constSlot_ok bnd_of_words F_of_words limb_lt)
open VG.Spec.Ed448 (Point)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

theorem kInit_eq : kInit = constSlot (slot 3) 0 ++ (constSlot (slot 4) 1 ++ (constSlot (slot 5) 1 ++
    (constSlot (slot 20) 1 ++ ([.movz .x .x19 (BitVec.ofNat 16 57) 0] : List Instr)))) := by
  simp only [kInit, List.append_assoc]; rfl

theorem kInit_ok {s : State} {base : Addr} {P S : Point} (hs : Scr s base) (hb : BEnv s.mem base)
    (hz : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0) (ht : TabOk s.mem base P 16)
    (hS : pt (EV s.mem base) 0 1 2 = S) :
    WP isa (.block kInit) s fun t => KInv t base P S 57 t ∧ Outside2 base 64 2816 ACC 1152 s.mem t.mem ∧
      t.gpr .x20 = s.gpr .x20 ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [kInit_eq, WP.block_append_iff]
  refine WP.mono (constSlot_ok hs (o := slot 3) (by decide) (by decide) 0) fun t1 ⟨v1, o1, k1⟩ => ?_
  have h1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h1 (o := slot 4) (by decide) (by decide) 1) fun t2 ⟨v2, o2, k2⟩ => ?_
  have h2 := h1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h2 (o := slot 5) (by decide) (by decide) 1) fun t3 ⟨v3, o3, k3⟩ => ?_
  have h3 := h2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h3 (o := slot 20) (by decide) (by decide) 1) fun t4 ⟨v4, o4, k4⟩ => ?_
  have h4 := h3.of_keeps k4 (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok t4 57 (by decide)) fun t ⟨ct, gt, mt, rdt, wrt⟩ => ?_
  have hst : Scr t base := ⟨(gt _ (by decide)).trans h4.x3, (gt _ (by decide)).trans h4.mask, wrt ▸ h4.wr, h4.nowrap⟩
  -- Which slots each store keeps.
  have O : ∀ i : Index, i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 20 → ∀ j < 8,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := fun i h3 h4 h5 h20 j hj => by
    have := i.isLt
    have n3 : i.val ≠ 3 := fun e => h3 (Fin.ext e)
    have n4 : i.val ≠ 4 := fun e => h4 (Fin.ext e)
    have n5 : i.val ≠ 5 := fun e => h5 (Fin.ext e)
    have n20 : i.val ≠ 20 := fun e => h20 (Fin.ext e)
    rw [mt, o4.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
      o3.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
      o2.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega),
      o1.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega)]
  have w3 : ∀ w < 8, word t.mem base (slot 3 + 8 * w) = limb 0 w := fun w hw => by
    rw [mt, o4.word (Or.inl (by simp only [slot]; omega)) (by simp only [slot]; omega),
      o3.word (Or.inl (by simp only [slot]; omega)) (by simp only [slot]; omega),
      o2.word (Or.inl (by simp only [slot]; omega)) (by simp only [slot]; omega)]
    exact v1 w hw
  have w4 : ∀ w < 8, word t.mem base (slot 4 + 8 * w) = limb 1 w := fun w hw => by
    rw [mt, o4.word (Or.inl (by simp only [slot]; omega)) (by simp only [slot]; omega),
      o3.word (Or.inl (by simp only [slot]; omega)) (by simp only [slot]; omega)]
    exact v2 w hw
  have w5 : ∀ w < 8, word t.mem base (slot 5 + 8 * w) = limb 1 w := fun w hw => by
    rw [mt, o4.word (Or.inl (by simp only [slot]; omega)) (by simp only [slot]; omega)]
    exact v3 w hw
  have w20 : ∀ w < 8, word t.mem base (slot 20 + 8 * w) = limb 1 w := fun w hw => by rw [mt]; exact v4 w hw
  have oSt : Outside2 base 64 2816 ACC 1152 s.mem t.mem := fun x a _ => by
    rw [mt, o4 x (by simp only [slot] at a ⊢; omega), o3 x (by simp only [slot] at a ⊢; omega),
      o2 x (by simp only [slot] at a ⊢; omega), o1 x (by simp only [slot] at a ⊢; omega)]
  have eO : ∀ i : Index, i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 20 → EV t.mem base i = EV s.mem base i :=
    fun i a b c d => congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (O i a b c d))
  have benv : BEnv t.mem base := by
    intro i
    by_cases h : i ≠ 3 ∧ i ≠ 4 ∧ i ≠ 5 ∧ i ≠ 20
    · exact fun j hj => by rw [O i h.1 h.2.1 h.2.2.1 h.2.2.2 j hj]; exact hb i j hj
    · have : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 20 := by
        by_contra hc; simp only [not_or] at hc; exact h ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
      rcases this with rfl | rfl | rfl | rfl
      · exact bnd_of_words w3
      · exact bnd_of_words w4
      · exact bnd_of_words w5
      · exact bnd_of_words w20
  have z19 : ∀ w < 8, limbs t.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [O 19 (by decide) (by decide) (by decide) (by decide) w hw]; exact hz w hw
  refine ⟨⟨by decide, ⟨hst, benv, z19, F_of_words w20, fun w hw => ?_, ht.of_outside2 oSt (by decide), rfl, rfl, rfl,
      Outside2.refl _ _ _ _ _ _⟩, ct, ?_, ?_⟩, oSt, ?_, ?_, ?_⟩
  · show (word t.mem base (slot 5 + 8 * w)).toNat < Mb
    rw [w5 w hw]; exact Nat.lt_of_lt_of_le (limb_lt _ _) (by decide)
  · show (⟨FV t.mem base (slot 3), FV t.mem base (slot 4), FV t.mem base (slot 5)⟩ : Point) = ⟨0, 1, 1⟩
    rw [F_of_words w3, F_of_words w4, F_of_words w5]
  · rw [← hS]; simp only [pt]
    rw [eO 0 (by decide) (by decide) (by decide) (by decide), eO 1 (by decide) (by decide) (by decide) (by decide),
      eO 2 (by decide) (by decide) (by decide) (by decide)]
  · rw [gt _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
  · rw [rdt, k4.2.1, k3.2.1, k2.2.1, k1.2.1]
  · rw [wrt, k4.2.2, k3.2.2, k2.2.2, k1.2.2]

end VG.Proof.Ed448.AArch64.Window
