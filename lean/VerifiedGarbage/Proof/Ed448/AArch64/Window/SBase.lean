import VerifiedGarbage.Proof.Ed448.AArch64.Window.Table
import VerifiedGarbage.Proof.X448.AArch64.Base.Loop
import VerifiedGarbage.Proof.X448.AArch64.Base.Setup
import VerifiedGarbage.Proof.Ed448.AArch64.Window.CopyK

/-!
# Ed448 verification on AArch64: `[S]B`

Untrusted: everything here is checked by Lean. `sBase`, from the bits of `S` at
`BITS`, every slot's limbs below `Ib` and zero in slot 19: both accumulators at
`[G] B` (`accs baseG57`), the comb's 57 steps and `16 A + B` (`sBase_ok`), as in
`vg_ed448_scalar_base`: `[S]B` in slots 0–2.
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC BITS)
open VG.Impl.X448.AArch64.Base (AX AY AZ BX BY BZ accs limb)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (StepInv Bits pt consts_ok bnd_of_words F_of_words loop_ok combine_ok)
open VG.Proof.Ed448 (Rep baseAff)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem sBase_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hz : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0) {S : Nat} (hS : S < 256 ^ 57)
    (hbits : Bits 57 base S s.mem)
    (htb : VG.Proof.X448.AArch64.Base.TblAt s base (s.syms VG.Impl.X448.AArch64.Base.combSym)) :
    WP isa sBase s fun t =>
      Scr t base ∧ BEnv t.mem base ∧ (∀ w < 8, limbs t.mem base (slot (19 : Index).val) w = 0) ∧
      Rep (pt (EV t.mem base) 0 1 2) ((S : ℤ) • baseAff) ∧ Outside2 base 64 2816 ACC 1152 s.mem t.mem ∧
      t.gpr .x30 = s.gpr .x30 ∧ t.gpr .x20 = s.gpr .x20 ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold sBase
  refine WP.seq (WP.mono_syms (consts_ok hs Impl.X448.baseG57) fun t ⟨tv, tOut, kt, tc⟩ syt => ?_)
  have hst : Scr t base := hs.of_keeps kt (by decide)
  have ev : ∀ (i : Index) (v : Spec.X448.Fe), (∀ w < 8, word t.mem base (slot i.val + 8 * w) = limb v w) →
      EV t.mem base i = v := fun i v h => F_of_words h
  have hG : Rep (VG.Proof.X448.basePt Impl.X448.baseG57) (((VG.Proof.X448.combG 57 : ℤ) + 0) • baseAff) := by
    rw [VG.Proof.X448.combG_57, add_zero, natCast_zsmul]; exact VG.Proof.X448.baseG57_ok
  have pA : pt (EV t.mem base) 0 1 2 = VG.Proof.X448.basePt Impl.X448.baseG57 := by
    simp only [pt, VG.Proof.X448.basePt]
    rw [ev 0 _ fun w hw => (tv w hw).1, ev 1 _ fun w hw => (tv w hw).2.1, ev 2 _ fun w hw => (tv w hw).2.2.1]
  have pB : pt (EV t.mem base) 3 4 5 = VG.Proof.X448.basePt Impl.X448.baseG57 := by
    simp only [pt, VG.Proof.X448.basePt]
    rw [ev 3 _ fun w hw => (tv w hw).2.2.2.1, ev 4 _ fun w hw => (tv w hw).2.2.2.2.1,
      ev 5 _ fun w hw => (tv w hw).2.2.2.2.2]
  have keep : ∀ i : Index, 6 ≤ i.val → ∀ w < 8, limbs t.mem base (slot i.val) w = limbs s.mem base (slot i.val) w :=
    fun i hi w hw => by
      have := i.isLt
      exact tOut.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega)
  have inv : StepInv 57 t base S 0 t := by
    refine ⟨by decide, hst, fun i w hw => ?_, fun w hw => ?_, by rw [tc]; rfl, fun q hq => ?_,
      by rw [pA]; exact hG, by rw [pB]; exact hG, rfl, rfl, rfl, rfl, Outside2.refl _ _ _ _ _ _, ?_⟩
    · by_cases hi : i.val < 6
      · have hi6 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
          rcases i with ⟨i, hlt⟩; simp only [Fin.ext_iff] at hi ⊢; omega
        rcases hi6 with rfl | rfl | rfl | rfl | rfl | rfl
        · exact bnd_of_words (fun w hw => (tv w hw).1) w hw
        · exact bnd_of_words (fun w hw => (tv w hw).2.1) w hw
        · exact bnd_of_words (fun w hw => (tv w hw).2.2.1) w hw
        · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.1) w hw
        · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.2.1) w hw
        · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.2.2) w hw
      · rw [keep i (by omega) w hw]; exact hb i w hw
    · rw [keep 19 (by decide) w hw]; exact hz w hw
    · have hn := hs.nowrap
      rw [tOut _ (by rw [VG.Proof.Ed448.AArch64.Window.ofs_off0' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)]
      exact hbits q hq
    · rw [syt]
      exact htb.of_far (by rw [kt.2.1, kt.2.2]) fun x hx => tOut x (Or.inr (by omega))
  refine WP.seq (WP.mono (loop_ok (by decide) (s₀ := t) 57 t (by decide) (Nat.le_refl _)
    (by rw [Nat.sub_self]; exact inv) rfl) fun u hu => ?_)
  refine WP.mono (combine_ok hS hu) fun v ⟨fv, rv⟩ => ⟨fv.scr, fv.env, fv.zero, rv, ?_, ?_, ?_, ?_, ?_⟩
  · have o2 : Outside2 base 64 2816 ACC 1152 s.mem t.mem := fun x a _ => tOut x (by omega)
    exact o2.trans fv.mem
  · rw [fv.lr, kt.1 _ (by decide)]
  · rw [fv.out, kt.1 _ (by decide)]
  · rw [fv.rd, kt.2.1]
  · rw [fv.wr, kt.2.2]

end VG.Proof.Ed448.AArch64.Window
