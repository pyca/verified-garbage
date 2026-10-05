import VerifiedGarbage.Proof.Ed448.AArch64.Window.Checks
import VerifiedGarbage.Proof.X448.AArch64.Fast.Finish
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
import VerifiedGarbage.Proof.Ed448.AArch64.Window.CopyK

/-!
# Ed448 verification on AArch64: the result

Untrusted: everything here is checked by Lean. `wfinish`: slots 12 and 13,
then 14 and 15, compared (`eqSlotsF_ok`, each check ORed into `x20`), the
result `x0 = (x20 == 0)`, and the callee-saved registers restored
(`wfinish_ok`).
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC X2)
open VG.Impl.X448.AArch64.Fast (saved)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs Saved restore_ok workRegs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (SavedX SavedV restoreX_ok)
open VG.Proof.Ed448.AArch64 (CFrame CKeep eqSlotsF_ok isZero_ok or_eq_zero64)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- `d := r`. -/
theorem mov_ok (d r : Reg) (s : State) :
    WP isa (.block [.addImm .x d r 0]) s fun t => t.gpr d = s.gpr r ∧ t.mem = s.mem ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, BitVec.add_zero, RegUpd.gpr_write_self,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r' hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem CFrame.saved {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : CFrame base m m') (hs : Saved base g m) :
    Saved base g m' :=
  ⟨(h.word (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (by decide)).trans hs.1,
    (h.word (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (by decide)).trans hs.2⟩

theorem CFrame.savedX {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : CFrame base m m') (hs : SavedX base g m) :
    SavedX base g m' := fun k hk =>
  (h.word (Or.inr (by simp only [X2, slot, Impl.X448.AArch64.Fast.SAVE]; omega))
    (Or.inl (by simp only [CAN, Impl.X448.AArch64.Fast.SAVE]; omega))
    (Or.inl (by simp only [ACC, Impl.X448.AArch64.Fast.SAVE]; omega))
    (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega)).trans (hs k hk)

theorem CFrame.savedV {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : CFrame base m m') (hs : SavedV base v m) :
    SavedV base v m' := by
  have hV : Impl.X448.AArch64.Fast.VSAVE = 4736 := rfl
  refine hs.frame fun d h1 h2 => ?_
  have ho : ofs base (off base d) = d := ofs_off0' base (by omega)
  exact h _ (by rw [ho]; simp only [X2, slot]; omega) (by rw [ho]; simp only [CAN]; omega)
    (by rw [ho]; simp only [ACC]; omega)

theorem wfinish_eq : wfinish = eqSlots 12 13 ++ (eqSlots 14 15 ++ (([.addImm .x .x5 .x20 0] : List Instr) ++ (isZero ++
    (([.addImm .x .x0 .x5 0] : List Instr) ++ (([ld .x19 0, ld .x20 8] : List Instr) ++ (Impl.X448.AArch64.Fast.restore ++
      Impl.X448.AArch64.Fast.vrestore)))))) := by
  simp only [wfinish, List.append_assoc]; rfl

/-- **The result** of the comparisons, and the registers restored. -/
theorem wfinish_ok {s : State} {base : Addr} (hs : Scr s base)
    (hb : ∀ i : Index, 12 ≤ i.val → i.val < 16 → ∀ j < 8, limbs s.mem base (slot i.val) j < 2 ^ 118)
    {g : Reg → BitVec 64} (sv : Saved base g s.mem) (svx : SavedX base g s.mem)
    {gv : VReg → BitVec 128} (svv : SavedV base gv s.mem) :
    WP isa (.block wfinish) s fun t =>
      t.gpr .x0 = (if s.gpr .x20 = 0 ∧ EV s.mem base 12 = EV s.mem base 13 ∧ EV s.mem base 14 = EV s.mem base 15
        then 1 else 0) ∧
      t.gpr .x19 = g .x19 ∧ t.gpr .x20 = g .x20 ∧ (∀ k < 8, t.gpr (saved k) = g (saved k)) ∧
      (∀ k < 8, (t.v (VG.Impl.Curve448.AArch64.Neon.V (8 + k))).extractLsb' 0 64 =
        (gv (VG.Impl.Curve448.AArch64.Neon.V (8 + k))).extractLsb' 0 64) ∧
      t.gpr .x30 = s.gpr .x30 ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ CFrame base s.mem t.mem := by
  rw [wfinish_eq, WP.block_append_iff]
  refine WP.mono (eqSlotsF_ok hs 12 13 (hb 12 (by decide) (by decide)) (hb 13 (by decide) (by decide))
    (by decide) (by decide)) fun s1 ⟨⟨c1, hc1, x1⟩, k1⟩ => ?_
  have hs1 := k1.scr hs
  have hb1 : ∀ j < 8, limbs s1.mem base (slot (14 : Index).val) j < 2 ^ 118 := fun j hj => by
    rw [k1.mem.limbs (i := 14) (by decide) (by omega)]; exact hb 14 (by decide) (by decide) j hj
  have hb1' : ∀ j < 8, limbs s1.mem base (slot (15 : Index).val) j < 2 ^ 118 := fun j hj => by
    rw [k1.mem.limbs (i := 15) (by decide) (by omega)]; exact hb 15 (by decide) (by decide) j hj
  rw [WP.block_append_iff]
  refine WP.mono (eqSlotsF_ok hs1 14 15 hb1 hb1' (by decide) (by decide)) fun s2 ⟨⟨c2, hc2, x2⟩, k2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (mov_ok .x5 .x20 s2) fun s3 ⟨v3, m3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (isZero_ok s3) fun s4 ⟨v4, m4, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mov_ok .x0 .x5 s4) fun s5 ⟨v5, m5, k5⟩ => ?_
  have k25 : Keeps (.x0 :: .x5 :: .x6 :: .x7 :: []) s2 s5 :=
    ((k3.mono (by decide)).trans (k4.mono (by decide))).trans (k5.mono (by decide))
  have hs5 : Scr s5 base := hs2.of_keeps k25 (by decide)
  have f02 : CFrame base s.mem s2.mem := k1.mem.trans k2.mem
  have m25 : s5.mem = s2.mem := by rw [m5, m4, m3]
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok hs5 (g := g) (by rw [m25]; exact CFrame.saved f02 sv)) fun s6 ⟨t19, t20, m6, k6⟩ => ?_
  have hs6 : Scr s6 base := hs5.of_keeps k6 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (restoreX_ok hs6 (g := g) (by rw [m6, m25]; exact CFrame.savedX f02 svx)) fun s7 ⟨tx, m7, k7⟩ => ?_
  have hs7 : Scr s7 base := hs6.of_keeps k7 (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Fast.vrestore_ok hs7 (by rw [m7, m6, m25]; exact CFrame.savedV f02 svv))
    fun t ⟨tv, mt, gt, rdt, wrt⟩ => ⟨?_, ?_, ?_, fun k hk => by rw [gt]; exact tx k hk, tv, ?_, ?_, ?_, ?_⟩
  · have hx : s2.gpr .x20 = s.gpr .x20 ||| c1 ||| c2 := by rw [x2, x1]
    rw [gt, k7.1 _ (by decide), k6.1 _ (by decide), v5, v4, v3, hx]
    refine if_congr ?_ rfl rfl
    rw [or_eq_zero64, or_eq_zero64, hc1, hc2, and_assoc, k1.mem.E (i := 14) (by decide), k1.mem.E (i := 15) (by decide)]
  · rw [gt, k7.1 _ (by decide)]; exact t19
  · rw [gt, k7.1 _ (by decide)]; exact t20
  · rw [gt, k7.1 _ (by decide), k6.1 _ (by decide), k25.1 _ (by decide), k2.regs.1 _ (by decide),
      k1.regs.1 _ (by decide)]
  · rw [rdt, k7.2.1, k6.2.1, k25.2.1, k2.regs.2.1, k1.regs.2.1]
  · rw [wrt, k7.2.2, k6.2.2, k25.2.2, k2.regs.2.2, k1.regs.2.2]
  · rw [mt, m7, m6, m25]; exact f02

end VG.Proof.Ed448.AArch64.Window
