import VerifiedGarbage.Proof.Ed448.AArch64.VerifyChecks
import VerifiedGarbage.Proof.Curve448.AArch64.Legacy

/-!
# Ed448 verification on AArch64: comparing slots of the register-resident arithmetic

Untrusted: everything here is checked by Lean. As `canon_ok` and `eqSlots_ok`
(`VerifyChecks.lean`), for slots whose limbs are below `2^118` (products of
the register-resident arithmetic) rather than X448's `weakBound`.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside ofs workRegs FieldMem)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv)
open VG.Impl.X448.AArch64 (ld st slot X2 ACC)

/-- `canon a`: slot `a` (limbs below `2^118`) fully reduced into `X2`, as sixteen 28-bit limbs. -/
theorem canonF_ok {s : State} {base : Addr} (hs : Scr s base) (a : Fin 22) (ha : a ≠ 1)
    (hca : ∀ j < 8, limbs s.mem base (slot a.val) j < 2 ^ 118) :
    WP isa (.block (canon a.val)) s fun t =>
      VG.Proof.X448.AArch64.Bounded t.mem base X2 ∧ VG.Proof.X448.AArch64.fe t.mem base X2 = (E s.mem base a).val ∧
      FieldMem base X2 s.mem t.mem ∧ Keeps workRegs s t := by
  have hal := a.isLt
  have hne : a.val ≠ 1 := fun e => ha (Fin.ext e)
  rw [canon, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs (o := X2) (a := slot a.val) (by decide)
    (by simp only [slot]; omega) (by decide) (by simp only [slot]; omega)
    (Or.inr (by simp only [X2, slot]; omega))) fun u ⟨ul, uo, uk⟩ => ?_
  have hsu := hs.of_keeps uk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.toLegacy_ok' hsu (o := X2) (by decide) (by decide)
    (fun i hi => by rw [show VG.Proof.X448.AArch64.limbs u.mem base X2 i = _ from ul i hi]; exact hca i hi))
    fun v ⟨vk, vb, vf⟩ => ?_
  have hsv := hsu.of_keeps vk.1 (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.freeze_ok hsv vb) fun t ⟨tb, tv, tm, tk⟩ => ?_
  refine ⟨tb, ?_, (FieldMem.output uo).trans (vk.2.trans tm), ((uk.trans vk.1).mono
    (fun r hr => List.mem_cons_of_mem _ hr)).trans tk⟩
  have hF : VG.Proof.X448.toFe (VG.Proof.X448.AArch64.fe v.mem base X2) = E s.mem base a := by
    have : VG.Proof.X448.AArch64.F v.mem base X2 = VG.Proof.Curve448.AArch64.F u.mem base X2 := vf
    rw [show VG.Proof.X448.toFe (VG.Proof.X448.AArch64.fe v.mem base X2) = VG.Proof.X448.AArch64.F v.mem base X2
      from rfl, this]
    exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr ul)
  rw [tv, ← hF, VG.Proof.X448.toFe_val]

/-- `eqSlots a b`: `x20 |= c`, with `c = 0` exactly when slots `a` and `b` hold the same element. -/
theorem eqSlotsF_ok {s : State} {base : Addr} (hs : Scr s base) (a b : Fin 22)
    (hca : ∀ j < 8, limbs s.mem base (slot a.val) j < 2 ^ 118) (hcb : ∀ j < 8, limbs s.mem base (slot b.val) j < 2 ^ 118)
    (ha : a ≠ 1) (hb1 : b ≠ 1) :
    WP isa (.block (eqSlots a.val b.val)) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ E s.mem base a = E s.mem base b) ∧ t.gpr .x20 = s.gpr .x20 ||| c) ∧
      CKeep base s t := by
  rw [eqSlots]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (canonF_ok hs a ha hca) fun u ⟨bu, fu, mu, ku⟩ => ?_
  have hsu := hs.of_keeps ku (by decide)
  have cu : CKeep base s u := CKeep.of_keeps ku (fun r hr => List.mem_cons_of_mem _ hr) (CFrame.of_field mu)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.copy_ok hsu (o := CAN) (a := X2) (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (by decide)))) fun v ⟨lv, ov, kv⟩ => ?_
  have hsv := hsu.of_keeps kv (by decide)
  have cv : CKeep base u v := CKeep.of_keeps kv (by decide) (CFrame.of_can ov)
  have x2v : ∀ j < 16, VG.Proof.X448.AArch64.limbs v.mem base X2 j = VG.Proof.X448.AArch64.limbs u.mem base X2 j :=
    fun j hj => congrArg BitVec.toNat (ov.word (Or.inl (by simp only [X2, slot, CAN]; omega)) (by simp only [X2, slot]; omega))
  have bcv : ∀ j < 8, limbs v.mem base (slot b.val) j < 2 ^ 118 := fun j hj => by
    rw [(cu.trans cv).mem.limbs hb1 (by omega)]; exact hcb j hj
  rw [WP.block_append_iff]
  refine WP.mono (canonF_ok hsv b hb1 bcv) fun w ⟨bw, fw, mw, kw⟩ => ?_
  have hsw := hsv.of_keeps kw (by decide)
  have cw : CKeep base v w := CKeep.of_keeps kw (fun r hr => List.mem_cons_of_mem _ hr) (CFrame.of_field mw)
  rw [WP.block_append_iff]
  refine WP.mono (diffCan_ok hsw) fun x ⟨x5, xm, xk⟩ => ?_
  refine WP.mono (orBad_ok x) fun t ⟨t20, tm, tk⟩ => ?_
  have can : ∀ j < 16, word w.mem base (CAN + 8 * j) = word v.mem base (CAN + 8 * j) := fun j hj =>
    Mem.readW_congr fun i hi => mw _ (by
        simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by simp only [CAN]; omega)]
        simp only [X2, slot, CAN]; omega)
      (by simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by simp only [CAN]; omega)]
          simp only [CAN, ACC]; omega)
  have eb : E v.mem base b = E s.mem base b := (cu.trans cv).mem.E hb1
  refine ⟨⟨x.gpr .x5, ?_, ?_⟩, ?_⟩
  · rw [x5]
    constructor
    · intro h
      apply Fin.ext
      rw [← fu, ← eb, ← fw]
      apply VG.Proof.X448.valN_congr
      intro j hj
      have e := congrArg BitVec.toNat (h j hj)
      rw [can j hj] at e
      have := lv j hj
      change (word v.mem base (CAN + 8 * j)).toNat = VG.Proof.X448.AArch64.limbs u.mem base X2 j at this
      change VG.Proof.X448.AArch64.limbs u.mem base X2 j = (word w.mem base (X2 + 8 * j)).toNat
      rw [← this, e]
    · intro h j hj
      have hv : VG.Proof.X448.AArch64.fe w.mem base X2 = VG.Proof.X448.AArch64.fe u.mem base X2 := by
        rw [fw, eb, fu, ← h]
      have := valN_inj 16 bw bu hv j hj
      apply BitVec.eq_of_toNat_eq
      rw [can j hj]
      change VG.Proof.X448.AArch64.limbs w.mem base X2 j = (word v.mem base (CAN + 8 * j)).toNat
      rw [this]; exact (lv j hj).symm
  · rw [t20, xk.1 _ (by decide), kw.1 _ (by decide), kv.1 _ (by decide), ku.1 _ (by decide)]
  · refine ((cu.trans cv).trans cw).trans ?_
    refine CKeep.of_keeps (rs := [.x4, .x5, .x6, .x20]) ((xk.mono (by decide)).trans (tk.mono (by decide)))
      (by decide) ?_
    rw [tm, xm]; exact CFrame.refl _ _

end VG.Proof.Ed448.AArch64
