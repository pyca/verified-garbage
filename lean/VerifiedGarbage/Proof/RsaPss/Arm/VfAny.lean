module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfPos
import VerifiedGarbage.Proof.RsaPss.Arm.VfPass
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.RsaPss.Arm.VfY
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `RsaPss.Arm.VfShift`, which only this module used -/

section

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the shift

`DB`, copied after `mHash` in `Y`, shifted left by `a = pos + 1` bytes in ten
passes: pass `p` shifts by `2^p` if bit `p` of `a` is set (`onePass_vp`), so
that after `p` passes byte `j` is byte `j + a mod 2^p` of `DB`, zeros after
its end (`SH`); after ten, `a < 2^10` (`shift_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- Byte `i` of `DB`, zero after its end. -/
abbrev Dp (P : EP) (τ : State) (i : Nat) : Byte := if i < dbN h P then dbF h P τ i else 0

/-- The shift's distance. -/
abbrev aV (P : EP) (τ : State) : Nat := pzF h P τ + 1

/-- What the shift keeps. -/
abbrev Kq (P : EP) (τ : State) (m : Mem) : Prop :=
  K2 h P τ m ∧ ∀ i < 8 + h.D, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P τ).getD i 0

/-- After `p` passes. -/
abbrev SH (P : EP) (τ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sA) 32 = BitVec.ofNat 32 (aV h P τ / 2 ^ p) ∧
    m.readW ((P.lay h.D).fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW ((P.lay h.D).fr sPc) 32 = BitVec.ofNat 32 (10 - p) ∧
    ∀ j < 2040 - h.D, m (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ % 2 ^ p)

theorem pzF_lt {P : EP} {τ : State} (hdb : 1 ≤ dbN h P) : pzF h P τ < dbN h P := by
  unfold pzF pzJ; split <;> omega_arith

/-- The bounds a pass needs. -/
theorem shB {P : EP} {σ : State} (hi : In h.D P σ) (hf : fits h P) :
    lo P ≤ 1 ∧ 1 ≤ dbN h P ∧ dbN h P + h.D ≤ 1023 ∧ h.D ≤ 64 ∧ 0 < h.D := by
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi hf
  exact ⟨hlo, by omega_arith, by omega_arith, hD, hD0⟩

/-- A pass's registers. -/
theorem passSet_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) (.block (passSet h.sh))
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) ∧
        s.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
        s.gpr .r1 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D + 2 ^ p) ∧ s.gpr .lr = BitVec.ofNat 32 (dbN h P) ∧
        s.gpr .r2 = maskOf (aV h P τ / 2 ^ p % 2 = 1)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hs⟩ => ?_
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hk.1.1 hk.1.2.1
  have hpz := pzF_lt h (τ := τ) hdb
  have hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have e3 : oY = 1024 := rfl
  have haV : aV h P τ < 1024 := by show pzF h P τ + 1 < 1024; omega_arith
  have hav : aV h P τ / 2 ^ p < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith)
  have hw : WP isa (.block (passSet h.sh)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
      t.gpr .r1 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D + 2 ^ p) ∧ t.gpr .lr = BitVec.ofNat 32 (dbN h P) ∧
      t.gpr .r2 = 0 - (BitVec.ofNat 32 (aV h P τ / 2 ^ p) &&& 1) := by
    prun [passSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hs.1, hs.2.1, hk.1.2.2.1.2,
      movw_val (show oY + 8 + dig h.sh < 2 ^ 16 by show oY + 8 + h.D < 2 ^ 16; omega_arith),
      movw_val (show 0 < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat, dpVal]
    rfl
  exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r2⟩ =>
    ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hs⟩, r0, r1, lr, by rw [r2, mask_bit hav]⟩

/-- Between a pass's bytes and its next stage: the slots of pass `p`, the
bytes of pass `p + 1`. -/
abbrev SM (P : EP) (τ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sA) 32 = BitVec.ofNat 32 (aV h P τ / 2 ^ p) ∧
    m.readW ((P.lay h.D).fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW ((P.lay h.D).fr sPc) 32 = BitVec.ofNat 32 (10 - p) ∧
    ∀ j < 2040 - h.D, m (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ % 2 ^ (p + 1))

/-- A pass's bytes. -/
theorem passMid_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) ∧
        s.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
        s.gpr .r1 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D + 2 ^ p) ∧ s.gpr .lr = BitVec.ofNat 32 (dbN h P) ∧
        s.gpr .r2 = maskOf (aV h P τ / 2 ^ p % 2 = 1))
      (countLoop passBody)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SM h P τ p s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.1.2.1
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hi₀ hf
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 1024 := rfl
  obtain hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  obtain hp0 : 0 < 2 ^ p := Nat.two_pow_pos p
  have e1 : oEm = 0 := rfl
  refine (pass_vp hg (o := oY + 8 + h.D) (d := 2 ^ p) (n := dbN h P) (by omega_arith) hp0 (by omega_arith)
    (c := fun τ => aV h P τ / 2 ^ p % 2 = 1) (X := fun τ m => Kq h P τ m ∧ SH h P τ p m)).mono
    (fun τ s ⟨⟨hc, hk, hs⟩, r0, r1, lr, r2⟩ => ⟨hc, ⟨hk, hs⟩, r0, r1, lr, r2⟩)
    fun τ s ⟨hc, m₀, ⟨hk, hs⟩, fr, hsel⟩ => ?_
  obtain away : ∀ r ∈ [sR P.scr (oY + 8 + h.D) (dbN h P)], Away2 (P.lay h.D) P.scr r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by omega_arith) (by omega_arith)
  obtain ks : ∀ d, d + 4 ≤ frameBytes → s.mem.readW ((P.lay h.D).fr d) 32 = m₀.readW ((P.lay h.D).fr d) 32 :=
    fun d hd => slot_keep (v := m₀.readW ((P.lay h.D).fr d) 32) fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hg.slot ok (by omega_arith) (by rw [hg.F]; omega_arith)) rfl
  refine ⟨hc, ⟨K2.keep h hk.1 fr away, sbytes_keep fr (fun r hr => ?_) (by omega_arith) hk.2⟩,
    by rw [ks _ (by decide)]; exact hs.1, by rw [ks _ (by decide)]; exact hs.2.1,
    by rw [ks _ (by decide)]; exact hs.2.2.1, fun j hj => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)
  obtain ms := mod_succ (aV h P τ) p
  by_cases e : j < dbN h P
  · rw [hsel j e]
    by_cases hc' : aV h P τ / 2 ^ p % 2 = 1
    · rw [ite_eq_left hc', show oY + 8 + h.D + 2 ^ p + j = oY + 8 + h.D + (2 ^ p + j) by omega_arith,
        hs.2.2.2 _ (by omega_arith)]
      congr 1; rw [ms, hc']; omega_arith
    · rw [ite_eq_right hc', hs.2.2.2 _ hj]
      congr 1; rw [ms, show aV h P τ / 2 ^ p % 2 = 0 by omega_arith]; omega_arith
  · have hm : s.mem (sa P.scr (oY + 8 + h.D + j)) = m₀ (sa P.scr (oY + 8 + h.D + j)) :=
      fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oY + 8 + h.D + j) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _
          (Region.contains_self _ _)
    rw [hm, hs.2.2.2 j hj]; unfold Dp; rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]

/-- The bytes and the slots after a pass. -/
theorem keep3 (P : EP) (hg : Geo (P.lay h.D) P.scr) {τ : State} {m m' : Mem}
    (hf : Frame [slotR (P.lay h.D) sA, slotR (P.lay h.D) sD, slotR (P.lay h.D) sPc] m m') (hk : Kq h P τ m)
    {f : Nat → Byte} (hy : ∀ j < 2040 - h.D, m (sa P.scr (oY + 8 + h.D + j)) = f j) :
    Kq h P τ m' ∧ ∀ j < 2040 - h.D, m' (sa P.scr (oY + 8 + h.D + j)) = f j := by
  obtain ⟨σ', ok⟩ := hg.ok
  have e3 : oY = 1024 := rfl
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  obtain aw : ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR (P.lay h.D) sA, slotR (P.lay h.D) sD, slotR (P.lay h.D) sPc],
      Region.Disjoint (sR P.scr o n) r := fun o n hon r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have e2 : oRsa = 8192 := rfl
  refine ⟨⟨K2.keep h hk.1 hf fun r hr => ?_, sbytes_keep hf (aw _ _ (by omega_arith)) (by omega_arith) hk.2⟩,
    sbytes_keep hf (aw _ _ (by omega_arith)) (by omega_arith) hy⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The next pass's slots, and the flags of whether it was the last. -/
theorem passNext_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SM h P τ p s.mem) (.block passNext)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ (p + 1) s.mem) ∧
        s.z = decide (10 - (p + 1) = 0)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hs⟩ => ?_
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hk.1.1 hk.1.2.1
  obtain hpz := pzF_lt h (τ := τ) hdb
  obtain haV : aV h P τ < 1024 := by show pzF h P τ + 1 < 1024; omega_arith
  obtain hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  obtain ea : BitVec.ofNat 32 (aV h P τ / 2 ^ p) >>> 1 = BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1)) := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith)), Nat.div_div_eq_div_mul,
      Nat.pow_one, ← Nat.pow_succ]
  obtain ed : BitVec.ofNat 32 (2 ^ p) + BitVec.ofNat 32 (2 ^ p) = BitVec.ofNat 32 (2 ^ (p + 1)) := by
    rw [BitVec.ofNat_add_ofNat, Nat.pow_succ]; congr 1; omega_arith
  obtain ec : BitVec.ofNat 32 (10 - p) - 1 = BitVec.ofNat 32 (10 - (p + 1)) := by
    rw [show 10 - p = (10 - (p + 1)) + 1 by omega_arith]; exact sub_one_ofNat (by omega_arith)
  obtain hz0 : ∀ y : BitVec 32, y - 0 = y := fun y => BitVec.sub_zero y
  have hi := hk.1.1
  obtain w1 : ∀ v, (s.mem.writeW ((P.lay h.D).fr sA) v).readW ((P.lay h.D).fr sD) 32 = BitVec.ofNat 32 (2 ^ p) :=
    fun v => by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hs.2.1
  obtain w2 : ∀ v v', ((s.mem.writeW ((P.lay h.D).fr sA) v).writeW ((P.lay h.D).fr sD) v').readW
      ((P.lay h.D).fr sPc) 32 = BitVec.ofNat 32 (10 - p) := fun v v' => by
    rw [slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide)]
    exact hs.2.2.1
  obtain hw : WP isa (.block passNext) s fun t =>
      t.mem = ((s.mem.writeW ((P.lay h.D).fr sA) (BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1)))).writeW
        ((P.lay h.D).fr sD) (BitVec.ofNat 32 (2 ^ (p + 1)))).writeW ((P.lay h.D).fr sPc)
          (BitVec.ofNat 32 (10 - (p + 1))) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.z = decide (10 - (p + 1) = 0) := by
    prun [passNext, sp0, ld, st, hc.st.sp, hc.aFr hg, hc.rFr hg, hs.1, hs.2.1, hs.2.2.1,
      slotAt hi (d := sA) (by decide), slotAt hi (d := sD) (by decide), slotAt hi (d := sPc) (by decide),
      hc.st.inFr (d := sA) (n := 4) (by show sA + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sD) (n := 4) (by show sD + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sPc) (n := 4) (by show sPc + 4 ≤ frameBytes; decide), ea, ed, ec, hz0, w1, w2,
      VG.Proof.X25519.Arm.ofNat_beq_zero (show 10 - (p + 1) < 2 ^ 32 by omega_arith), dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ?_
  obtain fr : Frame [slotR (P.lay h.D) sA, slotR (P.lay h.D) sD, slotR (P.lay h.D) sPc] s.mem t.mem := by
    rw [m]
    exact ((slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  obtain ⟨hk', hy'⟩ := keep3 h P hg fr hk hs.2.2.2
  refine ⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hk', ?_, ?_, ?_, hy'⟩, z⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]

/-- A pass. -/
theorem onePass_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) (passOne h.sh)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ (p + 1) s.mem) ∧
        s.z = decide (10 - (p + 1) = 0)) :=
  (passSet_vp h P hP hp).seq ((passMid_vp h P hP hp).seq (passNext_vp h P hP hp))

/-- The shift's distance, its first pass's, and its passes. -/
theorem shInit_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ j) (.block shInit)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ 0 s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hy⟩ => ?_
  have hi := hk.1.1
  obtain hw : WP isa (.block shInit) s fun t =>
      t.mem = ((s.mem.writeW ((P.lay h.D).fr sA) (BitVec.ofNat 32 (aV h P τ))).writeW
        ((P.lay h.D).fr sD) (BitVec.ofNat 32 1)).writeW ((P.lay h.D).fr sPc) (BitVec.ofNat 32 10) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [shInit, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hk.1.2.2.2.2.2.1,
      slotAt hi (d := sA) (by decide), slotAt hi (d := sD) (by decide), slotAt hi (d := sPc) (by decide),
      hc.st.inFr (d := sA) (n := 4) (by show sA + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sD) (n := 4) (by show sD + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sPc) (n := 4) (by show sPc + 4 ≤ frameBytes; decide),
      movw_val (show 1 < 2 ^ 16 by decide), movw_val (show 10 < 2 ^ 16 by decide),
      VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  obtain fr : Frame [slotR (P.lay h.D) sA, slotR (P.lay h.D) sD, slotR (P.lay h.D) sPc] s.mem t.mem := by
    rw [m]
    exact ((slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  obtain ⟨hk', hy'⟩ := keep3 h P hg fr hk hy
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hk', ?_, ?_, ?_, fun j hj => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, Nat.pow_zero, Nat.div_one]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [hy' j hj, Nat.pow_zero, Nat.mod_one, Nat.add_zero]

/-- `DB` shifted left by `pos + 1` bytes. -/
theorem shift_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ j) (shift h.sh)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ)) := by
  refine (shInit_vp h P hP).seq ?_
  let I : Nat → State → State → Prop := fun k τ s => k ≤ 10 ∧ Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
    SH h P τ (10 - k) s.mem
  refine (VP.loop (I := I) (fun k => ?_) 9).mono (fun τ s ⟨hc, hk, hs⟩ => ⟨by omega_arith, hc, hk, hs⟩) fun _ _ h => h
  by_cases hk : k ≤ 9
  swap
  · exact VP.empty fun τ s h' => hk (by have := h'.1; omega_arith)
  refine (onePass_vp h P hP (p := 9 - k) (by omega_arith)).mono
    (fun τ s ⟨_, hc, hq, hs⟩ => ⟨hc, hq, by rw [show 9 - k = 10 - (k + 1) by omega_arith]; exact hs⟩)
    fun τ s ⟨⟨hc, hq, hs⟩, z⟩ => ⟨?_, fun h0 => ⟨hc, hq, fun j hj => ?_⟩, fun hpos => ⟨by omega_arith, hc, hq, ?_⟩⟩
  · rw [VG.Proof.X25519.Arm.eval_ne, z, show 10 - (9 - k + 1) = k by omega_arith]; cases k <;> simp
  · subst h0
    obtain hb := shB h hq.1.1 hq.1.2.1
    obtain hpz := pzF_lt h (τ := τ) hb.2.1
    rw [hs.2.2.2 j hj, Nat.mod_eq_of_lt (show aV h P τ < 2 ^ (9 - 0 + 1) by
      show pzF h P τ + 1 < 1024; omega_arith)]
  · rw [show 10 - k = 9 - k + 1 by omega_arith]; exact hs

end VG.Proof.RsaPss.Arm.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: a salt of any length

`M' = 0⁸ ‖ mHash ‖` the bytes of `DB` after its first nonzero byte (`Ma`):
`DB` copied after `mHash` and shifted into place, hashed over the blocks of
the longest salt, and compared with `H` (`any_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- `M'`. -/
abbrev Ma (P : EP) (τ : State) : List Byte :=
  Spec.RsaPss.zeros 8 ++ digB h P τ ++ (dbL h P τ).drop (pzF h P τ + 1)

/-- Its blocks, those of the longest salt. -/
abbrev nbA (P : EP) : Nat := (dbN h P + (7 + h.D + h.L)) / h.B + 1

theorem pre_length (P : EP) (τ : State) : (Spec.RsaPss.zeros 8 ++ digB h P τ).length = 8 + h.D := by
  simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.Arm.bytesAt_length]

theorem dbL_length (P : EP) (τ : State) : (dbL h P τ).length = dbN h P := by simp [dbL]

theorem Ma_length (P : EP) (τ : State) : (Ma h P τ).length = 8 + h.D + (dbN h P - (pzF h P τ + 1)) := by
  rw [Ma, List.length_append, pre_length, List.length_drop, dbL_length]

theorem Ma_getD {P : EP} {τ : State} {j : Nat} :
    (Ma h P τ).getD (8 + h.D + j) 0 = Dp h P τ (j + aV h P τ) := by
  rw [Ma, RsaPss.getD_app, pre_length, ite_eq_right (by omega_arith), Nat.add_sub_cancel_left]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [← List.getD_eq_getElem?_getD]
  unfold Dp aV
  by_cases e : j + (pzF h P τ + 1) < dbN h P
  · rw [ite_eq_left e, Nat.add_comm, ← dbL_getD h e]
  · rw [ite_eq_right e, getD_ge (by rw [dbL_length]; omega_arith)]

/-- `DB` after `mHash`. -/
theorem cpDb_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ True) ∧ Y1 h P τ s.mem)
      (.seq (.block (cpDb h.sh)) Impl.Bignum.Arm.copyBytes)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ j) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hi₀ hf
  have e1 : oEm = 0 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 1024 := rfl
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ True) ∧ Y1 h P τ s.mem) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧ s.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧
      s.gpr .lr = BitVec.ofNat 32 (dbN h P))
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hy⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oY + 8 + h.D) (n := dbN h P) (by omega_arith) (by omega_arith))
      (hg.rbuf (o := oEm + lo P) (n := dbN h P) (by omega_arith) (by omega_arith))
      (by rw [hg.addr (by omega_arith), hg.addr (by omega_arith)]; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
      (f := fun τ i => dbF h P τ i)
      (Inv := fun τ m => Kq h P τ m ∧ ∀ j, dbN h P ≤ j → j < 2040 - h.D → m (sa P.scr (oY + 8 + h.D + j)) = 0)
      fun τ m m' ⟨hk, hz⟩ hf' => ?_).mono
      (fun τ s ⟨⟨hc, ⟨hk, _⟩, hy⟩, r0, r1, lr⟩ => ⟨hc, ⟨⟨hk, fun i hi => hy i (by omega_arith)⟩, fun j hj hj' => ?_⟩, r0, r1, lr, fun i hi => ?_⟩)
      fun τ s ⟨hc, ⟨hk, hz⟩, hs⟩ => ⟨hc, hk, fun j hj => ?_⟩)
  · have hw : WP isa (.block (cpDb h.sh)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧ t.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧
        t.gpr .lr = BitVec.ofNat 32 (dbN h P) := by
      prun [cpDb, atS, atDb, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.1.2.2.1.1,
        hk.1.2.2.1.2, movw_val (show oY + 8 + dig h.sh < 2 ^ 16 by show oY + 8 + h.D < 2 ^ 16; omega_arith),
        movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hy⟩, r0, r1, lr⟩
  · rw [hg.addr (by omega_arith)] at hf'
    refine ⟨⟨K2.keep h hk.1 hf' fun r hr => ?_, sbytes_keep hf' (fun r hr => ?_) (by omega_arith) hk.2⟩,
      fun j hj hj' => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)
    · rw [← hz j hj hj']
      exact hf' _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oY + 8 + h.D + j) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _
          (Region.contains_self _ _)
  · rw [show oY + 8 + h.D + j = oY + (8 + h.D + j) by omega_arith, hy _ (by omega_arith)]
    exact getD_ge (by rw [pre_length]; omega_arith)
  · rw [hg.byteAt_scr (by omega_arith), show oEm + lo P + i = oEm + lo P + i from rfl]; exact hk.2.2.2.1 i hi
  · unfold Dp
    by_cases e : j < dbN h P
    · rw [ite_eq_left e, ← hs j e, hg.byteAt_scr (by omega_arith)]
    · rw [ite_eq_right e]; exact hz j (by omega_arith) hj

/-- `M'`'s length and blocks. -/
theorem anyLen_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ)) (.block (anyLen h.sh))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kt h P (Ma h P) (nbA h P) τ s.mem ∧
        ∀ i < 2048, s.mem (sa P.scr (oY + i)) = (Ma h P τ).getD i 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hy⟩ => ?_
  have hi := hk.1.1
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hi hk.1.2.1
  obtain hpz := pzF_lt h (τ := τ) hdb
  have hL := h.L_le
  have hB := h.B_ge
  have e3 : oY = 1024 := rfl
  obtain e1 : BitVec.ofNat 32 (dbN h P + (7 + h.D + h.L)) >>> lgB h.sh =
      BitVec.ofNat 32 ((dbN h P + (7 + h.D + h.L)) / h.B) := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr (by omega_arith), h.pow_lg]
  obtain w1 : ∀ v, (s.mem.writeW ((P.lay h.D).fr sL) v).readW ((P.lay h.D).fr sDb) 32 = BitVec.ofNat 32 (dbN h P) :=
    fun v => by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hk.1.2.2.1.2
  obtain es : BitVec.ofNat 32 (dbN h P) - BitVec.ofNat 32 (pzF h P τ) = BitVec.ofNat 32 (dbN h P - pzF h P τ) :=
    Offset.ofNat_sub_ofNat (w := 32) (by omega_arith)
  obtain hw : WP isa (.block (anyLen h.sh)) s fun t =>
      t.mem = (s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (dbN h P - pzF h P τ + (7 + h.D)))).writeW
        ((P.lay h.D).fr sNb) (BitVec.ofNat 32 (nbA h P)) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [anyLen, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hk.1.2.2.1.2, hk.1.2.2.2.2.2.1, w1, es,
      slotAt hi (d := sL) (by decide), slotAt hi (d := sNb) (by decide),
      hc.st.inFr (d := sL) (n := 4) (by show sL + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sNb) (n := 4) (by show sNb + 4 ≤ frameBytes; decide),
      movw_val (show 7 + dig h.sh < 2 ^ 16 by show 7 + h.D < 2 ^ 16; omega_arith),
      movw_val (show 7 + dig h.sh + lenL h.sh < 2 ^ 16 by show 7 + h.D + h.L < 2 ^ 16; omega_arith),
      BitVec.ofNat_add_ofNat, e1, h.lg_range, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  obtain fr : Frame [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb] s.mem t.mem := by
    rw [m]
    exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  obtain ⟨σ', ok⟩ := hg.ok
  obtain aw : ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb],
      Region.Disjoint (sR P.scr o n) r := fun o n hon r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have e2 : oRsa = 8192 := rfl
  obtain hy' := sbytes_keep fr (aw _ _ (by omega_arith)) (by omega_arith) hy
  obtain hp' := sbytes_keep fr (aw _ _ (by omega_arith)) (by omega_arith) hk.2
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨K2.keep h hk.1 fr fun r hr => ?_, ?_, ?_⟩,
    fun i hi' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, Ma_length]
    congr 1; omega_arith
  · rw [m, Mem.readW_writeW_self32]
  · by_cases e : i < 8 + h.D
    · rw [hp' i e, Ma, RsaPss.getD_app (l := Spec.RsaPss.zeros 8 ++ digB h P τ), pre_length, ite_eq_left e]
    · have := hy' (i - (8 + h.D)) (by omega_arith)
      rw [show oY + 8 + h.D + (i - (8 + h.D)) = oY + i by omega_arith] at this
      rw [this, show i = 8 + h.D + (i - (8 + h.D)) by omega_arith, Ma_getD]
      congr 1; omega_arith

/-- A salt of any length. -/
theorem any_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧ True) ∧ s.syms = τ.syms) (anyPath f h.sh)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧
        s.gpr .r0 = if acc2 h P τ = 0 ∧ HOk h P τ (Ma h P τ) then 1 else 0) ∧ s.syms = τ.syms) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.2.1
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hL := h.L_le
  have hB := h.B_le
  obtain hB0 : 0 < h.B := by have := h.B_ge; omega_arith
  obtain ⟨hlo, hdb, hdD, hD', hD0⟩ := shB h hi₀ hf
  obtain q1 := Nat.lt_mul_div_succ (dbN h P + (7 + h.D + h.L)) hB0
  obtain q2 := Nat.mul_div_le (dbN h P + (7 + h.D + h.L)) h.B
  obtain hT : nbA h P * h.B ≤ 2048 := by
    show ((dbN h P + (7 + h.D + h.L)) / h.B + 1) * h.B ≤ 2048
    rw [Nat.succ_mul, Nat.mul_comm]; omega_arith
  show VP _ (.seq (yDig h.sh 4) (.seq (.block (cpDb h.sh)) (.seq Impl.Bignum.Arm.copyBytes (.seq (shift h.sh)
    (.seq (.block (anyLen h.sh)) (.seq (ctHash f h.sh 14) (cmpH h.sh))))))) _
  refine (VP.syms (yDig_vf h P ⟨σ₀, hi₀⟩ True)).seq (VP.assoc ((VP.syms (cpDb_vp h P ⟨σ₀, hi₀⟩)).seq
    ((VP.syms (shift_vp h P ⟨σ₀, hi₀⟩)).seq ((VP.syms (anyLen_vp h P ⟨σ₀, hi₀⟩)).seq ?_))))
  exact (tail_vp h P Q ⟨σ₀, hi₀⟩ hT (Nat.succ_pos _) (msg := Ma h P) fun τ => by
      rw [Ma_length]; show _ ≤ ((dbN h P + (7 + h.D + h.L)) / h.B + 1) * h.B; rw [Nat.mul_comm]; omega_arith).mono
    (fun τ s ⟨⟨hc, hk, hy⟩, sy⟩ => ⟨⟨hc, hk, fun i hi => hy i (by omega_arith)⟩, sy⟩) fun _ _ h' => h'

end VG.Proof.RsaPss.Arm.Vf
