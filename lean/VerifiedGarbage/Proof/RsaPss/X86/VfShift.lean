module

public import VerifiedGarbage.Proof.RsaPss.X86.VfFixed
public import VerifiedGarbage.Proof.RsaPss.X86.VfPass
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtLen
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS verification with a precomputed public key on x86: the shift

As on ARMv7 (`Proof/RsaPss/Arm/VfShift.lean`): `DB`'s place in `Y` shifted
left by `pos + 1` bytes in ten passes, pass `p` by `2^p` bytes if bit `p` of
the distance is set (`shift_vp`), so that no address depends on `pos`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

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

theorem mask_bit {v : Nat} (hv : v < 2 ^ 32) : 0 - (BitVec.ofNat 32 v &&& 1) = maskOf (v % 2 = 1) := by
  have e : BitVec.ofNat 32 v &&& 1 = BitVec.ofNat 32 (v % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    rw [show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]; omega
  rw [e]; unfold maskOf
  rcases Nat.mod_two_eq_zero_or_one v with e' | e' <;> rw [e'] <;> decide

theorem pzF_lt {P : EP} {τ : State} (hdb : 1 ≤ dbN h P) : pzF h P τ < dbN h P := by
  unfold pzF pzJ; split <;> omega

/-- The bounds a pass needs. -/
theorem shB {P : EP} {σ : State} (hi : In h.D P σ) (hf : fits h P) :
    lo P ≤ 1 ∧ 1 ≤ dbN h P ∧ dbN h P + h.D ≤ 1023 ∧ h.D ≤ 64 ∧ 0 < h.D := by
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi hf
  exact ⟨hlo, by omega, by omega, hD, hD0⟩

/-- A pass's registers. -/
theorem passSet_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) (.block (passSet h.H))
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) ∧
        s.gpr .esi = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
        s.gpr .edi = P.scr + BitVec.ofNat 32 (oY + 8 + h.D + 2 ^ p) ∧ s.gpr .ecx = BitVec.ofNat 32 (dbN h P) ∧
        s.gpr .edx = maskOf (aV h P τ / 2 ^ p % 2 = 1)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp, .ebp] h.certs.passSet (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hs⟩ => ?_
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hk.1.1 hk.1.2.1
  have hpz := pzF_lt h (τ := τ) hdb
  have hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
  have haV : aV h P τ < 1024 := by show pzF h P τ + 1 < 1024; omega
  have hav : aV h P τ / 2 ^ p < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  simp only [passSet, atS, addSlot, addi, ld, mi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => ?_
  have c3 : Ctx (P.lay h.D) P.scr τ t3 :=
    ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)
  refine wp_addm (B := (P.lay h.D).B) (by rw [c3.st.sp])
    (by rw [hg.aFr ok sD (by decide)]; exact c3.rFr hg sD (by decide)) fun t4 u4 => ?_
  have c4 : Ctx (P.lay h.D) P.scr τ t4 := c3.upd u4 (by decide) (by decide)
  refine c4.wp_slot hg (d := sA) (by decide) (by decide) (by decide) fun t5 c5 u5 => ?_
  refine wp_andi fun t6 u6 => wp_movi fun t7 u7 => wp_sub fun t8 u8 _ => ?_
  have c8 : Ctx (P.lay h.D) P.scr τ t8 :=
    ((c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).upd u8 (by decide) (by decide)
  refine c8.wp_slot hg (d := sDb) (by decide) (by decide) (by decide) fun t9 c9 u9 => WP.block_nil ?_
  have m9 : t9.mem = s.mem := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have esi2 : t2.gpr .esi = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) := by rw [u2.gpr, u1.gpr, hc.ebp]
  refine ⟨⟨c9, m9 ▸ hk, m9 ▸ hs⟩, ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, esi2]
  · simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.gpr, u3.gpr, esi2]
    rw [u3.mem, u2.mem, u1.mem, hg.aFr ok sD (by decide), hs.2.1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · rw [u9.gpr, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hk.1.2.2.1.2.2.1]
  · simp (disch := decide) only [u9.other, u8.gpr, u7.gpr, u7.other, u6.gpr, u5.gpr]
    rw [u4.mem, u3.mem, u2.mem, u1.mem, hs.1]
    exact mask_bit hav

/-- Between a pass's bytes and its next stage: the slots of pass `p`, the
bytes of pass `p + 1`. -/
abbrev SM (P : EP) (τ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sA) 32 = BitVec.ofNat 32 (aV h P τ / 2 ^ p) ∧
    m.readW ((P.lay h.D).fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW ((P.lay h.D).fr sPc) 32 = BitVec.ofNat 32 (10 - p) ∧
    ∀ j < 2040 - h.D, m (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ % 2 ^ (p + 1))

theorem mod_succ (a p : Nat) : a % 2 ^ (p + 1) = a % 2 ^ p + 2 ^ p * (a / 2 ^ p % 2) := by
  rw [Nat.pow_succ, Nat.mod_mul]

/-- A pass's bytes. -/
theorem passMid_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) ∧
        s.gpr .esi = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
        s.gpr .edi = P.scr + BitVec.ofNat 32 (oY + 8 + h.D + 2 ^ p) ∧ s.gpr .ecx = BitVec.ofNat 32 (dbN h P) ∧
        s.gpr .edx = maskOf (aV h P τ / 2 ^ p % 2 = 1))
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
  have e3 : oY = 2048 := rfl
  have hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
  have hp0 : 0 < 2 ^ p := Nat.two_pow_pos p
  have e1 : oEm = 1024 := rfl
  refine (pass_vp hg (o := oY + 8 + h.D) (d := 2 ^ p) (n := dbN h P) (by omega) hp0 (by omega)
    (c := fun τ => aV h P τ / 2 ^ p % 2 = 1) (X := fun τ m => Kq h P τ m ∧ SH h P τ p m)).mono
    (fun τ s ⟨⟨hc, hk, hs⟩, si, di, cx, dx⟩ => ⟨hc, ⟨hk, hs⟩, si, di, cx, dx⟩)
    fun τ s ⟨hc, m₀, ⟨hk, hs⟩, fr, hsel⟩ => ?_
  have away : ∀ r ∈ [sR P.scr (oY + 8 + h.D) (dbN h P)], Away2 (P.lay h.D) P.scr r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by omega) (by omega)
  have ks : ∀ d, d + 4 ≤ frameBytes → s.mem.readW ((P.lay h.D).fr d) 32 = m₀.readW ((P.lay h.D).fr d) 32 :=
    fun d hd => slot_keep (v := m₀.readW ((P.lay h.D).fr d) 32) fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hg.slot ok (by omega) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega)) rfl
  refine ⟨hc, ⟨K2.keep h hk.1 fr away, sbytes_keep fr (fun r hr => ?_) (by omega) hk.2⟩,
    by rw [ks _ (by decide)]; exact hs.1, by rw [ks _ (by decide)]; exact hs.2.1,
    by rw [ks _ (by decide)]; exact hs.2.2.1, fun j hj => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega) (by omega) (by omega)
  have ms := mod_succ (aV h P τ) p
  by_cases e : j < dbN h P
  · rw [hsel j e]
    by_cases hc' : aV h P τ / 2 ^ p % 2 = 1
    · rw [ite_eq_left hc', show oY + 8 + h.D + 2 ^ p + j = oY + 8 + h.D + (2 ^ p + j) by omega,
        hs.2.2.2 _ (by omega)]
      congr 1; rw [ms, hc']; omega
    · rw [ite_eq_right hc', hs.2.2.2 _ hj]
      congr 1; rw [ms, show aV h P τ / 2 ^ p % 2 = 0 by omega]; omega
  · have hm : s.mem (sa P.scr (oY + 8 + h.D + j)) = m₀ (sa P.scr (oY + 8 + h.D + j)) :=
      fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oY + 8 + h.D + j) (n := 1) (by omega) (by omega) (by omega) _
          (Region.contains_self _ _)
    rw [hm, hs.2.2.2 j hj]; unfold Dp; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The bytes and the slots after a pass. -/
theorem keep3 (P : EP) (hg : Geo (P.lay h.D) P.scr) {τ : State} {m m' : Mem}
    (hf : Frame [slotR (P.lay h.D) sA, slotR (P.lay h.D) sD, slotR (P.lay h.D) sPc] m m') (hk : Kq h P τ m)
    {f : Nat → Byte} (hy : ∀ j < 2040 - h.D, m (sa P.scr (oY + 8 + h.D + j)) = f j) :
    Kq h P τ m' ∧ ∀ j < 2040 - h.D, m' (sa P.scr (oY + 8 + h.D + j)) = f j := by
  obtain ⟨σ', ok⟩ := hg.ok
  have e3 : oY = 2048 := rfl
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have aw : ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR (P.lay h.D) sA, slotR (P.lay h.D) sD, slotR (P.lay h.D) sPc],
      Region.Disjoint (sR P.scr o n) r := fun o n hon r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have e2 : oRsa = 8192 := rfl
  refine ⟨⟨K2.keep h hk.1 hf fun r hr => ?_, sbytes_keep hf (aw _ _ (by omega)) (by omega) hk.2⟩,
    sbytes_keep hf (aw _ _ (by omega)) (by omega) hy⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- Three words stored in the slots of the shift. -/
theorem fr3 (L : Lay) (m : Mem) (a b c : BitVec 32) :
    Frame [slotR L sA, slotR L sD, slotR L sPc] m (((m.writeW (L.fr sA) a).writeW (L.fr sD) b).writeW (L.fr sPc) c) :=
  ((slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))).trans
    ((slot_frame _ _ _ _).mono (by simp))

/-- The words of the three slots after the stores. -/
theorem rd3 (L : Lay) (m : Mem) (a b c : BitVec 32) :
    (((m.writeW (L.fr sA) a).writeW (L.fr sD) b).writeW (L.fr sPc) c).readW (L.fr sA) 32 = a ∧
    (((m.writeW (L.fr sA) a).writeW (L.fr sD) b).writeW (L.fr sPc) c).readW (L.fr sD) 32 = b ∧
    (((m.writeW (L.fr sA) a).writeW (L.fr sD) b).writeW (L.fr sPc) c).readW (L.fr sPc) 32 = c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

/-- The next pass's slots, and the flags of whether it was the last. -/
theorem passNext_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SM h P τ p s.mem) (.block passNext)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ (p + 1) s.mem) ∧
        s.zf = some (decide (10 - (p + 1) = 0))) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.taint [.esp, .ebp] passNext_taint (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hs⟩ => ?_
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hk.1.1 hk.1.2.1
  have hpz := pzF_lt h (τ := τ) hdb
  have haV : aV h P τ < 1024 := by show pzF h P τ + 1 < 1024; omega
  have hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
  have ea : BitVec.ofNat 32 (aV h P τ / 2 ^ p) >>> 1 = BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1)) := by
    rw [ofNat_shr (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)), Nat.div_div_eq_div_mul,
      Nat.pow_one, ← Nat.pow_succ]
  have ed : BitVec.ofNat 32 (2 ^ p) + BitVec.ofNat 32 (2 ^ p) = BitVec.ofNat 32 (2 ^ (p + 1)) := by
    rw [BitVec.ofNat_add_ofNat, Nat.pow_succ]; congr 1; omega
  have ec : BitVec.ofNat 32 (10 - p) - 1 = BitVec.ofNat 32 (10 - (p + 1)) := by
    rw [ofNat_pred (by omega), Nat.sub_sub]
  simp only [passNext, ld, st]
  refine hc.wp_slot hg (d := sA) (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
  refine wp_shr (by decide) fun t2 u2 _ => ?_
  refine (c1.upd u2 (by decide) (by decide)).wp_st hg (d := sA) (by decide) fun t3 c3 m3 => ?_
  refine c3.wp_slot hg (d := sD) (by decide) (by decide) (by decide) fun t4 c4 u4 => ?_
  refine wp_add fun t5 u5 _ => (c4.upd u5 (by decide) (by decide)).wp_st hg (d := sD) (by decide)
    fun t6 c6 m6 => ?_
  refine c6.wp_slot hg (d := sPc) (by decide) (by decide) (by decide) fun t7 c7 u7 => ?_
  refine wp_subi fun t8 u8 _ z8 => (c7.upd u8 (by decide) (by decide)).wp_st hg (d := sPc) (by decide)
    fun t9 c9 m9 => WP.block_nil ?_
  have va : t2.gpr .eax = BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1)) := by rw [u2.gpr, u1.gpr, hs.1, ea]
  have m3' : t3.mem = s.mem.writeW ((P.lay h.D).fr sA) (BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1))) := by
    rw [m3.mem, va, u2.mem, u1.mem]
  have vd : t5.gpr .eax = BitVec.ofNat 32 (2 ^ (p + 1)) := by
    rw [u5.gpr, u4.gpr, m3', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hs.2.1, ed]
  have vc : t8.gpr .eax = BitVec.ofNat 32 (10 - (p + 1)) := by
    rw [u8.gpr, u7.gpr, m6.mem, u5.mem, u4.mem, m3', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hs.2.2.1, ec]
  have mm : t9.mem = ((s.mem.writeW ((P.lay h.D).fr sA) (BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1)))).writeW
      ((P.lay h.D).fr sD) (BitVec.ofNat 32 (2 ^ (p + 1)))).writeW ((P.lay h.D).fr sPc)
        (BitVec.ofNat 32 (10 - (p + 1))) := by
    rw [m9.mem, vc, u8.mem, u7.mem, m6.mem, vd, u5.mem, u4.mem, m3']
  obtain ⟨hk', hy'⟩ := keep3 h P hg (mm ▸ fr3 _ _ _ _ _) hk hs.2.2.2
  obtain ⟨r1, r2, r3⟩ := rd3 (P.lay h.D) s.mem (BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1)))
    (BitVec.ofNat 32 (2 ^ (p + 1))) (BitVec.ofNat 32 (10 - (p + 1)))
  rw [← mm] at r1 r2 r3
  refine ⟨⟨c9, hk', r1, r2, r3, hy'⟩, ?_⟩
  rw [m9.zf, z8, u7.gpr, m6.mem, u5.mem, u4.mem, m3', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
    Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hs.2.2.1, ec, ofNat_beq_zero (by omega)]

/-- A pass. -/
theorem onePass_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) (passOne h.H)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ (p + 1) s.mem) ∧
        s.zf = some (decide (10 - (p + 1) = 0))) :=
  (passSet_vp h P hP hp).seq ((passMid_vp h P hP hp).seq (passNext_vp h P hP hp))

/-- The shift's distance, its first pass's, and its passes. -/
theorem shInit_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ j) (.block shInit)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ 0 s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.taint [.esp, .ebp] shInit_taint (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hy⟩ => ?_
  simp only [shInit, ld, st, mi, addi]
  refine hc.wp_slot hg (d := sPos) (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
  refine wp_addi fun t2 u2 => (c1.upd u2 (by decide) (by decide)).wp_st hg (d := sA) (by decide)
    fun t3 c3 m3 => ?_
  refine wp_movi fun t4 u4 => (c3.upd u4 (by decide) (by decide)).wp_st hg (d := sD) (by decide)
    fun t5 c5 m5 => ?_
  refine wp_movi fun t6 u6 => (c5.upd u6 (by decide) (by decide)).wp_st hg (d := sPc) (by decide)
    fun t7 c7 m7 => WP.block_nil ?_
  have mm : t7.mem = ((s.mem.writeW ((P.lay h.D).fr sA) (BitVec.ofNat 32 (aV h P τ))).writeW
      ((P.lay h.D).fr sD) (BitVec.ofNat 32 1)).writeW ((P.lay h.D).fr sPc) (BitVec.ofNat 32 10) := by
    rw [m7.mem, u6.gpr, u6.mem, m5.mem, u4.gpr, u4.mem, m3.mem, u2.gpr, u1.gpr, u2.mem, u1.mem, hk.1.2.2.2.2.2.1,
      BitVec.ofNat_add_ofNat]
  obtain ⟨hk', hy'⟩ := keep3 h P hg (mm ▸ fr3 _ _ _ _ _) hk hy
  obtain ⟨r1, r2, r3⟩ := rd3 (P.lay h.D) s.mem (BitVec.ofNat 32 (aV h P τ)) (BitVec.ofNat 32 1) (BitVec.ofNat 32 10)
  rw [← mm] at r1 r2 r3
  refine ⟨c7, hk', ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [r1, Nat.pow_zero, Nat.div_one]
  · rw [r2]
  · rw [r3]
  · rw [hy' j hj, Nat.pow_zero, Nat.mod_one, Nat.add_zero]

/-- `DB` shifted left by `pos + 1` bytes. -/
theorem shift_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ j) (shift h.H)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ)) := by
  refine (shInit_vp h P hP).seq ?_
  let I : Nat → State → State → Prop := fun k τ s => k ≤ 10 ∧ Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
    SH h P τ (10 - k) s.mem
  refine (VP.loop (I := I) (fun k => ?_) 9).mono (fun τ s ⟨hc, hk, hs⟩ => ⟨by omega, hc, hk, hs⟩) fun _ _ h => h
  by_cases hk : k ≤ 9
  swap
  · exact VP.empty fun τ s h' => hk (by have := h'.1; omega)
  refine (onePass_vp h P hP (p := 9 - k) (by omega)).mono
    (fun τ s ⟨_, hc, hq, hs⟩ => ⟨hc, hq, by rw [show 9 - k = 10 - (k + 1) by omega]; exact hs⟩)
    fun τ s ⟨⟨hc, hq, hs⟩, z⟩ => ⟨?_, fun h0 => ⟨hc, hq, fun j hj => ?_⟩, fun hpos => ⟨by omega, hc, hq, ?_⟩⟩
  · show eval .ne s = _
    simp only [eval, z, show 10 - (9 - k + 1) = k by omega]
    by_cases h0 : k = 0 <;> simp [h0] <;> omega
  · subst h0
    have hb := shB h hq.1.1 hq.1.2.1
    have hpz := pzF_lt h (τ := τ) hb.2.1
    rw [hs.2.2.2 j hj, Nat.mod_eq_of_lt (show aV h P τ < 2 ^ (9 - 0 + 1) by
      show pzF h P τ + 1 < 1024; omega)]
  · rw [show 10 - k = 9 - k + 1 by omega]; exact hs

end VG.Proof.RsaPss.X86.Vf
