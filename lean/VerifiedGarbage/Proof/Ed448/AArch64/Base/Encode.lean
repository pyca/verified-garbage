import VerifiedGarbage.Proof.Ed448.AArch64.BaseEncode
import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Proof.X448.AArch64.Base.Add
import VerifiedGarbage.Proof.X448.AArch64.Fast.Finish
import VerifiedGarbage.Proof.X448.AArch64.Fast.Inv

/-!
# Ed448 base-point multiplication on AArch64: the encoding

Untrusted: everything here is checked by Lean. `encode`, for `R = (X : Y : Z)`
in slots 0–2 (`encode_ok`): `Z` inverted into `T7` (slot 21, `invert_ok`);
`Y` kept in slot 3 and `x = X/Z` fully reduced in `X2` (slot 1), its low bit
stored as the top bit of the output's byte 56 (`signByte_ok`); then `Y` back
in `X2`, and X448's `finish` writes `Y/Z` fully reduced to the output's first
56 bytes and restores the registers. Together, the 57 bytes are
`encodePoint R` (`encodePoint_code`).
-/

namespace VG.Proof.Ed448.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot X2 T7 ACC)
open VG.Impl.X448.AArch64.Fast (saved)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 Saved ofs FieldMem writeW8_apply
  moveOutput_ok freeze_ok)
open VG.Proof.X448.AArch64.Weak (Index Env E_update E_outside)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same SavedX SavedV invert_ok invEnv invEnv_eval invEnv_x2
  invEnv_keep IKeep env_update block_codeOf
  mulOp)
open VG.Proof.X448.AArch64.Base (copyOp)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The inversion's addition chain keeps slots 0 and 3. -/
theorem invEnv_0 (e : Env) : invEnv e 0 = e 0 := invEnv_keep e 0 (by decide)
theorem invEnv_3 (e : Env) : invEnv e 3 = e 3 := invEnv_keep e 3 (by decide)

/-- A fully reduced slot (sixteen limbs below `2^28`) is below `Ib`. -/
theorem bnd_of_bounded {m : Mem} {base : Addr} {o : Nat} (h : VG.Proof.X448.AArch64.Bounded m base o) :
    Bnd Ib m base o := fun i hi => Nat.lt_trans (h i (by omega)) (by decide)

/-- `encode`: the 57 bytes at `p` are the encoding of `R` (slots 0–2), and the
registers are restored from the working space. -/
theorem encode_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hp : s.gpr .x20 = p) (hw : ∀ j < 57, InRegions s.wr (off p j) 1)
    (hpd : ∀ j < 57, 8192 ≤ ofs base (off p j)) (hfar : ∀ j < 8192, 57 ≤ ofs p (off base j))
    {g : Reg → BitVec 64} (sv : Saved base g s.mem) (svx : SavedX base g s.mem)
    {gv : VReg → BitVec 128} (svV : SavedV base gv s.mem) :
    WP isa encode s fun t =>
      t.gpr .x19 = g .x19 ∧ t.gpr .x20 = g .x20 ∧ (∀ k < 8, t.gpr (saved k) = g (saved k)) ∧
      (∀ k < 8, (t.v (VG.Impl.Curve448.AArch64.Neon.V (8 + k))).extractLsb' 0 64 =
        (gv (VG.Impl.Curve448.AArch64.Neon.V (8 + k))).extractLsb' 0 64) ∧
      t.gpr .x30 = s.gpr .x30 ∧ Frame [⟨base, 8192⟩, ⟨p, 57⟩] s.mem t.mem ∧
      Spec.Ed448.bytesAt t.mem p 57 = Spec.Ed448.encodePoint (pt (EV s.mem base) 0 1 2) := by
  have far56 : 8192 ≤ ofs base (p + BitVec.ofNat 64 56) := hpd 56 (by decide)
  have fr : ∀ {m m' : Mem}, Outside base 0 8192 m m' → Frame [⟨base, 8192⟩, ⟨p, 57⟩] m m' :=
    fun h => (VG.Proof.X448.AArch64.Outside.frame h).mono (by simp)
  rw [encode]
  -- `1/Z` into `T7`.
  refine WP.seq (WP.mono (invert_ok hs hb) fun s1 ⟨k1, b1, e1⟩ => ?_)
  have hs1 : Scr s1 base := hs.of_keeps k1.regs (by decide)
  simp only [sign, List.append_assoc]
  rw [List.cons_append]
  refine WP.seq ?_
  -- The output pointer.
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (moveOutput_ok s1) fun s2 ⟨x2, m2, k2⟩ => ?_
  have hs2 : Scr s2 base := hs1.of_keeps k2 (by decide)
  have b2 : BEnv s2.mem base := by rw [m2]; exact b1
  -- `Y` to slot 3, and `X/Z` into `X2`.
  rw [WP.block_append_iff]
  refine block_codeOf (copyOp hs2 b2 3 1 fun s3 k3 b3 _ _ e3 =>
    mulOp (k3.scr hs2) b3 1 0 21 (Or.inr (by decide)) fun s4 k4 b4 m4 _ e4 => WP.block_nil ?_)
  have hs4 : Scr s4 base := k4.scr (k3.scr hs2)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.toLegacy_ok' hs4 (o := X2) (by decide) (by decide)
    (fun i hi => Nat.lt_trans (m4 i hi) (by decide))) fun s5 ⟨c5, l5, v5⟩ => ?_
  have hs5 := hs4.of_keeps c5.1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs5 l5) fun s6 ⟨l6, v6, m6, k6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  have x6 : s6.gpr .x1 = p := by
    rw [k6.1 _ (by decide), c5.1.1 _ (by decide), k4.regs.1 _ (by decide), k3.regs.1 _ (by decide), x2,
      k1.regs.1 _ (by decide), hp]
  have w6 : s6.wr = s.wr := by
    rw [k6.2.2, c5.1.2.2, k4.regs.2.2, k3.regs.2.2, k2.2.2, k1.regs.2.2]
  -- The sign byte.
  rw [WP.block_append_iff]
  refine WP.mono (signByte_ok hs6 x6 (by rw [w6]; exact hw 56 (by decide))) fun s7 ⟨m7, k7⟩ => ?_
  have hs7 := hs6.of_keeps k7 (by decide)
  have o67 : Outside base 8192 (2 ^ 64) s6.mem s7.mem := fun x hx => by
    rw [m7, writeW8_apply, ite_eq_right_iff.mpr]
    intro h; subst h
    have hlt := (p + BitVec.ofNat 64 56 - base).isLt
    simp only [ofs] at far56 hx
    omega
  have f46 : FieldMem base X2 s4.mem s6.mem := c5.2.trans m6
  have e6 : EV s6.mem base = Function.update (EV s4.mem base) 1
      (VG.Proof.X448.AArch64.Weak.F s6.mem base X2) := E_update f46
  have e76 : ∀ i : Index, EV s7.mem base i = EV s6.mem base i := fun i =>
    E_outside o67 i (Or.inl (by have := i.isLt; simp only [slot]; omega))
  have b7 : BEnv s7.mem base := by
    intro i j hj
    rw [o67.limbs (Or.inl (by have := i.isLt; simp only [slot]; omega))
      (by have := i.isLt; simp only [slot]; omega) (by omega)]
    by_cases hi : i = 1
    · subst hi; exact bnd_of_bounded l6 j hj
    · rw [f46.limbs (VG.Proof.X448.AArch64.Weak.slot_sep hi) (by have := i.isLt; simp only [slot, ACC]; omega)
        (by omega)]
      exact b4 i j hj
  -- `Y` back in `X2`.
  refine block_codeOf (copyOp hs7 b7 1 3 fun s8 k8 b8 _ _ e8 => WP.block_nil ?_)
  have hs8 : Scr s8 base := k8.scr hs7
  have x8 : s8.gpr .x1 = p := by rw [k8.regs.1 _ (by decide), k7.1 _ (by decide)]; exact x6
  have w8 : s8.wr = s.wr := by rw [k8.regs.2.2, k7.2.2]; exact w6
  -- The saved registers, through the operations since the entry.
  have o16 : Outside2 base 64 2816 ACC 1152 s.mem s6.mem :=
    (((k1.mem.trans (by rw [m2]; exact Outside2.refl _ _ _ _ _ _)).trans k3.mem).trans k4.mem).trans
      (VG.Proof.X448.AArch64.Fast.fieldMem_outside2 (o := 1) f46)
  have sv8 : Saved base g s8.mem :=
    ((sv.outside2 o16 (by decide) (by decide)).outside o67 (by decide)).outside2 k8.mem (by decide) (by decide)
  have svx8 : SavedX base g s8.mem :=
    ((svx.outside2 o16 (by decide) (by decide)).outside o67 (Or.inr (by decide))).outside2 k8.mem
      (by decide) (by decide)
  have svV8 : SavedV base gv s8.mem :=
    ((svV.outside2 o16 (by decide) (by decide)).outside o67 (Or.inr (by decide))).outside2 k8.mem
      (by decide) (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Fast.finish_ok hs8 b8 x8 (fun j hj => by rw [w8]; exact hw j (by omega))
    (fun j hj => Nat.le_trans (by decide) (hfar j hj)) sv8 svx8 svV8)
    fun t ⟨t19, t20, tx, tv, kt, ft, vt⟩ => ⟨t19, t20, tx, tv, ?_, ?_, ?_⟩
  · rw [kt.1 _ (by decide), k8.regs.1 _ (by decide), k7.1 _ (by decide), k6.1 _ (by decide),
      c5.1.1 _ (by decide), k4.regs.1 _ (by decide), k3.regs.1 _ (by decide), k2.1 _ (by decide),
      k1.regs.1 _ (by decide)]
  · -- Only the working space and the output change.
    have f67 : Frame [⟨base, 8192⟩, ⟨p, 57⟩] s6.mem s7.mem := by
      rw [m7]
      refine (Frame.refl _ _).writeW (r := ⟨p, 57⟩) (by simp) _ ?_
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      omega
    have ft' : Frame [⟨base, 8192⟩, ⟨p, 57⟩] s8.mem t.mem := fun x hx => ft x fun r hr hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hx _ (by simp) hc
      · exact hx ⟨p, 57⟩ (by simp) (by simp only [Region.Contains] at hc ⊢; omega)
    exact (((fr (o16.whole (by decide) (by decide))).trans f67).trans
      (fr (k8.mem.whole (by decide) (by decide)))).trans ft'
  · -- The values.
    have v1 : EV s8.mem base 1 = EV s.mem base 1 := by
      simp only [e8, e76, e6, e4, e3, m2, e1, VG.Proof.X448.AArch64.opCopy, Function.update_apply, invEnv_x2, Fin.reduceEq,
        ↓reduceIte]
    have v21 : EV s8.mem base 21 = Proof.X448.invert (EV s.mem base 2) := by
      simp only [e8, e76, e6, e4, e3, m2, e1, VG.Proof.X448.AArch64.opCopy, Function.update_apply, invEnv_eval, Fin.reduceEq,
        ↓reduceIte]
    have vx : VG.Proof.X448.AArch64.F s5.mem base X2 = EV s.mem base 0 * Proof.X448.invert (EV s.mem base 2) := by
      rw [v5]
      change EV s4.mem base 1 = _
      simp only [e4, e3, m2, e1, VG.Proof.X448.AArch64.opCopy, Function.update_apply, invEnv_0, invEnv_eval, Fin.reduceEq,
        ↓reduceIte]
    -- The sign: the low bit of `x`, fully reduced.
    have sgn : (word s6.mem base X2).toNat % 2 =
        (EV s.mem base 0 * Proof.X448.invert (EV s.mem base 2)).val % 2 := by
      rw [← vx]
      have hv : (VG.Proof.X448.AArch64.F s5.mem base X2).val =
          VG.Proof.X448.AArch64.fe s5.mem base X2 % Spec.X448.P := rfl
      rw [hv, ← v6, show VG.Proof.X448.AArch64.fe s6.mem base X2 =
        VG.Proof.X448.valN (limbs s6.mem base X2) 16 from rfl, VG.Proof.Ed448.AArch64.valN_mod_two]
      rfl
    have byte : t.mem (p + BitVec.ofNat 64 56) = BitVec.ofNat 8 (128 * ((EV s.mem base 0 *
        Proof.X448.invert (EV s.mem base 2)).val % 2)) := by
      have hout : ∀ r ∈ ([⟨base, 8192⟩, ⟨p, 56⟩] : List Region), ¬ r.Contains (p + BitVec.ofNat 64 56) 1 := by
        intro r hr hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [Region.Contains] at hc
          simp only [ofs] at far56
          omega
        · simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at hc
          omega
      rw [ft _ hout]
      rw [show s8.mem (p + BitVec.ofNat 64 56) = s7.mem (p + BitVec.ofNat 64 56) from
        k8.mem _ (by simp only [ofs] at far56 ⊢; omega) (by simp only [ofs, ACC] at far56 ⊢; omega)]
      rw [m7, writeW8_apply]
      simp only [ite_true, sgn]
    rw [VG.Proof.Ed448.AArch64.bytesAt_57, vt, byte, VG.Proof.X448.encodeUCoordinate_eq, v1, v21]
    exact (VG.Proof.Ed448.encodePoint_code _ _ _).symm

end VG.Proof.Ed448.AArch64.Base
