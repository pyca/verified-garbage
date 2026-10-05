import VerifiedGarbage.Proof.Ed448.AArch64.VerifyChecks
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.X448.AArch64.Base.Verified
import VerifiedGarbage.Proof.X448.AArch64.Fast.Verified
import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyVerified
/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Base.Encode`. -/
section

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
open VG.Proof.X448.AArch64.Weak (Index Env invEnv invEnv_eval invEnv_x2 E_update E_outside)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same SavedX SavedV invert_ok IKeep env_update block_codeOf
  mulOp)
open VG.Proof.X448.AArch64.Base (copyOp)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The inversion's addition chain keeps slots 0 and 3. -/
theorem invEnv_0 (e : Env) : invEnv e 0 = e 0 := rfl
theorem invEnv_3 (e : Env) : invEnv e 3 = e 3 := rfl

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

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Base.Setup`. -/
section

/-!
# Ed448 base-point multiplication on AArch64: the setup

Untrusted: everything here is checked by Lean. X448's comb's `entry` (the
registers saved, every slot zeroed), the bits of all 57 bytes of the scalar
(`bits_ok`), and both accumulators at `[G] B` for `G = 8 Σ_{j < 57} 256^j`
(`baseG57`): `StepInv` of the comb of 57 tables, for step 0.
-/

namespace VG.Proof.Ed448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 Saved bitRegs ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.X448.AArch64.Base (StepInv pt block1_ok consts_ok bnd_of_words F_of_words)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.Ed448 (Rep baseAff)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- What the setup leaves, from the function's entry state `sE`. -/
structure CombReady (sE : State) (base : Addr) (k : Nat) (t : State) : Prop where
  inv : StepInv 57 t base k 0 t
  saved : Saved base sE.gpr t.mem
  out : t.gpr .x20 = sE.gpr .x0
  savedX : SavedX base sE.gpr t.mem
  savedV : SavedV base sE.v t.mem
  lr : t.gpr .x30 = sE.gpr .x30
  rd : t.rd = sE.rd
  wr : t.wr = sE.wr
  mem : Outside base 0 8192 sE.mem t.mem

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hp : ∀ i < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    bytesAt m' p 57 = bytesAt m p 57 := by
  rw [VG.Proof.Ed448.bytesAt_eq, VG.Proof.Ed448.bytesAt_eq]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

theorem setup_ok {s : State} {base kp : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) (hk : s.gpr .x1 = kp)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (kp + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (kp + BitVec.ofNat 64 q)) :
    WP isa VG.Impl.Ed448.AArch64.baseSetup s (CombReady s base (decodeLE (bytesAt s.mem kp 57))) := by
  unfold VG.Impl.Ed448.AArch64.baseSetup
  refine WP.seq (WP.mono (block1_ok hb hw hn) fun a ⟨ha, sa, oa, xa, va, ka, za, outa⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.bits_ok ha (by rw [ka.1 _ (by decide)]; exact hk)
    (by rw [ka.2.1, ka.2.2]; exact hkr) hkd) fun b ⟨_, gb, rdb, wrb, ob, bitsb⟩ => ?_)
  have kb : Keeps (.x1 :: bitRegs) a b := ⟨gb, rdb, wrb⟩
  have hsb : Scr b base := ha.of_keeps kb (by decide)
  rw [bytesAt_outside outa hkd] at bitsb
  refine WP.mono (consts_ok hsb _) fun t ⟨tv, tOut, kt, tc⟩ => ?_
  have hst : Scr t base := hsb.of_keeps kt (by decide)
  -- Every word outside the constant slots and the bits is as `block1` left it.
  have wt : ∀ {d : Nat}, d + 8 ≤ 64 ∨ 832 ≤ d → d + 8 ≤ BITS ∨ BITS + 456 ≤ d → d + 8 ≤ 8192 →
      word t.mem base d = word a.mem base d := fun h1 h2 h3 => by
    rw [tOut.word (by omega) h3, ob.word h2 h3]
  -- The slots `block1` zeroed.
  have zs : ∀ i : Index, ∀ w < 8, word a.mem base (slot i.val + 8 * w) = 0 := fun i w hw => by
    have := i.isLt
    have hz := za (16 * i.val + w) (by omega)
    have e : slot 0 + 8 * (16 * i.val + w) = slot i.val + 8 * w := by simp only [slot]; omega
    rw [show VG.Proof.X448.AArch64.limbs a.mem base (slot 0) (16 * i.val + w) =
      (word a.mem base (slot i.val + 8 * w)).toNat by
        simp only [VG.Proof.X448.AArch64.limbs]; rw [e]] at hz
    exact BitVec.eq_of_toNat_eq hz
  have zt : ∀ i : Index, 6 ≤ i.val → ∀ w < 8, word t.mem base (slot i.val + 8 * w) = 0 := fun i hi w hw => by
    have := i.isLt
    rw [wt (by simp only [slot]; omega) (by simp only [slot, BITS]; omega) (by simp only [slot]; omega)]
    exact zs i w hw
  have ev : ∀ (i : Index) (v : Spec.X448.Fe), (∀ w < 8, word t.mem base (slot i.val + 8 * w) = limb v w) →
      VG.Proof.X448.AArch64.Weak.E t.mem base i = v := fun i v h => F_of_words h
  have pA : VG.Proof.X448.AArch64.Base.pt (VG.Proof.X448.AArch64.Weak.E t.mem base) 0 1 2 = VG.Proof.X448.basePt Impl.X448.baseG57 := by
    simp only [VG.Proof.X448.AArch64.Base.pt, VG.Proof.X448.basePt]
    rw [ev 0 _ fun w hw => (tv w hw).1, ev 1 _ fun w hw => (tv w hw).2.1, ev 2 _ fun w hw => (tv w hw).2.2.1]
  have pB : VG.Proof.X448.AArch64.Base.pt (VG.Proof.X448.AArch64.Weak.E t.mem base) 3 4 5 = VG.Proof.X448.basePt Impl.X448.baseG57 := by
    simp only [VG.Proof.X448.AArch64.Base.pt, VG.Proof.X448.basePt]
    rw [ev 3 _ fun w hw => (tv w hw).2.2.2.1, ev 4 _ fun w hw => (tv w hw).2.2.2.2.1,
      ev 5 _ fun w hw => (tv w hw).2.2.2.2.2]
  have hG : Rep (VG.Proof.X448.basePt Impl.X448.baseG57) (((VG.Proof.X448.combG 57 : ℤ) + 0) • baseAff) := by
    rw [VG.Proof.X448.combG_57, add_zero, natCast_zsmul]; exact VG.Proof.X448.baseG57_ok
  refine ⟨⟨by decide, hst, fun i w hw => ?_, fun w hw => ?_, by rw [tc]; rfl, fun q hq => ?_,
      by rw [pA]; exact hG, by rw [pB]; exact hG, rfl, rfl, rfl, rfl, Outside2.refl _ _ _ _ _ _⟩,
    ⟨by rw [wt (by decide) (by decide) (by decide)]; exact sa.1,
      by rw [wt (by decide) (by decide) (by decide)]; exact sa.2⟩,
    by rw [kt.1 _ (by decide), kb.1 _ (by decide)]; exact oa,
    fun k hk => by
      rw [wt (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega)
        (by simp only [Impl.X448.AArch64.Fast.SAVE, BITS]; omega) (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega)]
      exact xa k hk,
    (va.outside ob (by simp only [BITS, Impl.X448.AArch64.Fast.VSAVE]; omega)).outside tOut
      (by simp only [Impl.X448.AArch64.Fast.VSAVE]; omega),
    by rw [kt.1 _ (by decide), kb.1 _ (by decide), ka.1 _ (by decide)],
    by rw [kt.2.1, kb.2.1, ka.2.1], by rw [kt.2.2, kb.2.2, ka.2.2],
    (outa.trans (ob.mono (by omega) (by simp only [BITS]; omega))).trans (tOut.mono (by omega) (by omega))⟩
  · -- Every slot's limbs are below `Ib`.
    by_cases hi : i.val < 6
    · have hi6 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
        rcases i with ⟨i, hlt⟩; simp only [Fin.ext_iff] at hi ⊢; omega
      rcases hi6 with rfl | rfl | rfl | rfl | rfl | rfl
      · exact bnd_of_words (fun w hw => (tv w hw).1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.2.2) w hw
    · show (word t.mem base (slot i.val + 8 * w)).toNat < Ib
      rw [zt i (by omega) w hw]; decide
  · show (word t.mem base (slot (19 : Index).val + 8 * w)).toNat = 0
    rw [zt 19 (by decide) w hw]; rfl
  · have hn' := hn
    rw [tOut _ (by rw [VG.Proof.X448.AArch64.Base.ofs_off0 base (by simp only [BITS]; omega)]; simp only [BITS]; omega)]
    exact bitsb q hq

end VG.Proof.Ed448.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Base.Main`. -/
section

/-!
# Ed448 base-point multiplication on AArch64: the whole function

Untrusted: everything here is checked by Lean. The correctness of
`vg_ed448_scalar_base` against `scalarBaseLocal` (`BaseContract.lean`): the
comb of 57 tables leaves `R` representing `[k]B` (`combine_ok`), whose
encoding is `encodePoint (pointMul k B)` since both represent the same affine
point (`encodePoint_rep`); every write but the result's is in the working
space, so the scalar is read unchanged, and the callee-saved registers are
restored from it.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word Outside Outside2 Saved ofs far)
open VG.Proof.X448.AArch64.Base (loop_ok combine_ok)
open VG.Proof.Ed448.AArch64.Base (setup_ok encode_ok)
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- A byte of the working space is beyond the output. -/
theorem far_out {base p : Addr} (hd : (⟨p, 57⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 57 ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ 57
  omega

theorem decodeLE_57_lt (kb : List Byte) (hk : kb.length = 57) : decodeLE kb < 256 ^ 57 := by
  have h := VG.Proof.Ed448.decodeLE_lt' kb
  rwa [hk] at h

theorem scalarBase_correct {s : State} (hp : scalarBaseLocal.pre s) :
    WP isa scalarBase s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧
      scalarBaseLocal.post s t := by
  obtain ⟨hr, hw, hdo, hds, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .x2 = b := ⟨_, rfl⟩
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hbase]; simp
  rw [hbase] at hn hdo hds
  have hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 q) 1 := fun q hq =>
    ⟨⟨s.gpr .x1, 57⟩, by rw [hr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hkd : ∀ q < 57, 8192 ≤ ofs base (s.gpr .x1 + BitVec.ofNat 64 q) := fun q hq => far hds hq (by decide)
  have hod : ∀ q < 57, 8192 ≤ ofs base (s.gpr .x0 + BitVec.ofNat 64 q) := fun q hq => far hdo hq (by decide)
  set kb := bytesAt s.mem (s.gpr .x1) 57
  set k := decodeLE kb
  unfold scalarBase
  refine WP.seq (WP.mono (setup_ok hbase hws hn rfl hkr hkd) fun s1 R => ?_)
  refine WP.seq (WP.mono (loop_ok (by decide) (s₀ := s1) 57 s1 (by decide) le_rfl
    (by rw [Nat.sub_self]; exact R.inv)) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (combine_ok (decodeLE_57_lt kb (by simp [kb, VG.Proof.Ed448.bytesAt_eq, Spec.X25519.bytesAt])) h2)
    fun s3 ⟨f3, r3⟩ => ?_)
  -- The encoding.
  have out3 : s3.gpr .x20 = s.gpr .x0 := by rw [f3.out, R.out]
  have wr3 : s3.wr = s.wr := by rw [f3.wr, R.wr]
  have o13 : Outside2 base 64 2816 ACC 1152 s1.mem s3.mem := f3.mem
  refine WP.mono (encode_ok f3.scr f3.env out3
    (fun j hj => ⟨⟨s.gpr .x0, 57⟩, by rw [wr3, hw]; simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => hod j hj) (fun j hj => far_out hdo hj)
    (R.saved.outside2 o13 (by decide) (by decide)) (R.savedX.outside2 o13 (by decide) (by decide))
    (R.savedV.outside2 o13 (by decide) (by decide)))
    fun t ⟨t19, t20, tx, tv, t30, _, vt⟩ => ⟨?_, ?_, ?_⟩
  · intro r hr
    have lr : t.gpr .x30 = s.gpr .x30 := by rw [t30, f3.lr, R.lr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact t19
    · exact t20
    · exact tx 0 (by decide)
    · exact tx 1 (by decide)
    · exact tx 2 (by decide)
    · exact tx 3 (by decide)
    · exact tx 4 (by decide)
    · exact tx 5 (by decide)
    · exact tx 6 (by decide)
    · exact tx 7 (by decide)
    · exact lr
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tv 0 (by decide)
    · exact tv 1 (by decide)
    · exact tv 2 (by decide)
    · exact tv 3 (by decide)
    · exact tv 4 (by decide)
    · exact tv 5 (by decide)
    · exact tv 6 (by decide)
    · exact tv 7 (by decide)
  · show bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarBase kb
    rw [vt, Spec.Ed448.scalarBase]
    change Spec.Ed448.encodePoint (VG.Proof.X448.AArch64.Base.pt _ 0 1 2) = _
    rw [VG.Proof.Ed448.encodePoint_rep r3,
      VG.Proof.Ed448.encodePoint_rep (VG.Proof.Ed448.pointMul_rep k VG.Proof.Ed448.basePoint_rep),
      natCast_zsmul]

end VG.Proof.Ed448.AArch64

end
