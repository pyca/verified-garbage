import VerifiedGarbage.Proof.Ed448.AArch64.DecodeSteps
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
import VerifiedGarbage.Proof.Ed448.Recover

/-!
# Ed448 verification's equation on AArch64: decoding a point

Untrusted: everything here is checked by Lean. `decode rp xo yo`: the 57
bytes at `rp` decoded into slots `xo` and `yo` (`decode_ok`), with the
register-resident arithmetic: `x20 |= c`, `c = 0` exactly when they decode,
given that `recoverX` is `recoverRef` (`RecoverOk`), and then the slots hold
the point; every slot stays below the products' operand bound.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs workRegs FieldMem)
open VG.Proof.X448.AArch64.Weak (E opSwap)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same fclob cswapE subOp)
open VG.Proof.Curve448.AArch64 (mask)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Impl.X448.AArch64 (ld st slot X2 ACC)

/-- The registers decoding may change. -/
def decClob : List Reg := .x30 :: .x17 :: .x20 :: (workRegs ++ fclob)

theorem bytesAt57_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).take 56 = Spec.Ed448.bytesAt m p 56 := by
  simp only [Spec.Ed448.bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  rw [List.take_left' (by simp)]

theorem bytesAt57_getD (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).getD 56 0 = m (p + BitVec.ofNat 64 56) := by
  simp [Spec.Ed448.bytesAt, List.getD_eq_getElem?_getD]

theorem bytesAt57_len (m : Mem) (p : Addr) : (Spec.Ed448.bytesAt m p 57).length = 57 := by
  simp [Spec.Ed448.bytesAt]

theorem decode_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    {rp : Reg} {p : Addr} (hp : s.gpr rp = p) (hrp : rp = .x0 ∨ rp = .x1) (xo yo : Fin 22)
    (hxy : (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9)) (h11 : E s.mem base 11 = Spec.Ed448.d)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa (decode rp xo.val yo.val) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57)).isSome) ∧
        t.gpr .x20 = s.gpr .x20 ||| c) ∧
      (∀ pt, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57) = some pt →
        E t.mem base xo = pt.X ∧ E t.mem base yo = pt.Y ∧ pt.Z = 1) ∧
      (∀ i : Fin 22, i.val < 12 → i ≠ 1 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 10 → i ≠ xo → i ≠ yo →
        E t.mem base i = E s.mem base i) ∧ E t.mem base 10 = 1 ∧
      BEnv t.mem base ∧ Keeps decClob s t ∧ DFrame base s.mem t.mem := by
  have hxo1 : xo ≠ 1 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hxo12 : xo ≠ 12 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hxo13 : xo ≠ 13 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hyx : yo ≠ xo := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hy10 : yo ≠ 10 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hxlt : xo.val < 14 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hylt : yo.val < 14 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hxo : xo = 6 ∨ xo = 8 := by rcases hxy with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  rw [decode]
  -- `y`, its checks, the sign bit, and 1 in slot 10.
  refine WP.seq (WP.mono (head_ok hs hb hp hrp yo hy10 hr hfar)
    fun s1 ⟨y1, sg1, ⟨c1, hc1, b1⟩, e1, one1, bd1, m10, k1, d1⟩ => ?_)
  have hs1 : Scr s1 base := hs.of_keeps k1 (by decide)
  -- `u`, `v`, `u³v` and `u⁵v³`.
  refine WP.seq (WP.mono (uvOps_ok hs1 bd1 m10 xo yo hxy) fun s2 ⟨k2, bd2, e2⟩ => ?_)
  have hs2 := k2.scr hs1
  -- The root.
  refine WP.seq (WP.mono (Point56.powCall_ok hs2 bd2) fun s3 ⟨k3, bd3, e3, _⟩ => ?_)
  have hs3 := k3.scr hs2
  -- `x` and `v x²`.
  refine WP.seq (WP.mono (xOps_ok hs3 bd3 xo hxo) fun s4 ⟨k4, bd4, mx4, sm4, e4⟩ => ?_)
  have hs4 := k4.scr hs3
  -- The comparison of `v x²` with `u`, and zero in slot 13.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (eqSlotsF_ok hs4 12 13 (lt118 bd4 12) (lt118 bd4 13) (by decide) (by decide))
    fun s5 ⟨⟨c2, hc2, b5⟩, k5, x25⟩ => ?_
  have hs5 := k5.scr hs4
  have bd5 : BEnv s5.mem base := bnd_check bd4 k5.mem x25
  refine WP.mono (VG.Proof.X448.AArch64.Base.constSlot_ok hs5 (o := slot 13) (by decide) (by decide) 0)
    fun s6 ⟨w6, o6, k6⟩ => ?_
  have hs6 : Scr s6 base := hs5.of_keeps k6 (by decide)
  have z13 : ∀ j < 8, limbs s6.mem base (slot (13 : Fin 22).val) j < 2 ^ 56 := fun j hj => by
    change (word s6.mem base (slot 13 + 8 * j)).toNat < _
    rw [w6 j hj]; exact VG.Proof.X448.AArch64.Base.limb_lt _ _
  have l56 : ∀ i : Fin 22, i ≠ 13 → ∀ j < 8, limbs s6.mem base (slot i.val) j = limbs s5.mem base (slot i.val) j := by
    intro i hi j hj
    have h1 := VG.Proof.X448.AArch64.Weak.slot_sep hi
    have h2 := i.isLt
    exact o6.limbs (by simp only [slot] at *; omega) (by simp only [slot]; omega) (by omega)
  have E56 : ∀ i : Fin 22, i ≠ 13 → E s6.mem base i = E s5.mem base i := fun i hi =>
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (l56 i hi))
  have bd6 : BEnv s6.mem base := fun i j hj => by
    by_cases h : i = 13
    · subst h; exact Nat.lt_trans (z13 j hj) (by decide)
    · rw [l56 i h j hj]; exact bd5 i j hj
  have mx6 : Bnd Mb s6.mem base (slot xo.val) := fun j hj => by
    rw [l56 xo hxo13 j hj, k5.mem.limbs hxo1 (by omega)]; exact mx4 j hj
  -- `0 - x` into slot 12.
  refine WP.seq (subOp (o := 12) (a := 13) (b := xo) hs6 bd6 (fun j hj => Nat.lt_trans (z13 j hj) (by decide)) mx6
    (by decide) (Ne.symm hxo12) fun s7 k7 bd7 sm7 e7 => WP.block_nil ?_)
  have hs7 := k7.scr hs6
  -- The sign bit, the check of `x = 0`, the mask, and the swap.
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (signLoad_ok hs7) fun s8 ⟨x8, m8, k8⟩ => ?_
  have hs8 : Scr s8 base := hs7.of_keeps k8 (by decide)
  have hsb : (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 < 2 := by
    have := (s.mem (p + BitVec.ofNat 64 56)).isLt; omega
  have sgn : s8.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [x8, ← sg1,
      k7.mem.word (Or.inl (by simp only [SIGN]; omega)) (Or.inl (by simp only [SIGN, ACC]; omega)) (by decide),
      o6.word (Or.inl (by simp only [SIGN, slot]; omega)) (by decide),
      k5.mem.word (Or.inl (by simp only [SIGN, X2, slot]; omega)) (Or.inl (by simp only [SIGN, CAN]; omega))
        (Or.inl (by simp only [SIGN, ACC]; omega)) (by decide),
      k4.mem.word (Or.inl (by simp only [SIGN]; omega)) (Or.inl (by simp only [SIGN, ACC]; omega)) (by decide),
      k3.mem.word (Or.inl (by simp only [SIGN]; omega)) (Or.inl (by simp only [SIGN, ACC]; omega)) (by decide),
      k2.mem.word (Or.inl (by simp only [SIGN]; omega)) (Or.inl (by simp only [SIGN, ACC]; omega)) (by decide)]
  have bd8 : BEnv s8.mem base := m8 ▸ bd7
  rw [WP.block_append_iff]
  refine WP.mono (zeroSignF_ok hs8 bd8 xo hxo1 hsb sgn) fun s9 ⟨⟨c3, hc3, b9⟩, lo9, k9, bd9⟩ => ?_
  have hs9 := k9.scr hs8
  have sgn9 : s9.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [k9.regs.1 _ (by decide)]; exact sgn
  rw [WP.block_append_iff]
  refine WP.mono (negMask_ok hs9 hsb sgn9) fun s10 ⟨m10', mm10, k10⟩ => ?_
  have hs10 : Scr s10 base := hs9.of_keeps k10 (by decide)
  rw [negSwap, WP.block_append_iff]
  refine WP.mono (mov6_ok s10) fun s11 ⟨x6, mm11, k11⟩ => ?_
  have hs11 : Scr s11 base := hs10.of_keeps k11 (by decide)
  have bd11 : BEnv s11.mem base := by rw [mm11, mm10]; exact bd9
  refine WP.mono (cswapE hs11 bd11 xo 12 hxo12 (sw := decide (VG.Proof.X448.AArch64.limbs s9.mem base X2 0 % 2 ^^^
    (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)) (by rw [x6, m10']; rfl)) fun t ⟨kt, bdt, _, _, _, _, et⟩ => ?_
  -- The values.
  have e1' : ∀ i : Fin 22, i ≠ yo → i ≠ 10 → E s1.mem base i = E s.mem base i := e1
  have h11' : E s1.mem base 11 = Spec.Ed448.d := by
    rw [e1' 11 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide) (by decide), h11]
  obtain ⟨u2, vv2, t2, w2, k2'⟩ := uvEnv_eval xo yo hxy (E s1.mem base)
  simp only [one1, h11', y1] at u2 vv2 t2 w2
  simp only [← e2] at u2 vv2 t2 w2 k2'
  generalize hY : VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) = Y at *
  have r21 : E s3.mem base 21 = rootPow (E s2.mem base 12) := by rw [e3, rootEnv_eval]
  have r3k : ∀ i : Fin 22, i.val < 14 → E s3.mem base i = E s2.mem base i := fun i hi => by
    rw [e3, rootEnv_keep _ _ hi]
  obtain ⟨x4, x12, x13, k4'⟩ := xEnv_eval xo hxo (E s3.mem base)
  rw [← e4] at x4 x12 x13 k4'
  rw [r3k xo hxlt, t2, r21, w2] at x4 x12
  rw [r3k 3 (by decide), vv2] at x12
  rw [x13, r3k 13 (by decide), u2] at hc2
  rw [x12] at hc2
  generalize hu : Y * Y - 1 = u at *
  generalize hv : Spec.Ed448.d * (Y * Y) - 1 = v at *
  generalize ht : u * u * u * v = tt at *
  generalize hx : tt * rootPow (tt * ((u * v) * (u * v))) = x at *
  -- From `s4` to `s9`, the slots but 12, 13 and `X2` keep their values.
  have E79 : ∀ i : Fin 22, i ≠ 1 → i ≠ 12 → i ≠ 13 → E s9.mem base i = E s4.mem base i := fun i h1 h12 h13 => by
    rw [k9.mem.E h1, m8, sm7.env (by simp [h12]), E56 i h13, k5.mem.E h1]
  have x8 : E s8.mem base xo = x := by
    rw [m8, sm7.env (by simp [hxo12]), E56 xo hxo13, k5.mem.E hxo1, x4]
  rw [x8] at hc3 lo9
  have n12 : E s9.mem base 12 = 0 - x := by
    have h0 : E s6.mem base 13 = 0 := VG.Proof.X448.AArch64.Base.F_of_words w6
    rw [k9.mem.E (by decide), m8, e7, Function.update_self, h0, E56 xo hxo13, k5.mem.E hxo1, x4]
  have hD := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem p 57) (bytesAt57_len _ _)
    (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) ((s.mem (p + BitVec.ofNat 64 56)).toNat)
    (by rw [bytesAt57_take]) (by rw [bytesAt57_getD]) Y u v tt x hY hu hv ht hx
  have s11x : E s11.mem base = E s9.mem base := by rw [mm11, mm10]
  -- The final `x`.
  have xt : E t.mem base xo =
      if (x.val % 2 == 1) == ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128 == 1) then x else (x - x) - x := by
    rw [et, VG.Proof.X448.AArch64.opSwap, Function.update_of_ne hxo12, Function.update_self, s11x, n12,
      E79 xo hxo1 hxo12 hxo13, x4, sub_self]
    have hlo : VG.Proof.X448.AArch64.limbs s9.mem base X2 0 % 2 = x.val % 2 := lo9
    rw [hlo]
    have hx2 : x.val % 2 < 2 := Nat.mod_lt _ (by decide)
    generalize x.val % 2 = a at hx2 ⊢
    generalize (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = sb at hsb ⊢
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
      rfl
  -- What the rest keeps.
  have keepE : ∀ i : Fin 22, i ≠ 1 → i ≠ xo → i ≠ 12 → i ≠ 13 → E t.mem base i = E s4.mem base i := by
    intro i h1 hx h12 h13
    rw [et, VG.Proof.X448.AArch64.opSwap, Function.update_of_ne h12, Function.update_of_ne hx, s11x, E79 i h1 h12 h13]
  have kY : E t.mem base yo = Y := by
    have hy1 : yo ≠ 1 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    have hy12 : yo ≠ 12 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    have hy13 : yo ≠ 13 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    rw [keepE yo hy1 hyx hy12 hy13, k4' yo hyx hy12, r3k yo hylt,
      k2' yo (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hy12 hy13 hyx, y1]
  have kk : ∀ i : Fin 22, i.val < 12 → i ≠ 1 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ xo → E t.mem base i = E s1.mem base i := by
    intro i hi h1 h3 h4 h5 hix
    have h12 : i ≠ 12 := fun h => by rw [h] at hi; exact absurd hi (by decide)
    have h13 : i ≠ 13 := fun h => by rw [h] at hi; exact absurd hi (by decide)
    rw [keepE i h1 hix h12 h13, k4' i hix h12, r3k i (by omega), k2' i h3 h4 h5 h12 h13 hix]
  refine ⟨⟨c1 ||| c2 ||| c3, ?_, ?_⟩, fun pt hpt => ?_, fun i hi h1 h3 h4 h5 h10 hix hiy => ?_, ?_, bdt, ?_, ?_⟩
  · rw [or_eq_zero64, or_eq_zero64, hc1, hc2, hc3, hD]
    by_cases hall : ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall]
      exact ⟨fun _ => rfl, fun _ => ⟨⟨hall.1, hall.2.1⟩, hall.2.2⟩⟩
    · rw [ite_eq_right hall]
      exact ⟨fun h => absurd ⟨h.1.1, h.1.2, h.2⟩ hall, fun h => absurd h (by simp)⟩
  · rw [kt.regs.1 _ (by decide), k11.1 _ (by decide), k10.1 _ (by decide), b9, k8.1 _ (by decide),
      k7.regs.1 _ (by decide), k6.1 _ (by decide), b5, k4.regs.1 _ (by decide), k3.regs.1 _ (by decide),
      k2.regs.1 _ (by decide), b1]
    simp only [BitVec.or_assoc]
  · rw [hD] at hpt
    by_cases hall : ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall] at hpt
      cases hpt
      exact ⟨xt, kY, rfl⟩
    · rw [ite_eq_right hall] at hpt
      cases hpt
  · rw [kk i hi h1 h3 h4 h5 hix, e1' i hiy h10]
  · rw [kk 10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide), one1]
  · exact ((((((((((k1.mono (by decide)).trans (k2.regs.mono (by decide))).trans (k3.regs.mono (by decide))).trans
      (k4.regs.mono (by decide))).trans (k5.regs.mono (by decide))).trans (k6.mono (by decide))).trans
      (k7.regs.mono (by decide))).trans (k8.mono (by decide))).trans (k9.regs.mono (by decide))).trans
      ((k10.mono (by decide)).trans (k11.mono (by decide)))).trans (kt.regs.mono (by decide))
  · have d6 : DFrame base s5.mem s6.mem := DFrame.of_outside o6 (by simp only [slot]; omega)
    have d8 : DFrame base s7.mem s8.mem := by rw [m8]; exact fun _ _ _ _ => rfl
    have d11 : DFrame base s9.mem s11.mem := by rw [mm11, mm10]; exact fun _ _ _ _ => rfl
    exact ((((((((d1.trans (fkeep_dframe k2)).trans (DFrame.of_outside2 (Nat.le_refl _) k3.mem)).trans (fkeep_dframe k4)).trans
      (cframe_dframe k5.mem)).trans d6).trans (fkeep_dframe k7)).trans d8).trans
      ((cframe_dframe k9.mem).trans d11)).trans (fkeep_dframe kt)

end VG.Proof.Ed448.AArch64
