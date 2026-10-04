import VerifiedGarbage.Proof.Ed448.AArch64.VerifySign
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyRoot
import VerifiedGarbage.Proof.Ed448.AArch64.BaseField
import VerifiedGarbage.Proof.Ed448.VerifyFormulas
import VerifiedGarbage.Proof.Ed448.Recover

/-!
# Ed448 verification's equation on AArch64: decoding a point

`decode rp xo yo`: the 57 bytes at `rp` decoded into slots `xo` and `yo`
(`decode_ok`): `x20 |= c`, `c = 0` exactly when they decode, given that
`recoverX` is `recoverRef` (`RecoverOk`), and then the slots hold the point.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep Keeps off word limbs Outside Outside2 ofs workRegs FieldMem)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv cswapE opSwap IKeep)
open VG.Proof.Curve448.AArch64 (mask)
open VG.Impl.X448.AArch64 (ld st slot X2 ACC)

/-- What decoding writes: the slots and `CAN`, and the coefficients. -/
abbrev DFrame (base : Addr) (m m' : Mem) : Prop := Outside2 base 64 2944 ACC 512 m m'

theorem cframe_dframe {base : Addr} {m m' : Mem} (h : CFrame base m m') : DFrame base m m' :=
  fun x h1 h2 => h x (by simp only [X2, slot] at *; omega) (by simp only [CAN] at *; omega) h2

theorem keep_dframe {base : Addr} {s t : State} (h : Keep base s t) : DFrame base s.mem t.mem :=
  h.mem.mono (by decide) (Nat.le_refl _)

theorem ikeep_dframe {base : Addr} {s t : State} (h : IKeep base s t) : DFrame base s.mem t.mem :=
  h.mem.mono (by decide) (Nat.le_refl _)

theorem bytesAt57_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).take 56 = Spec.Ed448.bytesAt m p 56 := by
  simp only [Spec.Ed448.bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  rw [List.take_left' (by simp)]

theorem bytesAt57_getD (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).getD 56 0 = m (p + BitVec.ofNat 64 56) := by
  simp [Spec.Ed448.bytesAt, List.getD_eq_getElem?_getD]

theorem bytesAt57_len (m : Mem) (p : Addr) : (Spec.Ed448.bytesAt m p 57).length = 57 := by
  simp [Spec.Ed448.bytesAt]

theorem fopValid_decode (xo yo : Fin 22) (hxy : (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9)) :
    (∀ op ∈ decodeUV yo.val xo.val, fopValid op) ∧
      (∀ op ∈ ([.mul xo.val xo.val 21, .sqr 12 xo.val, .mul 12 3 12] : List FOp), fopValid op) ∧
      (∀ op ∈ ([.sub 12 xo.val xo.val, .sub 12 12 xo.val] : List FOp), fopValid op) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem decode_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {rp : Reg} {p : Addr} (hp : s.gpr rp = p) (hrp : rp = .x0 ∨ rp = .x1) (xo yo : Fin 22)
    (hxy : (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9))
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa (decode rp xo.val yo.val) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57)).isSome) ∧
        t.gpr .x20 = s.gpr .x20 ||| c) ∧
      (∀ pt, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57) = some pt →
        E t.mem base xo = pt.X ∧ E t.mem base yo = pt.Y ∧ pt.Z = 1) ∧
      (∀ i : Fin 22, i.val < 12 → i ≠ 1 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ xo → i ≠ yo →
        E t.mem base i = E s.mem base i) ∧
      BoundedEnv t.mem base ∧ Keeps (.x17 :: .x19 :: .x20 :: workRegs) s t ∧ DFrame base s.mem t.mem := by
  obtain ⟨v1, v2, v3⟩ := fopValid_decode xo yo hxy
  have hxo1 : xo ≠ 1 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hxo12 : xo ≠ 12 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hyx : yo ≠ xo := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hxlt : xo.val < 14 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hylt : yo.val < 14 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hxo : xo = 6 ∨ xo = 8 := by rcases hxy with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  rw [decode]
  -- `y`, its checks and the sign bit.
  refine WP.seq (WP.mono (decodeY_ok hs hb hp hrp yo hr hfar)
    fun s1 ⟨y1, sg1, ⟨c1, hc1, b1⟩, e1, bd1, k1, o1⟩ => ?_)
  have hs1 : Scr s1 base := hs.of_keeps k1 (by decide)
  -- `u`, `v`, `u³v` and `u⁵v³`.
  refine WP.seq (WP.mono (field_ok _ v1 hs1 bd1) fun s2 ⟨k2, bd2, e2⟩ => ?_)
  have hs2 := k2.scr hs1
  -- The root.
  refine WP.seq (WP.mono (root_spec base s2 hs2 bd2) fun s3 ⟨k3, bd3, e3⟩ => ?_)
  have hs3 := k3.scr hs2
  -- `x` and `v x²`.
  refine WP.seq (WP.mono (field_ok _ v2 hs3 bd3) fun s4 ⟨k4, bd4, e4⟩ => ?_)
  have hs4 := k4.scr hs3
  -- The checks, and the mask of the sign.
  simp only [List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (eqSlots_ok hs4 bd4 12 13 (by decide) (by decide)) fun s5 ⟨⟨c2, hc2, b5⟩, k5, bd5⟩ => ?_
  have hs5 := k5.scr hs4
  have sb17 : s5.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [k5.regs.1 _ (by decide), k4.regs.1 _ (by decide), k3.regs.1 _ (by decide), k2.regs.1 _ (by decide)]
    exact sg1
  have hsb : (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 < 2 := by
    have := (s.mem (p + BitVec.ofNat 64 56)).isLt; omega
  rw [WP.block_append_iff]
  refine WP.mono (zeroSign_ok hs5 bd5 xo hxo1 hsb sb17) fun s6 ⟨⟨c3, hc3, b6⟩, lo6, k6, bd6⟩ => ?_
  have hs6 := k6.scr hs5
  have sb17' : s6.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [k6.regs.1 _ (by decide)]; exact sb17
  refine WP.mono (negMask_ok hs6 hsb sb17') fun s7 ⟨m7, mm7, k7⟩ => ?_
  have hs7 : Scr s7 base := hs6.of_keeps k7 (by decide)
  have bd7 : BoundedEnv s7.mem base := mm7 ▸ bd6
  -- `-x`.
  refine WP.seq (WP.mono (field_ok _ v3 hs7 bd7) fun s8 ⟨k8, bd8, e8⟩ => ?_)
  have hs8 := k8.scr hs7
  have m8 : s8.gpr .x17 = s7.gpr .x17 := k8.regs.1 _ (by decide)
  -- The swap.
  rw [negSwap, WP.block_append_iff]
  refine WP.mono (mov6_ok s8) fun s9 ⟨x6, mm9, k9⟩ => ?_
  have hs9 : Scr s9 base := hs8.of_keeps k9 (by decide)
  have bd9 : BoundedEnv s9.mem base := mm9 ▸ bd8
  refine WP.mono (cswapE hs9 bd9 xo 12 hxo12 (sw := decide (VG.Proof.X448.AArch64.limbs s6.mem base X2 0 % 2 ^^^
    (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)) (by rw [x6, m8, m7]; rfl)) fun t ⟨kt, bdt, _, et⟩ => ?_
  -- The values.
  have e1' : ∀ i : Fin 22, i ≠ yo → E s1.mem base i = E s.mem base i := e1
  have h10' : E s1.mem base 10 = 1 := by
    rw [e1' 10 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h10]
  have h11' : E s1.mem base 11 = Spec.Ed448.d := by
    rw [e1' 11 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h11]
  obtain ⟨u2, vv2, t2, w2, k2'⟩ := decodeUV_eval xo yo hxy (E s1.mem base)
  simp only [h10', h11', y1] at u2 vv2 t2 w2
  simp only [← e2] at u2 vv2 t2 w2 k2'
  generalize hY : VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) = Y at *
  have r21 : E s3.mem base 21 = rootPow (E s2.mem base 12) := by rw [e3, rootEnv_eval]
  have r3k : ∀ i : Fin 22, i.val < 14 → E s3.mem base i = E s2.mem base i := fun i hi => by
    rw [e3, rootEnv_keep _ _ hi]
  obtain ⟨x4, x12, x13, k4'⟩ := decodeXOps_eval xo hxo (E s3.mem base)
  rw [← e4] at x4 x12 x13 k4'
  rw [r3k xo hxlt, t2, r21, w2] at x4 x12
  rw [r3k 3 (by decide), vv2] at x12
  rw [x13, r3k 13 (by decide), u2] at hc2
  rw [x12] at hc2
  generalize hu : Y * Y - 1 = u at *
  generalize hv : Spec.Ed448.d * (Y * Y) - 1 = v at *
  generalize ht : u * u * u * v = tt at *
  generalize hx : tt * rootPow (tt * ((u * v) * (u * v))) = x at *
  -- `x` at `s5` and `s6`.
  have x5 : E s5.mem base xo = x := by rw [k5.mem.E hxo1, x4]
  rw [x5] at hc3 lo6
  have hD := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem p 57) (bytesAt57_len _ _)
    (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) ((s.mem (p + BitVec.ofNat 64 56)).toNat)
    (by rw [bytesAt57_take]) (by rw [bytesAt57_getD]) Y u v tt x hY hu hv ht hx
  have s7x : E s7.mem base = E s6.mem base := by rw [mm7]
  have s9x : E s9.mem base = E s8.mem base := by rw [mm9]
  obtain ⟨n12, n8⟩ := subNeg_eval xo hxo12 (E s7.mem base)
  rw [← e8] at n12 n8
  have x7 : E s7.mem base xo = x := by rw [s7x, k6.mem.E hxo1, x5]
  -- The final `x`.
  have xt : E t.mem base xo =
      if (x.val % 2 == 1) == ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128 == 1) then x else (x - x) - x := by
    rw [et, opSwap, Function.update_of_ne hxo12, Function.update_self, s9x, n12, n8 xo hxo12, x7]
    have hlo : VG.Proof.X448.AArch64.limbs s6.mem base X2 0 % 2 = x.val % 2 := lo6
    rw [hlo]
    have hx2 : x.val % 2 < 2 := Nat.mod_lt _ (by decide)
    generalize x.val % 2 = a at hx2 ⊢
    generalize (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = sb at hsb ⊢
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
      rfl
  -- What the rest keeps.
  have keepE : ∀ i : Fin 22, i ≠ 1 → i ≠ xo → i ≠ 12 → E t.mem base i = E s4.mem base i := by
    intro i h1 hx h12
    rw [et, opSwap, Function.update_of_ne h12, Function.update_of_ne hx, s9x, n8 i h12, s7x, k6.mem.E h1,
      k5.mem.E h1]
  have kY : E t.mem base yo = Y := by
    have hy1 : yo ≠ 1 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    have hy12 : yo ≠ 12 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    rw [keepE yo hy1 hyx hy12, k4' yo hyx hy12, r3k yo hylt,
      k2' yo (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hyx, y1]
  refine ⟨⟨c1 ||| c2 ||| c3, ?_, ?_⟩, fun pt hpt => ?_, fun i hi h1 h3 h4 h5 hix hiy => ?_, bdt, ?_, ?_⟩
  · rw [or_eq_zero64, or_eq_zero64, hc1, hc2, hc3, hD]
    by_cases hall : ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall]
      exact ⟨fun _ => rfl, fun _ => ⟨⟨hall.1, hall.2.1⟩, hall.2.2⟩⟩
    · rw [ite_eq_right hall]
      exact ⟨fun h => absurd ⟨h.1.1, h.1.2, h.2⟩ hall, fun h => absurd h (by simp)⟩
  · rw [kt.regs.1 _ (by decide), k9.1 _ (by decide), k8.regs.1 _ (by decide), k7.1 _ (by decide), b6, b5,
      k4.regs.1 _ (by decide), k3.regs.1 _ (by decide), k2.regs.1 _ (by decide), b1]
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
  · have hi14 : i.val < 14 := by omega
    have h12 : i ≠ 12 := fun h => by rw [h] at hi; exact absurd hi (by decide)
    have h13 : i ≠ 13 := fun h => by rw [h] at hi; exact absurd hi (by decide)
    rw [keepE i h1 hix h12, k4' i hix h12, r3k i hi14, k2' i h3 h4 h5 h12 h13 hix, e1' i hiy]
  · refine ((((((((k1.mono (by decide)).trans (k2.regs.mono (by decide))).trans (k3.regs.mono (by decide))).trans
      (k4.regs.mono (by decide))).trans (k5.regs.mono (by decide))).trans (k6.regs.mono (by decide))).trans
      (k7.mono (by decide))).trans (k8.regs.mono (by decide))).trans ((k9.mono (by decide)).trans
      (kt.regs.mono (by decide)))
  · have d1 : DFrame base s.mem s1.mem := fun x h1 _ =>
      o1 x (by have := yo.isLt; simp only [slot] at *; omega)
    have d7 : DFrame base s6.mem s7.mem := by rw [mm7]; exact Outside2.refl _ _ _ _ _ _
    have d9 : DFrame base s8.mem s9.mem := by rw [mm9]; exact Outside2.refl _ _ _ _ _ _
    exact ((((((((d1.trans (keep_dframe k2)).trans (ikeep_dframe k3)).trans (keep_dframe k4)).trans
      (cframe_dframe k5.mem)).trans (cframe_dframe k6.mem)).trans d7).trans (keep_dframe k8)).trans d9).trans
      (keep_dframe kt)

end VG.Proof.Ed448.AArch64
