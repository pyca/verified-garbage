import VerifiedGarbage.Proof.Ed448.Arm.VerifySign
import VerifiedGarbage.Proof.Ed448.Arm.VerifyRoot
import VerifiedGarbage.Proof.Ed448.Recover

/-!
# Ed448 verification's equation on ARMv7: decoding a point

`decode_ok`: `decode p xo yo` on the 57 bytes at `q` (RFC 8032 §5.2.3):
`BAD |= 0` exactly when they decode, and then the point is `(x : y : 1)` with
`x` in slot `xo` and `y` in slot `yo` (by `Proof.Ed448.decodePoint_impl`,
given `RecoverOk`). The steps' field values: `u = y² - 1`, `v = d y² - 1`,
`t = u³v`, `x = t (t (uv)²)^((p-3)/4)`, the check `v x² = u`, and the sign.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot X2 ACC)
open VG.Proof.Ed448 (RecoverOk rootPow)

/-! ## The field steps -/

theorem decodeUV_eval (e : Env) (xo yo : Index) (h : xo = 6 ∧ yo = 7 ∨ xo = 8 ∧ yo = 9) :
    applyOps (decodeUVF yo xo) e 13 = e yo * e yo - e 10 ∧
    applyOps (decodeUVF yo xo) e 3 = e 11 * (e yo * e yo) - e 10 ∧
    applyOps (decodeUVF yo xo) e xo = (e yo * e yo - e 10) * (e yo * e yo - e 10) *
      (e yo * e yo - e 10) * (e 11 * (e yo * e yo) - e 10) ∧
    applyOps (decodeUVF yo xo) e 12 = (e yo * e yo - e 10) * (e yo * e yo - e 10) *
      (e yo * e yo - e 10) * (e 11 * (e yo * e yo) - e 10) *
      (((e yo * e yo - e 10) * (e 11 * (e yo * e yo) - e 10)) *
        ((e yo * e yo - e 10) * (e 11 * (e yo * e yo) - e 10))) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem decodeUV_keep (e : Env) (xo yo : Index) (h : xo = 6 ∧ yo = 7 ∨ xo = 8 ∧ yo = 9) (i : Index)
    (hi : i ≠ 3 ∧ i ≠ 4 ∧ i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 13 ∧ i ≠ xo) :
    applyOps (decodeUVF yo xo) e i = e i := by
  refine applyOps_keep _ _ ?_
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert i <;> decide

theorem decodeX_eval (e : Env) (xo : Index) (h : xo = 6 ∨ xo = 8) :
    applyOps (decodeXF xo) e xo = e xo * e 1 ∧
    applyOps (decodeXF xo) e 12 = e 3 * ((e xo * e 1) * (e xo * e 1)) := by
  rcases h with rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem decodeX_keep (e : Env) (xo : Index) (h : xo = 6 ∨ xo = 8) (i : Index) (hi : i ≠ 12 ∧ i ≠ xo) :
    applyOps (decodeXF xo) e i = e i := by
  refine applyOps_keep _ _ ?_
  rcases h with rfl | rfl <;> revert i <;> decide

theorem negX_eval (e : Env) (xo : Index) (h : xo = 6 ∨ xo = 8) :
    applyOps (negXF xo) e 12 = (e xo - e xo) - e xo := by
  rcases h with rfl | rfl <;> rfl

theorem negX_keep (e : Env) (xo : Index) (h : xo = 6 ∨ xo = 8) (i : Index) (hi : i ≠ 12) :
    applyOps (negXF xo) e i = e i := by
  refine applyOps_keep _ _ ?_
  rcases h with rfl | rfl <;> revert i <;> decide

/-! ## The bytes -/

theorem bytesAt57_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).take 56 = Spec.Ed448.bytesAt m p 56 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem bytesAt57_getD (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).getD 56 0 = m (p + BitVec.ofNat 64 56) := by
  simp [Spec.Ed448.bytesAt, List.getD_eq_getElem?_getD]

theorem bytesAt57_len (m : Mem) (p : Addr) : (Spec.Ed448.bytesAt m p 57).length = 57 := by
  simp [Spec.Ed448.bytesAt]

theorem decodeLE_56 (m : Mem) (p : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 56) = valN (decoded m p) 28 := by
  rw [Proof.Ed448.decodeLE_eq, show (56 : Nat) = 2 * 28 from rfl]
  exact decoded_val m p 28

/-! ## Decoding -/

theorem decode_ok (hR : RecoverOk) {s : State} {base q : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {p : Reg} (hp : p = .r8 ∨ p = .r10) (hq : State.addr (s.gpr p) = q) (hfit : (s.gpr p).toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (q + BitVec.ofNat 64 j))
    (xo yo : Index) (hxy : xo = 6 ∧ yo = 7 ∨ xo = 8 ∧ yo = 9)
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (decode p xo.val yo.val) s fun t =>
      VKeep base s t ∧ BoundedEnv t.mem base ∧
      BadUpd ((Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem q 57)).isSome) (s.gpr .r12) (t.gpr .r12) ∧
      (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem q 57) = some a →
        E t.mem base xo = a.X ∧ E t.mem base yo = a.Y ∧ a.Z = 1) ∧
      (∀ i : Index, i ≠ xo → i ≠ yo → (i.val = 0 ∨ i.val = 2 ∨ (6 ≤ i.val ∧ i.val ≤ 11) ∨ i.val = 21) →
        E t.mem base i = E s.mem base i) := by
  have hxo : xo = 6 ∨ xo = 8 := by rcases hxy with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hyx : yo ≠ xo := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hy1 : yo ≠ 1 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hx1 : xo ≠ 1 := by rcases hxo with rfl | rfl <;> decide
  unfold decode
  -- `y`, the sign bit, and the first checks
  refine WP.seq (WP.mono (decodeY_ok hs hb hp hq hfit hr hd yo hy1)
    fun s1 ⟨k1, b1, sg1, c1, y1, e1⟩ => ?_)
  have hs1 := k1.scr hs
  -- `u`, `v`, `t` and `t (uv)²`
  rw [← decodeUVF_impl]
  refine WP.seq (WP.mono (ops_ok hs1 b1 (decodeUVF yo xo)) fun s2 ⟨k2, b2, e2⟩ => ?_)
  have hs2 := k2.scr hs1
  -- the root
  refine WP.seq (WP.mono (root_ok hs2 b2) fun s3 ⟨k3, b3, e3⟩ => ?_)
  have hs3 := k3.scr hs2
  -- `x` and `v x²`
  rw [← decodeXF_impl]
  refine WP.seq (WP.mono (ops_ok hs3 b3 (decodeXF xo)) fun s4 ⟨k4, b4, e4⟩ => ?_)
  have hs4 := k4.scr hs3
  -- `v x² = u`
  refine WP.seq (WP.mono (eqSlots_ok hs4 b4 12 13 (by decide) (by decide) (by decide))
    fun s5 ⟨k5, b5, e5, c5⟩ => ?_)
  have hs5 := k5.scr hs4
  -- `-x`
  rw [← negXF_impl]
  refine WP.seq (WP.mono (ops_ok hs5 b5 (negXF xo)) fun s6 ⟨k6, b6, e6⟩ => ?_)
  have hs6 := k6.scr hs5
  -- the sign
  have hb128 : (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 < 2 := by
    have := (s.mem (q + BitVec.ofNat 64 56)).isLt; omega
  have K16 : CKeep base s1 s6 :=
    (Keep.toC k2).trans ((IKeep.toC k3).trans ((Keep.toC k4).trans (k5.trans (Keep.toC k6))))
  have sg : word s6.mem base SIGN = BitVec.ofNat 32 ((s.mem (q + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [K16.mem.word (Or.inl (by simp only [SIGN]; omega)) (Or.inl (by simp only [SIGN, ACC]; omega))
      (by decide), sg1]
  -- the values
  have h10' : E s1.mem base 10 = 1 := by
    rw [e1 10 (by decide) (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h10]
  have h11' : E s1.mem base 11 = Spec.Ed448.d := by
    rw [e1 11 (by decide) (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h11]
  obtain ⟨u2, v2, t2, w2⟩ := decodeUV_eval (E s1.mem base) xo yo hxy
  simp only [h10', h11', y1, ← e2] at u2 v2 t2 w2
  generalize hY : Proof.X448.toFe (valN (decoded s.mem q) 28) = Y at *
  generalize hu : Y * Y - 1 = u at *
  generalize hv : Spec.Ed448.d * (Y * Y) - 1 = v at *
  generalize ht : u * u * u * v = tt at *
  have r31 : E s3.mem base 1 = rootPow (E s2.mem base 12) := by rw [e3, rootEnv_eval]
  have r3k : ∀ i : Index, i ≠ 1 → (i.val < 14 ∨ 20 < i.val) → E s3.mem base i = E s2.mem base i :=
    fun i h1 h2 => by rw [e3, rootEnv_keep _ _ ⟨h1, h2⟩]
  have hxlt : xo.val < 14 := by rcases hxo with rfl | rfl <;> decide
  obtain ⟨x4, w4⟩ := decodeX_eval (E s3.mem base) xo hxo
  rw [← e4, r3k xo hx1 (Or.inl hxlt), t2, r31, w2] at x4
  rw [← e4, r3k xo hx1 (Or.inl hxlt), t2, r31, w2, r3k 3 (by decide) (Or.inl (by decide)), v2] at w4
  generalize hx : tt * rootPow (tt * ((u * v) * (u * v))) = x at *
  have x5 : E s5.mem base xo = x := by rw [e5 xo hx1, x4]
  have w5 : E s5.mem base 12 = v * (x * x) := by rw [e5 12 (by decide), w4]
  have u4 : E s4.mem base 13 = u := by
    rw [e4, decodeX_keep _ xo hxo 13 ⟨by decide, by rcases hxo with rfl | rfl <;> decide⟩,
      r3k 13 (by decide) (Or.inl (by decide)), u2]
  have n6 : E s6.mem base 12 = (E s6.mem base xo - E s6.mem base xo) - E s6.mem base xo := by
    rw [e6, negX_eval _ xo hxo, negX_keep _ xo hxo xo (by rcases hxo with rfl | rfl <;> decide)]
  refine WP.mono (decodeSign_ok hs6 b6 xo hxo hb128 sg n6) fun t ⟨kt, bt, ct, xt, et⟩ => ?_
  have x6 : E s6.mem base xo = x := by
    rw [e6, negX_keep _ xo hxo xo (by rcases hxo with rfl | rfl <;> decide), x5]
  rw [x6] at ct xt
  rw [w4, u4] at c5
  -- `decodePoint`
  have hD := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem q 57) (bytesAt57_len _ _)
    (valN (decoded s.mem q) 28) ((s.mem (q + BitVec.ofNat 64 56)).toNat)
    (by rw [bytesAt57_take, decodeLE_56]) (by rw [bytesAt57_getD]) Y u v tt x hY hu hv ht hx
  -- what is kept
  have r12 : ∀ {a b : State}, Keep base a b → b.gpr .r12 = a.gpr .r12 := fun h => h.regs.1 _ (by decide)
  have r12i : s3.gpr .r12 = s2.gpr .r12 := k3.regs.1 _ (by decide)
  have kY : E t.mem base yo = Y := by
    rw [et yo hy1 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide) hyx,
      e6, negX_keep _ xo hxo yo (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), e5 yo hy1, e4,
      decodeX_keep _ xo hxo yo ⟨by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide, hyx⟩,
      r3k yo hy1 (Or.inl (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide)), e2,
      decodeUV_keep _ xo yo hxy yo (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide), y1]
  refine ⟨k1.trans ((Keep.toV k2).trans ((IKeep.toV k3).trans ((Keep.toV k4).trans
    ((CKeep.toV k5).trans ((Keep.toV k6).trans (CKeep.toV kt)))))), bt, ?_, fun a ha => ?_,
    fun i hix hiy hi => ?_⟩
  · have c5' : BadUpd (v * (x * x) = u) (s1.gpr .r12) (s5.gpr .r12) := by
      rw [← r12 k2, ← r12i, ← r12 k4]; exact c5
    have ct' : BadUpd (¬(x = 0 ∧ (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 = 1)) (s5.gpr .r12)
        (t.gpr .r12) := by
      rw [← r12 k6]; exact ct
    refine ((c1.trans c5').trans ct').congr ?_
    rw [hD]
    by_cases hall : ((s.mem (q + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        valN (decoded s.mem q) 28 < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall]
      exact ⟨fun _ => rfl, fun _ => ⟨⟨hall.1, hall.2.1⟩, hall.2.2⟩⟩
    · rw [ite_eq_right hall]
      exact ⟨fun h => absurd ⟨h.1.1, h.1.2, h.2⟩ hall, fun h => absurd h (by simp)⟩
  · rw [hD] at ha
    by_cases hall : ((s.mem (q + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        valN (decoded s.mem q) 28 < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall] at ha
      cases ha
      exact ⟨xt, kY, rfl⟩
    · rw [ite_eq_right hall] at ha
      cases ha
  · have h1 : i ≠ 1 := fun h => by subst h; omega
    have h12 : i ≠ 12 := fun h => by subst h; omega
    rw [et i h1 h12 hix, e6, negX_keep _ xo hxo i h12, e5 i h1, e4, decodeX_keep _ xo hxo i ⟨h12, hix⟩,
      r3k i h1 (by omega), e2, decodeUV_keep _ xo yo hxy i ⟨fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega, h12, fun h => by subst h; omega, hix⟩,
      e1 i h1 hiy]

end VG.Proof.Ed448.Arm
