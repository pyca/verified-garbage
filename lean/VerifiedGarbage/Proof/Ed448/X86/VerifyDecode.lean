import VerifiedGarbage.Proof.Ed448.X86.VerifySign
import VerifiedGarbage.Proof.Ed448.X86.VerifyRoot
import VerifiedGarbage.Proof.Ed448.Recover

/-!
# Ed448 verification's equation on x86 (32-bit): decoding a point

`decode_ok`: `decode d xo yo` on the 57 bytes at `q`, the argument at
`[esp + d]` (RFC 8032 §5.2.3): `BAD |= 0` exactly when they decode, and then
the point is `(x : y : 1)` with `x` in slot `xo` and `y` in slot `yo` (by
`Proof.Ed448.decodePoint_impl`, given `RecoverOk`). The steps' field values
(`Proof/Ed448/VerifyFormulas.lean`): `u = y² - 1`, `v = d y² - 1`, `t = u³v`,
`x = t (t (uv)²)^((p-3)/4)`, the check `v x² = u`, and the sign.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.X448.X86 (slot X2 ACC at_)
open VG.Proof.Ed448 (RecoverOk rootPow evalOps fopValid)

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

theorem decode_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {d : Nat} {a : Addr} (ha : s.ea (at_ .esp d) = a) (har : InRegions (s.rd ++ s.wr) a 4)
    {p : BitVec 32} (hp : s.mem.readW a 32 = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (p.setWidth 64 + BitVec.ofNat 64 j))
    (xo yo : Index) (hxy : xo = 6 ∧ yo = 7 ∨ xo = 8 ∧ yo = 9)
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (decode d xo.val yo.val) s fun t =>
      VKeep base s t ∧ BoundedEnv t.mem base ∧
      BadUpd ((Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (p.setWidth 64) 57)).isSome)
        (word s.mem base BAD) (word t.mem base BAD) ∧
      (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (p.setWidth 64) 57) = some a →
        E t.mem base xo = a.X ∧ E t.mem base yo = a.Y ∧ a.Z = 1) ∧
      (∀ i : Index, i ≠ xo → i ≠ yo → (i.val = 0 ∨ i.val = 2 ∨ (6 ≤ i.val ∧ i.val ≤ 11)) →
        E t.mem base i = E s.mem base i) := by
  have hxo : xo = 6 ∨ xo = 8 := by rcases hxy with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hyx : yo ≠ xo := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hy1 : yo ≠ 1 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hx1 : xo ≠ 1 := by rcases hxo with rfl | rfl <;> decide
  have hx12 : xo ≠ 12 := by rcases hxo with rfl | rfl <;> decide
  have hxlt : xo.val < 14 := by rcases hxo with rfl | rfl <;> decide
  have hylt : yo.val < 14 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  generalize hq : p.setWidth 64 = q
  unfold decode
  -- `y`, the sign bit, and the first checks
  refine WP.seq (WP.mono (decodeY_ok hs hb ha har hp hfit hr hd yo hy1)
    fun s1 ⟨k1, b1, sg1, c1, y1, e1⟩ => ?_)
  rw [hq] at sg1 c1 y1
  have hs1 := k1.scr hs
  -- `u`, `v`, `t` and `t (uv)²`
  refine field_seq (decodeUV yo.val xo.val)
    (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hs1 b1 fun s2 k2 b2 e2 => ?_
  have hs2 := k2.scr hs1
  -- the root
  refine WP.seq (WP.mono (root_ok hs2 b2) fun s3 ⟨k3, b3, e3⟩ => ?_)
  have hs3 := k3.scr hs2
  -- `x` and `v x²`
  refine field_seq [.mul xo.val xo.val 21, .sqr 12 xo.val, .mul 12 3 12]
    (by rcases hxo with rfl | rfl <;> decide) hs3 b3 fun s4 k4 b4 e4 => ?_
  have hs4 := k4.scr hs3
  -- `v x² = u`
  refine WP.seq (WP.mono (eqSlots_ok hs4 b4 12 13 (by decide) (by decide) (by decide))
    fun s5 ⟨k5, b5, e5, c5⟩ => ?_)
  have hs5 := k5.scr hs4
  -- `-x`
  refine field_seq [.sub 12 xo.val xo.val, .sub 12 12 xo.val]
    (by rcases hxo with rfl | rfl <;> decide) hs5 b5 fun s6 k6 b6 e6 => ?_
  have hs6 := k6.scr hs5
  -- the sign
  have hb128 : (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 < 2 := by
    have := (s.mem (q + BitVec.ofNat 64 56)).isLt; omega
  have K16 : CKeep base s1 s6 :=
    (Keep.toC k2).trans ((IKeep.toC k3).trans ((Keep.toC k4).trans (k5.trans (Keep.toC k6))))
  have sg : word s6.mem base SIGN = BitVec.ofNat 32 ((s.mem (q + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [K16.sign, sg1]
  -- the values
  have h10' : E s1.mem base 10 = 1 := by
    rw [e1 10 (by decide) (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h10]
  have h11' : E s1.mem base 11 = Spec.Ed448.d := by
    rw [e1 11 (by decide) (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h11]
  obtain ⟨u2, v2, t2, w2, k2e⟩ := Proof.Ed448.decodeUV_eval xo yo hxy (E s1.mem base)
  simp only [h10', h11', y1, ← e2] at u2 v2 t2 w2 k2e
  generalize hY : Proof.X448.toFe (valN (decoded s.mem q) 28) = Y at *
  generalize hu : Y * Y - 1 = u at *
  generalize hv : Spec.Ed448.d * (Y * Y) - 1 = v at *
  generalize ht : u * u * u * v = tt at *
  have r321 : E s3.mem base 21 = rootPow (E s2.mem base 12) := by rw [e3, rootEnv_eval]
  have r3k : ∀ i : Index, i.val < 14 → E s3.mem base i = E s2.mem base i :=
    fun i h => by rw [e3, rootEnv_keep _ _ h]
  obtain ⟨x4, w4, u4, k4e⟩ := Proof.Ed448.decodeXOps_eval xo hxo (E s3.mem base)
  rw [← e4] at k4e
  rw [← e4, r3k xo hxlt, t2, r321, w2] at x4
  rw [← e4, r3k 3 (by decide), v2, r3k xo hxlt, t2, r321, w2] at w4
  rw [← e4, r3k 13 (by decide), u2] at u4
  generalize hx : tt * rootPow (tt * ((u * v) * (u * v))) = x at *
  have x5 : E s5.mem base xo = x := by rw [e5 xo hx1, x4]
  obtain ⟨n6, k6e⟩ := Proof.Ed448.subNeg_eval xo hx12 (E s5.mem base)
  rw [← e6] at n6 k6e
  have x6 : E s6.mem base xo = x := by rw [k6e xo hx12, x5]
  rw [x5] at n6
  refine WP.mono (decodeSign_ok hs6 b6 xo hxo hb128 sg (by rw [x6]; exact n6))
    fun t ⟨kt, bt, ct, xt, et⟩ => ?_
  rw [x6] at ct xt
  rw [w4, u4] at c5
  -- `decodePoint`
  have hD := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem q 57) (bytesAt57_len _ _)
    (valN (decoded s.mem q) 28) ((s.mem (q + BitVec.ofNat 64 56)).toNat)
    (by rw [bytesAt57_take, decodeLE_56]) (by rw [bytesAt57_getD]) Y u v tt x hY hu hv ht hx
  have kY : E t.mem base yo = Y := by
    rw [et yo hy1 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide) hyx,
      k6e yo (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), e5 yo hy1, k4e yo hyx
      (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), r3k yo hylt,
      k2e yo (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hyx, y1]
  refine ⟨k1.trans ((Keep.toV k2).trans ((IKeep.toV k3).trans ((Keep.toV k4).trans
    ((CKeep.toV k5).trans ((Keep.toV k6).trans (CKeep.toV kt)))))), bt, ?_, fun a ha => ?_,
    fun i hix hiy hi => ?_⟩
  · have c5' : BadUpd (v * (x * x) = u) (word s1.mem base BAD) (word s5.mem base BAD) := by
      rw [← Keep.bad k2, ← IKeep.bad k3, ← Keep.bad k4]; exact c5
    have ct' : BadUpd (¬(x = 0 ∧ (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 = 1)) (word s5.mem base BAD)
        (word t.mem base BAD) := by
      rw [← Keep.bad k6]; exact ct
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
    have h3 : i ≠ 3 := fun h => by subst h; omega
    have h4 : i ≠ 4 := fun h => by subst h; omega
    have h5 : i ≠ 5 := fun h => by subst h; omega
    have h13 : i ≠ 13 := fun h => by subst h; omega
    rw [et i h1 h12 hix, k6e i h12, e5 i h1, k4e i hix h12, r3k i (by omega),
      k2e i h3 h4 h5 h12 h13 hix, e1 i h1 hiy]

end VG.Proof.Ed448.X86
