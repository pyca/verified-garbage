module

import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ

/-!
# DSA verification on PPC64LE: `u1` and `u2`

`products_ok`: in the Q space, with q in array 0, `R² mod q` in array 8 and
`w` in array 4: the digest's scalar `z` (its first `min(d, qb)` octets, from
`r2`) and r,
then `u1 = z w mod q` and `u2 = r w mod q` (Montgomery multiplications by w,
then by `R²`) to the buffer's first and second `q_len` octets.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot slot_sep)

/-- The registers `scalar` writes. -/
def prodScalarRegs : List Reg := [.r0, .r3, .r6, .r12] ++ loadRegs

theorem pack_getQb {pl ql qb d : Nat} (h1 : pl < 2 ^ 16) (h2 : ql < 2 ^ 16) (h3 : qb < 2 ^ 16)
    (h4 : d < 2 ^ 16) : pack pl ql qb d <<< 16 >>> 48 = BitVec.ofNat 64 qb := by
  rw [shl_shr_ofNat _ 16 (by decide)]
  congr 1
  have e := pack_qb h1 h2 h3 h4
  simp only [Nat.reduceSub, Nat.reducePow] at *
  omega

/-- The borrow of `a − b`, for `a` and `b` below `2^63`. -/
theorem sub_shr63 {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = BitVec.ofNat 64 (if a < b then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow] at *
  split <;> omega

/-- `scalarLen`: `r6 := min(d, qb)`, from `r2`'s fields. -/
theorem scalarLen_ok {s : State} {pl ql qb d : Nat} (h2 : s.gpr .r2 = pack pl ql qb d) (h1 : pl < 2 ^ 16)
    (hq : ql < 2 ^ 16) (h3 : qb < 2 ^ 16) (h4 : d < 2 ^ 16) :
    WP isa scalarLen s fun t =>
      (t.gpr .r6 = BitVec.ofNat 64 (min d qb) ∧ t.mem = s.mem) ∧ Keep [.r0, .r3, .r6] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold scalarLen
  refine WP.seq (WP.mono (WP.keep [.r6, .r0, .r3] (Q := fun t => t.gpr .r6 = BitVec.ofNat 64 qb ∧
      t.gpr .r0 = BitVec.ofNat 64 d ∧ t.gpr .r3 = BitVec.ofNat 64 (if qb < d then 1 else 0) ∧ t.mem = s.mem)
    (by
      unfold getQb getD
      prun [h2, pack_getQb h1 hq h3 h4, pack_d h1 hq h3 h4,
        sub_shr63 (a := qb) (b := d) (by omega) (by omega)]) (by decide)) fun t ⟨⟨a6, a0, a3, m⟩, _⟩ => ?_)
  refine WP.ite _ (eval_zero_ofNat _ _ (by split <;> decide) a3) (fun hz => ?_) (fun hz => ?_)
  · have hz : ¬ qb < d := by
      have := of_decide_eq_true hz; split at this <;> simp_all
    prun [a0, m, BitVec.or_self]
    rw [Nat.min_eq_left (by omega)]
  · have hz : qb < d := by
      have := of_decide_eq_false hz; split at this <;> simp_all
    exact wp_nil ⟨by rw [a6, Nat.min_eq_right (by omega)], m⟩

/-- `scalar`: the digest's first `min(d, qb)` octets into array 6. -/
theorem prod_scalar_ok {s : State} {L : Lay} {key sig dig : Addr} {qb d : Nat} (h : QS s L key sig dig)
    (hL : L.Ok) (h2 : s.gpr .r2 = pack L.pl L.ql qb d) (hqb : qb ≤ L.ql) (hd : d < 2 ^ 16)
    (hdg : Src s L dig (min d qb)) :
    WP isa scalar s fun t =>
      (QS t L key sig dig ∧ arrQ t.mem L 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) ∧
        Outside L.Q (slot 4 6) (8 * (4 + 2)) s.mem t.mem) ∧ Keep prodScalarRegs s t := by
  have hql := hL.ql
  have hpl : L.pl < 2 ^ 16 := by rcases hL.pl with e | e | e <;> omega
  unfold scalar
  refine WP.seq (WP.mono (scalarLen_ok h2 hpl (by omega) (by omega) hd) fun s₀ ⟨⟨a6, m0⟩, k0⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = dig ∧ u.mem = s₀.mem)
    (by prun [((k0.gpr .r26 (by decide)).trans h.regs.r26), BitVec.add_zero]) (by decide))
    fun s₁ ⟨⟨a12, m1⟩, k1'⟩ => ?_)
  have a6 : s₁.gpr .r6 = BitVec.ofNat 64 (min d qb) := (k1'.gpr .r6 (by decide)).trans a6
  have k1 := k0.trans k1'
  have m1 : s₁.mem = s.mem := m1.trans m0
  have hdl : min d qb ≤ L.ql := Nat.le_trans (Nat.min_le_right _ _) hqb
  generalize min d qb = dl at a6 hdg hdl ⊢
  have Q1 := h.step k1 (by decide)
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega) a6) (fun hz => ?_) (fun hz => ?_)
  · have hz : dl = 0 := of_decide_eq_true hz
    subst hz
    refine WP.mono (zeroArr_ok Q1.inq.env (j := 6) (by decide)) fun t ⟨⟨z6, ot⟩, kt⟩ => ?_
    have qa : QArr L s₁.mem t.mem := QArr.of ot (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
    refine ⟨⟨Q1.step kt (by decide), ?_, ?_⟩, (k1.trans kt).mono (by decide)⟩
    · rw [arrQ, z6]; rfl
    · rw [← m1]; exact ot.mono (Nat.le_refl _) (by omega)
  · have hz : dl ≠ 0 := of_decide_eq_false hz
    refine WP.mono (loadQ_ok (j := 6) Q1 hL (by decide) (by decide) (hdg.keep k1.rd k1.wr) a12 a6 (by omega)
      (by omega)) fun t ⟨⟨Qt, v6, _, ot, _⟩, kt⟩ => ?_
    rw [m1] at v6 ot
    exact ⟨⟨Qt, v6, ot.mono (Nat.le_refl _) (by omega)⟩, (k1.trans kt).mono (by decide)⟩

/-- `montOp o a b` for `o` among 5 and 6, `[b] < c`. -/
theorem prod_mont_ok {s : State} {B : Addr} {Z w : Nat} (h : MCtx s B Z w) {o a b : Nat}
    (ho : o = 5 ∨ o = 6) (ha : a < 8) (ha2 : a ≠ 2) (hb : b < 8) (hb2 : b ≠ 2)
    (hB : arr s.mem B w b < arr s.mem B w 0) :
    WP isa (PublicChecked.montOp o a b) s fun t =>
      (arr t.mem B w o < arr s.mem B w 0 ∧
        arr t.mem B w o * 2 ^ (64 * w) % arr s.mem B w 0 = arr s.mem B w a * arr s.mem B w b % arr s.mem B w 0 ∧
        Outs B (montRanges w o) s.mem t.mem ∧ w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0)) ∧
      Keep Pub.montRegs s t := by
  have hw := h.hw
  have hw' := h.hw'
  have h8 := slot_lt (w := w) (show 8 < 28 by decide)
  have hZ := h.hZ
  refine WP.mono (Pub.montOp_ok h.hs (by omega) ha hb (by omega) (by omega) ha2 hb2
    (by omega) (by omega) (by omega) h.h10 h.h29 h.h11 h.h12 h.inv hB) fun t ⟨⟨hlt, heq, hout⟩, k⟩ =>
    ⟨⟨hlt, heq, hout, ?_⟩, k⟩
  refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => hout _ fun r hr => ?_)
  have := h.hs.nowrap
  have h0 := slot_lt (w := w) (show 0 < 28 by decide)
  rw [ofs_off B (by omega)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> omega

/-- A Montgomery multiplication's frame in the Q space. -/
theorem prod_qarr {L : Lay} {m m' : Mem} {o : Nat} (h : Outs L.Q (montRanges 4 o) m m') (ho : o = 5 ∨ o = 6) :
    QArr L m m' :=
  outs_within h (by
    simp only [montRanges, List.mem_cons, List.not_mem_nil, or_false]
    intro r hr
    rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp only [slot_eq] <;> omega)

/-- Two Montgomery multiplications, by `y` and by `R² mod q`: `x y mod q`. -/
theorem prod_mont_back {q R A B X Y : Nat} (hR : Nat.Coprime R q) (hB : B < q) (hA : A * R % q = X * Y % q)
    (hB' : B * R % q = A * (R * R % q) % q) : B = X * Y % q := by
  have e : B * R % q = X * Y * R % q := by
    rw [hB', Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, hA,
      Nat.mod_mul_mod]
  have := VG.Proof.Bignum.mont_cancel hR e
  rw [Nat.mod_eq_of_lt hB] at this
  exact this

/-- The buffer from `q_len` on is past the Q space. -/
theorem prod_sepQ (L : Lay) {d n : Nat} (hd : 1600 ≤ d) (hn : d + n ≤ 2 ^ 64) :
    ∀ x, ofs (off L.Q d) x < n → 1600 ≤ ofs L.Q x := by
  intro x hx
  have hlt := (x - L.Q).isLt
  simp only [ofs, off] at hx ⊢
  rw [Offset.toNat_sub_add x L.Q (by omega)] at hx
  by_contra hc
  rw [Nat.mod_eq_of_lt (by omega)] at hx
  omega

/-- Octets below a frame's range keep their values. -/
theorem prod_bytes_keep {B : Addr} {o n k : Nat} {m m' : Mem} (h : Outside B o n m m') (hk : k ≤ o)
    (hk' : k < 2 ^ 64) : Spec.Rsa.bytesAt m' B k = Spec.Rsa.bytesAt m B k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inl ?_)
  have hi := List.mem_range.mp hi
  rw [show B + BitVec.ofNat 64 i = off B i from rfl, VG.Proof.Bignum.PPC64LE.ofs_off0 B (by omega)]
  omega

/-- The registers `products` writes. -/
def prodRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22]

/-- `products`: `u1 = z w mod q` and `u2 = r w mod q` to the buffer. -/
theorem products_ok {s : State} {L : Lay} {key sig dig : Addr} {qb d W : Nat} (h : QS s L key sig dig)
    (hL : L.Ok) (hsg : Src s L sig (2 * L.ql)) (h2 : s.gpr .r2 = pack L.pl L.ql qb d) (hqb : qb ≤ L.ql) (hd : d < 2 ^ 16)
    (hdg : Src s L dig (min d qb))
    (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1) (hql : arrQ s.mem L 0 < 2 ^ (8 * L.ql))
    (h8 : arrQ s.mem L 8 = 2 ^ (128 * 4) % arrQ s.mem L 0) (h4 : arrQ s.mem L 4 = W)
    (hW : W < arrQ s.mem L 0) :
    WP isa products s fun t =>
      (QS t L key sig dig ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.ql) =
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) * W % arrQ s.mem L 0 ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off L.Buf L.ql) L.ql) = rOf s.mem L sig * W % arrQ s.mem L 0 ∧
        QBuf L s.mem t.mem) ∧ Keep prodRegs s t := by
  have hq := hL.ql
  have hpl := hL.pl
  have hn : slot 4 28 ≤ 2 ^ 64 := by decide
  have hcop : Nat.Coprime (2 ^ (64 * 4)) (arrQ s.mem L 0) := VG.Proof.Bignum.coprime_pow2 hqo _
  have hRR := pow_sq_eq 4
  generalize (2 : Nat) ^ (128 * 4) = R2 at h8 hRR
  unfold products
  -- The digest's scalar into array 6, r into array 5, `R² mod q` into array 1.
  refine WP.seq (WP.mono (prod_scalar_ok h hL h2 hqb hd hdg) fun s₁ ⟨⟨Q1, v6, o1⟩, k1⟩ => ?_)
  have qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  refine WP.seq (WP.mono (ptrR_ok Q1.regs) fun s₂ ⟨⟨a12, a6, m2⟩, k2⟩ => ?_)
  have Q2 := Q1.step k2 (by decide)
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q2 hL (by decide) (by decide)
      ((hsg.keep k12.rd k12.wr).sub (o := 0) (k := L.ql) (by omega)) (by rw [a12, off, BitVec.add_zero]) a6
      (by omega) (by omega)) fun s₃ ⟨⟨Q3, v5, _, o3, qa3⟩, k3⟩ => ?_)
  rw [m2] at v5 o3 qa3
  refine WP.seq (WP.mono (copy_ok Q3.inq.env (o := 1) (a := 8) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨v1, o4⟩, k4⟩ => ?_)
  have qa4 : QArr L s₃.mem s₄.mem := QArr.of o4 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  have Q4 := Q3.step k4 (by decide)
  have qa14 : QArr L s.mem s₄.mem := (qa1.trans qa3).trans qa4
  have o3' : Outside L.Q (slot 4 5) (8 * (4 + 2)) s₁.mem s₃.mem := o3.mono (Nat.le_refl _) (by omega)
  have a0 : arr s₄.mem L.Q 4 0 = arrQ s.mem L 0 := qa14.arr0
  have a4 : arr s₄.mem L.Q 4 4 = W := by
    rw [Outside.arrEq o4 (by decide) (by decide) hn, Outside.arrEq o3' (by decide) (by decide) hn,
      Outside.arrEq o1 (by decide) (by decide) hn]
    exact h4
  have a1 : arr s₄.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := by
    rw [v1, Outside.arrEq o3' (by decide) (by decide) hn, Outside.arrEq o1 (by decide) (by decide) hn]
    exact h8
  have a6 : arr s₄.mem L.Q 4 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) := by
    rw [Outside.arrEq o4 (by decide) (by decide) hn, Outside.arrEq o3' (by decide) (by decide) hn]
    exact v6
  have a5 : arr s₄.mem L.Q 4 5 = rOf s.mem L sig := by
    rw [Outside.arrEq o4 (by decide) (by decide) hn]
    refine v5.trans ?_
    rw [(hsg.sub (o := 0) (k := L.ql) (by omega)).bytes (qa1.qbody.body hL) hL.z256]
    simp only [rOf, off, BitVec.add_zero]
  -- `-q⁻¹`.
  have hodd : (word s₄.mem L.Q (slot 4 0)).toNat % 2 = 1 :=
    word_odd _ _ _ (2 * 4) (by decide) (by show arr s₄.mem L.Q 4 0 % 2 = 1; rw [a0]; exact hqo)
  refine WP.seq (WP.mono (Pub.minv_ok Q4.inq.env.hs Q4.inq.env.h10 (by decide) hodd)
    fun s₅ ⟨⟨i12, inv, m5⟩, k5⟩ => ?_)
  have M5 : MCtx s₅ L.Q 1600 4 := ⟨Q4.inq.env.keep k5 (by decide), i12, by rw [m5]; exact inv⟩
  rw [← m5] at a0 a4 a1 a6 a5
  -- u1.
  refine WP.seq (WP.mono (prod_mont_ok M5 (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [a4, a0]; exact hW)) fun s₆ ⟨⟨_, e6, o6, w6⟩, k6⟩ => ?_)
  have M6 := M5.keep k6 (by decide) w6
  rw [a0, a6, a4] at e6
  have b0 : arr s₆.mem L.Q 4 0 = arrQ s.mem L 0 :=
    (Outs.arrEq_mont o6 (by decide) (by decide) (by decide) (by decide) hn).trans a0
  have b1 : arr s₆.mem L.Q 4 1 = R2 % arrQ s.mem L 0 :=
    (Outs.arrEq_mont o6 (by decide) (by decide) (by decide) (by decide) hn).trans a1
  have b4 : arr s₆.mem L.Q 4 4 = W :=
    (Outs.arrEq_mont o6 (by decide) (by decide) (by decide) (by decide) hn).trans a4
  have b5 : arr s₆.mem L.Q 4 5 = rOf s.mem L sig :=
    (Outs.arrEq_mont o6 (by decide) (by decide) (by decide) (by decide) hn).trans a5
  refine WP.seq (WP.mono (prod_mont_ok M6 (o := 6) (a := 6) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [b1, b0]; exact Nat.mod_lt _ (by omega))) fun s₇ ⟨⟨l7, e7, o7, w7⟩, k7⟩ => ?_)
  have M7 := M6.keep k7 (by decide) w7
  rw [b0] at l7
  rw [b0, b1] at e7
  have u1 : arr s₇.mem L.Q 4 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) * W % arrQ s.mem L 0 :=
    prod_mont_back hcop l7 e6 (by rw [e7, hRR])
  have c0 : arr s₇.mem L.Q 4 0 = arrQ s.mem L 0 :=
    (Outs.arrEq_mont o7 (by decide) (by decide) (by decide) (by decide) hn).trans b0
  have c1 : arr s₇.mem L.Q 4 1 = R2 % arrQ s.mem L 0 :=
    (Outs.arrEq_mont o7 (by decide) (by decide) (by decide) (by decide) hn).trans b1
  have c4 : arr s₇.mem L.Q 4 4 = W :=
    (Outs.arrEq_mont o7 (by decide) (by decide) (by decide) (by decide) hn).trans b4
  have c5 : arr s₇.mem L.Q 4 5 = rOf s.mem L sig :=
    (Outs.arrEq_mont o7 (by decide) (by decide) (by decide) (by decide) hn).trans b5
  -- u2.
  refine WP.seq (WP.mono (prod_mont_ok M7 (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [c4, c0]; exact hW)) fun s₈ ⟨⟨_, e8, o8, w8⟩, k8⟩ => ?_)
  have M8 := M7.keep k8 (by decide) w8
  rw [c0, c5, c4] at e8
  have d0 : arr s₈.mem L.Q 4 0 = arrQ s.mem L 0 :=
    (Outs.arrEq_mont o8 (by decide) (by decide) (by decide) (by decide) hn).trans c0
  have d1 : arr s₈.mem L.Q 4 1 = R2 % arrQ s.mem L 0 :=
    (Outs.arrEq_mont o8 (by decide) (by decide) (by decide) (by decide) hn).trans c1
  have d6 : arr s₈.mem L.Q 4 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) * W % arrQ s.mem L 0 :=
    (Outs.arrEq_mont o8 (by decide) (by decide) (by decide) (by decide) hn).trans u1
  refine WP.seq (WP.mono (prod_mont_ok M8 (o := 5) (a := 5) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [d1, d0]; exact Nat.mod_lt _ (by omega))) fun s₉ ⟨⟨l9, e9, o9, w9⟩, k9⟩ => ?_)
  have M9 := M8.keep k9 (by decide) w9
  rw [d0] at l9
  rw [d0, d1] at e9
  have u2 : arr s₉.mem L.Q 4 5 = rOf s.mem L sig * W % arrQ s.mem L 0 :=
    prod_mont_back hcop l9 e8 (by rw [e9, hRR])
  have u1' : arr s₉.mem L.Q 4 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) * W % arrQ s.mem L 0 :=
    (Outs.arrEq_mont o9 (by decide) (by decide) (by decide) (by decide) hn).trans d6
  have qa9 : QArr L s.mem s₉.mem := by
    have := ((prod_qarr o6 (by decide)).trans (prod_qarr o7 (by decide))).trans
      ((prod_qarr o8 (by decide)).trans (prod_qarr o9 (by decide)))
    rw [m5] at this
    exact qa14.trans this
  have k39 := ((((k4.trans k5).trans k6).trans k7).trans k8).trans k9
  have k19 := (k12.trans k3).trans k39
  have Q9 : QS s₉ L key sig dig := ⟨⟨M9.toEnv, (k19.gpr .r21 (by decide)).trans h.inq.h21,
    (k19.gpr .r23 (by decide)).trans h.inq.h23⟩, h.scr.congr k19.wr, h.regs.keep k19⟩
  -- To the buffer.
  refine WP.seq (WP.mono (ptrBuf_ok hL Q9.regs) fun s₁₀ ⟨⟨c12, c6, m10⟩, k10⟩ => ?_)
  have e10 := M9.toEnv.keep k10 (by decide)
  refine WP.seq (WP.mono (storeBE_ok (j := 6) (O := L.Buf) (k := L.ql) e10 (by decide)
    (ScrL.bufN (s := s₁₀) (Q9.scr.congr k10.wr) hL (by omega)) c12 c6 (by omega) (by omega)
    (buf_sepQ L (by omega))) fun s₁₁ ⟨⟨vt, ot⟩, k11⟩ => ?_)
  rw [m10] at vt ot
  have k911 := k10.trans k11
  have qb11 : QBuf L s₉.mem s₁₁.mem := QBuf.ofBuf hL ot (by omega)
  have Q11 : QS s₁₁ L key sig dig := Q9.step k911 (by decide)
  refine WP.seq (WP.mono (ptrBuf2_ok hL Q11.regs) fun s₁₂ ⟨⟨f12, f6, m12⟩, k12'⟩ => ?_)
  have e12 := e10.keep (k11.trans k12') (by decide)
  refine WP.mono (storeBE_ok (j := 5) (O := off L.Buf L.ql) (k := L.ql) e12 (by decide)
    (scr_sub (ScrL.buf (s := s₁₂) (Q11.scr.congr k12'.wr) hL) (o := L.ql) (n := L.ql) (by omega) (by omega)) f12 f6
    (by omega) (by omega) (by rw [buf_eq, off_off]; exact prod_sepQ L (by omega) (by omega)))
    fun t ⟨⟨vt2, ot2⟩, kt⟩ => ?_
  rw [m12] at vt2 ot2
  have ot2b : Outside L.Buf (L.ql + 0) L.ql s₁₁.mem t.mem := outside_shift ot2 (by omega) (by omega)
  have qbt : QBuf L s₁₁.mem t.mem := QBuf.ofBuf hL (n := 2 * L.ql) (ot2b.mono (Nat.zero_le _) (by omega))
    (by omega)
  have kall := (k19.trans (k911.trans k12')).trans kt
  have ot' : Outside (off L.Q 1600) 0 L.ql s₉.mem s₁₁.mem := by rw [← buf_eq]; exact ot
  have otq := outside_shift ot' (by omega) (by decide)
  have u2' : arr s₁₁.mem L.Q 4 5 = rOf s.mem L sig * W % arrQ s.mem L 0 :=
    (Outside.val32 otq (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)).trans u2
  refine ⟨⟨Q11.step (k12'.trans kt) (by decide), ?_, ?_, qa9.qbuf.trans (qb11.trans qbt)⟩,
    kall.mono (by decide)⟩
  · rw [prod_bytes_keep ot2b (by omega) (by omega)]
    refine (vt.trans (read_low (w := 4) _ _ (by omega) ?_)).trans u1'
    show arr s₉.mem L.Q 4 6 < _
    rw [u1']
    exact Nat.lt_trans (Nat.mod_lt _ (by omega)) hql
  · refine (vt2.trans (read_low (w := 4) _ _ (by omega) ?_)).trans u2'
    show arr s₁₁.mem L.Q 4 5 < _
    rw [u2']
    exact Nat.lt_trans (Nat.mod_lt _ (by omega)) hql

end VG.Proof.Dsa.PPC64LE
