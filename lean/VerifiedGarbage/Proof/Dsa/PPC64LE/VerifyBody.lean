module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyComb
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
public import VerifiedGarbage.Proof.Dsa.PPC64LE.ReduceQ
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-! ### `Dsa.PPC64LE.VerifyProd`, which this module and modules that import it used -/

section

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
  obtain e := pack_qb h1 h2 h3 h4
  simp only [Nat.reduceSub, Nat.reducePow] at *
  omega_arith

/-- The borrow of `a − b`, for `a` and `b` below `2^63`. -/
theorem sub_shr63 {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = BitVec.ofNat 64 (if a < b then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow] at *
  split <;> omega_arith

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
        sub_shr63 (a := qb) (b := d) (by omega_arith) (by omega_arith)]) (by decide)) fun t ⟨⟨a6, a0, a3, m⟩, _⟩ => ?_)
  refine WP.ite _ (eval_zero_ofNat _ _ (by split <;> decide) a3) (fun hz => ?_) (fun hz => ?_)
  · have hz : ¬ qb < d := by
      have := of_decide_eq_true hz; split at this <;> simp_all
    prun [a0, m, BitVec.or_self]
    rw [Nat.min_eq_left (by omega_arith)]
  · have hz : qb < d := by
      have := of_decide_eq_false hz; split at this <;> simp_all
    exact wp_nil ⟨by rw [a6, Nat.min_eq_right (by omega_arith)], m⟩

/-- `scalar`: the digest's first `min(d, qb)` octets into array 6. -/
theorem prod_scalar_ok {s : State} {L : Lay} {key sig dig : Addr} {qb d : Nat} (h : QS s L key sig dig)
    (hL : L.Ok) (h2 : s.gpr .r2 = pack L.pl L.ql qb d) (hqb : qb ≤ L.ql) (hd : d < 2 ^ 16)
    (hdg : Src s L dig (min d qb)) :
    WP isa scalar s fun t =>
      (QS t L key sig dig ∧ arrQ t.mem L 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) ∧
        Outside L.Q (slot 4 6) (8 * (4 + 2)) s.mem t.mem) ∧ Keep prodScalarRegs s t := by
  have hql := hL.ql
  obtain hpl : L.pl < 2 ^ 16 := by rcases hL.pl with e | e | e <;> omega_arith
  unfold scalar
  refine WP.seq (WP.mono (scalarLen_ok h2 hpl (by omega_arith) (by omega_arith) hd) fun s₀ ⟨⟨a6, m0⟩, k0⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = dig ∧ u.mem = s₀.mem)
    (by prun [((k0.gpr .r26 (by decide)).trans h.regs.r26), BitVec.add_zero]) (by decide))
    fun s₁ ⟨⟨a12, m1⟩, k1'⟩ => ?_)
  obtain a6 : s₁.gpr .r6 = BitVec.ofNat 64 (min d qb) := (k1'.gpr .r6 (by decide)).trans a6
  obtain k1 := k0.trans k1'
  obtain m1 : s₁.mem = s.mem := m1.trans m0
  obtain hdl : min d qb ≤ L.ql := Nat.le_trans (Nat.min_le_right _ _) hqb
  generalize min d qb = dl at a6 hdg hdl ⊢
  obtain Q1 := h.step k1 (by decide)
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega_arith) a6) (fun hz => ?_) (fun hz => ?_)
  · have hz : dl = 0 := of_decide_eq_true hz
    subst hz
    refine WP.mono (zeroArr_ok Q1.inq.env (j := 6) (by decide)) fun t ⟨⟨z6, ot⟩, kt⟩ => ?_
    obtain qa : QArr L s₁.mem t.mem := QArr.of ot (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)
    refine ⟨⟨Q1.step kt (by decide), ?_, ?_⟩, (k1.trans kt).mono (by decide)⟩
    · rw [arrQ, z6]; rfl
    · rw [← m1]; exact ot.mono (Nat.le_refl _) (by omega_arith)
  · have hz : dl ≠ 0 := of_decide_eq_false hz
    refine WP.mono (loadQ_ok (j := 6) Q1 hL (by decide) (by decide) (hdg.keep k1.rd k1.wr) a12 a6 (by omega_arith)
      (by omega_arith)) fun t ⟨⟨Qt, v6, _, ot, _⟩, kt⟩ => ?_
    rw [m1] at v6 ot
    exact ⟨⟨Qt, v6, ot.mono (Nat.le_refl _) (by omega_arith)⟩, (k1.trans kt).mono (by decide)⟩

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
  obtain h8 := slot_lt (w := w) (show 8 < 28 by decide)
  have hZ := h.hZ
  refine WP.mono (Pub.montOp_ok h.hs (by omega_arith) ha hb (by omega_arith) (by omega_arith) ha2 hb2
    (by omega_arith) (by omega_arith) (by omega_arith) h.h10 h.h29 h.h11 h.h12 h.inv hB) fun t ⟨⟨hlt, heq, hout⟩, k⟩ =>
    ⟨⟨hlt, heq, hout, ?_⟩, k⟩
  refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => hout _ fun r hr => ?_)
  have := h.hs.nowrap
  obtain h0 := slot_lt (w := w) (show 0 < 28 by decide)
  rw [ofs_off B (by omega_arith)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> omega_arith

/-- A Montgomery multiplication's frame in the Q space. -/
theorem prod_qarr {L : Lay} {m m' : Mem} {o : Nat} (h : Outs L.Q (montRanges 4 o) m m') (ho : o = 5 ∨ o = 6) :
    QArr L m m' :=
  outs_within h (by
    simp only [montRanges, List.mem_cons, List.not_mem_nil, or_false]
    intro r hr
    rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp only [slot_eq] <;> omega_arith)

/-- Two Montgomery multiplications, by `y` and by `R² mod q`: `x y mod q`. -/
theorem prod_mont_back {q R A B X Y : Nat} (hR : Nat.Coprime R q) (hB : B < q) (hA : A * R % q = X * Y % q)
    (hB' : B * R % q = A * (R * R % q) % q) : B = X * Y % q := by
  obtain e : B * R % q = X * Y * R % q := by
    rw [hB', Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, hA,
      Nat.mod_mul_mod]
  have := VG.Proof.Bignum.mont_cancel hR e
  rw [Nat.mod_eq_of_lt hB] at this
  exact this

/-- The buffer from `q_len` on is past the Q space. -/
theorem prod_sepQ (L : Lay) {d n : Nat} (hd : 1600 ≤ d) (hn : d + n ≤ 2 ^ 64) :
    ∀ x, ofs (off L.Q d) x < n → 1600 ≤ ofs L.Q x := by
  intro x hx
  obtain hlt := (x - L.Q).isLt
  simp only [ofs, off] at hx ⊢
  rw [Offset.toNat_sub_add x L.Q (by omega_arith)] at hx
  by_contra hc
  rw [Nat.mod_eq_of_lt (by omega)] at hx
  omega_arith

/-- Octets below a frame's range keep their values. -/
theorem prod_bytes_keep {B : Addr} {o n k : Nat} {m m' : Mem} (h : Outside B o n m m') (hk : k ≤ o)
    (hk' : k < 2 ^ 64) : Spec.Rsa.bytesAt m' B k = Spec.Rsa.bytesAt m B k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inl ?_)
  obtain hi := List.mem_range.mp hi
  rw [show B + BitVec.ofNat 64 i = off B i from rfl, VG.Proof.Bignum.PPC64LE.ofs_off0 B (by omega_arith)]
  omega_arith

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
        QBuf L s.mem t.mem ∧ arrQ t.mem L 1 = 2 ^ (128 * 4) % arrQ s.mem L 0) ∧ Keep prodRegs s t := by
  have hq := hL.ql
  have hpl := hL.pl
  obtain hn : slot 4 28 ≤ 2 ^ 64 := by decide
  obtain hcop : Nat.Coprime (2 ^ (64 * 4)) (arrQ s.mem L 0) := VG.Proof.Bignum.coprime_pow2 hqo _
  obtain hRR := pow_sq_eq 4
  generalize (2 : Nat) ^ (128 * 4) = R2 at h8 hRR ⊢
  unfold products
  -- The digest's scalar into array 6, r into array 5, `R² mod q` into array 1.
  refine WP.seq (WP.mono (prod_scalar_ok h hL h2 hqb hd hdg) fun s₁ ⟨⟨Q1, v6, o1⟩, k1⟩ => ?_)
  obtain qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)
  refine WP.seq (WP.mono (ptrR_ok Q1.regs) fun s₂ ⟨⟨a12, a6, m2⟩, k2⟩ => ?_)
  obtain Q2 := Q1.step k2 (by decide)
  obtain k12 := k1.trans k2
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q2 hL (by decide) (by decide)
      ((hsg.keep k12.rd k12.wr).sub (o := 0) (k := L.ql) (by omega_arith)) (by rw [a12, off, BitVec.add_zero]) a6
      (by omega_arith) (by omega_arith)) fun s₃ ⟨⟨Q3, v5, _, o3, qa3⟩, k3⟩ => ?_)
  rw [m2] at v5 o3 qa3
  refine WP.seq (WP.mono (copy_ok Q3.inq.env (o := 1) (a := 8) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨v1, o4⟩, k4⟩ => ?_)
  obtain qa4 : QArr L s₃.mem s₄.mem := QArr.of o4 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)
  obtain Q4 := Q3.step k4 (by decide)
  obtain qa14 : QArr L s.mem s₄.mem := (qa1.trans qa3).trans qa4
  obtain o3' : Outside L.Q (slot 4 5) (8 * (4 + 2)) s₁.mem s₃.mem := o3.mono (Nat.le_refl _) (by omega_arith)
  have a0 : arr s₄.mem L.Q 4 0 = arrQ s.mem L 0 := qa14.arr0
  obtain a4 : arr s₄.mem L.Q 4 4 = W := by
    rw [Outside.arrEq o4 (by decide) (by decide) hn, Outside.arrEq o3' (by decide) (by decide) hn,
      Outside.arrEq o1 (by decide) (by decide) hn]
    exact h4
  obtain a1 : arr s₄.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := by
    rw [v1, Outside.arrEq o3' (by decide) (by decide) hn, Outside.arrEq o1 (by decide) (by decide) hn]
    exact h8
  obtain a6 : arr s₄.mem L.Q 4 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) := by
    rw [Outside.arrEq o4 (by decide) (by decide) hn, Outside.arrEq o3' (by decide) (by decide) hn]
    exact v6
  obtain a5 : arr s₄.mem L.Q 4 5 = rOf s.mem L sig := by
    rw [Outside.arrEq o4 (by decide) (by decide) hn]
    refine v5.trans ?_
    rw [(hsg.sub (o := 0) (k := L.ql) (by omega_arith)).bytes (qa1.qbody.body hL) hL.z256]
    simp only [rOf, off, BitVec.add_zero]
  -- `-q⁻¹`.
  obtain hodd : (word s₄.mem L.Q (slot 4 0)).toNat % 2 = 1 :=
    word_odd _ _ _ (2 * 4) (by decide) (by show arr s₄.mem L.Q 4 0 % 2 = 1; rw [a0]; exact hqo)
  refine WP.seq (WP.mono (Pub.minv_ok Q4.inq.env.hs Q4.inq.env.h10 (by decide) hodd)
    fun s₅ ⟨⟨i12, inv, m5⟩, k5⟩ => ?_)
  obtain M5 : MCtx s₅ L.Q 1600 4 := ⟨Q4.inq.env.keep k5 (by decide), i12, by rw [m5]; exact inv⟩
  rw [← m5] at a0 a4 a1 a6 a5
  -- u1.
  refine WP.seq (WP.mono (prod_mont_ok M5 (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [a4, a0]; exact hW)) fun s₆ ⟨⟨_, e6, o6, w6⟩, k6⟩ => ?_)
  obtain M6 := M5.keep k6 (by decide) w6
  rw [a0, a6, a4] at e6
  obtain b0 : arr s₆.mem L.Q 4 0 = arrQ s.mem L 0 :=
    (Outs.arrEq_mont o6 (by decide) (by decide) (by decide) (by decide) hn).trans a0
  obtain b1 : arr s₆.mem L.Q 4 1 = R2 % arrQ s.mem L 0 :=
    (Outs.arrEq_mont o6 (by decide) (by decide) (by decide) (by decide) hn).trans a1
  obtain b4 : arr s₆.mem L.Q 4 4 = W :=
    (Outs.arrEq_mont o6 (by decide) (by decide) (by decide) (by decide) hn).trans a4
  obtain b5 : arr s₆.mem L.Q 4 5 = rOf s.mem L sig :=
    (Outs.arrEq_mont o6 (by decide) (by decide) (by decide) (by decide) hn).trans a5
  refine WP.seq (WP.mono (prod_mont_ok M6 (o := 6) (a := 6) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [b1, b0]; exact Nat.mod_lt _ (by omega_arith))) fun s₇ ⟨⟨l7, e7, o7, w7⟩, k7⟩ => ?_)
  obtain M7 := M6.keep k7 (by decide) w7
  rw [b0] at l7
  rw [b0, b1] at e7
  obtain u1 : arr s₇.mem L.Q 4 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) * W % arrQ s.mem L 0 :=
    prod_mont_back hcop l7 e6 (by rw [e7, hRR])
  obtain c0 : arr s₇.mem L.Q 4 0 = arrQ s.mem L 0 :=
    (Outs.arrEq_mont o7 (by decide) (by decide) (by decide) (by decide) hn).trans b0
  obtain c1 : arr s₇.mem L.Q 4 1 = R2 % arrQ s.mem L 0 :=
    (Outs.arrEq_mont o7 (by decide) (by decide) (by decide) (by decide) hn).trans b1
  obtain c4 : arr s₇.mem L.Q 4 4 = W :=
    (Outs.arrEq_mont o7 (by decide) (by decide) (by decide) (by decide) hn).trans b4
  obtain c5 : arr s₇.mem L.Q 4 5 = rOf s.mem L sig :=
    (Outs.arrEq_mont o7 (by decide) (by decide) (by decide) (by decide) hn).trans b5
  -- u2.
  refine WP.seq (WP.mono (prod_mont_ok M7 (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [c4, c0]; exact hW)) fun s₈ ⟨⟨_, e8, o8, w8⟩, k8⟩ => ?_)
  obtain M8 := M7.keep k8 (by decide) w8
  rw [c0, c5, c4] at e8
  obtain d0 : arr s₈.mem L.Q 4 0 = arrQ s.mem L 0 :=
    (Outs.arrEq_mont o8 (by decide) (by decide) (by decide) (by decide) hn).trans c0
  obtain d1 : arr s₈.mem L.Q 4 1 = R2 % arrQ s.mem L 0 :=
    (Outs.arrEq_mont o8 (by decide) (by decide) (by decide) (by decide) hn).trans c1
  obtain d6 : arr s₈.mem L.Q 4 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) * W % arrQ s.mem L 0 :=
    (Outs.arrEq_mont o8 (by decide) (by decide) (by decide) (by decide) hn).trans u1
  refine WP.seq (WP.mono (prod_mont_ok M8 (o := 5) (a := 5) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [d1, d0]; exact Nat.mod_lt _ (by omega_arith))) fun s₉ ⟨⟨l9, e9, o9, w9⟩, k9⟩ => ?_)
  obtain M9 := M8.keep k9 (by decide) w9
  rw [d0] at l9
  rw [d0, d1] at e9
  obtain u2 : arr s₉.mem L.Q 4 5 = rOf s.mem L sig * W % arrQ s.mem L 0 :=
    prod_mont_back hcop l9 e8 (by rw [e9, hRR])
  obtain u1' : arr s₉.mem L.Q 4 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) * W % arrQ s.mem L 0 :=
    (Outs.arrEq_mont o9 (by decide) (by decide) (by decide) (by decide) hn).trans d6
  obtain qa9 : QArr L s.mem s₉.mem := by
    have := ((prod_qarr o6 (by decide)).trans (prod_qarr o7 (by decide))).trans
      ((prod_qarr o8 (by decide)).trans (prod_qarr o9 (by decide)))
    rw [m5] at this
    exact qa14.trans this
  obtain k39 := ((((k4.trans k5).trans k6).trans k7).trans k8).trans k9
  obtain k19 := (k12.trans k3).trans k39
  obtain Q9 : QS s₉ L key sig dig := ⟨⟨M9.toEnv, (k19.gpr .r21 (by decide)).trans h.inq.h21,
    (k19.gpr .r23 (by decide)).trans h.inq.h23⟩, h.scr.congr k19.wr, h.regs.keep k19⟩
  -- To the buffer.
  refine WP.seq (WP.mono (ptrBuf_ok hL Q9.regs) fun s₁₀ ⟨⟨c12, c6, m10⟩, k10⟩ => ?_)
  obtain e10 := M9.toEnv.keep k10 (by decide)
  refine WP.seq (WP.mono (storeBE_ok (j := 6) (O := L.Buf) (k := L.ql) e10 (by decide)
    (ScrL.bufN (s := s₁₀) (Q9.scr.congr k10.wr) hL (by omega_arith)) c12 c6 (by omega_arith) (by omega_arith)
    (buf_sepQ L (by omega_arith))) fun s₁₁ ⟨⟨vt, ot⟩, k11⟩ => ?_)
  rw [m10] at vt ot
  obtain k911 := k10.trans k11
  obtain qb11 : QBuf L s₉.mem s₁₁.mem := QBuf.ofBuf hL ot (by omega_arith)
  obtain Q11 : QS s₁₁ L key sig dig := Q9.step k911 (by decide)
  refine WP.seq (WP.mono (ptrBuf2_ok hL Q11.regs) fun s₁₂ ⟨⟨f12, f6, m12⟩, k12'⟩ => ?_)
  obtain e12 := e10.keep (k11.trans k12') (by decide)
  refine WP.mono (storeBE_ok (j := 5) (O := off L.Buf L.ql) (k := L.ql) e12 (by decide)
    (scr_sub (ScrL.buf (s := s₁₂) (Q11.scr.congr k12'.wr) hL) (o := L.ql) (n := L.ql) (by omega_arith) (by omega_arith)) f12 f6
    (by omega_arith) (by omega_arith) (by rw [buf_eq, off_off]; exact prod_sepQ L (by omega_arith) (by omega_arith)))
    fun t ⟨⟨vt2, ot2⟩, kt⟩ => ?_
  rw [m12] at vt2 ot2
  obtain ot2b : Outside L.Buf (L.ql + 0) L.ql s₁₁.mem t.mem := outside_shift ot2 (by omega_arith) (by omega_arith)
  obtain qbt : QBuf L s₁₁.mem t.mem := QBuf.ofBuf hL (n := 2 * L.ql) (ot2b.mono (Nat.zero_le _) (by omega_arith))
    (by omega_arith)
  obtain kall := (k19.trans (k911.trans k12')).trans kt
  obtain ot' : Outside (off L.Q 1600) 0 L.ql s₉.mem s₁₁.mem := by rw [← buf_eq]; exact ot
  obtain otq := outside_shift ot' (by omega_arith) (by decide)
  obtain u2' : arr s₁₁.mem L.Q 4 5 = rOf s.mem L sig * W % arrQ s.mem L 0 :=
    (Outside.val32 otq (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)).trans u2
  obtain a1t : arrQ t.mem L 1 = R2 % arrQ s.mem L 0 := by
    obtain e9' : arr s₉.mem L.Q 4 1 = R2 % arrQ s.mem L 0 :=
      (Outs.arrEq_mont o9 (by decide) (by decide) (by decide) (by decide) hn).trans d1
    obtain s11 : arr s₁₁.mem L.Q 4 1 = arr s₉.mem L.Q 4 1 :=
      Outside.val32 otq (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)
    obtain otq2 := outside_shift (B := L.Q) (a := 1600) (by rw [← buf_eq]; exact ot2b) (by omega_arith) (by decide)
    exact (Outside.val32 otq2 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)).trans
      (s11.trans e9')
  refine ⟨⟨Q11.step (k12'.trans kt) (by decide), ?_, ?_, qa9.qbuf.trans (qb11.trans qbt), a1t⟩,
    kall.mono (by decide)⟩
  · rw [prod_bytes_keep ot2b (by omega_arith) (by omega_arith)]
    refine (vt.trans (read_low (w := 4) _ _ (by omega_arith) ?_)).trans u1'
    show arr s₉.mem L.Q 4 6 < _
    rw [u1']
    exact Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hql
  · refine (vt2.trans (read_low (w := 4) _ _ (by omega_arith) ?_)).trans u2'
    show arr s₁₁.mem L.Q 4 5 < _
    rw [u2']
    exact Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hql

end VG.Proof.Dsa.PPC64LE

end

end

/-! ### `Dsa.PPC64LE.VerifyEnd`, which only this module used -/

section

/-!
# DSA verification on PPC64LE: the comparison

`compare_ok`: `v mod q` (`vModQ_ok`, from the P space's array 4) compared
with r, under the mask in the header's word `hMask`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot slot_sep)

theorem mask_bit (c b : Bool) :
    mask c &&& mask b &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (if c = true ∧ b = true then 1 else 0) := by
  cases c <;> cases b <;> rfl

/-- The registers `compare` writes. -/
def cmpRegs : List Reg :=
  copyRegs ++ vModRegs ++ [.r5, .r8, .r9] ++ [.r6, .r12] ++ loadRegs ++ eqRegs .r3 ++ [.r0, .r3, .r4]

/-- `compare`, in the P space with `V` in its array 4, q (odd) in the Q space's
array 0 and `R² mod q` in its array 1: `r3 := 1` if `V mod q = r` and `b`
(the mask in `hMask`), else 0. -/
theorem compare_ok {s : State} {L : Lay} {key sig dig : Addr} {b : Bool} {V : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hsg : Src s L sig (2 * L.ql)) (hP : InP s L)
    (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1) (h1 : arrQ s.mem L 1 = 2 ^ (128 * 4) % arrQ s.mem L 0)
    (hv : arrP s.mem L 4 = V) (hm : word s.mem L.S hMask = mask b) :
    WP isa Verify.compare s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if V % arrQ s.mem L 0 = rOf s.mem L sig ∧ b = true then 1 else 0) ∧
        Body L s.mem t.mem) ∧ Keep cmpRegs s t := by
  have hql := hL.ql
  have hpl := hL.pl
  have hw := hL.wp_ge
  have hbe := hL.buf_end
  have hnw := hL.nowrap
  have e74 : slot 4 4 = 448 := rfl
  have e75 : slot 4 5 = 496 := rfl
  unfold Verify.compare
  -- v into the P space's array 6.
  refine WP.seq (WP.mono (copy_ok hP.env (o := 6) (a := 4) (by decide) (by decide) (by decide))
    fun s₁ ⟨⟨v6, o1⟩, k1⟩ => ?_)
  obtain B1 : Body L s.mem s₁.mem := Body.ofP hL o1 (by simp only [Lay.slot_eq]; omega_arith)
    (by simp only [Lay.qOff, Lay.slot_eq]; omega_arith)
  obtain pb1 : PBody L s.mem s₁.mem := o1.mono (by simp only [Lay.slot_eq]; omega_arith)
    (by simp only [Lay.qOff, Lay.slot_eq]; omega_arith)
  obtain aq : ∀ j < 28, arrQ s₁.mem L j = arrQ s.mem L j := fun j hj => pb1.arrQ hL j hj
  -- `v mod q` into the Q space's array 4.
  refine WP.seq (WP.mono (vModQ_ok hL (hs.congr k1.wr) (hr.keep k1 (by decide)) (by rw [aq 0 (by decide)]; exact hq2)
      (by rw [aq 0 (by decide)]; exact hqo) (by rw [aq 1 (by decide), aq 0 (by decide)]; exact h1))
    fun s₂ ⟨⟨q2, r2, a4, a0, _, o2⟩, k2⟩ => ?_)
  rw [aq 0 (by decide)] at a4 a0
  obtain v6' : arrP s₁.mem L 6 = V := v6.trans hv
  rw [v6'] at a4
  obtain B2 : Body L s₁.mem s₂.mem := o2.mono (by simp only [Lay.qOff, Lay.slot_eq]; omega_arith)
    (by simp only [Lay.bOff, Lay.qOff] at hbe ⊢; have : slot 4 24 = 1408 := rfl; omega_arith)
  obtain B12 := B1.trans B2
  obtain k12 := k1.trans k2
  obtain Q2 : QS s₂ L key sig dig := ⟨q2, hs.congr k12.wr, r2⟩
  refine WP.seq (WP.mono (ptrR_ok Q2.regs) fun s₃ ⟨⟨b12, b6, m3⟩, k3⟩ => ?_)
  obtain Q3 := Q2.step k3 (by decide)
  obtain k13 := k12.trans k3
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q3 hL (by decide) (by decide)
      ((hsg.keep k13.rd k13.wr).sub (o := 0) (k := L.ql) (by omega_arith)) (by rw [b12, off, BitVec.add_zero]) b6
      (by omega_arith) (by omega_arith)) fun s₄ ⟨⟨Q4, v5, _, o4, qa4⟩, k4⟩ => ?_)
  refine WP.seq (WP.mono (eqMask_ok Q4.inq.env .r3 (a := 4) (b := 5) (by decide) (by decide))
    fun s₅ ⟨⟨c3, m5⟩, k5⟩ => ?_)
  obtain k15 := (k13.trans k4).trans k5
  refine WP.mono (WP.keep [.r0, .r3, .r4] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64
      (if V % arrQ s.mem L 0 = rOf s.mem L sig ∧ b = true then 1 else 0) ∧ u.mem = s₅.mem) ?_ (by decide))
    fun t ⟨⟨t3, mt⟩, kt⟩ => ⟨⟨t3, ?_⟩, (k15.trans kt).mono (by decide)⟩
  · have a1 : val32 s₄.mem L.Q (slot 4 4) (2 * 4) = V % arrQ s.mem L 0 := by
      rw [Outside.val32 o4 (by rw [e74, e75]; omega_arith) (by decide), m3]; exact a4
    obtain a5 : val32 s₄.mem L.Q (slot 4 5) (2 * 4) = rOf s.mem L sig := by
      have := v5
      rw [arrQ, arr] at this
      rw [this, m3, (hsg.sub (o := 0) (k := L.ql) (by omega_arith)).bytes B12 hL.z256]
      simp only [rOf, off, BitVec.add_zero]
    obtain hb5 : Body L s.mem s₅.mem := by
      rw [m5]; exact B12.trans (by rw [← m3]; exact qa4.qbody.body hL)
    obtain hv' : s₅.mem.readW (L.S + BitVec.ofNat 64 0) 64 = mask b := by
      have := Outside.word hb5 (d := 0) (by omega_arith) (by omega_arith)
      rw [← hm]; exact this
    obtain hld : InRegions (s₅.rd ++ s₅.wr) (L.S + BitVec.ofNat 64 0) 8 :=
      (hs.congr (k15.wr)).ld (show 0 + 8 ≤ L.Z by have := hL.z256; omega_arith)
    rw [a1, a5] at c3
    prun [c3, (k15.gpr .r21 (by decide)).trans hr.r21, hMask, hld, hv', mask_bit]
    simp only [decide_eq_true_eq]
  · rw [mt, m5]
    exact B12.trans (by rw [← m3]; exact qa4.qbody.body hL)

end VG.Proof.Dsa.PPC64LE

end

end


/-!
# DSA verification on PPC64LE: after the check of the key

`body_ok`: `Verify.body` leaves in `r3` 1 exactly when r and s are in
`(0, q)` and `(g^u1 y^u2 mod p) mod q = r`, for `w = s^(q − 2) mod q`,
`u1 = z w mod q` and `u2 = r w mod q` (`vComp`), z the digest's first
`min(digest_len, bitLength q / 8)` octets.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot slot_sep)

/-- The value verification compares with r. -/
def vComp (p q g y z r s : Nat) : Nat :=
  (g ^ (z * (s ^ (q - 2) % q) % q) % p * (y ^ (r * (s ^ (q - 2) % q) % q) % p) % p) % q

/-- Memory that changed only at offsets below `qOff` of `scratch` keeps the Q space. -/
theorem keepQ_of {L : Lay} (hL : L.Ok) {m m' : Mem} (h : ∀ x, L.qOff ≤ ofs L.S x → m' x = m x) :
    Outside L.Q 1600 (2 ^ 64 - 1600) m m' := by
  intro x hx
  obtain hq : L.qOff ≤ 11456 := by rw [hL.qOff_eq]; rcases hL.pl with e | e | e <;> omega_arith
  obtain hlt := (x - L.S).isLt
  obtain hlt' := (x - L.Q).isLt
  refine h x ?_
  simp only [ofs, Lay.Q, off] at hx ⊢
  rw [Offset.toNat_sub_add x L.S (by omega_arith)] at hx
  by_cases hd : L.qOff ≤ (x - L.S).toNat
  · exact hd
  · rw [Nat.mod_eq_of_lt (by omega_arith)] at hx; omega_arith

/-- A change in the Q space's arrays or the buffer keeps the P space. -/
theorem QBuf.keepP {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') :
    Outside L.S (L.qOff + slot 4 1) (1600 + 2 * L.pl - slot 4 1) m m' := by
  obtain hq : L.qOff ≤ 11456 := by rw [hL.qOff_eq]; rcases hL.pl with e | e | e <;> omega_arith
  exact outside_shift (B := L.S) (a := L.qOff) h (by have := hL.pl; rw [show slot 4 1 = 304 from rfl]; omega_arith)
    (by omega_arith)

theorem QBuf.arrP {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') {j : Nat} (hj : j < 28) :
    arrP m' L j = arrP m L j := by
  have := slot_lt (w := L.wp) hj
  exact Outside.val32 (h.keepP hL) (Or.inl (by simp only [Lay.qOff] at *; omega_arith))
    (by have := hL.nowrap; have := hL.buf_end; simp only [Lay.bOff, Lay.qOff] at *; omega_arith)

/-- A buffer's first `min n k` octets. -/
theorem bytesAt_take (m : Mem) (D : Addr) (n k : Nat) :
    (Spec.Rsa.bytesAt m D n).take k = Spec.Rsa.bytesAt m D (min n k) := by
  simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_comm]

/-- The store of the mask in the header. -/
theorem Kept.ofMask {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.S hMask 8 m m') : Kept L m m' :=
  ⟨h.mono (Nat.zero_le _) (by have := hL.z256; simp only [hMask]; omega_arith), fun i hi =>
    Outside.word h (Or.inr (by simp only [saveOff, hMask]; omega_arith))
      (by have := hL.nowrap; have := hL.z256; simp only [saveOff]; omega_arith)⟩

/-- The signature's and the digest's values, kept. -/
theorem sig_kept {s : State} {L : Lay} {sig dig : Addr} {D : Nat} (hsg : Src s L sig (2 * L.ql))
    (hdg : Src s L dig D) {m m' : Mem} (h : Outside L.S 0 L.Z m m') {k : Nat} (hk : k ≤ D) :
    rOf m' L sig = rOf m L sig ∧ sOf m' L sig = sOf m L sig ∧
      Spec.Rsa.bytesAt m' dig k = Spec.Rsa.bytesAt m dig k := by
  refine ⟨?_, ?_, (hdg.take hk).kept h⟩
  · have e := (hsg.sub (o := 0) (k := L.ql) (by omega_arith)).kept h
    simp only [off, BitVec.add_zero] at e
    simp only [rOf]; rw [e]
  · simp only [sOf]; rw [(hsg.sub (o := L.ql) (k := L.ql) (by omega_arith)).kept h]

/-- Every register but `r2` (the lengths) and `r21` (which keeps `S`). -/
def notR21 : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
    .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem keep_but21 {rs : List Reg} {s t : State} (h : Keep rs s t) (hr : Reg.r21 ∉ rs) (hr2 : Reg.r2 ∉ rs) :
    Keep notR21 s t :=
  h.mono fun r hm => by
    have : r ≠ .r21 := fun e => hr (e ▸ hm)
    have : r ≠ .r2 := fun e => hr2 (e ▸ hm)
    cases r <;> simp_all [notR21]

/-- The registers `Verify.body` writes: all but `r2` and `r21`. -/
abbrev bodyRegs : List Reg := notR21

/-- The store of the mask keeps the P space's arrays. -/
theorem mask_arrP {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.S hMask 8 m m') {j : Nat} (hj : j < 28) :
    arrP m' L j = arrP m L j := by
  have := slot_lt (w := L.wp) hj
  have := hL.wp_ge
  have := hL.nowrap
  have := hL.buf_end
  simp only [Lay.bOff, Lay.qOff] at *
  exact Outside.val32 h (Or.inr (by simp only [hMask, Lay.slot_eq] at *; omega_arith)) (by omega_arith)

/-- The store of the mask keeps the Q space. -/
theorem mask_keepQ {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.S hMask 8 m m') :
    Outside L.Q 1600 (2 ^ 64 - 1600) m m' :=
  keepQ_of hL fun x hx => h x (Or.inr (by simp only [hMask, Lay.qOff, Lay.slot_eq] at hx ⊢; omega_arith))

theorem body_ok {s₀ s : State} {L : Lay} {key sig dig : Addr} {d : Nat}
    (hL : L.Ok) (hK : KeyOk s₀.mem L key) (hc : Checked s₀ s L key sig dig d)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + L.ql)) (hsg : Src s L sig (2 * L.ql))
    (hd : d < 2 ^ 16) (hdg : Src s L dig d) :
    WP isa Verify.body s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if ((0 < rOf s.mem L sig ∧ rOf s.mem L sig < qOf s₀.mem L key) ∧
          (0 < sOf s.mem L sig ∧ sOf s.mem L sig < qOf s₀.mem L key)) ∧
          vComp (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (yOf s₀.mem L key)
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig
              (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
            (rOf s.mem L sig) (sOf s.mem L sig) = rOf s.mem L sig then 1 else 0) ∧
        Kept L s.mem t.mem ∧ t.gpr .r21 = L.S ∧ ScrL t L) ∧ Keep bodyRegs s t := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hnw := hL.nowrap
  obtain ⟨ip, scr, regs, p0, ptop, p8, q0, qtop, r2⟩ := hc
  obtain ⟨ep, eq, eg, ey⟩ := key_kept hk hkp.out
  unfold KeyOk at hK
  obtain hqlt : qOf s₀.mem L key < 2 ^ (8 * L.ql) := by
    rw [← eq, qOf, ← VG.Proof.Bignum.pow256_eq]
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  generalize pOf s₀.mem L key = p at hK p0 p8 ⊢
  generalize hq : qOf s₀.mem L key = q at hK q0 r2 hqlt ⊢
  generalize hgg : gOf s₀.mem L key = g at hK ⊢
  generalize hyy : yOf s₀.mem L key = y at hK ⊢
  obtain B := VG.Proof.Dsa.supported_bounds hK.1.1
  have hqo : q % 2 = 1 := hK.1.2.1
  have hpo : p % 2 = 1 := hK.1.2.2
  obtain hqb : Spec.Dsa.bitLength q ≤ 256 := by have := hK.1.1; unfold Spec.Dsa.supportedSizes at this; omega_arith
  generalize hn : Spec.Dsa.bitLength q / 8 = n at r2 ⊢
  obtain hnq : n ≤ L.ql := by
    obtain hq0 : q ≠ 0 := by omega_arith
    obtain hlog : q.log2 < 8 * L.ql := (Nat.log2_lt hq0).mpr hqlt
    have : Spec.Dsa.bitLength q = q.log2 + 1 := by simp [Spec.Dsa.bitLength, hq0]
    omega_arith
  unfold Verify.body
  -- r and s in range.
  refine WP.seq (WP.mono (ranges_ok hL scr regs hsg) fun s₁ ⟨⟨Q₁, r5₁, m22, qa₁⟩, k₁⟩ => ?_)
  rw [q0] at m22
  obtain q0₁ : arrQ s₁.mem L 0 = q := qa₁.arr0.trans q0
  -- The mask to the header.
  obtain hst : InRegions s₁.wr (L.S + BitVec.ofNat 64 hMask) 8 := (scr.congr k₁.wr).st (by simp only [hMask]; omega_arith)
  obtain he : exec (.store .d .r22 .r21 hMask) s₁ =
      some { s₁ with mem := s₁.mem.writeW (L.S + BitVec.ofNat 64 hMask) (s₁.gpr .r22) } := by
    rw [exec_std (by decide) (by rw [Q₁.inq.h21]; exact hst), Q₁.inq.h21]
  refine WP.seq (WP.mono (WP.keep [] (Q := fun u => u.mem = s₁.mem.writeW (L.S + BitVec.ofNat 64 hMask)
      (s₁.gpr .r22)) (by unfold keepMask; prun [he]) (by decide)) fun s₂ ⟨m₂, k₂⟩ => ?_)
  rw [m22] at m₂
  obtain wo : Outside L.S hMask 8 s₁.mem s₂.mem := by
    rw [m₂]; exact writeW_outside s₁.mem L.S _ (by simp only [hMask]; omega_arith)
  obtain hm₂ : word s₂.mem L.S hMask =
      mask (decide ((0 < rOf s.mem L sig ∧ rOf s.mem L sig < q) ∧ (0 < sOf s.mem L sig ∧ sOf s.mem L sig < q))) := by
    rw [m₂]; exact word_writeW_self s₁.mem L.S hMask _
  obtain Km : Kept L s₁.mem s₂.mem := Kept.ofMask hL wo
  obtain Kr : Kept L s.mem s₁.mem := Kept.ofBody hL (qa₁.qbody.body hL)
  obtain K₂ := Kr.trans Km
  obtain Q₂ : QS s₂ L key sig dig := Q₁.step k₂ (by decide)
  obtain q0₂ : arrQ s₂.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 (mask_keepQ hL wo) (by decide) (by decide)]; exact q0₁
  obtain pw : ∀ j < 28, arrP s₂.mem L j = arrP s.mem L j := fun j hj =>
    (mask_arrP hL wo hj).trans (qa₁.qbuf.arrP hL hj)
  obtain k₁₂ := k₁.trans k₂
  -- `R² mod q`.
  refine WP.seq (WP.mono (rrQ_ok Q₂ (by rw [q0₂]; omega_arith) (by rw [q0₂]; exact hqo)) fun s₃ ⟨⟨Q₃, h8₃, qa₃, _, _⟩, k₃⟩ => ?_)
  rw [q0₂] at h8₃
  obtain q0₃ : arrQ s₃.mem L 0 = q := qa₃.arr0.trans q0₂
  -- `q − 2`.
  refine WP.seq (WP.mono (qMinus2_ok Q₃ hL (by rw [q0₃]; omega_arith) (by rw [q0₃]; exact hqlt))
    fun s₄ ⟨⟨Q₄, bq₄, a8₄, qb₄, _⟩, k₄⟩ => ?_)
  rw [q0₃] at bq₄
  obtain q0₄ : arrQ s₄.mem L 0 = q := qb₄.arr0.trans q0₃
  obtain k₁₄ := (k₁₂.trans k₃).trans k₄
  obtain B₂₄ : Body L s₂.mem s₄.mem := (qa₃.qbody.body hL).trans (qb₄.body hL)
  obtain K₄ := K₂.trans (Kept.ofBody hL B₂₄)
  -- `w = s^(q − 2) mod q`.
  refine WP.seq (WP.mono (inverse_ok Q₄ hL (hsg.keep k₁₄.rd k₁₄.wr) (by rw [q0₄]; omega_arith) (by rw [q0₄]; exact hqo)
      (by rw [a8₄, h8₃, q0₄])) fun s₅ ⟨⟨Q₅, w4₅, a8₅, qa₅⟩, k₅⟩ => ?_)
  rw [q0₄, bq₄, (sig_kept hsg hdg K₄.out (Nat.zero_le d)).2.1] at w4₅
  obtain q0₅ : arrQ s₅.mem L 0 = q := qa₅.arr0.trans q0₄
  obtain k₁₅ := k₁₄.trans k₅
  obtain B₂₅ := B₂₄.trans (qa₅.qbody.body hL)
  obtain K₅ := K₂.trans (Kept.ofBody hL B₂₅)
  -- `u1`, `u2`.
  refine WP.seq (WP.mono (products_ok Q₅ hL (hsg.keep k₁₅.rd k₁₅.wr) ((k₁₅.gpr .r2 (by decide)).trans r2)
      hnq hd ((hdg.keep k₁₅.rd k₁₅.wr).take (Nat.min_le_left d n))
      (by rw [q0₅]; omega_arith) (by rw [q0₅]; exact hqo) (by rw [q0₅]; exact hqlt)
      (by rw [a8₅, a8₄, h8₃, q0₅]) w4₅ (by rw [q0₅]; exact Nat.mod_lt _ (by omega_arith)))
    fun s₆ ⟨⟨Q₆, u1₆, u2₆, qb₆, a1₆⟩, k₆⟩ => ?_)
  rw [q0₅] at a1₆
  rw [q0₅, (sig_kept hsg hdg K₅.out (Nat.min_le_left d n)).2.2] at u1₆
  rw [q0₅, (sig_kept hsg hdg K₅.out (Nat.zero_le d)).1] at u2₆
  obtain k₁₆ := k₁₅.trans k₆
  obtain qb₂₆ : QBuf L s₂.mem s₆.mem := ((qa₃.qbuf.trans qb₄).trans qa₅.qbuf).trans qb₆
  obtain B₂₆ := B₂₅.trans (qb₆.body hL)
  obtain K₆ := K₂.trans (Kept.ofBody hL B₂₆)
  obtain ⟨ep₆, -, eg₆, ey₆⟩ := key_kept hk (hkp.trans K₆).out
  -- `g^u1 y^u2 mod p`.
  refine WP.seq (WP.mono (combine_ok hL Q₆.scr Q₆.regs (hk.keep k₁₆.rd k₁₆.wr)
      ((qb₂₆.arrP hL (by decide)).trans ((pw 0 (by decide)).trans p0)) (by omega_arith) hpo
      ((qb₂₆.arrP hL (by decide)).trans ((pw 24 (by decide)).trans p8)))
    fun s₇ ⟨⟨v₇, a4₇, ip₇, B₇, Qk₇⟩, k₇⟩ => ?_)
  rw [u1₆, u2₆, eg₆, ey₆, hgg, hyy] at v₇
  obtain k₁₇ := k₁₆.trans k₇
  obtain q0₇ : arrQ s₇.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 Qk₇ (by decide) (by decide)]; exact qb₂₆.arr0.trans q0₂
  obtain K₇ := K₆.trans (Kept.ofBody hL B₇)
  obtain hm₇ : word s₇.mem L.S hMask = mask (decide ((0 < rOf s.mem L sig ∧ rOf s.mem L sig < q) ∧
      (0 < sOf s.mem L sig ∧ sOf s.mem L sig < q))) := by
    rw [Outside.word (B₂₆.trans B₇) (Or.inl (by decide)) (by simp only [hMask]; omega_arith)]; exact hm₂
  -- The comparison.
  obtain q1₇ : arrQ s₇.mem L 1 = 2 ^ (128 * 4) % q := by
    rw [arrQ, arr, Outside.val32 Qk₇ (by decide) (by decide)]; exact a1₆
  refine WP.mono (compare_ok hL (scr.congr k₁₇.wr) (regs.keep k₁₇) (hsg.keep k₁₇.rd k₁₇.wr) ip₇
      (by rw [q0₇]; omega_arith) (by rw [q0₇]; exact hqo) (by rw [q1₇, q0₇]) a4₇
      hm₇) fun t ⟨⟨r3, Bt⟩, kt⟩ => ?_
  rw [q0₇, v₇, (sig_kept hsg hdg K₇.out (Nat.zero_le d)).1] at r3
  refine ⟨⟨?_, K₂.trans (Kept.ofBody hL ((B₂₆.trans B₇).trans Bt)), (kt.gpr .r21 (by decide)).trans ip₇.h21,
    scr.congr (k₁₇.trans kt).wr⟩, keep_but21 (k₁₇.trans kt) (by decide) (by decide)⟩
  rw [r3]
  refine congrArg (BitVec.ofNat 64) (ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl))
  unfold vComp
  rw [decide_eq_true_eq]
  exact and_comm

end VG.Proof.Dsa.PPC64LE
