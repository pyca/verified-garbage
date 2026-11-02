module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyInv
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubMont
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA verification on RISC-V: `u1` and `u2`

As on PPC64LE (`Proof/Dsa/PPC64LE/VerifyProd.lean`). `products_ok`: in the Q
space, with q in array 0, `-q⁻¹ mod 2⁶⁴` in `t1`, `R² mod q` in array 24 and
`w` in array 4: the digest's scalar `z` (its first `min(d, qb)` octets, its
address from the header's `hDigest`, the lengths from `hLens`) and r, then
`u1 = z w mod q` and `u2 = r w mod q` (Montgomery multiplications by w, then
by `R²`) to the buffer's first and second `q_len` octets.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Verify
open VG.Proof.Bignum (slot Arrays)

/-- The borrow of `a − b`, for `a` and `b` below `2^63`. -/
theorem sub_shr63 {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = BitVec.ofNat 64 (if a < b then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow] at *
  split <;> omega

/-- The registers `scalarLen` writes. -/
def scalarLenRegs : List Reg := [.s8, .t3, .a0]

/-- `scalarLen`: `s8 := min(d, qb)`, from the header's lengths. -/
theorem scalarLen_ok {s : State} {L : Lay} {qb d : Nat} (hs : ScrL s L) (hL : L.Ok) (h6 : s.gpr .s6 = L.S)
    (hlen : word s.mem L.S hLens = pack L.pl L.ql qb d) (h3 : qb < 2 ^ 16) (h4 : d < 2 ^ 16) :
    WP isa scalarLen s fun t =>
      (t.gpr .s8 = BitVec.ofNat 64 (min d qb) ∧ t.mem = s.mem) ∧ Keep scalarLenRegs s t := by
  have hp : L.pl < 2 ^ 16 := by rcases hL.pl with e | e | e <;> omega_arith
  have hq : L.ql < 2 ^ 16 := by rcases hL.ql with e | e | e <;> omega_arith
  unfold scalarLen
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (getQb_ok hs hL h6 .s8) fun u ⟨⟨a8, mu⟩, ku⟩ =>
    WP.mono (getD_ok (hs.congr ku.2.2) hL (by rw [ku.gpr (by decide)]; exact h6) .t3)
      fun v ⟨⟨b3, mv⟩, kv⟩ => ?_)))
  rw [hlen, pack_qb hp hq h3 h4] at a8
  rw [mu, hlen, pack_d hp hq h3 h4] at b3
  have a8' : v.gpr .s8 = BitVec.ofNat 64 qb := (kv.gpr (by decide)).trans a8
  have hsub := sub_shr63 (a := qb) (b := d) (by omega) (by omega)
  refine WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = BitVec.ofNat 64 (if qb < d then 1 else 0) ∧
      t.mem = v.mem) (by brun [a8', b3, exec_shift_d (show 63 < 64 by decide), hsub]) (by decide) (by rfl))
    fun w ⟨⟨c0, mw⟩, kw⟩ => ?_
  have kuvw := (ku.trans kv).trans kw
  have m : w.mem = s.mem := by rw [mw, mv, mu]
  refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by split <;> decide) c0) (fun hz => ?_) (fun hz => ?_)
  · have hz : ¬ qb < d := by have := of_decide_eq_true hz; split at this <;> simp_all
    refine WP.mono (WP.keep [.s8] (Q := fun t => t.gpr .s8 = BitVec.ofNat 64 (min d qb) ∧ t.mem = w.mem)
      (by brun [(kw.gpr (r := .t3) (by decide)).trans b3, BitVec.add_zero]; rw [Nat.min_eq_left (by omega)])
      (by decide) (by rfl)) fun t ⟨⟨t8, mt⟩, kt⟩ => ⟨⟨t8, by rw [mt, m]⟩, (kuvw.trans kt).mono (by decide)⟩
  · have hz : qb < d := by have := of_decide_eq_false hz; split at this <;> simp_all
    refine WP.block_nil ⟨⟨by rw [kw.gpr (by decide), a8', Nat.min_eq_right (by omega)], m⟩,
      kuvw.mono (by decide)⟩

/-- The registers `scalar` writes. -/
def scalarRegs : List Reg := scalarLenRegs ++ [.s7] ++ loadRegs ++ [.s0, .t3, .t5]

/-- `scalar`: the digest's (at the header's `hDigest`) first `min(d, qb)`
octets into array 6. -/
theorem scalar_ok {s : State} {L : Lay} {key sig dig : Addr} {qb d : Nat} (hL : L.Ok) (h : QS s L key sig)
    (hdg8 : word s.mem L.S hDigest = dig) (hlen : word s.mem L.S hLens = pack L.pl L.ql qb d)
    (hqb : qb ≤ L.ql) (hd : d < 2 ^ 16) (hdg : Src s L dig (min d qb)) :
    WP isa scalar s fun t =>
      (QS t L key sig ∧ arrQ t.mem L 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) ∧
        Outside L.Q (slot L.wq 6) (8 * (L.wq + 1)) s.mem t.mem) ∧ Keep scalarRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have hql : L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have e6 := Lay.slot_eq L.wq 6; have e7 := Lay.slot_eq L.wq 7; have e1 := Lay.slot_eq L.wq 1
  unfold scalar
  refine WP.seq (WP.mono (scalarLen_ok h.scr hL h.regs.s6 hlen (by omega) hd) fun s₀ ⟨⟨a8, m0⟩, k0⟩ => ?_)
  obtain ⟨hin, hal⟩ := ScrL.hdr (h.scr.congr k0.2.2) hL (d := 8) (by decide) (by decide)
  refine WP.seq (WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = dig ∧ u.mem = s₀.mem)
    (by brun [hDigest, (k0.gpr (r := .s6) (by decide)).trans h.regs.s6, hin, hal, m0]; exact hdg8)
    (by rfl) (by rfl))
    fun s₁ ⟨⟨a7, m1⟩, k1'⟩ => ?_)
  have a8 : s₁.gpr .s8 = BitVec.ofNat 64 (min d qb) := (k1'.gpr (by decide)).trans a8
  have k1 := k0.trans k1'
  have m1 : s₁.mem = s.mem := m1.trans m0
  have hdl : min d qb ≤ L.ql := Nat.le_trans (Nat.min_le_right _ _) hqb
  generalize min d qb = dl at a8 hdg hdl ⊢
  have Q1 := h.stepM k1 m1
  refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by omega) a8) (fun hz => ?_) (fun hz => ?_)
  · have hz : dl = 0 := of_decide_eq_true hz
    subst hz
    refine WP.mono (zeroArr_ok Q1.inq.env (j := 6) (by decide)) fun t ⟨⟨z6, ot⟩, kt⟩ => ?_
    refine ⟨⟨Q1.step kt (Body.ofQ hL ot (by omega)), ?_, ?_⟩, (k1.trans kt).mono (by decide)⟩
    · rw [arrQ, z6]; rfl
    · rw [← m1]; exact ot.mono (Nat.le_refl _) (by omega)
  · have hz : dl ≠ 0 := of_decide_eq_false hz
    refine WP.mono (loadQ_ok (j := 6) Q1 hL (by decide) (hdg.keep k1.2.1 k1.2.2) a7 a8 (by omega)
      (by omega)) fun t ⟨⟨Qt, v6, _, ot⟩, kt⟩ => ?_
    rw [m1] at v6 ot
    exact ⟨⟨Qt, v6, ot⟩, (k1.trans kt).mono (by decide)⟩

/-! ## Montgomery multiplications in the Q space -/

/-- An array that `Arrays` does not list keeps its value. -/
theorem arrays_val {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m') {j : Nat}
    (hj : j < 28) (hjs : ∀ k ∈ js, k ≠ j) (hn : B.toNat + slot w 28 ≤ 2 ^ 64) :
    wordsVal m' B (slot w j) w = wordsVal m B (slot w j) w :=
  wordsVal_congr fun i hi => h.word_eq (fun k hk => by
      have := VG.Proof.Bignum.slot_sep (w := w) (hjs k hk); omega)
    (by have := slot_lt (w := w) hj; omega)

theorem arrays_word0 {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    (hjs : ∀ k ∈ js, k ≠ 0) (hn : B.toNat + slot w 28 ≤ 2 ^ 64) :
    word m' B (slot w 0) = word m B (slot w 0) :=
  h.word_eq (fun k hk => by have := VG.Proof.Bignum.slot_sep (w := w) (hjs k hk); omega)
    (by have := slot_lt (w := w) (show 0 < 28 by decide); omega)

theorem arrays_qarr {L : Lay} {js : List Nat} {m m' : Mem} (h : Arrays L.Q L.wq js m m')
    (hjs : ∀ k ∈ js, 1 ≤ k ∧ k < 28) : QArr L m m' := fun x hx => h x fun k hk => by
  obtain ⟨a, b⟩ := hjs k hk
  have := slot_mono (w := L.wq) a
  have := slot_lt (w := L.wq) b
  have e1 := Lay.slot_eq L.wq 1; have e28 := Lay.slot_eq L.wq 28
  simp only [VG.Proof.Bignum.ofs, ofs] at hx ⊢
  omega

/-- `montOp o a b` in the Q space, for `o` among 5 and 6, `[b] < q`. -/
theorem qmont_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig) (hi : QInv s L)
    {o a b : Nat} (ho : o = 5 ∨ o = 6) (ha : a < 8) (ha2 : a ≠ 2) (hb : b < 8) (hb2 : b ≠ 2)
    (hB : arrQ s.mem L b < arrQ s.mem L 0) :
    WP isa (PublicChecked.montOp o a b) s fun t =>
      (QS t L key sig ∧ QInv t L ∧ arrQ t.mem L o < arrQ s.mem L 0 ∧
        arrQ t.mem L o * 2 ^ (64 * L.wq) % arrQ s.mem L 0 = arrQ s.mem L a * arrQ s.mem L b % arrQ s.mem L 0 ∧
        (∀ j < 28, j ≠ 2 → j ≠ 3 → j ≠ o → arrQ t.mem L j = arrQ s.mem L j) ∧ QArr L s.mem t.mem) ∧
        Keep Pub.montRegs s t := by
  have e := h.inq.env
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have h8 := slot_lt (w := L.wq) (show 8 < 28 by decide)
  have hn : L.Q.toNat + slot L.wq 28 ≤ 2 ^ 64 := by have := e.hs.nowrap; omega
  refine WP.mono (Pub.montOp_ok e.hs (by omega) ha hb (by omega) (by omega) ha2 hb2 e.w2 (by omega)
    (by omega) e.a7 e.s5 e.t0 hi hB) fun t ⟨⟨lt, eq, ar⟩, k⟩ => ?_
  have qa : QArr L s.mem t.mem := arrays_qarr ar (by
    intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega)
  refine ⟨⟨h.step k (qa.body hL), ?_, lt, eq, fun j hj h2 h3 ho' => arrays_val ar hj (by
    intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega) hn, qa⟩, k⟩
  show ((word t.mem L.Q (slot L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [arrays_word0 ar (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega) hn,
    k.gpr (by decide)]
  exact hi

/-- Two Montgomery multiplications, by `y` and by `R² mod q`: `x y mod q`. -/
theorem prod_mont_back {q R A B X Y : Nat} (hR : Nat.Coprime R q) (hB : B < q) (hA : A * R % q = X * Y % q)
    (hB' : B * R % q = A * (R * R % q) % q) : B = X * Y % q := by
  have e : B * R % q = X * Y * R % q := by
    rw [hB', Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, hA,
      Nat.mod_mul_mod]
  have := VG.Proof.Bignum.mont_cancel hR e
  rw [Nat.mod_eq_of_lt hB] at this
  exact this

/-- Octets below a frame's range keep their values. -/
theorem prod_bytes_keep {B : Addr} {o n k : Nat} {m m' : Mem} (h : Outside B o n m m') (hk : k ≤ o)
    (hk' : k < 2 ^ 64) : Spec.Rsa.bytesAt m' B k = Spec.Rsa.bytesAt m B k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inl ?_)
  have hi := List.mem_range.mp hi
  rw [show B + BitVec.ofNat 64 i = off B i from rfl, ofs_off0 B (by omega_arith)]
  omega_arith

/-- The registers `products` writes. -/
def prodRegs : List Reg :=
  scalarRegs ++ [.s7, .s8] ++ loadRegs ++ copyRegs ++ Pub.montRegs ++ [.s7, .t2, .s8] ++ storeRegs

/-- `products`: `u1 = z w mod q` and `u2 = r w mod q` to the buffer. -/
theorem products_ok {s : State} {L : Lay} {key sig dig : Addr} {qb d W : Nat} (hL : L.Ok) (h : QS s L key sig)
    (hi : QInv s L) (hsg : Src s L sig (2 * L.ql)) (hdg8 : word s.mem L.S hDigest = dig)
    (hlen : word s.mem L.S hLens = pack L.pl L.ql qb d) (hqb : qb ≤ L.ql) (hd : d < 2 ^ 16)
    (hdg : Src s L dig (min d qb))
    (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1) (hql : arrQ s.mem L 0 < 2 ^ (8 * L.ql))
    (h24 : arrQ s.mem L 24 = 2 ^ (128 * L.wq) % arrQ s.mem L 0) (h4 : arrQ s.mem L 4 = W)
    (hW : W < arrQ s.mem L 0) :
    WP isa products s fun t =>
      (QS t L key sig ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.ql) =
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) * W % arrQ s.mem L 0 ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off L.Buf L.ql) L.ql) = rOf s.mem L sig * W % arrQ s.mem L 0 ∧
        QBuf L s.mem t.mem) ∧ Keep prodRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have hql' : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hpl : 128 ≤ L.pl := by rcases hL.pl with e | e | e <;> omega
  have e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7
  have e24 := e 24; have e25 := e 25; have e28 := e 28
  have hcop : Nat.Coprime (2 ^ (64 * L.wq)) (arrQ s.mem L 0) := VG.Proof.Bignum.coprime_pow2 hqo _
  have hRR := pow_two_mul L.wq
  generalize hq : arrQ s.mem L 0 = q at hq2 hqo hql h24 hW hcop ⊢
  generalize (2 : Nat) ^ (128 * L.wq) = R2 at h24 hRR
  unfold products
  -- The digest's scalar into array 6, r into array 5, `R² mod q` into array 1.
  refine WP.seq (WP.mono (scalar_ok hL h hdg8 hlen hqb hd hdg) fun s₁ ⟨⟨Q1, v6, o1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (ptrR_ok Q1.scr hL Q1.regs) fun s₂ ⟨⟨a7, a8, m2⟩, k2⟩ => ?_)
  have Q2 := Q1.stepM k2 m2
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q2 hL (by decide)
      ((hsg.keep k12.2.1 k12.2.2).sub (o := 0) (k := L.ql) (by omega)) (by rw [a7, off, BitVec.add_zero]) a8
      (by omega) (by omega)) fun s₃ ⟨⟨Q3, v5, _, o3⟩, k3⟩ => ?_)
  rw [m2] at v5 o3
  refine WP.seq (WP.mono (copy_ok Q3.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨c1, o4⟩, k4⟩ => ?_)
  have Q4 := Q3.step k4 (Body.ofQ hL o4 (by omega))
  have k14 := (k12.trans k3).trans k4
  -- The values in array 0, 1, 4, 5 and 6 and the inverse.
  have A0 : arrQ s₄.mem L 0 = q := by
    rw [arrQ, o4.wordsVal (by omega) (by omega_arith), o3.wordsVal (by omega) (by omega_arith),
      o1.wordsVal (by omega) (by omega_arith)]; exact hq
  have A4 : arrQ s₄.mem L 4 = W := by
    rw [arrQ, o4.wordsVal (by omega) (by omega_arith), o3.wordsVal (by omega) (by omega_arith),
      o1.wordsVal (by omega) (by omega_arith)]; exact h4
  have A6 : arrQ s₄.mem L 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) := by
    rw [arrQ, o4.wordsVal (by omega) (by omega_arith), o3.wordsVal (by omega) (by omega_arith)]; exact v6
  have A5 : arrQ s₄.mem L 5 = rOf s.mem L sig := by
    rw [arrQ, o4.wordsVal (by omega) (by omega_arith)]
    refine v5.trans ?_
    rw [(hsg.sub (o := 0) (k := L.ql) (by omega)).bytes (Body.ofQ hL o1 (by omega)) (by have := hL.z256; omega)]
    simp only [rOf, off, BitVec.add_zero]
  have A1 : arrQ s₄.mem L 1 = R2 % q := by
    rw [arrQ, wordsVal_congr (m := s₃.mem) (d := slot L.wq 24) fun i hi => c1 i (by omega)]
    rw [← h24, o3.wordsVal (by omega) (by omega_arith), o1.wordsVal (by omega) (by omega_arith)]
  have I4 : QInv s₄ L := by
    show ((word s₄.mem L.Q (slot L.wq 0)).toNat * (s₄.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o4.word (by omega) (by omega_arith), o3.word (by omega) (by omega_arith),
      o1.word (by omega) (by omega_arith), k14.gpr (by decide)]
    exact hi
  -- u1.
  refine WP.seq (WP.mono (qmont_ok hL Q4 I4 (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [A4, A0]; exact hW)) fun s₅ ⟨⟨Q5, I5, _, e5, k5a, qa5⟩, k5⟩ => ?_)
  rw [A0, A6, A4] at e5
  have B0 := (k5a 0 (by decide) (by decide) (by decide) (by decide)).trans A0
  have B1 := (k5a 1 (by decide) (by decide) (by decide) (by decide)).trans A1
  have B4 := (k5a 4 (by decide) (by decide) (by decide) (by decide)).trans A4
  have B5 := (k5a 5 (by decide) (by decide) (by decide) (by decide)).trans A5
  refine WP.seq (WP.mono (qmont_ok hL Q5 I5 (o := 6) (a := 6) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [B1, B0]; exact Nat.mod_lt _ (by omega)))
    fun s₆ ⟨⟨Q6, I6, l6, e6', k6a, qa6⟩, k6⟩ => ?_)
  rw [B0] at l6
  rw [B0, B1] at e6'
  have u1 : arrQ s₆.mem L 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) * W % q :=
    prod_mont_back hcop l6 e5 (by rw [e6', hRR])
  have C0 := (k6a 0 (by decide) (by decide) (by decide) (by decide)).trans B0
  have C1 := (k6a 1 (by decide) (by decide) (by decide) (by decide)).trans B1
  have C4 := (k6a 4 (by decide) (by decide) (by decide) (by decide)).trans B4
  have C5 := (k6a 5 (by decide) (by decide) (by decide) (by decide)).trans B5
  -- u2.
  refine WP.seq (WP.mono (qmont_ok hL Q6 I6 (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [C4, C0]; exact hW)) fun s₇ ⟨⟨Q7, I7, _, e7', k7a, qa7⟩, k7⟩ => ?_)
  rw [C0, C5, C4] at e7'
  have D0 := (k7a 0 (by decide) (by decide) (by decide) (by decide)).trans C0
  have D1 := (k7a 1 (by decide) (by decide) (by decide) (by decide)).trans C1
  have D6 := (k7a 6 (by decide) (by decide) (by decide) (by decide)).trans u1
  refine WP.seq (WP.mono (qmont_ok hL Q7 I7 (o := 5) (a := 5) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [D1, D0]; exact Nat.mod_lt _ (by omega)))
    fun s₈ ⟨⟨Q8, _, l8, e8, k8a, qa8⟩, k8⟩ => ?_)
  rw [D0] at l8
  rw [D0, D1] at e8
  have u2 : arrQ s₈.mem L 5 = rOf s.mem L sig * W % q := prod_mont_back hcop l8 e7' (by rw [e8, hRR])
  have u1' := (k8a 6 (by decide) (by decide) (by decide) (by decide)).trans D6
  have k48 := ((k5.trans k6).trans k7).trans k8
  -- To the buffer.
  refine WP.seq (WP.mono (ptrBuf_ok Q8.scr hL Q8.regs) fun s₉ ⟨⟨b7, b8, m9⟩, k9⟩ => ?_)
  have e9 := Q8.inq.env.keep k9
  refine WP.seq (WP.mono (storeBE_ok (j := 6) (O := L.Buf) (k := L.ql) e9 (by decide)
    (by have := ScrL.bufSt (Q8.scr.congr k9.2.2) hL (o := 0) (k := L.ql) (by omega)
        simpa only [off, BitVec.add_zero] using this)
    (by have := buf_nowrap hL (o := 0) (k := L.ql) (by omega) (by omega); simpa only [off, BitVec.add_zero] using this)
    b7 b8 (by omega) (by omega) (m2_sep hL)) fun s₁₀ ⟨⟨vt, ot⟩, k10⟩ => ?_)
  rw [m9] at vt ot
  have qb10 : QBuf L s₈.mem s₁₀.mem := QBuf.ofBuf hL ot (by omega)
  have Q10 := Q8.step (k9.trans k10) (qb10.body hL)
  refine WP.seq (WP.mono (ptrBuf2_ok Q10.scr hL Q10.regs) fun s₁₁ ⟨⟨f7, f8, m11⟩, k11⟩ => ?_)
  have e11 := e9.keep (k10.trans k11)
  have hso : ∀ x, ofs (off L.Buf L.ql) x < L.ql → 1600 ≤ ofs L.Q x := by
    rw [buf_eq, off_off]
    exact sepQ_from L (by omega) (by have := hL.buf_end; have := hL.nowrap; simp only [Lay.bOff] at *; omega)
  refine WP.mono (storeBE_ok (j := 5) (O := off L.Buf L.ql) (k := L.ql) e11 (by decide)
    (ScrL.bufSt (Q10.scr.congr k11.2.2) hL (o := L.ql) (k := L.ql) (by omega))
    (buf_nowrap hL (o := L.ql) (k := L.ql) (by omega) (by omega)) f7 f8 (by omega) (by omega) hso)
    fun t ⟨⟨vt2, ot2⟩, kt⟩ => ?_
  rw [m11] at vt2 ot2
  have ot2b : Outside L.Buf (L.ql + 0) L.ql s₁₀.mem t.mem :=
    outside_shift ot2 (by have := hL.buf_end; have := hL.nowrap; simp only [Lay.bOff] at *; omega) (by omega)
  have qbt : QBuf L s₁₀.mem t.mem := QBuf.ofBuf hL (n := 2 * L.ql) (ot2b.mono (Nat.zero_le _) (by omega))
    (by omega)
  have ot' : Outside (off L.Q 1600) 0 L.ql s₈.mem s₁₀.mem := by rw [← buf_eq]; exact ot
  have otq := outside_shift ot' (by have := hL.buf_end; have := hL.nowrap; simp only [Lay.bOff] at *; omega)
    (by decide)
  have u2' : arrQ s₁₀.mem L 5 = rOf s.mem L sig * W % q := by
    rw [arrQ, otq.wordsVal (Or.inl (by omega)) (by omega_arith)]; exact u2
  have qa18 : QArr L s.mem s₈.mem := by
    have qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by omega) (by omega)
    have qa3 : QArr L s₁.mem s₃.mem := QArr.of o3 (by omega) (by omega)
    have qa4 : QArr L s₃.mem s₄.mem := QArr.of o4 (by omega) (by omega)
    exact ((((((qa1.trans qa3).trans qa4).trans qa5).trans qa6).trans qa7).trans qa8)
  have kall := (((k14.trans k48).trans (k9.trans k10)).trans k11).trans kt
  refine ⟨⟨Q10.step (k11.trans kt) (qbt.body hL), ?_, ?_, (qa18.qbuf hL).trans (qb10.trans qbt)⟩,
    kall.mono (by decide)⟩
  · rw [prod_bytes_keep ot2b (by omega) (by omega)]
    refine (vt.trans (read_low _ _ (w := L.wq) (by omega) ?_)).trans u1'
    show arrQ s₈.mem L 6 < _
    rw [u1']
    exact Nat.lt_trans (Nat.mod_lt _ (by omega)) hql
  · refine (vt2.trans (read_low _ _ (w := L.wq) (by omega) ?_)).trans u2'
    show arrQ s₁₀.mem L 5 < _
    rw [u2']
    exact Nat.lt_trans (Nat.mod_lt _ (by omega)) hql

end VG.Proof.Dsa.RISCV64
