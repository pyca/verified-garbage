module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.KeyPair
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Add
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyProd
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRounds
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA signing on PPC64LE: `s = w (z + x r) mod q`

* `mont28_ok`: `PubMont.lean`'s `montOpN_ok` for any of the 28 arrays a
  working space of `slot w 28` octets holds, as `sValue` multiplies by r in
  array 9;
* `sValue_ok`: in the Q space, with q in array 0, w in array 4, `R² mod q` in
  array 8 and r in array 9, `w (z + x r) mod q` into array 6 (z the digest's
  scalar, x the key's last `q_len` octets).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot slot_sep hdr_lt_slot)

/-! ## Montgomery multiplications of any array -/

/-- `montOp o a b` for `o` among 5 and 6 and any arrays `a` and `b`, `[b] < c`. -/
theorem mont28_ok {s : State} {B : Addr} {Z w : Nat} (h : MCtx s B Z w) {o a b : Nat}
    (ho : o = 5 ∨ o = 6) (ha : a < 28) (ha2 : a ≠ 2) (hb : b < 28) (hb2 : b ≠ 2)
    (hB : arr s.mem B w b < arr s.mem B w 0) :
    WP isa (PublicChecked.montOp o a b) s fun t =>
      (arr t.mem B w o < arr s.mem B w 0 ∧
        arr t.mem B w o * 2 ^ (64 * w) % arr s.mem B w 0 = arr s.mem B w a * arr s.mem B w b % arr s.mem B w 0 ∧
        Outs B (montRanges w o) s.mem t.mem ∧ w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0)) ∧
      Keep Pub.montRegs s t := by
  have hw := h.hw
  have hw' := h.hw'
  have h8 := slot_lt (w := w) (show 8 < 28 by decide)
  refine WP.mono (Pub.montOpN_ok h.hs (n := 28) (by decide) (by omega) ha hb (by omega) (by omega) ha2 hb2
    (by omega_arith) (by omega_arith) h.hZ h.h10 h.h29 h.h11 h.h12 h.inv hB) fun t ⟨⟨hlt, heq, hout⟩, k⟩ =>
    ⟨⟨hlt, heq, hout, ?_⟩, k⟩
  refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => hout _ fun r hr => ?_)
  have := h.hs.nowrap
  have h0 := slot_lt (w := w) (show 0 < 28 by decide)
  have hZ := h.hZ
  rw [ofs_off B (by omega_arith)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> omega_arith

/-! ## The arrays a step keeps -/

/-- The Q space's arrays but those in `ws` are kept. -/
def AKeep (L : Lay) (ws : List Nat) (m m' : Mem) : Prop :=
  ∀ j, j < 28 → j ∉ ws → arrQ m' L j = arrQ m L j

theorem AKeep.get {L : Lay} {ws : List Nat} {m m' : Mem} (h : AKeep L ws m m') (j : Nat)
    (hj : j < 28 := by decide) (hn : j ∉ ws := by decide) : arr m' L.Q 4 j = arr m L.Q 4 j :=
  h j hj hn

theorem AKeep.trans {L : Lay} {ws ws' : List Nat} {m₁ m₂ m₃ : Mem} (h₁ : AKeep L ws m₁ m₂)
    (h₂ : AKeep L ws' m₂ m₃) : AKeep L (ws ++ ws') m₁ m₃ := fun j hj hn =>
  (h₂ j hj fun h => hn (List.mem_append_right _ h)).trans (h₁ j hj fun h => hn (List.mem_append_left _ h))

theorem AKeep.of_eq {L : Lay} {m m' : Mem} (h : m' = m) : AKeep L [] m m' := fun _ _ _ => by rw [h]

theorem AKeep.one {L : Lay} {o n : Nat} {m m' : Mem} (h : Outside L.Q (slot 4 o) n m m') (hn : n ≤ 48) :
    AKeep L [o] m m' := fun j hj ho =>
  Outside.arrEq (h.mono (Nat.le_refl _) (by omega_arith)) hj (by simpa only [List.mem_singleton] using ho) (by decide)

theorem AKeep.red {L : Lay} {m m' : Mem} (h : Outside L.Q (slot 4 1) (24 * (4 + 2)) m m') :
    AKeep L [1, 2, 3] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  exact Outside.val32 h (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)

theorem AKeep.add {L : Lay} {o : Nat} {m m' : Mem} (h : AddFrame L.Q 4 o m m') (hnw : L.Q.toNat + 1600 ≤ 2 ^ 64)
    (ho : o < 28) : AKeep L [2, 3, o] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  exact h.arr_eq (Z := 1600) (by decide) hnw hj hn.1 hn.2.1 hn.2.2 ho

theorem AKeep.mont {L : Lay} {o : Nat} {m m' : Mem} (h : Outs L.Q (montRanges 4 o) m m') :
    AKeep L [2, 3, o] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  exact Outs.arrEq_mont h hj hn.1 hn.2.1 hn.2.2 (by decide)

theorem AddFrame.qarr {L : Lay} {o : Nat} {m m' : Mem} (h : AddFrame L.Q 4 o m m') (ho1 : 1 ≤ o) (ho : o < 28) :
    QArr L m m' := by
  obtain ⟨m₁, h₁, h₂⟩ := h
  exact (QArr.of h₁ (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)).trans
    (QArr.of h₂ (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith))

/-! ## s -/

/-- The registers `sValue` writes. -/
def sValueRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24, .r25,
    .r30]

/-- `sValueRegs`, and `r10` and `r31`, which `sValue` restores. -/
def sValueAll : List Reg := .r10 :: .r31 :: sValueRegs

/-- `sValue`: in the Q space, `w (z + x r) mod q` into array 6. -/
theorem sValue_ok {s : State} {L : Lay} {key nonce dig : Addr} {qb d : Nat} (h : QS s L key nonce dig)
    (hL : L.Ok) (h2 : s.gpr .r2 = pack L.pl L.ql qb d) (hqb : qb ≤ L.ql) (hd : d < 2 ^ 16)
    (hdg : Src s L dig (min d qb)) (hk : Src s L key (3 * L.pl + 2 * L.ql))
    (hq3 : 3 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h8 : arrQ s.mem L 8 = 2 ^ (128 * 4) % arrQ s.mem L 0)
    (h4 : arrQ s.mem L 4 < arrQ s.mem L 0) (h9 : arrQ s.mem L 9 < arrQ s.mem L 0)
    (hz : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) < 2 * arrQ s.mem L 0) :
    WP isa sValue s fun t =>
      (QS t L key nonce dig ∧
        arrQ t.mem L 6 = arrQ s.mem L 4 * ((Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) %
          arrQ s.mem L 0 + xOf s.mem L key * arrQ s.mem L 9 % arrQ s.mem L 0) % arrQ s.mem L 0) %
            arrQ s.mem L 0 ∧
        arrQ t.mem L 9 = arrQ s.mem L 9 ∧ QArr L s.mem t.mem) ∧ Keep sValueRegs s t := by
  have hql := hL.ql
  have hcop : Nat.Coprime (2 ^ (64 * 4)) (arrQ s.mem L 0) := VG.Proof.Bignum.coprime_pow2 hqo _
  have hRR := pow_sq_eq 4
  generalize (2 : Nat) ^ (128 * 4) = R2 at h8 hRR
  have hnw : L.Q.toNat + 1600 ≤ 2 ^ 64 := h.inq.env.hs.nowrap
  unfold sValue
  -- z into array 6, 0 into array 7, `z mod q` into array 6.
  refine WP.seq (WP.mono (prod_scalar_ok h hL h2 hqb hd hdg) fun s₁ ⟨⟨Q1, v6, o1⟩, k1⟩ => ?_)
  generalize Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) = z at v6 hz ⊢
  have f1 : AKeep L [6] s.mem s₁.mem := AKeep.one o1 (by omega_arith)
  have qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)
  refine WP.seq (WP.mono (zeroArr_ok Q1.inq.env (j := 7) (by decide)) fun s₂ ⟨⟨z7, o2⟩, k2⟩ => ?_)
  have Q2 := Q1.step k2 (by decide)
  have f2 : AKeep L [7] s₁.mem s₂.mem := AKeep.one o2 (by omega_arith)
  have qa2 : QArr L s₁.mem s₂.mem := QArr.of o2 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)
  have q2 : arr s₂.mem L.Q 4 0 = arrQ s.mem L 0 := (qa1.trans qa2).arr0
  have z2 : arr s₂.mem L.Q 4 6 = z := (f2.get 6).trans v6
  refine WP.seq (WP.mono (addMod_ok Q2.inq.env (o := 6) (a := 6) (b := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [z2, z7, q2]; omega_arith)) fun s₃ ⟨⟨a6, fr3⟩, k3⟩ => ?_)
  rw [z2, z7, q2, Nat.add_zero] at a6
  have Q3 := Q2.step k3 (by decide)
  have f3 := AKeep.add fr3 hnw (by decide)
  have qa13 : QArr L s.mem s₃.mem := (qa1.trans qa2).trans (AddFrame.qarr fr3 (by decide) (by decide))
  have q3 : arr s₃.mem L.Q 4 0 = arrQ s.mem L 0 := qa13.arr0
  have k13 := (k1.trans k2).trans k3
  -- x's octets, and `x mod q` into array 1.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (ptrX_ok Q3.regs) fun s₄ ⟨⟨b12, b6, m4⟩, k4⟩ => ?_
  refine WP.mono (WP.keep [.r30, .r31] (Q := fun u => u.gpr .r30 = off key (3 * L.pl + L.ql) ∧
      u.gpr .r31 = BitVec.ofNat 64 L.ql ∧ u.mem = s₄.mem) (by prun [b12, b6, BitVec.add_zero]) (by decide))
    fun s₅ ⟨⟨c30, c31, m5⟩, k5⟩ => ?_
  have k35 := k4.trans k5
  have e3 := Q3.inq.env
  have hx := (hk.keep (k13.trans k35).rd (k13.trans k35).wr).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_arith)
  refine WP.seq (WP.mono (ModArith.reduce_ok (B := L.Q) (Z := 1600) (w := 4) (D := off key (3 * L.pl + L.ql))
    (L := L.ql) (e3.hs.congr k35.wr) (by decide) (by decide) (by decide)
    ((k35.gpr .r10 (by decide)).trans e3.h10) ((k35.gpr .r29 (by decide)).trans e3.h29)
    ((k35.gpr .r11 (by decide)).trans e3.h11)
    (by rw [m5, m4]; show 0 < arr s₃.mem L.Q 4 0; rw [q3]; omega_arith)
    (by rw [c30]; exact (BitVec.add_zero _).symm) c31 (by omega_arith) (by omega_arith) hx.rd (hx.sepQ hL))
    fun s₆ ⟨⟨v1, o6⟩, k6⟩ => ?_)
  have x6 : arr s₆.mem L.Q 4 1 = xOf s.mem L key % arrQ s.mem L 0 := by
    refine v1.trans ?_
    rw [m5, m4, (hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_arith)).bytes (qa13.qbody.body hL) hL.z256]
    show _ % arr s₃.mem L.Q 4 0 = _
    rw [q3]
    rfl
  have f6 := AKeep.red o6
  have qa6 : QArr L s₅.mem s₆.mem := QArr.of o6 (Nat.le_refl _) (by simp only [slot_eq]; omega_arith)
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun u => u.gpr .r31 = L.Q ∧ u.mem = s₆.mem)
      (by prun [((k35.trans k6).gpr .r23 (by decide)).trans Q3.inq.h23, BitVec.add_zero]) (by decide))
    fun s₇ ⟨⟨a31, m7⟩, k7⟩ => ?_)
  have k37 := (k35.trans k6).trans k7
  have Q7 : QS s₇ L key nonce dig := ⟨⟨⟨e3.hs.congr k37.wr, (k37.gpr .r10 (by decide)).trans e3.h10,
    (k37.gpr .r29 (by decide)).trans e3.h29, (k37.gpr .r11 (by decide)).trans e3.h11, a31, e3.hw, e3.hw', e3.hZ⟩,
    (k37.gpr .r21 (by decide)).trans Q3.inq.h21, (k37.gpr .r23 (by decide)).trans Q3.inq.h23⟩,
    Q3.scr.congr k37.wr, Q3.regs.keep k37⟩
  -- `x mod q` into array 5, `R² mod q` into array 1, `-q⁻¹`.
  refine WP.seq (WP.mono (copy_ok Q7.inq.env (o := 5) (a := 1) (by decide) (by decide) (by decide))
    fun s₈ ⟨⟨v5, o8⟩, k8⟩ => ?_)
  rw [m7, x6] at v5
  have Q8 := Q7.step k8 (by decide)
  have f8 : AKeep L [5] s₇.mem s₈.mem := AKeep.one o8 (by omega_arith)
  refine WP.seq (WP.mono (copy_ok Q8.inq.env (o := 1) (a := 8) (by decide) (by decide) (by decide))
    fun s₉ ⟨⟨v1', o9⟩, k9⟩ => ?_)
  have Q9 := Q8.step k9 (by decide)
  have f9 : AKeep L [1] s₈.mem s₉.mem := AKeep.one o9 (by omega_arith)
  have F38 := ((AKeep.of_eq (L := L) (m5.trans m4)).trans f6).trans ((AKeep.of_eq m7).trans f8)
  have F08 := ((f1.trans f2).trans f3).trans F38
  have qa35 : QArr L s₃.mem s₅.mem := by rw [m5, m4]; exact QArr.refl _ _
  have qa68 : QArr L s₆.mem s₈.mem := by
    rw [← m7]; exact QArr.of o8 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)
  have qa9 : QArr L s.mem s₉.mem := (((qa13.trans qa35).trans qa6).trans qa68).trans
    (QArr.of o9 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith))
  have q9 : arr s₉.mem L.Q 4 0 = arrQ s.mem L 0 := qa9.arr0
  have hodd : (word s₉.mem L.Q (slot 4 0)).toNat % 2 = 1 :=
    word_odd _ _ _ (2 * 4) (by decide) (by show arr s₉.mem L.Q 4 0 % 2 = 1; rw [q9]; exact hqo)
  refine WP.seq (WP.mono (Pub.minv_ok Q9.inq.env.hs Q9.inq.env.h10 (by decide) hodd)
    fun s₁₀ ⟨⟨i12, inv, m10⟩, k10⟩ => ?_)
  have M10 : MCtx s₁₀ L.Q 1600 4 := ⟨Q9.inq.env.keep k10 (by decide), i12, by rw [m10]; exact inv⟩
  have Q10 := Q9.step k10 (by decide)
  have F010 := (F08.trans f9).trans (AKeep.of_eq (L := L) m10)
  have A0 : arr s₁₀.mem L.Q 4 0 = arrQ s.mem L 0 := by rw [m10]; exact q9
  have A1 : arr s₁₀.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := by rw [m10, v1', F08.get 8]; exact h8
  have A4 : arr s₁₀.mem L.Q 4 4 = arrQ s.mem L 4 := F010.get 4
  have A5 : arr s₁₀.mem L.Q 4 5 = xOf s.mem L key % arrQ s.mem L 0 := by rw [m10, f9.get 5]; exact v5
  have A6 : arr s₁₀.mem L.Q 4 6 = z % arrQ s.mem L 0 :=
    ((F38.trans f9).trans (AKeep.of_eq (L := L) m10)).get 6 |>.trans a6
  have A9 : arr s₁₀.mem L.Q 4 9 = arrQ s.mem L 9 := F010.get 9
  -- `x r mod q` into array 5.
  refine WP.seq (WP.mono (mont28_ok M10 (o := 5) (a := 5) (b := 9) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [A9, A0]; exact h9)) fun s₁₁ ⟨⟨_, e11, o11, w11⟩, k11⟩ => ?_)
  have M11 := M10.keep k11 (by decide) w11
  have Q11 := Q10.step k11 (by decide)
  rw [A0, A5, A9] at e11
  have f11 := AKeep.mont o11
  have B0 : arr s₁₁.mem L.Q 4 0 = arrQ s.mem L 0 := (f11.get 0).trans A0
  have B1 : arr s₁₁.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := (f11.get 1).trans A1
  refine WP.seq (WP.mono (mont28_ok M11 (o := 5) (a := 5) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [B1, B0]; exact Nat.mod_lt _ (by omega_arith))) fun s₁₂ ⟨⟨l12, e12, o12, w12⟩, k12⟩ => ?_)
  have M12 := M11.keep k12 (by decide) w12
  have Q12 := Q11.step k12 (by decide)
  rw [B0] at l12
  rw [B0, B1] at e12
  have X12 : arr s₁₂.mem L.Q 4 5 = xOf s.mem L key % arrQ s.mem L 0 * arrQ s.mem L 9 % arrQ s.mem L 0 :=
    prod_mont_back hcop l12 e11 (by rw [e12, hRR])
  have f12 := AKeep.mont o12
  have F1012 := f11.trans f12
  have C0 : arr s₁₂.mem L.Q 4 0 = arrQ s.mem L 0 := (F1012.get 0).trans A0
  have C6 : arr s₁₂.mem L.Q 4 6 = z % arrQ s.mem L 0 := (F1012.get 6).trans A6
  -- `z + x r mod q` into array 6.
  have l1 := Nat.mod_lt z (show 0 < arrQ s.mem L 0 by omega_arith)
  have l2 := Nat.mod_lt (xOf s.mem L key % arrQ s.mem L 0 * arrQ s.mem L 9) (show 0 < arrQ s.mem L 0 by omega_arith)
  refine WP.seq (WP.mono (addMod_ok M12.toEnv (o := 6) (a := 6) (b := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [C6, X12, C0]; omega_arith)) fun s₁₃ ⟨⟨a13, fr13⟩, k13'⟩ => ?_)
  rw [C6, X12, C0, Nat.mod_mul_mod] at a13
  have qa13' := AddFrame.qarr fr13 (by decide) (by decide)
  have M13 := M12.keep k13' (by decide)
    (Outside.w32 qa13' (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith))
  have Q13 := Q12.step k13' (by decide)
  have f13 := AKeep.add fr13 hnw (by decide)
  have F1013 := F1012.trans f13
  have D0 : arr s₁₃.mem L.Q 4 0 = arrQ s.mem L 0 := (F1013.get 0).trans A0
  have D1 : arr s₁₃.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := (F1013.get 1).trans A1
  have D4 : arr s₁₃.mem L.Q 4 4 = arrQ s.mem L 4 := (F1013.get 4).trans A4
  -- `w (z + x r) mod q` into array 6.
  refine WP.seq (WP.mono (mont28_ok M13 (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [D4, D0]; exact h4)) fun s₁₄ ⟨⟨_, e14, o14, w14⟩, k14⟩ => ?_)
  have M14 := M13.keep k14 (by decide) w14
  have Q14 := Q13.step k14 (by decide)
  rw [D0, a13, D4] at e14
  have f14 := AKeep.mont o14
  have E0 : arr s₁₄.mem L.Q 4 0 = arrQ s.mem L 0 := (f14.get 0).trans D0
  have E1 : arr s₁₄.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := (f14.get 1).trans D1
  refine WP.mono (mont28_ok M14 (o := 6) (a := 6) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [E1, E0]; exact Nat.mod_lt _ (by omega_arith))) fun t ⟨⟨lt, et, ot, _⟩, kt⟩ => ?_
  rw [E0] at lt
  rw [E0, E1] at et
  have ft := AKeep.mont ot
  have Ft := (((F010.trans F1013).trans f14).trans ft)
  have qat : QArr L s.mem t.mem := (((qa9.trans (by rw [m10]; exact QArr.refl _ _)).trans
    (prod_qarr o11 (by decide))).trans ((prod_qarr o12 (by decide)).trans qa13')).trans
    ((prod_qarr o14 (by decide)).trans (prod_qarr ot (by decide)))
  have Qt := Q14.step kt (by decide)
  have kw : Keep sValueAll s t :=
    (((((((((((((k1.mono (rs' := sValueAll)).trans' (k2.mono)).trans' (k3.mono)).trans' (k4.mono)).trans'
      (k5.mono)).trans' (k6.mono)).trans' (k7.mono)).trans' (k8.mono)).trans' (k9.mono)).trans'
      (k10.mono)).trans' (k11.mono)).trans' (k12.mono)).trans' (k13'.mono)).trans' ((k14.mono).trans' (kt.mono))
  refine ⟨⟨Qt, ?_, Ft.get 9, qat⟩, ⟨fun r hr => ?_, kw.rd, kw.wr, kw.sp, kw.lr⟩⟩
  · exact (prod_mont_back hcop lt e14 (by rw [et, hRR])).trans (by rw [Nat.mul_comm _ (arrQ s.mem L 4)])
  · by_cases e10 : r = .r10
    · subst e10; rw [Qt.inq.env.h10, h.inq.env.h10]
    by_cases e31 : r = .r31
    · subst e31; rw [Qt.inq.env.h31, h.inq.env.h31]
    exact kw.gpr r fun h' => (List.mem_cons.mp h').elim e10 fun h' => (List.mem_cons.mp h').elim e31 hr

end VG.Proof.Dsa.PPC64LE
