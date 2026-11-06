module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignAdd
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignKeyPair
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyInv
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMont
import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA signing on RISC-V: `s = w (z + x r) mod q`

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/S.lean`).

* `qmont28_ok`: verification's `qmont_ok` for any of the 28 arrays, as
  `sValue` multiplies by r in array 25;
* `sValue_ok`: in the Q space, with q in array 0, w in array 4, `R² mod q` in
  array 24 and r in array 25, `w (z + x r) mod q` into array 6 (z the digest's
  scalar, x the key's last `q_len` octets).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Sign
open VG.Proof.Bignum (slot)

/-- `montOp o a b` in the Q space, for `o` among 5 and 6 and any arrays `a`
and `b`, `[b] < q`. -/
theorem qmont28_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig) (hi : QInv s L)
    {o a b : Nat} (ho : o = 5 ∨ o = 6) (ha : a < 28) (ha2 : a ≠ 2) (hb : b < 28) (hb2 : b ≠ 2)
    (hB : arrQ s.mem L b < arrQ s.mem L 0) :
    WP isa (PublicChecked.montOp o a b) s fun t =>
      (QS t L key sig ∧ QInv t L ∧ arrQ t.mem L o < arrQ s.mem L 0 ∧
        arrQ t.mem L o * 2 ^ (64 * L.wq) % arrQ s.mem L 0 = arrQ s.mem L a * arrQ s.mem L b % arrQ s.mem L 0 ∧
        (∀ j < 28, j ≠ 2 → j ≠ 3 → j ≠ o → arrQ t.mem L j = arrQ s.mem L j) ∧ QArr L s.mem t.mem) ∧
        Keep Pub.montRegs s t := by
  have e := h.inq.env
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have hn : L.Q.toNat + slot L.wq 28 ≤ 2 ^ 64 := by have := e.hs.nowrap; omega
  refine WP.mono (Pub.montOpN_ok e.hs (n := 28) (by decide) (by omega) ha hb (by omega) (by omega) ha2 hb2 e.w2
    (by omega) e.hZ e.a7 e.s5 e.t0 hi hB) fun t ⟨⟨lt, eq, ar⟩, k⟩ => ?_
  have qa : QArr L s.mem t.mem := arrays_qarr ar (by
    intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega)
  refine ⟨⟨h.step k (qa.body hL), ?_, lt, eq, fun j hj h2 h3 ho' => arrays_val ar hj (by
    intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega) hn, qa⟩, k⟩
  show ((word t.mem L.Q (slot L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [arrays_word0 ar (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega) hn,
    k.gpr (by decide)]
  exact hi

/-! ## The arrays a step keeps -/

/-- The Q space's arrays but those in `ws` are kept. -/
def AKeep (L : Lay) (ws : List Nat) (m m' : Mem) : Prop :=
  ∀ j, j < 28 → j ∉ ws → arrQ m' L j = arrQ m L j

theorem AKeep.get {L : Lay} {ws : List Nat} {m m' : Mem} (h : AKeep L ws m m') (j : Nat)
    (hj : j < 28 := by decide) (hn : j ∉ ws := by decide) : arrQ m' L j = arrQ m L j :=
  h j hj hn

theorem AKeep.trans {L : Lay} {ws ws' : List Nat} {m₁ m₂ m₃ : Mem} (h₁ : AKeep L ws m₁ m₂)
    (h₂ : AKeep L ws' m₂ m₃) : AKeep L (ws ++ ws') m₁ m₃ := fun j hj hn =>
  (h₂ j hj fun h => hn (List.mem_append_right _ h)).trans (h₁ j hj fun h => hn (List.mem_append_left _ h))

theorem AKeep.one {L : Lay} (hL : L.Ok) {o n : Nat} {m m' : Mem} (h : Outside L.Q (slot L.wq o) n m m')
    (hn : n ≤ 8 * (L.wq + 2)) : AKeep L [o] m m' := fun j hj ho => by
  have hjo : j ≠ o := by simpa only [List.mem_singleton] using ho
  have := slot_sep' (w := L.wq) hjo
  have := slot_lt (w := L.wq) hj
  have := hL.wq_ge
  exact h.wordsVal (by omega) (by simp only [Lay.slot_eq] at *; omega)

theorem AKeep.red {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.Q (slot L.wq 1) (24 * (L.wq + 2)) m m') :
    AKeep L [1, 2, 3] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  have hl := slot_lt (w := L.wq) hj
  have := hL.wq_ge
  have e0 := Lay.slot_eq L.wq 0; have e1 := Lay.slot_eq L.wq 1; have e4 := Lay.slot_eq L.wq 4
  have e28 := Lay.slot_eq L.wq 28
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact h.wordsVal (Or.inl (by omega)) (by omega)
  · have := slot_mono (w := L.wq) (show 4 ≤ j by omega)
    exact h.wordsVal (Or.inr (by omega)) (by omega)

theorem AKeep.add {L : Lay} (hL : L.Ok) {o : Nat} {m m' : Mem} (h : AddFrame L.Q L.wq o m m')
    (hnw : L.Q.toNat + 1600 ≤ 2 ^ 64) : AKeep L [2, 3, o] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  exact h.arr_eq (Z := 1600) hL.qslot hnw hj hn.1 hn.2.1 hn.2.2

theorem AKeep.mont {L : Lay} {o : Nat} {m m' : Mem}
    (h : ∀ j < 28, j ≠ 2 → j ≠ 3 → j ≠ o → arrQ m' L j = arrQ m L j) : AKeep L [2, 3, o] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  exact h j hj hn.1 hn.2.1 hn.2.2

theorem AddFrame.qarr {L : Lay} {o : Nat} {m m' : Mem} (h : AddFrame L.Q L.wq o m m') (ho1 : 1 ≤ o)
    (ho : o < 28) : QArr L m m' := by
  obtain ⟨m₁, h₁, h₂⟩ := h
  have h1 := slot_mono (w := L.wq) ho1
  have h2 := slot_lt (w := L.wq) ho
  exact (QArr.of h₁ (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega)).trans
    (QArr.of h₂ h1 (by omega))

theorem QArr.word0 {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QArr L m m') :
    word m' L.Q (slot L.wq 0) = word m L.Q (slot L.wq 0) := by
  have := hL.wq_ge
  exact h.word (Or.inl (by simp only [Lay.slot_eq]; omega)) (by simp only [Lay.slot_eq]; omega)

theorem QInv.keepW {s t : State} {L : Lay} (hi : QInv s L) (hw : word t.mem L.Q (slot L.wq 0) = word s.mem L.Q (slot L.wq 0))
    (h1 : t.gpr .t1 = s.gpr .t1) : QInv t L := by
  show ((word t.mem L.Q (slot L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [hw, h1]; exact hi

/-! ## s -/

/-- The registers `sValue` writes. -/
def sValueRegs : List Reg :=
  scalarRegs ++ [.s0, .t3, .t5] ++ addModRegs ++ ptrRegs ++ [.s9, .s10] ++
    (ModArith.redRegs ++ [.a2, .a5, .a6]) ++ copyRegs ++ copyRegs ++ Pub.montRegs ++ Pub.montRegs ++ addModRegs ++
    Pub.montRegs ++ Pub.montRegs

/-- `sValue`: in the Q space, `w (z + x r) mod q` into array 6. -/
theorem sValue_ok {s : State} {L : Lay} {key nonce dig : Addr} {qb d : Nat} (hL : L.Ok) (h : QS s L key nonce)
    (hi : QInv s L) (hdg8 : word s.mem L.S hDigest = dig) (hlen : word s.mem L.S hLens = pack L.pl L.ql qb d)
    (hqb : qb ≤ L.ql) (hd : d < 2 ^ 16) (hdg : Src s L dig (min d qb)) (hk : Src s L key (3 * L.pl + 2 * L.ql))
    (hq3 : 3 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h24 : arrQ s.mem L 24 = 2 ^ (128 * L.wq) % arrQ s.mem L 0)
    (h4 : arrQ s.mem L 4 < arrQ s.mem L 0) (h25 : arrQ s.mem L 25 < arrQ s.mem L 0)
    (hz : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) < 2 * arrQ s.mem L 0) :
    WP isa sValue s fun t =>
      (QS t L key nonce ∧ QInv t L ∧
        arrQ t.mem L 6 = arrQ s.mem L 4 * ((Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) %
          arrQ s.mem L 0 + xOf s.mem L key * arrQ s.mem L 25 % arrQ s.mem L 0) % arrQ s.mem L 0) %
            arrQ s.mem L 0 ∧
        arrQ t.mem L 25 = arrQ s.mem L 25 ∧ QArr L s.mem t.mem) ∧ Keep sValueRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hcop : Nat.Coprime (2 ^ (64 * L.wq)) (arrQ s.mem L 0) := VG.Proof.Bignum.coprime_pow2 hqo _
  have hRR := pow_two_mul L.wq
  have hnw : L.Q.toNat + 1600 ≤ 2 ^ 64 := h.inq.env.hs.nowrap
  have e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7
  have e8 := e 8; have e24 := e 24; have e25 := e 25; have e28 := e 28
  generalize hq : arrQ s.mem L 0 = q at hq3 hqo h24 h4 h25 hz hcop ⊢
  generalize (2 : Nat) ^ (128 * L.wq) = R2 at h24 hRR
  unfold sValue
  -- z into array 6, 0 into array 7, `z mod q` into array 6.
  refine WP.seq (WP.mono (scalar_ok hL h hdg8 hlen hqb hd hdg) fun s₁ ⟨⟨Q1, v6, o1⟩, k1⟩ => ?_)
  generalize Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) = z at v6 hz ⊢
  have f1 : AKeep L [6] s.mem s₁.mem := AKeep.one hL o1 (by omega)
  have qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by omega) (by omega)
  refine WP.seq (WP.mono (zeroArr_ok Q1.inq.env (j := 7) (by decide)) fun s₂ ⟨⟨z7, o2⟩, k2⟩ => ?_)
  have Q2 := Q1.step k2 (Body.ofQ hL o2 (by omega))
  have f2 : AKeep L [7] s₁.mem s₂.mem := AKeep.one hL o2 (by omega)
  have qa2 : QArr L s₁.mem s₂.mem := QArr.of o2 (by omega) (by omega)
  have q2 : arrQ s₂.mem L 0 = q := by rw [(qa1.trans qa2).arr0 hL]; exact hq
  have z2 : arrQ s₂.mem L 6 = z := (f2.get 6).trans v6
  refine WP.seq (WP.mono (addMod_ok Q2.inq.env (o := 6) (a := 6) (b := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show arrQ s₂.mem L 6 + arrQ s₂.mem L 7 < 2 * arrQ s₂.mem L 0; rw [z2, show arrQ s₂.mem L 7 = 0 from z7, q2]
        omega)) fun s₃ ⟨⟨a6, fr3⟩, k3⟩ => ?_)
  have a6' : arrQ s₃.mem L 6 = z % q := by
    show wordsVal s₃.mem L.Q (slot L.wq 6) L.wq = _
    rw [a6, show wordsVal s₂.mem L.Q (slot L.wq 6) L.wq = arrQ s₂.mem L 6 from rfl, z2,
      show wordsVal s₂.mem L.Q (slot L.wq 7) L.wq = 0 from z7,
      show wordsVal s₂.mem L.Q (slot L.wq 0) L.wq = arrQ s₂.mem L 0 from rfl, q2, Nat.add_zero]
  have qa3' := fr3.qarr (by decide) (by decide)
  have Q3 := Q2.step k3 (qa3'.body hL)
  have f3 := AKeep.add hL fr3 hnw
  have qa13 : QArr L s.mem s₃.mem := (qa1.trans qa2).trans qa3'
  have q3 : arrQ s₃.mem L 0 = q := by rw [qa13.arr0 hL]; exact hq
  have k13 := (k1.trans k2).trans k3
  have I3 : QInv s₃ L := hi.keepW (qa13.word0 hL) (k13.gpr (by decide))
  -- x's octets, and `x mod q` into array 1.
  refine WP.seq (WP.block_append (WP.mono (ptrX_ok Q3.scr hL Q3.regs) fun s₄ ⟨⟨b7, b8, m4⟩, k4⟩ =>
    WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = off key (3 * L.pl + L.ql) ∧
      u.gpr .s10 = BitVec.ofNat 64 L.ql ∧ u.mem = s₄.mem) (by brun [b7, b8, BitVec.add_zero]) (by decide) (by rfl))
    fun s₅ ⟨⟨c9, c10, m5⟩, k5⟩ => ?_))
  have k35 := k4.trans k5
  have hm5 : s₅.mem = s₃.mem := by rw [m5, m4]
  have e3 := Q3.inq.env.keep k35
  have hx := (hk.keep (k13.trans k35).2.1 (k13.trans k35).2.2).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega)
  refine WP.seq (WP.mono (ModArith.reduce64_ok (B := L.Q) (Z := 1600) (w := L.wq) (D := off key (3 * L.pl + L.ql))
    (L := L.ql) e3.hs (by omega) (by omega) (by omega) e3.a7 e3.s5 e3.t0
    (by rw [hm5]; show 0 < arrQ s₃.mem L 0; rw [q3]; omega)
    (by rw [c9]; exact (BitVec.add_zero _).symm) c10 (by omega) (by omega) hx.rd (hx.sepQ hL))
    fun s₆ ⟨⟨v1, o6⟩, k6⟩ => ?_)
  rw [hm5] at v1 o6
  have x6 : arrQ s₆.mem L 1 = xOf s.mem L key % q := by
    refine v1.trans ?_
    rw [(hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega)).bytes (qa13.body hL) (by have := hL.z256; omega)]
    show _ % arrQ s₃.mem L 0 = _
    rw [q3]
    rfl
  have f6 := AKeep.red hL o6
  have qa6 : QArr L s₃.mem s₆.mem := QArr.of o6 (Nat.le_refl _) (by omega)
  have Q6 := Q3.step (k35.trans k6) (qa6.body hL)
  -- `x mod q` into array 5, `R² mod q` into array 1.
  refine WP.seq (WP.mono (copy_ok Q6.inq.env (o := 5) (a := 1) (by decide) (by decide) (by decide))
    fun s₇ ⟨⟨v5, o7⟩, k7⟩ => ?_)
  have Q7 := Q6.step k7 (Body.ofQ hL o7 (by omega))
  have f7 : AKeep L [5] s₆.mem s₇.mem := AKeep.one hL o7 (Nat.le_refl _)
  refine WP.seq (WP.mono (copy_ok Q7.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₈ ⟨⟨v1', o8⟩, k8⟩ => ?_)
  have Q8 := Q7.step k8 (Body.ofQ hL o8 (by omega))
  have f8 : AKeep L [1] s₇.mem s₈.mem := AKeep.one hL o8 (Nat.le_refl _)
  have qa8 : QArr L s.mem s₈.mem :=
    ((qa13.trans qa6).trans (QArr.of o7 (by omega) (by omega))).trans (QArr.of o8 (by omega) (by omega))
  have k18 := ((k13.trans k35).trans k6).trans (k7.trans k8)
  have I8 : QInv s₈ L := hi.keepW (qa8.word0 hL) (k18.gpr (by decide))
  have F38 := (f6.trans f7).trans f8
  have F08 := ((f1.trans f2).trans f3).trans F38
  have A0 : arrQ s₈.mem L 0 = q := by rw [qa8.arr0 hL]; exact hq
  have A1 : arrQ s₈.mem L 1 = R2 % q := by
    rw [arrQ, wordsVal_congr (m := s₇.mem) (d := slot L.wq 24) fun i hi => v1' i (by omega)]
    show arrQ s₇.mem L 24 = _
    rw [f7.get 24, f6.get 24, f3.get 24, f2.get 24, f1.get 24]; exact h24
  have A4 : arrQ s₈.mem L 4 = arrQ s.mem L 4 := F08.get 4
  have A5 : arrQ s₈.mem L 5 = xOf s.mem L key % q := by
    rw [f8.get 5, arrQ, wordsVal_congr (m := s₆.mem) (d := slot L.wq 1) fun i hi => v5 i (by omega)]
    exact x6
  have A6 : arrQ s₈.mem L 6 = z % q := (F38.get 6).trans a6'
  have A25 : arrQ s₈.mem L 25 = arrQ s.mem L 25 := F08.get 25
  -- `x r mod q` into array 5.
  refine WP.seq (WP.mono (qmont28_ok hL Q8 I8 (o := 5) (a := 5) (b := 25) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [A25, A0]; exact h25)) fun s₉ ⟨⟨Q9, I9, _, e9, k9a, qa9⟩, k9⟩ => ?_)
  rw [A0, A5, A25] at e9
  have f9 := AKeep.mont k9a
  have B0 : arrQ s₉.mem L 0 = q := (f9.get 0).trans A0
  have B1 : arrQ s₉.mem L 1 = R2 % q := (f9.get 1).trans A1
  refine WP.seq (WP.mono (qmont28_ok hL Q9 I9 (o := 5) (a := 5) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [B1, B0]; exact Nat.mod_lt _ (by omega)))
    fun s₁₀ ⟨⟨Q10, I10, l10, e10, k10a, qa10⟩, k10⟩ => ?_)
  rw [B0] at l10
  rw [B0, B1] at e10
  have X10 : arrQ s₁₀.mem L 5 = xOf s.mem L key % q * arrQ s.mem L 25 % q :=
    prod_mont_back hcop l10 e9 (by rw [e10, hRR])
  have f10 := AKeep.mont k10a
  have F910 := f9.trans f10
  have C0 : arrQ s₁₀.mem L 0 = q := (F910.get 0).trans A0
  have C6 : arrQ s₁₀.mem L 6 = z % q := (F910.get 6).trans A6
  -- `z + x r mod q` into array 6.
  have l1 := Nat.mod_lt z (show 0 < q by omega)
  have l2 := Nat.mod_lt (xOf s.mem L key % q * arrQ s.mem L 25) (show 0 < q by omega)
  refine WP.seq (WP.mono (addMod_ok Q10.inq.env (o := 6) (a := 6) (b := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show arrQ s₁₀.mem L 6 + arrQ s₁₀.mem L 5 < 2 * arrQ s₁₀.mem L 0; rw [C6, X10, C0]; omega))
    fun s₁₁ ⟨⟨a11, fr11⟩, k11⟩ => ?_)
  have a11' : arrQ s₁₁.mem L 6 = (z % q + xOf s.mem L key * arrQ s.mem L 25 % q) % q := by
    show wordsVal s₁₁.mem L.Q (slot L.wq 6) L.wq = _
    rw [a11, show wordsVal s₁₀.mem L.Q (slot L.wq 6) L.wq = arrQ s₁₀.mem L 6 from rfl, C6,
      show wordsVal s₁₀.mem L.Q (slot L.wq 5) L.wq = arrQ s₁₀.mem L 5 from rfl, X10,
      show wordsVal s₁₀.mem L.Q (slot L.wq 0) L.wq = arrQ s₁₀.mem L 0 from rfl, C0, Nat.mod_mul_mod]
  have qa11 := fr11.qarr (by decide) (by decide)
  have Q11 := Q10.step k11 (qa11.body hL)
  have I11 : QInv s₁₁ L := I10.keepW (qa11.word0 hL) (k11.gpr (by decide))
  have f11 := AKeep.add hL fr11 hnw
  have F911 := F910.trans f11
  have D0 : arrQ s₁₁.mem L 0 = q := (F911.get 0).trans A0
  have D1 : arrQ s₁₁.mem L 1 = R2 % q := (F911.get 1).trans A1
  have D4 : arrQ s₁₁.mem L 4 = arrQ s.mem L 4 := (F911.get 4).trans A4
  -- `w (z + x r) mod q` into array 6.
  refine WP.seq (WP.mono (qmont28_ok hL Q11 I11 (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [D4, D0]; exact h4)) fun s₁₂ ⟨⟨Q12, I12, _, e12, k12a, qa12⟩, k12⟩ => ?_)
  rw [D0, a11', D4] at e12
  have f12 := AKeep.mont k12a
  have E0 : arrQ s₁₂.mem L 0 = q := (f12.get 0).trans D0
  have E1 : arrQ s₁₂.mem L 1 = R2 % q := (f12.get 1).trans D1
  refine WP.mono (qmont28_ok hL Q12 I12 (o := 6) (a := 6) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [E1, E0]; exact Nat.mod_lt _ (by omega)))
    fun t ⟨⟨Qt, It, lt, et, kta, qat⟩, kt⟩ => ?_
  rw [E0] at lt
  rw [E0, E1] at et
  have ft := AKeep.mont kta
  have Ft := (((F08.trans F910).trans f11).trans f12).trans ft
  have kall := (((((k18.trans k9).trans k10).trans k11).trans k12).trans kt)
  refine ⟨⟨Qt, It, ?_, Ft.get 25, (((((qa8.trans qa9).trans qa10).trans qa11).trans qa12).trans qat)⟩, ?_⟩
  · exact (prod_mont_back hcop lt e12 (by rw [et, hRR])).trans (by rw [Nat.mul_comm _ (arrQ s.mem L 4)])
  · simp only [sValueRegs, List.append_assoc] at kall ⊢
    exact kall

end VG.Proof.Dsa.RISCV64
