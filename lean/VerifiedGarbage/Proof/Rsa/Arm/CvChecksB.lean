module

public import VerifiedGarbage.Proof.Rsa.CrtValuesMask
public import VerifiedGarbage.Proof.Rsa.Arm.CvChecksA
public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad

/-! # `vg_rsa_crt_values` on ARMv7: the inverse, the mask, and the division of `d` set up -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- The mask of the checks, from the quotient `X₁` and remainder `X₂` of `n / p` and the gcd `V`. -/
abbrev maskOf := VG.Proof.Rsa.CrtValues.maskOf

/-- Before the division of `d` by `p - 1`. -/
structure StD (s0 : State) (X₁ X₂ : Nat) (s : State) : Prop where
  base : Base s0 s
  ws : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr
  count : s.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)
  q : num s.mem (cvB s0) (cvW s0) aQ = cvQ s0
  d : num s.mem (cvB s0) (cvW s0) aD = cvD s0
  ddTop : w32 s.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * cvW s0) = 0
  dq : num s.mem (cvB s0) (cvW s0) aDQ = cvD s0
  dd : num s.mem (cvB s0) (cvW s0) aDD = 2 * (cvP s0 / 2)
  hdr : DivHdr s.mem (cvB s0) (cvW s0) aDQ aDR2 aDD aDT
  mask : ∃ V, slot s.mem (cvB s0) sMask = (if maskOf (cvP s0) (cvQ s0) X₁ X₂ V then 1 else 0) ∧
    (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧
      (cvM s0 : Int) ∣ (num s.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - V ∧
      num s.mem (cvB s0) (cvW s0) 3 < cvM s0)

/-- `max` of two words below `2^31`, as `primeWidth` computes it. -/
theorem max_word {x y : BitVec 32} (hx : x.toNat < 2 ^ 31) (hy : y.toNat < 2 ^ 31) :
    y + ((x - y) &&& ((x - y) >>> 31 - 1)) = BitVec.ofNat 32 (max x.toNat y.toNat) := by
  by_cases h : x.toNat < y.toNat
  · have e : (x - y) >>> 31 = 1 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
      show _ = 1
      omega
    rw [e, show (1 : BitVec 32) - 1 = 0#32 from rfl, BitVec.and_zero, BitVec.add_zero, Nat.max_eq_right h.le]
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  · have e : (x - y) >>> 31 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
      show _ = 0
      omega
    rw [e, show (0 : BitVec 32) - 1 = BitVec.allOnes 32 from rfl, BitVec.and_allOnes, Nat.max_eq_left (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

/-- `primeWidth`: `⌈max(p_len, q_len) / 4⌉` into `r9`. -/
theorem primeWidth_ok {s0 s : State} (h : Base s0 s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Base s0 t → t.gpr .r9 = BitVec.ofNat 32 ((max (cvPl s0) (cvQl s0) + 3) / 4) →
      Rest [.r0, .r1, .r2, .r3, .r9] s t → t.mem = s.mem → WP isa (.block rest) t Q) :
    WP isa (.block (primeWidth ++ rest)) s Q := by
  have sp := h.pre.sp48
  rw [h.sp.symm] at sp
  have kb := h.pre.kb
  have p2 := h.pre.pl2
  have q2 := h.pre.ql2
  unfold primeWidth
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp h.rA_mem sp (i := 5) (by decide) fun s1 u1 => ?_
  have b1 := h.of_rest (u1.rest (ws := [.r0]) (by simp)) u1.mem
  refine wp_ldrSp b1.rA_mem (by rw [u1.sp]; exact sp) (i := 7) (by decide) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_dp (op2_reg _ _) fun s6 u6 => ?_
  refine wp_dp (op2_reg _ _) fun s7 u7 => ?_
  refine wp_dp (op2_imm (by decide)) fun s8 u8 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t u9 => ?_
  have rest : Rest [.r0, .r1, .r2, .r3, .r9] s t := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans
      ((u7.rest (by simp)).trans ((u8.rest (by simp)).trans (u9.rest (by simp)))))))))
  have mt : t.mem = s.mem := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine k t (h.of_rest rest mt) ?_ rest mt
  have a5 : stackArg s 5 = stackArg s0 5 := h.arg (by decide)
  have a7 : stackArg s1 7 = stackArg s0 7 := b1.arg (by decide)
  have e0 : s2.gpr .r0 = stackArg s0 5 := by rw [u2.other _ (by decide), u1.gpr, a5]
  have e1 : s2.gpr .r1 = stackArg s0 7 := by rw [u2.gpr, a7]
  have e2 : s5.gpr .r2 = stackArg s0 5 - stackArg s0 7 := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, e0, e1]
  have e3 : s5.gpr .r3 = (stackArg s0 5 - stackArg s0 7) >>> 31 - 1 := by
    rw [u5.gpr, dpVal, u4.gpr, u3.gpr, dpVal, e0, e1]
  have e7 : s7.gpr .r9 = BitVec.ofNat 32 (max (cvPl s0) (cvQl s0)) := by
    rw [u7.gpr, dpVal, u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), e1, u6.gpr, dpVal, e2, e3]
    exact max_word (by simp only [cvPl, cvK] at p2 kb ⊢; omega) (by simp only [cvQl, cvK] at q2 kb ⊢; omega)
  rw [u9.gpr, u8.gpr, dpVal, e7]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, show (3 : BitVec 32).toNat = 3 from rfl]
  simp only [cvPl, cvQl, cvK] at p2 q2 kb ⊢
  omega

/-- A value below `2^(32 k)` read at `w ≥ k` words is its low `k` words. -/
theorem val32_of_lt {m : Mem} {b : Addr} {d k w v : Nat} (hk : k ≤ w) (h : val32 m b d w = v)
    (hv : v < 2 ^ (32 * k)) : val32 m b d k = v := by
  have e := VG.Proof.Mont.val32_append m b d k (w - k)
  rw [show k + (w - k) = w by omega, h] at e
  have lo := val32_lt m b d k
  generalize val32 m b (d + 4 * k) (w - k) = hi at e
  generalize val32 m b d k = lo' at e lo ⊢
  rcases Nat.eq_zero_or_pos hi with rfl | hp
  · omega
  · have : 2 ^ (32 * k) ≤ 2 ^ (32 * k) * hi := Nat.le_mul_of_pos_right _ hp
    omega

theorem checksB_ok [InvLaw] {s0 s : State} {X₁ X₂ : Nat} (h : StI s0 X₁ X₂ s) :
    WP isa (seqs checksB) s (StD s0 X₁ X₂) := by
  have pre := h.base.pre
  have hw := h.ws
  have fit := fun j (hj : j < nArr) => hw.fit64 (j := j) hj
  unfold checksB
  -- `inverse` at the primes' width `kq`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil primeWidth]
  refine primeWidth_ok h.base fun t0 b0 e9 r0 m0 => WP.block_nil ?_
  have w16 := pre.w16
  have p1 := pre.pl1
  have p2 := pre.pl2
  have q1 := pre.ql1
  have q2 := pre.ql2
  generalize hkq : (max (cvPl s0) (cvQl s0) + 3) / 4 = kq at e9
  have kq1 : 0 < kq := by omega
  have kqw : kq ≤ cvW s0 := by simp only [cvW] at *; omega
  have g0 : VG.Proof.Rsa.Arm.Inv.Gk t0 (cvB s0) (cvZ s0) (cvW s0) kq nArr :=
    ⟨hw.nowrap, by rw [r0.wr]; exact hw.writable, hw.fits, kq1, kqw, hw.wle,
      by rw [r0.gpr _ (by decide)]; exact hw.r7, by rw [r0.gpr _ (by decide)]; exact hw.r8, e9⟩
  have lenQ : cvQ s0 < 2 ^ (32 * kq) := by
    have := VG.Proof.Bignum.os2ip_lt (qBytes s0)
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    refine lt_of_lt_of_le this ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have lenM : cvM s0 < 2 ^ (32 * kq) := by
    have hP : cvP s0 < 2 ^ (8 * cvPl s0) := by
      have := VG.Proof.Bignum.os2ip_lt (pBytes s0)
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
      exact this
    have le : 2 ^ (8 * cvPl s0) ≤ 2 ^ (32 * kq) := Nat.pow_le_pow_right (by decide) (by omega)
    have ev : 2 ^ (8 * cvPl s0) % 2 = 0 := by
      rw [show 8 * cvPl s0 = (8 * cvPl s0 - 1) + 1 by omega, Nat.pow_succ]; simp
    show 2 * (cvP s0 / 2) + 1 < _
    generalize cvP s0 = P at hP
    generalize 2 ^ (8 * cvPl s0) = E at hP le ev
    omega
  have vM : VG.Proof.Rsa.Arm.Inv.nk t0.mem (cvB s0) (cvW s0) aM kq = cvM s0 := by
    rw [m0]; exact val32_of_lt kqw h.m lenM
  have vQ : VG.Proof.Rsa.Arm.Inv.nk t0.mem (cvB s0) (cvW s0) 0 kq = cvQ s0 := by
    rw [m0]; exact val32_of_lt kqw h.u lenQ
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (InvLaw.inverseK_ok g0 (by decide) (by decide)) fun t1a ⟨g1, k1a, r1a, inv⟩ => ?_
  rw [vM, vQ] at inv
  rw [m0] at k1a
  have R01 : Rest (.r6 :: .r7 :: .r8 :: .r9 :: opRegs) s t1a := (r0.mono (by simp)).trans (r1a.mono (by simp))
  have b1a := h.base.keep k1a (by decide) (by decide) (by decide) R01.sp R01.rd R01.wr
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil ctx]
  refine ctx_ok b1a fun t1 b1 h1 r1c m1c => WP.block_nil ?_
  have k1 : Keep (cvB s0) (cvW s0) invArrs invSlots s.mem t1.mem := m1c ▸ k1a
  have r1 : Rest (.r6 :: .r7 :: .r8 :: .r9 :: opRegs) s t1 :=
    R01.trans (r1c.mono (by simp))
  have I : 1 < cvM s0 → num t1.mem (cvB s0) (cvW s0) 1 = Nat.gcd (cvQ s0) (cvM s0) ∧
      (cvM s0 : Int) ∣ (num t1.mem (cvB s0) (cvW s0) 3 : Int) * cvQ s0 - num t1.mem (cvB s0) (cvW s0) 1 ∧
      num t1.mem (cvB s0) (cvW s0) 3 < cvM s0 := fun hM => by
    have hmo : cvM s0 % 2 = 1 := by simp only [cvM]; omega
    obtain ⟨v1, v3⟩ := inv hmo hM
    obtain ⟨d, l⟩ := InvLaw.inv30_spec hmo hM lenQ lenM
    change VG.Proof.Rsa.Arm.Inv.nk t1.mem _ _ 1 _ = _ ∧ _ ∣ (VG.Proof.Rsa.Arm.Inv.nk t1.mem _ _ 3 _ : Int) * _ -
      VG.Proof.Rsa.Arm.Inv.nk t1.mem _ _ 1 _ ∧ VG.Proof.Rsa.Arm.Inv.nk t1.mem _ _ 3 _ < _
    rw [m1c, v1, v3]
    exact ⟨rfl, d, l⟩
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h1 (d := sE3) (a := 1) (b := aOne) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  have one1 : num t1.mem (cvB s0) (cvW s0) aOne = 1 := by
    rw [k1.num (by decide) (by decide) (fit _ (by decide)), h.one]
  rw [one1] at e2
  have sl : ∀ d, d + 4 ≤ hdr → d % 4 = 0 → d ∉ [sT, sE3, sOdd, sB, sC] →
      slot t2.mem (cvB s0) d = slot s.mem (cvB s0) d := fun d hd h4 hn => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp only [sT, sE3, sOdd, sB, sC, hdr] at hn hd
    rw [k2.slot (by simp only [hdr]; omega_arith) (by simp only [sT, sE3]; simp; omega_arith),
      k1.slot (by simp only [hdr]; omega_arith) (by simp only [invSlots, sOdd, sB, sC]; simp; omega_arith)]
  rw [wp_seqs_cons (List.cons_ne_nil _ _), List.append_assoc, ← List.append_nil (andS sMask sMask sE3)]
  refine andS_ok h2 (d := sMask) (a := sPodd) (b := sE1) (by decide) (by decide) (by decide)
    (by rw [sl _ (by decide) (by decide) (by decide), h.podd]; omega_arith) (by rw [sl _ (by decide) (by decide) (by decide), h.e1]; split <;> omega_arith)
    fun t3a h3a k3a m3a r3a => ?_
  refine andS_ok h3a (d := sMask) (a := sMask) (b := sE2) (by decide) (by decide) (by decide)
    (by rw [m3a]; split <;> omega_arith) (by rw [k3a.slot (by decide) (by decide), sl _ (by decide) (by decide) (by decide), h.e2]; split <;> omega_arith)
    fun t3b h3b k3b m3b r3b => ?_
  refine andS_ok h3b (d := sMask) (a := sMask) (b := sE3) (by decide) (by decide) (by decide)
    (by rw [m3b]; split <;> omega_arith)
    (by rw [k3b.slot (by decide) (by decide), k3a.slot (by decide) (by decide), e2]; split <;> omega_arith)
    fun t3 h3 k3 m3 r3 => WP.block_nil ?_
  have K3 : Keep (cvB s0) (cvW s0) [] [sMask] t2.mem t3.mem := k3a.trans (k3b.trans k3)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h3 (o := aDQ) (a := aD) (by decide) (by decide) (by decide) (by decide))
    fun t4 ⟨h4, k4, e4, r4, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h4 (o := aDD) (a := aP) (by decide) (by decide) (by decide) (by decide))
    fun t5 ⟨h5, k5, e5, r5, top5⟩ => ?_
  refine clrLow_ok h5 (by decide) (by decide) fun t6 h6 k6 e6 r6 top6 => ?_
  rw [← List.append_nil (divHdr _ _ _ _)]
  -- The count, through every step.
  have K : Keep (cvB s0) (cvW s0) (invArrs ++ [aDQ, aDD]) (invSlots ++ [sT, sE3, sMask]) s.mem t6.mem :=
    k1.mono.trans (k2.mono.trans (K3.mono.trans (k4.mono.trans (k5.mono.trans k6.mono))))
  have c6 : t6.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0) := by
    rw [← h.count]; refine BitVec.eq_of_toNat_eq ?_
    exact K.slot (e := 16) (by decide) (by decide)
  refine divHdr_ok h6 (by decide) (by decide) (by decide) (by decide) c6 fun t h7 k7 d7 r7 => WP.block_nil ?_
  have KK : Keep (cvB s0) (cvW s0) (invArrs ++ [aDQ, aDD]) (invSlots ++ [sT, sE3, sMask, 0, 4, 8, 12])
      s.mem t.mem := K.mono.trans k7.mono
  have R : Rest (.r6 :: .r7 :: .r8 :: .r9 :: opRegs) s t := r1.trans ((r2.mono (by simp)).trans ((r3a.mono (by simp)).trans
    ((r3b.mono (by simp)).trans ((r3.mono (by simp)).trans ((r4.mono (by simp)).trans ((r5.mono (by simp)).trans
      ((r6.mono (by simp)).trans (r7.mono (by simp)))))))))
  have bt := h.base.keep KK (by decide) (by decide) (by decide) R.sp R.rd R.wr
  have tr : ∀ j, j < nArr → j ∉ invArrs ++ [aDQ, aDD] →
      num t.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j := fun j hj hn =>
    KK.num (fun k hk e => hn (by subst e; exact hk)) (by decide) (fit j hj)
  have fDD := fit aDD (by decide)
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  refine ⟨bt, h7, ?_, ?_, ?_, ?_, ?_, ?_, d7, ?_⟩
  · rw [← h.count]; refine BitVec.eq_of_toNat_eq ?_
    exact KK.slot (e := 16) (by decide) (by decide)
  · rw [tr _ (by decide) (by decide), h.q]
  · rw [tr _ (by decide) (by decide), h.d]
  · rw [k7.word (by omega_arith) (by simp) (by decide) fDD, top6, top5,
      k4.word (by omega_arith) (by decide) (by simp) fDD, K3.word (by omega_arith) (by simp) (by decide) fDD,
      k2.word (by omega_arith) (by decide) (by decide) fDD, k1.word (by omega_arith) (by decide) (by decide) fDD, h.ddTop]
  · rw [k7.num (by simp) (by decide) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), e4, K3.num (by simp) (by decide) (fit _ (by decide)),
      k2.num (by decide) (by decide) (fit _ (by decide)), k1.num (by decide) (by decide) (fit _ (by decide)), h.d]
  · rw [k7.num (by simp) (by decide) (fit _ (by decide)), e6, e5, k4.num (by decide) (by simp) (fit _ (by decide)),
      K3.num (by simp) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      k1.num (by decide) (by decide) (fit _ (by decide)), h.p]
  · have x3 : num t.mem (cvB s0) (cvW s0) 3 = num t1.mem (cvB s0) (cvW s0) 3 := by
      rw [k7.num (by simp) (by decide) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
        k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
        K3.num (by simp) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide))]
    refine ⟨num t1.mem (cvB s0) (cvW s0) 1, ?_, fun hM => by rw [x3]; exact I hM⟩
    rw [k7.slot (by decide) (by decide), k6.slot (by decide) (by simp), k5.slot (by decide) (by simp),
      k4.slot (by decide) (by simp), m3, m3b, k3b.slot (e := sE3) (by decide) (by decide), m3a,
      k3a.slot (e := sE2) (by decide) (by decide), k3a.slot (e := sE3) (by decide) (by decide), e2,
      sl sPodd (by decide) (by decide) (by decide), sl sE1 (by decide) (by decide) (by decide),
      sl sE2 (by decide) (by decide) (by decide), h.podd, h.e1, h.e2]
    simp only [maskOf, VG.Proof.Rsa.CrtValues.maskOf]
    by_cases a : cvP s0 % 2 = 1 <;> by_cases b : X₁ = cvQ s0 <;> by_cases c : X₂ = 0 <;>
      by_cases d : num t1.mem (cvB s0) (cvW s0) 1 = 1 <;> simp [a, b, c, d]

end VG.Proof.Rsa.Arm.CrtValues
