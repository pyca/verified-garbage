import VerifiedGarbage.Proof.Ed448.X86.VerifyChecks
import VerifiedGarbage.Proof.Ed448.X86.VerifySign
import VerifiedGarbage.Proof.X448.X86.Restore

/-!
# Ed448 verification's equation on x86 (32-bit): the comparison and the result

`vfinish_ok`: `[4]Q` (`Q` in slots 0, 6 and 2) and `[4]R` (slots 8–10),
compared projectively (`X_Q Z_R = X_R Z_Q`, then `Y_Q Z_R = Y_R Z_Q`, each
check ORed into `BAD`), the callee-saved registers restored, and
`eax = (BAD == 0)`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (double evalOps evalOps_keep evalOps_append fopDest pt)
open VG.Impl.X448.X86 (slot ACC ld restore)

theorem doubleAt_keep062 (e : Env) (i : Index) (hi : 8 ≤ i.val ∧ i.val < 11) :
    evalOps (doubleAt 0 6 2) e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ doubleAt 0 6 2, fopDest op = 0 ∨ fopDest op = 2 ∨ fopDest op = 6 ∨
        (12 ≤ fopDest op ∧ fopDest op < 20) := by decide
    have := this op hop
    omega

theorem doubleAt_eval062 (e : Env) :
    pt (evalOps (doubleAt 0 6 2) e) 0 6 2 = double (pt e 0 6 2) := rfl

/-- The doublings and the first products. -/
def vcompare : List FOp :=
  doubleAt 0 6 2 ++ doubleAt 0 6 2 ++ doubleAt 8 9 10 ++ doubleAt 8 9 10 ++ [.mul 12 0 10, .mul 13 8 2]

/-- `[4]Q` and `[4]R`, and the first products `X_Q Z_R` and `X_R Z_Q`. -/
theorem compare_eval (e : Env) :
    pt (evalOps vcompare e) 0 6 2 = double (double (pt e 0 6 2)) ∧
    pt (evalOps vcompare e) 8 9 10 = double (double (pt e 8 9 10)) ∧
    evalOps vcompare e 12 = evalOps vcompare e 0 * evalOps vcompare e 10 ∧
    evalOps vcompare e 13 = evalOps vcompare e 8 * evalOps vcompare e 2 := by
  have hk : ∀ (ec : Env) (i : Index), i.val < 11 →
      evalOps [.mul 12 0 10, .mul 13 8 2] ec i = ec i := fun ec i hi =>
    evalOps_keep _ _ _ fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl <;> simp only [fopDest] <;> omega
  have p12 : ∀ ec : Env, evalOps [.mul 12 0 10, .mul 13 8 2] ec 12 = ec 0 * ec 10 := fun _ => rfl
  have p13 : ∀ ec : Env, evalOps [.mul 12 0 10, .mul 13 8 2] ec 13 = ec 8 * ec 2 := fun _ => rfl
  simp only [vcompare, evalOps_append]
  generalize h1 : evalOps (doubleAt 0 6 2) e = e1
  generalize h2 : evalOps (doubleAt 0 6 2) e1 = e2
  generalize h3 : evalOps (doubleAt 8 9 10) e2 = e3
  generalize h4 : evalOps (doubleAt 8 9 10) e3 = e4
  have q4 : pt e4 0 6 2 = double (double (pt e 0 6 2)) := by
    rw [pt_congr' (by rw [← h4, Proof.Ed448.doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h4, Proof.Ed448.doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h4, Proof.Ed448.doubleAt_keep8 _ _ (Or.inl (by decide))]),
      pt_congr' (by rw [← h3, Proof.Ed448.doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h3, Proof.Ed448.doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h3, Proof.Ed448.doubleAt_keep8 _ _ (Or.inl (by decide))]),
      ← h2, doubleAt_eval062, ← h1, doubleAt_eval062]
  have r4 : pt e4 8 9 10 = double (double (pt e 8 9 10)) := by
    rw [← h4, Proof.Ed448.doubleAt_eval8, ← h3, Proof.Ed448.doubleAt_eval8,
      pt_congr' (by rw [← h2, doubleAt_keep062 _ _ (by decide)])
      (by rw [← h2, doubleAt_keep062 _ _ (by decide)]) (by rw [← h2, doubleAt_keep062 _ _ (by decide)]),
      pt_congr' (by rw [← h1, doubleAt_keep062 _ _ (by decide)])
      (by rw [← h1, doubleAt_keep062 _ _ (by decide)]) (by rw [← h1, doubleAt_keep062 _ _ (by decide)])]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pt_congr' (hk e4 0 (by decide)) (hk e4 6 (by decide)) (hk e4 2 (by decide)), q4]
  · rw [pt_congr' (hk e4 8 (by decide)) (hk e4 9 (by decide)) (hk e4 10 (by decide)), r4]
  · rw [p12, hk e4 0 (by decide), hk e4 10 (by decide)]
  · rw [p13, hk e4 8 (by decide), hk e4 2 (by decide)]

/-- `ecx = (BAD == 0)`. -/
theorem isZeroBad_ok {s : State} {base : Addr} (hs : Scr s base) (h : (word s.mem base BAD).toNat < 65536) :
    WP isa (.block ([ld .ecx BAD, .alu .sub .ecx (.imm 1), .shift .shr .ecx 31] : List Instr)) s fun t =>
      t.gpr .ecx = (if word s.mem base BAD = 0 then 1 else 0) ∧ t.mem = s.mem ∧ Keeps [.ecx] s t := by
  refine load_ok hs (by decide) fun u hu => ?_
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun v hv _ => ?_
  refine wp_shift (by decide) fun t ht => WP.block_nil ⟨?_, by rw [ht.mem, hv.mem, hu.mem], ?_⟩
  · rw [ht.gpr, hv.gpr]
    change (u.gpr .ecx - 1) >>> 31 = _
    rw [hu.gpr]
    exact isZero16 _ h
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (ht.rest (by simp)))

/-- The comparison and the result. -/
theorem vfinish_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {g : Reg → BitVec 32} (hsv : Saved base g s.mem) (h12 : (word s.mem base BAD).toNat < 65536) :
    WP isa vfinish s fun t =>
      t.gpr .eax = (if word s.mem base BAD = 0 ∧
        Spec.Ed448.pointEqual (double (double (pt (E s.mem base) 0 6 2)))
          (double (double (pt (E s.mem base) 8 9 10))) = true then 1 else 0) ∧
      (∀ p ∈ savedSlots, t.gpr p.1 = g p.1) ∧ t.gpr .esp = s.gpr .esp ∧
      Outside base 0 8192 s.mem t.mem := by
  unfold vfinish
  refine field_seq vcompare (by decide) hs hb fun s1 k1 b1 e1 => ?_
  have hs1 := k1.scr hs
  obtain ⟨q1, r1, x12, x13⟩ := compare_eval (E s.mem base)
  rw [← e1] at q1 r1 x12 x13
  rw [WP.seq_iff]
  refine WP.mono (eqSlots_ok hs1 b1 12 13 (by decide) (by decide) (by decide))
    fun s2 ⟨k2, b2, e2, c2⟩ => ?_
  have hs2 := k2.scr hs1
  refine field_seq [.mul 12 6 10, .mul 13 9 2] (by decide) hs2 b2 fun s3 k3 b3 e3 => ?_
  have hs3 := k3.scr hs2
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (eqSlots_ok hs3 b3 12 13 (by decide) (by decide) (by decide))
    fun s4 ⟨k4, b4, e4, c4⟩ => ?_
  have hs4 := k4.scr hs3
  obtain ⟨c, hc, hcz, he⟩ := c2
  obtain ⟨c', hc', hcz', he'⟩ := c4
  have bad1 : word s1.mem base BAD = word s.mem base BAD := Keep.bad k1
  have bad3 : word s3.mem base BAD = word s2.mem base BAD := Keep.bad k3
  have hbad : word s4.mem base BAD = word s.mem base BAD ||| c ||| c' := by rw [he', bad3, he, bad1]
  have h4 : (word s4.mem base BAD).toNat < 65536 := by
    rw [hbad, BitVec.toNat_or, BitVec.toNat_or]
    exact Nat.or_lt_two_pow (n := 16) (Nat.or_lt_two_pow (n := 16) h12 hc) hc'
  rw [WP.block_append_iff]
  refine WP.mono (isZeroBad_ok hs4 h4) fun s5 ⟨v5, m5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  have sv5 : Saved base g s5.mem := by
    rw [m5]
    exact (((hsv.outside2 k1.mem (by decide) (by decide)).outside2 k2.mem.widen (by decide)
      (by decide)).outside2 k3.mem (by decide) (by decide)).outside2 k4.mem.widen (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok hs5 sv5) fun s6 ⟨r6, m6, k6⟩ => ?_
  refine wp_mov rfl fun t ht => WP.block_nil ⟨?_, fun p hp => ?_, ?_, ?_⟩
  · rw [ht.gpr]; change s6.gpr .ecx = _
    rw [k6.1 _ (by decide), v5, hbad]
    refine if_congr ?_ rfl rfl
    -- the values
    have y12 : E s3.mem base 12 = E s1.mem base 6 * E s1.mem base 10 := by
      rw [e3, ← e2 6 (by decide), ← e2 10 (by decide)]; rfl
    have y13 : E s3.mem base 13 = E s1.mem base 9 * E s1.mem base 2 := by
      rw [e3, ← e2 9 (by decide), ← e2 2 (by decide)]; rfl
    have hpe : Spec.Ed448.pointEqual (pt (E s1.mem base) 0 6 2) (pt (E s1.mem base) 8 9 10) = true ↔
        (E s1.mem base 0 * E s1.mem base 10 = E s1.mem base 8 * E s1.mem base 2 ∧
          E s1.mem base 6 * E s1.mem base 10 = E s1.mem base 9 * E s1.mem base 2) := by
      simp only [Spec.Ed448.pointEqual, pt, Bool.and_eq_true, beq_iff_eq]
    refine (BitVec.or_eq_zero_iff.trans (and_congr_left fun _ => BitVec.or_eq_zero_iff)).trans ?_
    refine (and_congr (and_congr Iff.rfl hcz) hcz').trans ?_
    rw [y12, y13, x12, x13, ← q1, ← r1, hpe]
    exact and_assoc
  · have hne : p.1 ≠ .eax := by
      simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    rw [ht.other _ hne]; exact r6 p hp
  · rw [ht.other _ (by decide), k6.1 _ (by decide), k5.1 _ (by decide), k4.regs.1 _ (by decide),
      k3.regs.1 _ (by decide), k2.regs.1 _ (by decide), k1.regs.1 _ (by decide)]
  · rw [ht.mem, m6, m5]
    exact (((k1.mem.whole (by decide) (by decide)).trans (k2.mem.widen.whole (by decide) (by decide))).trans
      (k3.mem.whole (by decide) (by decide))).trans (k4.mem.widen.whole (by decide) (by decide))

end VG.Proof.Ed448.X86
