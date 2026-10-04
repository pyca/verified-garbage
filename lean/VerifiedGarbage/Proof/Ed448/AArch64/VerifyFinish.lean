import VerifiedGarbage.Proof.Ed448.AArch64.VerifyStages

/-!
# Ed448 verification's equation on AArch64: the comparison and the result

`vfinish_ok`: `[4]Q` (`Q` in slots 0, 6 and 2) and `[4]R` (slots 8–10),
compared projectively (`X_Q Z_R = X_R Z_Q`, then `Y_Q Z_R = Y_R Z_Q`, each
check ORed into `x20`), the result `x0 = (x20 == 0)`, and `x19` and `x20`
restored.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep Keeps Outside2 Saved workRegs restore_ok)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv)
open VG.Impl.X448.AArch64 (ld)

/-- `d := r`. -/
theorem mov_ok (d r : Reg) (s : State) :
    WP isa (.block [.addImm .x d r 0]) s fun t => t.gpr d = s.gpr r ∧ t.mem = s.mem ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, BitVec.add_zero, RegUpd.gpr_write_self,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r' hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem doubleAt_keep062 (e : Fin 22 → Spec.X448.Fe) (i : Fin 22) (hi : 8 ≤ i.val ∧ i.val < 11) :
    evalOps (doubleAt 0 6 2) e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ doubleAt 0 6 2, fopDest op = 0 ∨ fopDest op = 2 ∨ fopDest op = 6 ∨
        (12 ≤ fopDest op ∧ fopDest op < 20) := by decide
    have := this op hop
    omega

theorem doubleAt_eval062 (e : Fin 22 → Spec.X448.Fe) :
    pt (evalOps (doubleAt 0 6 2) e) 0 6 2 = double (pt e 0 6 2) := rfl

/-- `[4]Q` and `[4]R`, and the first products `X_Q Z_R` and `X_R Z_Q`. -/
theorem compare_eval (e : Fin 22 → Spec.X448.Fe) :
    pt (evalOps (doubleAt 0 6 2 ++ doubleAt 0 6 2 ++ doubleAt 8 9 10 ++ doubleAt 8 9 10 ++
      ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e) 0 6 2 = double (double (pt e 0 6 2)) ∧
    pt (evalOps (doubleAt 0 6 2 ++ doubleAt 0 6 2 ++ doubleAt 8 9 10 ++ doubleAt 8 9 10 ++
      ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e) 8 9 10 = double (double (pt e 8 9 10)) ∧
    evalOps (doubleAt 0 6 2 ++ doubleAt 0 6 2 ++ doubleAt 8 9 10 ++ doubleAt 8 9 10 ++
      ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 12 =
      evalOps (doubleAt 0 6 2 ++ doubleAt 0 6 2 ++ doubleAt 8 9 10 ++ doubleAt 8 9 10 ++
        ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 0 *
      evalOps (doubleAt 0 6 2 ++ doubleAt 0 6 2 ++ doubleAt 8 9 10 ++ doubleAt 8 9 10 ++
        ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 10 ∧
    evalOps (doubleAt 0 6 2 ++ doubleAt 0 6 2 ++ doubleAt 8 9 10 ++ doubleAt 8 9 10 ++
      ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 13 =
      evalOps (doubleAt 0 6 2 ++ doubleAt 0 6 2 ++ doubleAt 8 9 10 ++ doubleAt 8 9 10 ++
        ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 8 *
      evalOps (doubleAt 0 6 2 ++ doubleAt 0 6 2 ++ doubleAt 8 9 10 ++ doubleAt 8 9 10 ++
        ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 2 := by
  have hk : ∀ (ec : Fin 22 → Spec.X448.Fe) (i : Fin 22), i.val < 11 →
      evalOps [.mul 12 0 10, .mul 13 8 2] ec i = ec i := fun ec i hi =>
    evalOps_keep _ _ _ fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl <;> simp only [fopDest] <;> omega
  have p12 : ∀ ec : Fin 22 → Spec.X448.Fe, evalOps [.mul 12 0 10, .mul 13 8 2] ec 12 = ec 0 * ec 10 :=
    fun _ => rfl
  have p13 : ∀ ec : Fin 22 → Spec.X448.Fe, evalOps [.mul 12 0 10, .mul 13 8 2] ec 13 = ec 8 * ec 2 :=
    fun _ => rfl
  simp only [evalOps_append]
  generalize h1 : evalOps (doubleAt 0 6 2) e = e1
  generalize h2 : evalOps (doubleAt 0 6 2) e1 = e2
  generalize h3 : evalOps (doubleAt 8 9 10) e2 = e3
  generalize h4 : evalOps (doubleAt 8 9 10) e3 = e4
  have q4 : pt e4 0 6 2 = double (double (pt e 0 6 2)) := by
    rw [pt_congr (by rw [← h4, doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h4, doubleAt_keep8 _ _ (Or.inl (by decide))]) (by rw [← h4, doubleAt_keep8 _ _ (Or.inl (by decide))]),
      pt_congr (by rw [← h3, doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h3, doubleAt_keep8 _ _ (Or.inl (by decide))]) (by rw [← h3, doubleAt_keep8 _ _ (Or.inl (by decide))]),
      ← h2, doubleAt_eval062, ← h1, doubleAt_eval062]
  have r4 : pt e4 8 9 10 = double (double (pt e 8 9 10)) := by
    rw [← h4, doubleAt_eval8, ← h3, doubleAt_eval8,
      pt_congr (by rw [← h2, doubleAt_keep062 _ _ (by decide)])
      (by rw [← h2, doubleAt_keep062 _ _ (by decide)]) (by rw [← h2, doubleAt_keep062 _ _ (by decide)]),
      pt_congr (by rw [← h1, doubleAt_keep062 _ _ (by decide)])
      (by rw [← h1, doubleAt_keep062 _ _ (by decide)]) (by rw [← h1, doubleAt_keep062 _ _ (by decide)])]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pt_congr (hk e4 0 (by decide)) (hk e4 6 (by decide)) (hk e4 2 (by decide)), q4]
  · rw [pt_congr (hk e4 8 (by decide)) (hk e4 9 (by decide)) (hk e4 10 (by decide)), r4]
  · rw [p12, hk e4 0 (by decide), hk e4 10 (by decide)]
  · rw [p13, hk e4 8 (by decide), hk e4 2 (by decide)]

/-- The comparison and the result. -/
theorem vfinish_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {g : Reg → BitVec 64} (hsv : Saved base g s.mem) :
    WP isa vfinish s fun t =>
      t.gpr .x0 = (if s.gpr .x20 = 0 ∧ Spec.Ed448.pointEqual (double (double (pt (E s.mem base) 0 6 2)))
        (double (double (pt (E s.mem base) 8 9 10))) = true then 1 else 0) ∧
      t.gpr .x19 = g .x19 ∧ t.gpr .x20 = g .x20 ∧
      (∀ r, r ∉ .x0 :: .x19 :: .x20 :: workRegs → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      DFrame base s.mem t.mem := by
  rw [vfinish, WP.seq_iff]
  refine WP.mono (field_ok _ (by decide) hs hb) fun s1 ⟨k1, b1, e1⟩ => ?_
  have hs1 := k1.scr hs
  obtain ⟨q1, r1, x12, x13⟩ := compare_eval (E s.mem base)
  rw [← e1] at q1 r1 x12 x13
  rw [WP.seq_iff]
  refine WP.mono (eqSlots_ok hs1 b1 12 13 (by decide) (by decide)) fun s2 ⟨⟨c4, hc4, x2⟩, k2, b2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.seq_iff]
  refine WP.mono (field_ok [.mul 12 6 10, .mul 13 9 2] (by decide) hs2 b2) fun s3 ⟨k3, b3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (eqSlots_ok hs3 b3 12 13 (by decide) (by decide)) fun s4 ⟨⟨c5, hc5, x4⟩, k4, b4⟩ => ?_
  have hs4 := k4.scr hs3
  rw [WP.block_append_iff]
  refine WP.mono (mov_ok .x5 .x20 s4) fun s5 ⟨v5, m5, k5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (isZero_ok s5) fun s6 ⟨v6, m6, k6⟩ => ?_
  rw [show ([.addImm .x .x0 .x5 0, ld .x19 0, ld .x20 8] : List Instr) =
    [.addImm .x .x0 .x5 0] ++ [ld .x19 0, ld .x20 8] from rfl, WP.block_append_iff]
  refine WP.mono (mov_ok .x0 .x5 s6) fun s7 ⟨v7, m7, k7⟩ => ?_
  have k57 : Keeps (.x0 :: .x19 :: .x20 :: workRegs) s4 s7 :=
    ((k5.mono (by decide)).trans (k6.mono (by decide))).trans (k7.mono (by decide))
  have hs7 : Scr s7 base := hs4.of_keeps k57 (by decide)
  have f14 : DFrame base s.mem s4.mem :=
    (((keep_dframe k1).trans (cframe_dframe k2.mem)).trans (keep_dframe k3)).trans (cframe_dframe k4.mem)
  have sv7 : Saved base g s7.mem := by
    rw [m7, m6, m5]; exact hsv.outside2 f14 (by decide) (by decide)
  refine WP.mono (restore_ok hs7 sv7) fun t ⟨t19, t20, mt, kt⟩ => ?_
  have k14 : Keeps (.x0 :: .x19 :: .x20 :: workRegs) s s4 :=
    (((k1.regs.mono (by decide)).trans (k2.regs.mono (by decide))).trans (k3.regs.mono (by decide))).trans
      (k4.regs.mono (by decide))
  have kall : Keeps (.x0 :: .x19 :: .x20 :: workRegs) s t := (k14.trans k57).trans (kt.mono (by decide))
  refine ⟨?_, t19, t20, kall.1, kall.2.1, kall.2.2, ?_⟩
  · -- the values
    have e2 : ∀ i : Fin 22, i ≠ 1 → E s2.mem base i = E s1.mem base i := fun i hi => k2.mem.E hi
    have y12 : E s3.mem base 12 = E s1.mem base 6 * E s1.mem base 10 := by
      rw [e3, ← e2 6 (by decide), ← e2 10 (by decide)]; rfl
    have y13 : E s3.mem base 13 = E s1.mem base 9 * E s1.mem base 2 := by
      rw [e3, ← e2 9 (by decide), ← e2 2 (by decide)]; rfl
    have hpe : Spec.Ed448.pointEqual (pt (E s1.mem base) 0 6 2) (pt (E s1.mem base) 8 9 10) = true ↔
        (E s1.mem base 0 * E s1.mem base 10 = E s1.mem base 8 * E s1.mem base 2 ∧
          E s1.mem base 6 * E s1.mem base 10 = E s1.mem base 9 * E s1.mem base 2) := by
      simp only [Spec.Ed448.pointEqual, pt, Bool.and_eq_true, beq_iff_eq]
    have hx : s4.gpr .x20 = s.gpr .x20 ||| c4 ||| c5 := by
      rw [x4, k3.regs.1 _ (by decide), x2, k1.regs.1 _ (by decide)]
    rw [kt.1 _ (by decide), v7, v6, v5, hx]
    refine if_congr ?_ rfl rfl
    rw [or_eq_zero64, or_eq_zero64, hc5, hc4, y12, y13, x12, x13, ← q1, ← r1, hpe, and_assoc]
  · rw [mt, m7, m6, m5]; exact f14

end VG.Proof.Ed448.AArch64
