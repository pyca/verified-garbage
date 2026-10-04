import VerifiedGarbage.Proof.Ed448.Arm.VerifyChecks
import VerifiedGarbage.Proof.Ed448.Arm.VerifySign
import VerifiedGarbage.Proof.X448.Arm.Restore

/-!
# Ed448 verification's equation on ARMv7: the comparison and the result

`vfinish_ok`: `Q` (slots 0, 21, 2) and `R` (slots 8–10) doubled twice and
compared projectively, `BAD |= 0` exactly when they represent the same point;
`r0 = 1` exactly when `BAD` is then 0, and the callee-saved registers
restored.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Proof.Ed448 (double)
open VG.Impl.X448.Arm (slot ACC saved ld ops Op)

/-- `[4]Q` and `[4]R`, doubling `Q` twice and then `R` twice. -/
def vcompare : List FieldOp := doubleF 0 21 2 ++ doubleF 0 21 2 ++ doubleF 8 9 10 ++ doubleF 8 9 10

theorem compare_eval (e : Env) :
    pt (applyOps vcompare e) 0 21 2 = double (double (pt e 0 21 2)) ∧
    pt (applyOps vcompare e) 8 9 10 = double (double (pt e 8 9 10)) := by
  simp only [vcompare, applyOps_append]
  generalize h1 : applyOps (doubleF 0 21 2) e = e1
  generalize h2 : applyOps (doubleF 0 21 2) e1 = e2
  generalize h3 : applyOps (doubleF 8 9 10) e2 = e3
  generalize h4 : applyOps (doubleF 8 9 10) e3 = e4
  refine ⟨?_, ?_⟩
  · rw [pt_congr' (by rw [← h4, doubleF_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h4, doubleF_keep8 _ _ (Or.inr (Or.inr (Or.inr (by decide))))])
      (by rw [← h4, doubleF_keep8 _ _ (Or.inl (by decide))]),
      pt_congr' (by rw [← h3, doubleF_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h3, doubleF_keep8 _ _ (Or.inr (Or.inr (Or.inr (by decide))))])
      (by rw [← h3, doubleF_keep8 _ _ (Or.inl (by decide))]),
      ← h2, doubleF_eval0, ← h1, doubleF_eval0]
  · rw [← h4, doubleF_eval8, ← h3, doubleF_eval8,
      pt_congr' (by rw [← h2, doubleF_keep0 _ _ (Or.inl (by decide))])
      (by rw [← h2, doubleF_keep0 _ _ (Or.inl (by decide))]) (by rw [← h2, doubleF_keep0 _ _ (Or.inl (by decide))]),
      pt_congr' (by rw [← h1, doubleF_keep0 _ _ (Or.inl (by decide))])
      (by rw [← h1, doubleF_keep0 _ _ (Or.inl (by decide))]) (by rw [← h1, doubleF_keep0 _ _ (Or.inl (by decide))])]

/-- `r1 = (r12 == 0)`. -/
theorem isZeroR1_ok {s : State} (h12 : (s.gpr .r12).toNat < 65536) :
    WP isa (.block [.dp .sub .r1 .r12 (.imm 1), .mov .r1 (.shifted .r1 .lsr 31)]) s fun t =>
      t.gpr .r1 = (if s.gpr .r12 = 0 then 1 else 0) ∧ t.mem = s.mem ∧ Keeps [.r1] s t := by
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_lsr (by decide)) fun t ht =>
    WP.block_nil ⟨?_, by rw [ht.mem, hu.mem], rest_keeps ((hu.rest (by decide)).trans (ht.rest (by decide)))⟩
  rw [ht.gpr, hu.gpr]
  exact isZero16 _ h12

theorem ops_seq {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (xs : List FieldOp)
    {c : Prog isa} {Q : State → Prop}
    (k : ∀ t, Keep base s t → BoundedEnv t.mem base → E t.mem base = applyOps xs (E s.mem base) → WP isa c t Q) :
    WP isa (.seq (ops (xs.map FieldOp.impl)) c) s Q :=
  WP.seq (WP.mono (ops_ok hs hb xs) fun t ⟨kt, bt, et⟩ => k t kt bt et)

theorem vtail_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {g : Reg → BitVec 32} (hsv : Saved base g s.mem) (h12 : (s.gpr .r12).toNat < 65536) :
    WP isa (.block (eqSlots (slot 12) (slot 13) ++
      ([.dp .sub .r1 .r12 (.imm 1), .mov .r1 (.shifted .r1 .lsr 31)] : List Instr) ++
      (List.range 8).map (fun i => ld (saved[i]!) (4 * i)) ++ ([.mov .r0 (.reg .r1)] : List Instr))) s fun t =>
      t.gpr .r0 = (if s.gpr .r12 = 0 ∧ E s.mem base 12 = E s.mem base 13 then 1 else 0) ∧
      (∀ i < 8, t.gpr (saved[i]!) = g (saved[i]!)) ∧
      (∀ r, r ∉ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved → t.gpr r = s.gpr r) := by
  simp only [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (eqSlots_ok hs hb 12 13 (by decide) (by decide) (by decide))
    fun s1 ⟨k1, _, _, ⟨c, hc, hcz, he⟩⟩ => ?_
  have hs1 := k1.scr hs
  have h12' : (s1.gpr .r12).toNat < 65536 := by
    rw [he, BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 16) h12 hc
  refine VG.Proof.X25519.Arm.WP.append (isZeroR1_ok h12') fun s2 ⟨r2, m2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  have sv2 : Saved base g s2.mem := by
    rw [m2]; exact hsv.outside2 k1.mem (by decide) (by decide)
  refine VG.Proof.X25519.Arm.WP.append (restore_ok hs2 sv2) fun s3 ⟨r3, m3, k3⟩ => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_reg _ _) fun t ht => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [ht.gpr, k3.1 _ (by decide), r2, he]
    refine if_congr ?_ rfl rfl
    exact BitVec.or_eq_zero_iff.trans (and_congr_right fun _ => hcz)
  · intro i hi
    rw [ht.other _ (by revert i; decide), r3 i hi]
  · intro r hr
    have a1 : ∀ x ∈ [Reg.r0], x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by decide
    have a2 : ∀ x ∈ saved, x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by decide
    have a3 : ∀ x ∈ [Reg.r1], x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by decide
    have a4 : ∀ x ∈ Reg.r12 :: .r11 :: workRegs, x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by
      decide
    rw [ht.other r (fun h => hr (a1 r (h ▸ List.mem_singleton_self _))), k3.1 r (fun h => hr (a2 r h)),
      k2.1 r (fun h => hr (a3 r h)), k1.regs.1 r (fun h => hr (a4 r h))]

theorem vfinish_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {g : Reg → BitVec 32} (hsv : Saved base g s.mem) (h12 : (s.gpr .r12).toNat < 65536) :
    WP isa vfinish s fun t =>
      t.gpr .r0 = (if s.gpr .r12 = 0 ∧ Spec.Ed448.pointEqual (double (double (pt (E s.mem base) 0 21 2)))
        (double (double (pt (E s.mem base) 8 9 10))) = true then 1 else 0) ∧
      (∀ i < 8, t.gpr (saved[i]!) = g (saved[i]!)) ∧
      (∀ r, r ∉ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved → t.gpr r = s.gpr r) := by
  unfold vfinish
  rw [show doubleAt 0 21 2 = (doubleF 0 21 2).map FieldOp.impl from rfl,
    show doubleAt 8 9 10 = (doubleF 8 9 10).map FieldOp.impl from rfl]
  refine ops_seq hs hb _ fun sa ka ba ea => ?_
  refine ops_seq (ka.scr hs) ba _ fun sb kb bb eb => ?_
  refine ops_seq (kb.scr (ka.scr hs)) bb _ fun sc kc bc ec => ?_
  refine ops_seq (kc.scr (kb.scr (ka.scr hs))) bc _ fun sd kd bd ed => ?_
  have hsd := kd.scr (kc.scr (kb.scr (ka.scr hs)))
  rw [show ([.mul (slot 12) (slot 0) (slot 10), .mul (slot 13) (slot 8) (slot 2)] : List Op) =
    ([.mul 12 0 10, .mul 13 8 2] : List FieldOp).map FieldOp.impl from rfl]
  refine ops_seq hsd bd _ fun s1 k1 b1 e1 => ?_
  have hs1 := k1.scr hsd
  refine WP.seq (WP.mono (eqSlots_ok hs1 b1 12 13 (by decide) (by decide) (by decide))
    fun s2 ⟨k2, b2, e2, c2⟩ => ?_)
  have hs2 := k2.scr hs1
  rw [show ([.mul (slot 12) (slot 21) (slot 10), .mul (slot 13) (slot 9) (slot 2)] : List Op) =
    ([.mul 12 21 10, .mul 13 9 2] : List FieldOp).map FieldOp.impl from rfl]
  refine ops_seq hs2 b2 _ fun s3 k3 b3 e3 => ?_
  have hs3 := k3.scr hs2
  have sv3 : Saved base g s3.mem :=
    ((((((hsv.outside2 ka.mem (by decide) (by decide)).outside2 kb.mem (by decide) (by decide)).outside2
      kc.mem (by decide) (by decide)).outside2 kd.mem (by decide) (by decide)).outside2 k1.mem (by decide)
      (by decide)).outside2 k2.mem (by decide) (by decide)).outside2 k3.mem (by decide) (by decide)
  obtain ⟨c, hc, hcz, he⟩ := c2
  have r12 : s3.gpr .r12 = s1.gpr .r12 ||| c := by
    rw [k3.regs.1 _ (by decide)]; exact he
  have r12' : s1.gpr .r12 = s.gpr .r12 := by
    rw [k1.regs.1 _ (by decide), kd.regs.1 _ (by decide), kc.regs.1 _ (by decide), kb.regs.1 _ (by decide),
      ka.regs.1 _ (by decide)]
  rw [r12'] at r12
  have h12' : (s3.gpr .r12).toNat < 65536 := by
    rw [r12, BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 16) h12 hc
  refine WP.mono (vtail_ok hs3 b3 sv3 h12') fun t ⟨rt, st, gt⟩ => ⟨?_, st, fun r hr => ?_⟩
  · rw [rt]
    refine if_congr ?_ rfl rfl
    -- the values
    have ed' : E sd.mem base = applyOps vcompare (E s.mem base) := by
      rw [ed, ec, eb, ea]; simp only [vcompare, applyOps_append]
    obtain ⟨q4, r4⟩ := compare_eval (E s.mem base)
    rw [← ed'] at q4 r4
    have x12 : E s3.mem base 12 = E sd.mem base 21 * E sd.mem base 10 := by
      rw [e3, show ∀ e : Env, applyOps [.mul 12 21 10, .mul 13 9 2] e 12 = e 21 * e 10 from fun _ => rfl,
        e2 21 (by decide), e2 10 (by decide), e1]; rfl
    have x13 : E s3.mem base 13 = E sd.mem base 9 * E sd.mem base 2 := by
      rw [e3, show ∀ e : Env, applyOps [.mul 12 21 10, .mul 13 9 2] e 13 = e 9 * e 2 from fun _ => rfl,
        e2 9 (by decide), e2 2 (by decide), e1]; rfl
    have y12 : E s1.mem base 12 = E sd.mem base 0 * E sd.mem base 10 := by rw [e1]; rfl
    have y13 : E s1.mem base 13 = E sd.mem base 8 * E sd.mem base 2 := by rw [e1]; rfl
    rw [r12]
    refine (and_congr_left fun _ => BitVec.or_eq_zero_iff).trans ?_
    change (s.gpr .r12 = 0 ∧ c = 0) ∧ E s3.mem base 12 = E s3.mem base 13 ↔ _
    rw [hcz, x12, x13, y12, y13, ← q4, ← r4]
    simp only [Spec.Ed448.pointEqual, pt, Bool.and_eq_true, beq_iff_eq, and_assoc]
  · have a1 : ∀ x ∈ workRegs, x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by decide
    have a2 : ∀ x ∈ Reg.r12 :: .r11 :: workRegs, x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by
      decide
    rw [gt r hr, k3.regs.1 r (fun h => hr (a1 r h)), k2.regs.1 r (fun h => hr (a2 r h)),
      k1.regs.1 r (fun h => hr (a1 r h)), kd.regs.1 r (fun h => hr (a1 r h)),
      kc.regs.1 r (fun h => hr (a1 r h)), kb.regs.1 r (fun h => hr (a1 r h)),
      ka.regs.1 r (fun h => hr (a1 r h))]

end VG.Proof.Ed448.Arm
