import VerifiedGarbage.Proof.Ed448.Arm.VerifyChecks
import VerifiedGarbage.Proof.Ed448.Arm.VerifySign
import VerifiedGarbage.Proof.X448.Arm.Restore
import VerifiedGarbage.Proof.X448.Arm.Counters
import VerifiedGarbage.Proof.Ed448.Arm.BaseStep

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

theorem ofNat32_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

/-- Both doublings of `vdouble`'s body. -/
theorem double2_eval (e : Env) :
    pt (applyOps (doubleF 0 21 2 ++ doubleF 8 9 10) e) 0 21 2 = double (pt e 0 21 2) ∧
    pt (applyOps (doubleF 0 21 2 ++ doubleF 8 9 10) e) 8 9 10 = double (pt e 8 9 10) := by
  rw [applyOps_append]
  constructor
  · rw [pt_congr' (doubleF_keep8 _ 0 (Or.inl (by decide)))
      (doubleF_keep8 _ 21 (Or.inr (Or.inr (Or.inr (by decide))))) (doubleF_keep8 _ 2 (Or.inl (by decide))),
      doubleF_eval0]
  · rw [doubleF_eval8, pt_congr' (doubleF_keep0 e 8 (Or.inl (by decide)))
      (doubleF_keep0 e 9 (Or.inl (by decide))) (doubleF_keep0 e 10 (Or.inl (by decide)))]

/-- `[2]Q` and `[2]R`, a step of `vdouble` with `k + 1` left. -/
theorem vdoubleStep_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) {k : Nat}
    (hk : k < 2 ^ 16) (he : s.gpr .r11 = BitVec.ofNat 32 (k + 1)) :
    WP isa (.seq (ops (doubleAt 0 21 2 ++ doubleAt 8 9 10))
      (.block [.dp .sub .r11 .r11 (.imm 1), .cmp .r11 (.imm 0)])) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 k ∧ isa.eval .ne t = some (!decide (k = 0)) ∧
      Keeps (.r11 :: workRegs) s t ∧ Outside2 base 64 2816 ACC 512 s.mem t.mem ∧ BoundedEnv t.mem base ∧
      pt (E t.mem base) 0 21 2 = double (pt (E s.mem base) 0 21 2) ∧
      pt (E t.mem base) 8 9 10 = double (pt (E s.mem base) 8 9 10) := by
  rw [show doubleAt 0 21 2 ++ doubleAt 8 9 10 = (doubleF 0 21 2 ++ doubleF 8 9 10).map FieldOp.impl from rfl]
  refine ops_seq hs hb _ fun u ku bu eu => ?_
  refine VG.Proof.X25519.Arm.WP.append (decR11_ok (t := k) (by rw [ku.regs.1 _ (by decide), he]))
    fun v ⟨ev, gv, mv, rv, wv⟩ => ?_
  refine VG.Proof.X25519.Arm.wp_cmp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t vt hz => WP.block_nil ?_
  obtain ⟨d1, d2⟩ := double2_eval (E s.mem base)
  have et : t.gpr .r11 = BitVec.ofNat 32 k := by rw [vt.gpr, ev]
  refine ⟨et, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, by rw [vt.mem, mv]; exact ku.mem, by rw [vt.mem, mv]; exact bu,
    by rw [vt.mem, mv, eu]; exact d1, by rw [vt.mem, mv, eu]; exact d2⟩
  · simp only [eval, hz, ev]
    change some (!(BitVec.ofNat 32 k - BitVec.ofNat 32 0 == 0)) = _
    rw [BitVec.sub_zero, ofNat32_beq_zero (by omega)]
  · rw [vt.gpr, gv r (fun h => hr (by simp [h])), ku.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h))]
  · rw [vt.rd, rv, ku.regs.2.1]
  · rw [vt.wr, wv, ku.regs.2.2]

/-- `[4]Q` and `[4]R`. -/
theorem vdouble_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) :
    WP isa vdouble s fun t => Keeps (.r11 :: workRegs) s t ∧ Outside2 base 64 2816 ACC 512 s.mem t.mem ∧
      BoundedEnv t.mem base ∧ pt (E t.mem base) 0 21 2 = double (double (pt (E s.mem base) 0 21 2)) ∧
      pt (E t.mem base) 8 9 10 = double (double (pt (E s.mem base) 8 9 10)) := by
  unfold vdouble
  refine WP.seq (WP.mono (setCounter_ok s 2 (by decide)) fun s₁ ⟨e₁, g₁, m₁, r₁, w₁⟩ => ?_)
  have k₁ : Keeps (.r11 :: workRegs) s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), r₁, w₁⟩
  refine WP.loop (M := isa) (fun m (t : State) => 1 ≤ m ∧ m ≤ 2 ∧ t.gpr .r11 = BitVec.ofNat 32 m ∧
      Keeps (.r11 :: workRegs) s t ∧ Outside2 base 64 2816 ACC 512 s.mem t.mem ∧ BoundedEnv t.mem base ∧
      pt (E t.mem base) 0 21 2 = (if m = 2 then id else double) (pt (E s.mem base) 0 21 2) ∧
      pt (E t.mem base) 8 9 10 = (if m = 2 then id else double) (pt (E s.mem base) 8 9 10)) ?_ 2 s₁
    ⟨by decide, by decide, e₁, k₁, by rw [m₁]; exact Outside2.refl _ _ _ _ _ _, m₁ ▸ hb, by rw [m₁]; rfl,
      by rw [m₁]; rfl⟩
  intro m t ⟨h1, h2, et, kt, ot, bt, qt, rt⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (vdoubleStep_ok (hs.of_keeps kt (by decide)) bt (by omega) et)
    fun u ⟨eu, zu, ku, ou, bu, qu, ru⟩ => ?_
  have ku' : Keeps (.r11 :: workRegs) s u := kt.trans ku
  have ou' := ot.trans ou
  rw [zu]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine .inl ⟨rfl, ku', ou', bu, ?_, ?_⟩
    · rw [qu, qt]; rfl
    · rw [ru, rt]; rfl
  · have k1 : k = 1 := by omega
    subst k1
    refine .inr ⟨rfl, 1, by omega, by omega, by omega, eu, ku', ou', bu, by rw [qu, qt]; rfl,
      by rw [ru, rt]; rfl⟩

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
  refine WP.seq (WP.mono (vdouble_ok hs hb) fun sd ⟨kd, od, bd, qd, rd⟩ => ?_)
  have hsd := hs.of_keeps kd (by decide)
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
    (((hsv.outside2 od (by decide) (by decide)).outside2 k1.mem (by decide)
      (by decide)).outside2 k2.mem (by decide) (by decide)).outside2 k3.mem (by decide) (by decide)
  obtain ⟨c, hc, hcz, he⟩ := c2
  have r12 : s3.gpr .r12 = s1.gpr .r12 ||| c := by
    rw [k3.regs.1 _ (by decide)]; exact he
  have r12' : s1.gpr .r12 = s.gpr .r12 := by
    rw [k1.regs.1 _ (by decide), kd.1 _ (by decide)]
  rw [r12'] at r12
  have h12' : (s3.gpr .r12).toNat < 65536 := by
    rw [r12, BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 16) h12 hc
  refine WP.mono (vtail_ok hs3 b3 sv3 h12') fun t ⟨rt, st, gt⟩ => ⟨?_, st, fun r hr => ?_⟩
  · rw [rt]
    refine if_congr ?_ rfl rfl
    -- the values
    have q4 := qd
    have r4 := rd
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
    have a3 : ∀ x ∈ Reg.r11 :: workRegs, x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by decide
    have a2 : ∀ x ∈ Reg.r12 :: .r11 :: workRegs, x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by
      decide
    rw [gt r hr, k3.regs.1 r (fun h => hr (a1 r h)), k2.regs.1 r (fun h => hr (a2 r h)),
      k1.regs.1 r (fun h => hr (a1 r h)), kd.1 r (fun h => hr (a3 r h))]

end VG.Proof.Ed448.Arm
