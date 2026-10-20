module
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyField
public import VerifiedGarbage.Proof.X448.Arm.Save

import VerifiedGarbage.Proof.Ed448.Arm.VerifySign
import VerifiedGarbage.Proof.X448.Arm.Restore
import VerifiedGarbage.Proof.X448.Arm.Counters
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Ed448 verification's equation on ARMv7: the comparison and the result

`vfinish_ok`: `Q` (slots 0, 21, 2) and `R` (slots 8–10) doubled twice and
compared projectively, `BAD |= 0` exactly when they represent the same point;
`r0 = 1` exactly when `BAD` is then 0, and the callee-saved registers
restored.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Proof.Ed448 (double)
open VG.Impl.X448.Arm (slot ACC saved ld ops Op)

/-- `r1 = (r10 == 0)`. -/
theorem isZeroR1_ok {s : State} (h12 : (s.gpr .r10).toNat < 65536) :
    WP isa (.block [.dp .sub .r1 .r10 (.imm 1), .mov .r1 (.shifted .r1 .lsr 31)]) s fun t =>
      t.gpr .r1 = (if s.gpr .r10 = 0 then 1 else 0) ∧ t.mem = s.mem ∧ Keeps [.r1] s t := by
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

/-- `vresult`: `r0 = (BAD == 0)`, the callee-saved registers and the link register restored. -/
theorem vresult_ok {s : State} {base : Addr} (hs : Scr s base)
    {g : Reg → BitVec 32} (hsv : Saved base g s.mem) (h12 : (s.gpr .r10).toNat < 65536) :
    WP isa (.block vresult) s fun t =>
      t.gpr .r0 = (if s.gpr .r10 = 0 then 1 else 0) ∧
      (∀ i < 8, t.gpr (saved[i]!) = g (saved[i]!)) ∧ t.gpr .lr = word s.mem base LR ∧
      (∀ r, r ∉ .lr :: .r0 :: .r1 :: saved → t.gpr r = s.gpr r) := by
  unfold vresult
  simp only [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (isZeroR1_ok h12) fun s2 ⟨r2, m2, k2⟩ => ?_
  have hs2 := hs.of_keeps k2 (by decide)
  have sv2 : Saved base g s2.mem := by rw [m2]; exact hsv
  refine VG.Proof.X25519.Arm.WP.append (restore_ok hs2 sv2) fun s3 ⟨r3, m3, k3⟩ => ?_
  refine VG.Proof.X25519.Arm.wp_ldr (a := off base LR) (by decide)
    (by rw [k3.1 _ (by decide)]; exact hs2.ea (by decide))
    (by rw [k3.2.1, k3.2.2]; exact hs2.read (by decide)) fun s4 h4 => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_reg _ _) fun t ht => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [ht.gpr, h4.other _ (by decide), k3.1 _ (by decide), r2]
  · intro i hi
    rw [ht.other _ (by revert i; decide), h4.other _ (by revert i; decide), r3 i hi]
  · rw [ht.other _ (by decide), h4.gpr, m3, m2]
  · intro r hr
    have a0 : ∀ x ∈ [Reg.lr], x ∈ .lr :: .r0 :: .r1 :: saved := by decide
    have a1 : ∀ x ∈ [Reg.r0], x ∈ .lr :: .r0 :: .r1 :: saved := by decide
    have a2 : ∀ x ∈ saved, x ∈ .lr :: .r0 :: .r1 :: saved := by decide
    have a3 : ∀ x ∈ [Reg.r1], x ∈ .lr :: .r0 :: .r1 :: saved := by decide
    rw [ht.other r (fun h => hr (a1 r (h ▸ List.mem_singleton_self _))),
      h4.other r (fun h => hr (a0 r (h ▸ List.mem_singleton_self _))), k3.1 r (fun h => hr (a2 r h)),
      k2.1 r (fun h => hr (a3 r h))]

/-- One pass of the comparison, `k + 1` left: `c = 0` exactly when slot 0 times slot 10 is slot 8
times slot 2, ORed into `BAD`; slots 21 and 9 copied into 0 and 8. -/
theorem vcmp_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) {k : Nat}
    (hk : k < 2) (he : s.gpr .r11 = BitVec.ofNat 32 (k + 1)) :
    WP isa vcmp s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 k ∧ isa.eval .ne t = some (!decide (k = 0)) ∧
      Keeps (.r10 :: .r11 :: workRegs) s t ∧ Outside2 base 64 2816 ACC 512 s.mem t.mem ∧
      BoundedEnv t.mem base ∧ E t.mem base 0 = E s.mem base 21 ∧ E t.mem base 8 = E s.mem base 9 ∧
      (∀ i : Index, i.val = 2 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 21 → E t.mem base i = E s.mem base i) ∧
      ∃ c : BitVec 32, c.toNat < 65536 ∧
        (c = 0 ↔ E s.mem base 0 * E s.mem base 10 = E s.mem base 8 * E s.mem base 2) ∧
        t.gpr .r10 = s.gpr .r10 ||| c := by
  unfold vcmp
  rw [show ([.mul (slot 12) (slot 0) (slot 10), .mul (slot 13) (slot 8) (slot 2)] : List Op) =
    ([.mul 12 0 10, .mul 13 8 2] : List FieldOp).map FieldOp.impl from rfl]
  refine ops_seq hs hb _ fun s1 k1 b1 e1 => ?_
  have hs1 := k1.scr hs
  have hk1 : ∀ i : Index, i ≠ 12 → i ≠ 13 → E s1.mem base i = E s.mem base i := fun i h12 h13 => by
    rw [e1]; simp only [applyOps, FieldOp.apply, opMul, Function.update_of_ne h13, Function.update_of_ne h12]
  have x12 : E s1.mem base 12 = E s.mem base 0 * E s.mem base 10 := by rw [e1]; rfl
  have x13 : E s1.mem base 13 = E s.mem base 8 * E s.mem base 2 := by rw [e1]; rfl
  refine WP.seq (WP.mono (eqSlots_ok hs1 b1 12 13 (by decide) (by decide) (by decide))
    fun s2 ⟨k2, b2, e2, c2, kw2⟩ => ?_)
  have hs2 := k2.scr hs1
  rw [show ([.copy (slot 0) (slot 21), .copy (slot 8) (slot 9)] : List Op) =
    ([.copy 0 21, .copy 8 9] : List FieldOp).map FieldOp.impl from rfl]
  refine ops_seq hs2 b2 _ fun s3 k3 b3 e3 => ?_
  have r11₃ : s3.gpr .r11 = BitVec.ofNat 32 (k + 1) := by
    rw [k3.regs.1 _ (by decide), kw2.1 _ (by decide), k1.regs.1 _ (by decide), he]
  refine VG.Proof.X25519.Arm.WP.append (decR11_ok (t := k) r11₃) fun v ⟨ev, gv, mv, rv, wv⟩ => ?_
  refine VG.Proof.X25519.Arm.wp_cmp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t vt hz => WP.block_nil ?_
  have e30 : E s3.mem base 0 = E s2.mem base 21 := by
    rw [e3]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_of_ne (by decide : (0 : Index) ≠ 8),
      Function.update_self]
  have e38 : E s3.mem base 8 = E s2.mem base 9 := by
    rw [e3]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_self,
      Function.update_of_ne (by decide : (9 : Index) ≠ 0)]
  have e3k : ∀ i : Index, i ≠ 0 → i ≠ 8 → E s3.mem base i = E s2.mem base i := fun i h0 h8 => by
    rw [e3]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_of_ne h8, Function.update_of_ne h0]
  have mt : t.mem = s3.mem := by rw [vt.mem, mv]
  obtain ⟨c, hcl, hcz, hcb⟩ := c2
  refine ⟨by rw [vt.gpr, ev], ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, by rw [mt]; exact b3, ?_, ?_, fun i hi => ?_,
    c, hcl, ?_, ?_⟩
  · simp only [eval, hz, ev]
    change some (!(BitVec.ofNat 32 k - BitVec.ofNat 32 0 == 0)) = _
    rw [BitVec.sub_zero, ofNat32_beq_zero (by omega)]
  · have a1 : ∀ x ∈ workRegs, x ∈ .r10 :: .r11 :: workRegs := by decide
    have a2 : ∀ x ∈ Reg.r10 :: workRegs, x ∈ .r10 :: .r11 :: workRegs := by decide
    rw [vt.gpr, gv r (fun h => hr (by subst h; decide)), k3.regs.1 r (fun h => hr (a1 r h)),
      kw2.1 r (fun h => hr (a2 r h)), k1.regs.1 r (fun h => hr (a1 r h))]
  · rw [vt.rd, rv, k3.regs.2.1, kw2.2.1, k1.regs.2.1]
  · rw [vt.wr, wv, k3.regs.2.2, kw2.2.2, k1.regs.2.2]
  · rw [mt]; exact (k1.mem.trans k2.mem).trans k3.mem
  · rw [mt, e30, e2 21 (by decide), hk1 21 (by decide) (by decide)]
  · rw [mt, e38, e2 9 (by decide), hk1 9 (by decide) (by decide)]
  · have h0 : i ≠ 0 := fun h => by subst h; revert hi; decide
    have h8 : i ≠ 8 := fun h => by subst h; revert hi; decide
    have h1 : i ≠ 1 := fun h => by subst h; revert hi; decide
    have h12 : i ≠ 12 := fun h => by subst h; revert hi; decide
    have h13 : i ≠ 13 := fun h => by subst h; revert hi; decide
    rw [mt, e3k i h0 h8, e2 i h1, hk1 i h12 h13]
  · rw [hcz, x12, x13]
  · rw [vt.gpr, gv _ (by decide), k3.regs.1 _ (by decide), hcb, k1.regs.1 _ (by decide)]

/-- A loop whose body runs twice. -/
theorem WP.loop2 {M : ISA} {b : Prog M} {c : M.Cond} {s : M.State} {Q : M.State → Prop}
    (h : WP M b s fun t => M.eval c t = some true ∧
      WP M b t fun u => M.eval c u = some false ∧ Q u) : WP M (.loop b c) s Q := by
  obtain ⟨t₁, s₁, e₁, hc₁, t₂, s₂, e₂, hc₂, q⟩ := h
  exact ⟨_, _, Exec.loopNext e₁ hc₁ (Exec.loopExit e₂ hc₂), q⟩

theorem vfinish_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {g : Reg → BitVec 32} (hsv : Saved base g s.mem) (h12 : (s.gpr .r10).toNat < 65536) :
    WP isa vfinish s fun t =>
      t.gpr .r0 = (if s.gpr .r10 = 0 ∧ Spec.Ed448.pointEqual (double (double (pt (E s.mem base) 0 21 2)))
        (double (double (pt (E s.mem base) 8 9 10))) = true then 1 else 0) ∧
      (∀ i < 8, t.gpr (saved[i]!) = g (saved[i]!)) ∧ t.gpr .lr = word s.mem base LR ∧
      (∀ r, r ∉ .lr :: .r0 :: .r1 :: .r10 :: .r11 :: workRegs ++ saved → t.gpr r = s.gpr r) := by
  unfold vfinish
  refine WP.seq (WP.mono (vdouble_ok hs hb) fun sd ⟨kd, od, bd, qd, rd⟩ => ?_)
  refine WP.seq (WP.mono (setCounter_ok sd 2 (by decide)) fun s1 ⟨e1, g1, m1, r1, w1⟩ => ?_)
  have kd1 : Keeps (.r11 :: workRegs) s s1 :=
    kd.trans ⟨fun r hr => g1 r (fun h => hr (by subst h; exact List.mem_cons_self)), r1, w1⟩
  have hs1 := hs.of_keeps kd1 (by decide)
  refine WP.seq (WP.loop2 ?_)
  -- the `X`s
  refine WP.mono (vcmp_ok hs1 (m1 ▸ bd) (k := 1) (by decide) e1)
    fun u ⟨eu, zu, ku, ou, bu, u0, u8, uk, c, hcl, hcz, hcb⟩ => ⟨by rw [zu]; rfl, ?_⟩
  -- the `Y`s
  refine WP.mono (vcmp_ok (hs1.of_keeps ku (by decide)) bu (k := 0) (by decide) eu)
    fun s3 ⟨_, z3, k3, o3, _, _, _, _, c', hcl', hcz', hcb'⟩ => ⟨by rw [z3]; rfl, ?_⟩
  have hs3 := (hs1.of_keeps ku (by decide)).of_keeps k3 (by decide)
  have r10 : s3.gpr .r10 = s.gpr .r10 ||| c ||| c' := by
    rw [hcb', hcb, kd1.1 _ (by decide)]
  have h12' : (s3.gpr .r10).toNat < 65536 := by
    rw [r10, BitVec.toNat_or, BitVec.toNat_or]
    exact Nat.or_lt_two_pow (n := 16) (Nat.or_lt_two_pow (n := 16) h12 hcl) hcl'
  have sv3 : Saved base g s3.mem :=
    ((hsv.outside2 od (by decide) (by decide)).outside2 (by rw [← m1]; exact ou) (by decide)
      (by decide)).outside2 o3 (by decide) (by decide)
  refine WP.mono (vresult_ok hs3 sv3 h12') fun t ⟨rt, st, lt, gt⟩ => ⟨?_, st, ?_, fun r hr => ?_⟩
  · rw [rt]
    refine if_congr ?_ rfl rfl
    rw [r10]
    refine (BitVec.or_eq_zero_iff.trans (and_congr_left fun _ => BitVec.or_eq_zero_iff)).trans ?_
    refine (and_congr (and_congr Iff.rfl hcz) hcz').trans ?_
    rw [u0, u8, uk 10 (by decide), uk 2 (by decide), m1, ← qd, ← rd]
    simp only [Spec.Ed448.pointEqual, pt, Bool.and_eq_true, beq_iff_eq, and_assoc]
    exact Iff.rfl
  · rw [lt, o3.word (by decide) (by decide) (by decide), ou.word (by decide) (by decide) (by decide), m1,
      od.word (by decide) (by decide) (by decide)]
  · have a1 : ∀ x ∈ Reg.r10 :: .r11 :: workRegs, x ∈ .lr :: .r0 :: .r1 :: .r10 :: .r11 :: workRegs ++ saved := by
      decide
    have a3 : ∀ x ∈ Reg.r11 :: workRegs, x ∈ .lr :: .r0 :: .r1 :: .r10 :: .r11 :: workRegs ++ saved := by
      decide
    have a0 : ∀ x ∈ Reg.lr :: .r0 :: .r1 :: saved, x ∈ .lr :: .r0 :: .r1 :: .r10 :: .r11 :: workRegs ++ saved := by
      decide
    rw [gt r (fun h => hr (a0 r h)), k3.1 r (fun h => hr (a1 r h)), ku.1 r (fun h => hr (a1 r h)),
      kd1.1 r (fun h => hr (a3 r h))]

end VG.Proof.Ed448.Arm
