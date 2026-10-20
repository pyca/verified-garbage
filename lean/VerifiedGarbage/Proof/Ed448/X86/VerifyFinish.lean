module
public import VerifiedGarbage.Impl.Ed448.X86.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.Formulas
public import VerifiedGarbage.Proof.X448.X86.Ops
public import VerifiedGarbage.Proof.X448.X86.Save

import VerifiedGarbage.Proof.Ed448.X86.VerifySign
import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.X448.X86.Counters
import VerifiedGarbage.Proof.Ed448.VerifyFormulas

/-!
# Ed448 verification's equation on x86 (32-bit): the comparison and the result

`vfinish_ok`: `[4]Q` (`Q` in slots 0, 6 and 2) and `[4]R` (slots 8–10),
compared projectively (`X_Q Z_R = X_R Z_Q`, then `Y_Q Z_R = Y_R Z_Q`, each
check ORed into `BAD`, by two passes of `vcmp`: `vcmp_ok`), the callee-saved registers restored, and
`eax = (BAD == 0)`.
-/

@[expose] public section

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

/-- Both doublings of `vdouble`'s body. -/
theorem double2_eval (e : Env) :
    pt (evalOps (doubleAt 0 6 2 ++ doubleAt 8 9 10) e) 0 6 2 = double (pt e 0 6 2) ∧
    pt (evalOps (doubleAt 0 6 2 ++ doubleAt 8 9 10) e) 8 9 10 = double (pt e 8 9 10) := by
  rw [evalOps_append]
  constructor
  · rw [pt_congr' (Proof.Ed448.doubleAt_keep8 _ 0 (Or.inl (by decide)))
      (Proof.Ed448.doubleAt_keep8 _ 6 (Or.inl (by decide))) (Proof.Ed448.doubleAt_keep8 _ 2 (Or.inl (by decide))),
      doubleAt_eval062]
  · rw [Proof.Ed448.doubleAt_eval8, pt_congr' (doubleAt_keep062 e 8 (by decide))
      (doubleAt_keep062 e 9 (by decide)) (doubleAt_keep062 e 10 (by decide))]

/-- `[2]Q` and `[2]R`, a step of `vdouble` with `k + 1` left. -/
theorem vdoubleStep_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base)
    (hb : BoundedEnv s.mem base) {k : Nat}
    (hk : k < 2 ^ 16) (he : s.gpr .esi = BitVec.ofNat 32 (k + 1)) :
    WP isa (.seq (field (doubleAt 0 6 2 ++ doubleAt 8 9 10)) (.block [.alu .sub .esi (.imm 1)])) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 k ∧ t.zf = some (decide (k = 0)) ∧ Keeps (.esi :: workRegs) s t ∧
      WsOut2 base 64 2816 ACC 512 s.mem t.mem ∧ BoundedEnv t.mem base ∧
      pt (E t.mem base) 0 6 2 = double (pt (E s.mem base) 0 6 2) ∧
      pt (E t.mem base) 8 9 10 = double (pt (E s.mem base) 8 9 10) := by
  refine field_seq _ (by decide) hs hc hb fun u ku bu eu => ?_
  refine WP.mono (decCounter_ok hk (by rw [ku.regs.1 _ (by decide), he])) fun t ⟨et, gt, mt, rt, wt, zt⟩ => ?_
  obtain ⟨d1, d2⟩ := double2_eval (E s.mem base)
  refine ⟨et, zt, ⟨fun r hr => ?_, rt.trans ku.regs.2.1, wt.trans ku.regs.2.2⟩, by rw [mt]; exact ku.mem,
    by rw [mt]; exact bu, by rw [mt, eu]; exact d1, by rw [mt, eu]; exact d2⟩
  rw [gt r (fun h => hr (by simp [h])), ku.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h))]

/-- `[4]Q` and `[4]R`. -/
theorem vdouble_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base)
    (hb : BoundedEnv s.mem base) :
    WP isa vdouble s fun t => Keeps (.esi :: workRegs) s t ∧ WsOut2 base 64 2816 ACC 512 s.mem t.mem ∧
      BoundedEnv t.mem base ∧ pt (E t.mem base) 0 6 2 = double (double (pt (E s.mem base) 0 6 2)) ∧
      pt (E t.mem base) 8 9 10 = double (double (pt (E s.mem base) 8 9 10)) := by
  unfold vdouble
  refine WP.seq (WP.mono (setCounter_ok s 2 (by decide)) fun s₁ ⟨e₁, g₁, m₁, r₁, w₁⟩ => ?_)
  have k₁ : Keeps (.esi :: workRegs) s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), r₁, w₁⟩
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.loop (M := isa) (fun m (t : State) => 1 ≤ m ∧ m ≤ 2 ∧ t.gpr .esi = BitVec.ofNat 32 m ∧
      Keeps (.esi :: workRegs) s t ∧ WsOut2 base 64 2816 ACC 512 s.mem t.mem ∧ BoundedEnv t.mem base ∧
      pt (E t.mem base) 0 6 2 = (if m = 2 then id else double) (pt (E s.mem base) 0 6 2) ∧
      pt (E t.mem base) 8 9 10 = (if m = 2 then id else double) (pt (E s.mem base) 8 9 10)) ?_ 2 s₁
    ⟨by decide, by decide, e₁, k₁, by rw [m₁]; exact WsOut2.refl _ _ _ _ _ _, m₁ ▸ hb, by rw [m₁]; rfl,
      by rw [m₁]; rfl⟩
  intro m t ⟨h1, h2, et, kt, ot, bt, qt, rt⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (vdoubleStep_ok (hs.of_keeps kt (by decide)) (hc.keep (kt.1 _ (by decide))) bt (by omega) et)
    fun u ⟨eu, zu, ku, ou, bu, qu, ru⟩ => ?_
  have ku' : Keeps (.esi :: workRegs) s u := kt.trans ku
  have ou' := ot.trans ou
  simp only [eval, zu, Option.map_some]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine .inl ⟨rfl, ku', ou', bu, ?_, ?_⟩
    · rw [qu, qt]; rfl
    · rw [ru, rt]; rfl
  · have k1 : k = 1 := by omega
    subst k1
    refine .inr ⟨rfl, 1, by omega, by omega, by omega, eu, ku', ou', bu, by rw [qu, qt]; rfl,
      by rw [ru, rt]; rfl⟩

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

/-- One pass of the comparison, `k + 1` left: `c = 0` exactly when slot 0 times slot 10 is slot 8
times slot 2, ORed into `BAD`; slots 6 and 9 copied into 0 and 8. -/
theorem vcmp_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) (hb : BoundedEnv s.mem base)
    {k : Nat} (hk : k < 2) (he : s.gpr .esi = BitVec.ofNat 32 (k + 1)) :
    WP isa vcmp s fun t =>
      t.gpr .esi = BitVec.ofNat 32 k ∧ t.zf = some (decide (k = 0)) ∧
      Keeps (.esi :: workRegs) s t ∧ WsOut2 base 16 2864 ACC 512 s.mem t.mem ∧ BoundedEnv t.mem base ∧
      E t.mem base 0 = E s.mem base 6 ∧ E t.mem base 8 = E s.mem base 9 ∧
      (∀ i : Index, i.val = 2 ∨ i.val = 6 ∨ i.val = 9 ∨ i.val = 10 → E t.mem base i = E s.mem base i) ∧
      ∃ c : BitVec 32, c.toNat < 65536 ∧
        (c = 0 ↔ E s.mem base 0 * E s.mem base 10 = E s.mem base 8 * E s.mem base 2) ∧
        word t.mem base BAD = word s.mem base BAD ||| c := by
  unfold vcmp
  refine field_seq [.mul 12 0 10, .mul 13 8 2] (by decide) hs hc hb fun s1 k1 b1 e1 => ?_
  have hs1 := k1.scr hs
  have hc1 := k1.ctx hc
  have hk1 : ∀ i : Index, i.val < 11 → E s1.mem base i = E s.mem base i := fun i hi => by
    rw [e1]
    exact evalOps_keep _ _ _ fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl <;> simp only [fopDest] <;> omega
  have x12 : E s1.mem base 12 = E s.mem base 0 * E s.mem base 10 := by rw [e1]; rfl
  have x13 : E s1.mem base 13 = E s.mem base 8 * E s.mem base 2 := by rw [e1]; rfl
  refine WP.seq (WP.mono (eqSlots_ok hs1 b1 12 13 (by decide) (by decide) (by decide))
    fun s2 ⟨k2, b2, e2, c2, kw2⟩ => ?_)
  have hs2 : Scr s2 base := hs1.of_keeps kw2 (by decide)
  have hc2 : CallCtx s2 base := hc1.keep (kw2.1 _ (by decide))
  rw [show Impl.X448.X86.ops [.copy (slot 0) (slot 6), .copy (slot 8) (slot 9)] =
    Impl.X448.X86.ops (([.copy 0 6, .copy 8 9] : List FieldOp).map FieldOp.impl) from rfl]
  refine WP.seq (WP.mono (ops_ok hs2 hc2 b2 [.copy 0 6, .copy 8 9]) fun s3 ⟨k3, b3, e3⟩ => ?_)
  have esi3 : s3.gpr .esi = BitVec.ofNat 32 (k + 1) := by
    rw [k3.regs.1 _ (by decide), kw2.1 _ (by decide), k1.regs.1 _ (by decide), he]
  refine WP.mono (decCounter_ok (by omega) esi3) fun t ⟨et, gt, mt, rt, wt, zt⟩ => ?_
  have e30 : E s3.mem base 0 = E s2.mem base 6 := by
    rw [e3]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_of_ne (by decide : (0 : Index) ≠ 8),
      Function.update_self]
  have e38 : E s3.mem base 8 = E s2.mem base 9 := by
    rw [e3]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_self,
      Function.update_of_ne (by decide : (9 : Index) ≠ 0)]
  have e3k : ∀ i : Index, i ≠ 0 → i ≠ 8 → E s3.mem base i = E s2.mem base i := fun i h0 h8 => by
    rw [e3]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_of_ne h8, Function.update_of_ne h0]
  obtain ⟨c, hcl, hcz, hcb⟩ := c2
  refine ⟨et, zt, ⟨fun r hr => ?_, rt.trans (k3.regs.2.1.trans (kw2.2.1.trans k1.regs.2.1)),
    wt.trans (k3.regs.2.2.trans (kw2.2.2.trans k1.regs.2.2))⟩, ?_, by rw [mt]; exact b3, ?_, ?_,
    fun i hi => ?_, c, hcl, ?_, ?_⟩
  · rw [gt r (fun h => hr (by subst h; exact List.mem_cons_self)),
      k3.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h)), kw2.1 r (fun h => hr (List.mem_cons_of_mem _ h)),
      k1.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h))]
  · rw [mt]; exact ((WsOut2.widen k1.mem).trans (BMem.widen k2.mem)).trans (WsOut2.widen k3.mem)
  · rw [mt, e30, e2 6 (by decide), hk1 6 (by decide)]
  · rw [mt, e38, e2 9 (by decide), hk1 9 (by decide)]
  · have h0 : i ≠ 0 := fun h => by subst h; revert hi; decide
    have h8 : i ≠ 8 := fun h => by subst h; revert hi; decide
    have h1 : i ≠ 1 := fun h => by subst h; revert hi; decide
    rw [mt, e3k i h0 h8, e2 i h1, hk1 i (by omega)]
  · rw [hcz, x12, x13]
  · rw [mt, Keep.bad k3, hcb, Keep.bad k1]

/-- A loop whose body runs twice. -/
theorem WP.loop2 {M : ISA} {b : Prog M} {c : M.Cond} {s : M.State} {Q : M.State → Prop}
    (h : WP M b s fun t => M.eval c t = some true ∧
      WP M b t fun u => M.eval c u = some false ∧ Q u) : WP M (.loop b c) s Q := by
  obtain ⟨t₁, s₁, e₁, hc₁, t₂, s₂, e₂, hc₂, q⟩ := h
  exact ⟨_, _, Exec.loopNext e₁ hc₁ (Exec.loopExit e₂ hc₂), q⟩

/-- The comparison and the result. -/
theorem vfinish_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base)
    (hb : BoundedEnv s.mem base)
    {g : Reg → BitVec 32} (hsv : Saved base g s.mem) (h12 : (word s.mem base BAD).toNat < 65536) :
    WP isa vfinish s fun t =>
      t.gpr .eax = (if word s.mem base BAD = 0 ∧
        Spec.Ed448.pointEqual (double (double (pt (E s.mem base) 0 6 2)))
          (double (double (pt (E s.mem base) 8 9 10))) = true then 1 else 0) ∧
      (∀ p ∈ savedSlots, t.gpr p.1 = g p.1) ∧ t.gpr .esp = s.gpr .esp := by
  unfold vfinish
  refine WP.seq (WP.mono (vdouble_ok hs hc hb) fun s0 ⟨k0, o0, b0, q0, r0⟩ => ?_)
  have hs0 := hs.of_keeps k0 (by decide)
  have hc0 := hc.keep (k0.1 _ (by decide))
  refine WP.seq (WP.mono (setCounter_ok s0 2 (by decide)) fun s1 ⟨e1, g1, m1, r1, w1⟩ => ?_)
  have k01 : Keeps (.esi :: workRegs) s s1 :=
    k0.trans ⟨fun r hr => g1 r (fun h => hr (by subst h; exact List.mem_cons_self)), r1, w1⟩
  have hs1 := hs.of_keeps k01 (by decide)
  have hc1 := hc.keep (k01.1 _ (by decide))
  have b1 : BoundedEnv s1.mem base := m1 ▸ b0
  refine WP.seq (WP.loop2 ?_)
  -- the `X`s
  refine WP.mono (vcmp_ok hs1 hc1 b1 (k := 1) (by decide) e1)
    fun u ⟨cu, zu, ku, ou, bu, u0, u8, uk, c, hcl, hcz, hcb⟩ => ⟨by simp only [eval, zu]; rfl, ?_⟩
  -- the `Y`s
  refine WP.mono (vcmp_ok (hs1.of_keeps ku (by decide)) (hc1.keep (ku.1 _ (by decide))) bu (k := 0)
    (by decide) cu) fun s4 ⟨_, z4, k4, o4, _, _, _, _, c', hcl', hcz', hcb'⟩ => ⟨by simp only [eval, z4]; rfl, ?_⟩
  have hs4 := (hs1.of_keeps ku (by decide)).of_keeps k4 (by decide)
  have hbad : word s4.mem base BAD = word s.mem base BAD ||| c ||| c' := by
    rw [hcb', hcb, m1, o0.word (Or.inl (by decide)) (Or.inl (by decide)) (by decide)]
  have h4 : (word s4.mem base BAD).toNat < 65536 := by
    rw [hbad, BitVec.toNat_or, BitVec.toNat_or]
    exact Nat.or_lt_two_pow (n := 16) (Nat.or_lt_two_pow (n := 16) h12 hcl) hcl'
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (isZeroBad_ok hs4 h4) fun s5 ⟨v5, m5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  have sv5 : Saved base g s5.mem := by
    rw [m5]
    exact (((hsv.wsout2 o0 (by decide) (by decide)).wsout2 (by rw [← m1]; exact ou) (by decide)
      (by decide)).wsout2 o4 (by decide) (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok hs5 sv5) fun s6 ⟨r6, m6, k6⟩ => ?_
  refine wp_mov rfl fun t ht => WP.block_nil ⟨?_, fun p hp => ?_, ?_⟩
  · rw [ht.gpr]; change s6.gpr .ecx = _
    rw [k6.1 _ (by decide), v5, hbad]
    refine if_congr ?_ rfl rfl
    have hpe : ∀ e : Env, Spec.Ed448.pointEqual (pt e 0 6 2) (pt e 8 9 10) = true ↔
        (e 0 * e 10 = e 8 * e 2 ∧ e 6 * e 10 = e 9 * e 2) := fun e => by
      simp only [Spec.Ed448.pointEqual, pt, Bool.and_eq_true, beq_iff_eq]
    refine (BitVec.or_eq_zero_iff.trans (and_congr_left fun _ => BitVec.or_eq_zero_iff)).trans ?_
    refine (and_congr (and_congr Iff.rfl hcz) hcz').trans ?_
    rw [u0, u8, uk 10 (by decide), uk 2 (by decide), m1, ← q0, ← r0, hpe]
    exact and_assoc
  · have hne : p.1 ≠ .eax := by
      simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    rw [ht.other _ hne]; exact r6 p hp
  · rw [ht.other _ (by decide), k6.1 _ (by decide), k5.1 _ (by decide), k4.1 _ (by decide),
      ku.1 _ (by decide), k01.1 _ (by decide)]

end VG.Proof.Ed448.X86
