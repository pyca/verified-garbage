import VerifiedGarbage.Proof.Ed448.X86.VerifyChecks
import VerifiedGarbage.Proof.Ed448.X86.VerifySign
import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.X448.X86.Counters

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
theorem vdoubleStep_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) {k : Nat}
    (hk : k < 2 ^ 16) (he : s.gpr .esi = BitVec.ofNat 32 (k + 1)) :
    WP isa (.seq (field (doubleAt 0 6 2 ++ doubleAt 8 9 10)) (.block [.alu .sub .esi (.imm 1)])) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 k ∧ t.zf = some (decide (k = 0)) ∧ Keeps (.esi :: workRegs) s t ∧
      Outside2 base 64 2816 ACC 512 s.mem t.mem ∧ BoundedEnv t.mem base ∧
      pt (E t.mem base) 0 6 2 = double (pt (E s.mem base) 0 6 2) ∧
      pt (E t.mem base) 8 9 10 = double (pt (E s.mem base) 8 9 10) := by
  refine field_seq _ (by decide) hs hb fun u ku bu eu => ?_
  refine WP.mono (decCounter_ok hk (by rw [ku.regs.1 _ (by decide), he])) fun t ⟨et, gt, mt, rt, wt, zt⟩ => ?_
  obtain ⟨d1, d2⟩ := double2_eval (E s.mem base)
  refine ⟨et, zt, ⟨fun r hr => ?_, rt.trans ku.regs.2.1, wt.trans ku.regs.2.2⟩, by rw [mt]; exact ku.mem,
    by rw [mt]; exact bu, by rw [mt, eu]; exact d1, by rw [mt, eu]; exact d2⟩
  rw [gt r (fun h => hr (by simp [h])), ku.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h))]

/-- `[4]Q` and `[4]R`. -/
theorem vdouble_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) :
    WP isa vdouble s fun t => Keeps (.esi :: workRegs) s t ∧ Outside2 base 64 2816 ACC 512 s.mem t.mem ∧
      BoundedEnv t.mem base ∧ pt (E t.mem base) 0 6 2 = double (double (pt (E s.mem base) 0 6 2)) ∧
      pt (E t.mem base) 8 9 10 = double (double (pt (E s.mem base) 8 9 10)) := by
  unfold vdouble
  refine WP.seq (WP.mono (setCounter_ok s 2 (by decide)) fun s₁ ⟨e₁, g₁, m₁, r₁, w₁⟩ => ?_)
  have k₁ : Keeps (.esi :: workRegs) s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), r₁, w₁⟩
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.loop (M := isa) (fun m (t : State) => 1 ≤ m ∧ m ≤ 2 ∧ t.gpr .esi = BitVec.ofNat 32 m ∧
      Keeps (.esi :: workRegs) s t ∧ Outside2 base 64 2816 ACC 512 s.mem t.mem ∧ BoundedEnv t.mem base ∧
      pt (E t.mem base) 0 6 2 = (if m = 2 then id else double) (pt (E s.mem base) 0 6 2) ∧
      pt (E t.mem base) 8 9 10 = (if m = 2 then id else double) (pt (E s.mem base) 8 9 10)) ?_ 2 s₁
    ⟨by decide, by decide, e₁, k₁, by rw [m₁]; exact Outside2.refl _ _ _ _ _ _, m₁ ▸ hb, by rw [m₁]; rfl,
      by rw [m₁]; rfl⟩
  intro m t ⟨h1, h2, et, kt, ot, bt, qt, rt⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (vdoubleStep_ok (hs.of_keeps kt (by decide)) bt (by omega) et) fun u ⟨eu, zu, ku, ou, bu, qu, ru⟩ => ?_
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
  refine WP.seq (WP.mono (vdouble_ok hs hb) fun s0 ⟨k0, o0, b0, q0, r0⟩ => ?_)
  have hs0 := hs.of_keeps k0 (by decide)
  refine field_seq [.mul 12 0 10, .mul 13 8 2] (by decide) hs0 b0 fun s1 k1 b1 e1 => ?_
  have hs1 := k1.scr hs0
  have hk : ∀ i : Index, i.val < 11 → E s1.mem base i = E s0.mem base i := fun i hi => by
    rw [e1]
    exact evalOps_keep _ _ _ fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl <;> simp only [fopDest] <;> omega
  have q1 : pt (E s1.mem base) 0 6 2 = double (double (pt (E s.mem base) 0 6 2)) := by
    rw [pt_congr' (hk 0 (by decide)) (hk 6 (by decide)) (hk 2 (by decide)), q0]
  have r1 : pt (E s1.mem base) 8 9 10 = double (double (pt (E s.mem base) 8 9 10)) := by
    rw [pt_congr' (hk 8 (by decide)) (hk 9 (by decide)) (hk 10 (by decide)), r0]
  have x12 : E s1.mem base 12 = E s1.mem base 0 * E s1.mem base 10 := by
    rw [hk 0 (by decide), hk 10 (by decide), e1]; rfl
  have x13 : E s1.mem base 13 = E s1.mem base 8 * E s1.mem base 2 := by
    rw [hk 8 (by decide), hk 2 (by decide), e1]; rfl
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
  have bad1 : word s1.mem base BAD = word s.mem base BAD :=
    (Keep.bad k1).trans (o0.word (Or.inl (by decide)) (Or.inl (by decide)) (by decide))
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
    exact ((((hsv.outside2 o0 (by decide) (by decide)).outside2 k1.mem (by decide) (by decide)).outside2 k2.mem.widen (by decide)
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
      k3.regs.1 _ (by decide), k2.regs.1 _ (by decide), k1.regs.1 _ (by decide), k0.1 _ (by decide)]
  · rw [ht.mem, m6, m5]
    exact ((((o0.whole (by decide) (by decide)).trans (k1.mem.whole (by decide) (by decide))).trans (k2.mem.widen.whole (by decide) (by decide))).trans
      (k3.mem.whole (by decide) (by decide))).trans (k4.mem.widen.whole (by decide) (by decide))

end VG.Proof.Ed448.X86
