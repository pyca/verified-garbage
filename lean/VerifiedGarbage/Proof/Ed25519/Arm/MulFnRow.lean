import VerifiedGarbage.Impl.Ed25519.Arm.MulFn
import VerifiedGarbage.Proof.X25519.Arm.Mul
import VerifiedGarbage.Proof.Ed25519.Arm.Field

/-!
# `vg_gf25519_r16_mul` on ARMv7: the rows

Untrusted: everything here is checked by Lean. The rows of `mulBody` are
X25519's (`row_ok`), but with the operands through pointers: `a_i` at `r10`,
which moves up a word a row, and `b` at `r11` (`mulRow_ok`, the invariant
`MulInv`: after `i` rows, `acc[0, i + 16)` holds the limbs of `x_{<i} · y`);
`r8` keeps the pointer to the result.
-/

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

/-- The registers the product changes. -/
abbrev mulClob : List Reg := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- After `i` rows of the product of `[x]` and `[y]` into `[o]`, from `s0`. -/
structure MulInv (e : Nat) (b : BitVec 32) (o x y : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : CtxN e b s
  rest : Rest mulClob s0 s
  r6 : s.gpr .r6 = mask16
  r7 : s.gpr .r7 = b + BitVec.ofNat 32 (4 * i)
  r8 : s.gpr .r8 = b + BitVec.ofNat 32 o
  r9 : s.gpr .r9 = BitVec.ofNat 32 (16 - i)
  r10 : s.gpr .r10 = b + BitVec.ofNat 32 (x + 4 * i)
  r11 : s.gpr .r11 = b + BitVec.ofNat 32 y
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s0.mem s.mem
  lt : ∀ k < i + 16, accw ACC s.mem (State.addr b) k < 65536
  val : val16 (accw ACC s.mem (State.addr b)) (i + 16) =
    val16 (limb s0.mem (State.addr b) x) i * V s0.mem (State.addr b) y

section
variable {e : Nat} {b : BitVec 32}

theorem addB (hfit : b.toNat + 4096 ≤ 2 ^ 32) {x d : Nat} (h : x + d < 4096) :
    State.addr (b + BitVec.ofNat 32 x + BitVec.ofNat 32 d) = State.addr b + BitVec.ofNat 64 (x + d) := by
  rw [Offset.add_add]; exact addr_add (by omega)

theorem mulSetup_ok {o x y : Nat} {s : State}
    (hc : CtxN e b s) (h1 : s.gpr .r1 = BitVec.ofNat 32 o) (h2 : s.gpr .r2 = BitVec.ofNat 32 x)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 y) :
    WP isa (.block mulSetup) s (MulInv e b o x y s 0) := by
  simp only [mulSetup, List.cons_append]
  refine wp_dp (op2_reg _ _) fun s1 u1 => wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => wp_movw fun s4 u4 => ?_
  have hr4 : Rest mulClob s s4 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans (u4.rest (by decide))))
  have hc4 : CtxN e b s4 := hc.of_rest hr4 (by decide)
  refine WP.append (zeroAcc_ok (by rw [ACC_eq]; decide) hc4) fun s5 ⟨hz, hf5, hr5⟩ => ?_
  have hc5 : CtxN e b s5 := hc4.of_rest hr5 (by decide)
  refine wp_mov (op2_reg _ _) fun s6 u6 => wp_mov (op2_imm (by decide)) fun s7 u7 => WP.block_nil ?_
  have hr7 : Rest [.r3, .r7, .r9] s4 s7 :=
    (hr5.mono (by decide)).trans ((u6.rest (by decide)).trans (u7.rest (by decide)))
  have hm7 : s7.mem = s5.mem := by rw [u7.mem, u6.mem]
  have e0 : s.gpr .r0 = b := hc.r0
  refine ⟨hc.of_rest (hr4.trans (hr7.mono (by decide))) (by decide),
    hr4.trans (hr7.mono (by decide)), ?_, ?_, ?_, u7.gpr, ?_, ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [hr7.gpr .r6 (by decide), u4.gpr]
  · rw [u7.other _ (by decide), u6.gpr, hc5.r0]; exact (BitVec.add_zero b).symm
  · rw [hr7.gpr .r8 (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.gpr, e0, h1]; rfl
  · rw [hr7.gpr .r10 (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr,
      u1.other _ (by decide), u1.other _ (by decide), e0, h2]; rfl
  · rw [hr7.gpr .r11 (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), u1.other _ (by decide), e0, h3]; rfl
  · rw [hm7, ← (show s4.mem = s.mem by rw [u4.mem, u3.mem, u2.mem, u1.mem])]
    exact hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
  · rw [accw, hm7]; unfold accw at hz; rw [hz k (by omega)]; decide
  · rw [hm7, val16_congr (g := fun _ => 0) (fun k hk => hz k hk), val16_zero_fn]
    exact (Nat.zero_mul _).symm

theorem mulRow_ok {o x y : Nat} (hx : x + 64 ≤ ACC) (hy : y + 64 ≤ ACC) {s0 : State}
    (hlx : Lim s0.mem (State.addr b) x) (hly : Lim s0.mem (State.addr b) y) {i : Nat}
    (hi : i < 16) {s : State} (h : MulInv e b o x y s0 i s) :
    WP isa (.block mulRow) s fun s' =>
      MulInv e b o x y s0 (i + 1) s' ∧ s'.z = decide (16 - (i + 1) = 0) := by
  have hA := ACC_eq
  have hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := h.ctx.fit; omega
  have hframe0 : ∀ z : Nat, z + 64 ≤ ACC → ∀ k < 16,
      limb s.mem (State.addr b) z k = limb s0.mem (State.addr b) z k := fun z hz k hk =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  simp only [mulRow, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (x + 4 * i)) (by decide)
    (by rw [h.r10, BitVec.add_zero]; exact addr_add (by omega))
    (h.ctx.inR (by omega)) fun s1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have hr2 : Rest [.r1, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : CtxN e b s2 := h.ctx.of_rest hr2 (by decide)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have e1 : (s2.gpr .r1).toNat = limb s0.mem (State.addr b) x i := by
    rw [u2.other _ (by decide), u1.gpr, ← hframe0 x hx i hi]; rfl
  have e7 : s2.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hr2.gpr _ (by decide), h.r7]
  have e11 : s2.gpr .r11 = b + BitVec.ofNat 32 y := by rw [hr2.gpr _ (by decide), h.r11]
  have P7 : State.addr (s2.gpr .r7) = State.addr b + BitVec.ofNat 64 (4 * i) := by
    rw [e7]; exact addr_add (by omega)
  have h7fit : (s2.gpr .r7).toNat + ACC + 64 ≤ 2 ^ 32 := by
    rw [e7, toNat_add_lt (by rw [toNat_imm (by omega)]; omega), toNat_imm (by omega)]; omega
  have hlt : ∀ j < 16, rowC (accw ACC s.mem (State.addr b)) (limb s0.mem (State.addr b) x)
      (limb s0.mem (State.addr b) y) i j + 65536 ≤ 2 ^ 32 := fun j hj =>
    rowC_le (hlx i hi) (hly j hj) (h.lt (i + j) (by omega))
  refine WP.append (pass_ok (rb := .r7) (o := ACC) (s0 := s2)
    (c := rowC (accw ACC s.mem (State.addr b)) (limb s0.mem (State.addr b) x) (limb s0.mem (State.addr b) y) i)
    (cin := 0) (by decide) (by omega) h7fit
    (fun k hk => by rw [P7, Offset.add_add]; exact hc2.inW (by omega))
    (by rw [hr2.gpr _ (by decide), h.r6]) (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    have hc' : CtxN e b s' := hc2.of_rest hp'.rest (by decide)
    have hf' : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [P7, Offset.add_add] at this
    simp only [mulRowSrc]
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (y + 4 * k)) (by omega)
      (by rw [hp'.rest.gpr _ (by decide), e11, addB hfit (by omega)]) (hc'.inR (by omega))
      fun t1 v1 => ?_
    refine wp_mul fun t2 v2 => ?_
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 4 * k))) (by omega)
      (by rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), e7,
        addB hfit (by omega)]) (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc'.inR (by omega))
      fun t3 v3 => ?_
    refine wp_dp (op2_reg _ _) fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have ey : (t1.gpr .r2).toNat = limb s0.mem (State.addr b) y k := by
        rw [v1.gpr, ← hframe0 y hy k hk, ← hm2]
        show wd s'.mem _ _ = wd s2.mem _ _
        exact wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      have ea : (t1.gpr .r1).toNat = limb s0.mem (State.addr b) x i := by
        rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
      have hab := Nat.mul_le_mul (Nat.le_of_lt_succ (hlx i hi)) (Nat.le_of_lt_succ (hly k hk))
      have e2 : (t2.gpr .r2).toNat = limb s0.mem (State.addr b) x i * limb s0.mem (State.addr b) y k := by
        rw [v2.gpr, toNat_mul_lt (by rw [ea, ey]; omega), ea, ey]
      have e3 : (t3.gpr .r3).toNat = accw ACC s.mem (State.addr b) (i + k) := by
        rw [v3.gpr, v2.mem, v1.mem, accw, ← hm2]
        show wd s'.mem _ _ = _
        rw [wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)]
        congr 1; omega
      have := hlt k hk
      rw [v4.gpr]
      show (t3.gpr .r3 + t3.gpr .r2).toNat = _
      rw [v3.other .r2 (by decide), toNat_add_lt (by rw [e3, e2]; simp only [rowC] at this; omega), e3, e2,
        rowC, Nat.add_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · -- The carry, and the next row.
    have hc3 : CtxN e b s3 := hc2.of_rest hp.rest (by decide)
    have e7' : s3.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hp.rest.gpr _ (by decide), e7]
    refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 64))) (by omega)
      (by rw [e7', addB hfit (by omega)]) (hc3.inW (by omega)) fun s4 u4 => ?_
    refine wp_dp (op2_imm (by decide)) fun s5 u5 => wp_dp (op2_imm (by decide)) fun s5' u5' => ?_
    refine wp_subs (op2_imm (by decide)) fun s6 u6 hz => ?_
    refine WP.block_nil ?_
    have hr6 : Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9, .r10] s s6 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans ((u5'.rest (by decide)).trans (u6.rest (by decide))))))
    have hm6 : s6.mem = s3.mem.writeW (State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 64))) (s3.gpr .r5) := by
      rw [u6.mem, u5'.mem, u5.mem, u4.mem]
    have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 64⟩] s.mem s3.mem := by
      have := hp.frame; rw [P7, Offset.add_add] at this; rw [← hm2]; exact this
    have t1 : (1 : BitVec 32).toNat = 1 := rfl
    have hr9 : s6.gpr .r9 = BitVec.ofNat 32 (16 - (i + 1)) := by
      rw [u6.gpr, u5'.other _ (by decide), u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide),
        hr2.gpr _ (by decide), h.r9]
      apply BitVec.eq_of_toNat_eq
      rw [toNat_sub_le (by rw [toNat_imm (by omega), t1]; omega), toNat_imm (by omega), toNat_imm (by omega),
        t1]
      omega
    -- The limbs of `ACC` after the row.
    have hacc : ∀ k < i + 17, accw ACC s6.mem (State.addr b) k =
        rowAcc (accw ACC s.mem (State.addr b)) (limb s0.mem (State.addr b) x) (limb s0.mem (State.addr b) y) i k := by
      intro k hk
      rw [accw, hm6]
      rcases Nat.lt_or_ge k (i + 16) with hk' | hk'
      · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
        rcases Nat.lt_or_ge k i with hki | hki
        · rw [wd_frame hpf fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)]
          simp only [rowAcc, hki, ite_true]; rfl
        · have := hp.outs (k - i) (by omega)
          rw [P7, wd_shift, show 4 * i + (ACC + 4 * (k - i)) = ACC + 4 * k by omega] at this
          rw [this]
          simp only [rowAcc, show ¬ k < i by omega, hk', ite_false, ite_true]
      · rw [show ACC + 4 * k = 4 * i + (ACC + 64) by omega, wd_write_self, hp.r5]
        simp only [rowAcc, show ¬ k < i by omega, show ¬ k < i + 16 by omega, ite_false]
    refine ⟨⟨hc3.of_rest ((u4.rest [.r7, .r9, .r10]).trans ((u5.rest (by decide)).trans
        ((u5'.rest (by decide)).trans (u6.rest (by decide))))) (by decide),
      h.rest.trans (hr6.mono (by decide)), by rw [hr6.gpr _ (by decide), h.r6], ?_,
      by rw [hr6.gpr _ (by decide), h.r8], hr9, ?_, by rw [hr6.gpr _ (by decide), h.r11], ?_,
      fun k hk => ?_, ?_⟩, ?_⟩
    · rw [u6.other _ (by decide), u5'.other _ (by decide), u5.gpr, u4.gpr, e7']
      show b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _
      rw [Offset.add_add, Nat.mul_succ]
    · rw [u6.other _ (by decide), u5'.gpr, u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide),
        hr2.gpr _ (by decide), h.r10]
      show b + BitVec.ofNat 32 (x + 4 * i) + BitVec.ofNat 32 4 = _
      rw [Offset.add_add, Nat.mul_succ, Nat.add_assoc]
    · rw [hm6]
      refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
    · rw [hacc k hk]
      exact rowAcc_lt (fun k hk => h.lt k (by omega)) hlt k hk
    · rw [val16_congr hacc]; exact row_val h.val
    · rw [hz, ← u6.gpr, hr9, ofNat_beq_zero (by omega)]

end

end VG.Proof.Ed25519.Arm
