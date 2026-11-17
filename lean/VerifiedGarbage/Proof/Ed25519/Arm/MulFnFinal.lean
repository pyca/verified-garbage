module

import VerifiedGarbage.Proof.Ed25519.Arm.Field
import VerifiedGarbage.Proof.X25519.Arm.Pass
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ed25519.Arm.MulFn
public import VerifiedGarbage.Proof.X25519.Arm.Mul

/-! ### `Ed25519.Arm.MulFnRow`, which this module and modules that import it used -/

section

/-!
# `vg_gf25519_r16_mul` on ARMv7: the rows

Untrusted: everything here is checked by Lean. The rows of `mulBody` are
X25519's (`row_ok`), but with the operands through pointers: `a_i` at `r10`,
which moves up a word a row, and `b` at `r11` (`mulRow_ok`, the invariant
`MulInv`: after `i` rows, `acc[0, i + 16)` holds the limbs of `x_{<i} · y`);
`r8` keeps the pointer to the result.
-/

@[expose] public section

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
  rw [Offset.add_add]; exact addr_add (by omega_using [hfit, h])

theorem mulSetup_ok {o x y : Nat} {s : State}
    (hc : CtxN e b s) (h1 : s.gpr .r1 = BitVec.ofNat 32 o) (h2 : s.gpr .r2 = BitVec.ofNat 32 x)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 y) :
    WP isa (.block mulSetup) s (MulInv e b o x y s 0) := by
  simp only [mulSetup, List.cons_append]
  refine wp_dp (op2_reg _ _) fun s1 u1 => wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => wp_movw fun s4 u4 => ?_
  obtain hr4 : Rest mulClob s s4 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans (u4.rest (by decide))))
  obtain hc4 : CtxN e b s4 := hc.of_rest hr4 (by decide)
  refine WP.append (zeroAcc_ok (by rw [ACC_eq]; decide) hc4) fun s5 ⟨hz, hf5, hr5⟩ => ?_
  obtain hc5 : CtxN e b s5 := hc4.of_rest hr5 (by decide)
  refine wp_mov (op2_reg _ _) fun s6 u6 => wp_mov (op2_imm (by decide)) fun s7 u7 => WP.block_nil ?_
  obtain hr7 : Rest [.r3, .r7, .r9] s4 s7 :=
    (hr5.mono (by decide)).trans ((u6.rest (by decide)).trans (u7.rest (by decide)))
  obtain hm7 : s7.mem = s5.mem := by rw [u7.mem, u6.mem]
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
  · rw [accw, hm7]; unfold accw at hz; rw [hz k (by omega_using [hk])]; decide
  · rw [hm7, val16_congr (g := fun _ => 0) (fun k hk => hz k hk), val16_zero_fn]
    exact (Nat.zero_mul _).symm

theorem mulRow_ok {o x y : Nat} (hx : x + 64 ≤ ACC) (hy : y + 64 ≤ ACC) {s0 : State}
    (hlx : Lim s0.mem (State.addr b) x) (hly : Lim s0.mem (State.addr b) y) {i : Nat}
    (hi : i < 16) {s : State} (h : MulInv e b o x y s0 i s) :
    WP isa (.block mulRow) s fun s' =>
      MulInv e b o x y s0 (i + 1) s' ∧ s'.z = decide (16 - (i + 1) = 0) := by
  have hA := ACC_eq
  obtain hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := h.ctx.fit; omega_arith
  obtain hframe0 : ∀ z : Nat, z + 64 ≤ ACC → ∀ k < 16,
      limb s.mem (State.addr b) z k = limb s0.mem (State.addr b) z k := fun z hz k hk =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  simp only [mulRow, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (x + 4 * i)) (by decide)
    (by rw [h.r10, BitVec.add_zero]; exact addr_add (by omega_arith))
    (h.ctx.inR (by omega_arith)) fun s1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  obtain hr2 : Rest [.r1, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hc2 : CtxN e b s2 := h.ctx.of_rest hr2 (by decide)
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  obtain e1 : (s2.gpr .r1).toNat = limb s0.mem (State.addr b) x i := by
    rw [u2.other _ (by decide), u1.gpr, ← hframe0 x hx i hi]; rfl
  obtain e7 : s2.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hr2.gpr _ (by decide), h.r7]
  obtain e11 : s2.gpr .r11 = b + BitVec.ofNat 32 y := by rw [hr2.gpr _ (by decide), h.r11]
  obtain P7 : State.addr (s2.gpr .r7) = State.addr b + BitVec.ofNat 64 (4 * i) := by
    rw [e7]; exact addr_add (by omega_arith)
  obtain h7fit : (s2.gpr .r7).toNat + ACC + 64 ≤ 2 ^ 32 := by
    rw [e7, toNat_add_lt (by rw [toNat_imm (by omega_arith)]; omega_arith), toNat_imm (by omega_arith)]; omega_arith
  obtain hlt : ∀ j < 16, rowC (accw ACC s.mem (State.addr b)) (limb s0.mem (State.addr b) x)
      (limb s0.mem (State.addr b) y) i j + 65536 ≤ 2 ^ 32 := fun j hj =>
    rowC_le (hlx i hi) (hly j hj) (h.lt (i + j) (by omega_arith))
  refine WP.append (pass_ok (rb := .r7) (o := ACC) (s0 := s2)
    (c := rowC (accw ACC s.mem (State.addr b)) (limb s0.mem (State.addr b) x) (limb s0.mem (State.addr b) y) i)
    (cin := 0) (by decide) (by omega_arith) h7fit
    (fun k hk => by rw [P7, Offset.add_add]; exact hc2.inW (by omega_arith))
    (by rw [hr2.gpr _ (by decide), h.r6]) (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    obtain hc' : CtxN e b s' := hc2.of_rest hp'.rest (by decide)
    obtain hf' : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [P7, Offset.add_add] at this
    simp only [mulRowSrc]
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (y + 4 * k)) (by omega_arith)
      (by rw [hp'.rest.gpr _ (by decide), e11, addB hfit (by omega_arith)]) (hc'.inR (by omega_arith))
      fun t1 v1 => ?_
    refine wp_mul fun t2 v2 => ?_
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 4 * k))) (by omega_arith)
      (by rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), e7,
        addB hfit (by omega_arith)]) (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc'.inR (by omega_arith))
      fun t3 v3 => ?_
    refine wp_dp (op2_reg _ _) fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have ey : (t1.gpr .r2).toNat = limb s0.mem (State.addr b) y k := by
        rw [v1.gpr, ← hframe0 y hy k hk, ← hm2]
        show wd s'.mem _ _ = wd s2.mem _ _
        exact wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      obtain ea : (t1.gpr .r1).toNat = limb s0.mem (State.addr b) x i := by
        rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
      obtain hab := Nat.mul_le_mul (Nat.le_of_lt_succ (hlx i hi)) (Nat.le_of_lt_succ (hly k hk))
      obtain e2 : (t2.gpr .r2).toNat = limb s0.mem (State.addr b) x i * limb s0.mem (State.addr b) y k := by
        rw [v2.gpr, toNat_mul_lt (by rw [ea, ey]; omega_arith), ea, ey]
      obtain e3 : (t3.gpr .r3).toNat = accw ACC s.mem (State.addr b) (i + k) := by
        rw [v3.gpr, v2.mem, v1.mem, accw, ← hm2]
        show wd s'.mem _ _ = _
        rw [wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)]
        congr 1; omega_arith
      have := hlt k hk
      rw [v4.gpr]
      show (t3.gpr .r3 + t3.gpr .r2).toNat = _
      rw [v3.other .r2 (by decide), toNat_add_lt (by rw [e3, e2]; simp only [rowC] at this; omega_arith), e3, e2,
        rowC, Nat.add_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · -- The carry, and the next row.
    obtain hc3 : CtxN e b s3 := hc2.of_rest hp.rest (by decide)
    obtain e7' : s3.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hp.rest.gpr _ (by decide), e7]
    refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 64))) (by omega_arith)
      (by rw [e7', addB hfit (by omega_arith)]) (hc3.inW (by omega_arith)) fun s4 u4 => ?_
    refine wp_dp (op2_imm (by decide)) fun s5 u5 => wp_dp (op2_imm (by decide)) fun s5' u5' => ?_
    refine wp_subs (op2_imm (by decide)) fun s6 u6 hz => ?_
    refine WP.block_nil ?_
    obtain hr6 : Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9, .r10] s s6 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans ((u5'.rest (by decide)).trans (u6.rest (by decide))))))
    obtain hm6 : s6.mem = s3.mem.writeW (State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 64))) (s3.gpr .r5) := by
      rw [u6.mem, u5'.mem, u5.mem, u4.mem]
    obtain hpf : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 64⟩] s.mem s3.mem := by
      have := hp.frame; rw [P7, Offset.add_add] at this; rw [← hm2]; exact this
    have t1 : (1 : BitVec 32).toNat = 1 := rfl
    obtain hr9 : s6.gpr .r9 = BitVec.ofNat 32 (16 - (i + 1)) := by
      rw [u6.gpr, u5'.other _ (by decide), u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide),
        hr2.gpr _ (by decide), h.r9]
      apply BitVec.eq_of_toNat_eq
      rw [toNat_sub_le (by rw [toNat_imm (by omega_arith), t1]; omega_arith), toNat_imm (by omega_arith), toNat_imm (by omega_arith),
        t1]
      omega_arith
    -- The limbs of `ACC` after the row.
    obtain hacc : ∀ k < i + 17, accw ACC s6.mem (State.addr b) k =
        rowAcc (accw ACC s.mem (State.addr b)) (limb s0.mem (State.addr b) x) (limb s0.mem (State.addr b) y) i k := by
      intro k hk
      rw [accw, hm6]
      rcases Nat.lt_or_ge k (i + 16) with hk' | hk'
      · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
        rcases Nat.lt_or_ge k i with hki | hki
        · rw [wd_frame hpf fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)]
          simp only [rowAcc, hki, ite_true]; rfl
        · have := hp.outs (k - i) (by omega_arith)
          rw [P7, wd_shift, show 4 * i + (ACC + 4 * (k - i)) = ACC + 4 * k by omega_arith] at this
          rw [this]
          simp only [rowAcc, show ¬ k < i by omega_arith, hk', ite_false, ite_true]
      · rw [show ACC + 4 * k = 4 * i + (ACC + 64) by omega_arith, wd_write_self, hp.r5]
        simp only [rowAcc, show ¬ k < i by omega_arith, show ¬ k < i + 16 by omega_arith, ite_false]
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
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [hacc k hk]
      exact rowAcc_lt (fun k hk => h.lt k (by omega_arith)) hlt k hk
    · rw [val16_congr hacc]; exact row_val h.val
    · rw [hz, ← u6.gpr, hr9, ofNat_beq_zero (by omega_arith)]

end

end VG.Proof.Ed25519.Arm

end

end

/-!
# `vg_gf25519_r16_mul` on ARMv7: the result

Untrusted: everything here is checked by Lean. After the rows, `mulFinal`
stores `lo + 38 hi` at the result through `r9` and folds the carry out in
twice (`mulFinal_ok`), as X25519's `passTail'_ok` and `tail_ok` do at an
offset of `r0`; the product of `mulBody` (`mulBody_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Impl.X25519.Arm (mulSrc)
open VG.Spec.X25519 (P)

section
variable {e : Nat} {b : BitVec 32}

theorem addrO' (hfit : b.toNat + 4096 ≤ 2 ^ 32) {o : Nat} (h : o < 4096) :
    State.addr (b + BitVec.ofNat 32 o) = State.addr b + BitVec.ofNat 64 o := addr_add (by omega_using [hfit, h])

/-- The carry out of the result at `r9`, in `r5`, folded in as 38 times itself, twice. -/
theorem tail9_ok {o : Nat} (ho : o + 64 ≤ ACC) {s : State} (hc : CtxN e b s)
    (h9 : s.gpr .r9 = b + BitVec.ofNat 32 o)
    (h6 : s.gpr .r6 = mask16) (h8 : s.gpr .r8 = 38) {c16 : Nat} (h5 : (s.gpr .r5).toNat = c16)
    (hc16 : c16 ≤ 38) (hl : Lim s.mem (State.addr b) o) :
    WP isa (.block (([.mul .r5 .r5 .r8] : List Instr) ++ pass .r9 0 mulTailSrc ++
      ([.mul .r5 .r5 .r8, .ldr .r3 .r9 0, .dp .add .r3 .r3 (.reg .r5), .str .r3 .r9 0] : List Instr))) s
      fun s' => Rest [.r2, .r3, .r4, .r5] s s' ∧
        Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧ Lim s'.mem (State.addr b) o ∧
        V s'.mem (State.addr b) o % P = (V s.mem (State.addr b) o + 2 ^ 256 * c16) % P := by
  have hA := ACC_eq
  obtain hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := hc.fit; omega_using [this]
  have t38 : (38 : BitVec 32).toNat = 38 := rfl
  obtain B9 : State.addr (b + BitVec.ofNat 32 o) = State.addr b + BitVec.ofNat 64 o := addrO' hfit (by omega_using [ho, hA])
  simp only [List.cons_append, List.nil_append]
  refine wp_mul fun s1 u1 => ?_
  obtain e1 : (s1.gpr .r5).toNat = 38 * c16 := by
    rw [u1.gpr, h8, toNat_mul_lt (by rw [h5, t38]; omega_using [hc16]), h5, t38]; omega_using []
  obtain hc1 : CtxN e b s1 := hc.of_rest (u1.rest (ws := [.r5]) (by decide)) (by decide)
  obtain e9 : s1.gpr .r9 = b + BitVec.ofNat 32 o := by rw [u1.other _ (by decide), h9]
  refine WP.append (pass_ok (rb := .r9) (s0 := s1) (o := 0) (c := limb s.mem (State.addr b) o)
    (cin := 38 * c16) (by decide) (by decide)
    (by rw [e9, toNat_add_lt (by rw [toNat_imm (by omega_using [ho, hA])]; omega_using [ho, hA, hfit]), toNat_imm (by omega_using [ho, hA])]; omega_using [ho, hA, hfit])
    (fun k hk => by rw [e9, B9, Offset.add_add]; exact hc1.inW (by omega_using [ho, hA, hk]))
    (by rw [u1.other _ (by decide), h6]) e1 (fun k hk => by have := hl k hk; omega_using [this]) (by omega_using [hc16])
    (fun k hk s' hp => ?_)) fun s2 hp => ?_
  · refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (o + 4 * k)) (by omega_using [hk])
      (by rw [hp.rest.gpr _ (by decide), e9, addB hfit (by omega_using [ho, hA, hk])])
      (by rw [hp.rest.rd, hp.rest.wr, u1.rd, u1.wr]; exact hc.inR (by omega_using [ho, hA, hk])) fun s'' u => ?_
    refine WP.block_nil ⟨?_, u.rest (by decide), u.mem⟩
    rw [u.gpr]
    show wd s'.mem _ _ = _
    rw [← u1.mem]
    refine wd_frame hp.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr, e9, B9, Offset.add_add]
    exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [ho, hA, hk]) (by omega_using [ho, hA, hk])
  · have hc2 : CtxN e b s2 := hc1.of_rest hp.rest (by decide)
    obtain ht := tail_facts hl hc16
    obtain hpo : ∀ j < 16, wd s2.mem (State.addr b) (o + 4 * j) =
        out (limb s.mem (State.addr b) o) (38 * c16) j := fun j hj => by
      have := hp.outs j hj; rwa [e9, B9, wd_shift, Nat.zero_add] at this
    obtain hpf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * 16⟩] s1.mem s2.mem := by
      have := hp.frame; rwa [e9, B9, BitVec.add_zero] at this
    obtain e9' : s2.gpr .r9 = b + BitVec.ofNat 32 o := by rw [hp.rest.gpr _ (by decide), e9]
    refine wp_mul fun s3 u3 => ?_
    obtain e3 : (s3.gpr .r5).toNat = 38 * chain (limb s.mem (State.addr b) o) (38 * c16) 16 := by
      rw [u3.gpr, hp.rest.gpr .r8 (by decide), u1.other .r8 (by decide), h8,
        toNat_mul_lt (by rw [hp.r5, t38]; have := ht.1; omega_using [this]), hp.r5, t38]; omega_using []
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 o) (by decide)
      (by rw [u3.other _ (by decide), e9', BitVec.add_zero, B9])
      (by rw [u3.rd, u3.wr]; exact hc2.inR (by omega_using [ho, hA])) fun s4 u4 => ?_
    refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
    obtain e9'' : s5.gpr .r9 = b + BitVec.ofNat 32 o := by
      rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), e9']
    refine wp_str (a := State.addr b + BitVec.ofNat 64 o) (by decide)
      (by rw [e9'', BitVec.add_zero, B9])
      (by rw [u5.wr, u4.wr, u3.wr]; exact hc2.inW (by omega_using [ho, hA])) fun s6 u6 => WP.block_nil ?_
    obtain w0 : s3.mem.readW (State.addr b + BitVec.ofNat 64 o) 32 =
        s2.mem.readW (State.addr b + BitVec.ofNat 64 o) 32 := by
      rw [u3.mem]
    obtain e5 : (s5.gpr .r3).toNat = tailL (limb s.mem (State.addr b) o) c16 0 := by
      rw [u5.gpr]
      show (s4.gpr .r3 + s4.gpr .r5).toNat = _
      rw [u4.gpr, u4.other .r5 (by decide), w0]
      obtain o0 := hpo 0 (by decide)
      rw [Nat.mul_zero, Nat.add_zero] at o0
      obtain h0 := ht.2.1 0 (by decide)
      simp only [tailL, ite_true] at h0 ⊢
      rw [toNat_add_lt (by rw [e3]; unfold wd at o0; rw [o0]; omega_using [h0]), e3]
      unfold wd at o0; rw [o0]
    obtain hm6 : s6.mem = s2.mem.writeW (State.addr b + BitVec.ofNat 64 o) (s5.gpr .r3) := by
      rw [u6.mem, u5.mem, u4.mem, u3.mem]
    obtain hlimb : ∀ k < 16, limb s6.mem (State.addr b) o k = tailL (limb s.mem (State.addr b) o) c16 k := by
      intro k hk
      rw [limb, hm6]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [Nat.mul_zero, Nat.add_zero, wd_write_self, e5]
      · rw [wd_write_other _ _ _ (by omega_using [hk0]) (by omega_using [ho, hA, hk]) (by omega_using [ho, hA]), hpo k hk]
        simp only [tailL, show k ≠ 0 by omega_using [hk0], ite_false]
    refine ⟨?_, ?_, fun k hk => by rw [hlimb k hk]; exact ht.2.1 k hk, ?_⟩
    · refine (u1.rest (ws := [.r2, .r3, .r4, .r5]) (by decide)).trans (hp.rest.trans ?_)
      refine (u3.rest (by decide)).trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ?_))
      exact u6.rest _
    · rw [hm6]
      refine (?_ : Frame _ s.mem s2.mem).writeW (List.mem_singleton_self _) _
        (Offset.contains (State.addr b) (d := o) (n := 4) (e := o) (k := 64) (Nat.le_refl _)
          (by omega_using []) (by omega_using [ho, hA]))
      rw [← u1.mem]
      exact hpf
    · rw [V, val16_congr hlimb, ht.2.2]; rfl

/-- After the rows: the result at `o`, below `2^16` limb by limb and congruent to the product. -/
theorem mulFinal_ok {o x y : Nat} (ho : o + 64 ≤ ACC) {s0 s : State} (h : MulInv e b o x y s0 16 s) :
    WP isa (.block mulFinal) s fun t =>
      Rest mulClob s0 t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o % P = val16 (accw ACC s.mem (State.addr b)) 32 % P := by
  have hA := ACC_eq
  obtain hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := h.ctx.fit; omega_using [this]
  obtain B9 : State.addr (b + BitVec.ofNat 32 o) = State.addr b + BitVec.ofNat 64 o := addrO' hfit (by omega_using [ho, hA])
  simp only [mulFinal, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  obtain hr3 : Rest [.r5, .r8, .r9] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  obtain hc3 : CtxN e b s3 := h.ctx.of_rest hr3 (by decide)
  obtain hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  obtain e9 : s3.gpr .r9 = b + BitVec.ofNat 32 o := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, h.r8]
  obtain e8 : s3.gpr .r8 = 38 := by rw [u3.other _ (by decide), u2.gpr]
  obtain e6 : s3.gpr .r6 = mask16 := by rw [hr3.gpr _ (by decide), h.r6]
  have hl32 : ∀ k < 32, accw ACC s.mem (State.addr b) k < 65536 := h.lt
  obtain ff := fold_facts hl32
  refine WP.append (pass_ok (rb := .r9) (s0 := s3) (o := 0) (c := foldC (accw ACC s.mem (State.addr b)))
    (cin := 0) (by decide) (by decide)
    (by rw [e9, toNat_add_lt (by rw [toNat_imm (by omega_using [ho, hA])]; omega_using [ho, hA, hfit]), toNat_imm (by omega_using [ho, hA])]; omega_using [ho, hA, hfit])
    (fun k hk => by rw [e9, B9, Offset.add_add]; exact hc3.inW (by omega_using [ho, hA, hk]))
    e6 (by rw [u3.gpr]; rfl) (foldC_le hl32) (by decide) (fun k hk s' hp => ?_)) fun s4 hp => ?_
  · have hc' : CtxN e b s' := hc3.of_rest hp.rest (by decide)
    refine ldr0_ok hc' (d := ACC + 4 * k) (by omega_using [hA, hk]) fun t1 v1 => ?_
    refine ldr0_ok (hc'.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide)) (d := ACC + 64 + 4 * k)
      (by omega_using [hA, hk]) fun t2 v2 => ?_
    refine wp_mul fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have hpf : ∀ d, o + 64 ≤ d → d + 4 ≤ 4096 → wd s'.mem (State.addr b) d = wd s3.mem (State.addr b) d :=
        fun d hd hd' => wd_frame hp.frame fun r hr => by
          rw [List.mem_singleton.mp hr, e9, B9, BitVec.add_zero]
          exact Offset.disjoint _ (.inr (by omega_using [hk, hd])) (by omega_using [hd']) (by omega_using [ho, hA, hk])
      obtain el : (t1.gpr .r3).toNat = accw ACC s.mem (State.addr b) k := by
        rw [v1.gpr]; show wd s'.mem _ _ = _
        rw [hpf _ (by omega_using [ho]) (by omega_using [hA, hk]), hm3]; rfl
      obtain eh : (t2.gpr .r2).toNat = accw ACC s.mem (State.addr b) (16 + k) := by
        rw [v2.gpr, v1.mem]; show wd s'.mem _ _ = _
        rw [hpf _ (by omega_using [ho]) (by omega_using [hA, hk]), hm3, accw]
        congr 1; omega_using []
      obtain h8 : t2.gpr .r8 = 38 := by
        rw [v2.other _ (by decide), v1.other _ (by decide), hp.rest.gpr _ (by decide), e8]
      obtain hh := hl32 (16 + k) (by omega_using [hk])
      obtain hl := hl32 k (by omega_using [hk])
      obtain e3 : (t3.gpr .r2).toNat = accw ACC s.mem (State.addr b) (16 + k) * 38 := by
        rw [v3.gpr, h8, toNat_mul_lt (by rw [eh]; show _ * 38 < _; omega_using [hh]), eh]; rfl
      rw [v4.gpr]
      show (t3.gpr .r3 + t3.gpr .r2).toNat = _
      rw [v3.other .r3 (by decide), v2.other .r3 (by decide), toNat_add_lt (by rw [el, e3]; omega_using [hh, hl]), el,
        e3, foldC, Nat.mul_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · have hc4 : CtxN e b s4 := hc3.of_rest hp.rest (by decide)
    obtain hpo : ∀ j < 16, wd s4.mem (State.addr b) (o + 4 * j) =
        out (foldC (accw ACC s.mem (State.addr b))) 0 j := fun j hj => by
      have := hp.outs j hj; rwa [e9, B9, wd_shift, Nat.zero_add] at this
    obtain hpf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s3.mem s4.mem := by
      have := hp.frame; rwa [e9, B9, BitVec.add_zero] at this
    obtain hl4 : Lim s4.mem (State.addr b) o := fun k hk => by rw [limb, hpo k hk]; exact out_lt _ _ _
    refine WP.mono (tail9_ok ho hc4 (by rw [hp.rest.gpr _ (by decide), e9])
      (by rw [hp.rest.gpr _ (by decide), e6]) (by rw [hp.rest.gpr _ (by decide), e8]) hp.r5 ff.1 hl4)
      fun t ⟨hrt, hft, hlt, hvt⟩ => ⟨?_, ?_, hlt, ?_⟩
    · exact h.rest.trans ((hr3.mono (by decide)).trans ((hp.rest.mono (by decide)).trans
        (hrt.mono (by decide))))
    · rw [← hm3]; exact hpf.trans hft
    · rw [hvt, V, val16_congr (f := limb s4.mem (State.addr b) o)
        (g := out (foldC (accw ACC s.mem (State.addr b))) 0) (fun k hk => hpo k hk)]
      exact ff.2

/-- The product of `[x]` and `[y]` into `[o]`, the offsets in `r1`–`r3`. -/
theorem mulBody_ok {o x y : Nat} (ho : o + 64 ≤ ACC) (hx : x + 64 ≤ ACC) (hy : y + 64 ≤ ACC)
    {s : State} (hc : CtxN e b s) (h1 : s.gpr .r1 = BitVec.ofNat 32 o) (h2 : s.gpr .r2 = BitVec.ofNat 32 x)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 y) (hlx : Lim s.mem (State.addr b) x)
    (hly : Lim s.mem (State.addr b) y) :
    WP isa mulBody s fun t =>
      Rest mulClob s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o % P = (V s.mem (State.addr b) x * V s.mem (State.addr b) y) % P := by
  unfold mulBody
  refine WP.seq (WP.mono (mulSetup_ok (o := o) (x := x) (y := y) hc h1 h2 h3) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (Q := MulInv e b o x y s 16) (WP.loop (M := isa)
    (fun n s' => ∃ i, n = 16 - i ∧ i < 16 ∧ MulInv e b o x y s i s') ?_ 16 s1 ⟨0, rfl, by decide, h1⟩)
    fun s2 h2 => ?_)
  · rintro n s' ⟨i, rfl, hi, hr⟩
    refine WP.mono (mulRow_ok hx hy hlx hly hi hr) fun s'' ⟨hr', hz⟩ => ?_
    by_cases h16 : i + 1 = 16
    · refine .inl ⟨by rw [eval_ne, hz]; simp [h16], ?_⟩
      rw [h16] at hr'; exact hr'
    · exact .inr ⟨by rw [eval_ne, hz]; simp; omega_using [hi, h16], 16 - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, h16], hr'⟩
  · refine WP.mono (mulFinal_ok ho h2) fun t ⟨hrt, hft, hlt, hvt⟩ => ⟨hrt, ?_, hlt, ?_⟩
    · exact (h2.frame.mono fun r hr => by simp [List.mem_singleton.mp hr]).trans
        (hft.mono fun r hr => by simp [List.mem_singleton.mp hr])
    · rw [hvt, show (32 : Nat) = 16 + 16 from rfl, h2.val]; rfl

end

end VG.Proof.Ed25519.Arm
