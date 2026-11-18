module

public import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
public import VerifiedGarbage.Proof.X25519.X86_64.Env
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Steps
public import VerifiedGarbage.Impl.X25519.X86_64.Adx
public import VerifiedGarbage.Proof.X25519.X86_64.Ops
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! ### `X25519.X86_64.Adx.Sqr`, which this module and modules that import it used -/

section

/-! ### `X25519.X86_64.Adx.Mul`, which this module and modules that import it used -/

section

/-!
# X25519 on x86-64: multiplication with BMI2 and ADX

The product's rows (`mul4_ok`, `MulProd.lean`), the reduction (`reduceX`), and
the multiplication `mulX o a b`, as `mul_ok` states `mul`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-! ## The reduction -/

theorem reduceLo_eq : reduceLo = ([.mov32 .rdx (.imm 38)] : List Instr) ++ (([clear] : List Instr) ++
    (madd .r8 .r9 (.reg .r12) ++ (madd .r9 .r10 (.reg .r13) ++ (madd .r10 .r11 (.reg .r14) ++
      maddLast .r11 .r12 (.reg .r15))))) := by
  simp only [reduceLo, List.append_assoc]; rfl

/-- `r8–r11 + 2²⁵⁶ r12 = r8–r11 + 38 · r12–r15`, with `r12 < 39` and `rdx = 38`. -/
theorem reduceLo_ok (s : State) :
    WP isa (.block reduceLo) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * (s'.gpr .r12).toNat =
        val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) ∧
      (s'.gpr .r12).toNat < 39 ∧ (s'.gpr .rdx).toNat = 38 ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [reduceLo_eq, WP.block_append_iff]
  refine WP.mono (movRdxImm_ok s 38) fun s1 ⟨d1, _, _, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (clear_ok s1) fun s2 ⟨z2, c2, o2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s2 rfl (noImm_reg _) c2 o2 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s3 ⟨c3, o3, hc3, ho3, e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s3 rfl (noImm_reg _) hc3 ho3 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s4 ⟨c4, o4, hc4, ho4, e4, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s4 rfl (noImm_reg _) hc4 ho4 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s5 ⟨c5, o5, hc5, ho5, e5, k5⟩ => ?_
  have z5 : s5.gpr .rbp = 0 := by
    rw [k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide), z2]
  refine WP.mono (maddLast_ok s5 rfl (noImm_reg _) hc5 ho5 z5 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s6 ⟨c6, o6, _, _, e6, k6⟩ => ?_
  -- `rdx = 38` along the way.
  have D : ∀ x : State, x.gpr .rdx = s1.gpr .rdx → (x.gpr .rdx).toNat = 38 := fun x h => h ▸ d1
  have D2 := D s2 (k2.1 _ (by decide))
  have D3 := D s3 ((k3.1 _ (by decide)).trans (k2.1 _ (by decide)))
  have D4 := D s4 ((k4.1 _ (by decide)).trans ((k3.1 _ (by decide)).trans (k2.1 _ (by decide))))
  have D5 := D s5 ((k5.1 _ (by decide)).trans ((k4.1 _ (by decide)).trans
    ((k3.1 _ (by decide)).trans (k2.1 _ (by decide)))))
  have D6 := D s6 ((k6.1 _ (by decide)).trans ((k5.1 _ (by decide)).trans ((k4.1 _ (by decide)).trans
    ((k3.1 _ (by decide)).trans (k2.1 _ (by decide))))))
  rw [D2, k2.1 .r12 (by decide), k1.1 .r12 (by decide), k2.1 .r8 (by decide), k1.1 .r8 (by decide),
    k2.1 .r9 (by decide), k1.1 .r9 (by decide)] at e3
  rw [D3, k3.1 .r13 (by decide), k2.1 .r13 (by decide), k1.1 .r13 (by decide),
    k3.1 .r10 (by decide), k2.1 .r10 (by decide), k1.1 .r10 (by decide)] at e4
  rw [D4, k4.1 .r14 (by decide), k3.1 .r14 (by decide), k2.1 .r14 (by decide),
    k1.1 .r14 (by decide), k4.1 .r11 (by decide), k3.1 .r11 (by decide), k2.1 .r11 (by decide),
    k1.1 .r11 (by decide)] at e5
  rw [D5, k5.1 .r15 (by decide), k4.1 .r15 (by decide), k3.1 .r15 (by decide),
    k2.1 .r15 (by decide), k1.1 .r15 (by decide)] at e6
  simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e3
  have hB : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
      38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) < 39 * 2 ^ 256 := by
    simp only [val4]
    have := (s.gpr .r8).isLt; have := (s.gpr .r9).isLt; have := (s.gpr .r10).isLt
    have := (s.gpr .r11).isLt; have := (s.gpr .r12).isLt; have := (s.gpr .r13).isLt
    have := (s.gpr .r14).isLt; have := (s.gpr .r15).isLt
    omega_arith
  have hv : val4 (s6.gpr .r8) (s6.gpr .r9) (s6.gpr .r10) (s6.gpr .r11) +
      2 ^ 256 * (s6.gpr .r12).toNat =
        val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) := by
    rw [k6.1 .r8 (by decide), k5.1 .r8 (by decide), k4.1 .r8 (by decide), k6.1 .r9 (by decide),
      k5.1 .r9 (by decide), k6.1 .r10 (by decide)]
    simp only [val4] at hB ⊢
    have := (s6.gpr .r11).isLt; have := (s6.gpr .r12).isLt
    have := Bool.toNat_le c6; have := Bool.toNat_le o6
    omega_arith
  have h12 : (s6.gpr .r12).toNat < 39 := by
    simp only [val4] at hv hB
    omega_arith
  exact ⟨hv, h12, D6, (((((k1.mono (by decide)).trans (k2.mono (by decide))).trans
    (k3.mono (by decide))).trans (k4.mono (by decide))).trans (k5.mono (by decide))).trans
    (k6.mono (by decide))⟩

theorem reduceX_eq : reduceX = reduceLo ++ fold19X := rfl

open VG.Spec.X25519 (P) in
/-- The last fold: `r8–r11 + 2²⁵⁶ r12` with `r12 < 79` and `rdx = 38`, folded into `r8–r11`. -/
theorem foldX_ok (s : State) (h12 : (s.gpr .r12).toNat < 79) (hd : (s.gpr .rdx).toNat = 38) :
    WP isa (.block (([.mulx .rcx .rax (.reg .r12)] : List Instr) ++ carry38)) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + 2 ^ 256 * (s.gpr .r12).toNat) % P ∧
      Keeps [.r8, .r9, .r10, .r11, .rax, .rcx] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok s rfl (noImm_reg _) (by decide)) fun s7 ⟨e7, _, _, k7⟩ => ?_
  rw [hd] at e7
  have hax : (s7.gpr .rax).toNat = 38 * (s.gpr .r12).toNat := by
    have := (s7.gpr .rax).isLt
    omega_arith
  refine WP.mono (carry38_ok s7 (by omega_arith)) fun s8 ⟨e8, k8⟩ => ?_
  refine ⟨?_, (k7.mono (by decide)).trans (k8.mono (by decide))⟩
  rw [e8, hax, k7.1 .r8 (by decide), k7.1 .r9 (by decide), k7.1 .r10 (by decide),
    k7.1 .r11 (by decide), fold256]

open VG.Spec.X25519 (P) in
/-- `r8–r11 + 2²⁵⁶ r12–r15`, reduced into `r8–r11` (modulo `p`), at most `2p`. -/
theorem reduceX_ok (s : State) :
    WP isa (.block reduceX) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          2 ^ 256 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)) % P ∧
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) ≤ 2 * P ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [reduceX_eq, WP.block_append_iff]
  refine WP.mono (reduceLo_ok s) fun s6 ⟨hv, h12, hd, k6⟩ => ?_
  refine WP.mono (fold19X_ok s6 (by omega_using [h12])) fun s8 ⟨e8, b8, k8⟩ => ?_
  refine ⟨?_, b8, k6.trans (k8.mono (by decide))⟩
  rw [e8, hv, fold256]

theorem reduceX2_eq : reduceX2 = reduceLo ++ (dbl5 ++
    (([.mulx .rcx .rax (.reg .r12)] : List Instr) ++ carry38)) := by
  simp only [reduceX2, List.append_assoc]

open VG.Spec.X25519 (P) in
/-- `2 (r8–r11 + 2²⁵⁶ r12–r15)`, reduced into `r8–r11` (modulo `p`). -/
theorem reduceX2_ok (s : State) :
    WP isa (.block reduceX2) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (2 * (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          2 ^ 256 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15))) % P ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [reduceX2_eq, WP.block_append_iff]
  refine WP.mono (reduceLo_ok s) fun s6 ⟨hv, h12, hd, k6⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dbl5_ok s6 (by omega_using [h12])) fun s7 ⟨e7, h7, k7⟩ => ?_
  refine WP.mono (foldX_ok s7 (by have := (s7.gpr .r12).isLt; omega_using [h12, h7])
    (by rw [k7.1 .rdx (by decide)]; exact hd)) fun s8 ⟨e8, k8⟩ => ?_
  refine ⟨?_, (k6.trans (k7.mono (by decide))).trans (k8.mono (by decide))⟩
  rw [e8, e7, hv, Nat.mul_mod, Nat.mul_mod (2 : Nat) (_ + 2 ^ 256 * _), fold256]

/-! ## The multiplication -/

theorem mulX_eq (o a b : Nat) : mulX o a b = (rowX0 a b ++ (rowR' a b 1 .r9 .r10 .r11 .r12 .r13 ++
    (rowR' a b 2 .r10 .r11 .r12 .r13 .r14 ++ rowR' a b 3 .r11 .r12 .r13 .r14 .r15))) ++
      (reduceX ++ store4 o) := by
  simp only [mulX, rowX_eq, List.append_assoc]; rfl

/-- `[o] = [a] · [b]`, at most `2p`. -/
theorem mulXBnd_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mulX o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b ∧
        fe s'.mem base o ≤ 2 * VG.Spec.X25519.P := by
  rw [mulX_eq, WP.block_append_iff]
  refine WP.mono (mul4_ok hs ha hb) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduceX_ok s₄) fun s₅ ⟨e5, b5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  refine WP.mono (store4_ok hs₅ ho) fun s₆ ⟨m6, g6, rd6, wr6⟩ => ?_
  have M : s₅.mem = s.mem := k5.2.1.trans k4.2.1
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_, by rw [m6, fe_st4 _ _ (by omega)]; exact b5⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g6, k5.1 r (by simp [*]), k4.1 r (by simp [*])]
  · rw [rd6, k5.2.2.1, k4.2.2.1]
  · rw [wr6, k5.2.2.2, k4.2.2.2]
  · rw [m6, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul
    rw [m6, fe_st4 _ _ (by omega), e5, e4]

/-- `[o] = [a] · [b]`. -/
theorem mulX_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mulX o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b :=
  WP.mono (mulXBnd_ok hs ho ha hb) fun _ ⟨h, e, _⟩ => ⟨h, e⟩

theorem mul2X_eq (o a b : Nat) : mul2X o a b = (rowX0 a b ++ (rowR' a b 1 .r9 .r10 .r11 .r12 .r13 ++
    (rowR' a b 2 .r10 .r11 .r12 .r13 .r14 ++ rowR' a b 3 .r11 .r12 .r13 .r14 .r15))) ++
      (reduceX2 ++ store4 o) := by
  simp only [mul2X, rowX_eq, List.append_assoc]; rfl

/-- `[o] = 2 · [a] · [b]`. -/
theorem mul2X_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mul2X o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o =
        F s.mem base a * F s.mem base b + F s.mem base a * F s.mem base b := by
  rw [mul2X_eq, WP.block_append_iff]
  refine WP.mono (mul4_ok hs ha hb) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduceX2_ok s₄) fun s₅ ⟨e5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  refine WP.mono (store4_ok hs₅ ho) fun s₆ ⟨m6, g6, rd6, wr6⟩ => ?_
  have M : s₅.mem = s.mem := k5.2.1.trans k4.2.1
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g6, k5.1 r (by simp [*]), k4.1 r (by simp [*])]
  · rw [rd6, k5.2.2.1, k4.2.2.1]
  · rw [wr6, k5.2.2.2, k4.2.2.2]
  · rw [m6, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul2
    rw [m6, fe_st4 _ _ (by omega), e5]
    exact congrArg (fun x => 2 * x % VG.Spec.X25519.P) e4

end VG.Proof.X25519.X86_64

end

end

/-!
# X25519 on x86-64: squaring with BMI2 and ADX

`sqrX o a`: the square `[a]²` into `r8–r15` (`sqr4_ok`, `SqrProd.lean`),
reduced as in `mulX`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- `r ∉ [...]` and `a ≠ b` for literal registers. -/
theorem sqrX_eq (o a : Nat) :
    sqrX o a = (sqrA a ++ (sqrB a ++ (sqrC a ++ sqrD a))) ++ (reduceX ++ store4 o) := by
  simp only [sqrX, List.append_assoc]

/-- `[o] = [a]²`, at most `2p`. -/
theorem sqrXBnd_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqrX o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a ∧
        fe s'.mem base o ≤ 2 * VG.Spec.X25519.P := by
  rw [sqrX_eq, WP.block_append_iff]
  refine WP.mono (sqr4_ok hs ha) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduceX_ok s₄) fun s₅ ⟨e5, b5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  refine WP.mono (store4_ok hs₅ ho) fun s₆ ⟨m6, g6, rd6, wr6⟩ => ?_
  have M : s₅.mem = s.mem := k5.2.1.trans k4.2.1
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_, by rw [m6, fe_st4 _ _ (by omega)]; exact b5⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g6, k5.1 r (by simp [*]), k4.1 r (by simp [*])]
  · rw [rd6, k5.2.2.1, k4.2.2.1]
  · rw [wr6, k5.2.2.2, k4.2.2.2]
  · rw [m6, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul
    rw [m6, fe_st4 _ _ (by omega), e5, e4]

/-- `[o] = [a]²`. -/
theorem sqrX_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqrX o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a :=
  WP.mono (sqrXBnd_ok hs ho ha) fun _ ⟨h, e, _⟩ => ⟨h, e⟩

theorem sqr2X_eq (o a : Nat) :
    sqr2X o a = (sqrA a ++ (sqrB a ++ (sqrC a ++ sqrD a))) ++ (reduceX2 ++ store4 o) := by
  simp only [sqr2X, List.append_assoc]

/-- `[o] = 2 · [a]²`. -/
theorem sqr2X_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqr2X o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o =
        F s.mem base a * F s.mem base a + F s.mem base a * F s.mem base a := by
  rw [sqr2X_eq, WP.block_append_iff]
  refine WP.mono (sqr4_ok hs ha) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduceX2_ok s₄) fun s₅ ⟨e5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  refine WP.mono (store4_ok hs₅ ho) fun s₆ ⟨m6, g6, rd6, wr6⟩ => ?_
  have M : s₅.mem = s.mem := k5.2.1.trans k4.2.1
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g6, k5.1 r (by simp [*]), k4.1 r (by simp [*])]
  · rw [rd6, k5.2.2.1, k4.2.2.1]
  · rw [wr6, k5.2.2.2, k4.2.2.2]
  · rw [m6, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul2
    rw [m6, fe_st4 _ _ (by omega), e5]
    exact congrArg (fun x => 2 * x % VG.Spec.X25519.P) e4

end VG.Proof.X25519.X86_64

end

end

/-!
# X25519 on x86-64: `b + a24 · a` with BMI2 and ADX, and `adx_ok`

`a24addX o b a`: `r8–r12 = [b] + a24 · [a]` (as a row of a product, added to
`[b]`), then `r12` folded as 38; and the field multiplications `adx` satisfy
`FieldOk`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem a24addX_eq (o b a : Nat) : a24addX o b a = ([.mov32 .rdx (.imm a24)] : List Instr) ++
    (loads b .r8 .r9 .r10 .r11 ++ (maddRow a .r8 .r9 .r10 .r11 .r12 ++
      (([.mov32 .rdx (.imm 38)] : List Instr) ++ (([.mulx .rcx .rax (.reg .r12)] : List Instr) ++
        (carry38 ++ store4 o))))) := by
  simp only [a24addX, maddRow, List.append_assoc]; rfl

/-- `[o] = [b] + a24 · [a]`. -/
theorem a24addX_ok {s : State} {base : Addr} (hs : Scr s base) {o b a : Nat} (ho : Slot o)
    (hb : Slot b) (ha : Slot a) :
    WP isa (.block (a24addX o b a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base b + Spec.X25519.a24 * F s.mem base a := by
  rw [a24addX_eq, WP.block_append_iff]
  refine WP.mono (movRdxImm_ok s a24) fun s1 ⟨d1, _, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadFe_ok hs1 hb) fun s2 ⟨l2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (maddRow_ok hs2 (by omega) (by decide)) fun s3 ⟨e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movRdxImm_ok s3 38) fun s4 ⟨d4, _, _, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok s4 rfl (noImm_reg _) (by decide)) fun s5 ⟨e5, _, _, k5⟩ => ?_
  have M1 : s1.mem = s.mem := k1.2.1
  have M2 : s2.mem = s.mem := k2.2.1.trans M1
  rw [M1] at l2
  rw [M2, l2, k2.1 .rdx (by decide), d1, show (a24 : BitVec 32).toNat = 121665 from rfl] at e3
  rw [show (s4.gpr .rdx).toNat = 38 from d4, k4.1 .r12 (by decide)] at e5
  -- `r8–r11 + 2²⁵⁶ r12 = [b] + a24 · [a]`, so `r12 ≤ a24` and `rax = 38 r12`.
  have h12 : (s3.gpr .r12).toNat < 121666 := by
    have hA := fe_lt s.mem base a
    have hB := fe_lt s.mem base b
    omega_using [e3, hA, hB]
  have hax : (s5.gpr .rax).toNat = 38 * (s3.gpr .r12).toNat := by
    have := (s5.gpr .rax).isLt
    omega_using [e5, h12, this]
  have hs5 := (hs3.of_keeps k4 (by decide)).of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carry38_ok s5 (by omega_using [hax, h12])) fun s6 ⟨e6, k6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  refine WP.mono (store4_ok hs6 ho) fun s7 ⟨m7, g7, rd7, wr7⟩ => ?_
  have K : Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s6 :=
    (((((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide))).trans (k5.mono (by decide))).trans (k6.mono (by decide))
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g7, K.1 r (by simp [hr])]
  · rw [rd7, K.2.2.1]
  · rw [wr7, K.2.2.2]
  · rw [m7, K.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_addA24
    rw [m7, fe_st4 _ _ (by omega), e6, hax, k5.1 .r8 (by decide), k5.1 .r9 (by decide),
      k5.1 .r10 (by decide), k5.1 .r11 (by decide), k4.1 .r8 (by decide), k4.1 .r9 (by decide),
      k4.1 .r10 (by decide), k4.1 .r11 (by decide), ← fold256, e3]

/-- The field multiplications with BMI2 and ADX. -/
theorem adx_ok : FieldOk adx where
  mul hs _ _ _ ho ha hb := mulX_ok hs ho ha hb
  sqr hs _ _ ho ha := sqrX_ok hs ho ha
  a24add hs _ _ _ ho hb ha := a24addX_ok hs ho hb ha
  mul2 hs _ _ _ ho ha hb := mul2X_ok hs ho ha hb
  sqr2 hs _ _ ho ha := sqr2X_ok hs ho ha
  mulB hs _ _ _ ho ha hb := mulXBnd_ok hs ho ha hb
  sqrB hs _ _ ho ha := sqrXBnd_ok hs ho ha

end VG.Proof.X25519.X86_64
