module

public import VerifiedGarbage.Proof.X448.RISCV64.Field
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.RISCV64.Pass
public import VerifiedGarbage.Proof.X25519.RISCV64.Pass

/-!
# X448 on RISCV64: sums and differences

`add o x y` and `sub o x y` store at `o` a number congruent to `[x] + [y]` and
`[x] - [y]` (as `[x] + 4p - [y]`); `o` may be `x` or `y`.
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64 VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Spec.X448 (P)

section
variable {b : Addr}

/-- A `pass` of sums, then the `tail`, with no carry in `a5`. -/
theorem passTail_ok {o : Nat} (ho : o + 56 ≤ 2048) (ho4 : o % 4 = 0) {src : Nat → List Instr} {c : Nat → Nat}
    (hc : ∀ k < 14, c k + 2 ^ 32 ≤ 2 ^ 64) (hv : val32 c 14 < 5 * (2 ^ 224 * 2 ^ 224)) {s1 : State}
    (hc1 : Ctx b s1) (h8 : s1.gpr .a5 = 0)
    (hsrc : ∀ k < 14, ∀ s', PassInv .a3 o s1 c 0 k s' → WP isa (.block (src k)) s' fun s'' =>
        (s''.gpr .a4).toNat = c k ∧ Rest [.a2, .a4] s' s'' ∧ s''.mem = s'.mem) :
    WP isa (.block (pass .a3 o src ++ tail o)) s1 fun s' =>
      Rest [.a2, .a4, .a5, .a7] s1 s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s1.mem s'.mem ∧
      V s'.mem b o % P = val32 c 14 % P := by
  refine WP.append (pass_ok (s0 := s1) (c := c) (cin := 0) (by decide) ho
    (fun k hk => by rw [hc1.a3]; exact hc1.inW (by omega_using [ho, hk]))
    (fun k hk => by rw [hc1.a3]; exact al4 hc1.al (by omega_using [ho4]))
    (by rw [h8]; rfl) hc (by decide) hsrc) fun s2 hp => ?_
  have hc2 : Ctx b s2 := hc1.of_rest hp.rest (by decide)
  have hpo : ∀ j < 14, wd s2.mem b (o + 4 * j) = out c 0 j := fun j hj => by
    have := hp.outs j hj; rwa [hc1.a3] at this
  have hpf : Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s1.mem s2.mem := by
    have := hp.frame; rwa [hc1.a3] at this
  have hcl := carry_le hv
  refine WP.mono (tail_ok ho ho4 hc2 hp.a5 hcl) fun s3 ⟨hr3, hf3, hv3⟩ => ?_
  refine ⟨(hp.rest.mono (by decide)).trans hr3, hpf.trans hf3, ?_⟩
  have hcv := chain_val c 0 14
  rw [pow448, Nat.add_zero] at hcv
  rw [hv3, V, val32_congr (f := limb s2.mem b o) (g := out c 0) (fun k hk => hpo k hk), hcv]

theorem add_ok {o x y : Nat} (ho : o + 56 ≤ 2048) (hx : x + 56 ≤ 2048) (hy : y + 56 ≤ 2048)
    (hox : o = x ∨ o + 56 ≤ x ∨ x + 56 ≤ o) (hoy : o = y ∨ o + 56 ≤ y ∨ y + 56 ≤ o)
    (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (add o x y)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x + V s.mem b y) % P := by
  have hvx := V_lt s.mem b x
  have hvy := V_lt s.mem b y
  unfold add
  rw [List.cons_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.a5]) (by decide)) (by decide)
  refine WP.mono (passTail_ok (c := fun k => limb s.mem b x k + limb s.mem b y k) ho ho4
    (fun k _ => by have := limb_lt s.mem b x k; have := limb_lt s.mem b y k; omega)
    (by rw [val32_add]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add hvx hvy) (by omega_using []))
    hc1 u1.gpr ?_)
    fun s' ⟨h1, h2, h3⟩ => ⟨(u1.rest (by decide)).trans (h1.mono (by decide)), by rw [← u1.mem]; exact h2,
      by rw [h3, val32_add]; rfl⟩
  intro k hk s' hp
  have hc' : Ctx b s' := hc1.of_rest hp.rest (by decide)
  refine lw0_ok hc' (d := x + 4 * k) (by omega_using [hx, hk]) (by omega_using [hx4]) fun t1 v1 => ?_
  have hc1' : Ctx b t1 := hc'.of_rest (v1.rest (ws := [.a4]) (by decide)) (by decide)
  refine lw0_ok hc1' (d := y + 4 * k) (by omega_using [hy, hk]) (by omega_using [hy4]) fun t2 v2 => ?_
  refine wp_add fun t3 v3 => WP.block_nil ⟨?_, ?_, by rw [v3.mem, v2.mem, v1.mem]⟩
  · have ex : wd s'.mem b (x + 4 * k) = limb s.mem b x k := by
      rw [wd_pass hc1 hp.frame (by omega_using [hox, hk]) (by omega_using [hx, hk]) (by omega_using [ho, hk]), u1.mem]; rfl
    have ey : wd t1.mem b (y + 4 * k) = limb s.mem b y k := by
      rw [v1.mem, wd_pass hc1 hp.frame (by omega_using [hoy, hk]) (by omega_using [hy, hk]) (by omega_using [ho, hk]), u1.mem]; rfl
    have := limb_lt s.mem b x k; have := limb_lt s.mem b y k
    rw [v3.gpr, v2.other .a4 (by decide), v1.gpr, v2.gpr]
    unfold wd at ex ey
    rw [toNat_add_lt (by rw [toNat_ext32, toNat_ext32, ex, ey]; omega), toNat_ext32, toNat_ext32, ex, ey]
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide)))

theorem subLo_facts (k : Nat) : subLo k ≤ 8 ∧ 2 ^ 34 - subLo k = fourP k := by
  unfold subLo fourP
  by_cases h7 : k = 7
  · simp only [h7, ite_true]; decide
  · simp only [h7, ite_false]; decide

theorem sub_ok {o x y : Nat} (ho : o + 56 ≤ 2048) (hx : x + 56 ≤ 2048) (hy : y + 56 ≤ 2048)
    (hox : o = x ∨ o + 56 ≤ x ∨ x + 56 ≤ o) (hoy : o = y ∨ o + 56 ≤ y ∨ y + 56 ≤ o)
    (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (sub o x y)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      (V s'.mem b o + V s.mem b y) % P = V s.mem b x % P := by
  have hvx := V_lt s.mem b x
  have hlx : ∀ k < 14, limb s.mem b x k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  have hly : ∀ k < 14, limb s.mem b y k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  obtain ⟨hcb, hcv⟩ := subC_facts hlx hly
  have hP := P_eq
  change val32 _ 14 + V s.mem b y = V s.mem b x + 4 * P at hcv
  unfold sub
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => wp_sll (by decide) fun s3 u3 => ?_
  have hr3 : Rest [.a1, .a5] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  have e4 : (s3.gpr .a1).toNat = 2 ^ 34 := by
    rw [u3.gpr, toNat_shl, u2.gpr, toNat_imm (by decide), Nat.one_mul, Nat.mod_eq_of_lt (by decide)]
  refine WP.mono (passTail_ok (c := subC (limb s.mem b x) (limb s.mem b y)) ho ho4 hcb
    (by omega_using [hvx, hP, hcv]) hc3 (by rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; rfl) ?_)
    fun s' ⟨h1, h2, h3⟩ => ⟨(hr3.mono (by decide)).trans (h1.mono (by decide)), by rw [← hm3]; exact h2, by
      rw [Nat.add_mod, h3, ← Nat.add_mod, hcv, Nat.mul_comm, Nat.add_mul_mod_self_left]⟩
  intro k hk s' hp
  have hc' : Ctx b s' := hc3.of_rest hp.rest (by decide)
  obtain ⟨l1, l2⟩ := subLo_facts k
  have ex : wd s'.mem b (x + 4 * k) = limb s.mem b x k := by
    rw [wd_pass hc3 hp.frame (by omega_using [hox, hk]) (by omega_using [hx, hk]) (by omega_using [ho, hk]), hm3]; rfl
  have ey : wd s'.mem b (y + 4 * k) = limb s.mem b y k := by
    rw [wd_pass hc3 hp.frame (by omega_using [hoy, hk]) (by omega_using [hy, hk]) (by omega_using [ho, hk]), hm3]; rfl
  have hX := hlx k hk
  have hY := hly k hk
  have e4' : (s'.gpr .a1).toNat = 2 ^ 34 := by rw [hp.rest.gpr _ (by decide), e4]
  unfold subSrc
  refine lw0_ok hc' (d := x + 4 * k) (by omega_using [hx, hk]) (by omega_using [hx4]) fun t1 v1 => ?_
  have e1 : (t1.gpr .a4).toNat = limb s.mem b x k := by rw [v1.gpr, toNat_ext32]; unfold wd at ex; rw [ex]
  have e14 : (t1.gpr .a1).toNat = 2 ^ 34 := by rw [v1.other _ (by decide), e4']
  refine wp_add fun t2 v2 => ?_
  have e2 : (t2.gpr .a4).toNat = limb s.mem b x k + 2 ^ 34 := by
    rw [v2.gpr, toNat_add_lt (by rw [e1, e14]; omega_using [hX]), e1, e14]
  refine wp_subi (by omega_using [l1]) fun t3 v3 => ?_
  have e3 : (t3.gpr .a4).toNat = limb s.mem b x k + fourP k := by
    rw [v3.gpr, toNat_sub_le (by rw [e2, toNat_imm (by omega_using [l1])]; omega_using [l1]), e2,
      toNat_imm (by omega_using [l1])]
    omega_using [l1, l2]
  have hc3' : Ctx b t3 :=
    hc'.of_rest ((v1.rest (ws := [.a4]) (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide))))
      (by decide)
  refine lw0_ok hc3' (d := y + 4 * k) (by omega_using [hy, hk]) (by omega_using [hy4]) fun t4 v4 => ?_
  refine wp_sub fun t5 v5 => WP.block_nil ⟨?_, ?_, by rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]⟩
  · have ey' : wd t3.mem b (y + 4 * k) = limb s.mem b y k := by rw [v3.mem, v2.mem, v1.mem, ey]
    unfold wd at ey'
    have hK : 2 ^ 34 - 8 ≤ fourP k := by simp only [fourP]; split <;> omega_using []
    rw [v5.gpr, v4.other .a4 (by decide), v4.gpr, toNat_sub_le (by rw [e3, toNat_ext32, ey']; omega_using [hY, hK]),
      e3, toNat_ext32, ey']; rfl
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))

end

end VG.Proof.X448.RISCV64
