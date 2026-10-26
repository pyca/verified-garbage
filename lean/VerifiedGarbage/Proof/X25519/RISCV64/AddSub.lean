module

public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.X25519.RISCV64.Pass
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 on RISCV64: sums and differences

`add o x y` and `sub o x y` store at `o` a number congruent to `[x] + [y]` and
`[x] - [y]` (as `[x] + 4p - [y]`); `o` may be `x` or `y`.
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X25519.RISCV64
open VG.Spec.X25519 (P)

section
variable {b : Addr}

/-- A word the pass has not written yet (the pass writes `[o, o + 4k)`). -/
theorem wd_pass {s0 s : State} (hc : Ctx b s0) {o k d : Nat}
    (hf : Frame [⟨s0.gpr .a3 + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem)
    (hd : d + 4 ≤ o ∨ o + 4 * k ≤ d) (hd' : d + 4 ≤ 2048) (ho : o + 4 * k ≤ 2048) :
    wd s.mem b d = wd s0.mem b d := by
  rw [hc.a3] at hf
  exact wd_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd (by omega_using [hd']) (by omega_using [ho])

/-- A `pass` of sums, then the `tail`, with 38 in `a7` and no carry in `a5`. -/
theorem passTail'_ok {o : Nat} (ho : o + 32 ≤ 2048) (ho4 : o % 4 = 0) {src : Nat → List Instr} {c : Nat → Nat}
    (hc : ∀ k < 8, c k + 2 ^ 32 ≤ 2 ^ 64) (hv : val32 c 8 < 39 * 2 ^ 256) {s1 : State}
    (hc1 : Ctx b s1) (h10 : s1.gpr .a7 = 38) (h8 : s1.gpr .a5 = 0)
    (hsrc : ∀ k < 8, ∀ s', PassInv .a3 o s1 c 0 k s' → WP isa (.block (src k)) s' fun s'' =>
        (s''.gpr .a4).toNat = c k ∧ Rest [.a2, .a4] s' s'' ∧ s''.mem = s'.mem) :
    WP isa (.block (pass .a3 o src ++ tail o)) s1 fun s' =>
      Rest [.a2, .a4, .a5] s1 s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s1.mem s'.mem ∧
      V s'.mem b o % P = val32 c 8 % P := by
  refine WP.append (pass_ok (s0 := s1) (c := c) (cin := 0) (by decide) ho
    (fun k hk => by rw [hc1.a3]; exact hc1.inW (by omega_using [ho, hk]))
    (fun _ _ => by rw [hc1.a3]; exact al4 hc1.al (by omega_using [ho4]))
    (by rw [h8]; rfl) hc (by decide) hsrc) fun s2 hp => ?_
  have hc2 : Ctx b s2 := hc1.of_rest hp.rest (by decide)
  have hpo : ∀ j < 8, wd s2.mem b (o + 4 * j) = out c 0 j := fun j hj => by
    have := hp.outs j hj; rwa [hc1.a3] at this
  have hpf : Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s1.mem s2.mem := by
    have := hp.frame; rwa [hc1.a3] at this
  have hcl := carry_le hv
  refine WP.mono (tail_ok ho ho4 hc2 (by rw [hp.rest.gpr _ (by decide), h10]) hp.a5 hcl)
    fun s3 ⟨hr3, hf3, hv3⟩ => ?_
  refine ⟨hp.rest.trans hr3, hpf.trans hf3, ?_⟩
  rw [hv3, V, val32_congr (f := limb s2.mem b o) (g := out c 0) (fun k hk => hpo k hk),
    chain_val, Nat.add_zero]

theorem add_ok {o x y : Nat} (ho : o + 32 ≤ 2048) (hx : x + 32 ≤ 2048) (hy : y + 32 ≤ 2048)
    (hox : o = x ∨ o + 32 ≤ x ∨ x + 32 ≤ o) (hoy : o = y ∨ o + 32 ≤ y ∨ y + 32 ≤ o)
    (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (add o x y)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x + V s.mem b y) % P := by
  have hvx := V_lt s.mem b x
  have hvy := V_lt s.mem b y
  unfold add
  rw [List.append_assoc]
  refine WP.append prologue_ok fun s1 ⟨h10, h8, hr1, hm1⟩ => ?_
  have hc1 : Ctx b s1 := hc.of_rest hr1 (by decide)
  refine WP.mono (passTail'_ok (c := fun k => limb s.mem b x k + limb s.mem b y k) ho ho4
    (fun k _ => by have := limb_lt s.mem b x k; have := limb_lt s.mem b y k; omega)
    (by rw [val32_add]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add hvx hvy) (by omega_using []))
    hc1 h10 h8 ?_)
    fun s' ⟨h1, h2, h3⟩ => ⟨(hr1.mono (by decide)).trans (h1.mono (by decide)), by rw [← hm1]; exact h2,
      by rw [h3, val32_add]; rfl⟩
  intro k hk s' hp
  have hc' : Ctx b s' := hc1.of_rest hp.rest (by decide)
  refine lw0_ok hc' (d := x + 4 * k) (by omega_using [hx, hk]) (by omega_using [hx4]) fun t1 v1 => ?_
  have hc1' : Ctx b t1 := hc'.of_rest (v1.rest (ws := [.a4]) (by decide)) (by decide)
  refine lw0_ok hc1' (d := y + 4 * k) (by omega_using [hy, hk]) (by omega_using [hy4]) fun t2 v2 => ?_
  refine wp_add fun t3 v3 => WP.block_nil ⟨?_, ?_, by rw [v3.mem, v2.mem, v1.mem]⟩
  · have ex : wd s'.mem b (x + 4 * k) = limb s.mem b x k := by
      rw [wd_pass hc1 hp.frame (by omega_using [hox, hk]) (by omega_using [hx, hk]) (by omega_using [ho, hk]), hm1]; rfl
    have ey : wd t1.mem b (y + 4 * k) = limb s.mem b y k := by
      rw [v1.mem, wd_pass hc1 hp.frame (by omega_using [hoy, hk]) (by omega_using [hy, hk]) (by omega_using [ho, hk]), hm1]; rfl
    have := limb_lt s.mem b x k; have := limb_lt s.mem b y k
    rw [v3.gpr, v2.other .a4 (by decide), v1.gpr, v2.gpr]
    unfold wd at ex ey
    rw [toNat_add_lt (by rw [toNat_ext32, toNat_ext32, ex, ey]; omega), toNat_ext32, toNat_ext32, ex, ey]
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide)))

theorem subLo_facts {k : Nat} (_hk : k < 8) : subLo k ≤ 2048 ∧ subLo k ≤ 76 ∧
    (if k = 7 then 2 ^ 33 else 2 ^ 34) - subLo k = fourP k := by
  unfold subLo fourP
  by_cases h0 : k = 0
  · subst h0; decide
  · by_cases h7 : k = 7
    · subst h7; decide
    · simp only [h0, h7, ite_false]; decide

theorem sub_ok {o x y : Nat} (ho : o + 32 ≤ 2048) (hx : x + 32 ≤ 2048) (hy : y + 32 ≤ 2048)
    (hox : o = x ∨ o + 32 ≤ x ∨ x + 32 ≤ o) (hoy : o = y ∨ o + 32 ≤ y ∨ y + 32 ≤ o)
    (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (sub o x y)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      (V s'.mem b o + V s.mem b y) % P = V s.mem b x % P := by
  have hvx := V_lt s.mem b x
  have hlx : ∀ k < 8, limb s.mem b x k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  have hly : ∀ k < 8, limb s.mem b y k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  obtain ⟨hcb, hcv⟩ := subC_facts hlx hly
  have hPv : 4 * P < 2 * 2 ^ 256 := by decide
  change val32 _ 8 + V s.mem b y = V s.mem b x + 4 * P at hcv
  unfold sub
  simp only [List.append_assoc]
  refine WP.append prologue_ok fun s1 ⟨h10, h8, hr1, hm1⟩ => ?_
  refine wp_li (by decide) fun s2 u2 => wp_sll (by decide) fun s3 u3 => ?_
  have hr3 : Rest [.a1, .a5, .a7] s s3 :=
    (hr1.mono (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, hm1]
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  have e4 : (s3.gpr .a1).toNat = 2 ^ 33 := by
    rw [u3.gpr, toNat_shl, u2.gpr, toNat_imm (by decide), Nat.one_mul, Nat.mod_eq_of_lt (by decide)]
  refine WP.mono (passTail'_ok (c := subC (limb s.mem b x) (limb s.mem b y)) ho ho4 hcb
    (by omega_using [hvx, hPv, hcv]) hc3 (by rw [u3.other _ (by decide), u2.other _ (by decide), h10])
    (by rw [u3.other _ (by decide), u2.other _ (by decide), h8]) ?_)
    fun s' ⟨h1, h2, h3⟩ => ⟨(hr3.mono (by decide)).trans (h1.mono (by decide)), by rw [← hm3]; exact h2, by
      rw [Nat.add_mod, h3, ← Nat.add_mod, hcv, Nat.mul_comm, Nat.add_mul_mod_self_left]⟩
  intro k hk s' hp
  have hc' : Ctx b s' := hc3.of_rest hp.rest (by decide)
  obtain ⟨l1, l2, l3⟩ := subLo_facts hk
  have ex : wd s'.mem b (x + 4 * k) = limb s.mem b x k := by
    rw [wd_pass hc3 hp.frame (by omega_using [hox, hk]) (by omega_using [hx, hk]) (by omega_using [ho, hk]), hm3]; rfl
  have hX := hlx k hk
  have hY := hly k hk
  have hK := fourP_ge k hk
  have e4' : (s'.gpr .a1).toNat = 2 ^ 33 := by rw [hp.rest.gpr _ (by decide), e4]
  -- The limb of `x` plus the high part of `4p`, in `a4`.
  have key : ∀ (t : State), Rest [.a4] s' t → t.mem = s'.mem →
      (t.gpr .a4).toNat = limb s.mem b x k + (if k = 7 then 2 ^ 33 else 2 ^ 34) →
      WP isa (.block ([.addi .a4 .a4 (-(subLo k)), .load .w .a2 .a3 (y + 4 * k), .sub .a4 .a4 .a2] : List Instr)) t
        fun s'' => (s''.gpr .a4).toNat = subC (limb s.mem b x) (limb s.mem b y) k ∧
          Rest [.a2, .a4] s' s'' ∧ s''.mem = s'.mem := by
    intro t ht hmt e7
    have hct : Ctx b t := hc'.of_rest ht (by decide)
    refine wp_subi l1 fun t1 v1 => ?_
    refine lw0_ok (hct.of_rest (v1.rest (ws := [.a4]) (by decide)) (by decide)) (d := y + 4 * k)
      (by omega_using [hy, hk]) (by omega_using [hy4]) fun t2 v2 => ?_
    refine wp_sub fun t3 v3 => WP.block_nil ⟨?_, ?_, by rw [v3.mem, v2.mem, v1.mem, hmt]⟩
    · have ey : wd t1.mem b (y + 4 * k) = limb s.mem b y k := by
        rw [v1.mem, hmt, wd_pass hc3 hp.frame (by omega_using [hoy, hk]) (by omega_using [hy, hk]) (by omega_using [ho, hk]), hm3]; rfl
      unfold wd at ey
      have hH : 2 ^ 33 ≤ (if k = 7 then 2 ^ 33 else 2 ^ 34) := by split <;> omega_using []
      have r1 : (t1.gpr .a4).toNat = limb s.mem b x k + fourP k := by
        generalize (if k = 7 then (2 : Nat) ^ 33 else 2 ^ 34) = H at e7 l3 hH
        rw [v1.gpr, toNat_sub_le (by rw [e7, toNat_imm (by omega_using [l2])]; omega_using [l2, hH]),
          e7, toNat_imm (by omega_using [l2])]
        omega_using [l3, l2, hH]
      rw [v3.gpr, v2.other .a4 (by decide), v2.gpr, toNat_sub_le (by rw [r1, toNat_ext32, ey]; omega_using [hY, hK]),
        r1, toNat_ext32, ey]; rfl
    · exact (ht.mono (by decide)).trans ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans
        (v3.rest (by decide))))
  unfold subSrc
  simp only [List.cons_append, List.nil_append]
  refine lw0_ok hc' (d := x + 4 * k) (by omega_using [hx, hk]) (by omega_using [hx4]) fun t1 v1 => ?_
  have e1 : (t1.gpr .a4).toNat = limb s.mem b x k := by rw [v1.gpr, toNat_ext32]; unfold wd at ex; rw [ex]
  have e14 : (t1.gpr .a1).toNat = 2 ^ 33 := by rw [v1.other _ (by decide), e4']
  by_cases h7 : k = 7
  · simp only [subHi, h7, ite_true, List.cons_append, List.nil_append]
    refine wp_add fun t2 v2 => ?_
    subst h7
    refine key t2 ((v1.rest (by decide)).trans (v2.rest (by decide))) (by rw [v2.mem, v1.mem]) ?_
    rw [v2.gpr, toNat_add_lt (by rw [e1, e14]; omega_using [hX])]
    simp only [ite_true]
    omega_using [e1, e14]
  · simp only [subHi, h7, ite_false, List.cons_append, List.nil_append]
    refine wp_add fun t2 v2 => wp_add fun t3 v3 => ?_
    refine key t3 ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide))))
      (by rw [v3.mem, v2.mem, v1.mem]) ?_
    have e2 : (t2.gpr .a4).toNat = limb s.mem b x k + 2 ^ 33 := by
      rw [v2.gpr, toNat_add_lt (by rw [e1, e14]; omega_using [hX]), e1, e14]
    have e24 : (t2.gpr .a1).toNat = 2 ^ 33 := by rw [v2.other _ (by decide), e14]
    have hi : (if k = 7 then (2 : Nat) ^ 33 else 2 ^ 34) = 2 ^ 34 := ite_eq_right_iff.mpr (fun h => absurd h h7)
    rw [v3.gpr, toNat_add_lt (by rw [e2, e24]; omega_using [hX])]
    omega_using [e2, e24, hi]

end

end VG.Proof.X25519.RISCV64
