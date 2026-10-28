module

public import VerifiedGarbage.Proof.X25519.RISCV64.Cswap
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.X448.RISCV64
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Spec.X448

/-!
# X448 on RISCV64: the conditional swap

`cswap x y` swaps the elements at `x` and `y` if the mask in `t0` is `-1`
and leaves them if it is `0` (`cswap_ok`), with X25519's invariant (`SwapInv`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64 VG.Proof.X25519 VG.Proof.X25519.RISCV64

section
variable {b : Addr}

theorem cswap_ok {x y : Nat} (hx : x + 56 ≤ 2048) (hy : y + 56 ≤ 2048) (hxy : x + 56 ≤ y ∨ y + 56 ≤ x)
    (hx4 : x % 4 = 0) (hy4 : y % 4 = 0)
    {s0 : State} (hc : Ctx b s0) {sw : Nat} (hsw : sw ≤ 1) (h11 : s0.gpr .t0 = 0 - BitVec.ofNat 64 sw) :
    WP isa (.block (cswap x y)) s0 (SwapInv b x y sw s0 14) := by
  refine wp_range_flatMap (M := isa) (SwapInv b x y sw s0) (fun k s hk h => ?_) 14 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  have wx : wd s.mem b (x + 4 * k) = limb s0.mem b x k :=
    wd_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [hx, hk]) (by omega_using [hx, hk])
      · exact Offset.disjoint _ (by omega_using [hxy, hk]) (by omega_using [hx, hk]) (by omega_using [hy, hk])
  have wy : wd s.mem b (y + 4 * k) = limb s0.mem b y k :=
    wd_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_using [hxy, hk]) (by omega_using [hy, hk]) (by omega_using [hx, hk])
      · exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [hy, hk]) (by omega_using [hy, hk])
  unfold cswapStep
  refine lw0_ok hcs (d := x + 4 * k) (by omega_using [hx, hk]) (by omega_arith) fun t1 v1 => ?_
  refine lw0_ok (hcs.of_rest (v1.rest (ws := [.a2]) (by decide)) (by decide)) (d := y + 4 * k)
    (by omega_using [hy, hk]) (by omega_arith) fun t2 v2 => ?_
  refine wp_xor fun t3 v3 => wp_and fun t4 v4 => ?_
  refine wp_xor fun t5 v5 => wp_xor fun t6 v6 => ?_
  have hr6 : Rest [.a2, .a4, .a5] s t6 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest (by decide))))))
  have hc6 : Ctx b t6 := hcs.of_rest hr6 (by decide)
  refine sw0_ok hc6 (d := x + 4 * k) (by omega_using [hx, hk]) (by omega_arith) fun t7 v7 => ?_
  refine sw0_ok (hc6.of_rest (v7.rest []) (by decide)) (d := y + 4 * k) (by omega_using [hy, hk]) (by omega_arith)
    fun t8 v8 => ?_
  refine WP.block_nil ?_
  -- The values.
  have eX : t2.gpr .a2 = (s.mem.readW (b + BitVec.ofNat 64 (x + 4 * k)) 32).setWidth 64 := by
    rw [v2.other _ (by decide), v1.gpr]
  have eY : t2.gpr .a4 = (s.mem.readW (b + BitVec.ofNat 64 (y + 4 * k)) 32).setWidth 64 := by
    rw [v2.gpr, v1.mem]
  have em : t3.gpr .t0 = 0 - BitVec.ofNat 64 sw := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h11]
  have e6x : t6.gpr .a2 = t2.gpr .a2 ^^^ ((t2.gpr .a2 ^^^ t2.gpr .a4) &&& (0 - BitVec.ofNat 64 sw)) := by
    rw [v6.other _ (by decide), v5.gpr, v4.other _ (by decide), v3.other _ (by decide), v4.gpr, v3.gpr, em]
  have e6y : t6.gpr .a4 = t2.gpr .a4 ^^^ ((t2.gpr .a2 ^^^ t2.gpr .a4) &&& (0 - BitVec.ofNat 64 sw)) := by
    rw [v6.gpr, v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v5.other _ (by decide),
      v4.gpr, v3.gpr, em]
  have hm8 : t8.mem = (s.mem.writeW (b + BitVec.ofNat 64 (x + 4 * k)) ((t6.gpr .a2).setWidth 32)).writeW
      (b + BitVec.ofNat 64 (y + 4 * k)) ((t6.gpr .a4).setWidth 32) := by
    rw [v8.mem, v7.gpr, v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  have vx : ((t6.gpr .a2).setWidth 32).toNat = sel sw (limb s0.mem b x k) (limb s0.mem b y k) := by
    rw [e6x, eX, eY, ← wx, ← wy]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0, lo32_ext]; rfl
    · rw [sel1, lo32_ext]; rfl
  have vy : ((t6.gpr .a4).setWidth 32).toNat = sel sw (limb s0.mem b y k) (limb s0.mem b x k) := by
    rw [e6y, eX, eY, ← wx, ← wy]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0', lo32_ext]; rfl
    · rw [sel1', lo32_ext]; rfl
  refine ⟨h.rest.trans (hr6.trans ((v7.rest _).trans (v8.rest _))), ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [hm8]
    refine ((h.frame.sub fun r hr => ?_).writeW (List.mem_cons_self ..) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hx, hk]))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hy, hk]))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by omega_using [])⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega_using [])⟩
  · rw [limb, hm8, wd_write_other _ _ _ (by omega_using [hxy, hk, hj]) (by omega_using [hx, hk, hj]) (by omega_using [hy, hk])]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega_using [hx, hk])]; exact h.lx j hj
    · rw [wd_write_self, vx]
  · rw [limb, hm8]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega_using [hy, hk]),
        wd_write_other _ _ _ (by omega) (by omega) (by omega_using [hx, hk])]; exact h.ly j hj
    · rw [wd_write_self, vy]

end

end VG.Proof.X448.RISCV64
