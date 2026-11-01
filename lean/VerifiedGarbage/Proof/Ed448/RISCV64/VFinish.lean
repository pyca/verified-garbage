module

import VerifiedGarbage.Proof.Ed448.RISCV64.VDecodeCheck
import VerifiedGarbage.Proof.Ed448.RISCV64.VSel
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseEncode
import VerifiedGarbage.Proof.X448.RISCV64.Freeze
import VerifiedGarbage.Proof.X448.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseStep
public import VerifiedGarbage.Proof.Ed448.RISCV64.VChecks
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.X448.RISCV64.Slots

/-!
# Ed448's verification on RISCV64: the result

`vFinish` checks that `Q` is the neutral point, `X = 0` and `Y - Z = 0`
fully reduced, and returns 1 exactly when no check failed (`vFinish_ok`):
1 less the top bit of `BAD | -BAD` (`top_nz`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y Z2 ACC freeze)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)

/-- The top bit of `x | -x` is set exactly when `x` is not 0. -/
theorem top_nz (x : BitVec 64) : ((x ||| (0 - x)) >>> 63).toNat = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; decide
  · rw [ite_eq_right h, BitVec.toNat_ushiftRight, BitVec.toNat_or, Nat.shiftRight_or_distrib]
    have hx : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have hlt := x.isLt
    have hn : (0 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub]; simp; omega
    rw [hn, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have h2 : (2 ^ 64 - x.toNat) / 2 ^ 63 ≤ 1 := by omega
    rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h3 | h3
    · rw [Nat.div_eq_of_lt h3, show (2 ^ 64 - x.toNat) / 2 ^ 63 = 1 by omega]; rfl
    · rw [show x.toNat / 2 ^ 63 = 1 by omega]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with e | e <;> rw [e] <;> rfl

theorem bad_zero_iff {m : Mem} {b : Addr} : (m.readW (b + BitVec.ofNat 64 BAD) 64 = 0) ↔ bad m b = 0 := by
  unfold bad
  exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩

section
variable {b : Addr}

theorem vFinish_ok {s : State} (hc : VCtx b s) {Q : Point} (hS : SlotsOk s.mem b RQ (ptV Q Q)) :
    WP isa (.block vFinish) s fun t =>
      t.gpr .a0 = BitVec.ofNat 64 (if bad s.mem b = 0 ∧ Q.X = 0 ∧ Q.Y = Q.Z then 1 else 0) := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hA := X448.RISCV64.ACC_eq
  have hY : Y = 896 := rfl
  have hdo : Region.Disjoint ⟨b, 2048⟩ ⟨b + BitVec.ofNat 64 OUT, 56⟩ :=
    (Offset.disjoint_base b (d := OUT) (n := 56) (k := 2048) (by omega) (by omega)).symm
  unfold vFinish
  simp only [outZero, copy, List.append_assoc, List.cons_append]
  -- `X`.
  refine WP.append (freeze_ok hc.ctx hc.a0 (fun k hk => by rw [Offset.add_add]; exact hc.inW (by omega)) hdo)
    fun s1 ⟨_, hr1, hf1, hw1⟩ => ?_
  have hc1 : VCtx b s1 := hc.of_rest hr1 (by decide) (by decide)
  refine WP.append (outOr_ok hc1) fun s2 ⟨hr2, hm2, hv2⟩ => ?_
  have hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  refine WP.append (orBad_ok hc2 (r := .a7) (by decide)) fun s3 ⟨hr3, hf3, hb3⟩ => ?_
  have hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  have hS3 := SlotsOk.lo (m := s1.mem) (m' := s3.mem) (by rw [← hm2]; exact hf3) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact disj_hi (by omega) (by omega)) (slots_freeze hf1 hdo hS (by decide))
    (by decide)
  -- `Y - Z`.
  refine WP.append (R64.subS (o := TA) (x := RY) (y := RZ) (by decide) (by decide) (by decide) (by decide) hc3.ctx hS3)
    fun s4 ⟨hr4, hf4, hS4⟩ => ?_
  have hc4 : VCtx b s4 := hc3.of_rest hr4 (by decide) (by decide)
  refine wp_li (by decide) fun s5 u5 => ?_
  have hc5 : VCtx b s5 := hc4.of_rest (u5.rest (ws := [.t0]) (by decide)) (by decide) (by decide)
  have hS5 := hS4
  rw [← u5.mem] at hS5
  refine WP.append (selG (o := X2) (q := TA) (r := TA) (sw := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc5.ctx (by decide) (by rw [u5.gpr]; rfl) hS5 (hS5 TA (by decide)) (hS5 TA (by decide)))
    fun s6 ⟨hr6, hf6, hS6⟩ => ?_
  have hc6 : VCtx b s6 := hc5.of_rest hr6 (by decide) (by decide)
  refine WP.append (freeze_ok hc6.ctx hc6.a0 (fun k hk => by rw [Offset.add_add]; exact hc6.inW (by omega)) hdo)
    fun s7 ⟨_, hr7, hf7, hw7⟩ => ?_
  have hc7 : VCtx b s7 := hc6.of_rest hr7 (by decide) (by decide)
  refine WP.append (outOr_ok hc7) fun s8 ⟨hr8, hm8, hv8⟩ => ?_
  have hc8 : VCtx b s8 := hc7.of_rest hr8 (by decide) (by decide)
  refine WP.append (orBad_ok hc8 (r := .a7) (by decide)) fun s9 ⟨hr9, hf9, hb9⟩ => ?_
  have hc9 : VCtx b s9 := hc8.of_rest hr9 (by decide) (by decide)
  -- The result.
  refine wp_ld (a := b + BitVec.ofNat 64 BAD) (by decide) (by rw [hc9.ctx.a3]) (hc9.al8 (by decide))
    (hc9.inR (by omega))
    fun t1 v1 => wp_li (by decide) fun t2 v2 => wp_sub fun t3 v3 => ?_
  refine wp_or fun t4 v4 => wp_srl (by decide) fun t5 v5 => wp_li (by decide) fun t6 v6 => wp_sub fun t7 v7 => ?_
  refine WP.block_nil ?_
  -- `BAD` along the way.
  have rB : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
      (∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r) → bad m' b = bad m b := fun hf hd => by
    unfold bad; rw [hf.readW (Region.contains_self _ (64 / 8)) hd (by decide)]
  have dYO : ∀ r ∈ [(⟨b + BitVec.ofNat 64 Y, 56⟩ : Region), ⟨b + BitVec.ofNat 64 OUT, 56⟩],
      Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have dFA : ∀ r ∈ [FA b], Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega) (by omega)
  have b1 : bad s1.mem b = bad s.mem b := rB hf1 dYO
  have b8 : bad s8.mem b = bad s3.mem b := by
    rw [bad, hm8, ← bad, rB hf7 dYO, rB hf6 dFA, bad, u5.mem, ← bad, rB hf4 dFA]
  have e9 : bad s9.mem b = bad s.mem b |||
      orw (fun k => wd s1.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 |||
      orw (fun k => wd s7.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 := by
    rw [hb9, b8, hb3, hv8, hv2, bad, hm2, ← bad, b1]
  -- The two elements.
  have hX : FS s.mem b X2 = Q.X := by
    rw [hS X2 (by decide)]; simp only [ptV, RX, X2, ↓reduceIte]
  have hYZ : FS s6.mem b X2 = Q.Y - Q.Z := by
    rw [hS6 X2 (by decide)]
    simp only [upd, ptV, pick, VG.Proof.X25519.sel, TA, RX, RY, RZ, X2, Z2, Nat.reduceEqDiff, ↓reduceIte]
  have i1 : orw (fun k => wd s1.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 ↔ Q.X = 0 := by
    rw [orw_eq_zero, ← val32_eq_zero, ← fs_zero hw1, hX]
  have i2 : orw (fun k => wd s7.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 ↔ Q.Y = Q.Z := by
    rw [orw_eq_zero, ← val32_eq_zero, ← fs_zero hw7, hYZ, fin_sub_eq_zero]
  -- The result.
  have ev : t3.gpr .a6 = s9.mem.readW (b + BitVec.ofNat 64 BAD) 64 := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.gpr]
  have e8 : t3.gpr .a5 = 0 - s9.mem.readW (b + BitVec.ofNat 64 BAD) 64 := by
    rw [v3.gpr, v2.gpr, v2.other _ (by decide), v1.gpr]; rfl
  have hz : (t5.gpr .a6).toNat = if s9.mem.readW (b + BitVec.ofNat 64 BAD) 64 = 0 then 0 else 1 := by
    rw [v5.gpr, v4.gpr, ev, e8, top_nz]
  rw [v7.gpr, v6.gpr, v6.other _ (by decide)]
  have hc' : (bad s9.mem b = 0) ↔ (bad s.mem b = 0 ∧ Q.X = 0 ∧ Q.Y = Q.Z) := by
    rw [e9, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff, i1, i2, and_assoc]
  apply BitVec.eq_of_toNat_eq
  by_cases h0 : bad s9.mem b = 0
  · rw [ite_eq_left (hc'.mp h0), ite_eq_left (bad_zero_iff.mpr h0)] at *
    rw [BitVec.toNat_sub, hz]; rfl
  · rw [ite_eq_right (fun h => h0 (hc'.mpr h)), ite_eq_right (fun h => h0 (bad_zero_iff.mp h))] at *
    rw [BitVec.toNat_sub, hz]; rfl

end

end VG.Proof.Ed448.RISCV64
