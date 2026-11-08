module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Bfly
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Mem
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.VNtt
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # ML-DSA's vector NTT on PPC64LE: the zetas

`z'` of each zeta, stored in `scratch` at the positions `scrK` says
(`scrK_wide`, `scrK_two`, …), and `z` from it (`zrec`): no zeta is 0
modulo `q` (`zeta_nz`). -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.VNtt

/-! ## Zetas -/

theorem zeta_lt (m : Nat) : zeta m < Spec.MlDsa.q := Nat.mod_lt _ (by decide)

theorem shoup_lt {z : Nat} (hz : z < Spec.MlDsa.q) : shoup z < 2 ^ 32 := by
  unfold shoup q
  have : z * 2 ^ 32 < 8380417 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hz (by decide)
  omega

/-- Multiplying by `c` with an inverse `d` modulo `q` keeps a residue nonzero. -/
theorem mul_mod_ne {c d x : Nat} (hcd : c * d % 8380417 = 1) (hx : x % 8380417 ≠ 0) : c * x % 8380417 ≠ 0 := by
  intro h
  apply hx
  have : x * (c * d) % 8380417 = x % 8380417 := by rw [Nat.mul_mod, hcd, Nat.mul_one, Nat.mod_mod]
  rw [← this, show x * (c * d) = c * x * d by rw [Nat.mul_comm c x, Nat.mul_assoc], Nat.mul_mod, h, Nat.zero_mul,
    Nat.zero_mod]

theorem pow_ne (b : Nat) : 1753 ^ b % 8380417 ≠ 0 := by
  induction b with
  | zero => decide
  | succ b ih => rw [Nat.pow_succ, Nat.mul_comm]; exact mul_mod_ne (d := 731434) (by decide) ih

/-- No zeta times `2³²` is 0 modulo `q`. -/
theorem zeta_nz (k : Nat) : zeta k * 2 ^ 32 % 8380417 ≠ 0 := by
  rw [Nat.mul_comm]
  refine mul_mod_ne (d := 8265825) (by decide) ?_
  rw [zeta, q, Nat.mod_mod]; exact pow_ne _

/-- `z` from `z'`: `⌊z' · q / 2³²⌋ + 1`. -/
theorem zrec {z : Nat} (hnz : z * 2 ^ 32 % 8380417 ≠ 0) : shoup z * 8380417 / 2 ^ 32 + 1 = z := by
  unfold shoup q
  omega

/-! ## Positions -/

theorem flip_eq {e : Nat} (he : e < 4) : swap1 e = e ^^^ 1 := by
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem flip_lt {e : Nat} (he : e < 4) : swap1 e < 4 := by unfold swap1; split <;> omega

theorem scrK_wide {k : Nat} (h : k < 64) : scrK k = k := by
  unfold scrK; rw [ite_eq_left h]

theorem scrK_two {g r : Nat} (hg : g < 16) (hr : r < 4) : scrK (64 + 4 * g + swap1 r) = 64 + 4 * g + r := by
  unfold scrK swap1
  rw [ite_eq_right (by split <;> omega), ite_eq_left (by split <;> omega)]
  split <;> split <;> omega

theorem scrK_even {g r : Nat} (hg : g < 16) (hr : r < 4) :
    scrK (128 + 8 * g + swap1 r) = 128 + 8 * g + 2 * r := by
  unfold scrK swap1
  rw [ite_eq_right (by split <;> omega), ite_eq_right (by split <;> omega), ite_eq_left (by split <;> omega)]
  split <;> split <;> omega

theorem scrK_odd {g r : Nat} (hg : g < 16) (hr : r < 4) :
    scrK (132 + 8 * g + swap1 r) = 128 + 8 * g + 2 * r + 1 := by
  unfold scrK swap1
  rw [ite_eq_right (by split <;> omega), ite_eq_right (by split <;> omega), ite_eq_right (by split <;> omega)]
  split <;> split <;> omega

theorem scrK_lt {p : Nat} (hp : p < 256) : scrK p < 256 := by
  unfold scrK swap1; repeat' split
  all_goals omega

/-! ## Storing the table -/

theorem loadImm_lo_bits (a b : BitVec 16) :
    ((a ++ (0 : BitVec 16)).signExtend 64 ||| b.setWidth 64).setWidth 32 = a ++ b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_signExtend, BitVec.getLsbD_append, hi,
    decide_true, Bool.true_and, show i < 64 by omega]
  by_cases h : i < 16
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge b i (by omega)]

theorem loadImm_lo {v : Nat} (hv : v < 2 ^ 32) :
    ((BitVec.ofNat 16 (v / 65536) ++ (0 : BitVec 16)).signExtend 64 |||
      (BitVec.ofNat 16 (v % 65536)).setWidth 64).setWidth 32 = BitVec.ofNat 32 v := by
  rw [loadImm_lo_bits]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)), Nat.shiftLeft_eq]
  omega

theorem scrV_lt (p : Nat) : scrV p < 2 ^ 32 := shoup_lt (zeta_lt _)

/-- After positions `1 … k` of the table at `r4`. -/
structure FillInv (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  vpr : s.vpr = s₀.vpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  syms : s.syms = s₀.syms
  frame : Frame [⟨s₀.gpr .r4, 1024⟩] s₀.mem s.mem
  tab : ∀ p, 0 < p → p ≤ k → s.mem.readW (s₀.gpr .r4 + BitVec.ofNat 64 (4 * p)) 32 = BitVec.ofNat 32 (scrV p)

theorem fill_ok {s₀ : State} (hwr : ∀ p < 256, InRegions s₀.wr (s₀.gpr .r4 + BitVec.ofNat 64 (4 * p)) 4) :
    WP isa (.block fill) s₀ (FillInv s₀ 255) := by
  refine wp_range_flatMap (M := isa) (FillInv s₀) (fun k s hk h => ?_) 255 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun p hp hp' => absurd hp' (by omega)⟩
  have hv := scrV_lt (k + 1)
  let s₁ := s.write .r12 ((BitVec.ofNat 16 (scrV (k + 1) / 65536) ++ (0 : BitVec 16)).signExtend 64)
  let s₂ := s₁.write .r12 (s₁.gpr .r12 ||| (BitVec.ofNat 16 (scrV (k + 1) % 65536)).setWidth 64)
  have v2 : (s₂.gpr .r12).setWidth 32 = BitVec.ofNat 32 (scrV (k + 1)) := by
    simp only [s₂, s₁, State.write, ite_true]; exact loadImm_lo hv
  have e : s₂.gpr .r4 + BitVec.ofNat 64 (4 * (k + 1)) = s₀.gpr .r4 + BitVec.ofNat 64 (4 * (k + 1)) := by
    simp only [s₂, s₁, State.write, reduceCtorEq, ite_false, h.gpr .r4 (by decide)]
  refine WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_store_w (by decide) (show 4 * (k + 1) < 2 ^ 15 by omega)
    (by show InRegions s₂.wr _ 4; rw [e]; exact h.wr ▸ hwr (k + 1) (by omega))) (wp_nil ?_)))
  show FillInv s₀ (k + 1)
    { s₂ with mem := (s₂.mem.writeW (s₂.gpr .r4 + BitVec.ofNat 64 (4 * (k + 1))) ((s₂.gpr .r12).setWidth 32)) }
  rw [e, v2]
  refine ⟨fun r hr => ?_, h.vpr, h.rd, h.wr, h.sp, h.lr, h.syms, ?_, fun p hp hp' => ?_⟩
  · simp only [s₂, s₁, State.write, hr, ite_false]; exact h.gpr r hr
  · exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · show (s.mem.writeW _ _).readW _ 32 = _
    by_cases ep : p = k + 1
    · subst ep; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.tab p hp (by omega)

end VG.Proof.MlDsa.PPC64LE.VNtt
