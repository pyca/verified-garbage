import VerifiedGarbage.Proof.X448.AArch64.Base.Loop
import VerifiedGarbage.Proof.X448.AArch64.Base.AddGen
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters

/-!
# X448 of the base point on AArch64: `16 A + B`

Untrusted: everything here is checked by Lean. After the comb's loop, four
doublings of `A` and the addition of `B` leave `[k] B` in `A` (`comb_total`).
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside2)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Proof.Ed448.Edwards (EPoint)
open VG.Proof.X448 (addPt addPt_rep)
open VG.Impl.X448.AArch64.Fast (codeOf)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- What every phase after the setup keeps. -/
structure Frame (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  lr : s.gpr .x30 = s₀.gpr .x30
  out : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem

theorem StepInv.frame {s₀ s : State} {base : Addr} {k j : Nat} (h : StepInv s₀ base k j s) :
    Frame s₀ base s := ⟨h.scr, h.env, h.zero, h.lr, h.out, h.rd, h.wr, h.mem⟩

/-- A complete addition, from `Frame`, with the points in slots `x1 y1 z1` and `x2 y2 z2`. -/
theorem addFrame_ok {s₀ s : State} {base : Addr} (h : Frame s₀ base s) (x1 y1 z1 x2 y2 z2 : Index)
    (hx1 : x1.val < 10) (hy1 : y1.val < 10) (hz1 : z1.val < 10) (hx2 : x2.val < 10) (hy2 : y2.val < 10)
    (hz2 : z2.val < 10) (hxy : x1 ≠ y1) (hzx : z1 ≠ x1) (hzy : z1 ≠ y1) :
    WP isa (.block (codeOf (addOps (slot x1.val) (slot y1.val) (slot z1.val) (slot x2.val) (slot y2.val)
        (slot z2.val)))) s fun t =>
      Frame s₀ base t ∧ Same base (temps ++ [x1, y1, z1]) s.mem t.mem ∧
      EV t.mem base = genEnv x1 y1 z1 x2 y2 z2 (EV s.mem base) ∧ t.gpr .x19 = s.gpr .x19 := by
  refine block_codeOf (WP.mono (addOps_ok x1 y1 z1 x2 y2 z2 hx1 hy1 hz1 hx2 hy2 hz2 hxy hzx hzy h.scr h.env
    (zero_env h.zero).2) fun t ⟨tk, tb, ts, _, _, _, te⟩ => ⟨⟨tk.scr h.scr, tb, fun w hw => ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ts, te, tk.regs.1 _ (by decide)⟩)
  · have : (19 : Index) ∉ temps ++ [x1, y1, z1] := by
      simp only [temps, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨by decide, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> (subst h; simp at *)
    rw [ts 19 this w hw]; exact h.zero w hw
  · rw [tk.regs.1 _ (by decide)]; exact h.lr
  · rw [tk.regs.1 _ (by decide)]; exact h.out
  · rw [tk.regs.2.1]; exact h.rd
  · rw [tk.regs.2.2]; exact h.wr
  · exact h.mem.trans tk.mem

/-- The doublings' state with `m` of them left. -/
structure DInv (s₀ : State) (base : Addr) (v w : ℤ) (m : Nat) (s : State) : Prop where
  frame : Frame s₀ base s
  counter : s.gpr .x19 = BitVec.ofNat 64 m
  a : Rep (pt (EV s.mem base) 0 1 2) ((2 ^ (4 - m) * v) • baseAff)
  b : Rep (pt (EV s.mem base) 3 4 5) (w • baseAff)

theorem dbl_ok {s₀ s : State} {base : Addr} {v w : ℤ} {m : Nat} (hm : 1 ≤ m) (hm4 : m ≤ 4)
    (h : DInv s₀ base v w m s) :
    WP isa (.block (codeOf (addOps AX AY AZ AX AY AZ) ++ ([.subImm .x .x19 .x19 1] : List Instr))) s
      fun t => DInv s₀ base v w (m - 1) t ∧ (t.gpr .x19 == 0) = decide (m - 1 = 0) := by
  rw [WP.block_append_iff]
  refine WP.mono (addFrame_ok h.frame 0 1 2 0 1 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨tf, ts, te, tc⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.Weak.decCounter_ok (k := m - 1) (by omega)
    (by rw [tc, h.counter]; congr 1; omega)) fun u ⟨uc, ug, um, urd, uwr, uz⟩ => ⟨⟨?_, uc, ?_, ?_⟩, uz⟩
  · exact ⟨tf.scr.of_keeps (rs := [.x19]) ⟨fun r hr => ug r (by simpa using hr), urd, uwr⟩ (by decide),
      by rw [um]; exact tf.env, by rw [um]; exact tf.zero, by rw [ug _ (by decide)]; exact tf.lr,
      by rw [ug _ (by decide)]; exact tf.out, by rw [urd]; exact tf.rd, by rw [uwr]; exact tf.wr, by rw [um]; exact tf.mem⟩
  · have hz := (zero_env h.frame.zero).1
    rw [um, te, genEnv_dbl, hz, genPt_eq]
    have := addPt_rep h.a h.a
    rw [← add_smul] at this
    rw [show (2 : ℤ) ^ (4 - (m - 1)) * v = 2 ^ (4 - m) * v + 2 ^ (4 - m) * v by
      rw [show 4 - (m - 1) = (4 - m) + 1 by omega, pow_succ]; ring]
    exact this
  · rw [um]
    have e : ∀ i : Index, i ∈ [3, 4, 5] → EV t.mem base i = EV s.mem base i := fun i hi => by
      refine Same.env ts ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    simp only [pt]
    rw [e 3 (by simp), e 4 (by simp), e 5 (by simp)]
    exact h.b

/-- **`16 A + B`**: from the comb's last step, `[k] B` in `A`. -/
theorem combine_ok {s₀ s : State} {base : Addr} {k : Nat} (hk : k < 256 ^ 56) (h : StepInv s₀ base k 56 s) :
    WP isa combine s fun t => Frame s₀ base t ∧ Rep (pt (EV t.mem base) 0 1 2) ((k : ℤ) • baseAff) := by
  let v : ℤ := VG.Proof.X448.baseGVal + VG.Proof.X448.oddSumZ k 56
  let w : ℤ := VG.Proof.X448.baseGVal + VG.Proof.X448.evenSumZ k 56
  unfold combine
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok s 4 (by decide))
    fun s1 ⟨c1, g1, m1, rd1, wr1⟩ => ?_)
  have f1 : Frame s₀ base s1 :=
    ⟨h.scr.of_keeps (rs := [.x19]) ⟨fun r hr => g1 r (by simpa using hr), rd1, wr1⟩ (by decide), by rw [m1]; exact h.env,
      by rw [m1]; exact h.zero, by rw [g1 _ (by decide)]; exact h.lr, by rw [g1 _ (by decide)]; exact h.out,
      by rw [rd1]; exact h.rd,
      by rw [wr1]; exact h.wr, by rw [m1]; exact h.mem⟩
  have d1 : DInv s₀ base v w 4 s1 :=
    ⟨f1, c1, by rw [m1]; simpa using h.odd, by rw [m1]; exact h.even⟩
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := fun t => DInv s₀ base v w 0 t)
    (fun m (t : State) => 1 ≤ m ∧ m ≤ 4 ∧ DInv s₀ base v w m t) ?_ 4 s1 ⟨by decide, le_refl _, d1⟩) ?_)
  · intro m t ⟨h1, h4, ht⟩
    refine WP.mono (dbl_ok h1 h4 ht) fun u ⟨hu, hz⟩ => ?_
    simp only [eval, State.read, BitVec.setWidth_eq, bne, hz]
    by_cases hm : m = 1
    · subst hm; exact .inl ⟨rfl, hu⟩
    · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬m - 1 = 0), Bool.not_false], m - 1,
        by omega, by omega, by omega, hu⟩
  · intro t ht
    refine WP.mono (addFrame_ok ht.frame 0 1 2 3 4 5 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)) fun u ⟨uf, _, ue, _⟩ => ⟨uf, ?_⟩
    rw [ue, genEnv_add, (zero_env ht.frame.zero).1, genPt_eq]
    have := addPt_rep ht.a ht.b
    rw [← add_smul, show (2 : ℤ) ^ (4 - 0) * v + w = 16 * v + w by norm_num,
      VG.Proof.X448.comb_total hk] at this
    exact this

end VG.Proof.X448.AArch64.Base
