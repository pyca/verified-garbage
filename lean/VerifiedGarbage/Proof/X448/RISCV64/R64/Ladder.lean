module

public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
import VerifiedGarbage.Proof.X25519.RISCV64.Cswap
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
import VerifiedGarbage.Proof.X448.RISCV64.R64.Mul
import VerifiedGarbage.Proof.X448.RISCV64.R64.AddSub
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
public import VerifiedGarbage.Proof.X448.Ladder
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.X448.RISCV64.R64
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.X448.RISCV64.Field

/-!
# X448 on RISC-V, 64-bit limbs: the field elements, and the ladder

The conditional swap a doubleword at a time (`cswap_ok`, the invariant
`SwapInv64`), as X25519's swap does a word at a time; the field operations of
`Impl/X448/RISCV64/R64.lean` as updates of the elements of `SlotsOk`
(`mulS`, `addS`, `subS`, `cswapS`), as `Proof/X448/RISCV64/Slots.lean` states
them for the 32-bit operations, for slots whose separation (`Sep1`) and
alignment to doublewords (`Sep8`) are decided on their offsets.

Then the ladder, as `Proof/X448/RISCV64/Ladder.lean` proves it: one iteration
(`step_ok`) takes the elements `x1, x2, z2, x3, z3, a24` from the state after
the bits `447` down to `n` (`ladderAfter k x1 n`) to the state after `n - 1`,
with the swap in `t2` and the counter in `t1`; the loop (`ladder_ok`) runs it
for the bits 447 down to 0. The operations' list (`ladOps`), the elements
(`ladV`) and their values after an iteration (`ladOps_vals`) are that
file's, but for the multiplication by `a24`, by the one-word constant
(`mulSmallS`) rather than by its slot (`ladAB_vals`).
-/

-- separate module: its proofs (about 2.5 s) cost more than its imports, and its importer's
-- changes need not re-check them

@[expose] public section

namespace VG.Proof.X448.RISCV64.R64

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64.R64 VG.Proof.X25519 VG.Proof.X25519.RISCV64

section
variable {b : Addr}

/-- While swapping `x` and `y` from `s0`, after `n` doublewords. -/
structure SwapInv64 (b : Addr) (x y sw : Nat) (s0 : State) (n : Nat) (s : State) : Prop where
  rest : Rest [.a2, .a4, .a5] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 x, 8 * n⟩, ⟨b + BitVec.ofNat 64 y, 8 * n⟩] s0.mem s.mem
  lx : ∀ j < n, ew s.mem b x j = sel sw (ew s0.mem b x j) (ew s0.mem b y j)
  ly : ∀ j < n, ew s.mem b y j = sel sw (ew s0.mem b y j) (ew s0.mem b x j)

theorem cswap_ok {x y : Nat} (hx : x + 56 ≤ 2048) (hy : y + 56 ≤ 2048) (hxy : x + 56 ≤ y ∨ y + 56 ≤ x)
    (hx8 : x % 8 = 0) (hy8 : y % 8 = 0)
    {s0 : State} (hc : Ctx b s0) {sw : Nat} (hsw : sw ≤ 1) (h11 : s0.gpr .t0 = 0 - BitVec.ofNat 64 sw) :
    WP isa (.block (cswap x y)) s0 (SwapInv64 b x y sw s0 7) := by
  refine wp_range_flatMap (M := isa) (SwapInv64 b x y sw s0) (fun k s hk h => ?_) 7 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  have wx : dw s.mem b (x + 8 * k) = ew s0.mem b x k :=
    dw_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have wy : dw s.mem b (y + 8 * k) = ew s0.mem b y k :=
    dw_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  unfold cswapStep
  refine ld_ok hcs (d := x + 8 * k) (by omega) (by omega) fun t1 v1 => ?_
  refine ld_ok (hcs.of_rest (v1.rest (ws := [.a2]) (by decide)) (by decide)) (d := y + 8 * k)
    (by omega) (by omega) fun t2 v2 => ?_
  refine wp_xor fun t3 v3 => wp_and fun t4 v4 => ?_
  refine wp_xor fun t5 v5 => wp_xor fun t6 v6 => ?_
  have hr6 : Rest [.a2, .a4, .a5] s t6 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest (by decide))))))
  have hc6 : Ctx b t6 := hcs.of_rest hr6 (by decide)
  refine sd_ok hc6 (d := x + 8 * k) (by omega) (by omega) fun t7 v7 => ?_
  refine sd_ok (hc6.of_rest (v7.rest []) (by decide)) (d := y + 8 * k) (by omega) (by omega)
    fun t8 v8 => ?_
  refine WP.block_nil ?_
  -- The values.
  have eX : t2.gpr .a2 = s.mem.readW (b + BitVec.ofNat 64 (x + 8 * k)) 64 := by
    rw [v2.other _ (by decide), v1.gpr]
  have eY : t2.gpr .a4 = s.mem.readW (b + BitVec.ofNat 64 (y + 8 * k)) 64 := by
    rw [v2.gpr, v1.mem]
  have em : t3.gpr .t0 = 0 - BitVec.ofNat 64 sw := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h11]
  have e6x : t6.gpr .a2 = t2.gpr .a2 ^^^ ((t2.gpr .a2 ^^^ t2.gpr .a4) &&& (0 - BitVec.ofNat 64 sw)) := by
    rw [v6.other _ (by decide), v5.gpr, v4.other _ (by decide), v3.other _ (by decide), v4.gpr, v3.gpr, em]
  have e6y : t6.gpr .a4 = t2.gpr .a4 ^^^ ((t2.gpr .a2 ^^^ t2.gpr .a4) &&& (0 - BitVec.ofNat 64 sw)) := by
    rw [v6.gpr, v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v5.other _ (by decide),
      v4.gpr, v3.gpr, em]
  have hm8 : t8.mem = (s.mem.writeW (b + BitVec.ofNat 64 (x + 8 * k)) (t6.gpr .a2)).writeW
      (b + BitVec.ofNat 64 (y + 8 * k)) (t6.gpr .a4) := by
    rw [v8.mem, v7.gpr, v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  have vx : (t6.gpr .a2).toNat = sel sw (ew s0.mem b x k) (ew s0.mem b y k) := by
    rw [e6x, eX, eY, ← wx, ← wy]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0]; rfl
    · rw [sel1]; rfl
  have vy : (t6.gpr .a4).toNat = sel sw (ew s0.mem b y k) (ew s0.mem b x k) := by
    rw [e6y, eX, eY, ← wx, ← wy]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0']; rfl
    · rw [sel1']; rfl
  refine ⟨h.rest.trans (hr6.trans ((v7.rest _).trans (v8.rest _))), ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [hm8]
    refine ((h.frame.sub fun r hr => ?_).writeW (List.mem_cons_self ..) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega)⟩
  · rw [ew, hm8, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.lx j hj
    · rw [dw_write_self, vx]
  · rw [ew, hm8]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega),
        dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.ly j hj
    · rw [dw_write_self, vy]

end

end

section

open VG VG.RISCV64 VG.Impl.X448.RISCV64.R64 VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Proof.X448.RISCV64 (V FS SlotsOk upd upd_self upd_of_ne Sep1 sep1_o sep1_get FA
  slots_after frame_FA frame_o swapV limb_frame)
open VG.Impl.X448.RISCV64 (ACC)
open VG.Spec.X448 (P Fe)
open VG.Proof.X448 (toFe toFe_mul toFe_add toFe_sub)

/-- `Sep1`, and every offset a multiple of 8. -/
def Sep8 (o : Nat) (qs : List Nat) : Bool :=
  Sep1 o qs && o % 8 == 0 && qs.all fun q => q % 8 == 0

theorem sep8_sep1 {o : Nat} {qs : List Nat} (h : Sep8 o qs = true) : Sep1 o qs = true := by
  simp only [Sep8, Bool.and_eq_true] at h; exact h.1.1

theorem sep8_o {o : Nat} {qs : List Nat} (h : Sep8 o qs = true) : o % 8 = 0 := by
  simp only [Sep8, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.2

theorem sep8_get {o : Nat} {qs : List Nat} (h : Sep8 o qs = true) {q : Nat} (hq : q ∈ qs) :
    q % 8 = 0 := by
  simp only [Sep8, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.2 q hq
  simpa using this

section
variable {b : Addr}

theorem mulS {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep8 o qs = true)
    (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b qs v) :
    WP isa (mul o x y) s fun s' => Rest clob64 s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (v x * v y)) := by
  have hq1 := sep8_sep1 hq
  refine WP.mono (mul_ok ho (sep1_get hq1 hx).2.1 (sep1_get hq1 hy).2.1 (sep8_o hq)
    (sep8_get hq hx) (sep8_get hq hy) hc)
    fun s' ⟨hr, hf, hv⟩ => ⟨hr, frame_FA ho hf, fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    rw [upd_self, ← hS x hx, ← hS y hy]
    exact toFe_mul hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq1 ho hf hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem addS {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep8 o qs = true)
    (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b qs v) :
    WP isa (.block (add o x y)) s fun s' => Rest clob64 s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (v x + v y)) := by
  have hq1 := sep8_sep1 hq
  have hx' := sep1_get hq1 hx
  have hy' := sep1_get hq1 hy
  have hA := ACC_eq
  refine WP.mono (add_ok (by omega) (by omega) (by omega) (sep8_o hq) (sep8_get hq hx)
    (sep8_get hq hy) hc) fun s' ⟨hr, hf, hv⟩ => ⟨hr, frame_FA ho (frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    rw [upd_self, ← hS x hx, ← hS y hy]
    exact toFe_add hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq1 ho (frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem subS {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep8 o qs = true)
    (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b qs v) :
    WP isa (.block (sub o x y)) s fun s' => Rest clob64 s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (v x - v y)) := by
  have hq1 := sep8_sep1 hq
  have hx' := sep1_get hq1 hx
  have hy' := sep1_get hq1 hy
  have hA := ACC_eq
  refine WP.mono (sub_ok (by omega) (by omega) (by omega) (sep8_o hq) (sep8_get hq hx)
    (sep8_get hq hy) hc) fun s' ⟨hr, hf, hv⟩ => ⟨hr, frame_FA ho (frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    rw [upd_self, ← hS x hx, ← hS y hy]
    exact toFe_sub hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq1 ho (frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

/-- `a24 · [x]`, the ladder's multiplication by a one-word constant. -/
theorem mulSmallS {o x : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep8 o qs = true)
    (ho : o + 56 ≤ ACC) (hx : x ∈ qs) {s : State} (hc : Ctx b s) (hS : SlotsOk s.mem b qs v) :
    WP isa (.block (mulSmall o x 39081)) s fun s' => Rest clob64 s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (VG.Spec.X448.a24 * v x)) := by
  have hq1 := sep8_sep1 hq
  have hx' := sep1_get hq1 hx
  have hA := ACC_eq
  have hK : (sext32 (39081 : BitVec 32)).toNat = 39081 := by decide
  refine WP.mono (mulSmall_ok (by rw [hK]; decide) (by rw [hK]; decide) (by omega) (by omega)
    (sep8_o hq) (sep8_get hq hx) hc) fun s' ⟨hr, hf, hv⟩ => ⟨hr, frame_FA ho (frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    rw [upd_self, ← hS x hx]
    rw [hK] at hv
    exact toFe_mul hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq1 ho (frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

/-- The number of an element is unchanged if its doublewords are. -/
theorem V_congr64 {m m' : Mem} {q q' : Nat} (h : ∀ k < 7, ew m' b q k = ew m b q' k) :
    V m' b q = V m b q' := by
  rw [V_eq, V_eq]; exact val7_congr h

theorem cswapS {x y : Nat} {qs : List Nat} {v : Nat → Fe}
    (hq : Sep8 x qs = true) (hq' : Sep8 y qs = true)
    (hx : x ∈ qs) (hy : y ∈ qs) (hxy : x + 56 ≤ y ∨ y + 56 ≤ x) {s : State} (hc : Ctx b s) {sw : Nat}
    (hsw : sw ≤ 1) (h11 : s.gpr .t0 = 0 - BitVec.ofNat 64 sw) (hS : SlotsOk s.mem b qs v) :
    WP isa (.block (cswap x y)) s fun s' => Rest [.a2, .a4, .a5] s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b qs (swapV x y sw v) := by
  have hq1 := sep8_sep1 hq
  have hq1' := sep8_sep1 hq'
  have hx' := sep1_get hq1 hx
  have hy' := sep1_get hq1 hy
  have hA := ACC_eq
  refine WP.mono (cswap_ok (b := b) (by omega) (by omega) hxy (sep8_get hq hx) (sep8_get hq hy)
    hc hsw h11)
    fun s' h => ⟨h.rest, ?_, ?_⟩
  · refine h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega)
  · intro q hq''
    have hlx : ∀ k < 7, ew s'.mem b x k = sel sw (ew s.mem b x k) (ew s.mem b y k) := h.lx
    have hly : ∀ k < 7, ew s'.mem b y k = sel sw (ew s.mem b y k) (ew s.mem b x k) := h.ly
    by_cases hqx : q = x
    · subst hqx
      simp only [swapV, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · rw [FS, V_congr64 (m := s.mem) (m' := s'.mem) (q' := q) fun k hk => by rw [hlx k hk]; rfl]; exact hS q hx
      · rw [FS, V_congr64 (m := s.mem) (m' := s'.mem) (q' := y) fun k hk => by rw [hlx k hk]; rfl]; exact hS y hy
    by_cases hqy : q = y
    · subst hqy
      simp only [swapV, hqx, ite_false, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · rw [FS, V_congr64 (m := s.mem) (m' := s'.mem) (q' := q) fun k hk => by rw [hly k hk]; rfl]; exact hS q hy
      · rw [FS, V_congr64 (m := s.mem) (m' := s'.mem) (q' := x) fun k hk => by rw [hly k hk]; rfl]; exact hS x hx
    · simp only [swapV, hqx, hqy, ite_false]
      obtain ⟨h1, h3, -⟩ := sep1_get hq1 hq''
      obtain ⟨h1', -⟩ := sep1_get hq1' hq''
      rw [FS, V_congr64 (m := s.mem) (m' := s'.mem) (q' := q) fun k hk => dw_frame h.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)]
      exact hS q hq''

end

end

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64.R64 VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64 (X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB A24 ACC BITS)
open VG.Proof.X448.RISCV64 (FS SlotsOk SlotsOk.mono SlotsOk.congr upd FA swapV FOp FOp.out FOp.x FOp.y
  FOp.val runOps outsQ ladOps LQ ladV ladOps_vals ofNat_xor xor_le_one Bits cswap_fst cswap_snd)
open VG.Spec.X448 (P Fe Ladder ladderStep cswap a24)
open VG.Proof.X448 (toFe ladderAfter ladderAfter_step ladderStep_eq bit bit_le ladderAfter_swap_le)

/-- The registers the code changes: all but the pointers to `out` (`a0`) and
the working space (`a3`). -/
abbrev work : List Reg := [.t2, .t1, .t0, .t3, .t4, .t5, .t6, .a1, .a2, .a4, .a5, .a6, .a7]

/-- `s'` is `s` but for the registers `work` and the field area. -/
structure Stp (b : Addr) (s s' : State) : Prop where
  rest : Rest work s s'
  frame : Frame [FA b] s.mem s'.mem

theorem Stp.refl (b : Addr) (s : State) : Stp b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem Stp.trans {b : Addr} {s₁ s₂ s₃ : State} (h₁ : Stp b s₁ s₂) (h₂ : Stp b s₂ s₃) : Stp b s₁ s₃ :=
  ⟨h₁.rest.trans h₂.rest, h₁.frame.trans h₂.frame⟩

theorem Stp.of_rest {b : Addr} {s s' : State} {ws : List Reg} (hr : Rest ws s s')
    (hws : ∀ r ∈ ws, r ∈ work) (hm : s'.mem = s.mem) : Stp b s s' :=
  ⟨hr.mono hws, by rw [hm]; exact Frame.refl _ _⟩

/-- Between field operations, from `s0`: `t2` and `t1` hold `a` and `c`,
and the slots `qs` the elements `v`. -/
structure Cur (b : Addr) (s0 : State) (a c : BitVec 64) (qs : List Nat) (v : Nat → Fe) (s : State) :
    Prop where
  ctx : Ctx b s
  stp : Stp b s0 s
  t2 : s.gpr .t2 = a
  t1 : s.gpr .t1 = c
  slots : SlotsOk s.mem b qs v

section
variable {b : Addr} {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe}

theorem Cur.next {s s' : State} (h : Cur b s0 a c qs v s) (hr : Rest clob64 s s')
    (hf : Frame [FA b] s.mem s'.mem) {qs' : List Nat} {v' : Nat → Fe}
    (hS : SlotsOk s'.mem b qs' v') : Cur b s0 a c qs' v' s' :=
  ⟨h.ctx.of_rest hr (by decide), h.stp.trans ⟨hr.mono (by decide), hf⟩,
    by rw [hr.gpr _ (by decide), h.t2], by rw [hr.gpr _ (by decide), h.t1], hS⟩

theorem opMul {o x y : Nat} (hq : Sep8 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (mul o x y) s (Cur b s0 a c (o :: qs) (upd v o (v x * v y))) :=
  WP.mono (mulS hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

theorem opAdd {o x y : Nat} (hq : Sep8 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (.block (add o x y)) s (Cur b s0 a c (o :: qs) (upd v o (v x + v y))) :=
  WP.mono (addS hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

theorem opSub {o x y : Nat} (hq : Sep8 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (.block (sub o x y)) s (Cur b s0 a c (o :: qs) (upd v o (v x - v y))) :=
  WP.mono (subS hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

theorem opMulSmall {o x : Nat} (hq : Sep8 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (.block (mulSmall o x 39081)) s (Cur b s0 a c (o :: qs) (upd v o (a24 * v x))) :=
  WP.mono (mulSmallS hq ho hx h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

end

/-! ## Sequences of field operations -/

/-- A field operation's code. -/
def fcode : FOp → Prog isa
  | .mul o x y => Impl.X448.RISCV64.R64.mul o x y
  | .add o x y => .block (Impl.X448.RISCV64.R64.add o x y)
  | .sub o x y => .block (Impl.X448.RISCV64.R64.sub o x y)

/-- The operations `ops`, then `k`. -/
def opsCode : List FOp → Prog isa → Prog isa
  | [], k => k
  | op :: ops, k => .seq (fcode op) (opsCode ops k)

/-- Each operation's slots are separate or equal, below `ACC`, and its inputs
known. -/
def opsOk : List FOp → List Nat → Bool
  | [], _ => true
  | op :: ops, qs => Sep8 op.out qs && op.out + 56 ≤ ACC && qs.contains op.x &&
      qs.contains op.y && opsOk ops (op.out :: qs)

theorem op_ok {b : Addr} {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe} (op : FOp)
    (hq : Sep8 op.out qs = true) (ho : op.out + 56 ≤ ACC) (hx : op.x ∈ qs) (hy : op.y ∈ qs)
    {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (fcode op) s (Cur b s0 a c (op.out :: qs) (upd v op.out (op.val v))) := by
  cases op with
  | mul o x y => exact opMul hq ho hx hy h
  | add o x y => exact opAdd hq ho hx hy h
  | sub o x y => exact opSub hq ho hx hy h

theorem ops_ok {b : Addr} {s0 : State} {a c : BitVec 64} {k : Prog isa} {Q : State → Prop} :
    ∀ (ops : List FOp) (qs : List Nat) (v : Nat → Fe) (s : State), opsOk ops qs = true →
      Cur b s0 a c qs v s → (∀ s', Cur b s0 a c (outsQ ops qs) (runOps ops v) s' → WP isa k s' Q) →
      WP isa (opsCode ops k) s Q
  | [], _, _, s, _, h, hk => hk s h
  | op :: ops, qs, v, s, hok, h, hk => by
    simp only [opsOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok
    obtain ⟨⟨⟨⟨h1, h3⟩, h4⟩, h5⟩, h6⟩ := hok
    exact WP.seq (WP.mono (op_ok op h1 h3 h4 h5 h) fun s' h' => ops_ok ops _ _ s' h6 h' hk)

/-! ## One iteration -/

theorem ladOps_ok : opsOk ladOps LQ = true := by decide

/-- The loop invariant of the ladder from `sL`, before the iteration for the
bit `n - 1`. -/
structure LadInv (b : Addr) (k : Nat) (x1 : Fe) (sL : State) (n : Nat) (s : State) : Prop where
  cur : Cur b sL (BitVec.ofNat 64 (ladderAfter k x1 n).swap) (BitVec.ofNat 64 n) LQ
    (ladV x1 (ladderAfter k x1 n)) s

theorem head_ok {b : Addr} {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 448) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa (.block stepHead) s (Cur b sL (BitVec.ofNat 64 (bit k (n - 1))) (BitVec.ofNat 64 (n - 1)) LQ
      (swapV Z2 Z3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1))
        (swapV X2 X3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) (ladV x1 (ladderAfter k x1 n))))) := by
  obtain ⟨hcur⟩ := h
  have hc := hcur.ctx
  have hB : BITS = 1064 := rfl
  have hA := ACC_eq
  have hsw := ladderAfter_swap_le k x1 hn'
  have hbt := bit_le k (n - 1)
  have hx := xor_le_one hsw hbt
  simp only [stepHead, mask, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_subi (by decide) fun s1 u1 => ?_
  have e12 : s1.gpr .t1 = BitVec.ofNat 64 (n - 1) := by
    rw [u1.gpr, hcur.t1, ofNat_sub_one hn (by omega_arith)]
  refine wp_add fun s2 u2 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 (n - 1 + BITS)) (by decide)
    (by rw [u2.gpr, e12, u1.other _ (by decide), hc.a3, Offset.add_add])
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hc.inR (by omega_arith)) fun s3 u3 => ?_
  have e4 : s3.gpr .a1 = BitVec.ofNat 64 (bit k (n - 1)) := by
    rw [u3.gpr, u2.mem, u1.mem, hcur.stp.frame _ fun r hr => ?_, Nat.add_comm, hbits _ (by omega_arith)]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    · rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := n - 1 + BITS) (n := 1) (k := ACC + 112) (by omega_arith)
        (by omega_arith) _ (Region.contains_self _ _) h
  refine wp_xor fun s4 u4 => ?_
  have e0 : s4.gpr .t2 = BitVec.ofNat 64 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) := by
    rw [u4.gpr, e4, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hcur.t2,
      ofNat_xor (by omega_arith) (by omega_arith)]
  refine wp_li (by decide) fun s5 u5 => wp_sub fun s6 u6 => ?_
  have e11 : s6.gpr .t0 = 0 - BitVec.ofNat 64 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) := by
    rw [u6.gpr, u5.gpr, u5.other _ (by decide), e0]; rfl
  have hr6 : Rest [.t2, .a1, .t0, .t1] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  have hm6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hc6 : Ctx b s6 := hc.of_rest hr6 (by decide)
  have hS6 : SlotsOk s6.mem b LQ (ladV x1 (ladderAfter k x1 n)) := by
    rw [hm6]; exact hcur.slots
  refine WP.append (cswapS (by decide) (by decide) (by decide) (by decide) (by decide)
    hc6 hx e11 hS6) fun s7 ⟨hr7, hf7, hS7⟩ => ?_
  have hc7 : Ctx b s7 := hc6.of_rest hr7 (by decide)
  refine WP.append (cswapS (by decide) (by decide) (by decide) (by decide) (by decide)
    hc7 hx (by rw [hr7.gpr _ (by decide), e11]) hS7) fun s8 ⟨hr8, hf8, hS8⟩ => ?_
  refine wp_addi (by decide) fun s9 u9 => WP.block_nil ?_
  have hr9 : Rest [.t2, .a1, .a2, .a4, .a5, .t0, .t1] s s9 :=
    (hr6.mono (by decide)).trans ((hr7.mono (by decide)).trans ((hr8.mono (by decide)).trans
      (u9.rest (by decide))))
  exact ⟨hc.of_rest hr9 (by decide),
    hcur.stp.trans ⟨hr9.mono (by decide), by rw [u9.mem, ← hm6]; exact hf7.trans hf8⟩,
    by rw [u9.gpr, hr8.gpr _ (by decide), hr7.gpr _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), e4, BitVec.add_zero],
    by rw [u9.other _ (by decide), hr8.gpr _ (by decide), hr7.gpr _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e12],
    by rw [u9.mem]; exact hS8⟩

/-- The operations of an iteration before its multiplication by `a24`, and
after it. -/
def ladA : List FOp := ladOps.take 15
def ladB : List FOp := ladOps.drop 16

theorem step_eq : step = .seq (.block stepHead)
    (opsCode ladA (.seq (.block (mulSmall Z2 E 39081)) (opsCode ladB (.block [])))) := rfl

theorem ladA_ok : opsOk ladA LQ = true := by decide

theorem ladB_ok : opsOk ladB (Z2 :: outsQ ladA LQ) = true := by decide

/-- The multiplication by `a24` is `ladOps`'s by the slot `A24`, which holds `a24`. -/
theorem ladAB_vals (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) (q : Nat) :
    runOps ladB (upd (runOps ladA (swapV Z2 Z3 (st.swap ^^^ bit k t) (swapV X2 X3 (st.swap ^^^ bit k t)
      (ladV x1 st)))) Z2 (a24 * runOps ladA (swapV Z2 Z3 (st.swap ^^^ bit k t)
        (swapV X2 X3 (st.swap ^^^ bit k t) (ladV x1 st))) E)) q =
    runOps ladOps (swapV Z2 Z3 (st.swap ^^^ bit k t) (swapV X2 X3 (st.swap ^^^ bit k t)
      (ladV x1 st))) q := by
  simp only [ladA, ladB, ladOps, List.take, List.drop, runOps, FOp.out, FOp.val, upd, swapV, ladV,
    X1, X2, Z2, X3, Z3, A, B, C, D, AA, BB, E, DA, CB, A24, Nat.reduceEqDiff, ↓reduceIte]

theorem step_ok {b : Addr} {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 448) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa step s fun s' => LadInv b k x1 sL (n - 1) s' ∧ (s'.gpr .t1 != 0) = decide (n - 1 ≠ 0) := by
  rw [step_eq]
  refine WP.seq (WP.mono (head_ok hbits hn hn' h) fun s1 h1 =>
    ops_ok ladA LQ _ s1 ladA_ok h1 fun s2 h2 => ?_)
  refine WP.seq (WP.mono (opMulSmall (o := Z2) (x := E) (by decide) (by decide) (by decide) h2)
    fun s3 h3 => ops_ok ladB _ _ s3 ladB_ok h3 fun s4 h4 => ?_)
  refine WP.block_nil ⟨⟨h4.ctx, h4.stp, ?_, h4.t1, ?_⟩, ?_⟩
  · rw [h4.t2, ladderAfter_step k x1 (show n - 1 < 448 by omega_arith), Nat.sub_add_cancel hn,
      ladderStep_eq]
  · refine (h4.slots.mono (by decide)).congr fun q hq => ?_
    rw [ladderAfter_step k x1 (show n - 1 < 448 by omega_arith), Nat.sub_add_cancel hn,
      ladAB_vals]
    exact ladOps_vals k x1 _ (n - 1) q hq
  · rw [h4.t1, ofNat_ne_zero (by omega_arith)]

/-- The ladder, from the state with the bits of the scalar in `BITS` and the
initial elements in `LQ`. -/
theorem ladder_ok {b : Addr} {k : Nat} {x1 : Fe} {s : State} (hc : Ctx b s) (hbits : Bits b k s.mem)
    (hS : SlotsOk s.mem b LQ (ladV x1 (VG.Proof.X448.init x1))) :
    WP isa ladder s fun s' => Stp b s s' ∧ Ctx b s' ∧
      s'.gpr .t2 = BitVec.ofNat 64 (ladderAfter k x1 0).swap ∧
      SlotsOk s'.mem b LQ (ladV x1 (ladderAfter k x1 0)) := by
  unfold ladder
  refine WP.seq (wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ?_)
  have hr2 : Rest [.t2, .t1] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hbits2 : Bits b k s2.mem := by rw [hm2]; exact hbits
  have h448 : LadInv b k x1 s2 448 s2 :=
    ⟨⟨hc.of_rest hr2 (by decide), Stp.refl _ _, by rw [u2.gpr]; rfl,
      by rw [u2.other _ (by decide), u1.gpr], by rw [hm2]; exact hS⟩⟩
  have hst : Stp b s s2 := Stp.of_rest hr2 (by decide) hm2
  refine WP.mono (Q := LadInv b k x1 s2 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 448 ∧ LadInv b k x1 s2 m s') ?_ 448 s2 ⟨by decide, Nat.le_refl _, h448⟩)
    fun s' ⟨h'⟩ => ⟨hst.trans h'.stp, h'.ctx, h'.t2, h'.slots⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (step_ok hbits2 h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_nonzero, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [hm], m - 1, by omega_arith, by omega_arith, by omega_arith, hl'⟩

end

end VG.Proof.X448.RISCV64.R64
