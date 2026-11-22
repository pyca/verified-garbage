module

public import VerifiedGarbage.Proof.X448.Invert
public import VerifiedGarbage.Proof.X448.PPC64LE.Slots
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X448.Ladder
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallOf
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `X448.PPC64LE.Ladder`, which this module and modules that import it used -/

section

/-!
# X448 on PPC64LE: the ladder

One iteration of the ladder (`step_ok`) takes the elements `x1, x2, z2, x3,
z3` from the state after the bits `447` down to `n` (`ladderAfter k x1
n`) to the state after `n - 1`, with the swap in `r0` and the counter in
`r12`; the loop (`ladder_ok`) runs it for the bits 447 down to 0.

The field operations (`FOp`, `opsCodeW`) take the multiplication as a
parameter, and the state between them (`CurW`, `StpW`) the registers that
may change (`MulCur`): `opsCode`, `Cur` and `Stp` are those of `mul` and
`work` (`mulCur_mul`), which X448's ladder and Ed448's proofs use.
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P Fe Ladder ladderStep cswap a24)
open VG.Proof.X448 (toFe ladderAfter ladderAfter_step ladderStep_eq bit bit_le ladderAfter_swap_le)

/-- The registers the field operations change: all but the pointers to `out`
(`r3`) and the working space (`r6`), and `r14`, which Ed448's loops keep a
value in; the caller restores `r15`–`r31`, which the multiplication uses. -/
abbrev work : List Reg :=
  [.r0, .r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23,
    .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- `s'` is `s` but for the registers `W` and the field area. -/
structure StpW (W : List Reg) (b : Addr) (s s' : State) : Prop where
  rest : Rest W s s'
  frame : Frame [FA b] s.mem s'.mem

/-- `s'` is `s` but for the registers `work` and the field area. -/
abbrev Stp := StpW work

theorem StpW.refl (W : List Reg) (b : Addr) (s : State) : StpW W b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem StpW.trans {W : List Reg} {b : Addr} {s₁ s₂ s₃ : State} (h₁ : StpW W b s₁ s₂) (h₂ : StpW W b s₂ s₃) :
    StpW W b s₁ s₃ :=
  ⟨h₁.rest.trans h₂.rest, h₁.frame.trans h₂.frame⟩

theorem StpW.of_rest {W : List Reg} {b : Addr} {s s' : State} {ws : List Reg} (hr : Rest ws s s')
    (hws : ∀ r ∈ ws, r ∈ W) (hm : s'.mem = s.mem) : StpW W b s s' :=
  ⟨hr.mono hws, by rw [hm]; exact Frame.refl _ _⟩

theorem StpW.mono {W W' : List Reg} {b : Addr} {s s' : State} (h : StpW W b s s') (hW : ∀ r ∈ W, r ∈ W') :
    StpW W' b s s' :=
  ⟨h.rest.mono hW, h.frame⟩

theorem Stp.refl (b : Addr) (s : State) : Stp b s s := StpW.refl _ _ _

theorem Stp.trans {b : Addr} {s₁ s₂ s₃ : State} (h₁ : Stp b s₁ s₂) (h₂ : Stp b s₂ s₃) : Stp b s₁ s₃ :=
  StpW.trans h₁ h₂

theorem Stp.of_rest {b : Addr} {s s' : State} {ws : List Reg} (hr : Rest ws s s')
    (hws : ∀ r ∈ ws, r ∈ work) (hm : s'.mem = s.mem) : Stp b s s' :=
  StpW.of_rest hr hws hm

/-- Between field operations, from `s0`: `r0` and `r12` hold `a` and `c`,
and the slots `qs` the elements `v`; only the registers `W` changed. -/
structure CurW (W : List Reg) (b : Addr) (s0 : State) (a c : BitVec 64) (qs : List Nat) (v : Nat → Fe)
    (s : State) : Prop where
  ctx : Ctx b s
  stp : StpW W b s0 s
  r0 : s.gpr .r0 = a
  r12 : s.gpr .r12 = c
  slots : SlotsOk s.mem b qs v

/-- `CurW` with only the registers of `work` changed. -/
abbrev Cur := CurW work

section
variable {W : List Reg} {b : Addr} {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe}

/-- A step that changes only the registers `ws` (not `r0`, `r6` or `r12`) of `W`. -/
theorem CurW.nextR {ws : List Reg} (hws : ∀ r ∈ ws, r ∈ W) (h0 : Reg.r0 ∉ ws) (h6 : Reg.r6 ∉ ws)
    (h12 : Reg.r12 ∉ ws) {s s' : State} (h : CurW W b s0 a c qs v s) (hr : Rest ws s s')
    (hf : Frame [FA b] s.mem s'.mem) {qs' : List Nat} {v' : Nat → Fe}
    (hS : SlotsOk s'.mem b qs' v') : CurW W b s0 a c qs' v' s' :=
  ⟨h.ctx.of_rest hr h6, h.stp.trans ⟨hr.mono hws, hf⟩,
    by rw [hr.gpr _ h0, h.r0], by rw [hr.gpr _ h12, h.r12], hS⟩

theorem CurW.next (hW : ∀ r ∈ clob, r ∈ W) {s s' : State} (h : CurW W b s0 a c qs v s)
    (hr : Rest clob s s') (hf : Frame [FA b] s.mem s'.mem) {qs' : List Nat} {v' : Nat → Fe}
    (hS : SlotsOk s'.mem b qs' v') : CurW W b s0 a c qs' v' s' :=
  h.nextR hW (by decide) (by decide) (by decide) hr hf hS

theorem Cur.next {s s' : State} (h : Cur b s0 a c qs v s) (hr : Rest clob s s')
    (hf : Frame [FA b] s.mem s'.mem) {qs' : List Nat} {v' : Nat → Fe}
    (hS : SlotsOk s'.mem b qs' v') : Cur b s0 a c qs' v' s' :=
  CurW.next (by decide) h hr hf hS

theorem opMul {o x y : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) (ho4 : o % 4 = 0) {s : State}
    (h : Cur b s0 a c qs v s) :
    WP isa (mul o x y) s (Cur b s0 a c (o :: qs) (upd v o (v x * v y))) :=
  WP.mono (mulS hq ho hx hy hx4 hy4 ho4 h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ =>
    h.nextR (by decide) (by decide) (by decide) (by decide) hr hf hS

theorem opAddW (hW : ∀ r ∈ clob, r ∈ W) {o x y : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC)
    (hx : x ∈ qs) (hy : y ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State}
    (h : CurW W b s0 a c qs v s) :
    WP isa (.block (add o x y)) s (CurW W b s0 a c (o :: qs) (upd v o (v x + v y))) :=
  WP.mono (addS hq ho hx hy ho4 hx4 hy4 h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hW hr hf hS

theorem opSubW (hW : ∀ r ∈ clob, r ∈ W) {o x y : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC)
    (hx : x ∈ qs) (hy : y ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State}
    (h : CurW W b s0 a c qs v s) :
    WP isa (.block (sub o x y)) s (CurW W b s0 a c (o :: qs) (upd v o (v x - v y))) :=
  WP.mono (subS hq ho hx hy ho4 hx4 hy4 h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hW hr hf hS

theorem opMul24W (hW : ∀ r ∈ clob, r ∈ W) {o x : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC)
    (hx : x ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) {s : State} (h : CurW W b s0 a c qs v s) :
    WP isa (.block (mulA24 o x)) s (CurW W b s0 a c (o :: qs) (upd v o (a24 * v x))) :=
  WP.mono (mul24S hq ho hx ho4 hx4 h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hW hr hf hS

theorem opAdd {o x y : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (.block (add o x y)) s (Cur b s0 a c (o :: qs) (upd v o (v x + v y))) :=
  opAddW (by decide) hq ho hx hy ho4 hx4 hy4 h

theorem opSub {o x y : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (.block (sub o x y)) s (Cur b s0 a c (o :: qs) (upd v o (v x - v y))) :=
  opSubW (by decide) hq ho hx hy ho4 hx4 hy4 h

theorem opMul24 {o x : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (.block (mulA24 o x)) s (Cur b s0 a c (o :: qs) (upd v o (a24 * v x))) :=
  opMul24W (by decide) hq ho hx ho4 hx4 h

end

/-- A multiplication `m` takes `CurW W` to `CurW W` with the product in its slot. -/
def MulCur (W : List Reg) (m : Nat → Nat → Nat → Prog isa) : Prop :=
  ∀ {b : Addr} {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe} {o x y : Nat},
    Sep1 o qs = true → o + 56 ≤ ACC → x ∈ qs → y ∈ qs → x % 4 = 0 → y % 4 = 0 → o % 4 = 0 →
    ∀ {s : State}, CurW W b s0 a c qs v s → WP isa (m o x y) s (CurW W b s0 a c (o :: qs) (upd v o (v x * v y)))

theorem mulCur_mul : MulCur work mul := fun hq ho hx hy hx4 hy4 ho4 _ h => opMul hq ho hx hy hx4 hy4 ho4 h

/-- `vg_x448_mul_core` writes no link register. -/
theorem mulCore_lrSafe : lrSafe (.block mulCore) = true := by
  have hch : ∀ k r, (chainR k r).writesLr = false := fun k r => by unfold chainR; split <;> rfl
  have hc : ∀ k, ((colR k).all fun i => !i.writesLr) = true := fun k => by
    simp [colR, firstR, termR, Instr.writesLr]
  have hr : (reduceR.all fun i => !i.writesLr) = true := by
    simp only [reduceR, chain7, rotR, List.all_append, List.all_cons, List.all_map, List.all_flatMap,
      List.all_nil, Function.comp_def, hch]
    simp [Instr.writesLr]
  show lrSafeBlock mulCore = true
  rw [show lrSafeBlock mulCore = mulCore.all (fun i => !i.writesLr) from rfl]
  simp only [mulCore, List.all_append, List.all_cons, List.all_nil, hr, List.all_flatMap, hc]
  simp [Instr.writesLr]

/-- `mul_ok`, for `mulC`: the product a call of `vg_x448_mul_core`, which
gives `r12` and `r0` back as they were. -/
theorem mulC_ok {b : Addr} {o x y : Nat} (ho : o + 56 ≤ ACC) (hx : x + 56 ≤ ACC)
    (hy : y + 56 ≤ ACC) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) (ho4 : o % 4 = 0) {s : State}
    (hc : Ctx b s) :
    WP isa (mulC o x y) s fun s' => Ctx b s' ∧ Rest clobR s s' ∧
      Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x * V s.mem b y) % P := by
  have hA := ACC_eq
  unfold mulC
  simp only [List.append_assoc]
  refine WP.seq ?_
  -- The operands, and `r12` and `r0` into `r4` and `r5`.
  refine ldsAt_ok (l := slotsOf opA 7) hx4 (slotsOf_fit hx4 (by omega_using [hx, hA])) (by decide) (by decide) hc
    fun s2 hc2 r2 m2 _ v2 => ?_
  refine ldsAt_ok (l := slotsOf opB 7) hy4 (slotsOf_fit hy4 (by omega_using [hy, hA])) (by decide) (by decide) hc2
    fun s3 hc3 r3 m3 _ v3 => ?_
  refine wp_addi (by decide) (by decide) fun s4 u4 => WP.cons exec_logic ?_
  refine WP.block_nil ?_
  generalize hs5 : s4.write .r5 (s4.gpr .r0 ||| s4.gpr .r0) = s5
  obtain u5 : Upd s4 s5 .r5 (s4.gpr .r0 ||| s4.gpr .r0) := hs5 ▸ Upd.write _ _ _
  obtain hr5 : Rest [.r4, .r5] s3 s5 := (u4.rest (by decide)).trans (u5.rest (by decide))
  obtain hc5 : Ctx b s5 := hc3.of_rest hr5 (by decide)
  obtain k12 : s5.gpr .r4 = s.gpr .r12 := by
    rw [u5.other _ (by decide), u4.gpr, BitVec.add_zero, r3.gpr _ (by decide), r2.gpr _ (by decide)]
  obtain k0 : s5.gpr .r5 = s.gpr .r0 := by
    rw [u5.gpr, BitVec.or_self, u4.other _ (by decide), r3.gpr _ (by decide), r2.gpr _ (by decide)]
  obtain opsA : ∀ i < 7, (s5.gpr (opA i)).toNat = ew s.mem b x i := fun i hi => by
    rw [hr5.gpr _ (by revert i; decide), r3.gpr _ (by revert i; decide),
      v2 (opA i, 8 * i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩), Offset.add_add]; rfl
  obtain opsB : ∀ j < 7, (s5.gpr (opB j)).toNat = ew s.mem b y j := fun j hj => by
    rw [hr5.gpr _ (by revert j; decide), v3 (opB j, 8 * j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩),
      m2, Offset.add_add]; rfl
  obtain m5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, m3, m2]
  -- The call.
  refine WP.seq (WP.callSafe mulCore_lrSafe ?_)
  obtain e4 : s5.callEntry.gpr .r4 = s.gpr .r12 := by rw [State.callEntry_gpr _ (by decide), k12]
  obtain e5 : s5.callEntry.gpr .r5 = s.gpr .r0 := by rw [State.callEntry_gpr _ (by decide), k0]
  obtain hce : Ctx b s5.callEntry :=
    ⟨by rw [State.callEntry_gpr _ (by decide)]; exact hc5.r6, by rw [State.callEntry_wr]; exact hc5.wr⟩
  unfold mulCore
  refine wp_addi (by decide) (by decide) fun s6 u6 => wp_addi (by decide) (by decide) fun s7 u7 => ?_
  refine wp_li (by decide) fun s8 u8 => wp_li (by decide) fun s9 u9 => ?_
  obtain hr9 : Rest [.r12, .r0, Impl.X448.PPC64LE.pw 0, Impl.X448.PPC64LE.pw 1] s5.callEntry s9 :=
    (((u6.rest (by decide)).trans (u7.rest (by decide))).trans (u8.rest (by decide))).trans (u9.rest (by decide))
  refine WP.append (columns_ok (b := b) (hce.of_rest hr9 (by decide))
    (by rw [u9.other _ (by decide), u8.gpr]; rfl) (by rw [u9.gpr]; rfl)) fun s10 ⟨hc10, r10, m10, v10⟩ => ?_
  obtain hA10 : colsV (fun i => (s9.gpr (opA i)).toNat) 7 = V s.mem b x := by
    rw [V_eq_cols]; exact colsV_congr fun i hi => by
      rw [hr9.gpr _ (by revert i; decide), State.callEntry_gpr _ (by revert i; decide), opsA i hi]
  obtain hB10 : colsV (fun j => (s9.gpr (opB j)).toNat) 7 = V s.mem b y := by
    rw [V_eq_cols]; exact colsV_congr fun j hj => by
      rw [hr9.gpr _ (by revert j; decide), State.callEntry_gpr _ (by revert j; decide), opsB j hj]
  rw [hA10, hB10] at v10
  refine WP.mono (reduceR_ok hc10) fun s11 ⟨hc11, r11, m11, v11⟩ => ?_
  -- The result stored at `o`.
  rw [← List.append_nil (stdsAt o (slotsOf Impl.X448.PPC64LE.pw 7))]
  refine stdsAt_ok (l := slotsOf Impl.X448.PPC64LE.pw 7) ho4 (slotsOf_fit ho4 (by omega_using [ho, hA])) hc11
    fun s12 g12 rd12 wr12 sp12 mem12 => WP.block_nil ⟨⟨by rw [g12]; exact hc11.r6, by rw [wr12]; exact hc11.wr⟩,
      ⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [congrFun g12, r11.gpr _ hr, r10.gpr _ hr]
    by_cases h12 : r = .r12
    · subst h12
      rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.gpr, BitVec.add_zero, e4]
    by_cases h0 : r = .r0
    · subst h0
      rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr, BitVec.add_zero, u6.other _ (by decide), e5]
    have hp : r ∉ [Reg.r12, .r0, Impl.X448.PPC64LE.pw 0, Impl.X448.PPC64LE.pw 1] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h12, h0, fun e => hr (e ▸ by decide), fun e => hr (e ▸ by decide)⟩
    have hl : r ∉ linkRegs := by
      simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h0, fun e => hr (e ▸ by decide), h12⟩
    rw [hr9.gpr _ hp, State.callEntry_gpr _ hl, hr5.gpr _ (fun e => hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at e; rcases e with rfl | rfl <;> decide)),
      r3.gpr _ (fun h => hr (by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h; exact opsB_in q hq)),
      r2.gpr _ (fun h => hr (by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h; exact opsA_in q hq))]
  · rw [rd12, r11.rd, r10.rd, hr9.rd, State.callEntry_rd, hr5.rd, r3.rd, r2.rd]
  · rw [wr12, r11.wr, r10.wr, hr9.wr, State.callEntry_wr, hr5.wr, r3.wr, r2.wr]
  · rw [sp12, r11.sp, r10.sp, hr9.sp, State.callEntry_sp, hr5.sp, r3.sp, r2.sp]
  · rw [mem12, m11, m10, u9.mem, u8.mem, u7.mem, u6.mem, State.callEntry_mem, m5]
    exact VG.PPC64LE.Spill.saveMem_frame_base (fun p hp => by obtain ⟨i, hi, rfl⟩ := slotsOf_mem hp; omega) (by decide) _ _ _
  · rw [V_eq_cols, ← v10, ← v11]
    congr 1
    refine colsV_congr fun k hk => ?_
    rw [mem12]
    show (Mem.readW _ _ 64).toNat = _
    rw [← Offset.add_add, saved_dw (by decide) _ _ _ hk]



theorem mulCS {b : Addr} {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0)
    (ho4 : o % 4 = 0) {s : State} (hc : Ctx b s) (hS : SlotsOk s.mem b qs v) :
    WP isa (mulC o x y) s fun s' => Rest clobR s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (v x * v y)) := by
  refine WP.mono (mulC_ok ho (sep1_get hq hx).2 (sep1_get hq hy).2 hx4 hy4 ho4 hc)
    fun s' ⟨_, hr, hf1, hv⟩ => ?_
  have hf : Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem s'.mem :=
    hf1.mono fun r hr => by simp [List.mem_singleton.mp hr]
  refine ⟨hr, frame_FA ho hf, fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    rw [upd_self, ← hS x hx, ← hS y hy]
    exact toFe_mul hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq ho hf hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem mulCur_mulC : MulCur work mulC := fun hq ho hx hy hx4 hy4 ho4 _ h =>
  WP.mono (mulCS hq ho hx hy hx4 hy4 ho4 h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ =>
    h.nextR (by decide) (by decide) (by decide) (by decide) hr hf hS
/-! ## Sequences of field operations -/

/-- A field operation: `o = x · y`, `a24 · x`, `x + y` or `x - y`. -/
inductive FOp
  | mul (o x y : Nat)
  | mul24 (o x : Nat)
  | add (o x y : Nat)
  | sub (o x y : Nat)

def FOp.code : FOp → Prog isa
  | .mul o x y => Impl.X448.PPC64LE.mul o x y
  | .mul24 o x => .block (mulA24 o x)
  | .add o x y => .block (Impl.X448.PPC64LE.add o x y)
  | .sub o x y => .block (Impl.X448.PPC64LE.sub o x y)

/-- `FOp.code`, with the multiplication `m`. -/
def FOp.codeW (m : Nat → Nat → Nat → Prog isa) : FOp → Prog isa
  | .mul o x y => m o x y
  | .mul24 o x => .block (mulA24 o x)
  | .add o x y => .block (Impl.X448.PPC64LE.add o x y)
  | .sub o x y => .block (Impl.X448.PPC64LE.sub o x y)

theorem FOp.code_eq (op : FOp) : op.code = op.codeW Impl.X448.PPC64LE.mul := by cases op <;> rfl

def FOp.out : FOp → Nat
  | .mul o _ _ | .mul24 o _ | .add o _ _ | .sub o _ _ => o

def FOp.x : FOp → Nat
  | .mul _ x _ | .mul24 _ x | .add _ x _ | .sub _ x _ => x

def FOp.y : FOp → Nat
  | .mul _ _ y | .add _ _ y | .sub _ _ y => y
  | .mul24 _ x => x

def FOp.val : FOp → (Nat → Fe) → Fe
  | .mul _ x y, v => v x * v y
  | .mul24 _ x, v => a24 * v x
  | .add _ x y, v => v x + v y
  | .sub _ x y, v => v x - v y

/-- The operations `ops`, then `k`. -/
def opsCode : List FOp → Prog isa → Prog isa
  | [], k => k
  | op :: ops, k => .seq op.code (opsCode ops k)

/-- `opsCode`, with the multiplication `m`. -/
def opsCodeW (m : Nat → Nat → Nat → Prog isa) : List FOp → Prog isa → Prog isa
  | [], k => k
  | op :: ops, k => .seq (op.codeW m) (opsCodeW m ops k)

theorem opsCode_eq : ∀ (ops : List FOp) (k : Prog isa), opsCode ops k = opsCodeW Impl.X448.PPC64LE.mul ops k
  | [], _ => rfl
  | op :: ops, k => by rw [opsCode, opsCodeW, FOp.code_eq, opsCode_eq ops k]

/-- Each operation's slots are separate or equal, below `ACC`, and its inputs
known. -/
def opsOk : List FOp → List Nat → Bool
  | [], _ => true
  | op :: ops, qs => Sep1 op.out qs && op.out + 56 ≤ ACC && qs.contains op.x &&
      qs.contains op.y && op.out % 4 == 0 && op.x % 4 == 0 && op.y % 4 == 0 &&
      opsOk ops (op.out :: qs)

/-- The elements after the operations. -/
def runOps : List FOp → (Nat → Fe) → Nat → Fe
  | [], v => v
  | op :: ops, v => runOps ops (upd v op.out (op.val v))

/-- The slots known after the operations. -/
def outsQ : List FOp → List Nat → List Nat
  | [], qs => qs
  | op :: ops, qs => outsQ ops (op.out :: qs)

theorem op_okW {W : List Reg} {m : Nat → Nat → Nat → Prog isa} (hW : ∀ r ∈ clob, r ∈ W) (hm : MulCur W m)
    {b : Addr} {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe} (op : FOp)
    (hq : Sep1 op.out qs = true) (ho : op.out + 56 ≤ ACC) (hx : op.x ∈ qs) (hy : op.y ∈ qs)
    (ho4 : op.out % 4 = 0) (hx4 : op.x % 4 = 0) (hy4 : op.y % 4 = 0) {s : State}
    (h : CurW W b s0 a c qs v s) :
    WP isa (op.codeW m) s (CurW W b s0 a c (op.out :: qs) (upd v op.out (op.val v))) := by
  cases op with
  | mul o x y => exact hm hq ho hx hy hx4 hy4 ho4 h
  | mul24 o x => exact opMul24W hW hq ho hx ho4 hx4 h
  | add o x y => exact opAddW hW hq ho hx hy ho4 hx4 hy4 h
  | sub o x y => exact opSubW hW hq ho hx hy ho4 hx4 hy4 h

theorem ops_okW {W : List Reg} {m : Nat → Nat → Nat → Prog isa} (hW : ∀ r ∈ clob, r ∈ W) (hm : MulCur W m)
    {b : Addr} {s0 : State} {a c : BitVec 64} {k : Prog isa} {Q : State → Prop} :
    ∀ (ops : List FOp) (qs : List Nat) (v : Nat → Fe) (s : State), opsOk ops qs = true →
      CurW W b s0 a c qs v s → (∀ s', CurW W b s0 a c (outsQ ops qs) (runOps ops v) s' → WP isa k s' Q) →
      WP isa (opsCodeW m ops k) s Q
  | [], _, _, s, _, h, hk => hk s h
  | op :: ops, qs, v, s, hok, h, hk => by
    simp only [opsOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h3⟩, h4⟩, h5⟩, h9⟩, h7⟩, h8⟩, h6⟩ := hok
    exact WP.seq (WP.mono (op_okW hW hm op h1 h3 h4 h5 h9 h7 h8 h) fun s' h' => ops_okW hW hm ops _ _ s' h6 h' hk)

theorem op_ok {b : Addr} {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe} (op : FOp)
    (hq : Sep1 op.out qs = true) (ho : op.out + 56 ≤ ACC) (hx : op.x ∈ qs) (hy : op.y ∈ qs)
    (ho4 : op.out % 4 = 0) (hx4 : op.x % 4 = 0) (hy4 : op.y % 4 = 0) {s : State}
    (h : Cur b s0 a c qs v s) :
    WP isa op.code s (Cur b s0 a c (op.out :: qs) (upd v op.out (op.val v))) := by
  rw [FOp.code_eq]; exact op_okW (by decide) mulCur_mul op hq ho hx hy ho4 hx4 hy4 h

theorem ops_ok {b : Addr} {s0 : State} {a c : BitVec 64} {k : Prog isa} {Q : State → Prop} :
    ∀ (ops : List FOp) (qs : List Nat) (v : Nat → Fe) (s : State), opsOk ops qs = true →
      Cur b s0 a c qs v s → (∀ s', Cur b s0 a c (outsQ ops qs) (runOps ops v) s' → WP isa k s' Q) →
      WP isa (opsCode ops k) s Q := fun ops qs v s hok h hk => by
  rw [opsCode_eq]; exact ops_okW (by decide) mulCur_mul ops qs v s hok h hk

/-! ## One iteration -/

/-- The field operations of an iteration, after the swaps. -/
def ladOps : List FOp :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB, .add C X3 Z3, .sub D X3 Z3,
    .mul DA D A, .mul CB C B, .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3,
    .mul Z3 X1 Z3, .mul X2 AA BB, .mul24 Z2 E, .add Z2 AA Z2, .mul Z2 E Z2]

/-- The slots the ladder's state lives in. -/
def LQ : List Nat := [X1, X2, Z2, X3, Z3]

theorem ladOps_ok : opsOk ladOps LQ = true := by decide

/-- The elements of the ladder's state `st`, and `x1`. -/
def ladV (x1 : Fe) (st : Ladder) (q : Nat) : Fe :=
  if q = X1 then x1 else if q = X2 then st.x2 else if q = Z2 then st.z2 else if q = X3 then st.x3
  else st.z3

theorem cswap_fst (sw : Nat) (x y : Fe) : (Spec.X448.cswap sw x y).1 = sel sw x y := by
  unfold Spec.X448.cswap sel; split <;> rfl

theorem cswap_snd (sw : Nat) (x y : Fe) : (Spec.X448.cswap sw x y).2 = sel sw y x := by
  unfold Spec.X448.cswap sel; split <;> rfl

/-- The elements after an iteration. -/
theorem ladOps_vals (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) :
    ∀ q ∈ LQ, runOps ladOps (swapV Z2 Z3 (st.swap ^^^ bit k t) (swapV X2 X3 (st.swap ^^^ bit k t)
      (ladV x1 st))) q = ladV x1 (ladderStep k x1 st t) q := by
  intro q hq
  rw [ladderStep_eq]
  simp only [LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;>
    simp only [ladOps, runOps, FOp.out, FOp.val, upd, swapV, ladV, cswap_fst, cswap_snd, X1, X2, Z2, X3,
      Z3, A, B, C, D, AA, BB, E, DA, CB, Nat.reduceEqDiff, ↓reduceIte]

theorem ofNat_xor {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x ^^^ BitVec.ofNat 64 y = BitVec.ofNat 64 (x ^^^ y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, toNat_imm hx, toNat_imm hy, toNat_imm (Nat.xor_lt_two_pow hx hy)]

theorem xor_le_one {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> decide

/-- The loop invariant of the ladder from `sL`, before the iteration for the
bit `n - 1`. -/
structure LadInv (b : Addr) (k : Nat) (x1 : Fe) (sL : State) (n : Nat) (s : State) : Prop where
  cur : CurW work b sL (BitVec.ofNat 64 (ladderAfter k x1 n).swap) (BitVec.ofNat 64 n) LQ
    (ladV x1 (ladderAfter k x1 n)) s

/-- The bits of the scalar in `BITS`. -/
def Bits (b : Addr) (k : Nat) (m : Mem) : Prop :=
  ∀ t < 448, m (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (bit k t)

theorem head_ok {b : Addr} {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 448) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa (.block stepHead) s (CurW work b sL (BitVec.ofNat 64 (bit k (n - 1))) (BitVec.ofNat 64 (n - 1)) LQ
      (swapV Z2 Z3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1))
        (swapV X2 X3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) (ladV x1 (ladderAfter k x1 n))))) := by
  obtain ⟨hcur⟩ := h
  have hc := hcur.ctx
  have hB : BITS = 1064 := rfl
  have hA := ACC_eq
  obtain hsw := ladderAfter_swap_le k x1 hn'
  obtain hbt := bit_le k (n - 1)
  obtain hx := xor_le_one hsw hbt
  simp only [stepHead, mask, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_subi (by decide) (by decide) fun s1 u1 => ?_
  obtain e12 : s1.gpr .r12 = BitVec.ofNat 64 (n - 1) := by
    rw [u1.gpr, hcur.r12, ofNat_sub_one hn (by omega_arith)]
  refine wp_add fun s2 u2 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 (n - 1 + BITS)) (by decide) (by decide)
    (by rw [u2.gpr, e12, u1.other _ (by decide), hc.r6, Offset.add_add])
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hc.inR (by omega_arith)) fun s3 u3 => ?_
  obtain e4 : s3.gpr .r4 = BitVec.ofNat 64 (bit k (n - 1)) := by
    rw [u3.gpr, u2.mem, u1.mem, hcur.stp.frame _ fun r hr => ?_, Nat.add_comm, hbits _ (by omega_arith)]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    · rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := n - 1 + BITS) (n := 1) (k := ACC + 112) (by omega_arith)
        (by omega_arith) _ (Region.contains_self _ _) h
  refine wp_xor fun s4 u4 => ?_
  obtain e0 : s4.gpr .r0 = BitVec.ofNat 64 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) := by
    rw [u4.gpr, e4, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hcur.r0,
      ofNat_xor (by omega_arith) (by omega_arith)]
  refine wp_li (by decide) fun s5 u5 => wp_sub fun s6 u6 => ?_
  obtain e11 : s6.gpr .r11 = 0 - BitVec.ofNat 64 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) := by
    rw [u6.gpr, u5.gpr, u5.other _ (by decide), e0]; rfl
  obtain hr6 : Rest [.r0, .r4, .r11, .r12] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  obtain hm6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain hc6 : Ctx b s6 := hc.of_rest hr6 (by decide)
  obtain hS6 : SlotsOk s6.mem b LQ (ladV x1 (ladderAfter k x1 n)) := by
    rw [hm6]; exact hcur.slots
  refine WP.append (cswapS (by decide) (by decide) (by decide) (by decide) (by decide)
    hc6 hx e11 hS6) fun s7 ⟨hr7, hf7, hS7⟩ => ?_
  obtain hc7 : Ctx b s7 := hc6.of_rest hr7 (by decide)
  refine WP.append (cswapS (by decide) (by decide) (by decide) (by decide) (by decide)
    hc7 hx (by rw [hr7.gpr _ (by decide), e11]) hS7) fun s8 ⟨hr8, hf8, hS8⟩ => ?_
  refine wp_addi (by decide) (by decide) fun s9 u9 => WP.block_nil ?_
  obtain hr9 : Rest [.r0, .r4, .r5, .r7, .r8, .r11, .r12] s s9 :=
    (hr6.mono (by decide)).trans ((hr7.mono (by decide)).trans ((hr8.mono (by decide)).trans
      (u9.rest (by decide))))
  exact ⟨hc.of_rest hr9 (by decide),
    hcur.stp.trans ⟨hr9.mono (by decide), by rw [u9.mem, ← hm6]; exact hf7.trans hf8⟩,
    by rw [u9.gpr, hr8.gpr _ (by decide), hr7.gpr _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), e4, BitVec.add_zero],
    by rw [u9.other _ (by decide), hr8.gpr _ (by decide), hr7.gpr _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e12],
    by rw [u9.mem]; exact hS8⟩

theorem step_eq : step = .seq (.block stepHead) (opsCode ladOps (.block [])) := rfl

theorem step_ok {b : Addr} {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 448) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa step s fun s' => LadInv b k x1 sL (n - 1) s' ∧ (s'.gpr .r12 != 0) = decide (n - 1 ≠ 0) := by
  rw [step_eq]
  refine WP.seq (WP.mono (head_ok hbits hn hn' h) fun s1 h1 =>
    ops_okW (by decide) mulCur_mul ladOps LQ _ s1 ladOps_ok h1 fun s2 h2 => ?_)
  refine WP.block_nil ⟨⟨h2.ctx, h2.stp, ?_, h2.r12, ?_⟩, ?_⟩
  · rw [h2.r0, ladderAfter_step k x1 (show n - 1 < 448 by omega_arith), Nat.sub_add_cancel hn,
      ladderStep_eq]
  · refine (h2.slots.mono (by decide)).congr fun q hq => ?_
    rw [ladderAfter_step k x1 (show n - 1 < 448 by omega_arith), Nat.sub_add_cancel hn]
    exact ladOps_vals k x1 _ (n - 1) q hq
  · rw [h2.r12, ofNat_ne_zero (by omega_arith)]

/-- The ladder, from the state with the bits of the scalar in `BITS` and the
initial elements in `LQ`. -/
theorem ladder_ok {b : Addr} {k : Nat} {x1 : Fe} {s : State} (hc : Ctx b s) (hbits : Bits b k s.mem)
    (hS : SlotsOk s.mem b LQ (ladV x1 (VG.Proof.X448.init x1))) :
    WP isa ladder s fun s' => StpW work b s s' ∧ Ctx b s' ∧
      s'.gpr .r0 = BitVec.ofNat 64 (ladderAfter k x1 0).swap ∧
      SlotsOk s'.mem b LQ (ladV x1 (ladderAfter k x1 0)) := by
  unfold ladder
  refine WP.seq (wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ?_)
  obtain hr2 : Rest [.r0, .r12] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  obtain hbits2 : Bits b k s2.mem := by rw [hm2]; exact hbits
  obtain h448 : LadInv b k x1 s2 448 s2 :=
    ⟨⟨hc.of_rest hr2 (by decide), StpW.refl _ _ _, by rw [u2.gpr]; rfl,
      by rw [u2.other _ (by decide), u1.gpr], by rw [hm2]; exact hS⟩⟩
  obtain hst : StpW work b s s2 := StpW.of_rest hr2 (by decide) hm2
  refine WP.mono (Q := LadInv b k x1 s2 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 448 ∧ LadInv b k x1 s2 m s') ?_ 448 s2 ⟨by decide, Nat.le_refl _, h448⟩)
    fun s' ⟨h'⟩ => ⟨hst.trans h'.stp, h'.ctx, h'.r0, h'.slots⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (step_ok hbits2 h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_nonzero, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [hm], m - 1, by omega_arith, by omega_arith, by omega_arith, hl'⟩

end VG.Proof.X448.PPC64LE

end

end

/-!
# X448 on PPC64LE: the inversion

`invert` computes `z^(p-2)` into `R` for the element `z` at `Z2` by the
addition chain of `Proof/X448/Invert.lean` (`invertQ_ok`), as RISC-V's `R64`
implementation does: runs of squarings (`sqn_ok`, a loop on `r12` after the
first), the chain as far as `z^(2²²³ - 1)` in `R` and `z^(2²²² - 1)` in `T6`
(`chain223_ok`), then its two final factors. The chain's slots `T0`–`T6` are
separate from the slots `qs` the caller keeps (`TempsOk`), whose elements it
keeps. The proofs take the multiplication and the registers that may
change as parameters (`invertQW_ok`, `invertW_ok`): `invertQ_ok` and
`invert_ok`, Ed448's and X448's, are those of `mul` and `work`. Also the helpers
of the ladders' and Ed448's loops (`cmp_ok`, …).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P Fe)

theorem pw_zero (z : Fe) : VG.Proof.X448.pw z 0 = 1 := rfl

theorem iteT {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem iteF {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

theorem shr_step (x t : Nat) : x >>> t = 2 * (x >>> (t + 1)) + x >>> t % 2 := by
  rw [Nat.shiftRight_succ]; omega_using []

section
variable {b : Addr} {s0 : State} {a : BitVec 64} {W : List Reg} {mf : Nat → Nat → Nat → Prog isa}

/-! ## The inversion -/

/-- The slots of the inversion. -/
def IQ : List Nat := [Z2, R, X2]


theorem sub_beq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y == 0) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    obtain e : BitVec.ofNat 64 x = BitVec.ofNat 64 y := by
      rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 x) (BitVec.ofNat 64 y), h']; simp
    have := congrArg BitVec.toNat e
    rwa [toNat_imm hx, toNat_imm hy] at this

theorem CurW.congr {s0 s : State} {a c : BitVec 64} {qs qs' : List Nat} {v w : Nat → Fe}
    (h : CurW W b s0 a c qs v s) (hq : ∀ q ∈ qs', q ∈ qs) (hv : ∀ q ∈ qs', v q = w q) : CurW W b s0 a c qs' w s :=
  ⟨h.ctx, h.stp, h.r0, h.r12, (h.slots.mono hq).congr hv⟩

/-- `subi r5, r12, d`, and the branch on `r5 = 0`. -/
theorem cmpW_ok (hW : ∀ r ∈ work, r ∈ W) {s0 s : State} {a : BitVec 64} {qs : List Nat} {v : Nat → Fe}
    {m d : Nat} (hm : m < 448) (hd : d < 448) (h : CurW W b s0 a (BitVec.ofNat 64 m) qs v s) :
    WP isa (.block [.subi .r5 .r12 d]) s fun s' => CurW W b s0 a (BitVec.ofNat 64 m) qs v s' ∧
      isa.eval (.zero .d .r5) s' = some (decide (m = d)) := by
  refine wp_subi (by decide) (by omega_using [hd]) fun s1 u1 => WP.block_nil ⟨h.next (fun r hr => hW r (by revert r; decide)) (u1.rest (by decide))
    (by rw [u1.mem]; exact Frame.refl _ _) (by rw [u1.mem]; exact h.slots), ?_⟩
  rw [eval_zero, u1.gpr, h.r12, sub_beq (by omega_using [hm]) (by omega_using [hd])]


/-! ## Separate slots -/

/-- The chain's temporaries. -/
abbrev TQ : List Nat := [T0, T1, T2, T3, T4, T5, T6]

/-- The temporaries are separate from the slots `qs`, and not among them. -/
def TempsOk (qs : List Nat) : Bool := TQ.all fun t => Sep1 t qs && !qs.contains t

theorem temps_get {qs : List Nat} (h : TempsOk qs = true) {t : Nat} (ht : t ∈ TQ) :
    Sep1 t qs = true ∧ t ∉ qs := by
  have := List.all_eq_true.mp h t ht
  simp only [Bool.and_eq_true] at this
  refine ⟨this.1, fun hm => ?_⟩
  have h2 := this.2
  rw [List.contains_iff_mem.mpr hm] at h2
  contradiction

theorem sep1_cons {o x : Nat} {l : List Nat} (h1 : Sep1 o [x] = true) (h2 : Sep1 o l = true) :
    Sep1 o (x :: l) = true := by
  simp only [Sep1, List.all_cons, List.all_nil, Bool.and_true] at h1 h2 ⊢
  rw [h1, h2]; rfl

/-- `Sep1 o` of a list of literal slots in front of `qs`, from `Sep1 o qs`. -/
macro "sep1" : tactic =>
  `(tactic| repeat (first | with_reducible assumption | refine sep1_cons (by decide) ?_))

theorem upd_upd (v : Nat → Fe) (o : Nat) (x y : Fe) : upd (upd v o x) o y = upd v o y := by
  funext q; by_cases h : q = o
  · subst h; rw [upd_self, upd_self]
  · rw [upd_of_ne _ _ h, upd_of_ne _ _ h, upd_of_ne _ _ h]

/-- `Cur` with any counter in `r12`. -/
abbrev CurE (W : List Reg) (b : Addr) (s0 : State) (a : BitVec 64) (qs : List Nat) (v : Nat → Fe)
    (s : State) : Prop :=
  ∃ c, CurW W b s0 a c qs v s

theorem opMulE (hmf : MulCur W mf) {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0)
    (ho4 : o % 4 = 0) {s : State} (h : CurE W b s0 a qs v s) :
    WP isa (mf o x y) s (CurE W b s0 a (o :: qs) (upd v o (v x * v y))) :=
  let ⟨c, h⟩ := h
  WP.mono (hmf hq ho hx hy hx4 hy4 ho4 h) fun _ h' => ⟨c, h'⟩

/-! ## Runs of squarings -/

/-- The loop of `sqn o x n` from `sL`, before the iteration that leaves `m - 1`
squarings to do. -/
abbrev SqInv (W : List Reg) (b : Addr) (s0 : State) (a : BitVec 64) (o n : Nat) (qs : List Nat)
    (v : Nat → Fe) (y : Fe) (k : Nat) (s : State) : Prop :=
  CurW W b s0 a (BitVec.ofNat 64 k) (o :: qs) (upd v o (VG.Proof.X448.sqn y (n - k))) s

theorem sep1_self {o : Nat} {qs : List Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC) :
    Sep1 o (o :: qs) = true := by
  refine sep1_cons ?_ hq
  simp only [Sep1, List.all_cons, List.all_nil, Bool.and_true, beq_self_eq_true,
    Bool.true_or, Bool.true_and, decide_eq_true_eq]
  exact ho

theorem sqStep_ok (hW : ∀ r ∈ work, r ∈ W) (hmf : MulCur W mf) {o n : Nat} {qs : List Nat} {v : Nat → Fe} {y : Fe} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) (ho4 : o % 4 = 0) {m : Nat} (hm : 1 ≤ m) (hmn : m < n) (hn : n ≤ 2048)
    {s : State} (h : SqInv W b s0 a o n qs v y m s) :
    WP isa (sqStepW mf o) s fun s' => SqInv W b s0 a o n qs v y (m - 1) s' ∧
      (s'.gpr .r12 != 0) = decide (m - 1 ≠ 0) := by
  unfold sqStepW
  refine WP.seq (wp_subi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  obtain h1 : CurW W b s0 a (BitVec.ofNat 64 (m - 1)) (o :: qs) (upd v o (VG.Proof.X448.sqn y (n - m))) s1 :=
    ⟨h.ctx.of_rest (u1.rest (ws := [.r12]) (by decide)) (by decide),
      h.stp.trans (StpW.of_rest (u1.rest (ws := [.r12]) (by decide)) (fun r hr => hW r (by rw [List.mem_singleton.mp hr]; decide)) u1.mem),
      by rw [u1.other _ (by decide), h.r0],
      by rw [u1.gpr, h.r12, ofNat_sub_one hm (by omega_using [hmn, hn])],
      by rw [u1.mem]; exact h.slots⟩
  refine WP.mono (hmf (o := o) (x := o) (y := o) (sep1_self hq ho) ho List.mem_cons_self
    List.mem_cons_self ho4 ho4 ho4 h1) fun s2 h2 => ⟨h2.congr (fun q hq => List.mem_cons_of_mem _ hq) fun q _ => ?_, ?_⟩
  · rw [upd_upd, upd_self, show n - (m - 1) = n - m + 1 by omega_using [hm, hmn]]; rfl
  · rw [h2.r12, ofNat_ne_zero (by omega_using [hmn, hn])]

/-- `[o] = [x]^(2^n)`. -/
theorem sqn_ok (hW : ∀ r ∈ work, r ∈ W) (hmf : MulCur W mf) {o x n : Nat} {qs : List Nat} {v : Nat → Fe} (hn1 : 1 ≤ n) (hn : n ≤ 2048)
    (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0)
    {s : State} (h : CurE W b s0 a qs v s) :
    WP isa (sqnW mf o x n) s (CurE W b s0 a (o :: qs) (upd v o (VG.Proof.X448.sqn (v x) n))) := by
  unfold sqnW
  by_cases h1 : n = 1
  · subst h1
    exact opMulE hmf hq ho hx hx hx4 hx4 ho4 h
  · simp only [h1, ↓reduceIte]
    refine WP.seq (WP.mono (opMulE hmf hq ho hx hx hx4 hx4 ho4 h) fun s1 ⟨c1, h1'⟩ => ?_)
    refine WP.seq (wp_li (by omega_using [hn]) fun s2 u2 => WP.block_nil ?_)
    obtain h2 : SqInv W b s0 a o n qs v (v x) (n - 1) s2 :=
      ⟨h1'.ctx.of_rest (u2.rest (ws := [.r12]) (by decide)) (by decide),
        h1'.stp.trans (StpW.of_rest (u2.rest (ws := [.r12]) (by decide)) (fun r hr => hW r (by rw [List.mem_singleton.mp hr]; decide)) u2.mem),
        by rw [u2.other _ (by decide), h1'.r0], by rw [u2.gpr],
        by rw [u2.mem, show n - (n - 1) = 1 by omega_using [hn1]]; exact h1'.slots⟩
    refine WP.mono (Q := SqInv W b s0 a o n qs v (v x) 0) (WP.loop (M := isa)
      (fun m s' => 1 ≤ m ∧ m < n ∧ SqInv W b s0 a o n qs v (v x) m s') ?_ (n - 1) s2
        ⟨by omega_using [hn1, h1], by omega_using [hn1], h2⟩) fun s' h' => ⟨_, by
          have := h'.slots; rw [Nat.sub_zero] at this; exact ⟨h'.ctx, h'.stp, h'.r0, h'.r12, this⟩⟩
    rintro m s' ⟨hm1, hm2, hl⟩
    refine WP.mono (sqStep_ok hW hmf hq ho ho4 hm1 hm2 hn hl) fun s'' ⟨hl', hz⟩ => ?_
    by_cases hm : m - 1 = 0
    · exact .inl ⟨by rw [eval_nonzero, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
    · exact .inr ⟨by rw [eval_nonzero, hz]; simp [hm], m - 1, by omega_using [hm1], by omega_using [hm], by omega_using [hm2], hl'⟩

/-! ## The chain

Each slot of the chain holds a power `pw z e` of `z`, its exponent a closed
expression, so that each step reads its operands' exponents off the
previous slots (`look`) and the exponents are checked by `decide`. -/

/-- `[o] = [x] · [y]` for powers of `z`. -/
theorem opMulP (hmf : MulCur W mf) {o x y : Nat} {qs : List Nat} {F : Nat → Fe} {z : Fe} {ea eb ee : Nat}
    (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs)
    (hFx : F x = VG.Proof.X448.pw z ea) (hFy : F y = VG.Proof.X448.pw z eb) (he : ea + eb = ee)
    (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) (ho4 : o % 4 = 0) {s : State} (h : CurE W b s0 a qs F s) :
    WP isa (mf o x y) s (CurE W b s0 a (o :: qs) (upd F o (VG.Proof.X448.pw z ee))) :=
  WP.mono (opMulE hmf hq ho hx hy hx4 hy4 ho4 h) fun _ ⟨c, h'⟩ => ⟨c, h'.congr (fun _ hq => hq) fun _ _ => by
    rw [hFx, hFy, VG.Proof.X448.pw_mul, he]⟩

/-- `[o] = [x]^(2^n)` for a power of `z`. -/
theorem sqnP (hW : ∀ r ∈ work, r ∈ W) (hmf : MulCur W mf) {o x n : Nat} {qs : List Nat} {F : Nat → Fe} {z : Fe} {ea : Nat} (hn1 : 1 ≤ n)
    (hn : n ≤ 2048) (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (hFx : F x = VG.Proof.X448.pw z ea) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) {s : State}
    (h : CurE W b s0 a qs F s) :
    WP isa (sqnW mf o x n) s
      (CurE W b s0 a (o :: qs) (upd F o (VG.Proof.X448.pw z (ea * 2 ^ n)))) :=
  WP.mono (sqn_ok hW hmf hn1 hn hq ho hx ho4 hx4 h) fun _ ⟨c, h'⟩ => ⟨c, h'.congr (fun _ hq => hq) fun _ _ => by
    rw [hFx, VG.Proof.X448.sqn_pw]⟩

/-- The elements after `chain223 Z2`: `z^(2²²³ - 1)` in `R` and
`z^(2²²² - 1)` in `T6`, for `z` in `Z2`. -/
def chainV (v : Nat → Fe) : Nat → Fe :=
  upd (upd v T6 (VG.Proof.X448.pw (v Z2) (2 ^ 222 - 1))) R (VG.Proof.X448.pw (v Z2) (2 ^ 223 - 1))

/-- A slot's element, read through the updates of literal slots. -/
macro "look" : tactic => `(tactic| simp (disch := decide) only [chainV, upd_self, upd_of_ne])

theorem chain223_ok (hW : ∀ r ∈ work, r ∈ W) (hmf : MulCur W mf) {qs : List Nat} {v : Nat → Fe} (hR : Sep1 R qs = true) (hZ : Z2 ∈ qs)
    (hT : TempsOk qs = true) {s : State} (h : CurE W b s0 a qs v s) :
    WP isa (chain223W mf Z2) s (CurE W b s0 a (R :: T6 :: qs) (chainV v)) := by
  obtain ⟨q0, n0⟩ := temps_get hT (t := T0) (by decide)
  obtain ⟨q1, n1⟩ := temps_get hT (t := T1) (by decide)
  obtain ⟨q2, n2⟩ := temps_get hT (t := T2) (by decide)
  obtain ⟨q3, n3⟩ := temps_get hT (t := T3) (by decide)
  obtain ⟨q4, n4⟩ := temps_get hT (t := T4) (by decide)
  obtain ⟨q5, n5⟩ := temps_get hT (t := T5) (by decide)
  obtain ⟨q6, n6⟩ := temps_get hT (t := T6) (by decide)
  -- `z` as the power `z^1` in its slot.
  have hZ0 : Z2 ∈ Z2 :: qs := List.mem_cons_self
  obtain h0 : CurE W b s0 a (Z2 :: qs) (upd v Z2 (VG.Proof.X448.pw (v Z2) 1)) s :=
    let ⟨c, h⟩ := h
    ⟨c, h.congr (fun q hq => by
      simp only [List.mem_cons] at hq; rcases hq with rfl | hq
      · exact hZ
      · exact hq) fun q _ => by
      by_cases e : q = Z2
      · subst e; rw [upd_self, VG.Proof.X448.pw_one]
      · rw [upd_of_ne _ _ e]⟩
  obtain hRZ : Sep1 R (Z2 :: qs) = true := sep1_cons (by decide) hR
  obtain g0 : Sep1 T0 (Z2 :: qs) = true := sep1_cons (by decide) q0
  obtain g1 : Sep1 T1 (Z2 :: qs) = true := sep1_cons (by decide) q1
  obtain g2 : Sep1 T2 (Z2 :: qs) = true := sep1_cons (by decide) q2
  obtain g3 : Sep1 T3 (Z2 :: qs) = true := sep1_cons (by decide) q3
  obtain g4 : Sep1 T4 (Z2 :: qs) = true := sep1_cons (by decide) q4
  obtain g5 : Sep1 T5 (Z2 :: qs) = true := sep1_cons (by decide) q5
  obtain g6 : Sep1 T6 (Z2 :: qs) = true := sep1_cons (by decide) q6
  unfold chain223W
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 1) (by decide) (by decide) (by sep1) (by decide) hZ0 (by look) (by decide) (by decide) h0) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (opMulP hmf (z := v Z2) (ea := 1 * 2 ^ 1) (eb := 1) (ee := 2 ^ 2 - 1) (by sep1) (by decide) (by simp) (by simp [hZ0])
    (by look) (by look) (by decide) (by decide) (by decide) (by decide) h1) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 2 - 1) (by decide) (by decide) (by sep1) (by decide) (by simp) (by look) (by decide) (by decide) h2) fun s3 h3 => ?_)
  refine WP.seq (WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 2 - 1) * 2 ^ 2) (eb := 2 ^ 2 - 1) (ee := 2 ^ 4 - 1) (by sep1) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) (by decide) (by decide) (by decide) h3) fun s4 h4 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 4 - 1) (by decide) (by decide) (by sep1) (by decide) (by simp) (by look) (by decide) (by decide) h4) fun s5 h5 => ?_)
  refine WP.seq (WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 4 - 1) * 2 ^ 4) (eb := 2 ^ 4 - 1) (ee := 2 ^ 8 - 1) (by sep1) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) (by decide) (by decide) (by decide) h5) fun s6 h6 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 8 - 1) (by decide) (by decide) (by sep1) (by decide) (by simp) (by look) (by decide) (by decide) h6) fun s7 h7 => ?_)
  refine WP.seq (WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 8 - 1) * 2 ^ 8) (eb := 2 ^ 8 - 1) (ee := 2 ^ 16 - 1) (by sep1) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) (by decide) (by decide) (by decide) h7) fun s8 h8 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 16 - 1) (by decide) (by decide) (by sep1) (by decide) (by simp) (by look) (by decide) (by decide) h8) fun s9 h9 => ?_)
  refine WP.seq (WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 16 - 1) * 2 ^ 16) (eb := 2 ^ 16 - 1) (ee := 2 ^ 32 - 1) (by sep1) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) (by decide) (by decide) (by decide) h9) fun s10 h10 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 32 - 1) (by decide) (by decide) (by sep1) (by decide) (by simp) (by look) (by decide) (by decide) h10) fun s11 h11 => ?_)
  refine WP.seq (WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 32 - 1) * 2 ^ 32) (eb := 2 ^ 32 - 1) (ee := 2 ^ 64 - 1) (by sep1) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) (by decide) (by decide) (by decide) h11) fun s12 h12 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 64 - 1) (by decide) (by decide) (by sep1) (by decide) (by simp) (by look) (by decide) (by decide) h12) fun s13 h13 => ?_)
  refine WP.seq (WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 64 - 1) * 2 ^ 64) (eb := 2 ^ 64 - 1) (ee := 2 ^ 128 - 1) (by sep1) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) (by decide) (by decide) (by decide) h13) fun s14 h14 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 128 - 1) (by decide) (by decide) (by sep1) (by decide) (by simp) (by look) (by decide) (by decide) h14) fun s15 h15 => ?_)
  refine WP.seq (WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 128 - 1) * 2 ^ 64) (eb := 2 ^ 64 - 1) (ee := 2 ^ 192 - 1) (by sep1) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) (by decide) (by decide) (by decide) h15) fun s16 h16 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 192 - 1) (by decide) (by decide) (by sep1) (by decide) (by simp) (by look) (by decide) (by decide) h16) fun s17 h17 => ?_)
  refine WP.seq (WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 192 - 1) * 2 ^ 16) (eb := 2 ^ 16 - 1) (ee := 2 ^ 208 - 1) (by sep1) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) (by decide) (by decide) (by decide) h17) fun s18 h18 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 208 - 1) (by decide) (by decide) (by sep1) (by decide) (by simp) (by look) (by decide) (by decide) h18) fun s19 h19 => ?_)
  refine WP.seq (WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 208 - 1) * 2 ^ 8) (eb := 2 ^ 8 - 1) (ee := 2 ^ 216 - 1) (by sep1) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) (by decide) (by decide) (by decide) h19) fun s20 h20 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 216 - 1) (by decide) (by decide) (by sep1) (by decide) (by simp) (by look) (by decide) (by decide) h20) fun s21 h21 => ?_)
  refine WP.seq (WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 216 - 1) * 2 ^ 4) (eb := 2 ^ 4 - 1) (ee := 2 ^ 220 - 1) (by sep1) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) (by decide) (by decide) (by decide) h21) fun s22 h22 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 220 - 1) (by decide) (by decide) (by sep1) (by decide) (by simp) (by look) (by decide) (by decide) h22) fun s23 h23 => ?_)
  refine WP.seq (WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 220 - 1) * 2 ^ 2) (eb := 2 ^ 2 - 1) (ee := 2 ^ 222 - 1) (by sep1) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) (by decide) (by decide) (by decide) h23) fun s24 h24 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 222 - 1) (by decide) (by decide) (by sep1) (by decide) (by simp) (by look) (by decide) (by decide) h24) fun s25 h25 => ?_)
  refine WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 222 - 1) * 2 ^ 1) (eb := 1) (ee := 2 ^ 223 - 1) (by sep1) (by decide) (by simp) (by simp [hZ0])
    (by look) (by look) (by decide) (by decide) (by decide) (by decide) h25) fun s26 ⟨c26, h26⟩ => ⟨c26,
    h26.congr (fun q hq => ?_) fun q hq => ?_⟩
  · simp only [List.mem_cons] at hq ⊢
    rcases hq with rfl | rfl | hq
    · exact .inl rfl
    · simp
    · simp [hq]
  · simp only [List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · simp (disch := decide) only [chainV, upd_self]
    · simp (disch := decide) only [chainV, upd_self, upd_of_ne]
    · have e0 : q ≠ T0 := fun e => n0 (e ▸ hq)
      obtain e1 : q ≠ T1 := fun e => n1 (e ▸ hq)
      obtain e2 : q ≠ T2 := fun e => n2 (e ▸ hq)
      obtain e3 : q ≠ T3 := fun e => n3 (e ▸ hq)
      obtain e4 : q ≠ T4 := fun e => n4 (e ▸ hq)
      obtain e5 : q ≠ T5 := fun e => n5 (e ▸ hq)
      obtain e6 : q ≠ T6 := fun e => n6 (e ▸ hq)
      by_cases eR : q = R
      · subst eR
        simp (disch := decide) only [chainV, upd_self]
      · simp only [chainV, upd_of_ne _ _ e0, upd_of_ne _ _ e1, upd_of_ne _ _ e2, upd_of_ne _ _ e3,
          upd_of_ne _ _ e4, upd_of_ne _ _ e5, upd_of_ne _ _ e6, upd_of_ne _ _ eR]
        by_cases eZ : q = Z2
        · subst eZ; rw [upd_self, VG.Proof.X448.pw_one]
        · rw [upd_of_ne _ _ eZ]

/-- The exponent of the inversion's chain. -/
theorem inv_exp : (2 ^ 223 - 1) * 2 ^ 225 + ((2 ^ 222 - 1) * 2 ^ 2 + 1) = P - 2 := by decide +kernel

/-- The slots other than `R`, whose element the chain overwrites. -/
theorem drop_R {qs : List Nat} (hq : Sep1 R qs = true) (hT : TempsOk qs = true) {a : BitVec 64}
    {v : Nat → Fe} {s : State} (hc : Ctx b s) (hS : ∀ q ∈ qs, q ≠ R → FS s.mem b q = v q)
    (h0 : s.gpr .r0 = a) :
    Sep1 R (qs.filter (· ≠ R)) = true ∧ TempsOk (qs.filter (· ≠ R)) = true ∧
      CurE W b s a (qs.filter (· ≠ R)) v s := by
  -- `R`'s element is whatever is there; the chain overwrites it.
  obtain hC : CurE W b s a (qs.filter (· ≠ R)) v s :=
    ⟨_, hc, StpW.refl _ _ _, h0, rfl, fun q hq => by
      simp only [List.mem_filter, decide_eq_true_eq] at hq; exact hS q hq.1 hq.2⟩
  obtain hfR : Sep1 R (qs.filter (· ≠ R)) = true := by
    exact List.all_eq_true.mpr fun q hq' => List.all_eq_true.mp hq q (List.mem_filter.mp hq').1
  obtain hfT : TempsOk (qs.filter (· ≠ R)) = true := by
    refine List.all_eq_true.mpr fun t ht => ?_
    obtain ⟨h1, h2⟩ := temps_get hT ht
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, ?_⟩
    · exact List.all_eq_true.mpr fun q hq' => List.all_eq_true.mp h1 q (List.mem_filter.mp hq').1
    · rw [Bool.eq_false_iff]
      intro hc
      exact h2 (List.mem_filter.mp (List.contains_iff_mem.mp hc)).1
  exact ⟨hfR, hfT, hC⟩

/-- The inversion of the element at `Z2` into `R`, keeping the slots `qs`
other than `R` (which may be any slots separate from `R` and the chain's
temporaries). -/
theorem invertQW_ok (hW : ∀ r ∈ work, r ∈ W) (hmf : MulCur W mf) {qs : List Nat} (hq : Sep1 R qs = true) (_hR : R ∈ qs) (hZ : Z2 ∈ qs)
    (hT : TempsOk qs = true) {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : ∀ q ∈ qs, q ≠ R → FS s.mem b q = v q) (h0 : s.gpr .r0 = a) :
    WP isa (invertW mf) s fun s' => StpW W b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b qs (upd v R (VG.Proof.X448.pw (v Z2) (P - 2))) := by
  obtain hZR : Z2 ≠ R := by decide
  obtain ⟨hfR, hfT, hC⟩ := drop_R (W := W) hq hT hc hS h0
  obtain hZf : Z2 ∈ qs.filter (· ≠ R) := by simp [hZ, hZR]
  obtain ⟨f6, _⟩ := temps_get hfT (t := T6) (by decide)
  unfold invertW invTailW
  refine WP.seq (WP.mono (chain223_ok hW hmf hfR hZf hfT hC) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 223 - 1) (by decide) (by decide) (by sep1)
    (by decide) (by simp) (by look) (by decide) (by decide) h1) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (sqnP hW hmf (z := v Z2) (ea := 2 ^ 222 - 1) (by decide) (by decide) (by sep1)
    (by decide) (by simp) (by look) (by decide) (by decide) h2) fun s3 h3 => ?_)
  refine WP.seq (WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 222 - 1) * 2 ^ 2) (eb := 1)
    (ee := (2 ^ 222 - 1) * 2 ^ 2 + 1) (by sep1) (by decide) (by simp)
    (by repeat (first | exact hZf | apply List.mem_cons_of_mem))
    (by look) (by look; exact (VG.Proof.X448.pw_one _).symm) rfl (by decide) (by decide) (by decide) h3) fun s4 h4 => ?_)
  refine WP.mono (opMulP hmf (z := v Z2) (ea := (2 ^ 223 - 1) * 2 ^ 225)
    (eb := (2 ^ 222 - 1) * 2 ^ 2 + 1) (ee := P - 2) (by sep1) (by decide) (by simp) (by simp)
    (by look) (by look) inv_exp (by decide) (by decide) (by decide) h4) fun s5 ⟨c5, h5⟩ => ⟨h5.stp, h5.ctx, fun q hq => ?_⟩
  by_cases eR : q = R
  · subst eR
    rw [h5.slots _ List.mem_cons_self, upd_self, upd_self]
  · have hq' : q ∈ qs.filter (· ≠ R) := by simp [hq, eR]
    obtain e6 : q ≠ T6 := fun e => (temps_get hT (t := T6) (by decide)).2 (e ▸ hq)
    rw [h5.slots q (by repeat (first | exact hq' | apply List.mem_cons_of_mem)), upd_of_ne _ _ eR]
    simp only [chainV, upd_of_ne _ _ e6, upd_of_ne _ _ eR]


/-- The inversion in X448: `z` at `Z2`, and `x2` at `X2` kept. -/
theorem invertW_ok (hW : ∀ r ∈ work, r ∈ W) (hmf : MulCur W mf) {a : BitVec 64} {v : Nat → Fe} {s : State}
    (hc : Ctx b s) (hS : SlotsOk s.mem b [Z2, X2] v) (h0 : s.gpr .r0 = a) :
    WP isa (invertW mf) s fun s' => StpW W b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b IQ (upd v R (VG.Proof.X448.pw (v Z2) (P - 2))) :=
  invertQW_ok hW hmf (by decide) (by decide) (by decide) (by decide) hc (fun q hq hqR => hS q (by
    simp only [IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · decide
    · exact absurd rfl hqR
    · decide)) h0

end

section
variable {b : Addr} {s0 : State} {a : BitVec 64}

theorem Cur.congr {s0 s : State} {a c : BitVec 64} {qs qs' : List Nat} {v w : Nat → Fe}
    (h : Cur b s0 a c qs v s) (hq : ∀ q ∈ qs', q ∈ qs) (hv : ∀ q ∈ qs', v q = w q) : Cur b s0 a c qs' w s :=
  CurW.congr h hq hv

/-- `subi r5, r12, d`, and the branch on `r5 = 0`. -/
theorem cmp_ok {s0 s : State} {a : BitVec 64} {qs : List Nat} {v : Nat → Fe} {m d : Nat}
    (hm : m < 448) (hd : d < 448) (h : Cur b s0 a (BitVec.ofNat 64 m) qs v s) :
    WP isa (.block [.subi .r5 .r12 d]) s fun s' => Cur b s0 a (BitVec.ofNat 64 m) qs v s' ∧
      isa.eval (.zero .d .r5) s' = some (decide (m = d)) :=
  cmpW_ok (by decide) hm hd h

/-- `invertQW_ok` with `mul`, which Ed448 uses. -/
theorem invertQ_ok {qs : List Nat} (hq : Sep1 R qs = true) (hR : R ∈ qs) (hZ : Z2 ∈ qs)
    (hT : TempsOk qs = true) {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : ∀ q ∈ qs, q ≠ R → FS s.mem b q = v q) (h0 : s.gpr .r0 = a) :
    WP isa Impl.X448.PPC64LE.invert s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b qs (upd v R (VG.Proof.X448.pw (v Z2) (P - 2))) :=
  invertQW_ok (by decide) mulCur_mul hq hR hZ hT hc hS h0

/-- The inversion in X448. -/
theorem invert_ok {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b [Z2, X2] v) (h0 : s.gpr .r0 = a) :
    WP isa Impl.X448.PPC64LE.invert s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b IQ (upd v R (VG.Proof.X448.pw (v Z2) (P - 2))) :=
  invertW_ok (by decide) mulCur_mul hc hS h0

/-- `invertQ_ok`, for the inversion as its callers run it, with `mulC`. -/
theorem invertQCall_ok {qs : List Nat} (hq : Sep1 R qs = true) (hR : R ∈ qs) (hZ : Z2 ∈ qs)
    (hT : TempsOk qs = true) {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : ∀ q ∈ qs, q ≠ R → FS s.mem b q = v q) :
    WP isa Impl.X448.PPC64LE.invertCall s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b qs (upd v R (VG.Proof.X448.pw (v Z2) (P - 2))) :=
  invertQW_ok (by decide) mulCur_mulC hq hR hZ hT hc hS rfl

/-- `invert_ok`, for the inversion as its callers run it, with `mulC`. -/
theorem invertCall_ok {v : Nat → Fe} {s : State} (hc : Ctx b s) (hS : SlotsOk s.mem b [Z2, X2] v) :
    WP isa Impl.X448.PPC64LE.invertCall s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b IQ (upd v R (VG.Proof.X448.pw (v Z2) (P - 2))) :=
  invertW_ok (by decide) mulCur_mulC hc hS rfl

end

end VG.Proof.X448.PPC64LE
