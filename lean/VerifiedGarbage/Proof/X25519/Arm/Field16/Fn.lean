import VerifiedGarbage.Proof.X25519.Arm.Field16.Row
import VerifiedGarbage.Proof.Framework.Arm.Spill

/-!
# `vg_gf25519_r16_mul` on ARMv7: what the function computes

From the operands' offsets in `r1`–`r3` (`Pre`): the registers it changes and
`o` saved in its own working space (`Spill`), the pointers (`entry_ok`), the
product's rows (`rows0_ok`, `rows_ok`, by `row_ok`), `lo + 38 hi` and the
carry folded in over the low half of `ACC` (`fold_ok`), the pointer to `[o]`
(`outPtr_ok`), the copy to `[o]` (`copy_ok`), and the registers restored
(`mulFn_ok`).
-/

namespace VG.Proof.X25519.Arm.Field16

open VG VG.Arm VG.Impl.X25519.Arm.Field16 VG.Proof.X25519.Arm
open VG.Impl.X25519.Arm (pass prologue zeroAcc mulSrc tail)
open VG.Spec.X25519 (P)

/-- The body's start: the working space at `b`, the offsets in `r1`–`r3`. -/
structure Pre (b : BitVec 32) (o x y : Nat) (s : State) : Prop where
  ctx : CtxN 0 b s
  r1 : s.gpr .r1 = BitVec.ofNat 32 o
  r2 : s.gpr .r2 = BitVec.ofNat 32 x
  r3 : s.gpr .r3 = BitVec.ofNat 32 y
  ho : o + 64 ≤ ACC
  hx : x + 64 ≤ ACC
  hy : y + 64 ≤ ACC
  lx : Lim s.mem (State.addr b) x
  ly : Lim s.mem (State.addr b) y

/-- `o` in `lr`, and the pointers. -/
theorem entry_ok {b : BitVec 32} {o x y : Nat} {s : State} (hc : CtxN 0 b s) (h1 : s.gpr .r1 = BitVec.ofNat 32 o)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 x) (h3 : s.gpr .r3 = BitVec.ofNat 32 y) :
    WP isa (.block entry) s fun e => Rest [.r8, .r12, .lr] s e ∧ e.mem = s.mem ∧ e.gpr .lr = BitVec.ofNat 32 o ∧
      e.gpr .r8 = b + BitVec.ofNat 32 x ∧ e.gpr .r12 = b + BitVec.ofNat 32 y := by
  simp only [entry]
  refine wp_mov (op2_reg _ _) fun s0 u0 => wp_dp (op2_reg _ _) fun s1 u1 => wp_dp (op2_reg _ _) fun s2 u2 =>
    WP.block_nil ⟨(u0.rest (by decide)).trans ((u1.rest (by decide)).trans (u2.rest (by decide))),
      by rw [u2.mem, u1.mem, u0.mem], ?_, ?_, ?_⟩
  · rw [u2.other _ (by decide), u1.other _ (by decide), u0.gpr, h1]
  · rw [u2.other _ (by decide), u1.gpr]
    show s0.gpr .r0 + s0.gpr .r2 = _
    rw [u0.other _ (by decide), u0.other _ (by decide), hc.r0, h2]
  · rw [u2.gpr, u1.other _ (by decide), u1.other _ (by decide)]
    show s0.gpr .r0 + s0.gpr .r3 = _
    rw [u0.other _ (by decide), u0.other _ (by decide), hc.r0, h3]

/-- `ACC` zeroed, the constants, and the row counter, from the pointers. -/
theorem rows0_ok {b : BitVec 32} {x y : Nat} {s : State} (hc : CtxN 0 b s) (h6 : s.gpr .r6 = mask16)
    (h8 : s.gpr .r8 = b + BitVec.ofNat 32 x) (h12 : s.gpr .r12 = b + BitVec.ofNat 32 y) :
    WP isa (.block (zeroAcc ACC ++ ([.mov .r7 (.reg .r0), .mov .r9 (.imm 16)] : List Instr))) s
      (RowInv b x y s 0) := by
  refine WP.append (zeroAcc_ok (acc := ACC) (by decide) hc) fun s2 ⟨hz, hf2, hr2⟩ => ?_
  have hc2 : CtxN 0 b s2 := hc.of_rest hr2 (by decide)
  refine wp_mov (op2_reg _ _) fun s3 u3 => wp_mov (op2_imm (by decide)) fun s4 u4 => WP.block_nil ?_
  have hrs : Rest [.r3, .r7, .r9] s s4 :=
    (hr2.mono (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
  have hr : Rest rclob s s4 := hrs.mono (by decide)
  have hm4 : s4.mem = s2.mem := by rw [u4.mem, u3.mem]
  refine ⟨hc.of_rest hr (by decide), hr, by rw [hrs.gpr _ (by decide), h6], ?_, u4.gpr,
    by rw [hrs.gpr _ (by decide), h8]; rfl, by rw [hrs.gpr _ (by decide), h12], ?_, fun k hk => ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.gpr, hc2.r0]; exact (BitVec.add_zero b).symm
  · rw [hm4]; exact hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
  · rw [accw, hm4]; unfold accw at hz; rw [hz k (by omega_arith)]; decide
  · rw [hm4, val16_congr (g := fun _ => 0) (fun k hk => hz k hk), val16_zero_fn]
    exact (Nat.zero_mul _).symm

/-- The sixteen rows. -/
theorem rows_ok {b : BitVec 32} {x y : Nat} (hx : x + 64 ≤ ACC) (hy : y + 64 ≤ ACC) {s0 s1 : State}
    (hlx : Lim s0.mem (State.addr b) x) (hly : Lim s0.mem (State.addr b) y) (h1 : RowInv b x y s0 0 s1) :
    WP isa (.loop (.block row) .ne) s1 (RowInv b x y s0 16) := by
  refine WP.mono (WP.loop (M := isa)
    (fun n s' => ∃ i, n = 16 - i ∧ i < 16 ∧ RowInv b x y s0 i s') ?_ 16 s1 ⟨0, rfl, by decide, h1⟩)
    fun s2 h2 => h2
  rintro n s' ⟨i, rfl, hi, hr⟩
  refine WP.mono (row_ok hx hy hlx hly hi hr) fun s'' ⟨hr', hz⟩ => ?_
  by_cases h16 : i + 1 = 16
  · refine .inl ⟨by rw [eval_ne, hz]; simp [h16], ?_⟩
    rw [h16] at hr'; exact hr'
  · exact .inr ⟨by rw [eval_ne, hz]; simp; omega_arith, 16 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, hr'⟩

/-- `lo + 38 hi` over the low half of `ACC`, and the carry folded in, with 38 in
`r8`. -/
theorem fold2_ok {b : BitVec 32} {x y : Nat} {s0 s2 : State} (hc : CtxN 0 b s2) (h6 : s2.gpr .r6 = mask16)
    (h8 : s2.gpr .r8 = 38) (hlt : ∀ k < 32, accw ACC s2.mem (State.addr b) k < 65536)
    (hval : val16 (accw ACC s2.mem (State.addr b)) 32 = V s0.mem (State.addr b) x * V s0.mem (State.addr b) y) :
    WP isa (.block (.mov .r5 (.imm 0) :: (pass .r0 ACC (mulSrc ACC) ++ tail ACC))) s2 fun s4 =>
      Rest [.r2, .r3, .r4, .r5] s2 s4 ∧ Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 64⟩] s2.mem s4.mem ∧
      Lim s4.mem (State.addr b) ACC ∧
      V s4.mem (State.addr b) ACC % P = V s0.mem (State.addr b) x * V s0.mem (State.addr b) y % P := by
  have hA : ACC = 1472 := rfl
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have hc3 : CtxN 0 b s3 := hc.of_rest (u3.rest (ws := [.r5]) (by decide)) (by decide)
  have hl32 : ∀ k < 32, accw ACC s2.mem (State.addr b) k < 65536 := hlt
  have hv : val16 (accw ACC s2.mem (State.addr b)) 32 = V s0.mem (State.addr b) x * V s0.mem (State.addr b) y :=
    hval
  have hlo := val16_lt (f := accw ACC s2.mem (State.addr b)) (n := 16) fun k hk => hl32 k (by omega_arith)
  have hhi := val16_lt (f := fun k => accw ACC s2.mem (State.addr b) (16 + k)) (n := 16) fun k hk =>
    hl32 (16 + k) (by omega_arith)
  refine WP.mono (passTail'_ok (c := foldC (accw ACC s2.mem (State.addr b))) (by decide)
    (foldC_le hl32) (by rw [val16_foldC]; rw [show 16 * 16 = 256 from rfl] at hlo hhi; omega_arith) hc3
    (by rw [u3.other _ (by decide), h6]) (by rw [u3.other _ (by decide), h8]) u3.gpr ?_)
    fun s4 ⟨hr4, hf4, hl4, hv4⟩ => ⟨(u3.rest (by decide)).trans hr4, by rw [u3.mem] at hf4; exact hf4, hl4, ?_⟩
  · intro k hk s' hp
    have hc' : CtxN 0 b s' := hc3.of_rest hp.rest (by decide)
    refine ldr0_ok hc' (d := ACC + 4 * k) (by omega_arith) fun t1 v1 => ?_
    refine ldr0_ok (hc'.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide)) (d := ACC + 64 + 4 * k)
      (by omega_arith) fun t2 v2 => ?_
    refine wp_mul fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have el : (t1.gpr .r3).toNat = accw ACC s2.mem (State.addr b) k := by
        rw [v1.gpr]; show wd s'.mem _ _ = _
        rw [wd_pass hc3 hp.frame (.inr (by omega_arith)) (by omega_arith) (by omega_arith), u3.mem]; rfl
      have eh : (t2.gpr .r2).toNat = accw ACC s2.mem (State.addr b) (16 + k) := by
        rw [v2.gpr, v1.mem]; show wd s'.mem _ _ = _
        rw [wd_pass hc3 hp.frame (.inr (by omega_arith)) (by omega_arith) (by omega_arith), u3.mem, accw]
        congr 1; omega_arith
      have h8 : t2.gpr .r8 = 38 := by
        rw [v2.other _ (by decide), v1.other _ (by decide), hp.rest.gpr _ (by decide),
          u3.other _ (by decide), h8]
      have hh := hl32 (16 + k) (by omega_arith)
      have hl := hl32 k (by omega_arith)
      have e3 : (t3.gpr .r2).toNat = accw ACC s2.mem (State.addr b) (16 + k) * 38 := by
        rw [v3.gpr, h8, toNat_mul_lt (by rw [eh]; show _ * 38 < _; omega_arith), eh]; rfl
      rw [v4.gpr]
      show (t3.gpr .r3 + t3.gpr .r2).toNat = _
      rw [v3.other .r3 (by decide), v2.other .r3 (by decide), toNat_add_lt (by rw [el, e3]; omega_arith), el,
        e3, foldC, Nat.mul_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · rw [hv4, val16_foldC, ← hv, show (32 : Nat) = 16 + 16 from rfl, val16_append, fold256]

/-- `fold2_ok`, from the rows. -/
theorem fold_ok {b : BitVec 32} {x y : Nat} {s0 s1 : State} (h1 : RowInv b x y s0 16 s1) :
    WP isa (.block (.mov .r8 (.imm 38) :: .mov .r5 (.imm 0) :: (pass .r0 ACC (mulSrc ACC) ++ tail ACC))) s1
      fun s4 => Rest [.r2, .r3, .r4, .r5, .r8] s1 s4 ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 64⟩] s1.mem s4.mem ∧ Lim s4.mem (State.addr b) ACC ∧
      V s4.mem (State.addr b) ACC % P = V s0.mem (State.addr b) x * V s0.mem (State.addr b) y % P := by
  have hA : ACC = 1472 := rfl
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have h2c : CtxN 0 b s2 := h1.ctx.of_rest (u2.rest (ws := [.r8]) (by decide)) (by decide)
  have h26 : s2.gpr .r6 = mask16 := by rw [u2.other _ (by decide), h1.r6]
  have h28 : s2.gpr .r8 = 38 := u2.gpr
  have hm2 : s2.mem = s1.mem := u2.mem
  have h2lt : ∀ k < 32, accw ACC s2.mem (State.addr b) k < 65536 := by rw [hm2]; exact h1.lt
  have h2val : val16 (accw ACC s2.mem (State.addr b)) 32 =
      V s0.mem (State.addr b) x * V s0.mem (State.addr b) y := by rw [hm2]; exact h1.val
  refine WP.mono (fold2_ok h2c h26 h28 h2lt h2val) fun s4 ⟨hr4, hf4, hl4, hv4⟩ =>
    ⟨(u2.rest (by decide)).trans (hr4.mono (by decide)), by rw [← hm2]; exact hf4, hl4, hv4⟩

/-- The result copied to `[o]`, through `r12`. -/
theorem copy_ok {b : BitVec 32} {o : Nat} (ho : o + 64 ≤ ACC) {s : State} (hc : CtxN 0 b s)
    (h12 : s.gpr .r12 = b + BitVec.ofNat 32 o) :
    WP isa (.block ((List.range 16).flatMap copyOut)) s fun s' =>
      Rest [.r3] s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧
      ∀ k < 16, limb s'.mem (State.addr b) o k = limb s.mem (State.addr b) ACC k := by
  have hA : ACC = 1472 := rfl
  have hfit : b.toNat + 4096 ≤ 2 ^ 32 := hc.fit
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => Rest [.r3] s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧
      ∀ k < n, limb s'.mem (State.addr b) o k = limb s.mem (State.addr b) ACC k)
    (fun n s' hn ⟨h1, h2, h3⟩ => ?_) 16 (Nat.le_refl _) s
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s' h => h
  have hc' : CtxN 0 b s' := hc.of_rest h1 (by decide)
  have hacc : limb s'.mem (State.addr b) ACC n = limb s.mem (State.addr b) ACC n :=
    wd_frame h2 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  simp only [copyOut]
  refine ldr0_ok hc' (d := ACC + 4 * n) (by omega_arith) fun t1 v1 => ?_
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (o + 4 * n)) (by omega_arith)
    (by rw [v1.other _ (by decide), h1.gpr _ (by decide), h12, Offset.add_add]; exact addr_add (by omega_arith))
    (by rw [v1.wr]; exact hc'.inW (by omega_arith)) fun t2 v2 => WP.block_nil ⟨h1.trans ((v1.rest (by decide)).trans
      (v2.rest _)), ?_, fun k hk => ?_⟩
  · rw [v2.mem, v1.mem]
    exact h2.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  · rw [limb, v2.mem, v1.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact h3 k hk
    · rw [wd_write_self, v1.gpr, ← hacc]; rfl

theorem saveSlots_ok : Spill.Slots SAVE (SAVE + 28) saveSlots := by decide

theorem saveSlots_restorable : Spill.Restorable .r0 saveSlots := by decide

/-- The pointer to `[o]`, from `o` in `lr`. -/
theorem outPtr_ok {b : BitVec 32} {o : Nat} {s : State} (hc : CtxN 0 b s) (hl : s.gpr .lr = BitVec.ofNat 32 o) :
    WP isa (.block outPtr) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧ t.gpr .r12 = b + BitVec.ofNat 32 o := by
  simp only [outPtr]
  refine wp_dp (op2_reg _ _) fun s1 u1 => WP.block_nil ⟨u1.rest (by decide), u1.mem, ?_⟩
  rw [u1.gpr]
  show s.gpr .r0 + s.gpr .lr = _
  rw [hc.r0, hl]

/-- `vg_gf25519_r16_mul`, from its entry: every register but `r1`–`r3` and
`r12` as it was, and the product's residue at `o`, with limbs below `2¹⁶`;
memory changes only at `o` and in the function's own working space. -/
theorem mulFn_ok {b : BitVec 32} {o x y : Nat} {s : State} (h : Pre b o x y s) :
    WP isa mulFn s fun t => Rest [.r1, .r2, .r3, .r12] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o % P = V s.mem (State.addr b) x * V s.mem (State.addr b) y % P := by
  have hA : ACC = 1472 := rfl
  have hS : SAVE = 1600 := rfl
  have hfit : b.toNat + 4096 ≤ 2 ^ 32 := h.ctx.fit
  have ho := h.ho
  have hx := h.hx
  have hy := h.hy
  have hB : State.addr (s.gpr .r0) = State.addr b := by rw [h.ctx.r0]
  let M1 := Spill.saveMem s.mem (State.addr b) s.gpr saveSlots
  have hf1 : Frame [⟨State.addr b + BitVec.ofNat 64 SAVE, 28⟩] s.mem M1 :=
    Spill.saveMem_frame_slots saveSlots_ok s.mem (State.addr b) s.gpr
  have hsv1 : Spill.Saved M1 (State.addr b) s.gpr saveSlots :=
    Spill.saveMem_saved (State.addr b) s.gpr s.mem saveSlots saveSlots_ok
  have hsav : ∀ {d n : Nat}, d + n ≤ ACC →
      ∀ r ∈ [(⟨State.addr b + BitVec.ofNat 64 SAVE, 28⟩ : Region)],
        (⟨State.addr b + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := fun hd r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  have hlim : ∀ z, z + 64 ≤ ACC → ∀ k < 16, limb M1 (State.addr b) z k = limb s.mem (State.addr b) z k :=
    fun z hz k hk => wd_frame hf1 fun r hr => hsav (d := z + 4 * k) (n := 4) (by omega_arith) r hr
  -- The start: saving, the constants, the pointers and the rows' invariant.
  refine WP.seq (WP.mono (Q := fun s2 => ∃ e, RowInv b x y e 0 s2 ∧ e.mem = M1 ∧
      Rest [.r5, .r6, .r8, .r12, .lr] s e ∧ e.gpr .lr = BitVec.ofNat 32 o) ?_
      fun s2 ⟨e, h2, hme, hre, hle⟩ => ?_)
  · show WP isa (.block ((saveSlots.map fun p => Instr.str p.1 .r0 p.2) ++
      (prologue ++ (entry ++ (zeroAcc ACC ++ ([.mov .r7 (.reg .r0), .mov .r9 (.imm 16)] : List Instr)))))) s _
    refine Spill.save_slots_ok saveSlots_ok (by rw [h.ctx.r0]; omega_arith)
      (fun d hd hd' => by rw [hB]; exact h.ctx.inW (by omega_arith)) ?_
    rw [hB]
    let s1 : State := { s with mem := M1 }
    have hc1 : CtxN 0 b s1 := ⟨h.ctx.r0, h.ctx.fit, h.ctx.wr⟩
    refine WP.append prologue_ok fun s2 ⟨h6, _, _, hr2, hm2⟩ => ?_
    have hc2 : CtxN 0 b s2 := hc1.of_rest hr2 (by decide)
    refine WP.append (entry_ok (o := o) (x := x) (y := y) hc2 (by rw [hr2.gpr _ (by decide)]; exact h.r1)
      (by rw [hr2.gpr _ (by decide)]; exact h.r2) (by rw [hr2.gpr _ (by decide)]; exact h.r3))
      fun e ⟨hre, hme, hl, h8, h12⟩ => ?_
    refine WP.mono (rows0_ok (hc2.of_rest hre (by decide)) (by rw [hre.gpr _ (by decide), h6]) h8 h12)
      fun s3 h3 => ⟨e, h3, by rw [hme, hm2], ?_, hl⟩
    have hr01 : Rest [.r5, .r6, .r8, .r12, .lr] s s1 := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    exact (hr01.trans (hr2.mono (by decide) : Rest [.r5, .r6, .r8, .r12, .lr] _ _)).trans
      (hre.mono (by decide) : Rest [.r5, .r6, .r8, .r12, .lr] _ _)
  have hlx : Lim e.mem (State.addr b) x := fun k hk => by rw [hme, hlim x hx k hk]; exact h.lx k hk
  have hly : Lim e.mem (State.addr b) y := fun k hk => by rw [hme, hlim y hy k hk]; exact h.ly k hk
  refine WP.seq (WP.mono (rows_ok hx hy hlx hly h2) fun s3 h3 => ?_)
  -- The fold, the pointer to `[o]`, the copy and the registers restored.
  show WP isa (.block ((.mov .r8 (.imm 38) :: .mov .r5 (.imm 0) :: (pass .r0 ACC (mulSrc ACC) ++ tail ACC)) ++
    (outPtr ++ ((List.range 16).flatMap copyOut ++ saveSlots.map fun p => Instr.ldr p.1 .r0 p.2)))) s3 _
  have hl3 : s3.gpr .lr = BitVec.ofNat 32 o := by rw [h3.rest.gpr _ (by decide), hle]
  refine WP.append (fold_ok h3) fun s4 ⟨hr4, hf4, hl4, hv4⟩ => ?_
  have hc4 : CtxN 0 b s4 := h3.ctx.of_rest hr4 (by decide)
  have hsvE : Spill.Saved e.mem (State.addr b) s.gpr saveSlots := by rw [hme]; exact hsv1
  have hsv4 : Spill.Saved s4.mem (State.addr b) s.gpr saveSlots :=
    hsvE.frame saveSlots_ok (h3.frame.trans (hf4.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩)) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  refine WP.append (outPtr_ok (o := o) hc4 (by rw [hr4.gpr _ (by decide), hl3])) fun s5 ⟨hr5, hm5, h12⟩ => ?_
  have hc5 : CtxN 0 b s5 := hc4.of_rest hr5 (by decide)
  refine WP.append (copy_ok ho hc5 h12) fun s6 ⟨hr6, hf6, hv6⟩ => ?_
  have hc6 : CtxN 0 b s6 := hc5.of_rest hr6 (by decide)
  have hsv6 : Spill.Saved s6.mem (State.addr (s6.gpr .r0)) s.gpr saveSlots := by
    rw [hc6.r0]
    refine hsv4.frame saveSlots_ok (rs := [⟨State.addr b + BitVec.ofNat 64 o, 64⟩]) (by rw [← hm5]; exact hf6)
      fun r hr => ?_
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  refine WP.mono (Spill.restore_block_ok saveSlots_ok saveSlots_restorable (by rw [hc6.r0]; omega_arith)
    (fun d _ _ => by rw [hc6.r0]; exact hc6.inR (by omega_arith)) hsv6)
    fun t ⟨hres, hoth, hmt, hrd, hwr, hsp⟩ => ?_
  have hrE : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r12, .lr] s s6 :=
    (hre.mono (by decide)).trans ((h3.rest.mono (by decide)).trans ((hr4.mono (by decide)).trans
      ((hr5.mono (by decide)).trans (hr6.mono (by decide)))))
  have hACC : ∀ {d n : Nat}, ACC ≤ d → d + n ≤ ACC + 160 →
      ∃ r' ∈ [(⟨State.addr b + BitVec.ofNat 64 o, 64⟩ : Region), ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩],
        Region.Sub ⟨State.addr b + BitVec.ofNat 64 d, n⟩ r' := fun h₁ h₂ =>
    ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ h₁ h₂⟩
  refine ⟨⟨fun r hr => ?_, by rw [hrd, hrE.rd], by rw [hwr, hrE.wr], by rw [hsp, hrE.sp]⟩, ?_, ?_, ?_⟩
  · by_cases hm : r ∈ saveSlots.map Prod.fst
    · exact Spill.restored_reg hres hm
    · rw [hoth r hm]
      refine hrE.gpr r ?_
      revert hr hm; cases r <;> decide
  · rw [hmt]
    refine (hf1.sub fun r hr => ?_).trans (?_ : Frame _ M1 s6.mem)
    · rw [List.mem_singleton.mp hr]; exact hACC (by omega_arith) (by omega_arith)
    rw [← hme]
    refine (h3.frame.sub fun r hr => ?_).trans ((hf4.sub fun r hr => ?_).trans ?_)
    · rw [List.mem_singleton.mp hr]; exact hACC (Nat.le_refl _) (by omega_arith)
    · rw [List.mem_singleton.mp hr]; exact hACC (Nat.le_refl _) (by omega_arith)
    rw [← hm5]
    exact hf6.sub fun r hr => ⟨_, List.mem_cons_self, by rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (Nat.le_refl _)⟩
  · intro k hk
    rw [hmt, limb, show wd s6.mem _ _ = limb s6.mem (State.addr b) o k from rfl, hv6 k hk, hm5]
    exact hl4 k hk
  · have ex : V e.mem (State.addr b) x = V s.mem (State.addr b) x := by
      rw [hme]; exact val16_congr (hlim x hx)
    have ey : V e.mem (State.addr b) y = V s.mem (State.addr b) y := by
      rw [hme]; exact val16_congr (hlim y hy)
    rw [hmt, show V s6.mem (State.addr b) o = V s4.mem (State.addr b) ACC by
      rw [← hm5]; exact val16_congr hv6, hv4, ex, ey]

end VG.Proof.X25519.Arm.Field16
