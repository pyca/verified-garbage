module

public import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Step
public import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Formula
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Flags
import VerifiedGarbage.Proof.X25519.AArch64.Ops
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # The `_alt` ladder's first iteration and its last three

The iteration for bit 254 (`first`), which clamping sets, and those for bits
2, 1 and 0 (`tail`), which it clears: three doublings of the point the swap
chooses. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.AltLadder
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519 VG.Proof.Ed25519.AArch64
open VG.Proof.X25519.AArch64.Alt (AltOp)
open VG.Proof.X25519.AArch64.Word (LoopKeep Good Scratch storeSwap_ok)
open VG.Impl.Ed25519.AArch64 (offset)
open VG.Impl.X25519.AArch64.Alt

theorem cmadd4x_ok {base : Addr} {s : State} (hs : Scratch s base) (hz : s.gpr .x17 = 0) :
    WP isa (.block (VG.Impl.X25519.AArch64.AltLadder.cmadd4x (offset 4) (offset 0) (offset 2))) s
      fun t => LoopKeep base s t ∧ t.gpr .x17 = 0 ∧
        fe t.mem base (offset 4) < P2 ∧ Outside base (offset 4) 32 s.mem t.mem ∧
        env t.mem base = Function.update (env s.mem base) 4
          (toFe 4 * env s.mem base 0 + env s.mem base 2) := by
  rw [VG.Impl.X25519.AArch64.AltLadder.cmadd4x, List.append_assoc, WP.block_append_iff]
  have ha : WP isa (.block [VG.Impl.Ed25519.AArch64.mov .x20 .x1, .movz .x .x1 4 0]) s fun t =>
      t.gpr .x20 = s.gpr .x1 ∧ (t.gpr .x1).toNat = 4 ∧ Keeps [.x20, .x1] s t := by
    apply WP.of_runBlock
    simp only [VG.Impl.Ed25519.AArch64.mov, runBlock_cons, runStep_some, runBlock_nil,
      exec_addImm_x (imm := 0) (by decide), VG.Proof.X25519.AArch64.exec_movz,
      RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq,
      ite_true, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨?_, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    · simp only [State.read, BitVec.setWidth_eq, BitVec.add_zero]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  refine WP.mono ha fun a ⟨a20, a1, ka⟩ => ?_
  have hsa : Scratch a base := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cmadd4E hsa 4 0 2 (by decide) (by decide) (by decide)
    ((ka.gpr _ (by decide)).trans hz) a1) fun b ⟨hb, lb, eb⟩ => ?_
  refine WP.mono (mov_ok b .x1 .x20) fun t ⟨t1, kt⟩ => ?_
  have k1 : ∀ r, r ≠ .x1 → t.gpr r = b.gpr r := fun r hr =>
    kt.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hr)
  refine ⟨⟨fun r hr h19 => ?_, by rw [kt.rd, hb.rd, ka.rd], by rw [kt.wr, hb.wr, ka.wr],
      by rw [kt.sp, hb.sp, ka.sp], ?_⟩, ?_, by rw [kt.mem]; exact lb,
    by rw [kt.mem, ← ka.mem]; exact hb.mem, by rw [kt.mem, eb, ka.mem]⟩
  · by_cases e1 : r = .x1
    · subst e1
      rw [t1, hb.gpr _ (by decide), a20]
    · have r20 : r ≠ .x20 := fun e => hr (e ▸ by decide)
      rw [k1 r e1, hb.gpr r (fun hm => hr (altClob_sub r hm)),
        ka.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨r20, e1⟩)]
  · rw [kt.mem, ← ka.mem]
    exact hb.mem.mono (by simp only [offset]; omega) (by simp only [offset]; omega)
  · rw [k1 _ (by decide), hb.gpr _ (by decide), ka.gpr _ (by decide), hz]

/-- The swap set: `x2 := 1`, stored. -/
theorem swap1_ok {base : Addr} {s : State} (hs : Scratch s base) :
    WP isa (.block [.movz .x .x2 1 0, VG.Impl.X25519.AArch64.Word.st .x2 VG.Impl.X25519.AArch64.Word.SWAP]) s
      fun t => LoopKeep base s t ∧ env t.mem base = env s.mem base ∧
        word t.mem base 768 = BitVec.ofNat 64 1 ∧ Outside base 768 8 s.mem t.mem := by
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, ?_⟩
  have k : Keeps [.x2] s (s.write .x .x2 ((1 : BitVec 16).setWidth 64)) :=
    ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
      rfl, rfl, rfl, rfl⟩
  refine WP.mono (storeSwap_ok (hs.of_keeps k (by decide))) fun t ⟨kt, et, wt, _, ot⟩ => ?_
  exact ⟨(LoopKeep.of_keeps k (by decide)).trans kt, et, by rw [wt, RegUpd.gpr_write_self]; rfl,
    by rw [← k.mem]; exact ot⟩

theorem first_ok {base : Addr} {s : State} {k : Nat} {x1 : Fe}
    (hs : Scratch s base) (hg : Good (env s.mem base) x1 (init x1)) (hb : bit k 254 = 1)
    (hB : Small s.mem base S14) :
    WP isa (.block VG.Impl.X25519.AArch64.AltLadder.first) s fun t =>
      LoopKeep base s t ∧ Good (env t.mem base) x1 (ladderAfter k x1 254) ∧
      word t.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 254).swap ∧ Bel t.mem base S14 := by
  simp only [VG.Impl.X25519.AArch64.AltLadder.first, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (x17_ok s) fun a ⟨za, ka⟩ => ?_
  have lka : LoopKeep base s a := LoopKeep.of_keeps ka (by decide)
  have B : ∀ j : VG.Impl.Ed25519.AArch64.Slot, S14 j = true → fe a.mem base (offset j) < P2 :=
    fun j hj => by rw [ka.mem]; exact Nat.lt_of_lt_of_le (hB j hj) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (subE (lka.scratch hs) 8 3 4 (by decide) (by decide) (by decide) za (B 4 rfl))
    fun b1 ⟨h1, e1⟩ => ?_
  have lk1 := lka.trans (AltOp.lk h1 (by decide))
  have z1 : b1.gpr .x17 = 0 := (h1.gpr _ (by decide)).trans za
  rw [WP.block_append_iff]
  refine WP.mono (addE (lk1.scratch hs) 1 3 4 (by decide) (by decide) (by decide) z1
    (by rw [fr h1 3 (by decide)]; exact B 3 rfl) (by rw [fr h1 4 (by decide)]; exact B 4 rfl))
    fun b2 ⟨h2, e2⟩ => ?_
  have lk2 := lk1.trans (AltOp.lk h2 (by decide))
  have z2 : b2.gpr .x17 = 0 := (h2.gpr _ (by decide)).trans z1
  rw [WP.block_append_iff]
  refine WP.mono (cmadd4x_ok (lk2.scratch hs) z2) fun b3 ⟨lk3', z3, l3, o3, e3⟩ => ?_
  have lk3 := lk2.trans lk3'
  have o3fe : ∀ j : VG.Impl.Ed25519.AArch64.Slot, j ≠ 4 →
      fe b3.mem base (offset j) = fe b2.mem base (offset j) :=
    fun j hj => o3.fe (apart j 4 hj) (by simp only [offset]; omega)
  rw [WP.block_append_iff]
  refine WP.mono (sqrE (lk3.scratch hs) 8 8 (by decide) (by decide) z3)
    fun b4 ⟨h4, l4, e4⟩ => ?_
  have lk4 := lk3.trans (AltOp.lk h4 (by decide))
  have z4 : b4.gpr .x17 = 0 := (h4.gpr _ (by decide)).trans z3
  rw [WP.block_append_iff]
  refine WP.mono (sqrE (lk4.scratch hs) 1 1 (by decide) (by decide) z4)
    fun b5 ⟨h5, l5, e5⟩ => ?_
  have lk5 := lk4.trans (AltOp.lk h5 (by decide))
  have z5 : b5.gpr .x17 = 0 := (h5.gpr _ (by decide)).trans z4
  rw [WP.block_append_iff]
  refine WP.mono (mulE (lk5.scratch hs) 3 0 4 (by decide) (by decide) (by decide) z5)
    fun b6 ⟨h6, l6, e6⟩ => ?_
  have lk6 := lk5.trans (AltOp.lk h6 (by decide))
  have z6 : b6.gpr .x17 = 0 := (h6.gpr _ (by decide)).trans z5
  rw [WP.block_append_iff]
  refine WP.mono (subE (lk6.scratch hs) 7 1 8 (by decide) (by decide) (by decide) z6
    (by rw [fr h6 8 (by decide), fr h5 8 (by decide)]; exact l4)) fun b7 ⟨h7, e7⟩ => ?_
  have lk7 := lk6.trans (AltOp.lk h7 (by decide))
  have z7 : b7.gpr .x17 = 0 := (h7.gpr _ (by decide)).trans z6
  rw [WP.block_append_iff]
  refine WP.mono (cmaddA24_ok (lk7.scratch hs) z7) fun b8 ⟨lk8', z8, _, _, o8, e8⟩ => ?_
  have lk8 := lk7.trans lk8'
  have o8fe : ∀ j : VG.Impl.Ed25519.AArch64.Slot, j ≠ 2 →
      fe b8.mem base (offset j) = fe b7.mem base (offset j) :=
    fun j hj => o8.fe (apart j 2 hj) (by simp only [offset]; omega)
  rw [WP.block_append_iff]
  refine WP.mono (mulE (lk8.scratch hs) 1 1 8 (by decide) (by decide) (by decide) z8)
    fun b9 ⟨h9, l9, e9⟩ => ?_
  have lk9 := lk8.trans (AltOp.lk h9 (by decide))
  have z9 : b9.gpr .x17 = 0 := (h9.gpr _ (by decide)).trans z8
  rw [WP.block_append_iff]
  refine WP.mono (mulE (lk9.scratch hs) 2 7 2 (by decide) (by decide) (by decide) z9)
    fun b10 ⟨h10, l10, e10⟩ => ?_
  have lk10 := lk9.trans (AltOp.lk h10 (by decide))
  refine WP.mono (swap1_ok (lk10.scratch hs)) fun t ⟨lkt, et, wt, ot⟩ => ?_
  have otfe : ∀ j : VG.Impl.Ed25519.AArch64.Slot, fe t.mem base (offset j) = fe b10.mem base (offset j) :=
    fun j => ot.fe (Or.inl (by simp only [offset]; omega)) (by simp only [offset]; omega)
  have h254 : ladderAfter k x1 254 = ladderStep k x1 (init x1) 254 :=
    ladderAfter_step k x1 (by decide)
  refine ⟨lk10.trans lkt, ?_, ?_, ?_⟩
  · have henv : env t.mem base = firstEnv (env s.mem base) := by
      have g1 : env b1.mem base = gF8 (env a.mem base) := e1
      have g2 : env b2.mem base = gF1 (env b1.mem base) := e2
      have g3 : env b3.mem base = gF4 (env b2.mem base) := e3
      have g4 : env b4.mem base = gD2 (env b3.mem base) := e4
      have g5 : env b5.mem base = gS2 (env b4.mem base) := e5
      have g6 : env b6.mem base = gF3 (env b5.mem base) := e6
      have g7 : env b7.mem base = gP (env b6.mem base) := e7
      have g8 : env b8.mem base = gE (env b7.mem base) := e8
      have g9 : env b9.mem base = gXn (env b8.mem base) := e9
      have g10 : env b10.mem base = gZn (env b9.mem base) := e10
      rw [et, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, ka.mem]
      rfl
    rw [henv, h254]
    exact firstEnv_ok _ k x1 hg hb
  · rw [wt, h254, ladderStep_eq, hb]
  · intro j hj
    rcases S14_cases j hj with rfl | rfl | rfl | rfl
    · rw [otfe, fr h10 1 (by decide)]; exact l9
    · rw [otfe]; exact l10
    · rw [otfe, fr h10 3 (by decide), fr h9 3 (by decide), o8fe 3 (by decide), fr h7 3 (by decide)]
      exact l6
    · rw [otfe, fr h10 4 (by decide), fr h9 4 (by decide), o8fe 4 (by decide), fr h7 4 (by decide),
        fr h6 4 (by decide), fr h5 4 (by decide), fr h4 4 (by decide)]
      exact l3

/-- A doubling of slots 1 and 2. -/
theorem dbl_ok {base : Addr} {s : State} (hs : Scratch s base) (hz : s.gpr .x17 = 0)
    (l1 : fe s.mem base (offset 1) < P2) (l2 : fe s.mem base (offset 2) < P2) :
    WP isa (.block VG.Impl.X25519.AArch64.AltLadder.dbl) s fun t =>
      LoopKeep base s t ∧ t.gpr .x17 = 0 ∧
      env t.mem base 1 = (dblPt (env s.mem base 1) (env s.mem base 2)).1 ∧
      env t.mem base 2 = (dblPt (env s.mem base 1) (env s.mem base 2)).2 ∧
      fe t.mem base (offset 1) < P2 ∧ fe t.mem base (offset 2) < P2 := by
  simp only [VG.Impl.X25519.AArch64.AltLadder.dbl, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (subE hs 8 1 2 (by decide) (by decide) (by decide) hz l2)
    fun b1 ⟨h1, e1⟩ => ?_
  have lk1 := AltOp.lk h1 (by decide)
  have z1 : b1.gpr .x17 = 0 := (h1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (addE (lk1.scratch hs) 1 1 2 (by decide) (by decide) (by decide) z1
    (by rw [fr h1 1 (by decide)]; exact l1) (by rw [fr h1 2 (by decide)]; exact l2))
    fun b2 ⟨h2, e2⟩ => ?_
  have lk2 := lk1.trans (AltOp.lk h2 (by decide))
  have z2 : b2.gpr .x17 = 0 := (h2.gpr _ (by decide)).trans z1
  rw [WP.block_append_iff]
  refine WP.mono (sqrE (lk2.scratch hs) 8 8 (by decide) (by decide) z2)
    fun b3 ⟨h3, l3, e3⟩ => ?_
  have lk3 := lk2.trans (AltOp.lk h3 (by decide))
  have z3 : b3.gpr .x17 = 0 := (h3.gpr _ (by decide)).trans z2
  rw [WP.block_append_iff]
  refine WP.mono (sqrE (lk3.scratch hs) 1 1 (by decide) (by decide) z3)
    fun b4 ⟨h4, _, e4⟩ => ?_
  have lk4 := lk3.trans (AltOp.lk h4 (by decide))
  have z4 : b4.gpr .x17 = 0 := (h4.gpr _ (by decide)).trans z3
  rw [WP.block_append_iff]
  refine WP.mono (subE (lk4.scratch hs) 7 1 8 (by decide) (by decide) (by decide) z4
    (by rw [fr h4 8 (by decide)]; exact l3)) fun b5 ⟨h5, e5⟩ => ?_
  have lk5 := lk4.trans (AltOp.lk h5 (by decide))
  have z5 : b5.gpr .x17 = 0 := (h5.gpr _ (by decide)).trans z4
  rw [WP.block_append_iff]
  refine WP.mono (cmaddA24_ok (lk5.scratch hs) z5) fun b6 ⟨lk6', z6, _, _, _, e6⟩ => ?_
  have lk6 := lk5.trans lk6'
  rw [WP.block_append_iff]
  refine WP.mono (mulE (lk6.scratch hs) 1 1 8 (by decide) (by decide) (by decide) z6)
    fun b7 ⟨h7, l7, e7⟩ => ?_
  have lk7 := lk6.trans (AltOp.lk h7 (by decide))
  have z7 : b7.gpr .x17 = 0 := (h7.gpr _ (by decide)).trans z6
  refine WP.mono (mulE (lk7.scratch hs) 2 7 2 (by decide) (by decide) (by decide) z7)
    fun t ⟨h8, l8, e8⟩ => ?_
  have henv : env t.mem base = dblEnv (env s.mem base) := by
    have g1 : env b1.mem base = gDd (env s.mem base) := e1
    have g2 : env b2.mem base = gSd (env b1.mem base) := e2
    have g3 : env b3.mem base = gD2 (env b2.mem base) := e3
    have g4 : env b4.mem base = gS2 (env b3.mem base) := e4
    have g5 : env b5.mem base = gP (env b4.mem base) := e5
    have g6 : env b6.mem base = gE (env b5.mem base) := e6
    have g7 : env b7.mem base = gXn (env b6.mem base) := e7
    have g8 : env t.mem base = gZn (env b7.mem base) := e8
    rw [g8, g7, g6, g5, g4, g3, g2, g1]
    rfl
  obtain ⟨v1, v2⟩ := dblEnv_vals (env s.mem base)
  refine ⟨lk7.trans (AltOp.lk h8 (by decide)), (h8.gpr _ (by decide)).trans z7,
    by rw [henv]; exact v1, by rw [henv]; exact v2, by rw [fr h8 1 (by decide)]; exact l7, l8⟩

/-- `Z` set iff the swap is clear. -/
theorem tailFlags_ok {base : Addr} {s : State} {sw : Nat} (hs : Scratch s base) (hsw : sw ≤ 1)
    (hw : word s.mem base 768 = BitVec.ofNat 64 sw) :
    WP isa (.block [.movz .x .x17 0 0, VG.Impl.X25519.AArch64.Word.ld .x3 VG.Impl.X25519.AArch64.Word.SWAP,
      .movz .x .x2 0 0, .subs .x .x3 .x3 .x2]) s fun t =>
      LoopKeep base s t ∧ t.gpr .x17 = 0 ∧ t.zf = (sw == 0) ∧ t.mem = s.mem := by
  change WP isa (.block (([.movz .x .x17 0 0] : List Instr) ++
    ([VG.Impl.Ed25519.AArch64.ld .x3 768] ++
    ([.movz .x .x2 0 0] ++ ([.subs .x .x3 .x3 .x2] : List Instr))))) s _
  rw [WP.block_append_iff]
  refine WP.mono (x17_ok s) fun a ⟨za, ka⟩ => ?_
  have hsa : Scratch a base := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hsa (d := 768) (by decide) (by decide) .x3) fun b ⟨bs, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, WP.block_nil ?_⟩
  have kc : Keeps [.x2] b (b.write .x .x2 ((0 : BitVec 16).setWidth 64)) :=
    ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
      rfl, rfl, rfl, rfl⟩
  refine WP.mono (subs_ok (kt := 0) hsw (by decide)
    (by rw [kc.gpr _ (by decide), bs, ka.mem, hw])
    (by rw [RegUpd.gpr_write_self]; rfl)) fun t ⟨tz, kt⟩ => ?_
  refine ⟨((LoopKeep.of_keeps ka (by decide)).trans (LoopKeep.of_keeps kb (by decide))).trans
      ((LoopKeep.of_keeps kc (by decide)).trans (LoopKeep.of_keeps kt (by decide))), ?_, tz, ?_⟩
  · rw [kt.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), za]
  · rw [kt.mem, kc.mem, kb.mem, ka.mem]

theorem cswap_fst {sw : Nat} (hsw : sw ≤ 1) (a b : Fe) :
    (Spec.X25519.cswap sw a b).1 = if (sw == 0) = true then a else b := by
  rcases (by omega : sw = 0 ∨ sw = 1) with rfl | rfl <;> rfl

/-- The iterations for bits 2, 1 and 0, from the state after bit 3: slots 1
and 2 end as the ladder's result, its last swap made. -/
theorem tail_ok {base : Addr} {s : State} {k : Nat} {x1 : Fe}
    (hs : Scratch s base) (hg : Good (env s.mem base) x1 (ladderAfter k x1 3))
    (hw : word s.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 3).swap)
    (hB : Bel s.mem base S14) (h0 : bit k 0 = 0) (h1 : bit k 1 = 0) (h2 : bit k 2 = 0) :
    WP isa (.block VG.Impl.X25519.AArch64.AltLadder.tail) s fun t =>
      LoopKeep base s t ∧
      env t.mem base 1 = (Spec.X25519.cswap (ladderAfter k x1 0).swap (ladderAfter k x1 0).x2
        (ladderAfter k x1 0).x3).1 ∧
      env t.mem base 2 = (Spec.X25519.cswap (ladderAfter k x1 0).swap (ladderAfter k x1 0).z2
        (ladderAfter k x1 0).z3).1 := by
  have hsw := ladderAfter_swap_le k x1 (n := 3) (by decide)
  simp only [VG.Impl.X25519.AArch64.AltLadder.tail, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (tailFlags_ok hs hsw hw) fun a ⟨lka, za, fa, ma⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (muxE (lka.scratch hs) 1 3 1 (by decide) (by decide) (by decide))
    fun b1 ⟨h1', z1f, f1, e1⟩ => ?_
  have lk1 := lka.trans (AltOp.lk h1' (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (muxE (lk1.scratch hs) 2 4 2 (by decide) (by decide) (by decide))
    fun b2 ⟨h2', _, f2, e2⟩ => ?_
  have lk2 := lk1.trans (AltOp.lk h2' (by decide))
  have z2 : b2.gpr .x17 = 0 := (h2'.gpr _ (by decide)).trans ((h1'.gpr _ (by decide)).trans za)
  have l1 : fe b2.mem base (offset 1) < P2 := by
    rw [fr h2' 1 (by decide), f1, ma]
    split
    · exact hB 1 rfl
    · exact hB 3 rfl
  have l2 : fe b2.mem base (offset 2) < P2 := by
    rw [f2, z1f, fr h1' 2 (by decide), fr h1' 4 (by decide), ma]
    split
    · exact hB 2 rfl
    · exact hB 4 rfl
  obtain ⟨g0, g1, g2, g3, g4, _⟩ := hg
  have v1 : env b2.mem base 1 = (Spec.X25519.cswap (ladderAfter k x1 3).swap
      (ladderAfter k x1 3).x2 (ladderAfter k x1 3).x3).1 := by
    rw [e2, Function.update_of_ne (by decide), e1, Function.update_self, fa, ma, g1, g3,
      cswap_fst hsw]
  have v2 : env b2.mem base 2 = (Spec.X25519.cswap (ladderAfter k x1 3).swap
      (ladderAfter k x1 3).z2 (ladderAfter k x1 3).z3).1 := by
    rw [e2, Function.update_self, z1f, fa, e1, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), ma, g2, g4, cswap_fst hsw]
  rw [WP.block_append_iff]
  refine WP.mono (dbl_ok (lk2.scratch hs) z2 l1 l2) fun c1 ⟨lkc1, zc1, x2c1, z2c1, lc1, mc1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dbl_ok ((lk2.trans lkc1).scratch hs) zc1 lc1 mc1)
    fun c2 ⟨lkc2, zc2, x2c2, z2c2, lc2, mc2⟩ => ?_
  refine WP.mono (dbl_ok (((lk2.trans lkc1).trans lkc2).scratch hs) zc2 lc2 mc2)
    fun t ⟨lkt, _, x2t, z2t, _, _⟩ => ?_
  have s2 := ladderStep_zero k x1 (ladderAfter k x1 3) 2 h2
  have s1 := ladderStep_zero k x1 (ladderAfter k x1 2) 1 h1
  have s0 := ladderStep_zero k x1 (ladderAfter k x1 1) 0 h0
  rw [← ladderAfter_step k x1 (n := 2) (by decide)] at s2
  rw [← ladderAfter_step k x1 (n := 1) (by decide)] at s1
  rw [← ladderAfter_step k x1 (n := 0) (by decide)] at s0
  obtain ⟨a2, b2', w2⟩ := s2
  obtain ⟨a1, b1', w1⟩ := s1
  obtain ⟨a0, b0, w0⟩ := s0
  simp only [w2, w1, Spec.X25519.cswap, Nat.zero_ne_one, ite_false] at a1 b1' a0 b0
  refine ⟨((lk2.trans lkc1).trans lkc2).trans lkt, ?_, ?_⟩
  · simp only [w0, Spec.X25519.cswap, Nat.zero_ne_one, ite_false]
    rw [x2t, x2c2, z2c2, x2c1, z2c1, v1, v2, a0, a1, b1', a2, b2']
  · simp only [w0, Spec.X25519.cswap, Nat.zero_ne_one, ite_false]
    rw [z2t, x2c2, z2c2, x2c1, z2c1, v1, v2, b0, a1, b1', a2, b2']

end VG.Proof.X25519.AArch64.AltLadder
