module

public import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Step
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Formula
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Head
import VerifiedGarbage.Proof.X25519.AArch64.Ladder
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Formula
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Flags
import VerifiedGarbage.Proof.X25519.AArch64.Ops
public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Top
public import VerifiedGarbage.Impl.X25519.AArch64.AltLadder
public import VerifiedGarbage.Proof.X25519.AArch64.Setup
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.X25519.AArch64.Top
import VerifiedGarbage.Proof.Ed25519.AArch64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.Bytes
public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
public import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed25519.AArch64.Codec
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddMemory
import VerifiedGarbage.Proof.Ed25519.AArch64.Freeze
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `X25519.AArch64.AltLadder.Ladder`, which only this module used -/

section

/-! ### `X25519.AArch64.Word.Ladder`, which only this module used -/

section

/-! The 255 public-count ladder iterations and the final conditional swaps. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64

theorem setCounter_ok (s : State) (n : BitVec 16) :
    WP isa (.block [.movz .x .x19 n 0]) s fun t =>
      t.gpr .x19 = n.setWidth 64 ∧ Keeps [.x19] s t := by
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, WP.block_nil ?_⟩
  exact ⟨RegUpd.gpr_write_self _ _ _ _, ⟨fun r hr =>
    RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr), rfl, rfl, rfl, rfl⟩⟩


end VG.Proof.X25519.AArch64.Word

end

end


/-! # The `_alt` ladder's iterations for bits 253 down to 3 -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.AltLadder
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519 VG.Proof.Ed25519.AArch64
open VG.Proof.X25519.AArch64.Word (LoopKeep Good Scratch bitOffset setCounter_ok)

/-- The loop's invariant. -/
def LInv (base : Addr) (s₀ : State) (k : Nat) (x1 : Fe) (n : Nat) (s : State) : Prop :=
  LoopKeep base s₀ s ∧ Good (env s.mem base) x1 (ladderAfter k x1 n) ∧
  s.gpr .x19 = BitVec.ofNat 64 n ∧ word s.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 n).swap ∧
  Bel s.mem base S14

theorem ladder_ok {base : Addr} {s : State} {k : Nat} {x1 : Fe} (hs : Scratch s base)
    (hg : Good (env s.mem base) x1 (ladderAfter k x1 254))
    (hw : word s.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 254).swap)
    (hb : ∀ i < 255, s.mem (off base (bitOffset+i)) = BitVec.ofNat 8 (bit k i))
    (hB : Bel s.mem base S14) :
    WP isa VG.Impl.X25519.AArch64.AltLadder.ladder s fun t =>
      LoopKeep base s t ∧ Good (env t.mem base) x1 (ladderAfter k x1 3) ∧
      word t.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 3).swap ∧ Bel t.mem base S14 := by
  refine WP.seq (WP.mono (setCounter_ok s 254) fun a ⟨ac, ka⟩ => ?_)
  obtain kla : LoopKeep base s a := LoopKeep.of_keeps ka (by decide)
  refine WP.loop (M := isa) (fun n t => 4 ≤ n ∧ n ≤ 254 ∧ LInv base s k x1 n t)
    ?_ 254 a ⟨by decide, by decide, kla, by rw [ka.mem]; exact hg, ac,
      by rw [ka.mem]; exact hw, fun i hi => by rw [ka.mem]; exact hB i hi⟩
  intro n t ⟨h4, h254, kt, gt, ct, wt, bt⟩
  obtain ⟨i, rfl⟩ : ∃ i, n = i+1 := ⟨n-1, by omega_using [h4]⟩
  refine WP.mono (step_ok (k := k) (kt.scratch hs) (by omega_using [h254]) (by omega_using [h4]) gt
    (ladderAfter_swap_le _ _ (by omega_using [h254])) ct wt (by rw [kt.bit (by omega_using [h254])]; exact hb i (by omega_using [h254])) bt)
    fun u ⟨ku, gu, cu, du, wu, bu⟩ => ?_
  obtain klu : LoopKeep base s u := kt.trans ku
  rw [← ladderAfter_step k x1 (by omega_using [h254])] at gu
  obtain ws : word u.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 i).swap := by
    rw [ladderAfter_step k x1 (by omega_using [h254])]
    exact wu
  obtain he : isa.eval (.nonzero .x .x16) u = some (decide (i - 3 ≠ 0)) := by
    simp only [eval, VG.Proof.Ed25519.AArch64.read_x, du,
      VG.Proof.Ed25519.AArch64.counter_nonzero (by omega_using [h254] : i - 3 < 2^64)]
  by_cases hi : i = 3
  · subst i; exact .inl ⟨by rw [he]; rfl, klu, gu, ws, bu⟩
  · exact .inr ⟨by rw [he]; simp only [Option.some.injEq, decide_eq_true_eq]; omega_using [h4, hi],
      i, by omega_using [], by omega_using [h4, hi], by omega_using [h254], klu, gu, cu, ws, bu⟩

end VG.Proof.X25519.AArch64.AltLadder

end

end

/-! ### `X25519.AArch64.AltLadder.Ends`, which only this module used -/

section

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
  obtain ha : WP isa (.block [VG.Impl.Ed25519.AArch64.mov .x20 .x1, .movz .x .x1 4 0]) s fun t =>
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
  obtain hsa : Scratch a base := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cmadd4E hsa 4 0 2 (by decide) (by decide) (by decide)
    ((ka.gpr _ (by decide)).trans hz) a1) fun b ⟨hb, lb, eb⟩ => ?_
  refine WP.mono (mov_ok b .x1 .x20) fun t ⟨t1, kt⟩ => ?_
  obtain k1 : ∀ r, r ≠ .x1 → t.gpr r = b.gpr r := fun r hr =>
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
    exact hb.mem.mono (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using [])
  · rw [k1 _ (by decide), hb.gpr _ (by decide), ka.gpr _ (by decide), hz]

/-- The swap set: `x2 := 1`, stored. -/
theorem swap1_ok {base : Addr} {s : State} (hs : Scratch s base) :
    WP isa (.block [.movz .x .x2 1 0, VG.Impl.X25519.AArch64.Word.st .x2 VG.Impl.X25519.AArch64.Word.SWAP]) s
      fun t => LoopKeep base s t ∧ env t.mem base = env s.mem base ∧
        word t.mem base 768 = BitVec.ofNat 64 1 ∧ Outside base 768 8 s.mem t.mem := by
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, ?_⟩
  obtain k : Keeps [.x2] s (s.write .x .x2 ((1 : BitVec 16).setWidth 64)) :=
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
  obtain lka : LoopKeep base s a := LoopKeep.of_keeps ka (by decide)
  obtain B : ∀ j : VG.Impl.Ed25519.AArch64.Slot, S14 j = true → fe a.mem base (offset j) < P2 :=
    fun j hj => by rw [ka.mem]; exact Nat.lt_of_lt_of_le (hB j hj) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (subE (lka.scratch hs) 8 3 4 (by decide) (by decide) (by decide) za (B 4 rfl))
    fun b1 ⟨h1, e1⟩ => ?_
  obtain lk1 := lka.trans (AltOp.lk h1 (by decide))
  obtain z1 : b1.gpr .x17 = 0 := (h1.gpr _ (by decide)).trans za
  rw [WP.block_append_iff]
  refine WP.mono (addE (lk1.scratch hs) 1 3 4 (by decide) (by decide) (by decide) z1
    (by rw [fr h1 3 (by decide)]; exact B 3 rfl) (by rw [fr h1 4 (by decide)]; exact B 4 rfl))
    fun b2 ⟨h2, e2⟩ => ?_
  obtain lk2 := lk1.trans (AltOp.lk h2 (by decide))
  obtain z2 : b2.gpr .x17 = 0 := (h2.gpr _ (by decide)).trans z1
  rw [WP.block_append_iff]
  refine WP.mono (cmadd4x_ok (lk2.scratch hs) z2) fun b3 ⟨lk3', z3, l3, o3, e3⟩ => ?_
  obtain lk3 := lk2.trans lk3'
  obtain o3fe : ∀ j : VG.Impl.Ed25519.AArch64.Slot, j ≠ 4 →
      fe b3.mem base (offset j) = fe b2.mem base (offset j) :=
    fun j hj => o3.fe (apart j 4 hj) (by simp only [offset]; omega_using [])
  rw [WP.block_append_iff]
  refine WP.mono (sqrE (lk3.scratch hs) 8 8 (by decide) (by decide) z3)
    fun b4 ⟨h4, l4, e4⟩ => ?_
  obtain lk4 := lk3.trans (AltOp.lk h4 (by decide))
  obtain z4 : b4.gpr .x17 = 0 := (h4.gpr _ (by decide)).trans z3
  rw [WP.block_append_iff]
  refine WP.mono (sqrE (lk4.scratch hs) 1 1 (by decide) (by decide) z4)
    fun b5 ⟨h5, l5, e5⟩ => ?_
  obtain lk5 := lk4.trans (AltOp.lk h5 (by decide))
  obtain z5 : b5.gpr .x17 = 0 := (h5.gpr _ (by decide)).trans z4
  rw [WP.block_append_iff]
  refine WP.mono (mulE (lk5.scratch hs) 3 0 4 (by decide) (by decide) (by decide) z5)
    fun b6 ⟨h6, l6, e6⟩ => ?_
  obtain lk6 := lk5.trans (AltOp.lk h6 (by decide))
  obtain z6 : b6.gpr .x17 = 0 := (h6.gpr _ (by decide)).trans z5
  rw [WP.block_append_iff]
  refine WP.mono (subE (lk6.scratch hs) 7 1 8 (by decide) (by decide) (by decide) z6
    (by rw [fr h6 8 (by decide), fr h5 8 (by decide)]; exact l4)) fun b7 ⟨h7, e7⟩ => ?_
  obtain lk7 := lk6.trans (AltOp.lk h7 (by decide))
  obtain z7 : b7.gpr .x17 = 0 := (h7.gpr _ (by decide)).trans z6
  rw [WP.block_append_iff]
  refine WP.mono (cmaddA24_ok (lk7.scratch hs) z7) fun b8 ⟨lk8', z8, _, _, o8, e8⟩ => ?_
  obtain lk8 := lk7.trans lk8'
  obtain o8fe : ∀ j : VG.Impl.Ed25519.AArch64.Slot, j ≠ 2 →
      fe b8.mem base (offset j) = fe b7.mem base (offset j) :=
    fun j hj => o8.fe (apart j 2 hj) (by simp only [offset]; omega_using [])
  rw [WP.block_append_iff]
  refine WP.mono (mulE (lk8.scratch hs) 1 1 8 (by decide) (by decide) (by decide) z8)
    fun b9 ⟨h9, l9, e9⟩ => ?_
  obtain lk9 := lk8.trans (AltOp.lk h9 (by decide))
  obtain z9 : b9.gpr .x17 = 0 := (h9.gpr _ (by decide)).trans z8
  rw [WP.block_append_iff]
  refine WP.mono (mulE (lk9.scratch hs) 2 7 2 (by decide) (by decide) (by decide) z9)
    fun b10 ⟨h10, l10, e10⟩ => ?_
  obtain lk10 := lk9.trans (AltOp.lk h10 (by decide))
  refine WP.mono (swap1_ok (lk10.scratch hs)) fun t ⟨lkt, et, wt, ot⟩ => ?_
  obtain otfe : ∀ j : VG.Impl.Ed25519.AArch64.Slot, fe t.mem base (offset j) = fe b10.mem base (offset j) :=
    fun j => ot.fe (Or.inl (by simp only [offset]; omega_using [])) (by simp only [offset]; omega_using [])
  obtain h254 : ladderAfter k x1 254 = ladderStep k x1 (init x1) 254 :=
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
  obtain lk1 := AltOp.lk h1 (by decide)
  obtain z1 : b1.gpr .x17 = 0 := (h1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (addE (lk1.scratch hs) 1 1 2 (by decide) (by decide) (by decide) z1
    (by rw [fr h1 1 (by decide)]; exact l1) (by rw [fr h1 2 (by decide)]; exact l2))
    fun b2 ⟨h2, e2⟩ => ?_
  obtain lk2 := lk1.trans (AltOp.lk h2 (by decide))
  obtain z2 : b2.gpr .x17 = 0 := (h2.gpr _ (by decide)).trans z1
  rw [WP.block_append_iff]
  refine WP.mono (sqrE (lk2.scratch hs) 8 8 (by decide) (by decide) z2)
    fun b3 ⟨h3, l3, e3⟩ => ?_
  obtain lk3 := lk2.trans (AltOp.lk h3 (by decide))
  obtain z3 : b3.gpr .x17 = 0 := (h3.gpr _ (by decide)).trans z2
  rw [WP.block_append_iff]
  refine WP.mono (sqrE (lk3.scratch hs) 1 1 (by decide) (by decide) z3)
    fun b4 ⟨h4, _, e4⟩ => ?_
  obtain lk4 := lk3.trans (AltOp.lk h4 (by decide))
  obtain z4 : b4.gpr .x17 = 0 := (h4.gpr _ (by decide)).trans z3
  rw [WP.block_append_iff]
  refine WP.mono (subE (lk4.scratch hs) 7 1 8 (by decide) (by decide) (by decide) z4
    (by rw [fr h4 8 (by decide)]; exact l3)) fun b5 ⟨h5, e5⟩ => ?_
  obtain lk5 := lk4.trans (AltOp.lk h5 (by decide))
  obtain z5 : b5.gpr .x17 = 0 := (h5.gpr _ (by decide)).trans z4
  rw [WP.block_append_iff]
  refine WP.mono (cmaddA24_ok (lk5.scratch hs) z5) fun b6 ⟨lk6', z6, _, _, _, e6⟩ => ?_
  obtain lk6 := lk5.trans lk6'
  rw [WP.block_append_iff]
  refine WP.mono (mulE (lk6.scratch hs) 1 1 8 (by decide) (by decide) (by decide) z6)
    fun b7 ⟨h7, l7, e7⟩ => ?_
  obtain lk7 := lk6.trans (AltOp.lk h7 (by decide))
  obtain z7 : b7.gpr .x17 = 0 := (h7.gpr _ (by decide)).trans z6
  refine WP.mono (mulE (lk7.scratch hs) 2 7 2 (by decide) (by decide) (by decide) z7)
    fun t ⟨h8, l8, e8⟩ => ?_
  obtain henv : env t.mem base = dblEnv (env s.mem base) := by
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
  obtain hsa : Scratch a base := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hsa (d := 768) (by decide) (by decide) .x3) fun b ⟨bs, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, WP.block_nil ?_⟩
  obtain kc : Keeps [.x2] b (b.write .x .x2 ((0 : BitVec 16).setWidth 64)) :=
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
  rcases (by omega_using [hsw] : sw = 0 ∨ sw = 1) with rfl | rfl <;> rfl

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
  obtain hsw := ladderAfter_swap_le k x1 (n := 3) (by decide)
  simp only [VG.Impl.X25519.AArch64.AltLadder.tail, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (tailFlags_ok hs hsw hw) fun a ⟨lka, za, fa, ma⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (muxE (lka.scratch hs) 1 3 1 (by decide) (by decide) (by decide))
    fun b1 ⟨h1', z1f, f1, e1⟩ => ?_
  obtain lk1 := lka.trans (AltOp.lk h1' (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (muxE (lk1.scratch hs) 2 4 2 (by decide) (by decide) (by decide))
    fun b2 ⟨h2', _, f2, e2⟩ => ?_
  obtain lk2 := lk1.trans (AltOp.lk h2' (by decide))
  obtain z2 : b2.gpr .x17 = 0 := (h2'.gpr _ (by decide)).trans ((h1'.gpr _ (by decide)).trans za)
  obtain l1 : fe b2.mem base (offset 1) < P2 := by
    rw [fr h2' 1 (by decide), f1, ma]
    split
    · exact hB 1 rfl
    · exact hB 3 rfl
  obtain l2 : fe b2.mem base (offset 2) < P2 := by
    rw [f2, z1f, fr h1' 2 (by decide), fr h1' 4 (by decide), ma]
    split
    · exact hB 2 rfl
    · exact hB 4 rfl
  obtain ⟨g0, g1, g2, g3, g4, _⟩ := hg
  obtain v1 : env b2.mem base 1 = (Spec.X25519.cswap (ladderAfter k x1 3).swap
      (ladderAfter k x1 3).x2 (ladderAfter k x1 3).x3).1 := by
    rw [e2, Function.update_of_ne (by decide), e1, Function.update_self, fa, ma, g1, g3,
      cswap_fst hsw]
  obtain v2 : env b2.mem base 2 = (Spec.X25519.cswap (ladderAfter k x1 3).swap
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
  obtain s2 := ladderStep_zero k x1 (ladderAfter k x1 3) 2 h2
  obtain s1 := ladderStep_zero k x1 (ladderAfter k x1 2) 1 h1
  obtain s0 := ladderStep_zero k x1 (ladderAfter k x1 1) 0 h0
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

end

end

/-! ### `X25519.AArch64.Word.Output`, which only this module used -/

section

/-! ### `X25519.AArch64.Word.Input`, which only this module used -/

section

/-! Decode RFC 7748 inputs into four-word fields. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

abbrev Kp := VG.Proof.X25519.AArch64.Kp
abbrev Sc := VG.Proof.X25519.AArch64.Sc

theorem outside_frame {base : Addr} {m m' : Mem} {d n : Nat}
    (h : Outside base d n m m') (hn : d+n ≤ 4096) : Frame [⟨base,4096⟩] m m' := by
  intro x hx
  apply h x
  obtain hh := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hh
  right
  change d+n ≤ (x-base).toNat
  omega_using [hn, hh]

theorem base_ok {base : Addr} {s : State} (hs : Sc base s)
    (hn : base.toNat + 4096 ≤ 2^64) :
    WP isa (.block [VG.Impl.X25519.AArch64.st .x0 48, mov .x1 .x0, mov .x0 .x3]) s fun t =>
      Scratch t base ∧ t.gpr .x1 = s.gpr .x0 ∧ word t.mem base 48 = s.gpr .x0 ∧
      Kp [.x0,.x1] s t ∧ Outside base 48 8 s.mem t.mem := by
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.X25519.AArch64.exec_st hs .x0 (off := 48) (by decide), ?_⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, mov,
    exec_addImm_x (by decide : 0 < 4096), read_x, BitVec.add_zero, RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨⟨hs.x3,hs.wr,hn⟩, trivial, Mem.readW_writeW_self64 _ _ _,
    ⟨fun r hr => by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr; simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false],rfl,rfl⟩,
    writeW_outside _ _ _ (by decide)⟩

theorem initGood (e : Env) (x : Fe) (hx : e 0 = x) :
    Good (evalOps ([.copy 3 0, .const 1 1, .const 2 0, .const 4 1, .const 18 121665] : List FieldOp) e) x (init x) :=
  ⟨hx, rfl, rfl, hx, rfl, rfl⟩


theorem decode_ok {base p : Addr} {s : State} (hs : Scratch s base)
    (hp : s.gpr .x2 = p)
    (hr : ∀ d, d+8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block (loadY ++ store4 (offset 0))) s fun t =>
      Keep base s t ∧ env t.mem base 0 = toFe (decodeUCoordinate (bytesAt s.mem p 32)) ∧
      fe t.mem base (offset 0) < 2 ^ 255 := by
  rw [WP.block_append_iff]
  refine WP.mono (loadY_ok s p hp hr) fun a ⟨av,ka⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps ka (by decide)) (slot_rangeWith (large := false) 0)) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hr => ka.gpr r (fun hh => hr (by simp only [clob, List.mem_cons, List.not_mem_nil, or_false] at *; grind)),
    ka.rd,ka.wr,ka.sp,?_,⟩,?_,?_⟩
  · rw [ka.mem]
    exact (st4_outside _ _ (by decide : offset 0+32<2^64) _ _ _ _).mono (by decide) (by decide)
  · change toFe (fe _ _ _) = _
    rw [fe_st4 _ _ (by decide), av, VG.Proof.Ed25519.decodeLE_eq,
      decodeUCoordinate_eq (length_bytesAt _ _ _)]
    rfl
  · rw [fe_st4 _ _ (by decide), av]
    exact Nat.mod_lt _ (by decide)

theorem init_ok {base : Addr} {s : State} {x : Fe} (hs : Scratch s base)
    (hx : env s.mem base 0 = x) (h0 : fe s.mem base (offset 0) < 2 ^ 255) :
    WP isa (.block (fieldCode ([.copy 3 0, .const 1 1, .const 2 0, .const 4 1, .const 18 121665] : List FieldOp) ++
      ([.movz .x .x2 0 0, VG.Impl.Ed25519.AArch64.st .x2 768] : List Instr))) s fun t =>
      LoopKeep base s t ∧ Good (env t.mem base) x (init x) ∧ word t.mem base 768 = 0 ∧
      Small t.mem base fun i => decide (1 ≤ i.val ∧ i.val ≤ 4) := by
  rw [WP.block_append_iff]
  obtain hS : Small s.mem base fun i => decide (i = 0) := fun i hi => by
    have : i = 0 := of_decide_eq_true hi
    subst this
    omega_using [h0]
  refine WP.mono (fieldCode_okS _ hs hS) fun a ⟨ka,ea,sa⟩ => ?_
  obtain ga := initGood (env s.mem base) x hx
  rw [← ea] at ga
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.X25519.AArch64.exec_movz, ?_⟩
  obtain kb : Keeps [.x2] a (a.write .x .x2 0) :=
    ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),rfl,rfl,rfl,rfl⟩
  obtain kab := (LoopKeep.of_field ka).trans (LoopKeep.of_keeps kb (by decide))
  refine WP.mono (storeSwap_ok (kab.scratch hs)) fun t ⟨kt,et,wt,_,ot⟩ => ?_
  obtain sa' : Small (a.write .x .x2 0).mem base
      (smallAfterOps [.copy 3 0, .const 1 1, .const 2 0, .const 4 1, .const 18 121665] fun i => decide (i = 0)) := by
    rw [RegUpd.mem_write]; exact sa
  exact ⟨kab.trans kt, by rw [et,RegUpd.mem_write]; exact ga,
    wt.trans (RegUpd.gpr_write_self _ _ _ _), (sa'.frame ot (by decide)).mono (by decide)⟩


theorem LoopKeep.kp {base : Addr} {s t : State} (h : LoopKeep base s t) :
    Kp (clob ++ ([.x19] : List Reg)) s t :=
  ⟨fun r hr => h.gpr r (fun hc => hr (List.mem_append_left _ hc))
    (fun hc => hr (List.mem_append_right _ (by simp [hc]))),h.rd,h.wr⟩

theorem savedBits {base : Addr} {m m' : Mem}
    (hf : Frame [VG.Proof.X25519.AArch64.bitsArea base] m m') {i : Nat} (hi : i < 6) :
    word m' base (8*i) = word m base (8*i) := by
  apply BitVec.eq_of_toNat_eq
  obtain hh := VG.Proof.X25519.AArch64.save_frame (b := base) (k := i) hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.AArch64.saveR_disj _ (by decide) (by decide)) hi
  simpa only [VG.Proof.X25519.AArch64.wd, VG.Impl.X25519.AArch64.SAVE, Nat.zero_add] using hh

theorem savedInitial {base : Addr} {m : Mem} {g : Reg → BitVec 64}
    (h : ∀ i < 6, VG.Proof.X25519.AArch64.wd m base (VG.Impl.X25519.AArch64.SAVE+8*i) =
      (g (VG.Impl.X25519.AArch64.saved.getD i .x19)).toNat) {i : Nat} (hi : i < 6) :
    word m base (8*i) = g (VG.Impl.X25519.AArch64.saved.getD i .x19) := by
  apply BitVec.eq_of_toNat_eq
  simpa only [VG.Proof.X25519.AArch64.wd, VG.Impl.X25519.AArch64.SAVE, Nat.zero_add] using h i hi

theorem setup_ok {base sc pt : Addr} {s : State} (hs : Sc base s)
    (hn : base.toNat+4096 ≤ 2^64) (h1 : s.gpr .x1 = sc) (h2 : s.gpr .x2 = pt)
    (hsr : (⟨sc,32⟩ : Region) ∈ s.rd) (hpr : (⟨pt,32⟩ : Region) ∈ s.rd)
    (hdS : (⟨sc,32⟩ : Region).Disjoint ⟨base,4096⟩)
    (hdP : (⟨pt,32⟩ : Region).Disjoint ⟨base,4096⟩) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.setup) s fun t =>
      Scratch t base ∧ Good (env t.mem base) (toFe (decodeUCoordinate (bytesAt s.mem pt 32)))
        (init (toFe (decodeUCoordinate (bytesAt s.mem pt 32)))) ∧
      word t.mem base 768 = 0 ∧ t.gpr .x1 = s.gpr .x0 ∧
      (∀ i < 255, t.mem (off base (bitOffset+i)) = BitVec.ofNat 8 (bit (decodeScalar25519 (bytesAt s.mem sc 32)) i)) ∧
      (∀ i < 6, word t.mem base (8*i) = s.gpr (VG.Impl.X25519.AArch64.saved.getD i .x19)) ∧
      Kp (clob ++ ([.x0,.x1,.x19] : List Reg)) s t ∧
      Small t.mem base (fun i => decide (1 ≤ i.val ∧ i.val ≤ 4)) := by
  rw [VG.Impl.X25519.AArch64.Word.setup]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.save_ok hs) fun a ⟨sv,fa,ka⟩ => ?_
  obtain hsa := hs.of_kp ka (by decide)
  obtain fsa : ∀ r ∈ [VG.Proof.X25519.AArch64.saveR base], Region.Sub r (VG.Proof.X25519.AArch64.scR base) := by
    intro r hr; rw [List.mem_singleton.mp hr]; exact Region.sub_of_ble rfl
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.bits_ok hsa
    (by rw [ka.gpr _ (by simp),h1])
    (fun i hi => ⟨_,List.mem_append_left _ (ka.rd ▸ hsr),Offset.contains_base sc (by omega_using [hi]) (by omega_using [hi])⟩)
    (fun i hi r hr => by
      rw [List.mem_singleton.mp hr]
      exact hdS.sub_right (VG.Proof.X25519.AArch64.sub_scR base (d := VG.Impl.X25519.AArch64.BITS) (n := 256) (by decide)) _
        (Offset.contains_base sc (by omega_using [hi]) (by omega_using [hi])))) fun b ⟨bb,fb,kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (hsa.of_kp kb (by decide)) hn) fun c ⟨hsc,oc,wc,kc,fc⟩ => ?_
  obtain fsc := outside_frame fc (by decide)
  obtain fsb : ∀ r ∈ [VG.Proof.X25519.AArch64.bitsArea base], Region.Sub r (VG.Proof.X25519.AArch64.scR base) := by
    intro r hr; rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.AArch64.sub_scR _ (by decide)
  obtain bp : bytesAt c.mem pt 32 = bytesAt s.mem pt 32 := by
    rw [VG.Proof.X25519.AArch64.bytesAt_out fsc (by simp only [List.mem_singleton,forall_eq]; exact Region.sub_of_ble rfl) hdP,
      VG.Proof.X25519.AArch64.bytesAt_out fb fsb hdP,
      VG.Proof.X25519.AArch64.bytesAt_out fa fsa hdP]
  change WP isa (.block ((loadY ++ store4 (offset 0)) ++
    (fieldCode [.copy 3 0,.const 1 1,.const 2 0,.const 4 1,.const 18 121665] ++
    ([.movz .x .x2 0 0, VG.Impl.Ed25519.AArch64.st .x2 768] : List Instr)))) c _
  rw [WP.block_append_iff]
  refine WP.mono (decode_ok hsc (by rw [kc.gpr _ (by decide),kb.gpr _ (by decide),ka.gpr _ (by simp),h2])
    (fun d hd => ⟨_,List.mem_append_left _ (by rw [kc.rd,kb.rd,ka.rd]; exact hpr),
      Offset.contains_base pt (by omega_using [hd]) (by omega_using [hd])⟩)) fun d ⟨kd,xd,bd⟩ => ?_
  rw [bp] at xd
  refine WP.mono (init_ok (kd.scr hsc) xd bd) fun t ⟨kt,gt,wt,st⟩ => ?_
  obtain ft : Outside base 48 728 b.mem t.mem :=
    (fc.mono (by decide) (by decide)).trans
      ((kd.mem.mono (by decide) (by decide)).trans (kt.mem.mono (by decide) (by decide)))
  refine ⟨kt.scratch (kd.scr hsc),gt,wt,?_,?_,?_,?_,st⟩
  · rw [kt.gpr _ (by decide) (by decide), kd.gpr _ (by decide),oc,
      kb.gpr _ (by decide),ka.gpr _ (by simp)]
  · intro i hi
    rw [ft (off base (bitOffset+i)) (by
      right; rw [ofs_off' base (by have := bitOffset_lt; omega_using [hi, this])]; have := bitOffset_lt; change 776 ≤ bitOffset+i; simp only [bitOffset, VG.Impl.X25519.AArch64.Word.BITS, VG.Impl.X25519.AArch64.BITS, VG.Impl.X25519.AArch64.slot, VG.Impl.X25519.AArch64.NSLOT]; omega_using []), bb i (by omega_using [hi])]
    exact VG.Proof.X25519.AArch64.clampB_eq (fun j hj => VG.Proof.X25519.AArch64.byte_out fa fsa hdS hj) hi
  · intro i hi
    rw [ft.word (Or.inl (by omega_using [hi])) (by omega_using [hi]), savedBits fb hi]
    exact savedInitial sv hi
  · exact (((ka.trans kb).trans kc).trans
      ((LoopKeep.of_field kd).trans kt).kp).sub (by decide)

end VG.Proof.X25519.AArch64.Word

end

end


/-! Canonical field encoding and restoration of the caller's registers. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

theorem restore_ok {s : State} {base : Addr} (hb : s.gpr .x0 = base)
    (hw : (⟨base, 4096⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64} (hsv : Saved base g s.mem) :
    WP isa (.block (saved.map (fun (r,o) => VG.Impl.Ed25519.AArch64.ld r o))) s fun t =>
      (∀ rd ∈ saved, t.gpr rd.1 = g rd.1) ∧ Keeps [.x19, .x20, .x21, .x22, .x23, .x24] s t := by
  obtain hr : ∀ d, d + 8 ≤ 4096 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_scWith (large := false) hd⟩
  apply WP.of_runBlock
  simp only [VG.Impl.Ed25519.AArch64.ld, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, State.load, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, hb, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self,
    hr 0 (by omega_using []), hr 8 (by omega_using []), hr 16 (by omega_using []), hr 24 (by omega_using []), hr 32 (by omega_using []), hr 40 (by omega_using []),
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun rd hrd => ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := hsv rd hrd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, word, Mem.readW,
        BitVec.setWidth_eq] using e
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem out_ok {s : State} {q : Addr} (hq : s.gpr .x1 = q) (hw : (⟨q, 32⟩ : Region) ∈ s.wr) :
    WP isa (.block [.str .x .x4 .x1 0, .str .x .x5 .x1 8, .str .x .x6 .x1 16, .str .x .x7 .x1 24]) s
      fun t => t = { s with mem := st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) } := by
  obtain w : ∀ d, d + 8 ≤ 32 → InRegions s.wr (off q d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base q hd (by omega_using [hd])⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.store, read_x,
    hq, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true,
    w 0 (by omega_using []), w 8 (by omega_using []), w 16 (by omega_using []), w 24 (by omega_using []),
    Option.bind_some, Option.some.injEq, exists_eq_left']
  rfl



theorem saved_output {base q : Addr} {m : Mem} {g : Reg → BitVec 64}
    (hs : Saved base g m) (hd : (⟨q,32⟩ : Region).Disjoint ⟨base,4096⟩)
    (w0 w1 w2 w3 : BitVec 64) : Saved base g (st4 m q 0 w0 w1 w2 w3) := by
  obtain hf : Frame [⟨q,32⟩] m (st4 m q 0 w0 w1 w2 w3) := by
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 0) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 8) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 16) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 24) (by decide) (by decide))
  intro rd hr
  obtain hh : rd.2+8 ≤ 4096 := by
    simp only [saved,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  change (st4 m q 0 w0 w1 w2 w3).readW (off base rd.2) 64 = g rd.1
  rw [hf.readW (a := off base rd.2) (w := 64) (r := ⟨base,4096⟩) (Offset.contains_base base hh (by omega_using [hh]))
    (by simp only [List.mem_singleton,forall_eq]; exact hd.symm) (by decide)]
  exact hs rd hr

theorem keeps_kp {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hr : rs ⊆ clob ++ ([.x1,.x19] : List Reg)) : Kp (clob ++ ([.x1,.x19] : List Reg)) s t :=
  ⟨fun r hn => h.gpr r (fun hh => hn (hr hh)),h.rd,h.wr⟩

theorem field_kp {base : Addr} {s t : State} (h : Keep base s t) : Kp (clob ++ ([.x1,.x19] : List Reg)) s t :=
  ⟨fun r hr => h.gpr r (fun hh => hr (List.mem_append_left _ hh)),h.rd,h.wr⟩


theorem serialize_ok {base q : Addr} {s : State} {g : Reg → BitVec 64}
    (hs : Scratch s base) (ho : s.gpr .x1 = q)
    (hw : (⟨q,32⟩ : Region) ∈ s.wr) (hd : (⟨q,32⟩ : Region).Disjoint ⟨base,4096⟩)
    (hsv : Saved base g s.mem) :
    WP isa (.block (([.str .x .x4 .x1 0,.str .x .x5 .x1 8,.str .x .x6 .x1 16,.str .x .x7 .x1 24] : List Instr) ++
      saved.map (fun (r,o) => VG.Impl.Ed25519.AArch64.ld r o))) s fun t =>
      (∀ rd ∈ saved, t.gpr rd.1 = g rd.1) ∧ Kp (clob ++ ([.x1,.x19] : List Reg)) s t ∧
      bytesAt t.mem q 32 = leBytes 32 (val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)) := by
  rw [WP.block_append_iff]
  refine WP.mono (out_ok ho hw) fun d de => ?_
  subst d
  obtain svd := saved_output hsv hd (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
  refine WP.mono (restore_ok (s := {s with mem := st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)})
    (g := g) hs.x0 hs.wr svd) fun t ⟨tg,kt⟩ => ?_
  obtain ko : Kp (clob ++ ([.x1,.x19] : List Reg)) s
      {s with mem := st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)} :=
    ⟨fun _ _ => rfl,rfl,rfl⟩
  exact ⟨tg,ko.trans (keeps_kp kt (by decide)) |>.sub (by decide),by rw [kt.mem,bytesAt_st4]⟩

theorem finish_ok {base q : Addr} {s : State} {g : Reg → BitVec 64}
    (hs : Scratch s base) (ho : s.gpr .x1 = q)
    (hw : (⟨q,32⟩ : Region) ∈ s.wr) (hd : (⟨q,32⟩ : Region).Disjoint ⟨base,4096⟩)
    (hsv : Saved base g s.mem) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.finish) s fun t =>
      (∀ rd ∈ saved, t.gpr rd.1 = g rd.1) ∧
      Kp (clob ++ ([.x1,.x19] : List Reg)) s t ∧
      bytesAt t.mem q 32 = encodeUCoordinate (env s.mem base 1 * env s.mem base 15) := by
  rw [VG.Impl.X25519.AArch64.Word.finish]
  simp only [VG.Impl.X25519.AArch64.Word.freeze,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.mul_ok hs (slot_rangeWith (large := false) 1)
    (slot_rangeWith (large := false) 1) (slot_rangeWith (large := false) 15)) fun a ⟨ka,ea⟩ => ?_
  obtain kma := op_keep (o := 1) ka
  obtain sva := hsv.outside kma.mem (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.freeze_ok (kma.scr hs) (slot_rangeWith (large := false) 1)) fun b ⟨bv,kb⟩ => ?_
  obtain hb := (kma.scr hs).of_keeps kb (by decide)
  refine WP.mono (serialize_ok (g := g) hb
    (by rw [kb.gpr _ (by decide),kma.gpr _ (by decide),ho])
    (by rw [kb.wr,kma.wr]; exact hw) hd (by rw [kb.mem]; exact sva)) fun t ⟨tg,kt,rt⟩ => ?_
  refine ⟨tg,?_,?_⟩
  · exact ((field_kp kma).trans (keeps_kp kb (by decide))).trans kt |>.sub (by decide)
  · rw [rt,encodeUCoordinate_eq,bv]
    exact congrArg (leBytes 32) (congrArg Fin.val ea)

end VG.Proof.X25519.AArch64.Word

end

end


/-!
# X25519 on AArch64: the `_alt` ladder's whole function

The four-word function's setup, the `_alt` ladder with its first and last
iterations, and the four-word function's inversion and output. No instruction writes a vector
register, so `v8`–`v15` are kept without being saved.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.AltLadder

open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 (offset)
open VG.Proof.Ed25519.AArch64 (env F Outside ofs clob word off ofs_off' Saved Small)
open VG.Proof.X25519.AArch64.Word (LoopKeep Good bitOffset localContract Kp Sc saved_of_words
  preservedCases Scratch)

theorem correct [VG.Proof.Ed25519.AArch64.Divstep.Sound] {s₀ : State} (hp : localContract.pre s₀) :
    WP isa VG.Impl.X25519.AArch64.AltLadder.x25519 s₀ fun t =>
      (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧ localContract.post s₀ t := by
  obtain pre := VG.Proof.X25519.AArch64.Pre.of s₀ hp.1
  let base := s₀.gpr .x3
  obtain hs : Sc base s₀ := ⟨rfl,by rw [pre.wr]; simp [base,VG.Proof.X25519.AArch64.scR]⟩
  rw [VG.Impl.X25519.AArch64.AltLadder.x25519]
  refine WP.seq (WP.mono (VG.Proof.X25519.AArch64.Word.setup_ok hs hp.2 rfl rfl
    (by rw [pre.rd]; simp) (by rw [pre.rd]; simp) pre.scalar_sc pre.point_sc)
    fun c ⟨hc, gc, wc, oc, bc, svc, kc, sc⟩ => ?_)
  obtain kl := length_bytesAt s₀.mem (s₀.gpr .x1) 32
  refine WP.seq (WP.mono (first_ok (k := decodeScalar25519 (bytesAt s₀.mem (s₀.gpr .x1) 32)) hc gc
    (by rw [scalar_bit kl (by decide)]; rfl) sc)
    fun c' ⟨kc', gc', wc', bc'⟩ => ?_)
  obtain hc' := kc'.scratch hc
  refine WP.seq (WP.mono (ladder_ok hc' gc' wc' (fun i hi => by rw [kc'.bit hi]; exact bc i hi) bc')
    fun d ⟨kd', gd, wd, bd⟩ => ?_)
  obtain kd := kc'.trans kd'
  obtain hd := kd.scratch hc
  refine WP.seq (WP.mono (tail_ok hd gd wd bd (by rw [scalar_bit kl (by decide)]; rfl)
    (by rw [scalar_bit kl (by decide)]; rfl) (by rw [scalar_bit kl (by decide)]; rfl))
    fun e ⟨ke, ex, ez⟩ => ?_)
  obtain he := ke.scratch hd
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.Divstep.invert_ok he) fun f ⟨fi, fk, f1, fm⟩ => ?_)
  obtain hf : Scratch f base := ⟨(fk.gpr _ (by decide)).trans he.x0, fk.wr ▸ he.wr, he.nowrap⟩
  obtain saved : Saved base s₀.gpr f.mem :=
    (((saved_of_words svc).outside kd.mem (by decide)).outside ke.mem (by decide)).outside fm (by decide)
  obtain out : f.gpr .x1 = s₀.gpr .x0 :=
    f1.trans ((ke.gpr _ (by decide) (by decide)).trans ((kd.gpr _ (by decide) (by decide)).trans oc))
  obtain dx : env f.mem base 1 = env e.mem base 1 :=
    congrArg toFe (VG.Proof.Ed25519.AArch64.Outside.fe fm (Or.inl (by decide : offset 1+32 ≤ 192))
      (by decide))
  obtain kf' : Kp (.x19 :: VG.Proof.Mont.AArch64.clob 4 ++ [.x2, .x20]) e f := ⟨fk.gpr, fk.rd, fk.wr⟩
  refine WP.mono (VG.Proof.X25519.AArch64.Word.finish_ok (g := s₀.gpr) hf out
    (by rw [fk.wr, ke.wr, kd.wr, kc.wr, pre.wr]; simp) pre.out_sc saved)
    fun t ⟨tg, kt, rt⟩ => ?_
  refine ⟨fun r hr => ?_, ?_⟩
  · rcases preservedCases r hr with ⟨rd,hrd,er⟩ | hn
    · rw [← er]; exact tg rd hrd
    · have kk := (((kc.trans kd.kp).trans ke.kp).trans kf').trans kt
      exact kk.sub (by decide) |>.gpr r hn
  · change bytesAt t.mem (s₀.gpr .x0) 32 = Spec.X25519.x25519
      (bytesAt s₀.mem (s₀.gpr .x1) 32) (bytesAt s₀.mem (s₀.gpr .x2) 32)
    rw [rt, dx, fi, ex, ez, x25519_eq]

theorem x25519_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] (s : State) (hs : localContract.pre s) :
    ∃ tr t, Exec isa VG.Impl.X25519.AArch64.AltLadder.x25519 s tr t ∧ abiPreserved s t ∧
      localContract.post s t := by
  obtain ⟨tr,t,he,⟨hg,hp⟩,hv⟩ := WP.preservedV (correct hs) (by lit_decide)
  exact ⟨tr,t,he,⟨hg,Exec.sp he,hv⟩,hp⟩

end VG.Proof.X25519.AArch64.AltLadder
