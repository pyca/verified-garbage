module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Dsa.RISCV64.Common
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on RISC-V: saving and restoring the callee-saved registers

`save ws` stores `s0`–`s5`, `s7`–`s11`, `ra` and `s6` in the P space's header
words 16–28 (at `ws`) and copies its address into `s6`; `restore` loads
them back through `s6`, `s6` last. (`Proof/Bignum/RISCV64/CrtSave.lean`'s
proofs, for this layout.)
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64 (Scr off_add add_ofNat_zero)

/-- The saved registers' words, 104 bytes. -/
abbrev savR (w : Addr) : Region := ⟨w, 104⟩

theorem saved_inj : ∀ i < 13, ∀ j < 13, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 12, saved i ≠ .s6 := by decide

theorem saved_12 : saved 12 = .s6 := rfl

theorem saved_ne_t2 : ∀ i < 13, saved i ≠ .t2 := by decide

theorem sav_contains (w : Addr) {i : Nat} (hi : i < 13) : (savR w).Contains (off w (8 * i)) 8 :=
  Offset.contains_base w (by omega_using [hi]) (by omega_using [hi])

theorem sav_sep (w : Addr) {i j : Nat} (hi : i < 13) (hj : j < 13) (h : i ≠ j) :
    Mem.Sep (off w (8 * i)) 8 (off w (8 * j)) 8 :=
  Offset.sep w (by omega_using [hi, hj, h]) (by omega_using [hi]) (by omega_using [hj])

/-- The saved registers' words of the working space at `S`. -/
abbrev savW (S : Addr) : Addr := S + BitVec.ofNat 64 128

theorem saveOff_eq (S : Addr) (i : Nat) : S + BitVec.ofNat 64 (saveOff i) = off (savW S) (8 * i) := by
  rw [off, Offset.add_add, saveOff]

/-- The first `n` registers are saved, from `s₀` (whose `t2` is the working
space). -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [savR (savW (s₀.gpr .t2))] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off (savW (s₀.gpr .t2)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step (s₀ : State) (hin : ∀ i < 13, InRegions s₀.wr (off (savW (s₀.gpr .t2)) (8 * i)) 8)
    (hal : ∀ i < 13, (off (savW (s₀.gpr .t2)) (8 * i)).toNat % 8 = 0)
    {n : Nat} (hn : n < 13) {s : State}
    (h : SI s₀ n s) : WP isa (.block [.store .d (saved n) .t2 (saveOff n)]) s (SI s₀ (n + 1)) := by
  have hw : s.gpr .t2 = s₀.gpr .t2 := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .t2 + BitVec.ofNat 64 (saveOff n)) 8 := by
    rw [h.wr, hw, saveOff_eq]; exact hin n hn
  have ha : (s.gpr .t2 + BitVec.ofNat 64 (saveOff n)).toNat % 8 = 0 := by
    rw [hw, saveOff_eq]; exact hal n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show saveOff n < 2048 by unfold saveOff; omega_using [hn]) ha hout,
    Option.some.injEq, exists_eq_left', hw, saveOff_eq]
  refine ⟨h.gpr, h.rd, h.wr, h.sp,
    h.frame.writeW (List.mem_singleton_self _) _ (sav_contains _ hn), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_using [hi, hn]) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The state after `save`, from `s₀`, the working space at `S`. -/
structure Saved (s₀ : State) (S : Addr) (s : State) : Prop where
  keep : Keep [.t2, .s6] s₀ s
  sp : s.sp = s₀.sp
  s6 : s.gpr .s6 = S
  frame : Frame [savR (savW S)] s₀.mem s.mem
  saved : ∀ i < 13, s.mem.readW (off (savW S) (8 * i)) 64 = s₀.gpr (saved i)

/-- The working space `S` from the first stack argument, then `save`. -/
theorem save_ok (s₀ : State) {S : Addr} (hS : stackArg s₀ 0 = S)
    (hst : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 8) (hsp : s₀.sp.toNat % 8 = 0)
    (hin : ∀ i < 13, InRegions s₀.wr (off (savW S) (8 * i)) 8)
    (hal : ∀ i < 13, (off (savW S) (8 * i)).toNat % 8 = 0) :
    WP isa (.block (([.addSp .t2 0, .load .d .t2 .t2 0] : List Instr) ++ save .t2)) s₀ (Saved s₀ S) := by
  rw [save, ← List.append_assoc]
  have hst' : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 0) 8 := by
    simpa only [stackArgAddr] using hst
  have hsa : (s₀.sp + BitVec.ofNat 64 0).toNat % 8 = 0 := by rw [add_ofNat_zero]; exact hsp
  have hv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 0) 64 = S := by
    rw [← hS]; simp [stackArg, stackArgAddr]
  have first : WP isa (.block [.addSp .t2 0, .load .d .t2 .t2 0]) s₀ fun s₁ => s₁ = s₀.write .t2 S := by
    brun [exec_addSp (show 0 < 2048 by decide), hst', hsa, hv, write_write]
  refine WP.block_append (WP.block_append (WP.mono first ?_))
  rintro s₁ rfl
  have h0 : (s₀.write .t2 S).gpr .t2 = S := gpr_write_self _ _ _
  refine WP.mono (wp_range_flatMap (M := isa) (SI (s₀.write .t2 S))
    (fun k s hk h => save_step (s₀.write .t2 S) (by rw [h0]; exact hin) (by rw [h0]; exact hal) hk h)
    13 (Nat.le_refl _) (s₀.write .t2 S)
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_
  have hf := h.frame
  have hsv := h.saved
  rw [h0] at hf hsv
  have hw : s.gpr .t2 = S := by rw [h.gpr, h0]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 0 by decide),
    BitVec.ofInt_ofNat, add_ofNat_zero, Option.some.injEq, exists_eq_left', hw]
  have k1 : Keep [.t2] s₀ (s₀.write .t2 S) := VG.Proof.Bignum.RISCV64.Keep.write _ _ _
  refine ⟨⟨fun r hr => ?_, h.rd, h.wr⟩, h.sp, gpr_write_self _ _ _, hf, fun i hi => ?_⟩
  · have hr6 : r ≠ .s6 := fun e => hr (by simp [e])
    have hr0 : r ∉ [Reg.t2] := fun e => hr (by simp_all)
    rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e hr6, h.gpr, k1.gpr hr0]
  · rw [mem_write, hsv i hi, gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_ne_t2 i hi)]

/-- `save`, from a state with the working space `S` in `t2`. -/
theorem saveT2_ok (s₀ : State) {S : Addr} (h2 : s₀.gpr .t2 = S)
    (hin : ∀ i < 13, InRegions s₀.wr (off (savW S) (8 * i)) 8)
    (hal : ∀ i < 13, (off (savW S) (8 * i)).toNat % 8 = 0) :
    WP isa (.block (save .t2)) s₀ (Saved s₀ S) := by
  rw [save]
  subst h2
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀)
    (fun k s hk h => save_step s₀ hin hal hk h) 13 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
  have hw : s.gpr .t2 = s₀.gpr .t2 := by rw [h.gpr]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 0 by decide),
    BitVec.ofInt_ofNat, add_ofNat_zero, Option.some.injEq, exists_eq_left', hw]
  refine ⟨⟨fun r hr => ?_, h.rd, h.wr⟩, h.sp, gpr_write_self _ _ _, h.frame, fun i hi => ?_⟩
  · have hr6 : r ≠ .s6 := fun e => hr (by simp [e])
    rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e hr6, h.gpr]
  · rw [mem_write]; exact h.saved i hi

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (S : Addr) (v : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  s6 : s.gpr .s6 = S
  restored : ∀ i < n, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 13, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64}
    (hsin : ∀ i < 13, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hal : ∀ i < 13, (off (savW S) (8 * i)).toNat % 8 = 0)
    (hsav : ∀ i < 13, sB.mem.readW (off (savW S) (8 * i)) 64 = v i)
    {n : Nat} (hn : n < 12) {s : State} (h : RI sB S v n s) :
    WP isa (.block [.load .d (saved n) .s6 (saveOff n)]) s (RI sB S v (n + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .s6 + BitVec.ofNat 64 (saveOff n)) 8 := by
    rw [h.rd, h.wr, h.s6, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin n (by omega_using [hn])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have ha : (s.gpr .s6 + BitVec.ofNat 64 (saveOff n)).toNat % 8 = 0 := by
    rw [h.s6, saveOff_eq]; exact hal n (by omega_using [hn])
  have hv : s.mem.readW (S + BitVec.ofNat 64 (saveOff n)) 64 = v n := by
    rw [h.mem, saveOff_eq]; exact hsav n (by omega_using [hn])
  have hn6 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show saveOff n < 2048 by unfold saveOff; omega_using [hn]) ha hin,
    Option.some.injEq, exists_eq_left', h.s6, hv]
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn6)]; exact h.s6
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e =>
        absurd (saved_inj i (by omega_using [hi, hn]) n (by omega_using [hn]) e) (by omega_using [hi])
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr n (by omega_using [hn]))]
    exact h.others r hr

/-- `restore`, from a state whose saved words, through `s6`, hold `v`. -/
theorem restore_ok (sB : State) {S : Addr} {v : Nat → BitVec 64} (hw : sB.gpr .s6 = S)
    (hsin : ∀ i < 13, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hal : ∀ i < 13, (off (savW S) (8 * i)).toNat % 8 = 0)
    (hsav : ∀ i < 13, sB.mem.readW (off (savW S) (8 * i)) 64 = v i) :
    WP isa (.block restore) sB fun s =>
      (∀ i < 13, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 13, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp := by
  rw [restore]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB S v)
    (fun k s hk h => restore_step sB hsin hal hsav hk h) 12 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .s6 + BitVec.ofNat 64 (saveOff 12)) 8 := by
    rw [h.rd, h.wr, h.s6, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin 12 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have ha : (s.gpr .s6 + BitVec.ofNat 64 (saveOff 12)).toNat % 8 = 0 := by
    rw [h.s6, saveOff_eq]; exact hal 12 (by decide)
  have hv : s.mem.readW (S + BitVec.ofNat 64 (saveOff 12)) 64 = v 12 := by
    rw [h.mem, saveOff_eq]; exact hsav 12 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show saveOff 12 < 2048 by decide) ha hin,
    Option.some.injEq, exists_eq_left', h.s6, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_iff.mpr fun e => absurd e (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_12, ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_12 ▸ hr 12 (by decide))]
    exact h.others r hr

end VG.Proof.Dsa.RISCV64
