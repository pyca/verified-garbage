module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA public-key operation on PPC64LE: saving and restoring

`save` loads the working space's address from the stack into `r11`
(`load_ok`), stores `r14`–`r29` in its header words 16–31 and copies its
address into `r23`; `restore` loads them back through `r23`, `r23` last.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE.PublicChecked

/-- The saved registers' words, 128 bytes. -/
abbrev savR (w : Addr) : Region := ⟨w, 128⟩

theorem saved_inj : ∀ i < 16, ∀ j < 16, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 15, saved i ≠ .r23 := by decide

theorem saved_15 : saved 15 = .r23 := rfl

theorem sav_contains (w : Addr) {i : Nat} (hi : i < 16) : (savR w).Contains (off w (8 * i)) 8 :=
  Offset.contains_base w (by omega_using [hi]) (by omega_using [hi])

theorem sav_sep (w : Addr) {i j : Nat} (hi : i < 16) (hj : j < 16) (h : i ≠ j) :
    Mem.Sep (off w (8 * i)) 8 (off w (8 * j)) 8 :=
  Offset.sep w (by omega_using [hi, hj, h]) (by omega_using [hi]) (by omega_using [hj])

/-- The saved registers' words of the working space at `S`. -/
abbrev savW (S : Addr) : Addr := S + BitVec.ofNat 64 128

theorem saveOff_eq (S : Addr) (i : Nat) : S + BitVec.ofNat 64 (128 + 8 * i) = off (savW S) (8 * i) := by
  rw [off, Offset.add_add]

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  frame : Frame [savR (savW (s₀.gpr .r11))] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off (savW (s₀.gpr .r11)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step (s₀ : State) (hin : ∀ i < 16, InRegions s₀.wr (off (savW (s₀.gpr .r11)) (8 * i)) 8)
    {n : Nat} (hn : n < 16) {s : State}
    (h : SI s₀ n s) : WP isa (.block [.store .d (saved n) .r11 ((128 + 8 * n))]) s (SI s₀ (n + 1)) := by
  have hw : s.gpr .r11 = s₀.gpr .r11 := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 ((128 + 8 * n))) 8 := by
    rw [h.wr, hw, saveOff_eq]; exact hin n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show Reg.r11 ≠ .r0 by decide) (show 128 + 8 * n < 2 ^ 15 ∧ (128 + 8 * n) % 4 = 0 by
      omega_using [hn]) hout, Option.some.injEq, exists_eq_left', hw, saveOff_eq]
  refine ⟨h.gpr, h.rd, h.wr, h.sp, h.lr,
    h.frame.writeW (List.mem_singleton_self _) _ (sav_contains _ hn), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_using [hi, hn]) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The state after `save`. -/
structure Saved (s₀ : State) (s : State) : Prop where
  keep : Keep [.r23] s₀ s
  r23 : s.gpr .r23 = s₀.gpr .r11
  frame : Frame [savR (savW (s₀.gpr .r11))] s₀.mem s.mem
  saved : ∀ i < 16, s.mem.readW (off (savW (s₀.gpr .r11)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_ok (s₀ : State) (hin : ∀ i < 16, InRegions s₀.wr (off (savW (s₀.gpr .r11)) (8 * i)) 8) :
    WP isa (.block saveRegs) s₀ (Saved s₀) := by
  rw [saveRegs]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀)
    (fun k s hk h => save_step s₀ hin hk h) 16 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
  have hw : s.gpr .r11 = s₀.gpr .r11 := by rw [h.gpr]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (show Reg.r11 ≠ .r0 by decide)
    (show 0 < 2 ^ 15 by decide), BitVec.add_zero, Option.some.injEq, exists_eq_left', hw]
  refine ⟨⟨fun r hr => ?_, h.rd, h.wr, h.sp, h.lr⟩, ?_, h.frame, h.saved⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e fun e => hr (by simp [e]), h.gpr]
  · rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e]

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (S : Addr) (v : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  r23 : s.gpr .r23 = S
  restored : ∀ i < n, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 16, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  lr : s.lr = sB.lr

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64}
    (hsin : ∀ i < 16, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 16, sB.mem.readW (off (savW S) (8 * i)) 64 = v i)
    {n : Nat} (hn : n < 15) {s : State} (h : RI sB S v n s) :
    WP isa (.block [.load .d (saved n) .r23 ((128 + 8 * n))]) s (RI sB S v (n + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 ((128 + 8 * n))) 8 := by
    rw [h.rd, h.wr, h.r23, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin n (by omega_using [hn])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 ((128 + 8 * n))) 64 = v n := by
    rw [h.mem, saveOff_eq]; exact hsav n (by omega_using [hn])
  have hn23 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) (show 128 + 8 * n < 2 ^ 15 ∧ (128 + 8 * n) % 4 = 0 by
      omega_using [hn]) hin, Option.some.injEq, exists_eq_left', h.r23, hv]
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn23)]; exact h.r23
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e =>
        absurd (saved_inj i (by omega_using [hi, hn]) n (by omega_using [hn]) e) (by omega_using [hi])
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr n (by omega_using [hn]))]
    exact h.others r hr

/-- `restore`, from a state whose saved words, through `r21`, hold `v`. -/
theorem restore_ok (sB : State) {S : Addr} {v : Nat → BitVec 64} (hw : sB.gpr .r23 = S)
    (hsin : ∀ i < 16, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 16, sB.mem.readW (off (savW S) (8 * i)) 64 = v i) :
    WP isa (.block VG.Impl.Bignum.PPC64LE.PublicChecked.restore) sB fun s =>
      (∀ i < 16, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 16, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp ∧ s.lr = sB.lr := by
  rw [VG.Impl.Bignum.PPC64LE.PublicChecked.restore]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB S v)
    (fun k s hk h => restore_step sB hsin hsav hk h) 15 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 ((128 + 8 * 15))) 8 := by
    rw [h.rd, h.wr, h.r23, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin 15 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 ((128 + 8 * 15))) 64 = v 15 := by
    rw [h.mem, saveOff_eq]; exact hsav 15 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) (show 128 + 8 * 15 < 2 ^ 15 ∧ (128 + 8 * 15) % 4 = 0 by decide) hin,
    Option.some.injEq, exists_eq_left', h.r23, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_iff.mpr fun e => absurd e (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_15, ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_15 ▸ hr 15 (by decide))]
    exact h.others r hr

/-- `loadS`: the first argument on the stack into `r11`. -/
theorem loadS_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) :
    WP isa (.block loadS) s fun t => (t.gpr .r11 = stackArg s 0 ∧ t.mem = s.mem ∧ t.sp = s.sp) ∧
      Keep [.r11] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold loadS
  simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd] at h
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  prun [ea, h, BitVec.add_zero]
  rfl

end VG.Proof.Bignum.PPC64LE.Pub
