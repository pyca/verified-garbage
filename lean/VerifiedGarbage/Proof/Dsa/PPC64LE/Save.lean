module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on PPC64LE: saving and restoring the nonvolatile registers

`save .r11` stores `r14`–`r31` in the P space's header words 14–31 (at
`r11`) and copies its address into `r21`; `restore` loads them back through
`r21`, `r21` last. (`Proof/Bignum/PPC64LE/PubSave.lean`'s proofs, for this
layout.)
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- The saved registers' words, 144 bytes. -/
abbrev savR (w : Addr) : Region := ⟨w, 144⟩

theorem saved_inj : ∀ i < 18, ∀ j < 18, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 17, saved i ≠ .r21 := by decide

theorem saved_17 : saved 17 = .r21 := rfl

theorem sav_contains (w : Addr) {i : Nat} (hi : i < 18) : (savR w).Contains (off w (8 * i)) 8 :=
  Offset.contains_base w (by omega_using [hi]) (by omega_using [hi])

theorem sav_sep (w : Addr) {i j : Nat} (hi : i < 18) (hj : j < 18) (h : i ≠ j) :
    Mem.Sep (off w (8 * i)) 8 (off w (8 * j)) 8 :=
  Offset.sep w (by omega_using [hi, hj, h]) (by omega_using [hi]) (by omega_using [hj])

/-- The saved registers' words of the working space at `S`. -/
abbrev savW (S : Addr) : Addr := S + BitVec.ofNat 64 112

theorem saveOff_eq (S : Addr) (i : Nat) : S + BitVec.ofNat 64 (112 + 8 * i) = off (savW S) (8 * i) := by
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

theorem save_step (s₀ : State) (hin : ∀ i < 18, InRegions s₀.wr (off (savW (s₀.gpr .r11)) (8 * i)) 8)
    {n : Nat} (hn : n < 18) {s : State}
    (h : SI s₀ n s) : WP isa (.block [.store .d (saved n) .r11 (saveOff n)]) s (SI s₀ (n + 1)) := by
  simp only [saveOff]
  have hw : s.gpr .r11 = s₀.gpr .r11 := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 ((112 + 8 * n))) 8 := by
    rw [h.wr, hw, saveOff_eq]; exact hin n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show Reg.r11 ≠ .r0 by decide) (show 112 + 8 * n < 2 ^ 15 ∧ (112 + 8 * n) % 4 = 0 by
      omega_using [hn]) hout, Option.some.injEq, exists_eq_left', hw, saveOff_eq]
  refine ⟨h.gpr, h.rd, h.wr, h.sp, h.lr,
    h.frame.writeW (List.mem_singleton_self _) _ (sav_contains _ hn), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_using [hi, hn]) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The state after `save`. -/
structure Saved (s₀ : State) (s : State) : Prop where
  keep : Keep [.r21] s₀ s
  r21 : s.gpr .r21 = s₀.gpr .r11
  frame : Frame [savR (savW (s₀.gpr .r11))] s₀.mem s.mem
  saved : ∀ i < 18, s.mem.readW (off (savW (s₀.gpr .r11)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_ok (s₀ : State) (hin : ∀ i < 18, InRegions s₀.wr (off (savW (s₀.gpr .r11)) (8 * i)) 8) :
    WP isa (.block (save .r11)) s₀ (Saved s₀) := by
  rw [save]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀)
    (fun k s hk h => save_step s₀ hin hk h) 18 (Nat.le_refl _) s₀
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
  r21 : s.gpr .r21 = S
  restored : ∀ i < n, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 18, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  lr : s.lr = sB.lr

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64}
    (hsin : ∀ i < 18, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 18, sB.mem.readW (off (savW S) (8 * i)) 64 = v i)
    {n : Nat} (hn : n < 17) {s : State} (h : RI sB S v n s) :
    WP isa (.block [.load .d (saved n) .r21 (saveOff n)]) s (RI sB S v (n + 1)) := by
  simp only [saveOff]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r21 + BitVec.ofNat 64 ((112 + 8 * n))) 8 := by
    rw [h.rd, h.wr, h.r21, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin n (by omega_using [hn])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 ((112 + 8 * n))) 64 = v n := by
    rw [h.mem, saveOff_eq]; exact hsav n (by omega_using [hn])
  have hn23 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r21 ≠ .r0 by decide) (show 112 + 8 * n < 2 ^ 15 ∧ (112 + 8 * n) % 4 = 0 by
      omega_using [hn]) hin, Option.some.injEq, exists_eq_left', h.r21, hv]
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn23)]; exact h.r21
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e =>
        absurd (saved_inj i (by omega_using [hi, hn]) n (by omega_using [hn]) e) (by omega_using [hi])
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr n (by omega_using [hn]))]
    exact h.others r hr

/-- `restore`, from a state whose saved words, through `r21`, hold `v`. -/
theorem restore_ok (sB : State) {S : Addr} {v : Nat → BitVec 64} (hw : sB.gpr .r21 = S)
    (hsin : ∀ i < 18, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 18, sB.mem.readW (off (savW S) (8 * i)) 64 = v i) :
    WP isa (.block VG.Impl.Dsa.PPC64LE.restore) sB fun s =>
      (∀ i < 18, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 18, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp ∧ s.lr = sB.lr := by
  rw [VG.Impl.Dsa.PPC64LE.restore]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB S v)
    (fun k s hk h => restore_step sB hsin hsav hk h) 17 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r21 + BitVec.ofNat 64 ((112 + 8 * 17))) 8 := by
    rw [h.rd, h.wr, h.r21, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin 17 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 ((112 + 8 * 17))) 64 = v 17 := by
    rw [h.mem, saveOff_eq]; exact hsav 17 (by decide)
  apply WP.of_runBlock
  simp only [saveOff, runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r21 ≠ .r0 by decide) (show 112 + 8 * 17 < 2 ^ 15 ∧ (112 + 8 * 17) % 4 = 0 by decide) hin,
    Option.some.injEq, exists_eq_left', h.r21, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_iff.mpr fun e => absurd e (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_17, ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_17 ▸ hr 17 (by decide))]
    exact h.others r hr

end VG.Proof.Dsa.PPC64LE
