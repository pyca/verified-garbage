module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on PPC64LE: saving and restoring

`save` loads the working space's address from the stack (its ninth argument
there) into `r11`, stores the 18 nonvolatile registers it uses from byte 112
of its header and copies its address into `r23` (`save_ok`); `restore` loads
them back through `r23`, `r23` last (`restore_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE.Crt

/-- The saved registers' words, 144 bytes. -/
abbrev savR (w : Addr) : Region := ⟨w, 144⟩

theorem saved_inj : ∀ i < 18, ∀ j < 18, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 17, saved i ≠ .r23 := by decide

theorem saved_17 : saved 17 = .r23 := rfl

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
    (h : SI s₀ n s) : WP isa (.block [.store .d (saved n) .r11 (savOff n)]) s (SI s₀ (n + 1)) := by
  simp only [savOff]
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
  keep : Keep [.r23] s₀ s
  r23 : s.gpr .r23 = s₀.gpr .r11
  frame : Frame [savR (savW (s₀.gpr .r11))] s₀.mem s.mem
  saved : ∀ i < 18, s.mem.readW (off (savW (s₀.gpr .r11)) (8 * i)) 64 = s₀.gpr (saved i)

theorem saveRegs_ok (s₀ : State) (hin : ∀ i < 18, InRegions s₀.wr (off (savW (s₀.gpr .r11)) (8 * i)) 8) :
    WP isa (.block ((List.range 18).flatMap (fun i => [.store .d (saved i) .r11 (savOff i)]) ++
      [.addi .r23 .r11 0])) s₀ (Saved s₀) := by
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
  r23 : s.gpr .r23 = S
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
    WP isa (.block [.load .d (saved n) .r23 (savOff n)]) s (RI sB S v (n + 1)) := by
  simp only [savOff]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 ((112 + 8 * n))) 8 := by
    rw [h.rd, h.wr, h.r23, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin n (by omega_using [hn])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 ((112 + 8 * n))) 64 = v n := by
    rw [h.mem, saveOff_eq]; exact hsav n (by omega_using [hn])
  have hn23 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) (show 112 + 8 * n < 2 ^ 15 ∧ (112 + 8 * n) % 4 = 0 by
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
    (hsin : ∀ i < 18, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 18, sB.mem.readW (off (savW S) (8 * i)) 64 = v i) :
    WP isa (.block VG.Impl.Bignum.PPC64LE.Crt.restore) sB fun s =>
      (∀ i < 18, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 18, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp ∧ s.lr = sB.lr := by
  rw [VG.Impl.Bignum.PPC64LE.Crt.restore, show savOff 17 = 112 + 8 * 17 from rfl]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB S v)
    (fun k s hk h => restore_step sB hsin hsav hk h) 17 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 ((112 + 8 * 17))) 8 := by
    rw [h.rd, h.wr, h.r23, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin 17 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 ((112 + 8 * 17))) 64 = v 17 := by
    rw [h.mem, saveOff_eq]; exact hsav 17 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) (show 112 + 8 * 17 < 2 ^ 15 ∧ (112 + 8 * 17) % 4 = 0 by decide) hin,
    Option.some.injEq, exists_eq_left', h.r23, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_iff.mpr fun e => absurd e (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_17, ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_17 ▸ hr 17 (by decide))]
    exact h.others r hr

/-- The ninth argument on the stack into `r11`. -/
theorem loadS_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 8) 8) :
    WP isa (.block [.addSp .r11 160, .load .d .r11 .r11 0]) s fun t =>
      (t.gpr .r11 = stackArg s 8 ∧ t.mem = s.mem ∧ t.sp = s.sp) ∧ Keep [.r11] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd] at h
  have ea : exec (.addSp .r11 160) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 160)) := by
    simp [exec]
  prun [ea, h, BitVec.add_zero]
  rfl

/-- `save`: the working space from the stack, the registers saved there. -/
theorem save_ok (s₀ : State) (h : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 8) 8)
    (hin : ∀ i < 18, InRegions s₀.wr (off (savW (stackArg s₀ 8)) (8 * i)) 8) :
    WP isa (.block save) s₀ fun t => ∃ s₁ : State, s₁.gpr .r11 = stackArg s₀ 8 ∧ s₁.mem = s₀.mem ∧
      Keep [.r11] s₀ s₁ ∧ Saved s₁ t := by
  rw [save, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadS_ok s₀ h) fun s₁ ⟨⟨a11, m1, _⟩, k1⟩ => ?_
  refine WP.mono (saveRegs_ok s₁ (fun i hi => by rw [k1.wr, a11]; exact hin i hi)) fun t ht =>
    ⟨s₁, a11, m1, k1, ht⟩

end VG.Proof.Bignum.PPC64LE.Crt
