module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Domain
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH's domain operations on PPC64LE: saving and restoring the nonvolatile registers

As `Proof/MillerRabin/PPC64LE/Save.lean`: `save ws` stores `r14`–`r31` in
the working space's header words 14–31 (144 bytes at `S + 112`, `S` in
`ws`), and copies `S` into `r23`; `restore` loads them back through `r23`,
`r23` last.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain

/-- The saved registers' words of the working space at `S`. -/
abbrev savW (S : Addr) : Addr := S + BitVec.ofNat 64 112

/-- Their 144 bytes. -/
abbrev savR (S : Addr) : Region := ⟨savW S, 144⟩

theorem saveOff_eq (S : Addr) (i : Nat) : S + BitVec.ofNat 64 (saveOff i) = off (savW S) (8 * i) := by
  rw [off, Offset.add_add]; simp only [saveOff]

theorem saved_inj : ∀ i < 18, ∀ j < 18, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 17, saved i ≠ .r23 := by decide

theorem saved_17 : saved 17 = .r23 := rfl

theorem sav_contains (S : Addr) {i : Nat} (hi : i < 18) : (savR S).Contains (off (savW S) (8 * i)) 8 :=
  Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

theorem sav_sep (S : Addr) {i j : Nat} (hi : i < 18) (hj : j < 18) (h : i ≠ j) :
    Mem.Sep (off (savW S) (8 * i)) 8 (off (savW S) (8 * j)) 8 :=
  Offset.sep _ (by omega_using [hi, hj, h]) (by omega_using [hi]) (by omega_using [hj])

/-- The first `n` registers are saved. -/
structure SI (ws : Reg) (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  frame : Frame [savR (s₀.gpr ws)] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off (savW (s₀.gpr ws)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step {ws : Reg} (hws : ws ≠ .r0) (s₀ : State) (hin : savR (s₀.gpr ws) ∈ s₀.wr) {n : Nat}
    (hn : n < 18) {s : State} (h : SI ws s₀ n s) :
    WP isa (.block [.store .d (saved n) ws (saveOff n)]) s (SI ws s₀ (n + 1)) := by
  have hw : s.gpr ws = s₀.gpr ws := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr ws + BitVec.ofNat 64 (saveOff n)) 8 := by
    rw [h.wr, hw, saveOff_eq]; exact ⟨_, hin, sav_contains _ hn⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d hws (show saveOff n < 2 ^ 15 ∧ (saveOff n) % 4 = 0 by simp only [saveOff]; omega_using [hn])
      hout, Option.some.injEq, exists_eq_left', hw, saveOff_eq]
  refine ⟨h.gpr, h.rd, h.wr, h.sp, h.lr,
    h.frame.writeW (List.mem_singleton_self _) _ (sav_contains _ hn), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_using [hi, hn]) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The state after `save ws`. -/
structure Saved (ws : Reg) (s₀ : State) (s : State) : Prop where
  keep : Keep [.r23] s₀ s
  r23 : s.gpr .r23 = s₀.gpr ws
  frame : Frame [savR (s₀.gpr ws)] s₀.mem s.mem
  saved : ∀ i < 18, s.mem.readW (off (savW (s₀.gpr ws)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_ok {ws : Reg} (hws : ws ≠ .r0) (s₀ : State) (hin : savR (s₀.gpr ws) ∈ s₀.wr) :
    WP isa (.block (save ws)) s₀ (Saved ws s₀) := by
  rw [save]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI ws s₀)
    (fun k s hk h => save_step hws s₀ hin hk h) 18 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
  have hw : s.gpr ws = s₀.gpr ws := by rw [h.gpr]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi hws
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

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64} (hsin : savR S ∈ sB.wr)
    (hsav : ∀ i < 18, sB.mem.readW (off (savW S) (8 * i)) 64 = v i)
    {n : Nat} (hn : n < 17) {s : State} (h : RI sB S v n s) :
    WP isa (.block [.load .d (saved n) .r23 (saveOff n)]) s (RI sB S v (n + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 (saveOff n)) 8 := by
    rw [h.rd, h.wr, h.r23, saveOff_eq]
    exact ⟨_, List.mem_append_right _ hsin, sav_contains _ (by omega_using [hn])⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 (saveOff n)) 64 = v n := by
    rw [h.mem, saveOff_eq]; exact hsav n (by omega_using [hn])
  have hn23 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) (show saveOff n < 2 ^ 15 ∧ (saveOff n) % 4 = 0 by
      simp only [saveOff]; omega_using [hn]) hin, Option.some.injEq, exists_eq_left', h.r23, hv]
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

/-- `restore`, from a state whose saved words, at `r23`, hold `v`. -/
theorem restore_ok (sB : State) {S : Addr} {v : Nat → BitVec 64} (hw : sB.gpr .r23 = S)
    (hsin : savR S ∈ sB.wr) (hsav : ∀ i < 18, sB.mem.readW (off (savW S) (8 * i)) 64 = v i) :
    WP isa (.block restore) sB fun s =>
      (∀ i < 18, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 18, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp ∧ s.lr = sB.lr := by
  rw [restore]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB S v)
    (fun k s hk h => restore_step sB hsin hsav hk h) 17 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 (saveOff 17)) 8 := by
    rw [h.rd, h.wr, h.r23, saveOff_eq]
    exact ⟨_, List.mem_append_right _ hsin, sav_contains _ (i := 17) (by decide)⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 (saveOff 17)) 64 = v 17 := by
    rw [h.mem, saveOff_eq]; exact hsav 17 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) (show saveOff 17 < 2 ^ 15 ∧ saveOff 17 % 4 = 0 by decide) hin,
    Option.some.injEq, exists_eq_left', h.r23, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_iff.mpr fun e => absurd e (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_17, ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_17 ▸ hr 17 (by decide))]
    exact h.others r hr

end VG.Proof.Ffdh.PPC64LE.Domain
