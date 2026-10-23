module

public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Setup
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Poly1305 on PPC64LE: saving and restoring the nonvolatile registers

`save w` stores `r14`–`r21` in the first 64 bytes of the working space at
`w`, and copies `w` into `r21`; `restore` loads `r14`–`r20` back through
`r21`, then `r21` itself.
-/

@[expose] public section

namespace VG.Proof.Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.Poly1305.PPC64LE

/-- The working space, 128 bytes: the registers are saved in its first 64. -/
abbrev savR (w : Addr) : Region := ⟨w, 128⟩

theorem saved_inj : ∀ i < 8, ∀ j < 8, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 7, saved i ≠ .r21 := by decide

theorem saved_7 : saved 7 = .r21 := rfl

theorem sav_contains (w : Addr) {i : Nat} (hi : i < 8) : (savR w).Contains (off w (8 * i)) 8 :=
  contains_off (by omega_using [hi]) (by omega_using [hi])

theorem sav_sep (w : Addr) {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) :
    Mem.Sep (off w (8 * i)) 8 (off w (8 * j)) 8 :=
  sep_off w (by omega_using [hi]) (by omega_using [hj]) (by decide) (by decide)
    (by omega_using [hi, hj, h])

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (w : Reg) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [savR (s₀.gpr w)] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off (s₀.gpr w) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step (s₀ : State) {w : Reg} (hw0 : w ≠ .r0) (hin : savR (s₀.gpr w) ∈ s₀.wr)
    {n : Nat} (hn : n < 8) {s : State} (h : SI s₀ w n s) :
    WP isa (.block [.store .d (saved n) w (8 * n)]) s (SI s₀ w (n + 1)) := by
  have hw : s.gpr w = s₀.gpr w := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr w + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [h.wr, hw]; exact ⟨_, hin, sav_contains _ hn⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d hw0 (show 8 * n < 2 ^ 15 ∧ (8 * n) % 4 = 0 by omega_using [hn]) hout,
    Option.some.injEq, exists_eq_left', hw]
  refine ⟨h.gpr, h.rd, h.wr, h.frame.writeW (List.mem_singleton_self _) _ (sav_contains _ hn),
    fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_using [hi, hn]) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The state after `save w`. -/
structure Saved (s₀ : State) (w : Reg) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r21 → s.gpr r = s₀.gpr r
  r21 : s.gpr .r21 = s₀.gpr w
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [savR (s₀.gpr w)] s₀.mem s.mem
  saved : ∀ i < 8, s.mem.readW (off (s₀.gpr w) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_ok (s₀ : State) {w : Reg} (hw0 : w ≠ .r0) (hin : savR (s₀.gpr w) ∈ s₀.wr) :
    WP isa (.block (save w)) s₀ (Saved s₀ w) := by
  rw [save]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀ w)
    (fun k s hk h => save_step s₀ hw0 hin hk h) 8 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
  have hw : s.gpr w = s₀.gpr w := by rw [h.gpr]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi hw0 (show 0 < 2 ^ 15 by decide),
    add_ofNat_zero, Option.some.injEq, exists_eq_left', hw]
  refine ⟨fun r hr => ?_, ?_, h.rd, h.wr, h.frame, h.saved⟩
  · rw [write_gpr, ite_eq_right hr, h.gpr]
  · rw [write_gpr, ite_eq_left rfl]

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (w : Addr) (v : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  r21 : s.gpr .r21 = w
  restored : ∀ i < n, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 8, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem restore_step (sB : State) {w : Addr} {v : Nat → BitVec 64} (hsin : savR w ∈ sB.wr)
    (hsav : ∀ i < 8, sB.mem.readW (off w (8 * i)) 64 = v i)
    {n : Nat} (hn : n < 7) {s : State} (h : RI sB w v n s) :
    WP isa (.block [.load .d (saved n) .r21 (8 * n)]) s (RI sB w v (n + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r21 + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [h.rd, h.wr, h.r21]; exact ⟨_, List.mem_append_right _ hsin, sav_contains _ (by omega_using [hn])⟩
  have hv : s.mem.readW (w + BitVec.ofNat 64 (8 * n)) 64 = v n := by
    rw [h.mem]; exact hsav n (by omega_using [hn])
  have hn21 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r21 ≠ .r0 by decide) (show 8 * n < 2 ^ 15 ∧ (8 * n) % 4 = 0 by
      omega_using [hn]) hin, Option.some.injEq, exists_eq_left', h.r21, hv]
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · rw [write_gpr, ite_eq_right (Ne.symm hn21)]; exact h.r21
  · rw [write_gpr]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e =>
        absurd (saved_inj i (by omega_using [hi, hn]) n (by omega_using [hn]) e) (by omega_using [hi])
      rw [ite_eq_right e]; exact h.restored i hi
    · rw [ite_eq_left rfl]
  · rw [write_gpr, ite_eq_right (hr n (by omega_using [hn]))]; exact h.others r hr

/-- `restore`, from a state whose working space, at `r21`, holds `v`. -/
theorem restore_ok (sB : State) {w : Addr} {v : Nat → BitVec 64} (hw : sB.gpr .r21 = w)
    (hsin : savR w ∈ sB.wr) (hsav : ∀ i < 8, sB.mem.readW (off w (8 * i)) 64 = v i) :
    WP isa (.block restore) sB fun s =>
      (∀ i < 8, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 8, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr := by
  rw [restore]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB w v)
    (fun k s hk h => restore_step sB hsin hsav hk h) 7 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r21 + BitVec.ofNat 64 56) 8 := by
    rw [h.rd, h.wr, h.r21]; exact ⟨_, List.mem_append_right _ hsin, sav_contains _ (i := 7) (by decide)⟩
  have hv : s.mem.readW (w + BitVec.ofNat 64 56) 64 = v 7 := by
    rw [h.mem]; exact hsav 7 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r21 ≠ .r0 by decide) (show 56 < 2 ^ 15 ∧ 56 % 4 = 0 by decide) hin,
    Option.some.injEq, exists_eq_left', h.r21, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · rw [write_gpr]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_7, ite_eq_left rfl]
  · rw [write_gpr, ite_eq_right (saved_7 ▸ hr 7 (by decide))]; exact h.others r hr

end VG.Proof.Poly1305.PPC64LE
