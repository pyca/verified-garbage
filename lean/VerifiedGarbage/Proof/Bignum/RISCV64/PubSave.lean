module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.PublicChecked
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA public-key operation on RISC-V: saving, restoring and setting up

`loadS` reads the working space's address from the stack into `t0`;
`saveRegs` stores `s0`–`s11` (`saved`) in its header words 16–27 and copies
its address into `s6`; `restore` loads them back through `s6`, `s6` last.
`setup_ok`: `out`, `k`, `w`, the arrays' size and array 0's base in their
registers.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pub

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64 (Scr off_add add_ofNat_zero)
open VG.Proof.Bignum (slot)

/-- The saved registers' words, 96 bytes. -/
abbrev savR (w : Addr) : Region := ⟨w, 96⟩

theorem saved_inj : ∀ i < 12, ∀ j < 12, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 11, saved i ≠ .s6 := by decide

theorem saved_11 : saved 11 = .s6 := rfl

theorem sav_contains (w : Addr) {i : Nat} (hi : i < 12) : (savR w).Contains (off w (8 * i)) 8 :=
  Offset.contains_base w (by omega_using [hi]) (by omega_using [hi])

theorem sav_sep (w : Addr) {i j : Nat} (hi : i < 12) (hj : j < 12) (h : i ≠ j) :
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
  frame : Frame [savR (savW (s₀.gpr .t0))] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off (savW (s₀.gpr .t0)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step (s₀ : State) (hin : ∀ i < 12, InRegions s₀.wr (off (savW (s₀.gpr .t0)) (8 * i)) 8)
    (hal : ∀ i < 12, (off (savW (s₀.gpr .t0)) (8 * i)).toNat % 8 = 0)
    {n : Nat} (hn : n < 12) {s : State}
    (h : SI s₀ n s) : WP isa (.block [.store .d (saved n) .t0 (128 + 8 * n)]) s (SI s₀ (n + 1)) := by
  have hw : s.gpr .t0 = s₀.gpr .t0 := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .t0 + BitVec.ofNat 64 (128 + 8 * n)) 8 := by
    rw [h.wr, hw, saveOff_eq]; exact hin n hn
  have ha : (s.gpr .t0 + BitVec.ofNat 64 (128 + 8 * n)).toNat % 8 = 0 := by
    rw [hw, saveOff_eq]; exact hal n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show 128 + 8 * n < 2048 by omega_using [hn]) ha hout,
    Option.some.injEq, exists_eq_left', hw, saveOff_eq]
  refine ⟨h.gpr, h.rd, h.wr, h.sp,
    h.frame.writeW (List.mem_singleton_self _) _ (sav_contains _ hn), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_using [hi, hn]) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The state after `save`. -/
structure Saved (s₀ : State) (s : State) : Prop where
  keep : Keep [.s6] s₀ s
  sp : s.sp = s₀.sp
  s6 : s.gpr .s6 = s₀.gpr .t0
  frame : Frame [savR (savW (s₀.gpr .t0))] s₀.mem s.mem
  saved : ∀ i < 12, s.mem.readW (off (savW (s₀.gpr .t0)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_ok (s₀ : State) (hin : ∀ i < 12, InRegions s₀.wr (off (savW (s₀.gpr .t0)) (8 * i)) 8)
    (hal : ∀ i < 12, (off (savW (s₀.gpr .t0)) (8 * i)).toNat % 8 = 0) :
    WP isa (.block saveRegs) s₀ (Saved s₀) := by
  rw [saveRegs]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀)
    (fun k s hk h => save_step s₀ hin hal hk h) 12 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
  have hw : s.gpr .t0 = s₀.gpr .t0 := by rw [h.gpr]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 0 by decide),
    BitVec.ofInt_ofNat, add_ofNat_zero, Option.some.injEq, exists_eq_left', hw]
  refine ⟨⟨fun r hr => ?_, h.rd, h.wr⟩, h.sp, ?_, h.frame, h.saved⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e fun e => hr (by simp [e]), h.gpr]
  · rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e]

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (S : Addr) (v : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  s6 : s.gpr .s6 = S
  restored : ∀ i < n, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 12, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64}
    (hsin : ∀ i < 12, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hal : ∀ i < 12, (off (savW S) (8 * i)).toNat % 8 = 0)
    (hsav : ∀ i < 12, sB.mem.readW (off (savW S) (8 * i)) 64 = v i)
    {n : Nat} (hn : n < 11) {s : State} (h : RI sB S v n s) :
    WP isa (.block [.load .d (saved n) .s6 (128 + 8 * n)]) s (RI sB S v (n + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .s6 + BitVec.ofNat 64 (128 + 8 * n)) 8 := by
    rw [h.rd, h.wr, h.s6, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin n (by omega_using [hn])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have ha : (s.gpr .s6 + BitVec.ofNat 64 (128 + 8 * n)).toNat % 8 = 0 := by
    rw [h.s6, saveOff_eq]; exact hal n (by omega_using [hn])
  have hv : s.mem.readW (S + BitVec.ofNat 64 (128 + 8 * n)) 64 = v n := by
    rw [h.mem, saveOff_eq]; exact hsav n (by omega_using [hn])
  have hn6 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show 128 + 8 * n < 2048 by omega_using [hn]) ha hin,
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
    (hsin : ∀ i < 12, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hal : ∀ i < 12, (off (savW S) (8 * i)).toNat % 8 = 0)
    (hsav : ∀ i < 12, sB.mem.readW (off (savW S) (8 * i)) 64 = v i) :
    WP isa (.block PublicChecked.restore) sB fun s =>
      (∀ i < 12, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 12, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp := by
  rw [PublicChecked.restore]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB S v)
    (fun k s hk h => restore_step sB hsin hal hsav hk h) 11 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .s6 + BitVec.ofNat 64 (128 + 8 * 11)) 8 := by
    rw [h.rd, h.wr, h.s6, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin 11 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have ha : (s.gpr .s6 + BitVec.ofNat 64 (128 + 8 * 11)).toNat % 8 = 0 := by
    rw [h.s6, saveOff_eq]; exact hal 11 (by decide)
  have hv : s.mem.readW (S + BitVec.ofNat 64 (128 + 8 * 11)) 64 = v 11 := by
    rw [h.mem, saveOff_eq]; exact hsav 11 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show 128 + 8 * 11 < 2048 by decide) ha hin,
    Option.some.injEq, exists_eq_left', h.s6, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_iff.mpr fun e => absurd e (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_11, ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_11 ▸ hr 11 (by decide))]
    exact h.others r hr

/-! ## The working space's address -/

/-- `loadS`: the first argument on the stack into `t0`. -/
theorem loadS_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8)
    (ha : s.sp.toNat % 8 = 0) :
    WP isa (.block loadS) s fun t => (t.gpr .t0 = stackArg s 0 ∧ t.mem = s.mem ∧ t.sp = s.sp) ∧
      Keep [.t0] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold loadS
  simp only [stackArgAddr, Nat.reduceMul] at h
  have ha' : (s.sp + BitVec.ofNat 64 0).toNat % 8 = 0 := by rw [add_ofNat_zero]; exact ha
  have h' : InRegions (s.rd ++ s.wr) s.sp 8 := by simpa only [add_ofNat_zero] using h
  brun [exec_addSp (show 0 < 2048 by decide), h, h', ha, ha']
  simp [stackArg, stackArgAddr]

/-! ## Setting up -/

theorem ofNat_add7_shr3 (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) :=
  Pre.ofNat_add7_shr3 k hk

/-- `setup`, `out` in `a0`, `k` in `a1` and the working space at `s6`: `out`
in `s10`, `k` in `s11`, `w` in `t0`, an array's size `8 w + 16` in `s5` and
array 0's base in `a7`. -/
theorem setup_ok {s : State} {O S : Addr} {k : Nat} (h10 : s.gpr .a0 = O)
    (h11 : s.gpr .a1 = BitVec.ofNat 64 k) (h6 : s.gpr .s6 = S) (hk' : k ≤ 1024) :
    WP isa (.block setup) s fun t =>
      (t.gpr .s10 = O ∧ t.gpr .s11 = BitVec.ofNat 64 k ∧ t.gpr .t0 = BitVec.ofNat 64 ((k + 7) / 8) ∧
        t.gpr .s5 = BitVec.ofNat 64 (8 * ((k + 7) / 8) + 16) ∧
        t.gpr .a7 = off S (slot ((k + 7) / 8) 0) ∧ t.mem = s.mem) ∧
      Keep [.a7, .s5, .s10, .s11, .t0] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold setup
  brun [h10, h11, h6, add_ofNat_zero, ofNat_add7_shr3 k (by omega_arith), Pre.ofNat_shl3, hdrBytes]
  refine ⟨?_, ?_⟩
  · simp only [BitVec.ofNat_add_ofNat]
  · simp [slot, hdrBytes, off]

end VG.Proof.Bignum.RISCV64.Pub
