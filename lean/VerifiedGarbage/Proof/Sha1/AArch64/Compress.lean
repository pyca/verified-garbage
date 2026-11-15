module

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Sha1.Spec
public import VerifiedGarbage.Impl.Sha1.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha1.AArch64.Lit
public import VerifiedGarbage.Proof.Sha1.StateMem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Sha1.Spec
meta import VerifiedGarbage.Impl.Sha1.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Sha1.AArch64.Lit
meta import VerifiedGarbage.Proof.Sha1.StateMem
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
/-!
# SHA-1 compression function on AArch64: the message schedule and the rounds
-/

@[expose] public section

namespace VG.Proof.Sha1.AArch64

open VG VG.AArch64 VG.Impl.Sha1.AArch64
open VG.Spec.Sha1 (HashValue Word Block K W f)

/-- The working variables `v` are in the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0].setWidth 64 ∧ s.gpr (var t 1) = v[1].setWidth 64 ∧
  s.gpr (var t 2) = v[2].setWidth 64 ∧ s.gpr (var t 3) = v[3].setWidth 64 ∧
  s.gpr (var t 4) = v[4].setWidth 64

/-- The pointers, the count and the registers the ABI requires us to
preserve: never written by the rounds. -/
def pubRegs : List Reg := [.x0, .x1, .x2, .x3, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
  .x26, .x27, .x28, .x30]

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 4) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 4 := by
  simp only [var]; congr 1; omega_using []

/-- The registers of the working variables are all different. -/
theorem round_nodup (t : Nat) : [var t 0, var t 1, var t 2, var t 3, var t 4].Nodup := by
  have h : ∀ c < 5, [work.getD ((0 + 5 - c) % 5) .x4, work.getD ((1 + 5 - c) % 5) .x4,
      work.getD ((2 + 5 - c) % 5) .x4, work.getD ((3 + 5 - c) % 5) .x4,
      work.getD ((4 + 5 - c) % 5) .x4].Nodup := by decide
  exact h (t % 5) (Nat.mod_lt _ (by omega_using []))

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 5 - t % 5) % 5]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem cur_mem (t : Nat) : cur t ∈ sched := by
  unfold cur List.getD
  cases h : sched[t % 3]?
  · simp [sched]
  · exact List.mem_of_getElem? h

/-- A word of the schedule stays in its register for three rounds. -/
theorem cur_add_three (t : Nat) : cur (t + 3) = cur t := by
  simp only [cur]; congr 1; omega_using []

theorem cur_ne {i j : Nat} (h : i % 3 ≠ j % 3) : cur i ≠ cur j := by
  have h' : ∀ a < 3, ∀ b < 3, a ≠ b → sched.getD a .x12 ≠ sched.getD b .x12 := by decide
  exact h' _ (Nat.mod_lt _ (by omega_using [])) _ (Nat.mod_lt _ (by omega_using [])) h

theorem work_ne' : ∀ r ∈ work, r ≠ KR ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs ∧ r ∉ sched := by decide

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ KR ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs ∧ r ∉ sched :=
  work_ne' r h

theorem sched_ne' : ∀ r ∈ sched, r ≠ KR ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ .x3 := by decide

theorem sched_ne {r : Reg} (h : r ∈ sched) : r ≠ KR ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ .x3 :=
  sched_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ KR ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ work ∧ r ∉ sched := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ KR ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ work ∧ r ∉ sched :=
  pubRegs_ne' r h

/-! ## One round -/

/-- `fₜ` as the code computes it. -/
def fval : Fn → Word → Word → Word → Word
  | .ch, x, y, z => (y ^^^ z) &&& x ^^^ z
  | .parity, x, y, z => x ^^^ y ^^^ z
  | .maj, x, y, z => (x ||| y) &&& z ||| x &&& y

theorem f_eq (t : Nat) (x y z : Word) : f t x y z = fval (fn t) x y z := by
  unfold Spec.Sha1.f fn
  (repeat' split) <;> simp only [fval, ch_eq, maj_eq, Spec.Sha1.parity]

theorem fcode_ok (g : Fn) (b c d : Reg) (s : State) (x y z : Word)
    (hbw : b ∈ work) (hcw : c ∈ work) (hdw : d ∈ work)
    (hb : s.gpr b = x.setWidth 64) (hc : s.gpr c = y.setWidth 64) (hd : s.gpr d = z.setWidth 64) :
    WP isa (.block (fcode g b c d)) s fun s' =>
      s'.gpr T1 = (fval g x y z).setWidth 64 ∧ (∀ r, r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨-, b1, -, -⟩ := work_ne hbw
  obtain ⟨-, c1, c2, -⟩ := work_ne hcw
  obtain ⟨-, d1, -, -⟩ := work_ne hdw
  simp only [T1, T2] at b1 c1 c2 d1 ⊢
  apply WP.of_runBlock
  cases g <;>
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self, fcode, T1, T2, runBlock_cons, runStep_some,
    runBlock_nil, exec_logic, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Size.bits,
    b1, c1, d1, hb, hc, hd,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨rfl, fun r h1 h2 => by simp [h1, h2], ?_⟩ <;> trivial

/-- The sum in the order the code accumulates it. -/
theorem sum_comm (r fv z k w : Word) : z + w + k + fv + r = r + fv + z + k + w := by
  ac_rfl

theorem sum_ok (a b e wr : Reg) (s : State) (x y z fv k w : Word)
    (hbw : b ∈ work) (hew : e ∈ work) (hbe : b ≠ e) (hww : wr ∈ sched)
    (ha : s.gpr a = x.setWidth 64) (hb : s.gpr b = y.setWidth 64) (he : s.gpr e = z.setWidth 64)
    (hf : s.gpr T1 = fv.setWidth 64) (hw : s.gpr wr = w.setWidth 64)
    (hk : s.gpr KR = k.setWidth 64) :
    WP isa (.block (sum a b e wr)) s fun s' =>
      s'.gpr e = (x.rotateRight 27 + fv + z + k + w).setWidth 64 ∧
      s'.gpr b = (y.rotateRight 2).setWidth 64 ∧
      (∀ r, r ≠ e → r ≠ b → r ≠ T2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨e0, e1, e2, -⟩ := work_ne hew
  obtain ⟨-, -, b2, -⟩ := work_ne hbw
  obtain ⟨-, -, w2, -⟩ := sched_ne hww
  have heb := hbe.symm
  have e0' := e0.symm; have e1' := e1.symm; have e2' := e2.symm
  simp only [KR, T1, T2] at e0' e1' e2 e2' b2 w2 hf hk ⊢
  apply WP.of_runBlock
  simp only [sum, KR, T1, T2, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, runBlock_cons, runStep_some,
    runBlock_nil, exec_add, exec_ror_w, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, Size.bits,
    e0', e1', e2, e2', b2, w2, hbe, heb, ha, hb, he, hf, hw, hk,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨congrArg _ (sum_comm _ _ _ _ _), trivial, fun r h1 h2 h3 => by simp [h1, h2, h3],
    trivial, trivial, trivial⟩

theorem rotl5 (x : Word) : x.rotateLeft 5 = x.rotateRight 27 := rotateLeft_eq x (by omega_using [])
theorem rotl30 (x : Word) : x.rotateLeft 30 = x.rotateRight 2 := rotateLeft_eq x (by omega_using [])
theorem rotl1 (x : Word) : x.rotateLeft 1 = x.rotateRight 31 := rotateLeft_eq x (by omega_using [])

/-- The round is symbolically executed once per function `f`, for any
registers `a … e` and any register of the schedule. -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hw : s.gpr (cur t) = w.setWidth 64)
    (hk : s.gpr KR = (K t).setWidth 64) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (f t v[1] v[2] v[3]) (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ∉ work → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hv
  have hd := round_nodup t
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hd
  obtain ⟨⟨h01, -, -, h04⟩, ⟨h12, h13, h14⟩, ⟨-, h24⟩, h34⟩ := hd
  have m0 := var_mem t 0; have m1 := var_mem t 1; have m2 := var_mem t 2
  have m3 := var_mem t 3; have m4 := var_mem t 4
  have mc := sched_ne (cur_mem t)
  rw [Impl.Sha1.AArch64.round, WP.block_append_iff]
  refine WP.mono (fcode_ok (fn t) _ _ _ s _ _ _ m1 m2 m3 h1 h2 h3)
    fun s₁ ⟨hT1, hk₁, hm₁, hrd₁, hwr₁⟩ => ?_
  have k₁ : ∀ r ∈ work, s₁.gpr r = s.gpr r := fun r hr =>
    hk₁ r (work_ne hr).2.1 (work_ne hr).2.2.1
  refine WP.mono (sum_ok (var t 0) (var t 1) (var t 4) (cur t) s₁ v[0] v[1] v[4] _ (K t) w m1 m4
    h14 (cur_mem t)
    (by rw [k₁ _ m0, h0]) (by rw [k₁ _ m1, h1]) (by rw [k₁ _ m4, h4]) hT1
    (by rw [hk₁ _ mc.2.1 mc.2.2.1, hw]) (by rw [hk₁ _ (by decide) (by decide), hk]))
    fun s₂ ⟨he, hb, hk₂, hm₂, hrd₂, hwr₂⟩ => ?_
  refine ⟨?_, by rw [hm₂, hm₁], by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁], fun r hr hr1 hr2 => ?_⟩
  · simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 4 by omega_using []),
      var_succ t _ (show 1 < 4 by omega_using []), var_succ t _ (show 2 < 4 by omega_using []),
      var_succ t _ (show 3 < 4 by omega_using [])]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [he, ← f_eq]; simp only [roundKW, rotl5]; rfl
    · rw [hk₂ _ h04 h01 (work_ne m0).2.2.1, k₁ _ m0, h0]; rfl
    · rw [hb]; simp only [roundKW, rotl30]; rfl
    · rw [hk₂ _ h24 (Ne.symm h12) (work_ne m2).2.2.1, k₁ _ m2, h2]; rfl
    · rw [hk₂ _ h34 (Ne.symm h13) (work_ne m3).2.2.1, k₁ _ m3, h3]; rfl
  · have hne : ∀ k, r ≠ var t k := fun k h => hr (h ▸ var_mem t k)
    rw [hk₂ r (hne 4) (hne 1) hr2, hk₁ r hr1 hr2]

/-! ## The constant -/

/-- `Kₜ` changes every 20 rounds. -/
theorem K_succ (t : Nat) (h : (t + 1) % 20 ≠ 0) : K (t + 1) = K t := by
  unfold Spec.Sha1.K
  (repeat' split) <;> first | rfl | (exfalso; omega)

theorem kcode_ok (t : Nat) (s : State) (hk : t % 20 ≠ 0 → s.gpr KR = (K t).setWidth 64) :
    WP isa (.block (kcode t)) s fun s' =>
      s'.gpr KR = (K t).setWidth 64 ∧ (∀ r, r ≠ KR → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  by_cases h : t % 20 = 0
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [kcode, h, KR, runBlock_cons, runStep_some,
      runBlock_nil, exec, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, Size.bits, ite_true, movz_movk',
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r h1 => by simp [h1], trivial⟩
  · simp only [kcode, h, ↓reduceIte]
    exact WP.block_nil (M := isa) ⟨hk h, fun _ _ => rfl, rfl, rfl, rfl⟩

/-! ## The message schedule -/

theorem slot_ok (j : Nat) : slot j % 4 = 0 ∧ slot j < 16384 := by
  simp only [slot]; omega_using []

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofNat 64 (slot j)

/-- The schedule is symbolically executed once for the block's words and
once for the others, for any register of the schedule. -/
theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hx1 : s.gpr .x1 = bp) (hx3 : s.gpr .x3 = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
    (hblk : t < 16 → rev32 (s.mem.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j)
    (hcur : 16 ≤ t → s.gpr (cur t) = (W M (t - 3)).setWidth 64) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.gpr (cur t) = (W M t).setWidth 64 ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ cur t → r ≠ T1 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  obtain ⟨-, c1, -, cx3⟩ := sched_ne (cur_mem t)
  have cx3' := cx3.symm
  simp only [T1] at c1 ⊢
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    have ho : 4 * t % 4 = 0 ∧ 4 * t < 16384 := by omega_using [ht]
    simp only [Impl.Sha1.AArch64.schedule, ht, ite_true]
    generalize cur t = c at *
    simp only [↓reduceIte, Nat.reduceLeDiff, runBlock_cons, runStep_some,
      runBlock_nil, exec_ldr_w ho, exec_str_w (slot_ok _),
      exec_rev32, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Size.bits, hx1, hx3, hi, hout,
      cx3', BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, hb,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, trivial, fun r h0 _ => ?_⟩
    simp [h0]
  · have hw := hwin (by omega_using [ht])
    have e3 := hcur (by omega_using [ht])
    have e8 := hw (t - 8) (by omega_using [ht]) (by omega_using [])
    have e14 := hw (t - 14) (by omega_using [ht]) (by omega_using [])
    have e16 := hw (t - 16) (by omega_using [ht]) (by omega_using [])
    rw [show slot (t - 8) = slot (t + 8) by simp only [slot]; omega_using [ht]] at e8
    rw [show slot (t - 14) = slot (t + 2) by simp only [slot]; omega_using [ht]] at e14
    rw [show slot (t - 16) = slot t by simp only [slot]; omega_using [ht]] at e16
    simp only [Impl.Sha1.AArch64.schedule, ht, ite_false, T1]
    generalize cur t = c at *
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, runBlock_cons, runStep_some,
      runBlock_nil, exec_ldr_w (slot_ok _),
      exec_str_w (slot_ok _), exec_logic, exec_ror_w, isa, State.read,
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Size.bits, hx3, hin, hout, BitVec.setWidth_setWidth_of_le,
      c1, cx3', BitVec.setWidth_eq, e3, e8, e14, e16, Option.some.injEq, exists_eq_left']
    have hW := W_ge M (t := t) (by omega_using [ht])
    rw [rotl1] at hW
    refine ⟨by rw [hW], by rw [hW], trivial, trivial, fun r h0 h1 => ?_⟩
    simp [h0, h1]

/-! ## The 80 rounds -/

/-- The window `⟨scr, 64⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 64⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 4 := by
  simp only [slotAddr, slot]
  exact Offset.contains_base _ (by omega_using []) (by omega_using [])

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  simp only [slotAddr, slot]
  exact Offset.sep _ (by omega_using [h]) (by omega_using []) (by omega_using [])

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha1.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j
  k : t % 20 ≠ 0 → s.gpr KR = (K t).setWidth 64
  last : ∀ j < t, t ≤ j + 3 → s.gpr (cur j) = (W M j).setWidth 64

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hrsi : sB.gpr .x1 = bp) (hrcx : sB.gpr .x3 = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → rev32 (m.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 80, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (by omega_using []), fun h => absurd rfl h,
      fun j hj => absurd hj (by omega_using [])⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega_using [ht])) fun s hs => ?_)
    rw [WP.block_append_iff]
    refine WP.mono (kcode_ok t s hs.k) fun s₀ ⟨hK, hr₀, hm₀, hrd₀, hwr₀⟩ => ?_
    have mc := sched_ne (cur_mem t)
    have hs_rsi : s₀.gpr .x1 = bp := by rw [hr₀ _ (by decide), hs.pub .x1 (by decide), hrsi]
    have hs_rcx : s₀.gpr .x3 = scr := by rw [hr₀ _ (by decide), hs.pub .x3 (by decide), hrcx]
    rw [WP.block_append_iff]
    refine WP.mono (schedule_ok t s₀ M bp scr hs_rsi hs_rcx
      (by rw [hrd₀, hwr₀, hs.rd, hs.wr]; exact hin) (by rw [hwr₀, hs.wr]; exact hout)
      (fun h => by rw [hrd₀, hwr₀, hs.rd, hs.wr]; exact hbin t h) (by rw [hm₀]; exact hblk _ hs.frame t)
      (fun _ => by rw [hm₀]; exact hs.win)
      (fun h => by
        have e := hs.last (t - 3) (by omega_using [h]) (by omega_using [h])
        rw [← cur_add_three (t - 3), show t - 3 + 3 = t by omega_using [h]] at e
        rw [hr₀ _ mc.1, e]))
      fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hv₁ : Vars t s₁ (VG.Spec.Sha1.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k => by
        have hw := work_ne (var_mem t k)
        rw [hr₁ _ (fun h => hw.2.2.2.2 (by rw [h]; exact cur_mem t)) hw.2.1, hr₀ _ hw.1]
      simp only [Vars, e] at hv ⊢
      exact hv
    have hK₁ : s₁.gpr KR = (K t).setWidth 64 := by
      rw [hr₁ _ (Ne.symm mc.1) (by decide), hK]
    refine WP.mono (round_ok t s₁ _ _ hv₁ hT0 hK₁) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hrd₀, hs.rd], by rw [hwr₂, hwr₁, hwr₀, hs.wr],
      ?_, ?_, fun h => ?_, ?_⟩
    · rw [rounds_succ, round_eq]; exact hv₂
    · have hp := pubRegs_ne hr
      rw [hr₂ r hp.2.2.2.1 hp.2.1 hp.2.2.1, hr₁ r (fun h => hp.2.2.2.2 (by rw [h]; exact cur_mem t)) hp.2.1,
        hr₀ r hp.1, hs.pub r hr]
    · rw [hm₂, hm₁, hm₀]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains scr t)
    · intro j hj hj'
      rw [hm₂, hm₁, hm₀]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep scr (by omega_using [hj, hj', hjt])) (by decide)]
        exact hs.win j (by omega_using [hj, hjt]) (by omega_using [hj'])
    · rw [K_succ t h, hr₂ _ (by decide) (by decide) (by decide), hK₁]
    · intro j hj hj'
      have mj := sched_ne (cur_mem j)
      rw [hr₂ _ (fun h => (work_ne h).2.2.2.2 (cur_mem j)) mj.2.1 mj.2.2.1]
      by_cases hjt : j = t
      · subst hjt; exact hT0
      · rw [hr₁ _ (cur_ne (by omega_using [hj, hj', hjt])) mj.2.1, hr₀ _ mj.1]
        exact hs.last j (by omega_using [hj, hjt]) (by omega_using [hj'])

end VG.Proof.Sha1.AArch64

/-!
# SHA-1 compression function on AArch64: the whole function
-/

/-!
## SHA-1: the AArch64 contract

The contracts the proofs are written against; the artifacts are emitted with the
shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the AArch64 implementations of the compression function and the
streaming interface, in terms of `Spec/Sha1.lean`.

The return address is in the link register `x30`, which the target's
calling convention requires to be preserved (`VG.AArch64.abiPreserved`), not
on the stack, so unlike on x86-64 no region needs to be kept disjoint from it.
-/

namespace VG.Proof.Sha1

open Spec.Sha1

open VG.AArch64 in
/-- AArch64 contract for
`vg_sha1_compress(state: *mut [u32; 5], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 14])`:
updates the hash value at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(20 bytes) and `scratch` (112 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers and `n` are public; the hash
value and the blocks are secret. -/
def compressAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 20⟩
    let blocks : Region := ⟨s.gpr .x1, 64 * (s.gpr .x2).toNat⟩
    let scratch : Region := ⟨s.gpr .x3, 112⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .x0) =
      compressBlocks (stateAt s.mem (s.gpr .x0)) s.mem (s.gpr .x1) (s.gpr .x2).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for `vg_sha1_init(state: *mut [u8; 84])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (84 bytes). The pointer is public. -/
def initAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 84⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := Repr s'.mem (s.gpr .x0) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for
`vg_sha1_update(state: *mut [u8; 84], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

The code may read `data` (`len` bytes) and read and write `state` (84
bytes) and `scratch` (160 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the 16 bytes below the stack pointer
(the frame saving `x30`), which do not wrap around. The pointers, `count` and
`len` are public; the state and the data are secret. -/
def updateAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 84⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 160⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    Repr s'.mem (s.gpr .x0) (m ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for
`vg_sha1_finalize(state: *mut [u8; 84], count: u64, out: *mut [u8; 20], scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the SHA-1 digest of `m` to `out`.

The code may read and write `state` (84 bytes, whose contents on exit are
unspecified), `out` (20 bytes) and `scratch` (160 bytes, whose contents on
exit are unspecified). These may not overlap each other, nor the 16 bytes
below the stack pointer (the frame saving `x30`), which do not wrap around.
The pointers and `count` are public; the state is secret. -/
def finalizeAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 84⟩
    let out : Region := ⟨s.gpr .x2, 20⟩
    let scratch : Region := ⟨s.gpr .x3, 160⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (s.gpr .x2) 20 = Spec.Sha1.hash m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.Sha1

namespace VG.Proof.Sha1.AArch64

open VG VG.AArch64 VG.Impl.Sha1.AArch64
open VG.Spec.Sha1 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! The hash value in memory and offsets into regions (`Proof/Sha1/StateMem.lean`). -/
export VG.Proof.Sha1.StateMem (toNat_ofNat_lt contains_offset sub_offset word_sep readW_writeW_word
  stateAt_eq stateAt_get writeState stateAt_writeState)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev bp : Addr := s₀.gpr .x1
abbrev nb : Nat := (s₀.gpr .x2).toNat
abbrev scr : Addr := s₀.gpr .x3
abbrev stR : Region := ⟨st s₀, 20⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 112⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha1.compressAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem nb_lt : 64 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega_using [hn]

theorem in_state {k : Nat} (hk : k < 5) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega_using [hk]) (by omega_using [hk])⟩

theorem out_state {k : Nat} (hk : k < 5) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega_using [hk]) (by omega_using [hk])⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by simp only [slot]; omega_using []) (by simp only [slot]; omega_using [])⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by simp only [slot]; omega_using []) (by simp only [slot]; omega_using [])⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_ofNat_add_ofNat _ _ _]
  exact contains_offset (by omega_using [hi, ht]) (by omega_using [hi, ht, this])

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x3 : s.gpr .x3 = scr s₀
  kept : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  x1 : s.gpr .x1 = blkAddr s₀ i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i)

theorem preserved_sub : ∀ r ∈ preserved, r ∈ pubRegs := by decide

/-! ## One block -/

theorem load_eq : load = [
    .ldr .w .x4 .x0 (4 * 0), .ldr .w .x5 .x0 (4 * 1), .ldr .w .x6 .x0 (4 * 2),
    .ldr .w .x7 .x0 (4 * 3), .ldr .w .x8 .x0 (4 * 4)] := by
  decide

theorem update_eq : update ++ advance = [
    .ldr .w .x9 .x0 (4 * 0), .ldr .w .x10 .x0 (4 * 1), .ldr .w .x11 .x0 (4 * 2),
    .ldr .w .x12 .x0 (4 * 3), .ldr .w .x13 .x0 (4 * 4),
    .add .w .x4 .x4 .x9, .add .w .x5 .x5 .x10, .add .w .x6 .x6 .x11, .add .w .x7 .x7 .x12,
    .add .w .x8 .x8 .x13,
    .str .w .x4 .x0 (4 * 0), .str .w .x5 .x0 (4 * 1), .str .w .x6 .x0 (4 * 2),
    .str .w .x7 .x0 (4 * 3), .str .w .x8 .x0 (4 * 4),
    .addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .x4 = v[0].setWidth 64 ∧ s.gpr .x5 = v[1].setWidth 64 ∧
    s.gpr .x6 = v[2].setWidth 64 ∧ s.gpr .x7 = v[3].setWidth 64 ∧
    s.gpr .x8 = v[4].setWidth 64 := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hx0 : s.gpr .x0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 5 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec_ldr_w, isa, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hx0,
    h0, h1, h2, h3, h4, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 5 by decide), stateAt_get _ _ (show 1 < 5 by decide),
    stateAt_get _ _ (show 2 < 5 by decide), stateAt_get _ _ (show 3 < 5 by decide),
    stateAt_get _ _ (show 4 < 5 by decide)]
  simp (config := {decide := true}) [pubRegs]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 5 → (stR s₀).Contains (st s₀ + BitVec.ofNat 64 (4 * k)) (32 / 8) :=
    fun k hk => contains_offset (by omega_using [hk]) (by omega_using [hk])
  simp only [writeState]
  refine ((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hx0 : s.gpr .x0 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 5) → s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .x1 = s.gpr .x1 + 64 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.gpr .x3 = s.gpr .x3 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 5 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 5 → InRegions s.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin 4 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH 4 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec_ldr_w, exec_str_w, exec_add, exec_addImm_x, exec_subImm_x, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Size.bits, hx0,
    i0, i1, i2, i3, i4, o0, o1, o2, o3, o4,
    m0, m1, m2, m3, m4, v0, v1, v2, v3, v4, ite_true, ite_false,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · simp only [writeState, Vector.getElem_zipWith]
  and_intros
  all_goals first
    | trivial
    | rfl
    | (intro r hr
       simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
       simp (config := {decide := true}))

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    rev32 (s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 32) = W (blk s₀ i) t := by
  rw [W_lt _ ht, rev32_readW]
  simp only [blk, blockAt, parseBlock, Offset.add_ofNat_add_one, Nat.add_assoc, Nat.reduceAdd]

theorem win_sub (p : Addr) : Region.Sub (winRegion p) ⟨p, 112⟩ := Region.sub_prefix (by omega_using [])

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .x .x2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.x0 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      rev32 (m.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  have hx1₁ : s₁.gpr .x1 = blkAddr s₀ i := (hpub₁ .x1 (by decide)).trans hL.x1
  have hx3₁ : s₁.gpr .x3 = scr s₀ := (hpub₁ .x3 (by decide)).trans hL.x3
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hx1₁ hx3₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 80 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hx0₂ : s₂.gpr .x0 = st s₀ := by rw [pub₂ .x0 (by decide), hL.x0]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hx0₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (contains_offset (by omega_using [hk]) (by omega_using [hk])) hst (by decide), hm₁,
      stateAt_get _ _ hk]
  obtain ⟨hm₃, hx1₃, hx2₃, hx0₃, hx3₃, hkept₃, hrd₃, hwr₃⟩ := h₃
  have hx2 : s₂.gpr .x2 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₂ .x2 (by decide), hL.x2, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [hm₃]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hx0₃, hx0₂], by rw [hx3₃, pub₂ .x3 (by decide), hL.x3],
      fun r hr => by rw [hkept₃ r hr, pub₂ r (preserved_sub r hr), hL.kept r hr],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_⟩
    rw [hm₃, stateAt_writeState, compressBlocks_succ, ← hL.state]
    rfl
  have hev : eval (.nonzero .x .x2) s₃ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2₃, hx2]
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this])] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega_using [hi, hlast], { hcommon _ rfl with x1 := ?_, x2 := ?_ }⟩
    · rw [hx1₃, pub₂ .x1 (by decide), hL.x1]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec _) = BitVec.ofNat _ 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hx2₃, hx2]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha1.compressAArch64.post s₀ s' := by
  have hc₀ : Common s₀ 0 s₀ :=
    ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  refine WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s' hc => ⟨hc.kept, hc.state⟩
  refine WP.ite (s₀.gpr .x2 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi], i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₀ :=
      { hc₀ with
        x1 := by simp [blkAddr]
        x2 := by simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₀ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 20⟩, ⟨0x3000, 112⟩]

theorem compress_verified :
    Verified AArch64.target Impl.Sha1.AArch64.compress Proof.Sha1.compressAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha1.AArch64
