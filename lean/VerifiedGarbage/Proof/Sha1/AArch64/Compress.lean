module

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Sha1.Spec
public import VerifiedGarbage.Impl.Sha1.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
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
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
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

/-- The pointers, the count and the link register: never written by the
rounds. -/
def pubRegs : List Reg := [.x0, .x1, .x2, .x3, .x30]

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

theorem wreg_mem (t : Nat) : wreg t ∈ wregs := by
  unfold wreg List.getD
  cases h : wregs[t % 16]?
  · simp [wregs]
  · exact List.mem_of_getElem? h

/-- The window's register depends on the round modulo 16 only. -/
theorem wreg_congr {a b : Nat} (h : a % 16 = b % 16) : wreg a = wreg b := by
  simp only [wreg, h]

theorem wreg_ne {i j : Nat} (h : i % 16 ≠ j % 16) : wreg i ≠ wreg j := by
  have h' : ∀ a < 16, ∀ b < 16, a ≠ b → wregs.getD a .x12 ≠ wregs.getD b .x12 := by decide
  exact h' _ (Nat.mod_lt _ (by omega_using [])) _ (Nat.mod_lt _ (by omega_using [])) h

theorem work_ne' : ∀ r ∈ work, r ≠ KR ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs ∧ r ∉ wregs := by decide

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ KR ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs ∧ r ∉ wregs :=
  work_ne' r h

theorem wregs_ne' : ∀ r ∈ wregs, r ≠ KR ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs ∧ r ∉ work := by decide

theorem wregs_ne {r : Reg} (h : r ∈ wregs) : r ≠ KR ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs ∧ r ∉ work :=
  wregs_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ KR ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ work ∧ r ∉ wregs := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ KR ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ work ∧ r ∉ wregs :=
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
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
  obtain ⟨-, b1, -, -⟩ := work_ne hbw
  obtain ⟨-, c1, c2, -⟩ := work_ne hcw
  obtain ⟨-, d1, -, -⟩ := work_ne hdw
  simp only [T1, T2] at b1 c1 c2 d1 ⊢
  apply WP.of_runBlock
  cases g <;>
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self, fcode, T1, T2, runBlock_cons, runStep_some,
    runBlock_nil, exec_logic, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.v_write, Size.bits, b1, c1, d1, hb, hc, hd,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨rfl, fun r h1 h2 => by simp [h1, h2], ?_⟩ <;> trivial

/-- The sum in the order the code accumulates it. -/
theorem sum_comm (r fv z k w : Word) : z + w + k + fv + r = r + fv + z + k + w := by
  ac_rfl

theorem sum_ok (a b e wr : Reg) (s : State) (x y z fv k w : Word)
    (hbw : b ∈ work) (hew : e ∈ work) (hbe : b ≠ e) (hww : wr ∈ wregs)
    (ha : s.gpr a = x.setWidth 64) (hb : s.gpr b = y.setWidth 64) (he : s.gpr e = z.setWidth 64)
    (hf : s.gpr T1 = fv.setWidth 64) (hw : (s.gpr wr).setWidth 32 = w)
    (hk : s.gpr KR = k.setWidth 64) :
    WP isa (.block (sum a b e wr)) s fun s' =>
      s'.gpr e = (x.rotateRight 27 + fv + z + k + w).setWidth 64 ∧
      s'.gpr b = (y.rotateRight 2).setWidth 64 ∧
      (∀ r, r ≠ e → r ≠ b → r ≠ T2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
  obtain ⟨e0, e1, e2, -⟩ := work_ne hew
  obtain ⟨-, -, b2, -⟩ := work_ne hbw
  obtain ⟨-, -, w2, -⟩ := wregs_ne hww
  have heb := hbe.symm
  have e0' := e0.symm; have e1' := e1.symm; have e2' := e2.symm
  simp only [KR, T1, T2] at e0' e1' e2 e2' b2 w2 hf hk ⊢
  apply WP.of_runBlock
  simp only [sum, KR, T1, T2, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, runBlock_cons, runStep_some,
    runBlock_nil, exec_add, exec_ror_w, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.v_write, Size.bits,
    e0', e1', e2, e2', b2, w2, hbe, heb, ha, hb, he, hf, hw, hk,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨congrArg _ (sum_comm _ _ _ _ _), trivial, fun r h1 h2 h3 => by simp [h1, h2, h3],
    trivial, trivial, trivial, trivial⟩

theorem rotl5 (x : Word) : x.rotateLeft 5 = x.rotateRight 27 := rotateLeft_eq x (by omega_using [])
theorem rotl30 (x : Word) : x.rotateLeft 30 = x.rotateRight 2 := rotateLeft_eq x (by omega_using [])
theorem rotl1 (x : Word) : x.rotateLeft 1 = x.rotateRight 31 := rotateLeft_eq x (by omega_using [])

/-- The round is symbolically executed once per function `f`, for any
registers `a … e` and any register of the schedule, whose low half is `Wₜ`. -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hw : (s.gpr (wreg t)).setWidth 32 = w)
    (hk : s.gpr KR = (K t).setWidth 64) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (f t v[1] v[2] v[3]) (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v ∧
      ∀ r, r ∉ work → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hv
  have hd := round_nodup t
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hd
  obtain ⟨⟨h01, -, -, h04⟩, ⟨h12, h13, h14⟩, ⟨-, h24⟩, h34⟩ := hd
  have m0 := var_mem t 0; have m1 := var_mem t 1; have m2 := var_mem t 2
  have m3 := var_mem t 3; have m4 := var_mem t 4
  have mc := wregs_ne (wreg_mem t)
  rw [Impl.Sha1.AArch64.round, WP.block_append_iff]
  refine WP.mono (fcode_ok (fn t) _ _ _ s _ _ _ m1 m2 m3 h1 h2 h3)
    fun s₁ ⟨hT1, hk₁, hm₁, hrd₁, hwr₁, hv₁⟩ => ?_
  have k₁ : ∀ r ∈ work, s₁.gpr r = s.gpr r := fun r hr =>
    hk₁ r (work_ne hr).2.1 (work_ne hr).2.2.1
  refine WP.mono (sum_ok (var t 0) (var t 1) (var t 4) (wreg t) s₁ v[0] v[1] v[4] _ (K t) w m1 m4
    h14 (wreg_mem t)
    (by rw [k₁ _ m0, h0]) (by rw [k₁ _ m1, h1]) (by rw [k₁ _ m4, h4]) hT1
    (by rw [hk₁ _ mc.2.1 mc.2.2.1, hw]) (by rw [hk₁ _ (by decide) (by decide), hk]))
    fun s₂ ⟨he, hb, hk₂, hm₂, hrd₂, hwr₂, hv₂⟩ => ?_
  refine ⟨?_, by rw [hm₂, hm₁], by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁], by rw [hv₂, hv₁],
    fun r hr hr1 hr2 => ?_⟩
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
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
  by_cases h : t % 20 = 0
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [kcode, h, KR, runBlock_cons, runStep_some,
      runBlock_nil, exec, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, RegUpd.v_write, Size.bits, ite_true, movz_movk',
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r h1 => by simp [h1], trivial⟩
  · simp only [kcode, h, ↓reduceIte]
    exact WP.block_nil (M := isa) ⟨hk h, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-! ## The message schedule -/

/-- The words of the schedule, in the order the code combines them. -/
theorem xor4 (a b c d : Word) : a ^^^ b ^^^ c ^^^ d = d ^^^ c ^^^ b ^^^ a := by ac_rfl

/-- The schedule's code, for any registers of the four words it reads, each
the low half of its register. -/
theorem schedule_run (s : State) (rw rb rc rd : Reg) (a b c d : Word)
    (nc : rc ≠ rw) (nd : rd ≠ rw)
    (hx : (s.gpr rw).setWidth 32 = a) (hb : (s.gpr rb).setWidth 32 = b)
    (hc : (s.gpr rc).setWidth 32 = c) (hd : (s.gpr rd).setWidth 32 = d) :
    WP isa (.block [.logic .eor .w rw rw rb, .logic .eor .w rw rw rc, .logic .eor .w rw rw rd,
        .ror .w rw rw 31]) s fun s' =>
      (s'.gpr rw).setWidth 32 = (a ^^^ b ^^^ c ^^^ d).rotateRight 31 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v ∧
      ∀ r, r ≠ rw → s'.gpr r = s.gpr r := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, runBlock_cons, runStep_some, runBlock_nil,
    exec_logic, exec_ror_w, isa, State.read, Size.bits, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.v_write, nc, nd, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, hx, hb, hc, hd, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, fun r h0 => ?_⟩
  simp only [h0, ite_false]

theorem schedule_ok (t : Nat) (ht : 16 ≤ t) (s : State) (M : Block)
    (hwin : ∀ j, t ≤ j + 16 → j < t → (s.gpr (wreg j)).setWidth 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      (s'.gpr (wreg t)).setWidth 32 = W M t ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.v = s.v ∧ ∀ r, r ≠ wreg t → s'.gpr r = s.gpr r := by
  have e16 := hwin (t - 16) (by omega_using [ht]) (by omega_using [ht])
  have e14 := hwin (t - 14) (by omega_using [ht]) (by omega_using [ht])
  have e8 := hwin (t - 8) (by omega_using [ht]) (by omega_using [ht])
  have e3 := hwin (t - 3) (by omega_using [ht]) (by omega_using [ht])
  rw [wreg_congr (show (t - 16) % 16 = t % 16 by omega_using [ht])] at e16
  rw [wreg_congr (show (t - 14) % 16 = (t + 2) % 16 by omega_using [ht])] at e14
  rw [wreg_congr (show (t - 8) % 16 = (t + 8) % 16 by omega_using [ht])] at e8
  rw [wreg_congr (show (t - 3) % 16 = (t + 13) % 16 by omega_using [ht])] at e3
  have h := schedule_run s (wreg t) (wreg (t + 2)) (wreg (t + 8)) (wreg (t + 13)) _ _ _ _
    (wreg_ne (by omega_using [])) (wreg_ne (by omega_using [])) e16 e14 e8 e3
  have hW := W_ge M (t := t) (by omega_using [ht])
  rw [rotl1] at hW
  simp only [Impl.Sha1.AArch64.schedule, show ¬ t < 16 by omega_using [ht], ite_false]
  exact WP.mono h fun s' ⟨h1, h2, h3, h4, h5, h6⟩ =>
    ⟨by rw [h1, hW, xor4 (W M (t - 16))], h2, h3, h4, h5, h6⟩

/-! ## The 80 rounds -/

/-- Rounds invariant, relative to the state `sB` at the start of the rounds:
the low halves of the window's registers hold the last 16 words of the
schedule (the block's, in the first 16 rounds). -/
structure RInv (H : HashValue) (M : Block) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha1.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  mem : s.mem = sB.mem
  v : s.v = sB.v
  win : ∀ j, t ≤ j + 16 → (j < t ∨ j < 16) → (s.gpr (wreg j)).setWidth 32 = W M j
  k : t % 20 ≠ 0 → s.gpr KR = (K t).setWidth 64

theorem rounds_ok (H : HashValue) (M : Block) (sB : State)
    (hw : ∀ j, j < 16 → (sB.gpr (wreg j)).setWidth 32 = W M j) (h0 : Vars 0 sB H) :
    ∀ t ≤ 80, WP isa (rounds t) sB (RInv H M sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, rfl, rfl,
      fun j _ hj => hw j (hj.elim (fun h => absurd h (Nat.not_lt_zero _)) id), fun h => absurd rfl h⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega_using [ht])) fun s hs => ?_)
    rw [WP.block_append_iff]
    refine WP.mono (kcode_ok t s hs.k) fun s₀ ⟨hK, hr₀, hm₀, hrd₀, hwr₀, hv₀⟩ => ?_
    have mc := wregs_ne (wreg_mem t)
    rw [WP.block_append_iff]
    -- The word of the schedule.
    have hsched : WP isa (.block (schedule t)) s₀ fun s₁ =>
        (s₁.gpr (wreg t)).setWidth 32 = W M t ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
        s₁.v = s₀.v ∧ ∀ r, r ≠ wreg t → s₁.gpr r = s₀.gpr r := by
      have hwin : ∀ j, t ≤ j + 16 → (j < t ∨ j < 16) → (s₀.gpr (wreg j)).setWidth 32 = W M j :=
        fun j h1 h2 => by rw [hr₀ _ (wregs_ne (wreg_mem j)).1]; exact hs.win j h1 h2
      by_cases h16 : t < 16
      · simp only [Impl.Sha1.AArch64.schedule, h16, ite_true]
        exact WP.block_nil ⟨hwin t (by omega_using []) (.inr h16), rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
      · exact schedule_ok t (by omega_using [h16]) s₀ M fun j h1 h2 => hwin j h1 (.inl h2)
    refine WP.mono hsched fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hv₁, hr₁⟩ => ?_
    have hv₁' : Vars t s₁ (VG.Spec.Sha1.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k => by
        have hw := work_ne (var_mem t k)
        rw [hr₁ _ (fun h => hw.2.2.2.2 (by rw [h]; exact wreg_mem t)), hr₀ _ hw.1]
      simp only [Vars, e] at hv ⊢
      exact hv
    have hK₁ : s₁.gpr KR = (K t).setWidth 64 := by
      rw [hr₁ _ (Ne.symm mc.1), hK]
    refine WP.mono (round_ok t s₁ _ _ hv₁' hT0 hK₁) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hvv₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hrd₀, hs.rd], by rw [hwr₂, hwr₁, hwr₀, hs.wr],
      by rw [hm₂, hm₁, hm₀, hs.mem], by rw [hvv₂, hv₁, hv₀, hs.v], fun j hj hj' => ?_, fun h => ?_⟩
    · rw [rounds_succ, round_eq]; exact hv₂
    · have hp := pubRegs_ne hr
      rw [hr₂ r hp.2.2.2.1 hp.2.1 hp.2.2.1, hr₁ r (fun h => hp.2.2.2.2 (by rw [h]; exact wreg_mem t)),
        hr₀ r hp.1, hs.pub r hr]
    · have mj := wregs_ne (wreg_mem j)
      rw [hr₂ _ mj.2.2.2.2 mj.2.1 mj.2.2.1]
      by_cases hjt : j % 16 = t % 16
      · have : j = t := by omega_using [hj, hj', hjt]
        subst this; exact hT0
      · rw [hr₁ _ (wreg_ne hjt), hr₀ _ mj.1]
        exact hs.win j (by omega_using [hj]) (by
          have : j ≠ t := fun e => hjt (by rw [e])
          omega_using [hj', this])
    · rw [K_succ t h, hr₂ _ (by decide) (by decide) (by decide), hK₁]

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

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_ofNat_add_ofNat _ _ _]
  exact contains_offset (by omega_using [hi, ht]) (by omega_using [hi, ht, this])

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

/-- Two words of the block, loaded at once. -/
theorem in_blk2 {i j : Nat} (hi : i < nb s₀) (hj : j < 8) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (8 * j)) 8 := by
  have := h.nb_lt
  refine ⟨blR s₀, by simp [h.rd], ?_⟩
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (8 * j) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 8 * j) from Offset.add_add _ _ _]
  exact contains_offset (by omega_using [hi, hj]) (by omega_using [hi, hj, this])

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

/-! ## One block -/

/-- The low word of a byte-reversed doubleword is its high word, byte-reversed. -/
theorem rev64_lo (x : BitVec 64) : (rev64 x).setWidth 32 = rev32 (x.extractLsb' 32 32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [rev64, rev32, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first
    | omega
    | (simp (disch := omega) only [decide_eq_true, Bool.true_and]
       exact congrArg _ (by omega))

/-- The high word of a byte-reversed doubleword is its low word, byte-reversed. -/
theorem rev64_hi (x : BitVec 64) : (rev64 x >>> 32).setWidth 32 = rev32 (x.extractLsb' 0 32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [rev64, rev32, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first
    | omega
    | (simp (disch := omega) only [decide_eq_true, Bool.true_and]
       exact congrArg _ (by omega))

theorem wX1 (j : Nat) : wreg j ≠ .x1 := fun e =>
  (wregs_ne (wreg_mem j)).2.2.2.1 (by rw [e]; decide)

/-- The block's words loaded two at a time from the address `p` in `x1`:
each is the low half of its register. -/
theorem loadPairs_ok (p : Addr) : ∀ (n : Nat) (s : State), n ≤ 8 → s.gpr .x1 = p →
    (∀ i, i < n → InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 8) →
    WP isa (.block ((List.range n).flatMap loadPair)) s fun s' =>
      (∀ k, k < 2 * n →
        (s'.gpr (wreg k)).setWidth 32 = rev32 (s.mem.readW (p + BitVec.ofNat 64 (4 * k)) 32)) ∧
      (∀ x, (∀ k, k < 2 * n → x ≠ wreg k) → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v
  | 0, s, _, _, _ =>
    WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, s, hn, hb, hin => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (loadPairs_ok p n s (by omega_using [hn]) hb (fun i hi => hin i (by omega_using [hi])))
      fun s₁ ⟨hk₁, ho₁, hm₁, hrd₁, hwr₁, hv₁⟩ => ?_
    have eb : s₁.gpr .x1 = p := by rw [ho₁ .x1 fun k _ => (wX1 k).symm, hb]
    have i1 : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x1 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [hrd₁, hwr₁, eb]; exact hin n (by omega_using [])
    have hne : wreg (2 * n) ≠ wreg (2 * n + 1) := wreg_ne (by omega_using [hn])
    have hX1 : Reg.x1 ≠ wreg (2 * n + 1) := (wX1 _).symm
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, loadPair]
    rw [WP.block_cons_iff]
    refine ⟨_, exec_ldr_x ⟨by omega_using [], by omega_using [hn]⟩ i1, ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨_, exec_rev, ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨_, exec_lsr_x (sh := 32) (by decide), WP.block_nil ⟨fun k hk => ?_, fun x hx => ?_, ?_, ?_, ?_, ?_⟩⟩
    · by_cases h1 : k = 2 * n + 1
      · subst h1
        rw [RegUpd.gpr_write_of_ne _ .x _ hne.symm, RegUpd.gpr_write_self, BitVec.setWidth_eq]
        simp only [State.read, Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write_self]
        rw [rev64_lo, VG.AArch64.readW64_hi, eb, Offset.add_add, hm₁,
          show 8 * n + 4 = 4 * (2 * n + 1) by omega_using []]
      · by_cases h0 : k = 2 * n
        · subst h0
          rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
          simp only [State.read, Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write_self]
          rw [rev64_hi, VG.AArch64.readW64_lo, eb, hm₁, show 8 * n = 4 * (2 * n) by omega_using []]
        · have n0 : wreg k ≠ wreg (2 * n) := wreg_ne (by omega_using [hk, hn, h0])
          have n1 : wreg k ≠ wreg (2 * n + 1) := wreg_ne (by omega_using [hk, hn, h1])
          rw [RegUpd.gpr_write_of_ne _ .x _ n0, RegUpd.gpr_write_of_ne _ .x _ n1,
            RegUpd.gpr_write_of_ne _ .x _ n1, hk₁ k (by omega_using [hk, h0, h1])]
    · have n0 := hx (2 * n) (by omega_using [])
      have n1 := hx (2 * n + 1) (by omega_using [])
      rw [RegUpd.gpr_write_of_ne _ .x _ n0, RegUpd.gpr_write_of_ne _ .x _ n1,
        RegUpd.gpr_write_of_ne _ .x _ n1, ho₁ x fun k hk => hx k (by omega_using [hk])]
    · rw [RegUpd.mem_write, RegUpd.mem_write, RegUpd.mem_write, hm₁]
    · rw [RegUpd.rd_write, RegUpd.rd_write, RegUpd.rd_write, hrd₁]
    · rw [RegUpd.wr_write, RegUpd.wr_write, RegUpd.wr_write, hwr₁]
    · rw [RegUpd.v_write, RegUpd.v_write, RegUpd.v_write, hv₁]

/-- Words loaded from the address `p` in `b`, into registers different from
each other and from `b`. -/
theorem ldrws_ok (b : Reg) (r : Nat → Reg) (p : Addr) : ∀ (n : Nat) (s : State), n ≤ 4096 → s.gpr b = p →
    (∀ k, k < n → r k ≠ b) → (∀ i, i < n → ∀ j, j < n → i ≠ j → r i ≠ r j) →
    (∀ k, k < n → InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (4 * k)) 4) →
    WP isa (.block ((List.range n).map fun k => .ldr .w (r k) b (4 * k))) s fun s' =>
      (∀ k, k < n → s'.gpr (r k) = (s.mem.readW (p + BitVec.ofNat 64 (4 * k)) 32).setWidth 64) ∧
      (∀ x, (∀ k, k < n → x ≠ r k) → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v
  | 0, s, _, _, _, _, _ =>
    WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, s, hn, hb, hr, hd, hin => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ldrws_ok b r p n s (by omega_using [hn]) hb (fun k hk => hr k (by omega_using [hk]))
      (fun i hi j hj => hd i (by omega_using [hi]) j (by omega_using [hj]))
      (fun k hk => hin k (by omega_using [hk]))) fun s₁ ⟨hk₁, ho₁, hm₁, hrd₁, hwr₁, hv₁⟩ => ?_
    have eb : s₁.gpr b = p := by rw [ho₁ b fun k hk => (hr k (by omega_using [hk])).symm, hb]
    have i1 : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr b + BitVec.ofNat 64 (4 * n)) 4 := by
      rw [hrd₁, hwr₁, eb]; exact hin _ (by omega_using [])
    simp only [List.map_cons, List.map_nil]
    rw [WP.block_cons_iff]
    refine ⟨_, exec_ldr_w ⟨by omega_using [], by omega_using [hn]⟩ i1,
      WP.block_nil ⟨fun k hk => ?_, fun x hx => ?_, ?_, ?_, ?_, ?_⟩⟩
    · by_cases h0 : k = n
      · subst h0
        rw [RegUpd.gpr_write_self, eb, hm₁]
      · rw [RegUpd.gpr_write_of_ne _ .w _ (hd _ hk _ (by omega_using []) h0),
          hk₁ k (by omega_using [hk, h0])]
    · rw [RegUpd.gpr_write_of_ne _ .w _ (hx _ (by omega_using [])), ho₁ x fun k hk => hx k (by omega_using [hk])]
    · rw [RegUpd.mem_write, hm₁]
    · rw [RegUpd.rd_write, hrd₁]
    · rw [RegUpd.wr_write, hwr₁]
    · rw [RegUpd.v_write, hv₁]

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

/-- `load`: the hash value into the working variables. -/
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hx0 : s.gpr .x0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ x, x ∉ work → s₁.gpr x = s.gpr x) ∧
      s₁.v = s.v ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  refine WP.mono (ldrws_ok .x0 (var 0) (st s₀) 5 s (by decide) hx0 (by decide) (by decide)
    (fun k hk => by rw [hrd, hwr]; exact hp.in_state hk)) fun s₁ ⟨hk₁, ho₁, m₁, rd₁, wr₁, v₁⟩ => ?_
  have e : ∀ (k : Nat) (hk : k < 5), s₁.gpr (var 0 k) = ((stateAt s.mem (st s₀))[k]).setWidth 64 :=
    fun k hk => by rw [hk₁ k hk, stateAt_get _ _ hk]
  exact ⟨⟨e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide)⟩,
    fun x hx => ho₁ x (fun k _ e => hx (e ▸ var_mem 0 k)), v₁, rd₁, wr₁, m₁⟩

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
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
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
    runBlock_nil, exec_ldr_w, exec_str_w, exec_add, exec_addImm_x, exec_subImm_x, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.v_write, Size.bits, hx0,
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

/-- The loop invariant, at the start of block `i`: the caller's callee-saved
registers are in their lanes. -/
structure AInv (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = blkAddr s₀ i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i)
  x30 : s.gpr .x30 = s₀.gpr .x30
  saved : ∀ k ∈ saves, laneOf s k.2.1 k.2.2 = s₀.gpr k.1
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : AInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .x .x2) s' = some false ∧ AInv s₀ (nb s₀) s') ∨
      (eval (.nonzero .x .x2) s' = some true ∧ i + 1 < nb s₀ ∧ AInv s₀ (i + 1) s') := by
  unfold body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPairs_ok (blkAddr s₀ i) 8 s (by decide) hL.x1
    (fun k hk => by rw [hL.rd, hL.wr]; exact hp.in_blk2 hi hk))
    fun s₁ ⟨hw₁, ho₁, m₁, rd₁, wr₁, v₁⟩ => ?_
  have pub₁ : ∀ r ∈ pubRegs, s₁.gpr r = s.gpr r := fun r hr =>
    ho₁ r fun k _ e => (pubRegs_ne hr).2.2.2.2 (e ▸ wreg_mem k)
  refine WP.mono (load_ok hp ((pub₁ .x0 (by decide)).trans hL.x0) (rd₁.trans hL.rd) (wr₁.trans hL.wr))
    fun s₂ ⟨hv₂, ho₂, v₂, rd₂, wr₂, m₂⟩ => ?_
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [ho₂ r (pubRegs_ne hr).2.2.2.1, pub₁ r hr]
  have hw₂ : ∀ j, j < 16 → (s₂.gpr (wreg j)).setWidth 32 = W (blk s₀ i) j := fun j hj => by
    rw [ho₂ _ (wregs_ne (wreg_mem j)).2.2.2.2, hw₁ j hj,
      hL.frame.readW (hp.blk_contains hi hj) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i j hj
  rw [m₁] at hv₂
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) s₂ hw₂ hv₂ 80 (Nat.le_refl _)) fun s₃ hR => ?_)
  have pub₃ : ∀ r ∈ pubRegs, s₃.gpr r = s.gpr r := fun r hr => by rw [hR.pub r hr, pub₂ r hr]
  have mem₃ : s₃.mem = s.mem := by rw [hR.mem, m₂, m₁]
  have hx0₃ : s₃.gpr .x0 = st s₀ := by rw [pub₃ .x0 (by decide), hL.x0]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hx0₃
    (by rw [hR.rd, rd₂, rd₁, hL.rd]) (by rw [hR.wr, wr₂, wr₁, hL.wr])
    fun k hk => by rw [mem₃, stateAt_get _ _ hk]) fun s₄ h₄ => ?_
  obtain ⟨m₄, hx1₄, hx2₄, hx0₄, hx3₄, hkept₄, rd₄, wr₄, v₄⟩ := h₄
  have := hp.nb_lt
  have hx2 : s₃.gpr .x2 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₃ .x2 (by decide), hL.x2, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₄.mem := by
    refine hL.frame.trans ?_
    rw [m₄, mem₃]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hA : ∀ j, j = i + 1 → AInv s₀ j s₄ := by
    rintro j rfl
    refine ⟨by rw [hx0₄, hx0₃], ?_, by rw [hx2₄, hx2], ?_, fun k hk => ?_,
      by rw [rd₄, hR.rd, rd₂, rd₁, hL.rd], by rw [wr₄, hR.wr, wr₂, wr₁, hL.wr], hframe, ?_⟩
    · rw [hx1₄, pub₃ .x1 (by decide), hL.x1]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec _) = BitVec.ofNat _ 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hkept₄ .x30 (by decide), pub₃ .x30 (by decide), hL.x30]
    · have e : laneOf s₄ k.2.1 k.2.2 = laneOf s k.2.1 k.2.2 := by simp only [laneOf, v₄, hR.v, v₂, v₁]
      rw [e, hL.saved k hk]
    · rw [m₄, stateAt_writeState, compressBlocks_succ, ← hL.state]
      rfl
  have hev : eval (.nonzero .x .x2) s₄ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2₄, hx2]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hA _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this])] at h'
      exact hne h'
    exact ⟨by rw [hev]; simpa using h0, by omega_using [hi, hlast], hA _ rfl⟩

/-! ## The whole function -/

/-- The callee-saved registers are those kept in lanes, and `x30`. -/
theorem preserved_cases : ∀ r ∈ preserved, r = .x30 ∨ ∃ k ∈ saves, k.1 = r := by decide

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha1.compressAArch64.post s₀ s' := by
  refine WP.ite (s₀.gpr .x2 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    refine WP.block_nil (M := isa) ⟨fun _ _ => rfl, ?_⟩
    show stateAt s₀.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) (nb s₀)
    rw [h0]; rfl
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ AInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .x .x2) s' = some false ∧ AInv s₀ (nb s₀) s') ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi], i + 1, rfl, hi', hL'⟩
    -- The callee-saved registers into their lanes.
    refine WP.seq (WP.mono (insOf_ok saves s₀ (by decide) (by decide)) fun t ⟨tg, tm, trd, twr, _, tl, _⟩ => ?_)
    have hL₀ : AInv s₀ 0 t :=
      { x0 := by rw [tg]
        x1 := by rw [tg]; simp [blkAddr]
        x2 := by rw [tg]; simp [nb]
        x30 := by rw [tg]
        saved := tl
        rd := trd
        wr := twr
        frame := by rw [tm]; exact Frame.refl _ _
        state := by rw [tm]; rfl }
    refine WP.seq (WP.mono (WP.loop (M := isa) Inv hstep (nb s₀) _ ⟨0, rfl, hpos, hL₀⟩) fun s hA => ?_)
    -- And back from them.
    refine WP.mono (umovOf_ok saves s (by decide) (by decide)) fun t' ⟨m', _, _, _, hs', ho'⟩ =>
      ⟨fun r hr => ?_, ?_⟩
    · rcases preserved_cases r hr with rfl | ⟨k, hk, rfl⟩
      · rw [ho' _ (by decide), hA.x30]
      · rw [hs' k hk, hA.saved k hk]
    · show stateAt t'.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) (nb s₀)
      rw [m']; exact hA.state

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
  · refine LaneTaint.constantTime (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha1.AArch64
