module

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Sha512.Spec
public import VerifiedGarbage.Impl.Sha512.AArch64
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Sha512.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Sha512.Spec
meta import VerifiedGarbage.Impl.Sha512.AArch64
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Sha512.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# SHA-512 compression function on AArch64: the message schedule and the rounds
-/

@[expose] public section

namespace VG.Proof.Sha512.AArch64

open VG VG.AArch64 VG.Impl.Sha512.AArch64
open VG.Spec.Sha512 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

/-- The working variables `v` are in the registers of round `t`, and
`b ⊕ c` in `mreg (t + 1)`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧
  s.gpr (var t 2) = v[2] ∧ s.gpr (var t 3) = v[3] ∧
  s.gpr (var t 4) = v[4] ∧ s.gpr (var t 5) = v[5] ∧
  s.gpr (var t 6) = v[6] ∧ s.gpr (var t 7) = v[7] ∧
  s.gpr (mreg (t + 1)) = v[1] ^^^ v[2]

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega_using []

/-- `a ⊕ b` of a round is in the register of two rounds before. -/
theorem mreg_add2 (t : Nat) : mreg (t + 1 + 1) = mreg t := by
  simp only [mreg]; rw [show (t + 1 + 1) % 2 = t % 2 by omega_using []]

/-- The registers of round `t` that alternate. -/
theorem mreg_cases (t : Nat) :
    (mreg t = .x1 ∧ mreg (t + 1) = .x2) ∨ (mreg t = .x2 ∧ mreg (t + 1) = .x1) := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · exact .inl (by simp [mreg, h, show (t + 1) % 2 = 1 by omega_using [h]])
  · exact .inr (by simp [mreg, h, show (t + 1) % 2 = 0 by omega_using [h]])

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 8 - t % 8) % 8]?
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

theorem wreg_ne {a b : Nat} (h : a % 16 ≠ b % 16) : wreg a ≠ wreg b := by
  have ha := Nat.mod_lt a (show 16 > 0 by decide)
  have hb := Nat.mod_lt b (show 16 > 0 by decide)
  simp only [wreg]
  generalize a % 16 = x at *
  generalize b % 16 = y at *
  revert h; revert hb; revert y; revert ha; revert x
  decide

/-- The window's registers are none of the others. -/
theorem wregs_ne : ∀ r ∈ wregs, r ∉ work ∧ r ≠ T ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ KT := by decide

theorem work_ne : ∀ r ∈ work, r ≠ T ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ KT := by decide

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, T, mreg t, mreg (t + 1),
      wreg t].Nodup := by
  have h1 : [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, T, mreg t,
      mreg (t + 1)].Nodup := by
    rcases mreg_cases t with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> simp only [var] <;>
      have := Nat.mod_lt t (show 8 > 0 by bdd_omega) <;> generalize t % 8 = c at * <;>
      revert this <;> revert c <;> decide
  have hw := wregs_ne _ (wreg_mem t)
  have h2 : ∀ r ∈ [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, T, mreg t,
      mreg (t + 1)], r ≠ wreg t := by
    intro r hr e
    rw [← e] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hw.1 (var_mem _ _)
      | exact hw.2.1 rfl
      | (rcases mreg_cases t with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
          first | exact hw.2.2.1 e1 | exact hw.2.2.2.1 e1 | exact hw.2.2.1 e2 | exact hw.2.2.2.1 e2)
  exact List.nodup_append.mpr ⟨h1, List.pairwise_singleton _ _, fun a ha b hb =>
    (List.mem_singleton.mp hb) ▸ h2 a ha⟩

/-- `Maj`, from `b ⊕ c` and `a ⊕ b`. -/
theorem maj_xor (x y z : Word) : maj x y z = (y ^^^ z) &&& (x ^^^ y) ^^^ y := by
  ext i; simp only [maj, BitVec.getElem_xor, BitVec.getElem_and]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

/-- `T₁`, in the order the code adds it up and in the specification's. -/
theorem t1_order (h s c k w : Word) : h + w + k + s + c = h + s + c + k + w := by ac_rfl

/-- The round is symbolically executed once, for any registers `a … h`
(which `round_nodup` says are different from each other and the temporaries). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (k w : Word)
    (hv : Vars t s v) (hk : s.gpr T = k) (hw : s.gpr (wreg t) = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v k w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v ∧
      ∀ r, r ≠ var t 7 → r ≠ var t 3 → r ≠ T → r ≠ mreg t → r ≠ mreg (t + 1) → s'.gpr r = s.gpr r := by
  -- The registers the round reads and writes.
  have hs := round_nodup t
  have hs' := VG.nodup_reverse hs
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by bdd_omega),
    var_succ t _ (show 1 < 7 by bdd_omega), var_succ t _ (show 2 < 7 by bdd_omega),
    var_succ t _ (show 3 < 7 by bdd_omega), var_succ t _ (show 4 < 7 by bdd_omega),
    var_succ t _ (show 5 < 7 by bdd_omega), var_succ t _ (show 6 < 7 by bdd_omega), mreg_add2] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha512.AArch64.round]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  generalize mreg (t + 1) = mp at *
  generalize mreg t = mk at *
  generalize wreg t = cw at *
  simp only [T, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hs hs' hk ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.v_write, Size.bits, ite_true, ite_false, hs, hs', h0, h1, h2, h3, h4, h5, h6, h7,
    h8, hk, hw, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, trivial, trivial, trivial,
    fun r nh nd n1 nk np => ?_⟩
  rotate_right
  · simp only [nh, nd, n1, nk, np, ite_false]
  all_goals try rw [t1_order v[7] _ _ k w]
  all_goals
    simp (config := {failIfUnchanged := false}) only [roundKW_0, roundKW_1, roundKW_2, roundKW_3,
      roundKW_4, roundKW_5, roundKW_6, roundKW_7, bsig1, ch_eq, bsig0, maj_xor, BitVec.add_assoc]

/-! ## The message schedule -/

/-- `σ₁` and `σ₀`, with the shift first. -/
theorem ssig1_shr (x : Word) : ssig1 x = x >>> 6 ^^^ x.rotateRight 19 ^^^ x.rotateRight 61 := by
  unfold ssig1; ac_rfl

theorem ssig0_shr (x : Word) : ssig0 x = x >>> 7 ^^^ x.rotateRight 1 ^^^ x.rotateRight 8 := by
  unfold ssig0; ac_rfl

/-- The word of the schedule, in the order the code adds it up. -/
theorem W_sum (M : Block) {t : Nat} (h : 16 ≤ t) :
    W M (t - 16) + (W M (t - 15) >>> 7 ^^^ (W M (t - 15)).rotateRight 1 ^^^ (W M (t - 15)).rotateRight 8) +
      W M (t - 7) +
      (W M (t - 2) >>> 6 ^^^ (W M (t - 2)).rotateRight 19 ^^^ (W M (t - 2)).rotateRight 61) = W M t := by
  rw [W_ge M h, ssig1_shr, ssig0_shr]; ac_rfl

/-- The schedule's code, for any registers of the four words it reads. -/
theorem schedule_run (s : State) (rw rp rq ru : Reg) (a b c d : Word)
    (n1 : rw ≠ .x0) (n2 : rp ≠ .x0) (n3 : rq ≠ .x0) (n4 : ru ≠ .x0) (n5 : rq ≠ rw) (n6 : ru ≠ rw)
    (hx : s.gpr rw = a) (h15 : s.gpr rp = b) (h7 : s.gpr rq = c) (h2 : s.gpr ru = d) :
    WP isa (.block [.lsr .x .x0 rp 7, .logicRor .eor .x .x0 .x0 rp 1, .logicRor .eor .x .x0 .x0 rp 8,
        .add .x rw rw .x0, .lsr .x .x0 ru 6, .logicRor .eor .x .x0 .x0 ru 19,
        .logicRor .eor .x .x0 .x0 ru 61, .add .x rw rw rq, .add .x rw rw .x0]) s fun s' =>
      s'.gpr rw = a + (b >>> 7 ^^^ b.rotateRight 1 ^^^ b.rotateRight 8) + c +
        (d >>> 6 ^^^ d.rotateRight 19 ^^^ d.rotateRight 61) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v ∧
      ∀ r, r ≠ rw → r ≠ .x0 → s'.gpr r = s.gpr r := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, runBlock_cons, runStep_some, runBlock_nil, exec_add,
    exec_logicRor, exec_lsr_x, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.v_write, Size.bits, n1, n2, n3, n4, n5, n6, Ne.symm n1, BitVec.setWidth_eq,
    hx, h15, h7, h2, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, fun r h0 h1 => ?_⟩
  simp only [h0, h1, ite_false]

theorem schedule_ok (t : Nat) (ht : 16 ≤ t) (s : State) (M : Block)
    (hwin : ∀ j, t ≤ j + 16 → j < t → s.gpr (wreg j) = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.gpr (wreg t) = W M t ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v ∧
      ∀ r, r ≠ wreg t → r ≠ T → s'.gpr r = s.gpr r := by
  have e16 := hwin (t - 16) (by bdd_omega) (by bdd_omega)
  have e15 := hwin (t - 15) (by bdd_omega) (by bdd_omega)
  have e7 := hwin (t - 7) (by bdd_omega) (by bdd_omega)
  have e2 := hwin (t - 2) (by bdd_omega) (by bdd_omega)
  rw [wreg_congr (show (t - 16) % 16 = t % 16 by omega_using [ht])] at e16
  rw [wreg_congr (show (t - 15) % 16 = (t + 1) % 16 by omega_using [ht])] at e15
  rw [wreg_congr (show (t - 7) % 16 = (t + 9) % 16 by omega_using [ht])] at e7
  rw [wreg_congr (show (t - 2) % 16 = (t + 14) % 16 by omega_using [ht])] at e2
  have hT : ∀ j, wreg j ≠ .x0 := fun j => (wregs_ne _ (wreg_mem j)).2.1
  have h := schedule_run s (wreg t) (wreg (t + 1)) (wreg (t + 9)) (wreg (t + 14)) _ _ _ _ (hT _) (hT _) (hT _)
    (hT _) (wreg_ne (by omega_using [])) (wreg_ne (by omega_using [])) e16 e15 e7 e2
  simp only [Impl.Sha512.AArch64.schedule, show ¬ t < 16 by omega_using [ht], ite_false, T]
  exact WP.mono h fun s' ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨by rw [h1]; exact W_sum M ht, h2, h3, h4, h5, h6⟩

/-! ## The constants -/

/-- `ldrTbl` of round `t`'s constant, from `KT` holding the table's address. -/
theorem exec_kld {s : State} {t : Nat} (ht : t < 80) (d : Reg) (hx : s.gpr KT = s.syms kTab) :
    exec (.ldrTbl .x d KT (8 * t) kTab Spec.Sha512.Ks) s = some (s.write .x d (K t)) := by
  have hl : Spec.Sha512.Ks.length = 80 := rfl
  have hc : s.gpr KT = s.syms kTab ∧ 8 * t % Size.x.bytes = 0 ∧ 8 * t < 4096 * Size.x.bytes ∧
      8 * t / 8 < Spec.Sha512.Ks.length :=
    ⟨hx, by show 8 * t % 8 = 0; omega_using [], by show 8 * t < 4096 * 8; omega_using [ht],
      by rw [hl]; omega_using [ht]⟩
  have e : Spec.Sha512.Ks.getD t 0 = K t := rfl
  simp only [exec, ite_eq_left_of_eq_true _ _ (eq_true hc)]
  rw [show 8 * t / 8 = t by omega_using [], show 8 * t % 8 = 0 by omega_using [], e]
  exact congrArg (fun x => some (s.write .x d x)) BitVec.extractLsb'_eq_self

/-- `kload`: `Kₜ` into `T`. -/
theorem kload_ok (t : Nat) (ht : t < 80) (s : State) (hx : s.gpr KT = s.syms kTab) :
    WP isa (.block (kload t)) s fun s' =>
      s'.gpr T = K t ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v ∧
      ∀ r, r ≠ T → s'.gpr r = s.gpr r := by
  apply WP.of_runBlock
  have e : runBlock isa (kload t) s = some (s.write .x T (K t)) := by
    simp only [kload]
    rw [runBlock_cons, exec_kld ht _ hx, runStep_some, runBlock_nil]
  refine ⟨_, e, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · rw [RegUpd.mem_write]
  · rw [RegUpd.rd_write]
  · rw [RegUpd.wr_write]
  · rw [RegUpd.v_write]
  · rw [RegUpd.gpr_write_of_ne _ .x _ hr]

/-! ## The 80 rounds -/

/-- Rounds invariant, relative to the state `sB` at the start of the rounds:
the window holds the last 16 words of the schedule (the block's, in the first
16 rounds). -/
structure RInv (H : HashValue) (M : Block) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha512.rounds H M t)
  win : ∀ j, t ≤ j + 16 → (j < t ∨ j < 16) → s.gpr (wreg j) = W M j
  kt : s.gpr KT = sB.gpr KT
  x30 : s.gpr .x30 = sB.gpr .x30
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  v : s.v = sB.v
  syms : s.syms = sB.syms

/-- What the rounds never write. -/
theorem kept_ne (t : Nat) : ∀ r ∈ [KT, Reg.x30],
    r ≠ wreg t ∧ r ≠ T ∧ r ≠ var t 7 ∧ r ≠ var t 3 ∧ r ≠ mreg t ∧ r ≠ mreg (t + 1) := by
  intro r hr
  have hw := wregs_ne _ (wreg_mem t)
  have h7 := work_ne _ (var_mem t 7)
  have h3 := work_ne _ (var_mem t 3)
  have hwk : ∀ r ∈ [KT, Reg.x30], r ∉ wregs ∧ r ∉ work ∧ r ≠ T ∧ r ≠ .x1 ∧ r ≠ .x2 := by decide
  obtain ⟨k1, k2, k3, k4, k5⟩ := hwk r hr
  refine ⟨fun e => k1 (e ▸ wreg_mem t), k3, fun e => k2 (e ▸ var_mem t 7), fun e => k2 (e ▸ var_mem t 3), ?_, ?_⟩ <;>
    rcases mreg_cases t with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [e1, e2] <;> with_reducible assumption

theorem rounds_ok (H : HashValue) (M : Block) (sB : State) (hkt : sB.gpr KT = sB.syms kTab)
    (hw : ∀ j, j < 16 → sB.gpr (wreg j) = W M j) (h0 : Vars 0 sB H) :
    ∀ t ≤ 80, WP isa (rounds t) sB (RInv H M sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun j _ hj => hw j (hj.elim (fun h => absurd h (Nat.not_lt_zero _)) id),
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by bdd_omega)) fun s hs => ?_)
    rw [List.append_assoc, WP.block_append_iff]
    -- The word of the schedule.
    have hsched : WP isa (.block (schedule t)) s fun s₁ =>
        s₁.gpr (wreg t) = W M t ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.v = s.v ∧
        ∀ r, r ≠ wreg t → r ≠ T → s₁.gpr r = s.gpr r := by
      by_cases h16 : t < 16
      · simp only [Impl.Sha512.AArch64.schedule, h16, ite_true]
        exact WP.block_nil ⟨hs.win t (by bdd_omega) (.inr h16), rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩
      · exact schedule_ok t (by bdd_omega) s M fun j h1 h2 => hs.win j h1 (.inl h2)
    refine VG.AArch64.WP.mono_syms hsched fun s₁ ⟨hW₁, hm₁, hrd₁, hwr₁, hv₁, hr₁⟩ hsy₁ => ?_
    have kn := kept_ne t
    -- The constant.
    rw [WP.block_append_iff]
    refine VG.AArch64.WP.mono_syms (kload_ok t (by bdd_omega) s₁
      (by rw [hr₁ KT (kn _ (by simp)).1 (kn _ (by simp)).2.1, hsy₁, hs.kt, hs.syms]; exact hkt))
      fun s₂ ⟨hK₂, hm₂, hrd₂, hwr₂, hv₂, hr₂⟩ hsy₂ => ?_
    have wT : ∀ j, wreg j ≠ T := fun j => (wregs_ne _ (wreg_mem j)).2.1
    have keep₂ : ∀ r ∈ work, s₂.gpr r = s.gpr r := fun r hr => by
      have hw := wregs_ne _ (wreg_mem t)
      rw [hr₂ r (work_ne r hr).1, hr₁ r (fun e => hw.1 (e ▸ hr)) (work_ne r hr).1]
    have hv₂' : Vars t s₂ (VG.Spec.Sha512.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₂.gpr (var t k) = s.gpr (var t k) := fun k => keep₂ _ (var_mem t k)
      have em : s₂.gpr (mreg (t + 1)) = s.gpr (mreg (t + 1)) := by
        have hw := wregs_ne _ (wreg_mem t)
        have : mreg (t + 1) ≠ T ∧ mreg (t + 1) ≠ wreg t := by
          rcases mreg_cases t with ⟨-, e2⟩ | ⟨-, e2⟩ <;> rw [e2]
          · exact ⟨by decide, fun e => hw.2.2.2.1 e.symm⟩
          · exact ⟨by decide, fun e => hw.2.2.1 e.symm⟩
        rw [hr₂ _ this.1, hr₁ _ this.2 this.1]
      simp only [Vars, e, em] at hv ⊢
      exact hv
    have hw₂ : s₂.gpr (wreg t) = W M t := by rw [hr₂ _ (wT t), hW₁]
    -- The round.
    refine VG.AArch64.WP.mono_syms (round_ok t s₂ _ _ _ hv₂' hK₂ hw₂)
      fun s₃ ⟨hv₃, hm₃, hrd₃, hwr₃, hvv₃, hr₃⟩ hsy₃ => ?_
    have kept : ∀ r ∈ [KT, Reg.x30], s₃.gpr r = s.gpr r := fun r hr => by
      obtain ⟨k1, k2, k3, k4, k5, k6⟩ := kn r hr
      rw [hr₃ r k3 k4 k2 k5 k6, hr₂ r k2, hr₁ r k1 k2]
    refine ⟨?_, fun j hj hj' => ?_, by rw [kept _ (by simp), hs.kt], by rw [kept _ (by simp), hs.x30], by rw [hm₃, hm₂, hm₁, hs.mem], by rw [hrd₃, hrd₂, hrd₁, hs.rd],
      by rw [hwr₃, hwr₂, hwr₁, hs.wr], by rw [hvv₃, hv₂, hv₁, hs.v], by rw [hsy₃, hsy₂, hsy₁, hs.syms]⟩
    · have e : VG.Spec.Sha512.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha512.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₃
    · have hwj := wregs_ne _ (wreg_mem j)
      have n7 : wreg j ≠ var t 7 := fun e => hwj.1 (e ▸ var_mem t 7)
      have n3 : wreg j ≠ var t 3 := fun e => hwj.1 (e ▸ var_mem t 3)
      have nm : wreg j ≠ mreg t ∧ wreg j ≠ mreg (t + 1) := by
        rcases mreg_cases t with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
        · exact ⟨hwj.2.2.1, hwj.2.2.2.1⟩
        · exact ⟨hwj.2.2.2.1, hwj.2.2.1⟩
      rw [hr₃ _ n7 n3 (wT j) nm.1 nm.2, hr₂ _ (wT j)]
      by_cases hjt : j % 16 = t % 16
      · have : j = t := by omega_using [hj, hj', hjt]
        subst this; exact hW₁
      · rw [hr₁ _ (wreg_ne hjt) (wT j)]
        exact hs.win j (by omega_using [hj]) (by
          have : j ≠ t := fun e => hjt (by rw [e])
          omega_using [hj', this])

end VG.Proof.Sha512.AArch64

/-!
# SHA-512 compression function on AArch64: the whole function
-/

/-!
## SHA-512: the AArch64 contracts

The contracts the proofs are written against; the artifacts are emitted with the
shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the AArch64 implementations of the compression function and the
streaming interface, in terms of `Spec/Sha512.lean`.

The return address is in the link register `x30`, which the target's
calling convention requires to be preserved (`VG.AArch64.abiPreserved`), not
on the stack, so unlike on x86-64 no region needs to be kept disjoint from it.
-/

namespace VG.Proof.Sha512

open Spec.Sha512

open VG.AArch64 in
/-- AArch64 contract for
`vg_sha512_compress(state: *mut [u64; 8], blocks: *const [u8; 128], n: usize, scratch: *mut [u64; 80])`:
updates the hash value at `state` with the `n` 128-byte blocks at `blocks`.

The code may read `blocks` (`128 * n` bytes) and read and write `state`
(64 bytes) and `scratch` (`scratchBytes` bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers and `n` are public; the hash
value and the blocks are secret. -/
def compressAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 64⟩
    let blocks : Region := ⟨s.gpr .x1, 128 * (s.gpr .x2).toNat⟩
    let scratch : Region := ⟨s.gpr .x3, Impl.Sha512.AArch64.scratchBytes⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .x0) =
      compressBlocks (stateAt s.mem (s.gpr .x0)) s.mem (s.gpr .x1) (s.gpr .x2).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for `vg_<alg>_init(state: *mut [u8; 192])`, where `iv` is
the initial hash value of `<alg>` (`H0_384`, `H0_512`, `H0_512_224` or
`H0_512_256`): makes the streaming state at `state` represent the empty
message, hashed from `iv`.

The code may write `state` (192 bytes). The pointer is public. -/
def initAArch64 (iv : HashValue) : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 192⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := Repr iv s'.mem (s.gpr .x0) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for
`vg_sha512_update(state: *mut [u8; 192], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 86])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), hashed from any initial hash value, then afterwards it
represents `m` followed by the `len` bytes at `data`, from the same one.

The code may read `data` (`len` bytes) and read and write `state` (192
bytes) and `scratch` (`scratchBytes + 48` bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the 16 bytes below the stack pointer
(the frame saving `x30`), which do not wrap around. The pointers, `count` and
`len` are public; the state and the data are secret. -/
def updateAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 192⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, Impl.Sha512.AArch64.scratchBytes + 48⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, Repr iv s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    Repr iv s'.mem (s.gpr .x0) (m ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for
`vg_sha512_finalize(state: *mut [u8; 192], count: u64, out: *mut [u8; 64], scratch: *mut [u64; 86])`:
if the streaming state at `state` represents a message `m` of `count` bytes,
fewer than 2⁶⁴, hashed from the initial hash value `iv`, writes the final
hash value `H⁽ᴺ⁾` of `m` from `iv` (64 bytes; `finalHash iv m`) to `out`. The
digest of SHA-384, SHA-512/224 or SHA-512/256 is its first 48, 28 or 32
bytes.

The code may read and write `state` (192 bytes, whose contents on exit are
unspecified), `out` (64 bytes) and `scratch` (`scratchBytes + 48` bytes, whose contents on
exit are unspecified). These may not overlap each other, nor the 16 bytes
below the stack pointer (the frame saving `x30`), which do not wrap around.
The pointers and `count` are public; the state is secret. -/
def finalizeAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 192⟩
    let out : Region := ⟨s.gpr .x2, 64⟩
    let scratch : Region := ⟨s.gpr .x3, Impl.Sha512.AArch64.scratchBytes + 48⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, Repr iv s.mem (s.gpr .x0) m → m.length < 2 ^ 64 →
    s.gpr .x1 = BitVec.ofNat 64 m.length → bytesAt s'.mem (s.gpr .x2) 64 = finalHash iv m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.Sha512

namespace VG.Proof.Sha512.AArch64

open VG VG.AArch64 VG.Impl.Sha512.AArch64
open VG.Spec.Sha512 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## Addresses and regions -/

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (8 * j)) 8 (p + BitVec.ofNat 64 (8 * k)) 8 :=
  Offset.sep p (by bdd_omega) (by bdd_omega) (by bdd_omega)

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 8) (hk : k < 8)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (8 * k)) v).readW (p + BitVec.ofNat 64 (8 * j)) 64 =
    m.readW (p + BitVec.ofNat 64 (8 * j)) 64 :=
  Mem.readW_writeW_sep (word_sep p hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofNat 64 (8 * k)) 64 := by
  simp only [stateAt, Vector.getElem_ofFn]

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev bp : Addr := s₀.gpr .x1
abbrev nb : Nat := (s₀.gpr .x2).toNat
abbrev scr : Addr := s₀.gpr .x3
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev blR : Region := ⟨bp s₀, 128 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 640⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (128 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha512.compressAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem nb_lt : 128 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega_using [hn]

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by bdd_omega) (by bdd_omega)⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by bdd_omega) (by bdd_omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 8 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (8 * t) =
    bp s₀ + BitVec.ofNat 64 (128 * i + 8 * t) from Offset.add_ofNat_add_ofNat _ _ _]
  exact contains_offset (by bdd_omega) (by bdd_omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 8 :=
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

/-! ## One block -/

/-- `ldp`: two words next to each other. -/
theorem exec_ldp {s : State} {t1 t2 n : Reg} {off : Nat} (ht : t1 ≠ t2) (ho : off % 8 = 0 ∧ off ≤ 504)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off + 8) 8) :
    exec (.ldp t1 t2 n off) s =
      some ((s.write .x t1 (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64)).write .x t2
        (s.mem.readW (s.gpr n + BitVec.ofNat 64 off + 8) 64)) := by
  have hc : t1 ≠ t2 ∧ off % 8 = 0 ∧ off ≤ 504 := ⟨ht, ho⟩
  simp only [exec, ite_eq_left_of_eq_true _ _ (eq_true hc), State.load, h1, h2, ite_true, Option.bind_some,
    Option.map_some, Mem.readW]

/-- `stp`: two words next to each other. -/
theorem exec_stp {s : State} {t1 t2 n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off ≤ 504)
    (h1 : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8)
    (h2 : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off + 8) 8) :
    exec (.stp t1 t2 n off) s = some { s with mem :=
      ((s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr t1)).writeW
        (s.gpr n + BitVec.ofNat 64 off + 8) (s.gpr t2)) } := by
  simp only [exec, ite_eq_left_of_eq_true _ _ (eq_true ho), State.store, State.read, h1, h2, ite_true,
    Option.bind_some, Mem.writeW, Size.bits, BitVec.setWidth_eq]

/-- The addresses of a pair of words, as `ldp` and `stp` have them. -/
theorem pair_lo (p : Addr) (i : Nat) : p + BitVec.ofNat 64 (16 * i) = p + BitVec.ofNat 64 (8 * (2 * i)) := by
  rw [show 16 * i = 8 * (2 * i) by omega_using []]

theorem pair_hi (p : Addr) (i : Nat) :
    p + BitVec.ofNat 64 (16 * i) + 8 = p + BitVec.ofNat 64 (8 * (2 * i + 1)) := by
  rw [BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat,
    show 16 * i + 8 = 8 * (2 * i + 1) by omega_using []]

/-- Pairs of words loaded from the address `p` in `b`, into registers
different from each other and from `b`. -/
theorem ldps_ok (b : Reg) (r : Nat → Reg) (p : Addr) : ∀ (n : Nat) (s : State), n ≤ 31 → s.gpr b = p →
    (∀ k, k < 2 * n → r k ≠ b) → (∀ i, i < 2 * n → ∀ j, j < 2 * n → i ≠ j → r i ≠ r j) →
    (∀ k, k < 2 * n → InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * k)) 8) →
    WP isa (.block ((List.range n).map fun i => .ldp (r (2 * i)) (r (2 * i + 1)) b (16 * i))) s fun s' =>
      (∀ k, k < 2 * n → s'.gpr (r k) = s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64) ∧
      (∀ x, (∀ k, k < 2 * n → x ≠ r k) → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v
  | 0, s, _, _, _, _, _ =>
    WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, s, hn, hb, hr, hd, hin => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ldps_ok b r p n s (by omega_using [hn]) hb (fun k hk => hr k (by omega_using [hk]))
      (fun i hi j hj => hd i (by omega_using [hi]) j (by omega_using [hj]))
      (fun k hk => hin k (by omega_using [hk]))) fun s₁ ⟨hk₁, ho₁, hm₁, hrd₁, hwr₁, hv₁⟩ => ?_
    have eb : s₁.gpr b = p := by rw [ho₁ b fun k hk => (hr k (by omega_using [hk])).symm, hb]
    have i1 : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr b + BitVec.ofNat 64 (16 * n)) 8 := by
      rw [hrd₁, hwr₁, eb, pair_lo]; exact hin _ (by omega_using [])
    have i2 : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr b + BitVec.ofNat 64 (16 * n) + 8) 8 := by
      rw [hrd₁, hwr₁, eb, pair_hi]; exact hin _ (by omega_using [])
    have hne : r (2 * n) ≠ r (2 * n + 1) :=
      hd _ (by omega_using []) _ (by omega_using []) (by omega_using [])
    simp only [List.map_cons, List.map_nil]
    rw [WP.block_cons_iff]
    refine ⟨_, exec_ldp hne ⟨by omega_using [], by omega_using [hn]⟩ i1 i2,
      WP.block_nil ⟨fun k hk => ?_, fun x hx => ?_, ?_, ?_, ?_, ?_⟩⟩
    · by_cases h1 : k = 2 * n + 1
      · subst h1
        rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, eb, pair_hi, hm₁]
      · by_cases h0 : k = 2 * n
        · subst h0
          rw [RegUpd.gpr_write_of_ne _ .x _ hne, RegUpd.gpr_write_self, BitVec.setWidth_eq, eb, pair_lo, hm₁]
        · rw [RegUpd.gpr_write_of_ne _ .x _ (hd _ hk _ (by omega_using []) h1),
            RegUpd.gpr_write_of_ne _ .x _ (hd _ hk _ (by omega_using []) h0),
            hk₁ k (by omega_using [hk, h0, h1])]
    · rw [RegUpd.gpr_write_of_ne _ .x _ (hx _ (by omega_using [])),
        RegUpd.gpr_write_of_ne _ .x _ (hx _ (by omega_using [])), ho₁ x fun k hk => hx k (by omega_using [hk])]
    · rw [RegUpd.mem_write, RegUpd.mem_write, hm₁]
    · rw [RegUpd.rd_write, RegUpd.rd_write, hrd₁]
    · rw [RegUpd.wr_write, RegUpd.wr_write, hwr₁]
    · rw [RegUpd.v_write, RegUpd.v_write, hv₁]

/-- Each register of a list of different ones, with its octets reversed. -/
theorem revs_ok : ∀ (l : List Reg) (s : State), l.Nodup →
    WP isa (.block (l.map fun r => .rev r r)) s fun s' =>
      (∀ r ∈ l, s'.gpr r = rev64 (s.gpr r)) ∧ (∀ x, x ∉ l → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v
  | [], s, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | r :: l, s, hn => by
    obtain ⟨hn₁, hn₂⟩ := List.nodup_cons.mp hn
    simp only [List.map_cons]
    rw [WP.block_cons_iff]
    refine ⟨_, exec_rev, WP.mono (revs_ok l _ hn₂) fun s' ⟨h1, h2, h3, h4, h5, h6⟩ =>
      ⟨fun x hx => ?_, fun x hx => ?_, ?_, ?_, ?_, ?_⟩⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [h2 _ hn₁, RegUpd.gpr_write_self, BitVec.setWidth_eq]
        simp only [State.read, Size.bits, BitVec.setWidth_eq]
      · have ne : x ≠ r := fun e => hn₁ (by rw [← e]; exact hx)
        rw [h1 x hx, RegUpd.gpr_write_of_ne _ .x _ ne]
    · simp only [List.mem_cons, not_or] at hx
      rw [h2 x hx.2, RegUpd.gpr_write_of_ne _ .x _ hx.1]
    · rw [h3, RegUpd.mem_write]
    · rw [h4, RegUpd.rd_write]
    · rw [h5, RegUpd.wr_write]
    · rw [h6, RegUpd.v_write]

/-! ### Lanes -/

theorem lane_setV_self (s : State) (v : VReg) {l : Nat} (hl : l < 2) (x : BitVec 64) :
    laneOf (s.setV v (setLane (s.v v) 64 l x)) v l = x := by
  rw [laneOf_setV]
  simp only [↓reduceIte, extract_setLane64 _ _ hl hl]

theorem lane_setV_other (s : State) (v : VReg) {l l' : Nat} (hl : l < 2) (hl' : l' < 2) (h : l ≠ l')
    (x : BitVec 64) : laneOf (s.setV v (setLane (s.v v) 64 l x)) v l' = laneOf s v l' := by
  rw [laneOf_setV]
  simp only [↓reduceIte, extract_setLane64 _ _ hl hl', h]

theorem lane_setV_ne (s : State) {v w : VReg} (h : w ≠ v) (y : BitVec 128) (l : Nat) :
    laneOf (s.setV v y) w l = laneOf s w l := by
  rw [laneOf_setV]
  simp only [h, ↓reduceIte]

/-- A register into a lane, then the rest of a block. -/
theorem ins_step {s : State} {v : VReg} {l : Nat} {r : Reg} (hl : l < 2) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ s' : State, s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      laneOf s' v l = s.gpr r →
      (∀ w l', (w ≠ v ∨ l' ≠ l) → l' < 2 → laneOf s' w l' = laneOf s w l') → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.ins .d2 v l r) :: is)) s Q := by
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ins hl, k _ (RegUpd.gpr_setV _ _ _) (RegUpd.mem_setV _ _ _) (RegUpd.rd_setV _ _ _)
    (RegUpd.wr_setV _ _ _) (lane_setV_self _ _ hl _) fun w l' h hl' => ?_⟩
  by_cases hw : w = v
  · subst hw
    exact lane_setV_other _ _ hl hl' (fun e => h.elim (fun h => h rfl) (fun h => h e.symm)) _
  · exact lane_setV_ne _ hw _ _

/-- A lane into a register, then the rest of a block. -/
theorem umov_step {s : State} {r : Reg} {v : VReg} {l : Nat} (hl : l < 2) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ s' : State, s'.gpr r = laneOf s v l → (∀ x, x ≠ r → s'.gpr x = s.gpr x) → s'.v = s.v →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.umov .x r v l :: is)) s Q := by
  rw [WP.block_cons_iff]
  exact ⟨_, exec_umov hl, k _ ((RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _))
    (fun x hx => RegUpd.gpr_write_of_ne _ .x _ hx) (RegUpd.v_write _ _ _ _) (RegUpd.mem_write _ _ _ _)
    (RegUpd.rd_write _ _ _ _) (RegUpd.wr_write _ _ _ _)⟩

theorem wT (j : Nat) : wreg j ≠ T := (wregs_ne _ (wreg_mem j)).2.1

/-- `loadBlock`: the block's words into the window, and the next block's
address into its lane. -/
theorem loadBlock_ok {s : State} {p : Addr} (hp : laneOf s PV 1 = p)
    (hin : ∀ k, k < 16 → InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block loadBlock) s fun s' =>
      (∀ j, j < 16 → s'.gpr (wreg j) = rev64 (s.mem.readW (p + BitVec.ofNat 64 (8 * j)) 64)) ∧
      laneOf s' PV 1 = p + 128 ∧
      (∀ w l, (w ≠ PV ∨ l ≠ 1) → l < 2 → laneOf s' w l = laneOf s w l) ∧
      (∀ x, x ∉ wregs → x ≠ T → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold loadBlock
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine umov_step (by decide) fun s₁ g₁ o₁ v₁ m₁ rd₁ wr₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldps_ok T wreg p 8 s₁ (by decide) (g₁.trans hp) (fun k _ => wT k)
    (fun i hi j hj hij => wreg_ne (by omega_using [hi, hj, hij])) (by rw [rd₁, wr₁]; exact hin))
    fun s₂ ⟨hk₂, ho₂, m₂, rd₂, wr₂, v₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (revs_ok wregs s₂ (by decide)) fun s₃ ⟨hr₃, ho₃, m₃, rd₃, wr₃, v₃⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  refine ins_step (by decide) fun s₅ g₅ m₅ rd₅ wr₅ l₅ lo₅ => WP.block_nil ⟨fun j hj => ?_, ?_, fun w l h hl => ?_,
    fun x hx hT => ?_, ?_, ?_, ?_⟩
  · rw [g₅, RegUpd.gpr_write_of_ne _ .x _ (wT j), hr₃ _ (wreg_mem j), hk₂ j (by omega_using [hj]), m₁]
  · have e : s₃.gpr T = p := by
      rw [ho₃ T (by decide), ho₂ T (fun k _ => (wT k).symm), g₁, hp]
    rw [l₅, RegUpd.gpr_write_self, BitVec.setWidth_eq]
    simp only [State.read, Size.bits, BitVec.setWidth_eq, e]
    rfl
  · rw [lo₅ w l h hl]
    simp only [laneOf, RegUpd.v_write, v₃, v₂, v₁]
  · rw [g₅, RegUpd.gpr_write_of_ne _ .x _ hT, ho₃ x hx, ho₂ x (fun k _ e => hx (e ▸ wreg_mem k)), o₁ x hT]
  · rw [m₅, RegUpd.mem_write, m₃, m₂, m₁]
  · rw [rd₅, RegUpd.rd_write, rd₃, rd₂, rd₁]
  · rw [wr₅, RegUpd.wr_write, wr₃, wr₂, wr₁]

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .x4 = v[0] ∧ s.gpr .x5 = v[1] ∧
    s.gpr .x6 = v[2] ∧ s.gpr .x7 = v[3] ∧
    s.gpr .x8 = v[4] ∧ s.gpr .x9 = v[5] ∧
    s.gpr .x10 = v[6] ∧ s.gpr .x11 = v[7] ∧ s.gpr .x2 = v[1] ^^^ v[2] := Iff.rfl

/-- `load`: the hash value into the working variables. -/
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hst : laneOf s PV 0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s' =>
      Vars 0 s' (stateAt s.mem (st s₀)) ∧
      (∀ x, x ∉ work → x ≠ T → x ≠ .x2 → s'.gpr x = s.gpr x) ∧
      s'.v = s.v ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold load
  simp only [List.cons_append, List.nil_append, show mreg 1 = Reg.x2 from rfl]
  refine umov_step (by decide) fun s₁ g₁ o₁ v₁ m₁ rd₁ wr₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldps_ok T (var 0) (st s₀) 4 s₁ (by decide) (g₁.trans hst)
    (fun k _ => (work_ne _ (var_mem 0 k)).1) (by decide)
    (fun k hk => by rw [rd₁, wr₁, hrd, hwr]; exact hp.in_state hk))
    fun s₂ ⟨hk₂, ho₂, m₂, rd₂, wr₂, v₂⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨_, exec_logic (op := .eor) (sz := .x) (s := s₂) (d := .x2) (n := var 0 1) (m := var 0 2),
    WP.block_nil ⟨?_, fun x hx hT h2 => ?_, ?_, ?_, ?_, ?_⟩⟩
  · have e : ∀ (y : BitVec 64) (k : Nat) (hk : k < 8),
        (s₂.write .x .x2 y).gpr (var 0 k) = (stateAt s.mem (st s₀))[k] := fun y k hk => by
      rw [RegUpd.gpr_write_of_ne _ .x _ (work_ne _ (var_mem 0 k)).2.2.1, hk₂ k hk, m₁, stateAt_get _ _ hk]
    rw [vars0]
    refine ⟨e _ 0 (by decide), e _ 1 (by decide), e _ 2 (by decide), e _ 3 (by decide), e _ 4 (by decide),
      e _ 5 (by decide), e _ 6 (by decide), e _ 7 (by decide), ?_⟩
    rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
    simp only [State.read, Size.bits, BitVec.setWidth_eq]
    rw [hk₂ 1 (by decide), hk₂ 2 (by decide), m₁, stateAt_get _ _ (by decide), stateAt_get _ _ (by decide)]
  · rw [RegUpd.gpr_write_of_ne _ .x _ h2, ho₂ x (fun k _ e => hx (e ▸ var_mem 0 k)), o₁ x hT]
  · rw [RegUpd.v_write, v₂, v₁]
  · rw [RegUpd.mem_write, m₂, m₁]
  · rw [RegUpd.rd_write, rd₂, rd₁]
  · rw [RegUpd.wr_write, wr₂, wr₁]

/-- Eight 64-bit words written to consecutive addresses. -/
def writeState (m : Mem) (p : Addr) (v : HashValue) : Mem :=
  ((((((((m.writeW (p + BitVec.ofNat 64 (8 * 0)) v[0]).writeW
    (p + BitVec.ofNat 64 (8 * 1)) v[1]).writeW
    (p + BitVec.ofNat 64 (8 * 2)) v[2]).writeW
    (p + BitVec.ofNat 64 (8 * 3)) v[3]).writeW
    (p + BitVec.ofNat 64 (8 * 4)) v[4]).writeW
    (p + BitVec.ofNat 64 (8 * 5)) v[5]).writeW
    (p + BitVec.ofNat 64 (8 * 6)) v[6]).writeW
    (p + BitVec.ofNat 64 (8 * 7)) v[7])

set_option simprocs false in
theorem stateAt_writeState (m : Mem) (p : Addr) (v : HashValue) : stateAt (writeState m p v) p = v := by
  apply stateAt_eq
  intro k hk
  simp only [writeState]
  rcases (by bdd_omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;> subst h <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW_writeW_word]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 8 → (stR s₀).Contains (st s₀ + BitVec.ofNat 64 (8 * k)) (64 / 8) :=
    fun k hk => contains_offset (by bdd_omega) (by bdd_omega)
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _ (c 6 ?_)).writeW ?_ _ (c 7 ?_) <;>
  simp

theorem update_eq : update ++ advance = .umov .x T PV 0 ::
    ((List.range 4).map (fun i => Instr.ldp (wreg (2 * i)) (wreg (2 * i + 1)) T (16 * i)) ++
    (([.add .x .x4 .x4 .x12, .add .x .x5 .x5 .x13, .add .x .x6 .x6 .x14, .add .x .x7 .x7 .x15,
      .add .x .x8 .x8 .x16, .add .x .x9 .x9 .x17, .add .x .x10 .x10 .x19, .add .x .x11 .x11 .x20,
      .stp .x4 .x5 .x0 (16 * 0), .stp .x6 .x7 .x0 (16 * 1), .stp .x8 .x9 .x0 (16 * 2),
      .stp .x10 .x11 .x0 (16 * 3)] : List Instr) ++
     ([.umov .x T CV 0, .subImm .x T T 1, .vop (.ins .d2 CV 0 T)] : List Instr))) := by
  decide

/-- The hash value, in eight registers, added into the working variables and
stored at `p`. -/
theorem addStore_ok {s : State} {p : Addr} (V H : HashValue) (hx0 : s.gpr .x0 = p)
    (hv : s.gpr .x4 = V[0] ∧ s.gpr .x5 = V[1] ∧ s.gpr .x6 = V[2] ∧ s.gpr .x7 = V[3] ∧
      s.gpr .x8 = V[4] ∧ s.gpr .x9 = V[5] ∧ s.gpr .x10 = V[6] ∧ s.gpr .x11 = V[7])
    (hh : s.gpr .x12 = H[0] ∧ s.gpr .x13 = H[1] ∧ s.gpr .x14 = H[2] ∧ s.gpr .x15 = H[3] ∧
      s.gpr .x16 = H[4] ∧ s.gpr .x17 = H[5] ∧ s.gpr .x19 = H[6] ∧ s.gpr .x20 = H[7])
    (hout : ∀ k : Nat, k < 8 → InRegions s.wr (p + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block [.add .x .x4 .x4 .x12, .add .x .x5 .x5 .x13, .add .x .x6 .x6 .x14,
      .add .x .x7 .x7 .x15, .add .x .x8 .x8 .x16, .add .x .x9 .x9 .x17, .add .x .x10 .x10 .x19,
      .add .x .x11 .x11 .x20, .stp .x4 .x5 .x0 (16 * 0), .stp .x6 .x7 .x0 (16 * 1),
      .stp .x8 .x9 .x0 (16 * 2), .stp .x10 .x11 .x0 (16 * 3)]) s fun s' =>
      s'.mem = writeState s.mem p (Vector.zipWith (· + ·) V H) ∧
      (∀ x, x ∉ work → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
  have lo : ∀ i : Nat, i < 4 → InRegions s.wr (p + BitVec.ofNat 64 (16 * i)) 8 := fun i hi => by
    rw [pair_lo]; exact hout _ (by omega_using [hi])
  have hi : ∀ i : Nat, i < 4 → InRegions s.wr (p + BitVec.ofNat 64 (16 * i) + 8) 8 := fun i hi => by
    rw [pair_hi]; exact hout _ (by omega_using [hi])
  have a0 := lo 0 (by decide); have a1 := lo 1 (by decide); have a2 := lo 2 (by decide)
  have a3 := lo 3 (by decide)
  have b0 := hi 0 (by decide); have b1 := hi 1 (by decide); have b2 := hi 2 (by decide)
  have b3 := hi 3 (by decide)
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hh
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_stp,
    State.read, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.v_write,
    Size.bits, hx0, a0, a1, a2, a3, b0, b1, b2, b3, v0, v1, v2, v3, v4, v5, v6, v7, h0, h1, h2, h3, h4,
    h5, h6, h7, ite_false, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun x hx => ?_, trivial⟩
  · simp only [pair_hi]
    simp only [pair_lo]
    simp only [writeState, Vector.getElem_zipWith, RegUpd.mem_write, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd]
  · have : x ≠ .x4 ∧ x ≠ .x5 ∧ x ≠ .x6 ∧ x ≠ .x7 ∧ x ≠ .x8 ∧ x ≠ .x9 ∧ x ≠ .x10 ∧ x ≠ .x11 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hx (by decide)
    obtain ⟨n4, n5, n6, n7, n8, n9, n10, n11⟩ := this
    simp only [n4, n5, n6, n7, n8, n9, n10, n11, ite_false]

/-- The end of a block: the hash value is updated, and the count, in its
lane and in `T`, is one less. -/
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (c : BitVec 64)
    (hv : Vars 0 s V) (hst : laneOf s PV 0 = st s₀) (hc : laneOf s CV 0 = c)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) → s.mem.readW (st s₀ + BitVec.ofNat 64 (8 * k)) 64 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr T = c - 1 ∧ laneOf s' CV 0 = c - 1 ∧
      (∀ w l, (w ≠ CV ∨ l ≠ 0) → l < 2 → laneOf s' w l = laneOf s w l) ∧
      s'.gpr KT = s.gpr KT ∧ s'.gpr .x30 = s.gpr .x30 ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [update_eq]
  refine umov_step (by decide) fun s₁ g₁ o₁ v₁ m₁ rd₁ wr₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldps_ok T wreg (st s₀) 4 s₁ (by decide) (g₁.trans hst) (fun k _ => wT k)
    (fun i hi j hj hij => wreg_ne (by omega_using [hi, hj, hij]))
    (fun k hk => by rw [rd₁, wr₁, hrd, hwr]; exact hp.in_state hk))
    fun s₂ ⟨hk₂, ho₂, m₂, rd₂, wr₂, v₂⟩ => ?_
  have hk' : ∀ (k : Nat) (hk : k < 8), s₂.gpr (wreg k) = H[k] := fun k hk => by
    rw [hk₂ k hk, m₁, hH k hk]
  have keep₂ : ∀ x ∈ work, s₂.gpr x = s.gpr x := fun x hx => by
    have hw : ∀ k, x ≠ wreg k := fun k e => (wregs_ne _ (wreg_mem k)).1 (e ▸ hx)
    rw [ho₂ x (fun k _ => hw k), o₁ x (work_ne x hx).1]
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, -⟩ := hv
  rw [WP.block_append_iff]
  refine WP.mono (addStore_ok (s := s₂) (p := st s₀) V H
    (show s₂.gpr T = st s₀ by rw [ho₂ T (fun k _ => (wT k).symm), g₁, hst])
    ⟨(keep₂ _ (by decide)).trans v0, (keep₂ _ (by decide)).trans v1, (keep₂ _ (by decide)).trans v2,
      (keep₂ _ (by decide)).trans v3, (keep₂ _ (by decide)).trans v4, (keep₂ _ (by decide)).trans v5,
      (keep₂ _ (by decide)).trans v6, (keep₂ _ (by decide)).trans v7⟩
    ⟨hk' 0 (by decide), hk' 1 (by decide), hk' 2 (by decide), hk' 3 (by decide), hk' 4 (by decide),
      hk' 5 (by decide), hk' 6 (by decide), hk' 7 (by decide)⟩
    (fun k hk => by rw [wr₂, wr₁, hwr]; exact hp.out_state hk))
    fun s₃ ⟨m₃, o₃, rd₃, wr₃, v₃⟩ => ?_
  -- The count.
  refine umov_step (by decide) fun s₄ g₄ o₄ v₄ m₄ rd₄ wr₄ => ?_
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 1) (by decide), ?_⟩
  refine ins_step (by decide) fun s₆ g₆ m₆ rd₆ wr₆ l₆ lo₆ => WP.block_nil ?_
  have lane₄ : ∀ w l, laneOf s₄ w l = laneOf s w l := fun w l => by
    simp only [laneOf, v₄, v₃, v₂, v₁]
  have eT : (s₄.write .x T (s₄.read .x T - BitVec.ofNat 64 1)).gpr T = c - 1 := by
    rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
    simp only [State.read, Size.bits, BitVec.setWidth_eq]
    rw [g₄]
    have : laneOf s₃ CV 0 = c := by simp only [laneOf, v₃, v₂, v₁]; exact hc
    rw [this]; rfl
  have other : ∀ x, x ∉ work → x ∉ wregs → x ≠ T → s₆.gpr x = s.gpr x := fun x hw hx hT => by
    rw [g₆, RegUpd.gpr_write_of_ne _ .x _ hT, o₄ x hT, o₃ x hw, ho₂ x (fun k _ e => hx (e ▸ wreg_mem k)),
      o₁ x hT]
  refine ⟨?_, ?_, ?_, fun w l h hl => ?_, other _ (by decide) (by decide) (by decide),
    other _ (by decide) (by decide) (by decide), ?_, ?_⟩
  · rw [m₆, RegUpd.mem_write, m₄, m₃, m₂, m₁]
  · rw [g₆]; exact eT
  · rw [l₆]; exact eT
  · rw [lo₆ w l h hl]
    simp only [laneOf, RegUpd.v_write]
    exact lane₄ w l
  · rw [rd₆, RegUpd.rd_write, rd₄, rd₃, rd₂, rd₁]
  · rw [wr₆, RegUpd.wr_write, wr₄, wr₃, wr₂, wr₁]

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (128 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    rev64 (s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 64) = W (blk s₀ i) t := by
  rw [W_lt _ ht, rev64_readW]
  simp only [blk, blockAt, parseBlock, Offset.add_ofNat_add_one, Nat.add_assoc, Nat.reduceAdd]

/-- The loop invariant, at the start of block `i`: the pointers and the
count are in their lanes, with the caller's callee-saved registers. -/
structure AInv (s₀ : State) (i : Nat) (s : State) : Prop where
  stp : laneOf s PV 0 = st s₀
  dp : laneOf s PV 1 = blkAddr s₀ i
  cnt : laneOf s CV 0 = BitVec.ofNat 64 (nb s₀ - i)
  saved : ∀ k ∈ saves, laneOf s k.2.1 k.2.2 = s₀.gpr k.1
  x30 : s.gpr .x30 = s₀.gpr .x30
  kt : s.gpr KT = s.syms kTab
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

theorem saves_lanes : ∀ k ∈ saves, k.2.1 ≠ PV ∧ k.2.1 ≠ CV ∧ k.2.2 < 2 := by decide

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : AInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .x T) s' = some false ∧ AInv s₀ (nb s₀) s') ∨
      (eval (.nonzero .x T) s' = some true ∧ i + 1 < nb s₀ ∧ AInv s₀ (i + 1) s') := by
  unfold body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine VG.AArch64.WP.mono_syms (loadBlock_ok hL.dp (fun k hk => by rw [hL.rd, hL.wr]; exact hp.in_blk hi hk))
    fun s₁ ⟨hw₁, hdp₁, hl₁, ho₁, m₁, rd₁, wr₁⟩ sy₁ => ?_
  refine VG.AArch64.WP.mono_syms (load_ok hp (by rw [hl₁ PV 0 (.inr (by decide)) (by decide), hL.stp])
    (rd₁.trans hL.rd) (wr₁.trans hL.wr)) fun s₂ ⟨hv₂, ho₂, v₂, m₂, rd₂, wr₂⟩ sy₂ => ?_
  have keep₂ : ∀ x, x ∉ work → x ∉ wregs → x ≠ T → x ≠ .x2 → s₂.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [ho₂ x h1 h3 h4, ho₁ x h2 h3]
  have hkt₂ : s₂.gpr KT = s₂.syms kTab := by
    rw [keep₂ KT (by decide) (by decide) (by decide) (by decide), sy₂, sy₁]; exact hL.kt
  have hw₂ : ∀ j, j < 16 → s₂.gpr (wreg j) = W (blk s₀ i) j := fun j hj => by
    have hw := wregs_ne _ (wreg_mem j)
    rw [ho₂ _ hw.1 hw.2.1 hw.2.2.2.1, hw₁ j hj,
      hL.frame.readW (hp.blk_contains hi hj) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i j hj
  rw [m₁] at hv₂
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) s₂ hkt₂ hw₂ hv₂ 80 (Nat.le_refl _)) fun s₃ hR => ?_)
  have lane₃ : ∀ w l, laneOf s₃ w l = laneOf s₁ w l := fun w l => by simp only [laneOf, hR.v, v₂]
  have mem₃ : s₃.mem = s.mem := by rw [hR.mem, m₂, m₁]
  refine VG.AArch64.WP.mono_syms (update_ok hp _ (stateAt s.mem (st s₀)) (BitVec.ofNat 64 (nb s₀ - i)) hR.vars
    (by rw [lane₃, hl₁ PV 0 (.inr (by decide)) (by decide), hL.stp])
    (by rw [lane₃, hl₁ CV 0 (.inl (by decide)) (by decide), hL.cnt])
    (by rw [hR.rd, rd₂, rd₁, hL.rd]) (by rw [hR.wr, wr₂, wr₁, hL.wr])
    fun k hk => by rw [mem₃, stateAt_get _ _ hk]) fun s₄ h₄ sy₄ => ?_
  obtain ⟨m₄, hT₄, hc₄, hl₄, kt₄, x30₄, rd₄, wr₄⟩ := h₄
  have hcnt : BitVec.ofNat 64 (nb s₀ - i) - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by bdd_omega), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₄.mem := by
    refine hL.frame.trans ?_
    rw [m₄, mem₃]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hA : ∀ j, j = i + 1 → AInv s₀ j s₄ := by
    rintro j rfl
    refine ⟨?_, ?_, ?_, fun k hk => ?_, ?_, ?_, by rw [rd₄, hR.rd, rd₂, rd₁, hL.rd],
      by rw [wr₄, hR.wr, wr₂, wr₁, hL.wr], hframe, ?_⟩
    · rw [hl₄ PV 0 (.inl (by decide)) (by decide), lane₃, hl₁ PV 0 (.inr (by decide)) (by decide), hL.stp]
    · rw [hl₄ PV 1 (.inl (by decide)) (by decide), lane₃, hdp₁]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (128 : BitVec _) = BitVec.ofNat _ 128 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hc₄, hcnt]
    · obtain ⟨n1, n2, n3⟩ := saves_lanes k hk
      rw [hl₄ _ _ (.inl n2) n3, lane₃, hl₁ _ _ (.inl n1) n3, hL.saved k hk]
    · rw [x30₄, hR.x30, keep₂ _ (by decide) (by decide) (by decide) (by decide), hL.x30]
    · rw [kt₄, hR.kt, hkt₂, sy₄, hR.syms]
    · rw [m₄, stateAt_writeState, compressBlocks_succ, ← hL.state]
      rfl
  have hev : eval (.nonzero .x T) s₄ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    have hT' : s₄.gpr .x0 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := hT₄.trans hcnt
    simp only [eval, T, State.read, Size.bits, BitVec.setWidth_eq, hT']
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hA _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by bdd_omega
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by bdd_omega)] at h'
      exact hne h'
    exact ⟨by rw [hev]; simpa using h0, by bdd_omega, hA _ rfl⟩

/-! ## The whole function -/

/-- The callee-saved registers are those kept in lanes, and `x30`. -/
theorem preserved_cases : ∀ r ∈ preserved, r = .x30 ∨ ∃ k ∈ saves, k.1 = r := by decide

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha512.compressAArch64.post s₀ s' := by
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
        (eval (.nonzero .x T) s' = some false ∧ AInv s₀ (nb s₀) s') ∨
        (eval (.nonzero .x T) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by bdd_omega, i + 1, rfl, hi', hL'⟩
    -- The registers into their lanes, and the table's address.
    refine WP.seq ?_
    unfold enter
    rw [WP.block_append_iff]
    refine WP.mono (insOf_ok saves s₀ (by decide) (by decide)) fun t ⟨tg, tm, trd, twr, _, tl, tot⟩ => ?_
    refine ins_step (by decide) fun u₁ g₁ m₁ rd₁ wr₁ l₁ lo₁ => ins_step (by decide)
      fun u₂ g₂ m₂ rd₂ wr₂ l₂ lo₂ => ins_step (by decide) fun u₃ g₃ m₃ rd₃ wr₃ l₃ lo₃ => ?_
    rw [WP.block_cons_iff]
    refine ⟨_, exec_adrSym, WP.block_nil ?_⟩
    have hg : ∀ r, u₃.gpr r = s₀.gpr r := fun r => by rw [g₃, g₂, g₁, tg]
    have hgw : ∀ r, r ≠ KT → (u₃.write .x KT (u₃.syms kTab)).gpr r = s₀.gpr r := fun r hr => by
      rw [RegUpd.gpr_write_of_ne _ .x _ hr, hg]
    have hlw : ∀ w l, laneOf (u₃.write .x KT (u₃.syms kTab)) w l = laneOf u₃ w l := fun w l => by
      simp only [laneOf, RegUpd.v_write]
    have hL₀ : AInv s₀ 0 (u₃.write .x KT (u₃.syms kTab)) :=
      { stp := by
          rw [hlw, lo₃ PV 0 (.inl (by decide)) (by decide), lo₂ PV 0 (.inr (by decide)) (by decide), l₁, tg]
        dp := by
          rw [hlw, lo₃ PV 1 (.inl (by decide)) (by decide), l₂, g₁, tg]
          simp [blkAddr]
        cnt := by
          rw [hlw, l₃, g₂, g₁, tg]
          simp [nb]
        saved := fun k hk => by
          obtain ⟨n1, n2, n3⟩ := saves_lanes k hk
          rw [hlw, lo₃ _ _ (.inl n2) n3, lo₂ _ _ (.inl n1) n3, lo₁ _ _ (.inl n1) n3, tl k hk]
        x30 := hgw _ (by decide)
        kt := (RegUpd.gpr_write_self u₃ .x KT _).trans (BitVec.setWidth_eq _)
        rd := by rw [RegUpd.rd_write, rd₃, rd₂, rd₁, trd]
        wr := by rw [RegUpd.wr_write, wr₃, wr₂, wr₁, twr]
        frame := by rw [RegUpd.mem_write, m₃, m₂, m₁, tm]; exact Frame.refl _ _
        state := by rw [RegUpd.mem_write, m₃, m₂, m₁, tm]; rfl }
    refine WP.seq (WP.mono (WP.loop (M := isa) Inv hstep (nb s₀) _ ⟨0, rfl, hpos, hL₀⟩) fun s hA => ?_)
    -- The callee-saved registers back from their lanes.
    unfold leave
    rw [WP.block_append_iff]
    refine WP.mono (umovOf_ok saves s (by decide) (by decide)) fun t' ⟨m', _, _, _, hs', ho'⟩ => ?_
    refine umov_step (by decide) fun w _ o _ m _ _ => WP.block_nil ⟨fun r hr => ?_, ?_⟩
    · have hx1 : r ≠ .x1 := by rintro rfl; revert hr; decide
      rw [o r hx1]
      rcases preserved_cases r hr with rfl | ⟨k, hk, rfl⟩
      · rw [ho' _ (by decide), hA.x30]
      · rw [hs' k hk, hA.saved k hk]
    · show stateAt w.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) (nb s₀)
      rw [m, m']; exact hA.state

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x3000, 640⟩]

theorem compress_verified :
    Verified AArch64.target Impl.Sha512.AArch64.compress Proof.Sha512.compressAArch64 := by
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

end VG.Proof.Sha512.AArch64
