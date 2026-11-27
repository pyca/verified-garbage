module

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.Sha256.Spec
public import VerifiedGarbage.Impl.Sha256.AArch64
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sha256.StateMem
public import VerifiedGarbage.Proof.Sha256.AArch64.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Sha256.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Sha256.Spec
meta import VerifiedGarbage.Impl.Sha256.AArch64
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Proof.Sha256.AArch64.Contract
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Sha256.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# SHA-256 compression function on AArch64: the message schedule and the rounds
-/

@[expose] public section

namespace VG.Proof.Sha256.AArch64

open VG VG.AArch64 VG.Impl.Sha256.AArch64
open VG.Impl.Sha256.AArch64.Sha2 (kName kTable)
open VG.Spec.Sha256 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

/-- The working variables `v` are in the registers of round `t`, and
`b ⊕ c` in `mreg (t + 1)`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0].setWidth 64 ∧ s.gpr (var t 1) = v[1].setWidth 64 ∧
  s.gpr (var t 2) = v[2].setWidth 64 ∧ s.gpr (var t 3) = v[3].setWidth 64 ∧
  s.gpr (var t 4) = v[4].setWidth 64 ∧ s.gpr (var t 5) = v[5].setWidth 64 ∧
  s.gpr (var t 6) = v[6].setWidth 64 ∧ s.gpr (var t 7) = v[7].setWidth 64 ∧
  s.gpr (mreg (t + 1)) = (v[1] ^^^ v[2]).setWidth 64

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
  obtain ha := Nat.mod_lt a (show 16 > 0 by decide)
  obtain hb := Nat.mod_lt b (show 16 > 0 by decide)
  simp only [wreg]
  generalize a % 16 = x at *
  generalize b % 16 = y at *
  revert h; revert hb; revert y; revert ha; revert x
  decide

/-- The window's registers are none of the others. -/
theorem wregs_ne : ∀ r ∈ wregs, r ∉ work ∧ r ≠ T ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ KT := by decide

theorem work_ne : ∀ r ∈ work, r ≠ T ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ KT := by decide

theorem wT (j : Nat) : wreg j ≠ T := (wregs_ne _ (wreg_mem j)).2.1

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, T, mreg t, mreg (t + 1),
      wreg t].Nodup := by
  obtain h1 : [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, T, mreg t,
      mreg (t + 1)].Nodup := by
    rcases mreg_cases t with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> simp only [var] <;>
      have := Nat.mod_lt t (show 8 > 0 by omega_using []) <;> generalize t % 8 = c at * <;>
      revert this <;> revert c <;> decide
  obtain hw := wregs_ne _ (wreg_mem t)
  obtain h2 : ∀ r ∈ [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, T, mreg t,
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

/-- `T₁`, and `T₁ + T₂`, in the order the code adds them up. -/
theorem t1_sum (h w k s c : Word) : h + w + k + s + c = h + s + c + k + w := by ac_rfl

theorem t12_sum (h w k s c z m : Word) : h + w + k + s + c + z + m = h + s + c + k + w + (z + m) := by
  ac_rfl

/-- The round is symbolically executed once, for any registers `a … h`
(which `round_nodup` says are different from each other and the
temporaries), with the register writes kept folded (`VG.AArch64.RegUpd`).
`Wₜ` is the low half of its register. -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (k w : Word)
    (hv : Vars t s v) (hk : s.gpr T = k.setWidth 64) (hw : (s.gpr (wreg t)).setWidth 32 = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v k w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v ∧
      ∀ r, r ≠ var t 7 → r ≠ var t 3 → r ≠ T → r ≠ mreg t → r ≠ mreg (t + 1) → s'.gpr r = s.gpr r := by
  -- The registers the round reads and writes.
  obtain hs := round_nodup t
  obtain hs' := VG.nodup_reverse hs
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega_using []),
    var_succ t _ (show 1 < 7 by omega_using []), var_succ t _ (show 2 < 7 by omega_using []),
    var_succ t _ (show 3 < 7 by omega_using []), var_succ t _ (show 4 < 7 by omega_using []),
    var_succ t _ (show 5 < 7 by omega_using []), var_succ t _ (show 6 < 7 by omega_using []),
    mreg_add2] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha256.AArch64.round]
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
  simp only [T, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, or_false, not_or, List.nodup_nil, and_true] at hs hs' hk ⊢
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.read, Size.bits,
    RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.v_write, ite_true, Nat.reduceLT, Nat.reduceLeDiff, not_false_eq_true,
    hs, hs', h0, h1, h2, h3, h4, h5, h6, h7, h8, hk, hw,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, trivial, trivial, trivial,
    fun r nh nd n1 nk np => ?_⟩
  rotate_right
  · simp only [RegUpd.gpr_write_of_ne, nh, nd, n1, nk, np, not_false_eq_true]
  all_goals
    refine congrArg (BitVec.setWidth 64) ?_
    simp only [roundKW_0, roundKW_1, roundKW_2, roundKW_3, roundKW_4, roundKW_5, roundKW_6, roundKW_7,
      bsig1, ch_eq, bsig0, maj_xor]
  · exact t12_sum _ _ _ _ _ _ _
  · exact congrArg _ (t1_sum _ _ _ _ _)

/-! ## The message schedule -/

/-- `σ₁` and `σ₀`, with the shift first. -/
theorem ssig1_shr (x : Word) : ssig1 x = x >>> 10 ^^^ x.rotateRight 17 ^^^ x.rotateRight 19 := by
  unfold ssig1; ac_rfl

theorem ssig0_shr (x : Word) : ssig0 x = x >>> 3 ^^^ x.rotateRight 7 ^^^ x.rotateRight 18 := by
  unfold ssig0; ac_rfl

/-- The word of the schedule, in the order the code adds it up. -/
theorem W_sum (M : Block) {t : Nat} (h : 16 ≤ t) :
    W M (t - 16) + (W M (t - 15) >>> 3 ^^^ (W M (t - 15)).rotateRight 7 ^^^ (W M (t - 15)).rotateRight 18) +
      W M (t - 7) +
      (W M (t - 2) >>> 10 ^^^ (W M (t - 2)).rotateRight 17 ^^^ (W M (t - 2)).rotateRight 19) = W M t := by
  rw [W_ge M h, ssig1_shr, ssig0_shr]; ac_rfl

/-- The schedule's code, for any registers of the four words it reads, each
the low half of its register. -/
theorem schedule_run (s : State) (rw rp rq ru : Reg) (a b c d : Word)
    (n1 : rw ≠ .x0) (n2 : rp ≠ .x0) (n3 : rq ≠ .x0) (n4 : ru ≠ .x0) (n5 : rq ≠ rw) (n6 : ru ≠ rw)
    (hx : (s.gpr rw).setWidth 32 = a) (h15 : (s.gpr rp).setWidth 32 = b)
    (h7 : (s.gpr rq).setWidth 32 = c) (h2 : (s.gpr ru).setWidth 32 = d) :
    WP isa (.block [.lsr .w .x0 rp 3, .logicRor .eor .w .x0 .x0 rp 7, .logicRor .eor .w .x0 .x0 rp 18,
        .add .w rw rw .x0, .lsr .w .x0 ru 10, .logicRor .eor .w .x0 .x0 ru 17,
        .logicRor .eor .w .x0 .x0 ru 19, .add .w rw rw rq, .add .w rw rw .x0]) s fun s' =>
      (s'.gpr rw).setWidth 32 = a + (b >>> 3 ^^^ b.rotateRight 7 ^^^ b.rotateRight 18) + c +
        (d >>> 10 ^^^ d.rotateRight 17 ^^^ d.rotateRight 19) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v ∧
      ∀ r, r ≠ rw → r ≠ .x0 → s'.gpr r = s.gpr r := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, runBlock_cons, runStep_some, runBlock_nil, exec_add,
    exec_logicRor, exec_lsr_w, isa, State.read, Size.bits, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.v_write, Nat.reduceLeDiff, n1, n2, n3, n4, n5, n6, Ne.symm n1,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, hx, h15, h7, h2, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, fun r h0 h1 => ?_⟩
  simp only [h0, h1, ite_false]

theorem schedule_ok (t : Nat) (ht : 16 ≤ t) (s : State) (M : Block)
    (hwin : ∀ j, t ≤ j + 16 → j < t → (s.gpr (wreg j)).setWidth 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      (s'.gpr (wreg t)).setWidth 32 = W M t ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.v = s.v ∧ ∀ r, r ≠ wreg t → r ≠ T → s'.gpr r = s.gpr r := by
  obtain e16 := hwin (t - 16) (by omega_using [ht]) (by omega_using [ht])
  obtain e15 := hwin (t - 15) (by omega_using [ht]) (by omega_using [ht])
  obtain e7 := hwin (t - 7) (by omega_using [ht]) (by omega_using [ht])
  obtain e2 := hwin (t - 2) (by omega_using [ht]) (by omega_using [ht])
  rw [wreg_congr (show (t - 16) % 16 = t % 16 by omega_using [ht])] at e16
  rw [wreg_congr (show (t - 15) % 16 = (t + 1) % 16 by omega_using [ht])] at e15
  rw [wreg_congr (show (t - 7) % 16 = (t + 9) % 16 by omega_using [ht])] at e7
  rw [wreg_congr (show (t - 2) % 16 = (t + 14) % 16 by omega_using [ht])] at e2
  obtain hT : ∀ j, wreg j ≠ .x0 := fun j => wT j
  obtain h := schedule_run s (wreg t) (wreg (t + 1)) (wreg (t + 9)) (wreg (t + 14)) _ _ _ _ (hT _) (hT _) (hT _)
    (hT _) (wreg_ne (by omega_using [])) (wreg_ne (by omega_using [])) e16 e15 e7 e2
  simp only [Impl.Sha256.AArch64.schedule, show ¬ t < 16 by omega_using [ht], ite_false, T]
  exact WP.mono h fun s' ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨by rw [h1]; exact W_sum M ht, h2, h3, h4, h5, h6⟩

/-! ## The constants -/

theorem kTab_length : kTable.length = 32 := by simp [kTable]

/-- Round `t`'s constant is a half of a word of the table. -/
theorem kTab_word : ∀ t, t < 64 → (kTable.getD (4 * t / 8) 0).extractLsb' (8 * (4 * t % 8)) 32 = K t := by
  decide

/-- `ldrTbl` of round `t`'s constant, from `KT` holding the table's address. -/
theorem exec_kld {s : State} {t : Nat} (ht : t < 64) (hx : s.gpr KT = s.syms kName) :
    exec (.ldrTbl .w T KT (4 * t) kName kTable) s = some (s.write .w T (K t)) := by
  obtain hc : s.gpr KT = s.syms kName ∧ 4 * t % Size.w.bytes = 0 ∧ 4 * t < 4096 * Size.w.bytes ∧
      4 * t / 8 < kTable.length :=
    ⟨hx, by show 4 * t % 4 = 0; omega_using [], by show 4 * t < 4096 * 4; omega_using [ht],
      by rw [kTab_length]; omega_using [ht]⟩
  simp only [exec, ite_eq_left_of_eq_true _ _ (eq_true hc)]
  exact congrArg (fun x => some (s.write .w T x)) (kTab_word t ht)

/-- `kload`: `Kₜ` into `T`. -/
theorem kload_ok (t : Nat) (ht : t < 64) (s : State) (hx : s.gpr KT = s.syms kName) :
    WP isa (.block (kload t)) s fun s' =>
      s'.gpr T = (K t).setWidth 64 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v ∧
      ∀ r, r ≠ T → s'.gpr r = s.gpr r := by
  apply WP.of_runBlock
  obtain e : runBlock isa (kload t) s = some (s.write .w T (K t)) := by
    simp only [kload]
    rw [runBlock_cons, exec_kld ht hx, runStep_some, runBlock_nil]
  refine ⟨_, e, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [RegUpd.gpr_write_self]
  · rw [RegUpd.mem_write]
  · rw [RegUpd.rd_write]
  · rw [RegUpd.wr_write]
  · rw [RegUpd.v_write]
  · rw [RegUpd.gpr_write_of_ne _ .w _ hr]

/-! ## The 64 rounds -/

/-- Rounds invariant, relative to the state `sB` at the start of the rounds:
the low halves of the window's registers hold the last 16 words of the
schedule (the block's, in the first 16 rounds). -/
structure RInv (H : HashValue) (M : Block) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha256.rounds H M t)
  win : ∀ j, t ≤ j + 16 → (j < t ∨ j < 16) → (s.gpr (wreg j)).setWidth 32 = W M j
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
  obtain hwk : ∀ r ∈ [KT, Reg.x30], r ∉ wregs ∧ r ∉ work ∧ r ≠ T ∧ r ≠ .x1 ∧ r ≠ .x2 := by decide
  obtain ⟨k1, k2, k3, k4, k5⟩ := hwk r hr
  refine ⟨fun e => k1 (e ▸ wreg_mem t), k3, fun e => k2 (e ▸ var_mem t 7), fun e => k2 (e ▸ var_mem t 3), ?_, ?_⟩ <;>
    rcases mreg_cases t with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [e1, e2] <;> with_reducible assumption

theorem rounds_ok (H : HashValue) (M : Block) (sB : State) (hkt : sB.gpr KT = sB.syms kName)
    (hw : ∀ j, j < 16 → (sB.gpr (wreg j)).setWidth 32 = W M j) (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (rounds t) sB (RInv H M sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun j _ hj => hw j (hj.elim (fun h => absurd h (Nat.not_lt_zero _)) id),
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega_using [ht])) fun s hs => ?_)
    rw [List.append_assoc, WP.block_append_iff]
    -- The word of the schedule.
    obtain hsched : WP isa (.block (schedule t)) s fun s₁ =>
        (s₁.gpr (wreg t)).setWidth 32 = W M t ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
        s₁.v = s.v ∧ ∀ r, r ≠ wreg t → r ≠ T → s₁.gpr r = s.gpr r := by
      by_cases h16 : t < 16
      · simp only [Impl.Sha256.AArch64.schedule, h16, ite_true]
        exact WP.block_nil ⟨hs.win t (by omega_using []) (.inr h16), rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩
      · exact schedule_ok t (by omega_using [h16]) s M fun j h1 h2 => hs.win j h1 (.inl h2)
    refine VG.AArch64.WP.mono_syms hsched fun s₁ ⟨hW₁, hm₁, hrd₁, hwr₁, hv₁, hr₁⟩ hsy₁ => ?_
    obtain kn := kept_ne t
    -- The constant.
    rw [WP.block_append_iff]
    refine VG.AArch64.WP.mono_syms (kload_ok t (by omega_using [ht]) s₁
      (by rw [hr₁ KT (kn _ (by simp)).1 (kn _ (by simp)).2.1, hsy₁, hs.kt, hs.syms]; exact hkt))
      fun s₂ ⟨hK₂, hm₂, hrd₂, hwr₂, hv₂, hr₂⟩ hsy₂ => ?_
    obtain keep₂ : ∀ r ∈ work, s₂.gpr r = s.gpr r := fun r hr => by
      obtain hw := wregs_ne _ (wreg_mem t)
      rw [hr₂ r (work_ne r hr).1, hr₁ r (fun e => hw.1 (e ▸ hr)) (work_ne r hr).1]
    obtain hv₂' : Vars t s₂ (VG.Spec.Sha256.rounds H M t) := by
      have hv := hs.vars
      obtain e : ∀ k, s₂.gpr (var t k) = s.gpr (var t k) := fun k => keep₂ _ (var_mem t k)
      obtain em : s₂.gpr (mreg (t + 1)) = s.gpr (mreg (t + 1)) := by
        obtain hw := wregs_ne _ (wreg_mem t)
        have : mreg (t + 1) ≠ T ∧ mreg (t + 1) ≠ wreg t := by
          rcases mreg_cases t with ⟨-, e2⟩ | ⟨-, e2⟩ <;> rw [e2]
          · exact ⟨by decide, fun e => hw.2.2.2.1 e.symm⟩
          · exact ⟨by decide, fun e => hw.2.2.1 e.symm⟩
        rw [hr₂ _ this.1, hr₁ _ this.2 this.1]
      simp only [Vars, e, em] at hv ⊢
      exact hv
    obtain hw₂ : (s₂.gpr (wreg t)).setWidth 32 = W M t := by rw [hr₂ _ (wT t), hW₁]
    -- The round.
    refine VG.AArch64.WP.mono_syms (round_ok t s₂ _ _ _ hv₂' hK₂ hw₂)
      fun s₃ ⟨hv₃, hm₃, hrd₃, hwr₃, hvv₃, hr₃⟩ hsy₃ => ?_
    obtain kept : ∀ r ∈ [KT, Reg.x30], s₃.gpr r = s.gpr r := fun r hr => by
      obtain ⟨k1, k2, k3, k4, k5, k6⟩ := kn r hr
      rw [hr₃ r k3 k4 k2 k5 k6, hr₂ r k2, hr₁ r k1 k2]
    refine ⟨?_, fun j hj hj' => ?_, by rw [kept _ (by simp), hs.kt], by rw [kept _ (by simp), hs.x30],
      by rw [hm₃, hm₂, hm₁, hs.mem], by rw [hrd₃, hrd₂, hrd₁, hs.rd],
      by rw [hwr₃, hwr₂, hwr₁, hs.wr], by rw [hvv₃, hv₂, hv₁, hs.v], by rw [hsy₃, hsy₂, hsy₁, hs.syms]⟩
    · have e : VG.Spec.Sha256.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha256.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₃
    · have hwj := wregs_ne _ (wreg_mem j)
      obtain n7 : wreg j ≠ var t 7 := fun e => hwj.1 (e ▸ var_mem t 7)
      obtain n3 : wreg j ≠ var t 3 := fun e => hwj.1 (e ▸ var_mem t 3)
      obtain nm : wreg j ≠ mreg t ∧ wreg j ≠ mreg (t + 1) := by
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

end VG.Proof.Sha256.AArch64

/-!
# SHA-256 compression function on AArch64: the whole function
-/

namespace VG.Proof.Sha256.AArch64

open VG VG.AArch64 VG.Impl.Sha256.AArch64
open VG.Impl.Sha256.AArch64.Sha2 (kName)
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! The hash value in memory and offsets into regions (`Proof/Sha256/StateMem.lean`). -/
export VG.Proof.Sha256.StateMem (toNat_ofNat_lt contains_offset sub_offset word_sep
  readW_writeW_word stateAt_eq stateAt_get writeState stateAt_writeState)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev bp : Addr := s₀.gpr .x1
abbrev nb : Nat := (s₀.gpr .x2).toNat
abbrev scr : Addr := s₀.gpr .x3
abbrev stR : Region := ⟨st s₀, 32⟩
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

theorem pre_of (s₀ : State) (h : Proof.Sha256.compressAArch64.pre s₀) : Pre s₀ := by
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

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega_using [hk]) (by omega_using [hk])⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega_using [hk]) (by omega_using [hk])⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_add _ _ _]
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

/-! ## One block -/

/-- A byte of a field of `x` is a byte of `x`. -/
private theorem byte_extract {w : Nat} (x : BitVec w) (s n k : Nat) (h : k + 8 ≤ n) :
    (x.extractLsb' s n).extractLsb' k 8 = x.extractLsb' (s + k) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.add_assoc]
  rw [decide_eq_true (show k + i < n by omega), Bool.true_and]

/-- A byte appended is the number shifted by a byte, plus it. -/
private theorem toNat_append_byte {n : Nat} (a : BitVec n) (b : BitVec 8) :
    (a ++ b).toNat = a.toNat * 256 + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

/-- The low and the high four of eight bytes, as numbers: the two halves of `rev64` are stated about the
bytes' values, eight numbers below 256, rather than bit by bit, which is a case for every byte a bit may be
in on either side. -/
private theorem bytes8_halves (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256)
    (h3 : b3 < 256) (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    (((((((b0 * 256 + b1) * 256 + b2) * 256 + b3) * 256 + b4) * 256 + b5) * 256 + b6) * 256 + b7) % 2 ^ 32 =
        ((b4 * 256 + b5) * 256 + b6) * 256 + b7 ∧
      (((((((b0 * 256 + b1) * 256 + b2) * 256 + b3) * 256 + b4) * 256 + b5) * 256 + b6) * 256 + b7) >>> 32 %
          2 ^ 32 = ((b0 * 256 + b1) * 256 + b2) * 256 + b3 := by
  omega

/-- The low word of a byte-reversed doubleword is its high word, byte-reversed. -/
theorem rev64_lo (x : BitVec 64) : (rev64 x).setWidth 32 = rev32 (x.extractLsb' 32 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [rev64, rev32, byte_extract, Nat.reduceAdd, Nat.reduceLeDiff, BitVec.toNat_setWidth, toNat_append_byte]
  exact (bytes8_halves _ _ _ _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)).1

/-- The high word of a byte-reversed doubleword is its low word, byte-reversed. -/
theorem rev64_hi (x : BitVec 64) : (rev64 x >>> 32).setWidth 32 = rev32 (x.extractLsb' 0 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [rev64, rev32, byte_extract, Nat.reduceAdd, Nat.reduceLeDiff, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, toNat_append_byte]
  exact (bytes8_halves _ _ _ _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)).2

/-- The block's words loaded two at a time from the address `p` in `T`: each
is the low half of its register. -/
theorem loadPairs_ok (p : Addr) : ∀ (n : Nat) (s : State), n ≤ 8 → s.gpr T = p →
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
    obtain eb : s₁.gpr T = p := by rw [ho₁ T fun k _ => (wT k).symm, hb]
    obtain i1 : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr T + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [hrd₁, hwr₁, eb]; exact hin n (by omega_using [])
    obtain hne : wreg (2 * n) ≠ wreg (2 * n + 1) := wreg_ne (by omega_using [hn])
    obtain hT1 : T ≠ wreg (2 * n + 1) := (wT _).symm
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
          obtain n1 : wreg k ≠ wreg (2 * n + 1) := wreg_ne (by omega_using [hk, hn, h1])
          rw [RegUpd.gpr_write_of_ne _ .x _ n0, RegUpd.gpr_write_of_ne _ .x _ n1,
            RegUpd.gpr_write_of_ne _ .x _ n1, hk₁ k (by omega_using [hk, h0, h1])]
    · have n0 := hx (2 * n) (by omega_using [])
      obtain n1 := hx (2 * n + 1) (by omega_using [])
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
    obtain eb : s₁.gpr b = p := by rw [ho₁ b fun k hk => (hr k (by omega_using [hk])).symm, hb]
    obtain i1 : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr b + BitVec.ofNat 64 (4 * n)) 4 := by
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

/-- `loadBlock`: the block's words into the window, and the next block's
address into its lane. -/
theorem loadBlock_ok {s : State} {p : Addr} (hp : laneOf s PV 1 = p)
    (hin : ∀ i, i < 8 → InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block loadBlock) s fun s' =>
      (∀ j, j < 16 →
        (s'.gpr (wreg j)).setWidth 32 = rev32 (s.mem.readW (p + BitVec.ofNat 64 (4 * j)) 32)) ∧
      laneOf s' PV 1 = p + 64 ∧
      (∀ w l, (w ≠ PV ∨ l ≠ 1) → l < 2 → laneOf s' w l = laneOf s w l) ∧
      (∀ x, x ∉ wregs → x ≠ T → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold loadBlock
  simp only [List.cons_append, List.nil_append]
  refine umov_step (by decide) fun s₁ g₁ o₁ v₁ m₁ rd₁ wr₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPairs_ok p 8 s₁ (by decide) (g₁.trans hp) (by rw [rd₁, wr₁]; exact hin))
    fun s₂ ⟨hk₂, ho₂, m₂, rd₂, wr₂, v₂⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 64) (by decide), ?_⟩
  refine ins_step (by decide) fun s₅ g₅ m₅ rd₅ wr₅ l₅ lo₅ => WP.block_nil ⟨fun j hj => ?_, ?_, fun w l h hl => ?_,
    fun x hx hT => ?_, ?_, ?_, ?_⟩
  · rw [g₅, RegUpd.gpr_write_of_ne _ .x _ (wT j), hk₂ j (by omega_using [hj]), m₁]
  · have e : s₂.gpr T = p := by
      rw [ho₂ T (fun k _ => (wT k).symm), g₁, hp]
    rw [l₅, RegUpd.gpr_write_self, BitVec.setWidth_eq]
    simp only [State.read, Size.bits, BitVec.setWidth_eq, e]
    rfl
  · rw [lo₅ w l h hl]
    simp only [laneOf, RegUpd.v_write, v₂, v₁]
  · rw [g₅, RegUpd.gpr_write_of_ne _ .x _ hT, ho₂ x (fun k _ e => hx (e ▸ wreg_mem k)), o₁ x hT]
  · rw [m₅, RegUpd.mem_write, m₂, m₁]
  · rw [rd₅, RegUpd.rd_write, rd₂, rd₁]
  · rw [wr₅, RegUpd.wr_write, wr₂, wr₁]

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .x4 = v[0].setWidth 64 ∧ s.gpr .x5 = v[1].setWidth 64 ∧
    s.gpr .x6 = v[2].setWidth 64 ∧ s.gpr .x7 = v[3].setWidth 64 ∧
    s.gpr .x8 = v[4].setWidth 64 ∧ s.gpr .x9 = v[5].setWidth 64 ∧
    s.gpr .x10 = v[6].setWidth 64 ∧ s.gpr .x11 = v[7].setWidth 64 ∧
    s.gpr .x2 = (v[1] ^^^ v[2]).setWidth 64 := Iff.rfl

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
  refine WP.mono (ldrws_ok T (var 0) (st s₀) 8 s₁ (by decide) (g₁.trans hst)
    (fun k _ => (work_ne _ (var_mem 0 k)).1) (by decide)
    (fun k hk => by rw [rd₁, wr₁, hrd, hwr]; exact hp.in_state hk))
    fun s₂ ⟨hk₂, ho₂, m₂, rd₂, wr₂, v₂⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨_, exec_logic (op := .eor) (sz := .w) (s := s₂) (d := .x2) (n := var 0 1) (m := var 0 2),
    WP.block_nil ⟨?_, fun x hx hT h2 => ?_, ?_, ?_, ?_, ?_⟩⟩
  · have e : ∀ (y : BitVec 32) (k : Nat) (hk : k < 8),
        (s₂.write .w .x2 y).gpr (var 0 k) = ((stateAt s.mem (st s₀))[k]).setWidth 64 := fun y k hk => by
      rw [RegUpd.gpr_write_of_ne _ .w _ (work_ne _ (var_mem 0 k)).2.2.1, hk₂ k hk, m₁, stateAt_get _ _ hk]
    rw [vars0]
    refine ⟨e _ 0 (by decide), e _ 1 (by decide), e _ 2 (by decide), e _ 3 (by decide), e _ 4 (by decide),
      e _ 5 (by decide), e _ 6 (by decide), e _ 7 (by decide), ?_⟩
    rw [RegUpd.gpr_write_self]
    simp only [State.read, Size.bits, hk₂ 1 (by decide), hk₂ 2 (by decide), m₁,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
      stateAt_get _ _ (show 1 < 8 by decide),
      stateAt_get _ _ (show 2 < 8 by decide)]
  · rw [RegUpd.gpr_write_of_ne _ .w _ h2, ho₂ x (fun k _ e => hx (e ▸ var_mem 0 k)), o₁ x hT]
  · rw [RegUpd.v_write, v₂, v₁]
  · rw [RegUpd.mem_write, m₂, m₁]
  · rw [RegUpd.rd_write, rd₂, rd₁]
  · rw [RegUpd.wr_write, wr₂, wr₁]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  obtain c : ∀ k, k < 8 → (stR s₀).Contains (st s₀ + BitVec.ofNat 64 (4 * k)) (32 / 8) :=
    fun k hk => contains_offset (by omega_using [hk]) (by omega_using [hk])
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _ (c 6 ?_)).writeW ?_ _ (c 7 ?_) <;>
  simp

theorem update_eq : update ++ advance = .umov .x T PV 0 ::
    ((List.range 8).map (fun k => Instr.ldr .w (wreg k) T (4 * k)) ++
    (([.add .w .x4 .x4 .x12, .add .w .x5 .x5 .x13, .add .w .x6 .x6 .x14, .add .w .x7 .x7 .x15,
      .add .w .x8 .x8 .x16, .add .w .x9 .x9 .x17, .add .w .x10 .x10 .x19, .add .w .x11 .x11 .x20,
      .str .w .x4 .x0 (4 * 0), .str .w .x5 .x0 (4 * 1), .str .w .x6 .x0 (4 * 2),
      .str .w .x7 .x0 (4 * 3), .str .w .x8 .x0 (4 * 4), .str .w .x9 .x0 (4 * 5),
      .str .w .x10 .x0 (4 * 6), .str .w .x11 .x0 (4 * 7)] : List Instr) ++
     ([.umov .x T CV 0, .subImm .x T T 1, .vop (.ins .d2 CV 0 T)] : List Instr))) := by
  decide

/-- The hash value, in eight registers, added into the working variables and
stored at `p`. -/
theorem addStore_ok {s : State} {p : Addr} (V H : HashValue) (hx0 : s.gpr .x0 = p)
    (hv : s.gpr .x4 = V[0].setWidth 64 ∧ s.gpr .x5 = V[1].setWidth 64 ∧ s.gpr .x6 = V[2].setWidth 64 ∧
      s.gpr .x7 = V[3].setWidth 64 ∧ s.gpr .x8 = V[4].setWidth 64 ∧ s.gpr .x9 = V[5].setWidth 64 ∧
      s.gpr .x10 = V[6].setWidth 64 ∧ s.gpr .x11 = V[7].setWidth 64)
    (hh : s.gpr .x12 = H[0].setWidth 64 ∧ s.gpr .x13 = H[1].setWidth 64 ∧ s.gpr .x14 = H[2].setWidth 64 ∧
      s.gpr .x15 = H[3].setWidth 64 ∧ s.gpr .x16 = H[4].setWidth 64 ∧ s.gpr .x17 = H[5].setWidth 64 ∧
      s.gpr .x19 = H[6].setWidth 64 ∧ s.gpr .x20 = H[7].setWidth 64)
    (hout : ∀ k : Nat, k < 8 → InRegions s.wr (p + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block [.add .w .x4 .x4 .x12, .add .w .x5 .x5 .x13, .add .w .x6 .x6 .x14,
      .add .w .x7 .x7 .x15, .add .w .x8 .x8 .x16, .add .w .x9 .x9 .x17, .add .w .x10 .x10 .x19,
      .add .w .x11 .x11 .x20, .str .w .x4 .x0 (4 * 0), .str .w .x5 .x0 (4 * 1), .str .w .x6 .x0 (4 * 2),
      .str .w .x7 .x0 (4 * 3), .str .w .x8 .x0 (4 * 4), .str .w .x9 .x0 (4 * 5),
      .str .w .x10 .x0 (4 * 6), .str .w .x11 .x0 (4 * 7)]) s fun s' =>
      s'.mem = writeState s.mem p (Vector.zipWith (· + ·) V H) ∧
      (∀ x, x ∉ work → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
  obtain o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  obtain o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  obtain o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hh
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_str_w,
    State.read, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.v_write, Size.bits, hx0, o0, o1, o2, o3, o4, o5, o6, o7, v0, v1, v2, v3, v4,
    v5, v6, v7, h0, h1, h2, h3, h4, h5, h6, h7, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun x hx => ?_, trivial⟩
  · simp only [writeState, Vector.getElem_zipWith]
  · have : x ≠ .x4 ∧ x ≠ .x5 ∧ x ≠ .x6 ∧ x ≠ .x7 ∧ x ≠ .x8 ∧ x ≠ .x9 ∧ x ≠ .x10 ∧ x ≠ .x11 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hx (by decide)
    obtain ⟨n4, n5, n6, n7, n8, n9, n10, n11⟩ := this
    simp only [RegUpd.gpr_write_of_ne, n4, n5, n6, n7, n8, n9, n10, n11, not_false_eq_true]

/-- The end of a block: the hash value is updated, and the count, in its
lane and in `T`, is one less. -/
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (c : BitVec 64)
    (hv : Vars 0 s V) (hst : laneOf s PV 0 = st s₀) (hc : laneOf s CV 0 = c)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) → s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr T = c - 1 ∧ laneOf s' CV 0 = c - 1 ∧
      (∀ w l, (w ≠ CV ∨ l ≠ 0) → l < 2 → laneOf s' w l = laneOf s w l) ∧
      s'.gpr KT = s.gpr KT ∧ s'.gpr .x30 = s.gpr .x30 ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [update_eq]
  refine umov_step (by decide) fun s₁ g₁ o₁ v₁ m₁ rd₁ wr₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldrws_ok T wreg (st s₀) 8 s₁ (by decide) (g₁.trans hst) (fun k _ => wT k)
    (fun i hi j hj hij => wreg_ne (by omega_using [hi, hj, hij]))
    (fun k hk => by rw [rd₁, wr₁, hrd, hwr]; exact hp.in_state hk))
    fun s₂ ⟨hk₂, ho₂, m₂, rd₂, wr₂, v₂⟩ => ?_
  obtain hk' : ∀ (k : Nat) (hk : k < 8), s₂.gpr (wreg k) = H[k].setWidth 64 := fun k hk => by
    rw [hk₂ k hk, m₁, hH k hk]
  obtain keep₂ : ∀ x ∈ work, s₂.gpr x = s.gpr x := fun x hx => by
    obtain hw : ∀ k, x ≠ wreg k := fun k e => (wregs_ne _ (wreg_mem k)).1 (e ▸ hx)
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
  obtain lane₄ : ∀ w l, laneOf s₄ w l = laneOf s w l := fun w l => by
    simp only [laneOf, v₄, v₃, v₂, v₁]
  obtain eT : (s₄.write .x T (s₄.read .x T - BitVec.ofNat 64 1)).gpr T = c - 1 := by
    rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
    simp only [State.read, Size.bits, BitVec.setWidth_eq]
    rw [g₄]
    have : laneOf s₃ CV 0 = c := by simp only [laneOf, v₃, v₂, v₁]; exact hc
    rw [this]; rfl
  obtain other : ∀ x, x ∉ work → x ∉ wregs → x ≠ T → s₆.gpr x = s.gpr x := fun x hw hx hT => by
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
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    rev32 (s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 32) = W (blk s₀ i) t := by
  rw [W_lt _ ht, rev32_readW]
  simp only [blk, blockAt, parseBlock]
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) from
      Offset.add_add _ _ 1,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) from
      Offset.add_add _ _ 1,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 3) from
      Offset.add_add _ _ 1]

/-- The loop invariant, at the start of block `i`: the pointers and the
count are in their lanes, with the caller's callee-saved registers. -/
structure AInv (s₀ : State) (i : Nat) (s : State) : Prop where
  stp : laneOf s PV 0 = st s₀
  dp : laneOf s PV 1 = blkAddr s₀ i
  cnt : laneOf s CV 0 = BitVec.ofNat 64 (nb s₀ - i)
  saved : ∀ k ∈ saves, laneOf s k.2.1 k.2.2 = s₀.gpr k.1
  x30 : s.gpr .x30 = s₀.gpr .x30
  kt : s.gpr KT = s.syms kName
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
  refine VG.AArch64.WP.mono_syms (loadBlock_ok hL.dp (fun k hk => by rw [hL.rd, hL.wr]; exact hp.in_blk2 hi hk))
    fun s₁ ⟨hw₁, hdp₁, hl₁, ho₁, m₁, rd₁, wr₁⟩ sy₁ => ?_
  refine VG.AArch64.WP.mono_syms (load_ok hp (by rw [hl₁ PV 0 (.inr (by decide)) (by decide), hL.stp])
    (rd₁.trans hL.rd) (wr₁.trans hL.wr)) fun s₂ ⟨hv₂, ho₂, v₂, m₂, rd₂, wr₂⟩ sy₂ => ?_
  obtain keep₂ : ∀ x, x ∉ work → x ∉ wregs → x ≠ T → x ≠ .x2 → s₂.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [ho₂ x h1 h3 h4, ho₁ x h2 h3]
  obtain hkt₂ : s₂.gpr KT = s₂.syms kName := by
    rw [keep₂ KT (by decide) (by decide) (by decide) (by decide), sy₂, sy₁]; exact hL.kt
  obtain hw₂ : ∀ j, j < 16 → (s₂.gpr (wreg j)).setWidth 32 = W (blk s₀ i) j := fun j hj => by
    obtain hw := wregs_ne _ (wreg_mem j)
    rw [ho₂ _ hw.1 hw.2.1 hw.2.2.2.1, hw₁ j hj,
      hL.frame.readW (hp.blk_contains hi hj) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i j hj
  rw [m₁] at hv₂
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) s₂ hkt₂ hw₂ hv₂ 64 (Nat.le_refl _)) fun s₃ hR => ?_)
  obtain lane₃ : ∀ w l, laneOf s₃ w l = laneOf s₁ w l := fun w l => by simp only [laneOf, hR.v, v₂]
  obtain mem₃ : s₃.mem = s.mem := by rw [hR.mem, m₂, m₁]
  refine VG.AArch64.WP.mono_syms (update_ok hp _ (stateAt s.mem (st s₀)) (BitVec.ofNat 64 (nb s₀ - i)) hR.vars
    (by rw [lane₃, hl₁ PV 0 (.inr (by decide)) (by decide), hL.stp])
    (by rw [lane₃, hl₁ CV 0 (.inl (by decide)) (by decide), hL.cnt])
    (by rw [hR.rd, rd₂, rd₁, hL.rd]) (by rw [hR.wr, wr₂, wr₁, hL.wr])
    fun k hk => by rw [mem₃, stateAt_get _ _ hk]) fun s₄ h₄ sy₄ => ?_
  obtain ⟨m₄, hT₄, hc₄, hl₄, kt₄, x30₄, rd₄, wr₄⟩ := h₄
  have := hp.nb_lt
  obtain hcnt : BitVec.ofNat 64 (nb s₀ - i) - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_using [hi]),
      Nat.sub_sub]
  obtain hframe : Frame [stR s₀, scrR s₀] s₀.mem s₄.mem := by
    refine hL.frame.trans ?_
    rw [m₄, mem₃]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  obtain hA : ∀ j, j = i + 1 → AInv s₀ j s₄ := by
    rintro j rfl
    refine ⟨?_, ?_, ?_, fun k hk => ?_, ?_, ?_, by rw [rd₄, hR.rd, rd₂, rd₁, hL.rd],
      by rw [wr₄, hR.wr, wr₂, wr₁, hL.wr], hframe, ?_⟩
    · rw [hl₄ PV 0 (.inl (by decide)) (by decide), lane₃, hl₁ PV 0 (.inr (by decide)) (by decide), hL.stp]
    · rw [hl₄ PV 1 (.inl (by decide)) (by decide), lane₃, hdp₁]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec _) = BitVec.ofNat _ 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hc₄, hcnt]
    · obtain ⟨n1, n2, n3⟩ := saves_lanes k hk
      rw [hl₄ _ _ (.inl n2) n3, lane₃, hl₁ _ _ (.inl n1) n3, hL.saved k hk]
    · rw [x30₄, hR.x30, keep₂ _ (by decide) (by decide) (by decide) (by decide), hL.x30]
    · rw [kt₄, hR.kt, hkt₂, sy₄, hR.syms]
    · rw [m₄, stateAt_writeState, compressBlocks_succ, ← hL.state]
      rfl
  obtain hev : eval (.nonzero .x T) s₄ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    obtain hT' : s₄.gpr .x0 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := hT₄.trans hcnt
    simp only [eval, T, State.read, Size.bits, BitVec.setWidth_eq, hT']
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hA _ rfl⟩
  · right
    obtain hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    obtain h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this])] at h'
      exact hne h'
    exact ⟨by rw [hev]; simpa using h0, by omega_using [hi, hlast], hA _ rfl⟩

/-! ## The whole function -/

/-- The callee-saved registers are those kept in lanes, and `x30`. -/
theorem preserved_cases : ∀ r ∈ preserved, r = .x30 ∨ ∃ k ∈ saves, k.1 = r := by decide

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha256.compressAArch64.post s₀ s' := by
  refine WP.ite (s₀.gpr .x2 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    refine WP.block_nil (M := isa) ⟨fun _ _ => rfl, ?_⟩
    show stateAt s₀.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) (nb s₀)
    rw [h0]; rfl
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ AInv s₀ i s
    obtain hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .x T) s' = some false ∧ AInv s₀ (nb s₀) s') ∨
        (eval (.nonzero .x T) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi], i + 1, rfl, hi', hL'⟩
    -- The registers into their lanes, and the table's address.
    refine WP.seq ?_
    unfold enter
    rw [WP.block_append_iff]
    refine WP.mono (insOf_ok saves s₀ (by decide) (by decide)) fun t ⟨tg, tm, trd, twr, _, tl, tot⟩ => ?_
    refine ins_step (by decide) fun u₁ g₁ m₁ rd₁ wr₁ l₁ lo₁ => ins_step (by decide)
      fun u₂ g₂ m₂ rd₂ wr₂ l₂ lo₂ => ins_step (by decide) fun u₃ g₃ m₃ rd₃ wr₃ l₃ lo₃ => ?_
    rw [WP.block_cons_iff]
    refine ⟨_, exec_adrSym, WP.block_nil ?_⟩
    obtain hg : ∀ r, u₃.gpr r = s₀.gpr r := fun r => by rw [g₃, g₂, g₁, tg]
    obtain hgw : ∀ r, r ≠ KT → (u₃.write .x KT (u₃.syms kName)).gpr r = s₀.gpr r := fun r hr => by
      rw [RegUpd.gpr_write_of_ne _ .x _ hr, hg]
    obtain hlw : ∀ w l, laneOf (u₃.write .x KT (u₃.syms kName)) w l = laneOf u₃ w l := fun w l => by
      simp only [laneOf, RegUpd.v_write]
    obtain hL₀ : AInv s₀ 0 (u₃.write .x KT (u₃.syms kName)) :=
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
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 112⟩]

theorem compress_verified :
    Verified AArch64.target Impl.Sha256.AArch64.compress Proof.Sha256.compressAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he⟩, h₂⟩
  · refine LaneTaint.constantTime (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    first
    | exact Offset.disjoint_of_le (by decide) (by decide)
    | exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide))

end VG.Proof.Sha256.AArch64
