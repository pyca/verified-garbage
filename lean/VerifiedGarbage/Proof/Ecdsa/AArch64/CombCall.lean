module

public import VerifiedGarbage.Impl.Ecdsa.AArch64.CombCall
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves

/-!
# ECDSA on AArch64: the comb as an internal function

A call of the comb's function (`combCall`) does what the comb does
(`combCorrect_call`): its body runs from the state the call leaves
(`State.callEntry`), which differs from the caller's only in the registers a
call changes (`linkRegs`, which the comb may change too) and the flags; the
register that `LrSave` names keeps the return address through the comb,
which writes no instruction to it (`LrSave.Ok`), so that the function
returns (`WP.callBody`).

The comb's function calls functions of its own, which restore the
callee-saved registers they write (`Abi.lean`'s `restores`), so it writes
them in instructions of the functions it calls, though none of its own:
`CallsKeepN` accepts such a function, whose own instructions keep them,
since the functions it calls are among those `CallsKeepN` checks
(`abiPreserved_ofN`, `AbiOnce.lean`).
-/

@[expose] public section

namespace VG.AArch64

/-- A call of code verified in its caller's regions: the body runs from the
state the call leaves, and returns if it leaves `x30` as the call did. -/
theorem WP.callBody {name : String} {body : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa body s.callEntry fun u => u.gpr .x30 = s.callEntry.gpr .x30 ∧ Q u) :
    WP isa (.call name body) s Q := by
  obtain ⟨t, u, he, h30, hq⟩ := h
  exact ⟨_, _, Exec.call (call_callEntry s) he (by simp only [isa, ret, h30, ite_true]), hq⟩

end VG.AArch64

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

/-- What the comb must leave alone for its function to keep its return
address where `LrSave` says: `x30` itself (with no call, which would change
it), a general register the comb may change (`tcombClob`) but writes no
instruction to, or a SIMD register no instruction writes. -/
noncomputable def _root_.VG.Impl.Ecdsa.AArch64.LrSave.ok (n : Nat) (comb : Prog isa) : LrSave → Bool
  | .none => comb.noCalls && comb.allInstrs (fun i => !clobbers i .x30)
  | .gpr r => (tcombClob n).contains r && !linkRegs.contains r && r != .x0 &&
      comb.allInstrs (fun i => !clobbers i r)
  | .vec v => comb.allInstrs (fun i => vdstOf i != some v)

theorem linkRegs_tcombClob (n : Nat) : ∀ r ∈ linkRegs, r ∈ tcombClob n := by
  intro r hr
  simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp [tcombClob, combClob, clob]

/-- The comb's facts hold in a state with the same memory, regions and
symbols. -/
theorem _root_.VG.Proof.Weierstrass.AArch64.TCombFixed.of_same {K : TCombCfg} {C : Curve} {base : Addr} {size : Nat} {s t : State}
    {k : Nat} {T : Addr} {ws : List (BitVec 64)} (h : TCombFixed K C base size s k T ws)
    (hm : t.mem = s.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsy : t.syms = s.syms) :
    TCombFixed K C base size t k T ws := by
  obtain ⟨a, b, ro, z, bits, klt, tsym, ⟨trd, tval⟩, out⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, klt, ?_, ⟨?_, ?_⟩, out⟩
  · show toM _ _ (wordsVal t.mem _ _ _) = _; rw [hm]; exact a
  · show toM _ _ (wordsVal t.mem _ _ _) = _; rw [hm]; exact b
  · rw [hm]; exact ro
  · rw [hm]; exact z
  · rw [hm]; exact bits
  · rw [hsy]; exact tsym
  · rw [hrd, hwr]; exact trd
  · rw [hm]; exact tval

theorem save_gpr_ok (s : State) (r : Reg) :
    WP isa (.block [.addImm .x r .x30 0]) s fun s₁ => s₁ = s.write .x r (s.gpr .x30) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, ite_true, BitVec.setWidth_eq, BitVec.add_zero,
    Option.some.injEq, exists_eq_left']

theorem restore_gpr_ok (s : State) (r : Reg) :
    WP isa (.block [.addImm .x .x30 r 0]) s fun s₁ => s₁ = s.write .x .x30 (s.gpr r) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, ite_true, BitVec.setWidth_eq, BitVec.add_zero,
    Option.some.injEq, exists_eq_left']

theorem save_vec_ok (s : State) (v : VReg) :
    WP isa (.block [.vop (.ins .d2 v 0 .x30)]) s fun s₁ =>
      s₁ = s.setV v (setLane (s.v v) 64 0 (s.gpr .x30)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, Mont.exec_ins (show 0 < 2 by decide), runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']

theorem restore_vec_ok (s : State) (v : VReg) :
    WP isa (.block [.umov .x .x30 v 0]) s fun s₁ =>
      s₁ = s.write .x .x30 ((s.v v).extractLsb' 0 64) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, Mont.exec_umov (show 0 < 2 by decide), runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left', Nat.mul_zero]

/-- The comb's postcondition, from the caller's state `s`, for a state `u`
with the memory of one that satisfies it from `s₀`, and the registers of `s`
but `tcombClob`. -/
theorem combPost_of {c : Cfg} {base : Addr} {k : Nat} {s s₀ s₂ u : State}
    (K₀ : ∀ r, r ∉ tcombClob c.combCfg.M.n → s₀.gpr r = s.gpr r)
    (hrd₀ : s₀.rd = s.rd) (hwr₀ : s₀.wr = s.wr) (hsp₀ : s₀.sp = s.sp) (hm₀ : s₀.mem = s.mem)
    (K₂ : ∀ r, r ∉ tcombClob c.combCfg.M.n → u.gpr r = s₂.gpr r)
    (hrd₂ : u.rd = s₂.rd) (hwr₂ : u.wr = s₂.wr) (hsp₂ : u.sp = s₂.sp) (hm₂ : u.mem = s₂.mem)
    (h : KeepRegs (tcombClob c.combCfg.M.n) s₀ s₂ ∧
      Unch base (combPW c) s₀.mem s₂.mem ∧
      ModOkA c.combCfg.M size c.C.p s₂.mem base ∧
      (∀ x ∈ [c.combCfg.A.x,c.combCfg.A.y,c.combCfg.A.z],
        wordsVal s₂.mem base x c.combCfg.M.n < c.C.p) ∧
      Rep c.C (tmv c.C c.combCfg.M.n base s₂ c.combCfg.A.x)
        (tmv c.C c.combCfg.M.n base s₂ c.combCfg.A.y)
        (tmv c.C c.combCfg.M.n base s₂ c.combCfg.A.z) (mul k (G c.C))) :
    KeepRegs (tcombClob c.combCfg.M.n) s u ∧
      Unch base (combPW c) s.mem u.mem ∧
      ModOkA c.combCfg.M size c.C.p u.mem base ∧
      (∀ x ∈ [c.combCfg.A.x,c.combCfg.A.y,c.combCfg.A.z],
        wordsVal u.mem base x c.combCfg.M.n < c.C.p) ∧
      Rep c.C (tmv c.C c.combCfg.M.n base u c.combCfg.A.x)
        (tmv c.C c.combCfg.M.n base u c.combCfg.A.y)
        (tmv c.C c.combCfg.M.n base u c.combCfg.A.z) (mul k (G c.C)) := by
  obtain ⟨K, U, M, L, R⟩ := h
  refine ⟨⟨fun r hr => by rw [K₂ r hr, K.gpr r hr, K₀ r hr], by rw [hrd₂, K.rd, hrd₀],
    by rw [hwr₂, K.wr, hwr₀], by rw [hsp₂, K.sp, hsp₀]⟩, by rw [hm₂, ← hm₀]; exact U,
    by rw [hm₂]; exact M, by rw [hm₂]; exact L, ?_⟩
  show Rep c.C (toM _ _ (wordsVal u.mem _ _ _)) (toM _ _ (wordsVal u.mem _ _ _))
    (toM _ _ (wordsVal u.mem _ _ _)) _
  rw [hm₂]; exact R

theorem not_true_eq {b : Bool} (h : (!b) = true) : b = false := by
  cases b <;> simp_all

theorem write_x_self (s : State) (r : Reg) (v : BitVec 64) : (s.write .x r v).gpr r = v := by
  simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq]

/-- A call of the comb's function does what the comb does. -/
theorem combCorrect_call {c : Cfg} {comb : Prog isa} (hcomb : CombCorrect c comb)
    {name : String} {lr : LrSave} (hk : lr.ok c.combCfg.M.n comb = true) :
    CombCorrect c (combCall name lr comb) := by
  intro base k T s hs hm hf
  obtain hL := linkRegs_tcombClob c.combCfg.M.n
  obtain K₀ : ∀ r, r ∉ tcombClob c.combCfg.M.n → s.callEntry.gpr r = s.gpr r :=
    fun r hr => State.callEntry_gpr s fun h => hr (hL r h)
  obtain hs₀ : Scr s.callEntry base size :=
    ⟨by rw [State.callEntry_gpr s (by decide)]; exact hs.x0, by rw [State.callEntry_wr]; exact hs.wr,
      hs.nowrap, hs.enc⟩
  obtain hm₀ : ModOkA c.combCfg.M size c.C.p s.callEntry.mem base := by
    rw [State.callEntry_mem]; exact hm
  obtain hf₀ : TCombFixed c.combCfg c.C base size s.callEntry k T c.combWords :=
    hf.of_same (State.callEntry_mem s) (State.callEntry_rd s) (State.callEntry_wr s) rfl
  unfold combCall
  refine WP.callBody ?_
  cases lr with
  | none =>
    obtain ⟨hnc, hx⟩ := Bool.and_eq_true _ _ ▸ hk
    obtain ⟨t, s₂, he, h⟩ := hcomb hs₀ hm₀ hf₀
    refine ⟨t, s₂, he, Exec.gpr (fun i hi =>
        not_true_eq (List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hx) i hi)) he (.inl hnc),
      combPost_of K₀ (State.callEntry_rd s) (State.callEntry_wr s) (State.callEntry_sp s)
        (State.callEntry_mem s) (fun _ _ => rfl) rfl rfl rfl rfl h⟩
  | gpr r =>
    simp only [LrSave.ok, Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true',
      bne_iff_ne, ne_eq] at hk
    obtain ⟨⟨⟨hrc, hrl⟩, hr0⟩, hx⟩ := hk
    obtain hrl : r ∉ linkRegs := fun h => by rw [List.contains_iff_mem.mpr h] at hrl; cases hrl
    refine WP.seq (WP.mono (save_gpr_ok _ r) fun s₁ e₁ => ?_)
    subst e₁
    obtain hs₁ : Scr (s.callEntry.write .x r (s.callEntry.gpr .x30)) base size :=
      ⟨by rw [RegUpd.gpr_write_of_ne _ _ _ (Ne.symm hr0)]; exact hs₀.x0, hs₀.wr, hs₀.nowrap, hs₀.enc⟩
    obtain ⟨t, s₂, he, h⟩ := hcomb hs₁ hm₀ (hf₀.of_same rfl rfl rfl rfl)
    obtain h₂ : s₂.gpr r = s.callEntry.gpr .x30 := by
      rw [Exec.gpr (fun i hi =>
        not_true_eq (List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hx) i hi)) he (.inr hrl)]
      exact write_x_self _ _ _
    refine WP.seq ⟨t, s₂, he, WP.mono (restore_gpr_ok s₂ r) fun s₃ e₃ => ?_⟩
    subst e₃
    refine ⟨by rw [write_x_self, h₂], combPost_of (s₀ := s.callEntry.write .x r (s.callEntry.gpr .x30))
      (fun q hq => by
        rw [RegUpd.gpr_write_of_ne _ _ _ (fun e : q = r => hq (by rw [e]; exact hrc)), K₀ q hq])
      (State.callEntry_rd s) (State.callEntry_wr s) (State.callEntry_sp s) (State.callEntry_mem s)
      (fun q hq => RegUpd.gpr_write_of_ne _ _ _ (fun e : q = .x30 => hq (by rw [e]; simp [tcombClob])))
      rfl rfl rfl rfl h⟩
  | vec v =>
    obtain hk : comb.allInstrs (fun i => vdstOf i != some v) = true := hk
    refine WP.seq (WP.mono (save_vec_ok _ v) fun s₁ e₁ => ?_)
    subst e₁
    obtain hs₁ : Scr (s.callEntry.setV v (setLane (s.callEntry.v v) 64 0 (s.callEntry.gpr .x30))) base size :=
      ⟨by rw [RegUpd.gpr_setV]; exact hs₀.x0, hs₀.wr, hs₀.nowrap, hs₀.enc⟩
    obtain ⟨t, s₂, he, h⟩ := hcomb hs₁ hm₀ (hf₀.of_same rfl rfl rfl rfl)
    obtain h₂ : (s₂.v v).extractLsb' 0 64 = s.callEntry.gpr .x30 := by
      rw [Exec.vec (fun i hi => by
        have := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hk) i hi
        exact fun e => by rw [e] at this; simp at this) he, RegUpd.v_setV_self]
      have := Mont.extract_setLane (s.callEntry.v v) (s.callEntry.gpr .x30) (i := 0) (j := 0)
        (by decide) (by decide)
      simpa using this
    refine WP.seq ⟨t, s₂, he, WP.mono (restore_vec_ok s₂ v) fun s₃ e₃ => ?_⟩
    subst e₃
    refine ⟨by rw [write_x_self, h₂], combPost_of
      (s₀ := s.callEntry.setV v (setLane (s.callEntry.v v) 64 0 (s.callEntry.gpr .x30)))
      (fun q hq => by rw [RegUpd.gpr_setV, K₀ q hq])
      (State.callEntry_rd s) (State.callEntry_wr s) (State.callEntry_sp s) (State.callEntry_mem s)
      (fun q hq => RegUpd.gpr_write_of_ne _ _ _ (fun e : q = .x30 => hq (by rw [e]; simp [tcombClob])))
      rfl rfl rfl rfl h⟩

end VG.Proof.Ecdsa.AArch64
