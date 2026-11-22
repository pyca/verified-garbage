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
(`abiPreserved_ofN`).
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

/-- `CallsKeep`, which also accepts a function none of whose own instructions
(outside the functions it calls, which it checks too) writes `untouched`. -/
abbrev CallsKeepN (c : Prog isa) : Prop :=
  (c.calls.all fun nb => nb.2.allInstrs (fun i => (dsts i).all fun r => !untouched.contains r) ||
    (((straight nb.2).any fun is => untouched.all fun r => restores r is) ||
      (untouched.all fun r => nb.2.allInstrs (keepsReg r)) ||
      topAll (fun i => (dsts i).all fun r => !untouched.contains r) nb.2)) = true

theorem topAll_mono {p q : Instr → Bool} (hpq : ∀ i, p i = true → q i = true) :
    ∀ c : Prog isa, topAll p c = true → topAll q c = true := by
  intro c
  induction c with
  | icall i _ _ n _ ihn =>
    simp only [topAll, Bool.and_eq_true]; exact fun h => ⟨hpq i h.1, ihn h.2⟩
  | block is =>
    rw [topAll_block, topAll_block, List.all_eq_true, List.all_eq_true]
    exact fun h i hi => hpq i (h i hi)
  | seq a b iha ihb | ite _ a b iha ihb =>
    simp only [topAll, Bool.and_eq_true]; exact fun h => ⟨iha h.1, ihb h.2⟩
  | loop b _ ih => exact ih
  | call _ _ _ => intro _; rfl
  | frame i b j ih =>
    simp only [topAll, Bool.and_eq_true]; exact fun h => ⟨⟨hpq i h.1.1, ih h.1.2⟩, hpq j h.2⟩

/-- `gpr_top`, for functions that keep the register in their own instructions
too. -/
theorem gpr_topN {r : Reg} (hr : r ∉ linkRegs) {c : Prog isa} {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') (hc : topAll (keepsReg r) c = true)
    (hb : (c.calls.all fun nb => (straight nb.2).any (restores r) || nb.2.allInstrs (keepsReg r) ||
      topAll (keepsReg r) nb.2) = true) :
    s'.gpr r = s.gpr r := by
  induction h with
  | icall _ hc₁ e hr' ih =>
    simp only [Code.calls, List.all_append, List.all_cons, Bool.and_eq_true, Bool.or_eq_true] at hb
    rcases hb.1.1 with (hb' | hb') | hb'
    · obtain ⟨is, his, hres⟩ := (Option.any_eq_true _ _).mp hb'
      obtain ⟨_, eb⟩ := straight_exec his e
      rw [ret_eq hr', restores_ok hres eb, (call_eq hc₁).2.2.2.2 r hr]
    · rw [ret_eq hr', Exec.gpr (fun i hi => by
          have := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hb') i hi
          simpa [keepsReg] using this) e (.inr hr), (call_eq hc₁).2.2.2.2 r hr]
    · rw [ret_eq hr', ih hb' hb.1.2, (call_eq hc₁).2.2.2.2 r hr]
  | icallNext _ _ _ ih =>
    exact ih (by simp only [topAll, Bool.and_eq_true] at hc ⊢; exact hc.2)
      (by simp only [Code.calls, List.all_append, List.all_cons, Bool.and_eq_true] at hb ⊢; exact hb.2)
  | block h =>
    exact execBlock_keep (fun s : State => s.gpr r) (ok := fun i => keepsReg r i = true)
      (fun hi he => exec_gpr (by simpa [keepsReg] using hi) he)
      (List.all_eq_true.mp (by rwa [topAll_block] at hc)) h
  | seq _ _ ih₁ ih₂ =>
    simp only [topAll, Bool.and_eq_true] at hc
    simp only [Code.calls, List.all_append, Bool.and_eq_true] at hb
    rw [ih₂ hc.2 hb.2, ih₁ hc.1 hb.1]
  | iteT _ _ ih =>
    simp only [topAll, Bool.and_eq_true] at hc
    simp only [Code.calls, List.all_append, Bool.and_eq_true] at hb
    exact ih hc.1 hb.1
  | iteF _ _ ih =>
    simp only [topAll, Bool.and_eq_true] at hc
    simp only [Code.calls, List.all_append, Bool.and_eq_true] at hb
    exact ih hc.2 hb.2
  | loopExit _ _ ih => exact ih hc hb
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc hb, ih₁ hc hb]
  | call hc₁ e hr' ih =>
    simp only [Code.calls, List.all_cons, Bool.and_eq_true, Bool.or_eq_true] at hb
    rcases hb.1 with (hb' | hb') | hb'
    · obtain ⟨is, his, hres⟩ := (Option.any_eq_true _ _).mp hb'
      obtain ⟨_, eb⟩ := straight_exec his e
      rw [ret_eq hr', restores_ok hres eb, (call_eq hc₁).2.2.2.2 r hr]
    · rw [ret_eq hr', Exec.gpr (fun i hi => by
          have := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hb') i hi
          simpa [keepsReg] using this) e (.inr hr), (call_eq hc₁).2.2.2.2 r hr]
    · rw [ret_eq hr', ih hb' hb.2, (call_eq hc₁).2.2.2.2 r hr]
  | frame hp _ hq ih =>
    simp only [topAll, Bool.and_eq_true] at hc
    simp only [Code.calls] at hb
    obtain ⟨-, -, -, hg, -⟩ := push_eq hp
    rw [(pop_eq hq).2.2.2.1 r (dstOf_ne_of_clobbers (by simpa [keepsReg] using hc.2)), ih hc.1.2 hb, hg]

theorem untouched_keepN {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hn : CallsKeepN c) (hu : KeepsUntouched c) : ∀ r ∈ untouched, s'.gpr r = s.gpr r := by
  intro r h
  refine gpr_topN (by revert h; revert r; decide) he
    (topAll_mono (fun i hi => keepsReg_of_untouched h hi) c hu) ?_
  refine List.all_eq_true.mpr fun nb hnb => ?_
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hn nb hnb) with h' | h'
  · refine Bool.or_eq_true_iff.mpr (.inl (Bool.or_eq_true_iff.mpr (.inr ?_)))
    rw [Code.allInstrs_eq] at h' ⊢
    exact List.all_eq_true.mpr fun i hi => keepsReg_of_untouched h (List.all_eq_true.mp h' i hi)
  rcases Bool.or_eq_true_iff.mp h' with h' | h'
  · rcases Bool.or_eq_true_iff.mp h' with h' | h'
    · obtain ⟨is, his, hres⟩ := (Option.any_eq_true _ _).mp h'
      exact Bool.or_eq_true_iff.mpr (.inl (Bool.or_eq_true_iff.mpr
        (.inl ((Option.any_eq_true _ _).mpr ⟨is, his, List.all_eq_true.mp hres r h⟩))))
    · exact Bool.or_eq_true_iff.mpr (.inl (Bool.or_eq_true_iff.mpr (.inr (List.all_eq_true.mp h' r h))))
  · exact Bool.or_eq_true_iff.mpr (.inr
      (topAll_mono (fun i hi => keepsReg_of_untouched h hi) nb.2 h'))

/-- `abiPreserved_of`, with `CallsKeepN`. -/
theorem abiPreserved_ofN {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hn : CallsKeepN c) (hu : KeepsUntouched c) (hv : c.allInstrs keepsV = true)
    (hsv : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x30], s'.gpr r = s.gpr r) :
    abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he hv⟩
  by_cases h : r ∈ untouched
  · exact untouched_keepN he hn hu r h
  · refine hsv r ?_
    revert h
    revert r
    decide

end VG.Proof.Ecdsa.AArch64
