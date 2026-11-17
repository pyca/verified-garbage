module

public import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Entry
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Layout
public import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Lost

/-! ### `Ed25519.Arm.Whole.Entry`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

structure EntryStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ .r12 → r ≠ .lr → t.gpr r = s.gpr r
  syms : t.syms = s.syms

theorem EntryStep.refl (s : State) : EntryStep s s := ⟨rfl, rfl, rfl, fun _ _ _ => rfl, rfl⟩
theorem EntryStep.trans {s t u : State} (h : EntryStep s t) (h' : EntryStep t u) : EntryStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    fun r hn hl => (h'.regs r hn hl).trans (h.regs r hn hl), h'.syms.trans h.syms⟩

theorem argReg_ne12 (j : Nat) : argReg j ≠ .r12 := by unfold argReg; split <;> decide
theorem argReg_neLR (j : Nat) : argReg j ≠ .lr := by unfold argReg; split <;> decide

def inputWord (s : State) (j : Nat) : BitVec 32 :=
  if j < 4 then s.gpr (argReg j)
  else s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (280 + 4 * (j - 4)))) 32

theorem saveWord_ok {s : State} {j : Nat} (hj : j < 6)
    (hw : InRegions s.wr (State.addr (s.sp + BitVec.ofNat 32 (248 + 4 * j))) 4)
    (hr : 4 ≤ j → InRegions (s.rd ++ s.wr)
      (State.addr (s.sp + BitVec.ofNat 32 (280 + 4 * (j - 4)))) 4) :
    WP isa (.block (saveWord j)) s fun t => EntryStep s t ∧
      t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 (248 + 4 * j))) (inputWord s j) := by
  have hs : 4 * j < 4096 := by omega_using [hj]
  have ha : BitVec.ofNat 32 248 + BitVec.ofNat 32 (4 * j) = BitVec.ofNat 32 (248 + 4 * j) :=
    (BitVec.ofNat_add 248 (4 * j)).symm
  by_cases h4 : j < 4
  · apply WP.of_runBlock
    simp only [saveWord, ite_true, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, State.store32, Nat.reduceLT, hs, ite_true, RegUpd.gpr_setReg, RegUpd.wr_setReg,
      RegUpd.mem_setReg, RegUpd.sp_setReg, argReg_ne12, ite_false, BitVec.add_assoc, ha,
      hw, Option.some.injEq, exists_eq_left', inputWord, h4, ite_true]
    refine ⟨⟨rfl, rfl, rfl, ?_, rfl⟩, True.intro⟩
    intro r hn _
    simp only [RegUpd.gpr_setReg, hn, ite_false]
  · have hl : 280 + 4 * (j - 4) < 4096 := by omega_using [hj]
    have hr' := hr (by omega_using [h4])
    apply WP.of_runBlock
    simp only [saveWord, ite_false, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
      Nat.reduceLT, reduceCtorEq, hs, hl, ite_true, hr', Option.map_some, RegUpd.gpr_setReg,
      RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.sp_setReg, BitVec.add_assoc, ha,
      hw, Option.some.injEq, exists_eq_left', inputWord, h4, ite_false]
    refine ⟨⟨rfl, rfl, rfl, ?_, rfl⟩, True.intro⟩
    intro r hn hlr
    simp only [RegUpd.gpr_setReg, hn, hlr, ite_false]

structure Saved (s : State) (n : Nat) (t : State) : Prop where
  step : EntryStep s t
  frame : Frame [⟨State.addr s.sp + 248, 24⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (State.addr s.sp + BitVec.ofNat 64 (248 + 4 * j)) 32 = inputWord s j

theorem Saved.input_word {s t : State} {n j : Nat} (h : Saved s n t)
    (_hj : j < 6) (hf : s.sp.toNat + 280 + 4 * (j - 4) < 2 ^ 32) : inputWord t j = inputWord s j := by
  unfold inputWord
  split
  · exact h.step.regs _ (argReg_ne12 _) (argReg_neLR _)
  · rw [h.step.sp]
    refine h.frame.readW (r := ⟨State.addr (s.sp + BitVec.ofNat 32 (280 + 4 * (j - 4))), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    rintro r hr
    rw [List.mem_singleton.mp hr, addr_add (by omega_using [hf])]
    exact Offset.disjoint _ (d := 280 + 4 * (j - 4)) (e := 248)
      (by omega_using []) (by omega_using [_hj]) (by omega_using [])

theorem saveArgs_ok {s : State} : ∀ n ≤ 6,
    s.sp.toNat + 280 + 4 * (n - 4) ≤ 2 ^ 32 →
    (⟨State.addr s.sp + 248, 24⟩ : Region) ∈ s.wr →
    (∀ j < n, 4 ≤ j → InRegions (s.rd ++ s.wr)
      (State.addr (s.sp + BitVec.ofNat 32 (280 + 4 * (j - 4)))) 4) →
    WP isa (.block (saveArgs n)) s (Saved s n)
  | 0, _, _, _, _ => WP.block_nil ⟨.refl s, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn, hf, hw, hr => by
    rw [saveArgs, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (saveArgs_ok n (by omega_using [hn]) (by omega_using [hf]) hw (fun j hj => hr j (by omega_using [hj]))) fun u hu => ?_
    have he : State.addr (u.sp + BitVec.ofNat 32 (248 + 4 * n)) =
        State.addr s.sp + BitVec.ofNat 64 (248 + 4 * n) := by
      rw [hu.step.sp, addr_add (by omega_using [hf])]
    have uw : InRegions u.wr (State.addr (u.sp + BitVec.ofNat 32 (248 + 4 * n))) 4 := by
      rw [he, hu.step.wr]
      exact ⟨_, hw, Offset.contains _ (e := 248) (k := 24) (by omega_using []) (by omega_using [hn]) (by decide)⟩
    have ur : 4 ≤ n → InRegions (u.rd ++ u.wr)
        (State.addr (u.sp + BitVec.ofNat 32 (280 + 4 * (n - 4)))) 4 := by
      intro h4
      rw [hu.step.sp, hu.step.rd, hu.step.wr]
      exact hr n (by omega_using []) h4
    refine WP.mono (saveWord_ok (by omega_using [hn]) uw ur) fun t ⟨ht, mt⟩ => ?_
    have hi : inputWord u n = inputWord s n := by
      by_cases h4 : n < 4
      · simp only [inputWord, h4, ite_true]
        exact hu.step.regs _ (argReg_ne12 _) (argReg_neLR _)
      · exact hu.input_word (by omega_using [hn]) (by omega_using [hf, h4])
    rw [he, hi] at mt
    refine ⟨hu.step.trans ht, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (e := 248) (k := 24) (by omega_using []) (by omega_using [hn]) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep ?_ (by decide)]
        · exact hu.words j (by omega_using [hj, hjn])
        · exact Offset.sep _ (by omega_using [hjn]) (by omega_using [hn, hj]) (by omega_using [hn])

end VG.Proof.Ed25519.Arm.Whole

end

end


/-! Merged from `Proof.Ed25519.Arm.Whole.WrapSaved`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.Arm.Whole.WrapGeometry`. -/
section
namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

abbrev base (s : State) : BitVec 32 := s.sp - 280
abbrev entered (s : State) : State := allocated 248 (allocated 24 (pushed [.r12] (pushed [.lr] s)))
abbrev bodyRd (s : State) : List Region := s.rd ++ [ARGS (base s)]
abbrev bodyWr (s : State) : List Region := FR (base s) :: s.wr
abbrev stack (s : State) : Region := ⟨State.addr (base s), 280⟩

theorem entered_sp (s : State) : (entered s).sp = base s := by
  change s.sp - 4#32 - 4#32 - 24#32 - 248#32 = s.sp - 280
  simp only [BitVec.sub_sub]
  rfl

theorem base_args (s : State) : base s + 248#32 = s.sp - 4#32 - 4#32 - 24#32 := by
  simp only [base, BitVec.sub_sub]
  change s.sp - 280#32 + 248#32 = s.sp - 32#32
  rw [show (280#32) = 32#32 + 248#32 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_pad (s : State) : base s + 272#32 = s.sp - 4#32 - 4#32 := by
  simp only [base, BitVec.sub_sub]
  change s.sp - 280#32 + 272#32 = s.sp - 8#32
  rw [show (280#32) = 8#32 + 272#32 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_lr (s : State) : base s + 276#32 = s.sp - 4#32 := by
  change s.sp - 280#32 + 276#32 = s.sp - 4#32
  rw [show (280#32) = 4#32 + 276#32 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_top {s : State} (h : 280 ≤ s.sp.toNat) : (base s).toNat + 280 = s.sp.toNat := by
  change (s.sp - 280#32).toNat + 280 = s.sp.toNat
  rw [BitVec.toNat_sub_of_le (by change 280 ≤ s.sp.toNat; exact h)]
  change s.sp.toNat - 280 + 280 = s.sp.toNat
  omega_using [h]

theorem base_addr {s : State} (h : 280 ≤ s.sp.toNat) :
    State.addr (base s) = State.addr s.sp - 280 := by
  have e : base s + 280#32 = s.sp := BitVec.sub_add_cancel _ _
  have ha := addr_add (a := base s) (k := 280) (by rw [base_top h]; exact s.sp.isLt)
  rw [e] at ha
  rw [ha]
  exact (BitVec.add_sub_cancel _ _).symm

theorem entered_wr {s : State} (h : 280 ≤ s.sp.toNat) :
    (entered s).wr = FR (base s) :: ARGS (base s) ::
      ⟨State.addr (base s) + 272, 4⟩ :: ⟨State.addr (base s) + 276, 4⟩ :: s.wr := by
  have hb := base_top h
  have hs := s.sp.isLt
  change ⟨State.addr (entered s).sp, 248⟩ ::
    ⟨State.addr (s.sp - 4#32 - 4#32 - 24#32), 24⟩ ::
    ⟨State.addr (s.sp - 4#32 - 4#32), 4⟩ :: ⟨State.addr (s.sp - 4#32), 4⟩ :: s.wr = _
  rw [entered_sp, ← base_args, ← base_pad, ← base_lr,
    addr_add (by omega_using [hb]), addr_add (by omega_using [hb]), addr_add (by omega_using [hb])]
  rfl

theorem entered_mem {s : State} (h : 280 ≤ s.sp.toNat) :
    (entered s).mem = (s.mem.writeW (State.addr (base s) + 276) (s.gpr .lr)).writeW
      (State.addr (base s) + 272) (s.gpr .r12) := by
  have hb := base_top h
  have hs := s.sp.isLt
  change (s.mem.writeW (State.addr (s.sp - 4#32)) (s.gpr .lr)).writeW
    (State.addr (s.sp - 4#32 - 4#32)) (s.gpr .r12) = _
  rw [← base_pad, ← base_lr, addr_add (by omega_using [hb]), addr_add (by omega_using [hb])]
  rfl

end VG.Proof.Ed25519.Arm.Whole
end

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

theorem entered_frame {s : State} (h : 280 ≤ s.sp.toNat) :
    Frame [stack s] s.mem (entered s).mem := by
  rw [entered_mem h]
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base _ (by decide : 276 + 4 ≤ 280) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide : 272 + 4 ≤ 280) (by decide))

theorem saved_ctx {s p : State} {n : Nat} (hs : Saved (entered s) n p) :
    Ctx (base s) s.gpr p.mem (bodyRd s) s.wr (p.withRegions (bodyRd s) (bodyWr s)) := by
  refine ⟨rfl, rfl, hs.step.sp.trans (entered_sp s), ?_, Frame.refl _ _⟩
  intro r hr hlr
  exact hs.step.regs r (by intro h; subst r; simp [preserved] at hr) hlr

theorem saved_frame {s p : State} {n : Nat} (h : 280 ≤ s.sp.toNat) (hs : Saved (entered s) n p) :
    Frame [stack s] s.mem p.mem := by
  refine (entered_frame h).trans (Frame.sub hs.frame fun r hr => ?_)
  rw [List.mem_singleton.mp hr, entered_sp]
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide : 248 + 24 ≤ 280)⟩

def originalWord (s : State) (j : Nat) : BitVec 32 :=
  if j < 4 then s.gpr (argReg j)
  else s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 32

theorem input_entered {s : State} {j : Nat} (hs : 280 ≤ s.sp.toNat)
    (_hj : j < 6) (ht : s.sp.toNat + 4 * (j - 4) < 2 ^ 32) :
    inputWord (entered s) j = originalWord s j := by
  unfold inputWord originalWord
  split
  · rfl
  · have e : (entered s).sp + BitVec.ofNat 32 (280 + 4 * (j - 4)) =
        s.sp + BitVec.ofNat 32 (4 * (j - 4)) := by
      rw [entered_sp, BitVec.ofNat_add, ← BitVec.add_assoc]
      change s.sp - 280#32 + 280#32 + _ = _
      rw [BitVec.sub_add_cancel]
    rw [e]
    have hb := base_top hs
    have ae : State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4))) =
        State.addr (base s) + BitVec.ofNat 64 (280 + 4 * (j - 4)) := by
      rw [← e, entered_sp, addr_add (by omega_using [ht, hb])]
    refine (entered_frame hs).readW (r := ⟨State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4))), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    rintro r hr
    rw [List.mem_singleton.mp hr, ae]
    exact Offset.disjoint_base _ (by omega_using []) (by omega_using [_hj])

theorem saved_words {s p : State} {n j : Nat} (hs : 280 ≤ s.sp.toNat)
    (hn : n ≤ 6) (ht : s.sp.toNat + 4 * (n - 4) ≤ 2 ^ 32)
    (hp : Saved (entered s) n p) (hj : j < n) :
    p.mem.readW (State.addr (base s) + BitVec.ofNat 64 (248 + 4 * j)) 32 = originalWord s j := by
  have h := hp.words j hj
  rw [entered_sp] at h
  refine h.trans (input_entered hs (by omega_using [hn, hj]) ?_)
  by_cases h4 : j < 4
  · have hi := s.sp.isLt
    omega_using [ht, hj]
  · omega_using [ht, hj]

/-- Widen permissions around a body while retaining its precise write frame. -/
theorem narrow {c : Prog isa} {s : State} {rd wr : List Region} {P Q : State → Prop}
    (h : WP isa c (s.withRegions rd wr) P)
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr)
    (hQ : ∀ u, u.rd = rd → u.wr = wr → u.sp = s.sp → Frame wr s.mem u.mem → P u →
      Q (u.withRegions s.rd s.wr)) (hn : c.noFrames = true) : WP isa c s Q := by
  obtain ⟨t, u, he, hp⟩ := h
  obtain ⟨hr, hw', hs, hf⟩ := Exec.regions he hn
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) hc hw
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  exact ⟨t, _, he', hQ u hr hw' hs hf hp⟩

theorem enter_save {s : State} {n : Nat} (hcount : n ≤ 6) (hsp : 280 ≤ s.sp.toNat)
    (htop : s.sp.toNat + 4 * (n - 4) ≤ 2 ^ 32)
    (hr : ∀ j < n, 4 ≤ j → InRegions (s.rd ++ s.wr)
      (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 4) :
    WP isa (.block (saveArgs n)) (entered s) (Saved (entered s) n) := by
  have he : (entered s).sp.toNat + 280 + 4 * (n - 4) ≤ 2 ^ 32 := by
    rw [entered_sp, base_top hsp]
    exact htop
  have ha : (⟨State.addr (entered s).sp + 248, 24⟩ : Region) ∈ (entered s).wr := by
    rw [entered_sp, entered_wr hsp]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have hsread : ∀ j < n, 4 ≤ j → InRegions ((entered s).rd ++ (entered s).wr)
      (State.addr ((entered s).sp + BitVec.ofNat 32 (280 + 4 * (j - 4)))) 4 := by
    intro j hj h4
    rw [entered_sp, BitVec.ofNat_add, ← BitVec.add_assoc]
    change InRegions _ (State.addr (s.sp - 280#32 + 280#32 + _)) _
    rw [BitVec.sub_add_cancel]
    obtain ⟨r, hR, hC⟩ := hr j hj h4
    refine ⟨r, ?_, hC⟩
    change r ∈ s.rd ++ (entered s).wr
    rw [entered_wr hsp]
    exact List.mem_append.mpr (List.mem_append.mp hR |>.imp id fun h =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))))
  exact saveArgs_ok n hcount he ha hsread

end VG.Proof.Ed25519.Arm.Whole
end

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

attribute [local instance_reducible] freed

/-- What the releases leave, whatever memory and unknowns each leaves. -/
def finishL (u : State) (m₁ m₂ m₃ m₄ : Mem) (u₁ u₂ u₃ u₄ : Nat → BitVec 32) : State :=
  { popped .lr 4 { popped .r12 4 { freed 24 { freed 248 u with mem := m₁, unknowns := u₁ }
    with mem := m₂, unknowns := u₂ } with mem := m₃, unknowns := u₃ } with mem := m₄, unknowns := u₄ }

section
variable {u : State} {m₁ m₂ m₃ m₄ : Mem} {u₁ u₂ u₃ u₄ : Nat → BitVec 32}

theorem finishL_mem : (finishL u m₁ m₂ m₃ m₄ u₁ u₂ u₃ u₄).mem = m₄ := rfl
theorem finishL_sp : (finishL u m₁ m₂ m₃ m₄ u₁ u₂ u₃ u₄).sp = u.sp + 280#32 := by
  change u.sp + 248#32 + 24#32 + 4#32 + 4#32 = _
  simp only [BitVec.add_assoc]
  rfl

theorem finishL_gpr {r : Reg} (h12 : r ≠ .r12) (hl : r ≠ .lr) :
    (finishL u m₁ m₂ m₃ m₄ u₁ u₂ u₃ u₄).gpr r = u.gpr r := by
  change (popped .lr 4 { popped .r12 4 { freed 24 { freed 248 u with mem := m₁, unknowns := u₁ }
    with mem := m₂, unknowns := u₂ } with mem := m₃, unknowns := u₃ }).gpr r = _
  rw [popped_gpr hl]
  change (popped .r12 4 { freed 24 { freed 248 u with mem := m₁, unknowns := u₁ }
    with mem := m₂, unknowns := u₂ }).gpr r = _
  rw [popped_gpr h12]
  rfl

theorem finishL_lr :
    (finishL u m₁ m₂ m₃ m₄ u₁ u₂ u₃ u₄).gpr .lr = m₃.readW (State.addr (u.sp + 276#32)) 32 := by
  change m₃.readW (State.addr (u.sp + 248#32 + 24#32 + 4#32)) 32 = _
  simp only [BitVec.add_assoc]
  rfl

end

theorem saved_lr {s p : State} {n : Nat} (hsp : 280 ≤ s.sp.toNat) (hp : Saved (entered s) n p) :
    p.mem.readW (State.addr (base s) + 276) 32 = s.gpr .lr := by
  rw [hp.frame.readW (r := ⟨State.addr (base s) + 276, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
  · rw [entered_mem hsp, Mem.readW_writeW_sep ?_ (by decide)]
    · exact Mem.readW_writeW_self32 _ _ _
    · exact Offset.sep _ (by decide) (by decide) (by decide)
  · rintro r hr
    rw [List.mem_singleton.mp hr, entered_sp]
    exact Offset.disjoint _ (d := 276) (e := 248) (by decide) (by decide) (by decide)

theorem wrap_ok {body : Prog isa} (hn : body.noFrames = true) {s : State} {n : Nat}
    (hcount : n ≤ 6) (hsp : 280 ≤ s.sp.toNat)
    (htop : s.sp.toNat + 4 * (n - 4) ≤ 2 ^ 32)
    (hr : ∀ j < n, 4 ≤ j → InRegions (s.rd ++ s.wr)
      (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 4)
    (hw : ∀ r ∈ s.wr, (stack s).Disjoint r)
    {P : Mem → Mem → BitVec 32 → Prop}
    (hb : ∀ p, Saved (entered s) n p →
      WP isa body (p.withRegions (bodyRd s) (bodyWr s)) fun u =>
        Ctx (base s) s.gpr p.mem (bodyRd s) s.wr u ∧ P p.mem u.mem (u.gpr .r0))
    (hP : ∀ m m₁ m₂ r, Frame [stack s] m₁ m₂ → P m m₁ r → P m m₂ r) :
    WP isa (wrap n body) s fun t => abiPreserved s t ∧
      ∃ m, Frame [stack s] s.mem m ∧ P m t.mem (t.gpr .r0) := by
  refine WP.frameLost (by decide) (by change 4 ≤ s.sp.toNat; omega_using [hsp]) (by decide) ?_
  refine WP.frameLost (by decide) ?_ (by decide) ?_
  · change 4 ≤ (s.sp - 4#32).toNat
    rw [BitVec.toNat_sub_of_le (by change 4 ≤ s.sp.toNat; omega_using [hsp])]
    change 4 ≤ s.sp.toNat - 4
    omega_using [hsp]
  · refine WP.allocLost (by decide) ?_ ?_
    · change 24 ≤ (s.sp - 4#32 - 4#32).toNat
      rw [BitVec.sub_sub]
      change 24 ≤ (s.sp - 8#32).toNat
      rw [BitVec.toNat_sub_of_le (by change 8 ≤ s.sp.toNat; omega_using [hsp])]
      change 24 ≤ s.sp.toNat - 8
      omega_using [hsp]
    · refine WP.allocLost (by decide) ?_ ?_
      · change 248 ≤ (s.sp - 4#32 - 4#32 - 24#32).toNat
        simp only [BitVec.sub_sub]
        change 248 ≤ (s.sp - 32#32).toNat
        rw [BitVec.toNat_sub_of_le (by change 32 ≤ s.sp.toNat; omega_using [hsp])]
        change 248 ≤ s.sp.toNat - 32
        omega_using [hsp]
      · refine WP.seq (WP.mono (enter_save hcount hsp htop hr) fun p hp => ?_)
        refine narrow (hb p hp) ?_ ?_ ?_ hn
        · refine Covers.of_sub fun r hR => ?_
          rw [hp.step.rd, hp.step.wr, entered_wr hsp]
          simp only [bodyRd, bodyWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hR
          rcases hR with (hR | rfl) | (rfl | hR)
          · exact ⟨r, List.mem_append_left _ hR, 0, by simp⟩
          · exact ⟨ARGS (base s), List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp⟩
          · exact ⟨FR (base s), List.mem_append_right _ List.mem_cons_self, 0, by simp⟩
          · exact ⟨r, List.mem_append_right _ (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hR)))), 0, by simp⟩
        · refine Covers.of_sub fun r hR => ?_
          rw [hp.step.wr, entered_wr hsp]
          simp only [bodyWr, List.mem_cons] at hR
          rcases hR with rfl | hR
          · exact ⟨FR (base s), List.mem_cons_self, 0, by simp⟩
          · exact ⟨r, by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hR))), 0, by simp⟩
        · intro u _ _ _ _ hbody m₁ u₁ h₁ m₂ u₂ h₂ m₃ u₃ h₃ m₄ u₄ h₄
          obtain ⟨hc, ho⟩ := hbody
          -- The four released frames are the entry's regions.
          have e := entered_wr hsp
          change ⟨State.addr (entered s).sp, 248⟩ :: ⟨State.addr (s.sp - 4#32 - 4#32 - 24#32), 24⟩ ::
            ⟨State.addr (s.sp - 4#32 - 4#32), 4⟩ :: ⟨State.addr (s.sp - 4#32), 4⟩ :: s.wr = _ at e
          simp only [List.cons.injEq] at e
          obtain ⟨e₁, e₂, e₃, e₄, -⟩ := e
          change Frame [⟨State.addr (entered s).sp, 248⟩] u.mem m₁ at h₁
          change Frame [⟨State.addr (s.sp - 4#32 - 4#32 - 24#32), 24⟩] m₁ m₂ at h₂
          change Frame [⟨State.addr (s.sp - 4#32 - 4#32), 4⟩] m₂ m₃ at h₃
          change Frame [⟨State.addr (s.sp - 4#32), 4⟩] m₃ m₄ at h₄
          rw [e₁] at h₁; rw [e₂] at h₂; rw [e₃] at h₃; rw [e₄] at h₄
          have inner : Frame [⟨State.addr (base s), 276⟩] u.mem m₃ := by
            refine ((h₁.sub fun r hr => ?_).trans (h₂.sub fun r hr => ?_)).trans (h₃.sub fun r hr => ?_) <;>
              rw [List.mem_singleton.mp hr] <;> refine ⟨_, List.mem_singleton_self _, ?_⟩
            · exact Region.sub_prefix (by decide)
            · exact Offset.sub_base _ (by decide)
            · exact Offset.sub_base _ (by decide)
          have whole : Frame [stack s] u.mem m₄ :=
            (inner.sub fun r hr => by
              rw [List.mem_singleton.mp hr]
              exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩).trans
            (h₄.sub fun r hr => by
              rw [List.mem_singleton.mp hr]
              exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩)
          have lr : m₃.readW (State.addr (base s) + 276) 32 = s.gpr .lr := by
            rw [inner.readW (r := ⟨State.addr (base s) + 276, 4⟩) (Region.contains_self _ _) (fun r hr => by
              rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)) (by decide)]
            rw [hc.frame.readW (r := ⟨State.addr (base s) + 276, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
            · exact saved_lr hsp hp
            · intro r hR
              simp only [List.mem_append, List.mem_singleton] at hR
              rcases hR with hR | rfl
              · exact (hw r hR).sub_left (Offset.sub_base _ (by decide : 276 + 4 ≤ 280))
              · exact Offset.disjoint_base _ (by decide) (by decide)
          change abiPreserved s (finishL (u.withRegions p.rd p.wr) m₁ m₂ m₃ m₄ u₁ u₂ u₃ u₄) ∧
            ∃ m, Frame [stack s] s.mem m ∧ P m (finishL (u.withRegions p.rd p.wr) m₁ m₂ m₃ m₄ u₁ u₂ u₃ u₄).mem
              ((finishL (u.withRegions p.rd p.wr) m₁ m₂ m₃ m₄ u₁ u₂ u₃ u₄).gpr .r0)
          refine ⟨⟨?_, ?_⟩, p.mem, saved_frame hsp hp, ?_⟩
          · intro r hR
            by_cases hl : r = .lr
            · subst r
              rw [finishL_lr, State.withRegions_sp, hc.sp,
                addr_add (by have hb := base_top hsp; have hi := s.sp.isLt; omega_using [hb])]
              exact lr
            · rw [finishL_gpr (by intro h; subst r; simp [preserved] at hR) hl]
              exact hc.cs r hR hl
          · rw [finishL_sp, State.withRegions_sp, hc.sp]
            exact BitVec.sub_add_cancel _ _
          · rw [finishL_mem, finishL_gpr (by decide) (by decide)]
            exact hP _ _ _ _ whole ho

end VG.Proof.Ed25519.Arm.Whole
