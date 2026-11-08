module

public import VerifiedGarbage.Proof.Sha3.Contract
public import VerifiedGarbage.Proof.Sha3.RISCV64.Contract
public import VerifiedGarbage.Proof.Sha3.RISCV64.Round
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Sha3.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.Contract
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Contract
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Round
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Wp
meta import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Words64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Keccak-f[1600] on RISC-V: the whole function

The 608-byte frame contains round constants, twenty memory lanes for each
alternating state, and saves for all twelve callee-saved registers. The
first five physical slots of each state hold the original values of the
registers used to cache those lanes (`CSaved`). Copy-in initializes the
first cache; each round checks its destination's saves and logical state
(`Round.round_ok`) and frames the other bank's saves. Copy-out reads the
first five lanes from the cache before restoring both banks.

Aligned copies use doubleword loads and stores; the byte-at-a-time paths
cover arbitrary state alignment. Both share the input-commit and logical
output-load lemmas. The external contract and stack requirement are unchanged.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64
open VG.RISCV64.Steps (wp_andi)
open VG.Spec.Sha3 (stateAt keccakF rnd RC)
open VG.Proof.Sha3 (Lanes laneAddr lane_contains foldl_succ)
open VG.Proof.Sha3.RISCV64.Round (rowReg kept round_ok check₀ check₁ keeps₀ keeps₁)
open VG.Proof.Sha3.Compl (cmpl msk)

abbrev KState := Spec.Sha3.State
/-! ## The precondition -/

section
variable (s₀ : State)

/-- The frame's base. -/
abbrev F : Addr := s₀.sp - BitVec.ofNat 64 608
abbrev st : Addr := s₀.gpr .a0
abbrev scr : Addr := s₀.gpr .a1
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev scrR : Region := ⟨scr s₀, 512⟩
abbrev frR : Region := ⟨F s₀, 608⟩
/-- Frame offset `d`. -/
abbrev off (d : Nat) : Addr := F s₀ + BitVec.ofNat 64 d
abbrev A₀ : KState := stateAt s₀.mem (st s₀)
/-- The writable regions in the frame. -/
abbrev W : List Region := [frR s₀, stR s₀, scrR s₀]

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  al : s₀.sp.toNat % 16 = 0
  sp : 608 ≤ s₀.sp.toNat
  fr_st : (frR s₀).Disjoint (stR s₀)
  fr_scr : (frR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha3.permuteRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem F_toNat : (F s₀).toNat = s₀.sp.toNat - 608 := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; have := h.sp; omega),
    BitVec.toNat_ofNat]

theorem F_al : (F s₀).toNat % 16 = 0 := by
  rw [h.F_toNat]; have := h.al; have := h.sp; omega

theorem al_off {d : Nat} (hd : d % 8 = 0) (hd' : d < 2 ^ 32) : (off s₀ d).toNat % 8 = 0 :=
  al8 h.F_al hd hd'

theorem fr_st' : ∀ r ∈ [frR s₀], (stR s₀).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.fr_st.symm

end Pre

theorem in_fr (s₀ : State) {d : Nat} (hd : d + 8 ≤ 608) : InRegions (W s₀) (off s₀ d) 8 :=
  ⟨frR s₀, List.mem_cons_self .., Offset.contains_base _ hd (by omega)⟩

theorem in_st (s₀ : State) {i : Nat} (hi : i < 25) : InRegions (W s₀) (laneAddr (st s₀) i) 8 :=
  ⟨stR s₀, by simp, lane_contains _ hi⟩

theorem off_add (s₀ : State) (a b : Nat) : off s₀ a + BitVec.ofNat 64 b = off s₀ (a + b) := by
  simp only [off]; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem laneAddr_off (s₀ : State) (a i : Nat) : laneAddr (off s₀ a) i = off s₀ (a + 8 * i) :=
  off_add s₀ a (8 * i)

/-- Frame words at separate offsets. -/
theorem rw_off (s₀ : State) (m : Mem) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 32)
    (he : e + 8 ≤ 2 ^ 32) (v : BitVec 64) :
    (m.writeW (off s₀ d) v).readW (off s₀ e) 64 = m.readW (off s₀ e) 64 :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

theorem frame_off {s₀ : State} {m m' : Mem} (hf : Frame [frR s₀] m m') {d : Nat} (hd : d + 8 ≤ 608)
    (v : BitVec 64) : Frame [frR s₀] m (m'.writeW (off s₀ d) v) :=
  hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ hd (by omega))

/-- The bank whose first five physical slots save its old register values. -/
def cacheBank (b : Bool) : Reg := if b then .a0 else .a1

def cacheOff (b : Bool) (i : Nat) : Nat := (if b then 192 else 392) + 8 * i

def CSaved (s₀ : State) (m : Mem) : Prop :=
  ∀ b i, i < 5 → m.readW (off s₀ (cacheOff b i)) 64 = s₀.gpr (cacheReg (cacheBank b) i)

def cacheRegions (s₀ : State) : List Region := [⟨off s₀ 192, 40⟩, ⟨off s₀ 392, 40⟩]

/-- The only physical state slots which still contain saved registers. -/
theorem cacheRegions_sub (s₀ : State) {m m' : Mem} (h : Frame (cacheRegions s₀) m m') :
    Frame [frR s₀] m m' := h.sub fun r hr => by
  simp only [cacheRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;>
    exact ⟨frR s₀, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩

/-- Saving registers does not overwrite constants or the two original saves. -/
theorem cacheRegions_read {s₀ : State} {m m' : Mem} (h : Frame (cacheRegions s₀) m m')
    {d : Nat} (hd : d + 8 ≤ 192 ∨ 592 ≤ d) (hd' : d + 8 ≤ 608) :
    m'.readW (off s₀ d) 64 = m.readW (off s₀ d) 64 := by
  refine h.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [cacheRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- All later prologue writes avoid the save slots. -/
theorem CSaved.write {s₀ : State} {m : Mem} (h : CSaved s₀ m) {d : Nat}
    (hd : d + 8 ≤ 192 ∨ (232 ≤ d ∧ d + 8 ≤ 392) ∨ 432 ≤ d) (hd' : d + 8 ≤ 608)
    (v : BitVec 64) : CSaved s₀ (m.writeW (off s₀ d) v) := by
  intro b i hi
  rw [rw_off s₀ _ (by cases b <;> simp only [cacheOff, Bool.false_eq_true, ite_false, ite_true] <;> omega)
    (by omega) (by cases b <;> simp only [cacheOff, Bool.false_eq_true, ite_false, ite_true] <;> omega)]
  exact h b i hi

/-- Save both banks, using precisely the slots their cached lanes vacate. -/
theorem cacheSave_ok {s₀ s : State} (hp : Pre s₀) (h6 : s.gpr .t6 = F s₀) (hwr : s.wr = W s₀)
    (hg : ∀ b i, i < 5 → s.gpr (cacheReg (cacheBank b) i) = s₀.gpr (cacheReg (cacheBank b) i)) :
    WP isa (.block cacheSave) s fun s' =>
      Mupd s s' s'.mem ∧ CSaved s₀ s'.mem ∧ Frame (cacheRegions s₀) s.mem s'.mem := by
  let Inv (k : Nat) (s' : State) : Prop :=
    Mupd s s' s'.mem ∧
    (∀ b i, i < k → s'.mem.readW (off s₀ (cacheOff b i)) 64 = s₀.gpr (cacheReg (cacheBank b) i)) ∧
    Frame (cacheRegions s₀) s.mem s'.mem
  unfold cacheSave
  refine wp_range_flatMap (M := isa) Inv (fun i t hi ⟨hm, hs, hf⟩ => ?_) 5 (Nat.le_refl _) s
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  refine wp_sd (by simp only [stOff]; omega) (a := off s₀ (192 + 8 * i))
    (by rw [hm.gpr, h6]; rfl) (hp.al_off (by omega) (by omega))
    (by rw [hm.wr, hwr]; exact in_fr s₀ (by omega)) fun t₁ u₁ => ?_
  refine wp_sd (by simp only [scrOff]; omega) (a := off s₀ (392 + 8 * i))
    (by rw [u₁.gpr, hm.gpr, h6]; rfl) (hp.al_off (by omega) (by omega))
    (by rw [u₁.wr, hm.wr, hwr]; exact in_fr s₀ (by omega)) fun t₂ u₂ => WP.block_nil ?_
  refine ⟨⟨by rw [u₂.gpr, u₁.gpr, hm.gpr], rfl, by rw [u₂.rd, u₁.rd, hm.rd],
    by rw [u₂.wr, u₁.wr, hm.wr], by rw [u₂.sp, u₁.sp, hm.sp]⟩, ?_, ?_⟩
  · intro b j hj
    by_cases he : j = i
    · subst j
      cases b
      · simp only [cacheOff, cacheBank, Bool.false_eq_true, ite_false]
        rw [u₂.mem, Mem.readW_writeW_self64, u₁.gpr, hm.gpr]
        exact hg false i hi
      · simp only [cacheOff, cacheBank, ite_true]
        rw [u₂.mem, rw_off s₀ _ (by omega) (by omega) (by omega), u₁.mem,
          Mem.readW_writeW_self64, hm.gpr]
        exact hg true i hi
    · have hj' : j < i := by omega
      rw [u₂.mem, rw_off s₀ _
        (by cases b <;> simp only [cacheOff, Bool.false_eq_true, ite_false, ite_true] <;> omega)
        (by omega) (by cases b <;> simp only [cacheOff, Bool.false_eq_true, ite_false, ite_true] <;> omega),
        u₁.mem, rw_off s₀ _
        (by cases b <;> simp only [cacheOff, Bool.false_eq_true, ite_false, ite_true] <;> omega)
        (by omega) (by cases b <;> simp only [cacheOff, Bool.false_eq_true, ite_false, ite_true] <;> omega)]
      exact hs b j hj'
  · rw [u₂.mem, u₁.mem]
    refine (hf.writeW (r := ⟨off s₀ 192, 40⟩) (by simp [cacheRegions]) _ ?_).writeW
      (r := ⟨off s₀ 392, 40⟩) (by simp [cacheRegions]) _ ?_
    · rw [← off_add]; exact Offset.contains_base _ (by omega) (by omega)
    · rw [← off_add]; exact Offset.contains_base _ (by omega) (by omega)

/-! ## The frame's contents -/

/-- The saved registers, and the round constants. -/
def Aux (s₀ : State) (m : Mem) : Prop :=
  m.readW (off s₀ 592) 64 = s₀.gpr .s0 ∧ m.readW (off s₀ 600) 64 = s₀.gpr .s1 ∧
    ∀ j < 24, m.readW (off s₀ (8 * j)) 64 = RC j

/-- Writes to a region disjoint from the constants and the saved registers keep them. -/
theorem Aux.frame {s₀ : State} {m m' : Mem} (h : Aux s₀ m) {R : Region}
    (hR : ∀ d, (d + 8 ≤ 192 ∨ 592 ≤ d) → d + 8 ≤ 608 → Region.Disjoint ⟨off s₀ d, 8⟩ R)
    (hf : Frame [R] m m') : Aux s₀ m' := by
  have e : ∀ d, (d + 8 ≤ 192 ∨ 592 ≤ d) → d + 8 ≤ 608 → m'.readW (off s₀ d) 64 = m.readW (off s₀ d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (by simpa using hR d h₁ h₂) (by decide)
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · rw [e 592 (by omega) (by omega)]; exact h.1
  · rw [e 600 (by omega) (by omega)]; exact h.2.1
  · rw [e (8 * j) (by omega) (by omega)]; exact h.2.2 j hj

/-- The copies of the state in the frame, at offsets 192 and 392, are
disjoint from the constants and the saved registers. -/
theorem copy_disjoint (s₀ : State) {a : Nat} (ha : a = 192 ∨ a = 392) {d : Nat}
    (hd : d + 8 ≤ 192 ∨ 592 ≤ d) (hd' : d + 8 ≤ 608) :
    Region.Disjoint ⟨off s₀ d, 8⟩ ⟨off s₀ a, 200⟩ :=
  Offset.disjoint _ (by omega) (by omega) (by omega)

/-! ## The prologue -/

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    {s : State} (hg : s.gpr = s₀.gpr) (hrd : s.rd = []) (hwr : s.wr = W s₀) (hsp : s.sp = F s₀)
    (hm : s.mem = s₀.mem)
    (k : ∀ s', s'.gpr .t6 = F s₀ → s'.gpr .s1 = st s₀ → s'.rd = [] → s'.wr = W s₀ →
      s'.sp = F s₀ → s'.mem.readW (off s₀ 592) 64 = s₀.gpr .s0 →
      s'.mem.readW (off s₀ 600) 64 = s₀.gpr .s1 → Frame [frR s₀] s₀.mem s'.mem →
      WP isa (.block rest) s' Q) :
    WP isa (.block (save ++ rest)) s Q := by
  simp only [save, List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  have h6 : s₁.gpr .t6 = F s₀ := by rw [u₁.gpr, hsp]; exact BitVec.add_zero _
  refine wp_sd (by decide) (a := off s₀ 592) (by rw [h6]) (hp.al_off (by decide) (by decide))
    (by rw [u₁.wr, hwr]; exact in_fr s₀ (by decide)) fun s₂ g₂ => ?_
  refine wp_sd (by decide) (a := off s₀ 600) (by rw [g₂.gpr, h6])
    (hp.al_off (by decide) (by decide))
    (by rw [g₂.wr, u₁.wr, hwr]; exact in_fr s₀ (by decide)) fun s₃ g₃ => ?_
  refine wp_mv fun s₄ u₄ => ?_
  have g₂₃ : s₃.gpr = s₁.gpr := by rw [g₃.gpr, g₂.gpr]
  refine k s₄ (by rw [u₄.other _ (by decide), g₂₃, h6]) (by rw [u₄.gpr, g₂₃, u₁.other _ (by decide), hg])
    (by rw [u₄.rd, g₃.rd, g₂.rd, u₁.rd, hrd]) (by rw [u₄.wr, g₃.wr, g₂.wr, u₁.wr, hwr])
    (by rw [u₄.sp, g₃.sp, g₂.sp, u₁.sp, hsp]) ?_ ?_ ?_
  · rw [u₄.mem, g₃.mem, g₂.mem, rw_off s₀ _ (by omega) (by omega) (by omega),
      Mem.readW_writeW_self64, u₁.other _ (by decide), hg]
  · rw [u₄.mem, g₃.mem, Mem.readW_writeW_self64, g₂.gpr, u₁.other _ (by decide), hg]
  · rw [u₄.mem, g₃.mem, g₂.mem, u₁.mem, hm]
    exact frame_off (frame_off (Frame.refl _ _) (by omega) _) (by omega) _

/-! ## The round constants -/

/-- The fold of `Spec.Sha3.RC` on any seven bits, as `rcBuild` builds it. -/
theorem rc_fold (b0 b1 b2 b3 b4 b5 b6 : Bool) :
    (List.range 7).foldl (fun RC j => if [b0, b1, b2, b3, b4, b5, b6].getD j false then
        RC ||| (1#64 <<< (2 ^ j - 1)) else RC) 0 =
      ((BitVec.ofNat 64 ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 8 else 0) +
          (if b3 then 128 else 0)) |||
        (if b4 then 1#64 <<< 15 else 0)) ||| (if b5 then 1#64 <<< 31 else 0)) |||
        (if b6 then 1#64 <<< 63 else 0) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> decide

/-- `RC k` as `rcBuild` builds it: the four low bits as a number, then bits
15, 31 and 63. -/
theorem rc_eq (k : Nat) :
    RC k = ((BitVec.ofNat 64 (rcLo k) ||| (if rcBit k 4 then 1#64 <<< 15 else 0)) |||
      (if rcBit k 5 then 1#64 <<< 31 else 0)) ||| (if rcBit k 6 then 1#64 <<< 63 else 0) :=
  rc_fold (rcBit k 0) (rcBit k 1) (rcBit k 2) (rcBit k 3) (rcBit k 4) (rcBit k 5) (rcBit k 6)

theorem rcLo_lt (k : Nat) : rcLo k < 2048 := by
  unfold rcLo; split <;> split <;> split <;> split <;> omega

/-- `orIf`: `t0 |= r` if `b`. -/
theorem orIf_ok {b : Bool} {r : Reg} {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' .t0 (s.gpr .t0 ||| (if b then s.gpr r else 0)) → WP isa (.block is) s' Q) :
    WP isa (.block (orIf b r ++ is)) s Q := by
  cases b
  · exact k s ⟨by simp, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  · exact WP.cons exec_logic (by simpa using k _ (Upd.write _ _ _))

/-- `rcHigh`: bits 15, 31 and 63 in `t3`, `t4` and `t5`. -/
theorem rcHigh_ok {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .t3 = 1#64 <<< 15 → s'.gpr .t4 = 1#64 <<< 31 → s'.gpr .t5 = 1#64 <<< 63 →
      (∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (rcHigh ++ is)) s Q := by
  simp only [rcHigh, List.cons_append, List.nil_append]
  refine WP.cons exec_lui ?_
  have u₁ := Upd.write s .t3 (sext32 ((8 : BitVec 20) ++ (0 : BitVec 12)))
  generalize s.write .t3 _ = s₁ at u₁ ⊢
  refine wp_li (imm := 1) (by decide) fun s₂ u₂ => Steps.wp_sll (by decide) fun s₃ u₃ =>
    Steps.wp_sll (by decide) fun s₄ u₄ => ?_
  have e4 : s₄.gpr .t4 = 1#64 <<< 31 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr]
  refine k s₄ ?_ e4 ?_ (fun r h3 h4 h5 => ?_) ?_ ?_ ?_ ?_
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; decide
  · rw [u₄.gpr, u₃.gpr, u₂.gpr]; decide
  · rw [u₄.other r h5, u₃.other r h4, u₂.other r h4, u₁.other r h3]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- `rcBuild k`: `RC k` in `t0`, from bits 15, 31 and 63 in `t3`–`t5`. -/
theorem rcBuild_ok (k : Nat) {s : State} (h3 : s.gpr .t3 = 1#64 <<< 15) (h4 : s.gpr .t4 = 1#64 <<< 31)
    (h5 : s.gpr .t5 = 1#64 <<< 63) {is : List Instr} {Q : State → Prop}
    (kk : ∀ s', s'.gpr .t0 = RC k → (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (rcBuild k ++ is)) s Q := by
  simp only [rcBuild, List.cons_append, List.append_assoc]
  refine wp_li (rcLo_lt k) fun s₁ u₁ => orIf_ok fun s₂ u₂ => orIf_ok fun s₃ u₃ =>
    orIf_ok fun s₄ u₄ => kk s₄ ?_ (fun r h => ?_) ?_ ?_ ?_ ?_
  · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide),
      h3, h4, h5, rc_eq]
  · rw [u₄.other r h, u₃.other r h, u₂.other r h, u₁.other r h]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- During the stores of the round constants. -/
def RcInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr .t6 = F s₀ ∧ s.gpr .s1 = st s₀ ∧ s.rd = [] ∧ s.wr = W s₀ ∧ s.sp = F s₀ ∧
    s.mem.readW (off s₀ 592) 64 = s₀.gpr .s0 ∧ s.mem.readW (off s₀ 600) 64 = s₀.gpr .s1 ∧
    (∀ j < k, s.mem.readW (off s₀ (8 * j)) 64 = RC j) ∧ Frame [frR s₀] s₀.mem s.mem

/-- `t3`–`t5` hold bits 15, 31 and 63. -/
def High (s : State) : Prop :=
  s.gpr .t3 = 1#64 <<< 15 ∧ s.gpr .t4 = 1#64 <<< 31 ∧ s.gpr .t5 = 1#64 <<< 63

theorem rcs_ok {s₀ : State} (hp : Pre s₀) (s : State) (hs : RcInv s₀ 0 s) :
    WP isa (.block rcStores) s (RcInv s₀ 24) := by
  unfold rcStores
  refine rcHigh_ok fun s₁ e3 e4 e5 o m rd wr sp => ?_
  obtain ⟨h6, h1, hrd, hwr, hsp, v₁, v₂, _, hf⟩ := hs
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s => RcInv s₀ k s ∧ High s)
    (fun k s' hk ⟨⟨h6, h1, hrd, hwr, hsp, v₁, v₂, hv, hf⟩, e3, e4, e5⟩ => ?_) 24 (Nat.le_refl _) s₁
    ⟨⟨by rw [o _ (by decide) (by decide) (by decide), h6],
      by rw [o _ (by decide) (by decide) (by decide), h1], by rw [rd, hrd], by rw [wr, hwr],
      by rw [sp, hsp], by rw [m, v₁], by rw [m, v₂], fun j hj => absurd hj (Nat.not_lt_zero _),
      by rw [m]; exact hf⟩, e3, e4, e5⟩) fun _ h => h.1
  refine rcBuild_ok k e3 e4 e5 fun s₁ g₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_
  refine wp_sd (by omega) (a := off s₀ (8 * k)) (by rw [o₁ _ (by decide), h6])
    (hp.al_off (by omega) (by omega)) (by rw [wr₁, hwr]; exact in_fr s₀ (by omega)) fun s₂ g₂ => ?_
  refine WP.block_nil ⟨⟨by rw [g₂.gpr, o₁ _ (by decide), h6],
    by rw [g₂.gpr, o₁ _ (by decide), h1], by rw [g₂.rd, rd₁, hrd],
    by rw [g₂.wr, wr₁, hwr], by rw [g₂.sp, sp₁, hsp], ?_, ?_, fun j hj => ?_, ?_⟩,
    by rw [g₂.gpr, o₁ _ (by decide), e3], by rw [g₂.gpr, o₁ _ (by decide), e4],
    by rw [g₂.gpr, o₁ _ (by decide), e5]⟩
  · rw [g₂.mem, rw_off s₀ _ (by omega) (by omega) (by omega), m₁, v₁]
  · rw [g₂.mem, rw_off s₀ _ (by omega) (by omega) (by omega), m₁, v₂]
  · rw [g₂.mem]
    by_cases e : j = k
    · subst e; rw [Mem.readW_writeW_self64, g₁]
    · rw [rw_off s₀ _ (by omega) (by omega) (by omega), m₁]; exact hv j (by omega)
  · rw [g₂.mem, m₁]; exact frame_off hf (by omega) _

/-- `laneReg` is none of the registers the copies use besides. -/
theorem laneReg_ne : ∀ i < 25, laneReg i ≠ .t1 ∧ laneReg i ≠ .t2 ∧ laneReg i ≠ .s1 ∧ laneReg i ≠ .t6 := by
  decide

theorem laneReg_row : ∀ x < 5, laneReg (20 + x) = rowReg x := by decide

theorem laneReg_ne_row : ∀ i < 25, ∀ x < 5, 20 + x < i → laneReg i ≠ rowReg x := by decide

theorem row_ne : ∀ x < 5, rowReg x ≠ .t1 ∧ rowReg x ≠ .t2 := by decide

/-- A NOT of lane `i` if it is kept complemented. -/
theorem cmplLane_ok {s : State} {r : Reg} {i : Nat} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' r (s.gpr r ^^^ msk i) → WP isa (.block is) s' Q) :
    WP isa (.block (cmplLane r i ++ is)) s Q := by
  unfold cmplLane
  split
  · rename_i hc
    have e : msk i = BitVec.allOnes 64 := by simp only [msk, hc, ite_true]
    exact wp_not fun s' u => k s' (e ▸ u)
  · rename_i hc
    have e : msk i = 0 := by simp only [msk, hc, Bool.false_eq_true, ite_false]
    exact k s ⟨by rw [e]; simp, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-- During the copies of the lanes into the frame. -/
def cval (s₀ s : State) (i : Nat) : BitVec 64 :=
  if i < 5 then s.gpr (cacheReg .a0 i) else s.mem.readW (off s₀ (192 + 8 * i)) 64

def CInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr .t6 = F s₀ ∧ s.gpr .s1 = st s₀ ∧ s.rd = [] ∧ s.wr = W s₀ ∧ s.sp = F s₀ ∧
    Aux s₀ s.mem ∧ Frame [frR s₀] s₀.mem s.mem ∧
    (∀ j (hj : j < 25), j < k → cval s₀ s j = (cmpl (A₀ s₀))[j]) ∧
    (∀ x (hx : x < 5), 20 + x < k → s.gpr (rowReg x) = (cmpl (A₀ s₀))[20 + x]) ∧ CSaved s₀ s.mem

theorem lane₀ (s₀ : State) {m : Mem} (hp : Pre s₀) (hf : Frame [frR s₀] s₀.mem m) {i : Nat}
    (hi : i < 25) : m.readW (laneAddr (st s₀) i) 64 = (A₀ s₀)[i] := by
  rw [hf.readW (lane_contains _ hi) hp.fr_st' (by decide)]
  simp [Spec.Sha3.stateAt, laneAddr]

theorem laneReg_cached : ∀ i < 5, laneReg i = cacheReg .a0 i := by decide

theorem cache_ne_lane : ∀ i < 25, ∀ j < 5, i ≠ j → cacheReg .a0 j ≠ laneReg i := by decide

theorem cache_ne_tmps : ∀ j < 5, cacheReg .a0 j ≠ .t1 ∧ cacheReg .a0 j ≠ .t2 := by decide

/-- Effects shared by the aligned and byte-at-a-time input loads. -/
structure InUpd (s₀ : State) (i : Nat) (hi : i < 25) (s t : State) : Prop where
  val : t.gpr (laneReg i) = (cmpl (A₀ s₀))[i]
  other : ∀ r, r ≠ laneReg i → r ≠ .t1 → r ≠ .t2 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem copyStore_ok {s₀ s : State} (hp : Pre s₀) {i : Nat} (hi : i < 25)
    (h6 : s.gpr .t6 = F s₀) (hwr : s.wr = W s₀) :
    WP isa (.block (if i < 5 then [] else [.store .d (laneReg i) .t6 (stOff + 8 * i)])) s
      fun t => Mupd s t (if i < 5 then s.mem else s.mem.writeW (off s₀ (192 + 8 * i)) (s.gpr (laneReg i))) := by
  by_cases hc : i < 5
  · simp only [ite_eq_left hc]
    exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp only [ite_eq_right hc]
    exact wp_sd (by simp only [stOff]; omega) (by rw [h6]; rfl) (hp.al_off (by omega) (by omega))
      (by rw [hwr]; exact in_fr s₀ (by omega)) fun _ h => WP.block_nil h

/-- Commit a loaded lane; cached lanes leave their physical save slots untouched. -/
theorem copyTail_ok {s₀ s t : State} (hp : Pre s₀) {i : Nat} (hi : i < 25)
    (h : CInv s₀ i s) (u : InUpd s₀ i hi s t) :
    WP isa (.block (if i < 5 then [] else [.store .d (laneReg i) .t6 (stOff + 8 * i)])) t (CInv s₀ (i + 1)) := by
  obtain ⟨h6, h1, hrd, hwr, hsp, haux, hf, hl, hrow, hcs⟩ := h
  obtain ⟨n1, n2, ns, n6⟩ := laneReg_ne i hi
  have g6 : t.gpr .t6 = F s₀ := by rw [u.other _ (Ne.symm n6) (by decide) (by decide), h6]
  refine WP.mono (copyStore_ok hp hi g6 (by rw [u.wr, hwr])) fun v g => ?_
  refine ⟨by rw [g.gpr, g6], by rw [g.gpr, u.other _ (Ne.symm ns) (by decide) (by decide), h1],
    by rw [g.rd, u.rd, hrd], by rw [g.wr, u.wr, hwr], by rw [g.sp, u.sp, hsp], ?_, ?_,
    fun j hj hji => ?_, fun x hx hxi => ?_, ?_⟩
  · rw [g.mem]
    by_cases hc : i < 5
    · rw [ite_eq_left hc, u.mem]; exact haux
    · rw [ite_eq_right hc, u.mem]
      exact haux.frame (fun d h₁ h₂ => copy_disjoint s₀ (.inl rfl) h₁ h₂ |>.sub_right
        (Offset.sub _ (by omega) (by omega))) ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Region.contains_self _ _))
  · rw [g.mem]
    by_cases hc : i < 5
    · rw [ite_eq_left hc, u.mem]; exact hf
    · rw [ite_eq_right hc, u.mem]; exact frame_off hf (by omega) _
  · unfold cval
    by_cases hj5 : j < 5
    · rw [ite_eq_left hj5, g.gpr]
      by_cases he : j = i
      · subst j; rw [← laneReg_cached i hj5]; exact u.val
      · obtain ⟨nt1, nt2⟩ := cache_ne_tmps j hj5
        rw [u.other _ (cache_ne_lane i hi j hj5 (Ne.symm he)) nt1 nt2]
        have h := hl j hj (by omega)
        simpa only [cval, ite_eq_left hj5] using h
    · rw [ite_eq_right hj5, g.mem]
      by_cases hc : i < 5
      · rw [ite_eq_left hc, u.mem]
        have h := hl j hj (by omega)
        simpa only [cval, ite_eq_right hj5] using h
      · rw [ite_eq_right hc]
        by_cases he : j = i
        · subst j; rw [Mem.readW_writeW_self64]; exact u.val
        · rw [u.mem, rw_off s₀ _ (by omega) (by omega) (by omega)]
          have h := hl j hj (by omega)
          simpa only [cval, ite_eq_right hj5] using h
  · rw [g.gpr]
    by_cases he : 20 + x = i
    · subst i; rw [← laneReg_row x hx]; exact u.val
    · have hne : rowReg x ≠ laneReg i := fun h => laneReg_ne_row i hi x hx (by omega) h.symm
      obtain ⟨nt1, nt2⟩ := row_ne x hx
      rw [u.other _ hne nt1 nt2]
      exact hrow x hx (by omega)
  · rw [g.mem]
    by_cases hc : i < 5
    · rw [ite_eq_left hc, u.mem]; exact hcs
    · rw [ite_eq_right hc, u.mem]
      exact hcs.write (.inr (.inl ⟨by omega, by omega⟩)) (by omega) _

theorem copyIns_ok {s₀ : State} (hp : Pre s₀) (s : State) (hs : CInv s₀ 0 s) :
    WP isa (.block ((List.range 25).flatMap copyIn)) s (CInv s₀ 25) := by
  refine wp_range_flatMap (M := isa) (CInv s₀) (fun i t hi h => ?_) 25 (Nat.le_refl _) s hs
  obtain ⟨h6, h1, hrd, hwr, hsp, haux, hf, hl, hrow, hcs⟩ := h
  obtain ⟨n1, n2, ns, n6⟩ := laneReg_ne i hi
  unfold copyIn
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Words64.loadLE64_ok (d := laneReg i) (tmp := .t1) (tmp2 := .t2) (n := .s1)
    (off := 8 * i) ns (by decide) n1 (by decide) (by decide) n2 (by omega)
    (by rw [hrd, hwr, h1]; exact in_st s₀ hi)) fun s₁ u₁ => ?_
  refine cmplLane_ok fun s₂ u₂ => ?_
  exact copyTail_ok hp hi ⟨h6, h1, hrd, hwr, hsp, haux, hf, hl, hrow, hcs⟩
    { val := by rw [u₂.gpr, u₁.gpr, h1, ← laneAddr, lane₀ s₀ hp hf hi, Round.cmpl_get _ hi]
      other := fun r hn ht1 ht2 => (u₂.other r hn).trans (u₁.other r hn ht1 ht2)
      mem := u₂.mem.trans u₁.mem, rd := u₂.rd.trans u₁.rd, wr := u₂.wr.trans u₁.wr, sp := u₂.sp.trans u₁.sp }

/-- A lane of an 8-byte aligned state is aligned. -/
theorem al_lane {p : Addr} (h : p.toNat % 8 = 0) (i : Nat) : (laneAddr p i).toNat % 8 = 0 := by
  rw [laneAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- `x & 7` is zero exactly when `x` is 8-byte aligned. -/
theorem and7 (x : BitVec 64) : (x &&& BitVec.ofInt 64 7 == 0) = decide (x.toNat % 8 = 0) := by
  have e : (x &&& BitVec.ofInt 64 7).toNat = x.toNat % 8 := by
    rw [BitVec.toNat_and, show (BitVec.ofInt 64 7).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  by_cases h : x.toNat % 8 = 0
  · rw [decide_eq_true h, beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by rw [e, h]; rfl)
  · rw [decide_eq_false h]
    exact beq_false_of_ne fun h' => h (by rw [← e, h']; rfl)

/-- The copies into the frame of an 8-byte aligned state. -/
theorem copyInsA_ok {s₀ : State} (hp : Pre s₀) (hal : (st s₀).toNat % 8 = 0) (s : State) (hs : CInv s₀ 0 s) :
    WP isa (.block ((List.range 25).flatMap copyInA)) s (CInv s₀ 25) := by
  refine wp_range_flatMap (M := isa) (CInv s₀) (fun i t hi h => ?_) 25 (Nat.le_refl _) s hs
  obtain ⟨h6, h1, hrd, hwr, hsp, haux, hf, hl, hrow, hcs⟩ := h
  unfold copyInA
  simp only [List.cons_append, List.nil_append]
  refine wp_ld (by omega) (a := laneAddr (st s₀) i) (by rw [h1]) (al_lane hal i)
    (by rw [hrd, hwr]; exact in_st s₀ hi) fun s₁ u₁ => ?_
  refine cmplLane_ok fun s₂ u₂ => ?_
  exact copyTail_ok hp hi ⟨h6, h1, hrd, hwr, hsp, haux, hf, hl, hrow, hcs⟩
    { val := by rw [u₂.gpr, u₁.gpr, lane₀ s₀ hp hf hi, Round.cmpl_get _ hi]
      other := fun r hn _ _ => (u₂.other r hn).trans (u₁.other r hn)
      mem := u₂.mem.trans u₁.mem, rd := u₂.rd.trans u₁.rd, wr := u₂.wr.trans u₁.wr, sp := u₂.sp.trans u₁.sp }

def cacheRegisters : List Reg := [.s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

theorem cacheReg_mem : ∀ b i, i < 5 → cacheReg b i ∈ cacheRegisters := by
  intro b
  by_cases hb : b = .a0
  · subst b; decide
  · simp only [cacheReg, hb, ite_false]
    decide

theorem cacheReg_ne {b r : Reg} {i : Nat} (hi : i < 5) (hr : r ∉ cacheRegisters) : cacheReg b i ≠ r := by
  intro he
  exact hr (he ▸ cacheReg_mem b i hi)

theorem cacheRegisters_cases {r : Reg} (hr : r ∈ cacheRegisters) :
    ∃ (b : Bool) (i : Fin 5), r = cacheReg (cacheBank b) i := by
  simp only [cacheRegisters, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨true, 0, rfl⟩
  · exact ⟨true, 1, rfl⟩
  · exact ⟨true, 2, rfl⟩
  · exact ⟨true, 3, rfl⟩
  · exact ⟨true, 4, rfl⟩
  · exact ⟨false, 0, rfl⟩
  · exact ⟨false, 1, rfl⟩
  · exact ⟨false, 2, rfl⟩
  · exact ⟨false, 3, rfl⟩
  · exact ⟨false, 4, rfl⟩

theorem cacheReg_inj : ∀ b c i, i < 5 → ∀ j, j < 5 →
    cacheReg (cacheBank b) i = cacheReg (cacheBank c) j → b = c ∧ i = j := by decide

theorem vLanes_congr {s t : State} {b : Reg} {p : Addr} {A : KState} (h : Round.VLanes s b p A)
    (hm : t.mem = s.mem) (hg : ∀ i < 5, t.gpr (cacheReg b i) = s.gpr (cacheReg b i)) : Round.VLanes t b p A := by
  intro i hi
  by_cases hc : i < 5
  · simp only [ite_eq_left hc]
    rw [hg i hc]
    simpa only [ite_eq_left hc] using h i hi
  · simp only [ite_eq_right hc]
    rw [hm]
    simpa only [ite_eq_right hc] using h i hi

/-- The round checks the saves in its destination; its frame keeps the other bank. -/
theorem csaved_round {s₀ : State} {m m' : Mem} (h : CSaved s₀ m) (b : Bool)
    (hs : ∀ i < 5, m'.readW (laneAddr (off s₀ (if b then 192 else 392)) i) 64 = s₀.gpr (cacheReg (cacheBank b) i))
    (hf : Frame [⟨off s₀ (if b then 192 else 392), 200⟩] m m') : CSaved s₀ m' := by
  intro c i hi
  by_cases hc : c = b
  · subst c
    simpa only [laneAddr_off, cacheOff] using hs i hi
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact h c i hi
    · simp only [List.mem_singleton] at hr
      subst r
      cases b <;> cases c
      · exact False.elim (hc rfl)
      · simp only [cacheOff, Bool.false_eq_true, ite_false, ite_true]
        exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · simp only [cacheOff, Bool.false_eq_true, ite_false, ite_true]
        exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact False.elim (hc rfl)

/-! ## The rounds -/

/-- The rounds' invariant, before iteration `j` (round `2j`): the state,
with the lanes `complLanes` complemented, in the frame at offset 192, and
its row 4 in `rowReg`. -/
structure LInv (s₀ : State) (j : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = off s₀ 192
  a1 : s.gpr .a1 = off s₀ 392
  s0 : s.gpr .s0 = off s₀ (16 * j)
  s1 : s.gpr .s1 = st s₀
  rd : s.rd = []
  wr : s.wr = W s₀
  sp : s.sp = F s₀
  state : Round.VLanes s .a0 (off s₀ 192) (cmpl ((List.range (2 * j)).foldl rnd (A₀ s₀)))
  row : ∀ x (hx : x < 5), s.gpr (rowReg x) = (cmpl ((List.range (2 * j)).foldl rnd (A₀ s₀)))[20 + x]
  aux : Aux s₀ s.mem
  frame : Frame [frR s₀] s₀.mem s.mem
  csaved : CSaved s₀ s.mem

theorem pointers_ok {s₀ : State} {s : State} (hs : CInv s₀ 25 s) :
    WP isa (.block pointers) s (LInv s₀ 0) := by
  obtain ⟨h6, h1, hrd, hwr, hsp, haux, hf, hl, hrow, hcs⟩ := hs
  simp only [pointers]
  refine wp_addSp (by decide) fun s₁ u₁ => wp_addSp (by decide) fun s₂ u₂ => wp_mv fun s₃ u₃ =>
    WP.block_nil ?_
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hsp]; rfl,
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.sp, hsp]; rfl,
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h6]; exact (BitVec.add_zero _).symm,
    by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h1],
    by rw [u₃.rd, u₂.rd, u₁.rd, hrd], by rw [u₃.wr, u₂.wr, u₁.wr, hwr],
    by rw [u₃.sp, u₂.sp, u₁.sp, hsp], fun i hi => ?_, fun x hx => ?_, m₃ ▸ haux, m₃ ▸ hf, m₃ ▸ hcs⟩
  · by_cases hc : i < 5
    · simp only [ite_eq_left hc, Nat.mul_zero, List.range_zero, List.foldl_nil]
      rw [u₃.other _ (cacheReg_ne hc (by decide)), u₂.other _ (cacheReg_ne hc (by decide)),
        u₁.other _ (cacheReg_ne hc (by decide))]
      simpa only [cval, ite_eq_left hc] using hl i hi (by omega)
    · simp only [ite_eq_right hc, Nat.mul_zero, List.range_zero, List.foldl_nil]
      rw [m₃, laneAddr_off]
      simpa only [cval, ite_eq_right hc] using hl i hi (by omega)
  · have : rowReg x ≠ .s0 ∧ rowReg x ≠ .a1 ∧ rowReg x ≠ .a0 := by revert x; decide
    rw [u₃.other _ this.1, u₂.other _ this.2.1, u₁.other _ this.2.2]
    exact hrow x hx (by omega)

/-- Where a round reads and writes. -/
theorem env (s₀ : State) {a b : Nat} (ha : a = 192 ∧ b = 392 ∨ a = 392 ∧ b = 192)
    {r : Nat} (hr : r < 24) :
    Proof.Sha3.Env [] (W s₀) (off s₀ a) (off s₀ b) (off s₀ (8 * r)) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, in_fr s₀ (by omega), Offset.disjoint _ (by omega) (by omega)
    (by omega), Offset.disjoint _ (by omega) (by omega) (by omega)⟩
  · rw [laneAddr_off]; exact in_fr s₀ (by omega)
  · rw [laneAddr_off]; exact in_fr s₀ (by omega)

theorem foldl_two (A : KState) (j : Nat) :
    (List.range (2 * (j + 1))).foldl rnd A = rnd (rnd ((List.range (2 * j)).foldl rnd A) (2 * j)) (2 * j + 1) := by
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, foldl_succ, foldl_succ]

theorem off_ne (s₀ : State) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (off s₀ a != off s₀ b) = !decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false, Bool.not_false, bne_iff_ne, ne_eq]
    exact Offset.add_ofNat_ne _ ha hb h

/-- The round's writes keep the frame's constants and saved registers. -/
theorem aux_round {s₀ : State} {m m' : Mem} (h : Aux s₀ m) {b : Nat} (hb : b = 192 ∨ b = 392)
    (hf : Frame [⟨off s₀ b, 200⟩] m m') : Aux s₀ m' :=
  h.frame (fun _ h₁ h₂ => copy_disjoint s₀ hb h₁ h₂) hf

theorem frame_round {s₀ : State} {m m' : Mem} (hf₀ : Frame [frR s₀] s₀.mem m) {b : Nat}
    (hb : b + 200 ≤ 608) (hf : Frame [⟨off s₀ b, 200⟩] m m') : Frame [frR s₀] s₀.mem m' :=
  hf₀.trans (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨frR s₀, List.mem_singleton_self _, Offset.sub_base _ hb⟩)

/-- Two rounds, from iteration `j`. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < 12) {s : State} (hL : LInv s₀ j s) :
    WP isa (.block body) s fun s' =>
      eval (.ne .s0 .a0) s' = some (!decide (j + 1 = 12)) ∧ LInv s₀ (j + 1) s' := by
  unfold body
  rw [WP.block_append_iff, WP.block_append_iff]
  have he₀ := env s₀ (a := 192) (b := 392) (.inl ⟨rfl, rfl⟩) (r := 2 * j) (by omega)
  have he₁ := env s₀ (a := 392) (b := 192) (.inr ⟨rfl, rfl⟩) (r := 2 * j + 1) (by omega)
  have ea₀ : s.gpr .s0 + BitVec.ofNat 64 (8 * 0) = off s₀ (8 * (2 * j)) := by
    rw [hL.s0, off_add, show 16 * j + 8 * 0 = 8 * (2 * j) by omega]
  refine WP.mono (round_ok check₀ keeps₀ (by decide) (by decide) 0 (by decide) (rc := RC (2 * j)) (saved := fun i => s₀.gpr (cacheReg .a1 i))
    (src := off s₀ 192) (dst := off s₀ 392) hL.a0 hL.a1 (hp.al_off (by decide) (by decide))
    (hp.al_off (by decide) (by decide)) (by rw [ea₀]; exact hp.al_off (by omega) (by omega))
    (by rw [hL.rd, hL.wr, ea₀]; exact he₀) hL.state (by intro i hi; simpa only [laneAddr_off, cacheOff, cacheBank, Bool.false_eq_true, ite_false] using hL.csaved false i hi) hL.row
    (by rw [ea₀]; exact hL.aux.2.2 (2 * j) (by omega))) fun s₁ ⟨l₁, w₁, cs₁, f₁, rd₁, wr₁, sp₁, k₁⟩ => ?_
  have csave₁ := csaved_round hL.csaved false cs₁ f₁
  have aux₁ : Aux s₀ s₁.mem := aux_round hL.aux (.inr rfl) f₁
  have ea₁ : s₁.gpr .s0 + BitVec.ofNat 64 (8 * 1) = off s₀ (8 * (2 * j + 1)) := by
    rw [k₁ .s0 (by decide), hL.s0, off_add, show 16 * j + 8 * 1 = 8 * (2 * j + 1) by omega]
  refine WP.mono (round_ok check₁ keeps₁ (by decide) (by decide) 1 (by decide) (rc := RC (2 * j + 1)) (saved := fun i => s₀.gpr (cacheReg .a0 i))
    (src := off s₀ 392) (dst := off s₀ 192)
    (by rw [k₁ .a1 (by decide)]; exact hL.a1) (by rw [k₁ .a0 (by decide)]; exact hL.a0)
    (hp.al_off (by decide) (by decide)) (hp.al_off (by decide) (by decide))
    (by rw [ea₁]; exact hp.al_off (by omega) (by omega))
    (by rw [rd₁, wr₁, hL.rd, hL.wr, ea₁]; exact he₁) l₁ (by intro i hi; simpa only [laneAddr_off, cacheOff, cacheBank, ite_true] using csave₁ true i hi) w₁
    (by rw [ea₁]; exact aux₁.2.2 (2 * j + 1) (by omega))) fun s₂ ⟨l₂, w₂, cs₂, f₂, rd₂, wr₂, sp₂, k₂⟩ => ?_
  have csave₂ := csaved_round csave₁ true cs₂ f₂
  have h0 : s₂.gpr .s0 = off s₀ (16 * j) := by rw [k₂ .s0 (by decide), k₁ .s0 (by decide), hL.s0]
  refine wp_addi (by decide) fun s₃ u₃ => WP.block_nil ⟨?_, ?_⟩
  · have e0 : s₃.gpr .s0 = off s₀ (16 * (j + 1)) := by
      rw [u₃.gpr, h0, off_add, show 16 * j + 16 = 16 * (j + 1) by omega]
    have e1 : s₃.gpr .a0 = off s₀ 192 := by
      rw [u₃.other _ (by decide), k₂ .a0 (by decide), k₁ .a0 (by decide), hL.a0]
    show some (s₃.gpr .s0 != s₃.gpr .a0) = _
    rw [e0, e1, off_ne s₀ (by omega) (by omega)]
    have : (16 * (j + 1) = 192) ↔ (j + 1 = 12) := by omega
    simp only [this]
  · have keep : ∀ r ∈ kept, r ≠ .s0 → s₃.gpr r = s.gpr r := fun r hr h1 => by
      rw [u₃.other r h1, k₂ r hr, k₁ r hr]
    have hst : cmpl (Proof.Sha3.outState (Proof.Sha3.outState ((List.range (2 * j)).foldl rnd (A₀ s₀))
        (RC (2 * j))) (RC (2 * j + 1))) = cmpl ((List.range (2 * (j + 1))).foldl rnd (A₀ s₀)) := by
      rw [Proof.Sha3.outState_eq, Proof.Sha3.outState_eq, foldl_two]
    rw [hst] at l₂ w₂
    have hrow : ∀ x < 5, rowReg x ≠ .s0 := by decide
    refine ⟨by rw [keep .a0 (by decide) (by decide), hL.a0],
      by rw [keep .a1 (by decide) (by decide), hL.a1],
      by rw [u₃.gpr, h0, off_add, show 16 * j + 16 = 16 * (j + 1) by omega],
      by rw [keep .s1 (by decide) (by decide), hL.s1],
      by rw [u₃.rd, rd₂, rd₁, hL.rd], by rw [u₃.wr, wr₂, wr₁, hL.wr], by rw [u₃.sp, sp₂, sp₁, hL.sp],
      vLanes_congr l₂ u₃.mem (fun i hi => u₃.other _ (cacheReg_ne hi (by decide))), fun x hx => ?_, ?_, ?_, u₃.mem ▸ csave₂⟩
    · rw [u₃.other _ (hrow x hx)]; exact w₂ x hx
    · rw [u₃.mem]; exact aux_round aux₁ (.inl rfl) f₂
    · rw [u₃.mem]
      exact frame_round (frame_round hL.frame (by omega) f₁) (by omega) f₂

/-! ## The epilogue -/

/-- During the copies of the lanes back into the state, from the state `sL`
the rounds leave. -/
def EInv (s₀ sL : State) (k : Nat) (s : State) : Prop :=
  s.gpr .a0 = off s₀ 192 ∧ s.gpr .s1 = st s₀ ∧ s.rd = [] ∧ s.wr = W s₀ ∧ s.sp = F s₀ ∧
    Frame [stR s₀] sL.mem s.mem ∧
    (∀ j (hj : j < 25), j < k → s.mem.readW (laneAddr (st s₀) j) 64 = (keccakF (A₀ s₀))[j]) ∧
    ∀ j < 5, s.gpr (cacheReg .a0 j) = sL.gpr (cacheReg .a0 j)

/-- Load a logical output lane, from its cache or the unchanged frame. -/
theorem outLoad_ok {s₀ sL s : State} (hp : Pre s₀) (hL : LInv s₀ 12 sL) {n i : Nat}
    (hs : EInv s₀ sL n s) (hi : i < 25) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t .t0 (cmpl (keccakF (A₀ s₀)))[i] → WP isa (.block rest) t Q) :
    WP isa (.block (ld .t0 .a0 i ++ rest)) s Q := by
  obtain ⟨h0, h1, hrd, hwr, hsp, hf, hl, hc⟩ := hs
  have hX : Round.VLanes sL .a0 (off s₀ 192) (cmpl (keccakF (A₀ s₀))) := hL.state
  unfold ld
  by_cases hi5 : i < 5
  · simp only [ite_eq_left hi5, List.cons_append, List.nil_append]
    refine wp_mv fun t u => k t ?_
    have hv : s.gpr (cacheReg .a0 i) = (cmpl (keccakF (A₀ s₀)))[i] := by
      rw [hc i hi5]
      simpa only [ite_eq_left hi5] using hX i hi
    rw [hv] at u
    exact u
  · simp only [ite_eq_right hi5, List.cons_append, List.nil_append]
    refine wp_ld (by omega) (a := off s₀ (192 + 8 * i)) (by rw [h0, off_add])
      (hp.al_off (by omega) (by omega)) (by rw [hrd, hwr]; exact in_fr s₀ (by omega)) fun t u => k t ?_
    have hv : s.mem.readW (off s₀ (192 + 8 * i)) 64 = (cmpl (keccakF (A₀ s₀)))[i] := by
      rw [← laneAddr_off, hf.readW (lane_contains _ hi) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.fr_st.sub_left (Offset.sub_base (F s₀) (d := 192) (n := 200) (k := 608) (by omega)))
        (by decide)]
      simpa only [ite_eq_right hi5] using hX i hi
    rw [hv] at u
    exact u

theorem cmpl_msk (A : KState) {i : Nat} (hi : i < 25) : (cmpl A)[i] ^^^ msk i = A[i] := by
  rw [Round.cmpl_get _ hi, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem copyOuts_ok {s₀ : State} (hp : Pre s₀) {sL : State} (hL : LInv s₀ 12 sL) (s : State)
    (hs : EInv s₀ sL 0 s) : WP isa (.block ((List.range 25).flatMap copyOut)) s (EInv s₀ sL 25) := by
  refine wp_range_flatMap (M := isa) (EInv s₀ sL)
    (fun i s' hi ⟨h0, h1, hrd, hwr, hsp, hf, hl, hcache⟩ => ?_) 25 (Nat.le_refl _) s hs
  unfold copyOut
  rw [List.append_assoc]
  refine outLoad_ok hp hL ⟨h0, h1, hrd, hwr, hsp, hf, hl, hcache⟩ hi fun s₁ u₁ => ?_
  refine cmplLane_ok fun s₂ u₂ => ?_
  have hv : s₂.gpr .t0 = (keccakF (A₀ s₀))[i] := by
    rw [u₂.gpr, u₁.gpr, cmpl_msk _ hi]
  have g1 : s₂.gpr .s1 = st s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h1]
  refine WP.mono (Words64.storeLE64_ok (v := .t0) (tmp := .t1) (tmp2 := .t2) (n := .s1) (off := 8 * i)
    (by decide) (by decide) (by decide) (by decide) (by omega)
    (by rw [u₂.wr, u₁.wr, hwr, g1]; exact in_st s₀ hi)) fun s₃ ⟨o₃, m₃, rd₃, wr₃, sp₃⟩ => ?_
  have m₂ : s₂.mem = s'.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨by rw [o₃ _ (by decide) (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h0],
    by rw [o₃ _ (by decide) (by decide), g1], by rw [rd₃, u₂.rd, u₁.rd, hrd],
    by rw [wr₃, u₂.wr, u₁.wr, hwr], by rw [sp₃, u₂.sp, u₁.sp, hsp], ?_, fun j hj hji => ?_, fun j hj => ?_⟩
  · rw [m₃, g1, m₂]
    exact hf.writeW (List.mem_singleton_self _) _ (lane_contains _ hi)
  · rw [m₃, g1, m₂]
    by_cases e : j = i
    · subst e; rw [Mem.readW_writeW_self64, hv]
    · rw [Mem.readW_writeW_sep (Proof.Sha3.lane_sep _ hj hi e) (by decide)]
      exact hl j hj (by omega)
  · obtain ⟨nt1, nt2⟩ := cache_ne_tmps j hj
    rw [o₃ _ nt1 nt2, u₂.other _ (cacheReg_ne hj (by decide)), u₁.other _ (cacheReg_ne hj (by decide))]
    exact hcache j hj

/-- The copies back into an 8-byte aligned state. -/
theorem copyOutsA_ok {s₀ : State} (hp : Pre s₀) (hal : (st s₀).toNat % 8 = 0) {sL : State}
    (hL : LInv s₀ 12 sL) (s : State) (hs : EInv s₀ sL 0 s) :
    WP isa (.block ((List.range 25).flatMap copyOutA)) s (EInv s₀ sL 25) := by
  refine wp_range_flatMap (M := isa) (EInv s₀ sL)
    (fun i s' hi ⟨h0, h1, hrd, hwr, hsp, hf, hl, hcache⟩ => ?_) 25 (Nat.le_refl _) s hs
  unfold copyOutA
  rw [List.append_assoc]
  refine outLoad_ok hp hL ⟨h0, h1, hrd, hwr, hsp, hf, hl, hcache⟩ hi fun s₁ u₁ => ?_
  refine cmplLane_ok fun s₂ u₂ => ?_
  have hv : s₂.gpr .t0 = (keccakF (A₀ s₀))[i] := by
    rw [u₂.gpr, u₁.gpr, cmpl_msk _ hi]
  have g1 : s₂.gpr .s1 = st s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h1]
  refine wp_sd (by omega) (a := laneAddr (st s₀) i) (by rw [g1]) (al_lane hal i)
    (by rw [u₂.wr, u₁.wr, hwr]; exact in_st s₀ hi) fun s₃ g₃ => WP.block_nil ?_
  have m₂ : s₂.mem = s'.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨by rw [g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h0],
    by rw [g₃.gpr, g1], by rw [g₃.rd, u₂.rd, u₁.rd, hrd],
    by rw [g₃.wr, u₂.wr, u₁.wr, hwr], by rw [g₃.sp, u₂.sp, u₁.sp, hsp], ?_, fun j hj hji => ?_, fun j hj => ?_⟩
  · rw [g₃.mem, m₂]
    exact hf.writeW (List.mem_singleton_self _) _ (lane_contains _ hi)
  · rw [g₃.mem, m₂]
    by_cases e : j = i
    · subst e; rw [Mem.readW_writeW_self64, hv]
    · rw [Mem.readW_writeW_sep (Proof.Sha3.lane_sep _ hj hi e) (by decide)]
      exact hl j hj (by omega)
  · rw [g₃.gpr, u₂.other _ (cacheReg_ne hj (by decide)), u₁.other _ (cacheReg_ne hj (by decide))]
    exact hcache j hj

/-- Restoring the cache banks changes only those registers. -/
theorem cacheRestore_ok {s₀ s : State} (hp : Pre s₀) (h0 : s.gpr .a0 = off s₀ 192)
    (hrd : s.rd = []) (hwr : s.wr = W s₀) (hs : CSaved s₀ s.mem) :
    WP isa (.block cacheRestore) s fun t =>
      (∀ b i, i < 5 → t.gpr (cacheReg (cacheBank b) i) = s₀.gpr (cacheReg (cacheBank b) i)) ∧
      (∀ r, r ∉ cacheRegisters → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let Inv (k : Nat) (t : State) : Prop :=
    (∀ b i, i < k → t.gpr (cacheReg (cacheBank b) i) = s₀.gpr (cacheReg (cacheBank b) i)) ∧
    (∀ r, r ∉ cacheRegisters → t.gpr r = s.gpr r) ∧
    t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp
  unfold cacheRestore
  refine wp_range_flatMap (M := isa) Inv (fun i t hi ⟨hcs, hkeep, hm, hrd', hwr', hsp⟩ => ?_)
    5 (Nat.le_refl _) s ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  refine wp_ld (by omega) (a := off s₀ (192 + 8 * i)) (by rw [hkeep .a0 (by decide), h0, off_add])
    (hp.al_off (by omega) (by omega)) (by rw [hrd', hwr', hrd, hwr]; exact in_fr s₀ (by omega)) fun t₁ u₁ => ?_
  refine wp_ld (by omega) (a := off s₀ (392 + 8 * i))
    (by rw [u₁.other _ (Ne.symm (cacheReg_ne hi (by decide))), hkeep .a0 (by decide), h0, off_add,
      show 192 + (200 + 8 * i) = 392 + 8 * i by omega])
    (hp.al_off (by omega) (by omega))
    (by rw [u₁.rd, u₁.wr, hrd', hwr', hrd, hwr]; exact in_fr s₀ (by omega)) fun t₂ u₂ => WP.block_nil ?_
  refine ⟨?_, ?_, by rw [u₂.mem, u₁.mem, hm], by rw [u₂.rd, u₁.rd, hrd'],
    by rw [u₂.wr, u₁.wr, hwr'], by rw [u₂.sp, u₁.sp, hsp]⟩
  · intro b j hj
    by_cases he : j = i
    · subst j
      cases b
      · simp only [cacheBank, Bool.false_eq_true, ite_false]
        rw [u₂.gpr, u₁.mem, hm]
        simpa only [cacheOff, cacheBank, Bool.false_eq_true, ite_false] using hs false i hi
      · simp only [cacheBank, ite_true]
        have hne : cacheReg .a0 i ≠ cacheReg .a1 i := by
          intro he
          have h := (cacheReg_inj true false i hi i hi he).1
          cases h
        rw [u₂.other _ hne, u₁.gpr, hm]
        simpa only [cacheOff, cacheBank, ite_true] using hs true i hi
    · have hj' : j < i := by omega
      have hnA : cacheReg (cacheBank b) j ≠ cacheReg .a0 i := by
        intro heq
        exact he (cacheReg_inj b true j (by omega) i hi heq).2
      have hnB : cacheReg (cacheBank b) j ≠ cacheReg .a1 i := by
        intro heq
        exact he (cacheReg_inj b false j (by omega) i hi heq).2
      rw [u₂.other _ hnB, u₁.other _ hnA]
      exact hcs b j hj'
  · intro r hr
    have hnA : r ≠ cacheReg .a0 i := by
      intro he; apply hr; rw [he]; exact cacheReg_mem _ i hi
    have hnB : r ≠ cacheReg .a1 i := by
      intro he; apply hr; rw [he]; exact cacheReg_mem _ i hi
    rw [u₂.other _ hnB, u₁.other _ hnA]
    exact hkeep r hr

/-- Copy back, restore both banks, and restore the original two saved registers. -/
theorem epiTail_ok {s₀ : State} (hp : Pre s₀) {sL : State} (hL : LInv s₀ 12 sL) {outs : List Instr}
    (hc : WP isa (.block outs) sL (EInv s₀ sL 25)) :
    WP isa (.block (outs ++ restore)) sL fun s' =>
      s'.gpr .s0 = s₀.gpr .s0 ∧ s'.gpr .s1 = s₀.gpr .s1 ∧ s'.sp = F s₀ ∧ s'.wr = W s₀ ∧
        stateAt s'.mem (st s₀) = keccakF (A₀ s₀) ∧ ∀ r ∈ cacheRegisters, s'.gpr r = s₀.gpr r := by
  rw [WP.block_append_iff]
  refine WP.mono hc fun s₁ ⟨h0, h1, hrd, hwr, hsp, hf, hl, _⟩ => ?_
  have hfr : ∀ d, d + 8 ≤ 608 → s₁.mem.readW (off s₀ d) 64 = sL.mem.readW (off s₀ d) 64 := fun d hd =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.fr_st.sub_left (Offset.sub_base (F s₀) (d := d) (n := 8) (k := 608) hd)) (by decide)
  unfold restore
  rw [WP.block_append_iff]
  refine WP.mono (cacheRestore_ok hp h0 hrd hwr (by
    intro b i hi
    rw [hfr (cacheOff b i) (by cases b <;> simp only [cacheOff, Bool.false_eq_true, ite_false, ite_true] <;> omega)]
    exact hL.csaved b i hi)) fun s₂ ⟨hc, hk, hm, rd, wr, sp⟩ => ?_
  refine wp_ld (by decide) (a := off s₀ 592) (by rw [hk .a0 (by decide), h0, off_add]; rfl)
    (hp.al_off (by decide) (by decide))
    (by rw [rd, wr, hrd, hwr]; exact in_fr s₀ (by decide)) fun s₃ u₃ => ?_
  refine wp_ld (by decide) (a := off s₀ 600) (by rw [u₃.other _ (by decide), hk .a0 (by decide), h0, off_add]; rfl)
    (hp.al_off (by decide) (by decide))
    (by rw [u₃.rd, u₃.wr, rd, wr, hrd, hwr]; exact in_fr s₀ (by decide)) fun s₄ u₄ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, hm, hfr 592 (by decide)]; exact hL.aux.1
  · rw [u₄.gpr, u₃.mem, hm, hfr 600 (by decide)]; exact hL.aux.2.1
  · rw [u₄.sp, u₃.sp, sp, hsp]
  · rw [u₄.wr, u₃.wr, wr, hwr]
  · apply Vector.ext
    intro i hi
    simp only [Spec.Sha3.stateAt, Vector.getElem_ofFn, u₄.mem, u₃.mem, hm]
    exact hl i hi hi
  · intro r hr
    obtain ⟨b, i, rfl⟩ := cacheRegisters_cases hr
    rw [u₄.other _ (cacheReg_ne i.isLt (by decide)), u₃.other _ (cacheReg_ne i.isLt (by decide))]
    exact hc b i i.isLt

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {sL : State} (hL : LInv s₀ 12 sL) :
    WP isa epilogue sL fun s' =>
      s'.gpr .s0 = s₀.gpr .s0 ∧ s'.gpr .s1 = s₀.gpr .s1 ∧ s'.sp = F s₀ ∧ s'.wr = W s₀ ∧
        stateAt s'.mem (st s₀) = keccakF (A₀ s₀) ∧ ∀ r ∈ cacheRegisters, s'.gpr r = s₀.gpr r := by
  unfold epilogue
  refine WP.seq (wp_andi (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have hL₁ : LInv s₀ 12 s₁ :=
    ⟨(u₁.other _ (by decide)).trans hL.a0, (u₁.other _ (by decide)).trans hL.a1,
     (u₁.other _ (by decide)).trans hL.s0, (u₁.other _ (by decide)).trans hL.s1,
     u₁.rd.trans hL.rd, u₁.wr.trans hL.wr, u₁.sp.trans hL.sp,
     vLanes_congr hL.state u₁.mem (fun i hi => u₁.other _ (cacheReg_ne hi (by decide))),
     fun x hx => by
       have hn : rowReg x ≠ .t0 := by revert x; decide
       rw [u₁.other _ hn]; exact hL.row x hx,
     u₁.mem ▸ hL.aux, u₁.mem ▸ hL.frame, u₁.mem ▸ hL.csaved⟩
  have e0 : EInv s₀ s₁ 0 s₁ := ⟨hL₁.a0, hL₁.s1, hL₁.rd, hL₁.wr, hL₁.sp, Frame.refl _ _,
    fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  refine WP.ite (M := isa) (decide ((st s₀).toNat % 8 = 0))
    (by show some (s₁.gpr .t0 == 0) = _; rw [u₁.gpr, hL.s1, and7]) (fun h => ?_) (fun _ => ?_)
  · exact epiTail_ok hp hL₁ (copyOutsA_ok hp (of_decide_eq_true h) hL₁ s₁ e0)
  · exact epiTail_ok hp hL₁ (copyOuts_ok hp hL₁ s₁ e0)

/-- Registers that no instruction of code without calls writes keep their
values, as a postcondition. -/
theorem WP.gprs' {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r) (hn : c.noCalls = true) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (.inl hn)⟩

def keepsCache : Option Reg → Bool
  | some .s2 | some .s3 | some .s4 | some .s5 | some .s6 | some .s7 | some .s8
  | some .s9 | some .s10 | some .s11 => false
  | _ => true

theorem prefix_keeps : (Code.block (Impl.Sha3.RISCV64.setupPrefix) : Prog isa).allInstrs
    (fun i => keepsCache (dstOf i)) = true := by lit_decide

theorem prefix_other : ∀ r ∈ cacheRegisters, ∀ i ∈ instrs (Code.block (Impl.Sha3.RISCV64.setupPrefix) : Prog isa), dstOf i ≠ some r := by
  intro r hr i hi he
  have h := List.all_eq_true.mp ((Code.allInstrs_eq _ _).symm.trans prefix_keeps) i hi
  rw [he] at h
  have hf : keepsCache (some r) = false := by
    simp only [cacheRegisters, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hf] at h
  cases h

theorem setupPrefix_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (Impl.Sha3.RISCV64.setupPrefix)) (allocd 608 s₀) (RcInv s₀ 24) := by
  unfold Impl.Sha3.RISCV64.setupPrefix
  refine save_ok hp (s := allocd 608 s₀) rfl hp.rd (by simp only [allocd, hp.wr]) rfl rfl
    fun s₁ h6 h1 hrd hwr hsp v₁ v₂ hf => ?_
  exact rcs_ok hp s₁ ⟨h6, h1, hrd, hwr, hsp, v₁, v₂, fun _ h => absurd h (Nat.not_lt_zero _), hf⟩

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) (allocd 608 s₀) fun s => CInv s₀ 0 s ∧ s.gpr .t0 = st s₀ &&& BitVec.ofInt 64 7 := by
  unfold setup
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.gprs' (rs := cacheRegisters) (setupPrefix_ok hp) prefix_other (by decide)) fun s₂ ⟨hRC, hG⟩ => ?_
  obtain ⟨g6, g1, grd, gwr, gsp, w₁, w₂, wc, gf⟩ := hRC
  rw [WP.block_append_iff]
  refine WP.mono (cacheSave_ok hp g6 gwr (fun b i hi => hG _ (cacheReg_mem _ i hi))) fun s₃ ⟨hm, hcs, hcf⟩ => ?_
  have haux : Aux s₀ s₃.mem :=
    ⟨(cacheRegions_read hcf (by omega) (by omega)).trans w₁,
     (cacheRegions_read hcf (by omega) (by omega)).trans w₂,
     fun j hj => (cacheRegions_read hcf (by omega) (by omega)).trans (wc j hj)⟩
  refine wp_andi (by decide) fun s₄ u₄ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (by omega), ?_⟩, ?_⟩
  · rw [u₄.other _ (by decide), hm.gpr, g6]
  · rw [u₄.other _ (by decide), hm.gpr, g1]
  · rw [u₄.rd, hm.rd, grd]
  · rw [u₄.wr, hm.wr, gwr]
  · rw [u₄.sp, hm.sp, gsp]
  · rw [u₄.mem]; exact haux
  · rw [u₄.mem]; exact gf.trans (cacheRegions_sub _ hcf)
  · rw [u₄.mem]; exact hcs
  · rw [u₄.gpr, hm.gpr, g1]

/-- The copy into the frame, by either copy, and the rounds' pointers. -/
theorem copyIns'_ok {s₀ : State} (hp : Pre s₀) {s : State} (hs : CInv s₀ 0 s)
    (h0 : s.gpr .t0 = st s₀ &&& BitVec.ofInt 64 7) : WP isa copyIns s (LInv s₀ 0) := by
  unfold copyIns
  refine WP.ite (M := isa) (decide ((st s₀).toNat % 8 = 0))
    (by show some (s.gpr .t0 == 0) = _; rw [h0, and7]) (fun h => ?_) (fun _ => ?_)
  · rw [WP.block_append_iff]
    exact WP.mono (copyInsA_ok hp (of_decide_eq_true h) s hs) fun _ h => pointers_ok h
  · rw [WP.block_append_iff]
    exact WP.mono (copyIns_ok hp s hs) fun _ h => pointers_ok h

theorem main_ok {s₀ : State} (hp : Pre s₀) :
    WP isa main (allocd 608 s₀) fun s' =>
      s'.gpr .s0 = s₀.gpr .s0 ∧ s'.gpr .s1 = s₀.gpr .s1 ∧ s'.sp = F s₀ ∧ s'.wr = W s₀ ∧
        stateAt s'.mem (st s₀) = keccakF (A₀ s₀) ∧ ∀ r ∈ cacheRegisters, s'.gpr r = s₀.gpr r := by
  unfold main
  refine WP.seq (WP.mono (setup_ok hp) fun s₀' ⟨hc, h0⟩ => ?_)
  refine WP.seq (WP.mono (copyIns'_ok hp hc h0) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := LInv s₀ 12) ?_ fun s₂ h₂ => epilogue_ok hp h₂)
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = 12 - j ∧ j < 12 ∧ LInv s₀ j s
  refine WP.loop (M := isa) Inv (fun n s ⟨j, hn, hj, hL⟩ => ?_) 12 s₁ ⟨0, rfl, by omega, h₁⟩
  refine WP.mono (body_ok hp hj hL) fun s' ⟨he, hl⟩ => ?_
  by_cases hlast : j + 1 = 12
  · exact .inl ⟨by show eval (.ne .s0 .a0) s' = _; rw [he, hlast]; rfl, hlast ▸ hl⟩
  · exact .inr ⟨by show eval (.ne .s0 .a0) s' = _; rw [he]; simp [hlast],
      12 - (j + 1), by omega, j + 1, rfl, by omega, hl⟩

/-- The callee-saved registers the code never writes, and the return address. -/
def untouched : List Reg := [.ra]

/-- `untouched.all fun r => o != some r` as one `match`, which the kernel
evaluates faster. -/
def keepsU : Option Reg → Bool
  | some .ra => false
  | _ => true

theorem untouched_keep : main.allInstrs (fun i => keepsU (dstOf i)) = true := by
  decide +kernel

theorem main_noCalls : main.noCalls = true := by decide +kernel

theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs main, dstOf i ≠ some r := by
  intro r hr i hi e
  have h := List.all_eq_true.mp ((Code.allInstrs_eq _ _).symm.trans untouched_keep) i hi
  rw [e] at h
  simp only [untouched, List.mem_singleton] at hr
  subst r
  simp [keepsU] at h

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' =>
      s'.gpr .s0 = s₀.gpr .s0 ∧ s'.gpr .s1 = s₀.gpr .s1 ∧ s'.sp = s₀.sp ∧
        (∀ r ∈ cacheRegisters, s'.gpr r = s₀.gpr r) ∧
        (∀ r ∈ untouched, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permuteRISCV64.post s₀ s' := by
  have hm := WP.gprs' (main_ok hp) untouched_ok main_noCalls
  refine WP.alloc (n := 608) ⟨by decide, by decide, by decide⟩ hp.sp (WP.mono hm
    fun s₂ ⟨⟨h0, h1, hsp, hwr, hst, hc⟩, hu⟩ => ?_)
  refine ⟨h0, h1, ?_, hc, fun r hr => hu r hr, ?_⟩
  · show s₂.sp + BitVec.ofNat 64 608 = s₀.sp
    rw [hsp, BitVec.sub_add_cancel]
  · simp only [Proof.Sha3.permuteRISCV64, freed]
    exact hst

theorem preserved_split : ∀ r ∈ preserved, r = .s0 ∨ r = .s1 ∨ r ∈ cacheRegisters ∨ r ∈ untouched := by decide

theorem permute_correct (s : State) (hs : Proof.Sha3.permuteRISCV64.pre s) :
    ∃ t s', Exec isa Impl.Sha3.RISCV64.permute s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.permuteRISCV64.post s s' := by
  obtain ⟨t, s', he, h0, h1, hsp, hc, hu, h₂⟩ := correct (pre_of s hs)
  refine ⟨t, s', he, ⟨fun r hr => ?_, hsp, hu .ra (by decide)⟩, h₂⟩
  rcases preserved_split r hr with rfl | rfl | h | h
  exacts [h0, h1, hc r h, hu r h]

/-- The permutation's addresses and branches depend only on its public pointers. -/
theorem permute_ct : ConstantTime isa Proof.Sha3.permuteRISCV64.pre Proof.Sha3.permuteRISCV64.pub
    Impl.Sha3.RISCV64.permute := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h0, h1]

end VG.Proof.Sha3.RISCV64
