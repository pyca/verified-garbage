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

The structure of the PPC64LE proof (`Proof/Sha3/PPC64LE/Permute.lean`), in a
frame on the stack (`WP.alloc`): the prologue saves `s0` and `s1`, stores
the round constants (`movImm64_ok`) and copies the state into the frame a
byte at a time, complementing the lanes `complLanes` (`loadLE64_ok`); each
iteration of the loop is two rounds (`Round.round_ok`, by evaluation); the
epilogue copies the state back a byte at a time, complementing those lanes
back (`storeLE64_ok`), and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64
open VG.Spec.Sha3 (stateAt keccakF rnd RC)
open VG.Proof.Sha3 (Lanes laneAddr lane_contains foldl_succ)
open VG.Proof.Sha3.RISCV64.Round (rowReg kept round_ok check₀ check₁ keeps₀ keeps₁)
open VG.Proof.Sha3.Compl (cmpl msk)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

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

theorem sp_off (s₀ : State) (d : Nat) : F s₀ + BitVec.ofNat 64 d = off s₀ d := rfl

/-- Frame words at separate offsets. -/
theorem rw_off (s₀ : State) (m : Mem) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 32)
    (he : e + 8 ≤ 2 ^ 32) (v : BitVec 64) :
    (m.writeW (off s₀ d) v).readW (off s₀ e) 64 = m.readW (off s₀ e) 64 :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

theorem frame_off {s₀ : State} {m m' : Mem} (hf : Frame [frR s₀] m m') {d : Nat} (hd : d + 8 ≤ 608)
    (v : BitVec 64) : Frame [frR s₀] m (m'.writeW (off s₀ d) v) :=
  hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ hd (by omega))

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

/-- During the stores of the round constants. -/
def RcInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr .t6 = F s₀ ∧ s.gpr .s1 = st s₀ ∧ s.rd = [] ∧ s.wr = W s₀ ∧ s.sp = F s₀ ∧
    s.mem.readW (off s₀ 592) 64 = s₀.gpr .s0 ∧ s.mem.readW (off s₀ 600) 64 = s₀.gpr .s1 ∧
    (∀ j < k, s.mem.readW (off s₀ (8 * j)) 64 = RC j) ∧ Frame [frR s₀] s₀.mem s.mem

theorem rcs_ok {s₀ : State} (hp : Pre s₀) (s : State) (hs : RcInv s₀ 0 s) :
    WP isa (.block rcStores) s (RcInv s₀ 24) := by
  refine wp_range_flatMap (M := isa) (RcInv s₀) (fun k s' hk ⟨h6, h1, hrd, hwr, hsp, v₁, v₂, hv, hf⟩ => ?_)
    24 (Nat.le_refl _) s hs
  rw [WP.block_append_iff]
  refine WP.mono (Words64.movImm64_ok (show Reg.t0 ≠ .t1 by decide) (RC k)) fun s₁ ⟨g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  refine wp_sd (by omega) (a := off s₀ (8 * k)) (by rw [o₁ _ (by decide) (by decide), h6])
    (hp.al_off (by omega) (by omega)) (by rw [wr₁, hwr]; exact in_fr s₀ (by omega)) fun s₂ g₂ => ?_
  refine WP.block_nil ⟨by rw [g₂.gpr, o₁ _ (by decide) (by decide), h6],
    by rw [g₂.gpr, o₁ _ (by decide) (by decide), h1], by rw [g₂.rd, rd₁, hrd],
    by rw [g₂.wr, wr₁, hwr], by rw [g₂.sp, sp₁, hsp], ?_, ?_, fun j hj => ?_, ?_⟩
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
def CInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr .t6 = F s₀ ∧ s.gpr .s1 = st s₀ ∧ s.rd = [] ∧ s.wr = W s₀ ∧ s.sp = F s₀ ∧
    Aux s₀ s.mem ∧ Frame [frR s₀] s₀.mem s.mem ∧
    (∀ j (hj : j < 25), j < k → s.mem.readW (off s₀ (192 + 8 * j)) 64 = (cmpl (A₀ s₀))[j]) ∧
    ∀ x (hx : x < 5), 20 + x < k → s.gpr (rowReg x) = (cmpl (A₀ s₀))[20 + x]

theorem lane₀ (s₀ : State) {m : Mem} (hp : Pre s₀) (hf : Frame [frR s₀] s₀.mem m) {i : Nat}
    (hi : i < 25) : m.readW (laneAddr (st s₀) i) 64 = (A₀ s₀)[i] := by
  rw [hf.readW (lane_contains _ hi) hp.fr_st' (by decide)]
  simp [Spec.Sha3.stateAt, laneAddr]

theorem copyIns_ok {s₀ : State} (hp : Pre s₀) (s : State) (hs : CInv s₀ 0 s) :
    WP isa (.block ((List.range 25).flatMap copyIn)) s (CInv s₀ 25) := by
  refine wp_range_flatMap (M := isa) (CInv s₀)
    (fun i s' hi ⟨h6, h1, hrd, hwr, hsp, haux, hf, hl, hrow⟩ => ?_) 25 (Nat.le_refl _) s hs
  obtain ⟨n1, n2, ns, n6⟩ := laneReg_ne i hi
  unfold copyIn
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Words64.loadLE64_ok (d := laneReg i) (tmp := .t1) (tmp2 := .t2) (n := .s1)
    (off := 8 * i) ns (by decide) n1 (by decide) (by decide) n2 (by omega)
    (by rw [hrd, hwr, h1]; exact in_st s₀ hi)) fun s₁ u₁ => ?_
  refine cmplLane_ok fun s₂ u₂ => ?_
  have hv : s₂.gpr (laneReg i) = (cmpl (A₀ s₀))[i] := by
    rw [u₂.gpr, u₁.gpr, h1, ← laneAddr, lane₀ s₀ hp hf hi, Round.cmpl_get _ hi]
  have g6 : s₂.gpr .t6 = F s₀ := by
    rw [u₂.other _ (Ne.symm n6), u₁.other _ (Ne.symm n6) (by decide) (by decide), h6]
  refine wp_sd (by simp only [stOff]; omega) (a := off s₀ (192 + 8 * i)) (by rw [g6]; rfl) (hp.al_off (by omega) (by omega))
    (by rw [u₂.wr, u₁.wr, hwr]; exact in_fr s₀ (by omega)) fun s₃ g₃ => WP.block_nil ?_
  have m₂ : s₂.mem = s'.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨by rw [g₃.gpr, g6], by rw [g₃.gpr, u₂.other _ (Ne.symm ns), u₁.other _ (Ne.symm ns)
      (by decide) (by decide), h1], by rw [g₃.rd, u₂.rd, u₁.rd, hrd], by rw [g₃.wr, u₂.wr, u₁.wr, hwr],
    by rw [g₃.sp, u₂.sp, u₁.sp, hsp], ?_, ?_, fun j hj hji => ?_, fun x hx hxi => ?_⟩
  · rw [g₃.mem, m₂]
    exact haux.frame (fun d h₁ h₂ => copy_disjoint s₀ (.inl rfl) h₁ h₂ |>.sub_right
      (Offset.sub _ (by omega) (by omega))) ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _))
  · rw [g₃.mem, m₂]; exact frame_off hf (by omega) _
  · rw [g₃.mem, m₂]
    by_cases e : j = i
    · subst e; rw [Mem.readW_writeW_self64, hv]
    · rw [rw_off s₀ _ (by omega) (by omega) (by omega)]; exact hl j hj (by omega)
  · rw [g₃.gpr]
    by_cases e : 20 + x = i
    · subst e; rw [← laneReg_row x hx]; exact hv
    · have hne : rowReg x ≠ laneReg i := fun h => laneReg_ne_row i hi x hx (by omega) h.symm
      have hrn := row_ne x hx
      rw [u₂.other _ hne, u₁.other _ hne hrn.1 hrn.2]
      exact hrow x hx (by omega)

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
  refine wp_range_flatMap (M := isa) (CInv s₀)
    (fun i s' hi ⟨h6, h1, hrd, hwr, hsp, haux, hf, hl, hrow⟩ => ?_) 25 (Nat.le_refl _) s hs
  obtain ⟨n1, n2, ns, n6⟩ := laneReg_ne i hi
  unfold copyInA ld
  rw [List.cons_append]
  refine wp_ld (by omega) (a := laneAddr (st s₀) i) (by rw [h1]) (al_lane hal i)
    (by rw [hrd, hwr]; exact in_st s₀ hi) fun s₁ u₁ => ?_
  refine cmplLane_ok fun s₂ u₂ => ?_
  have hv : s₂.gpr (laneReg i) = (cmpl (A₀ s₀))[i] := by
    rw [u₂.gpr, u₁.gpr, lane₀ s₀ hp hf hi, Round.cmpl_get _ hi]
  have g6 : s₂.gpr .t6 = F s₀ := by
    rw [u₂.other _ (Ne.symm n6), u₁.other _ (Ne.symm n6), h6]
  refine wp_sd (by simp only [stOff]; omega) (a := off s₀ (192 + 8 * i)) (by rw [g6]; rfl) (hp.al_off (by omega) (by omega))
    (by rw [u₂.wr, u₁.wr, hwr]; exact in_fr s₀ (by omega)) fun s₃ g₃ => WP.block_nil ?_
  have m₂ : s₂.mem = s'.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨by rw [g₃.gpr, g6], by rw [g₃.gpr, u₂.other _ (Ne.symm ns), u₁.other _ (Ne.symm ns), h1],
    by rw [g₃.rd, u₂.rd, u₁.rd, hrd], by rw [g₃.wr, u₂.wr, u₁.wr, hwr],
    by rw [g₃.sp, u₂.sp, u₁.sp, hsp], ?_, ?_, fun j hj hji => ?_, fun x hx hxi => ?_⟩
  · rw [g₃.mem, m₂]
    exact haux.frame (fun d h₁ h₂ => copy_disjoint s₀ (.inl rfl) h₁ h₂ |>.sub_right
      (Offset.sub _ (by omega) (by omega))) ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _))
  · rw [g₃.mem, m₂]; exact frame_off hf (by omega) _
  · rw [g₃.mem, m₂]
    by_cases e : j = i
    · subst e; rw [Mem.readW_writeW_self64, hv]
    · rw [rw_off s₀ _ (by omega) (by omega) (by omega)]; exact hl j hj (by omega)
  · rw [g₃.gpr]
    by_cases e : 20 + x = i
    · subst e; rw [← laneReg_row x hx]; exact hv
    · have hne : rowReg x ≠ laneReg i := fun h => laneReg_ne_row i hi x hx (by omega) h.symm
      rw [u₂.other _ hne, u₁.other _ hne]
      exact hrow x hx (by omega)

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
  state : Lanes s.mem (off s₀ 192) (cmpl ((List.range (2 * j)).foldl rnd (A₀ s₀)))
  row : ∀ x (hx : x < 5), s.gpr (rowReg x) = (cmpl ((List.range (2 * j)).foldl rnd (A₀ s₀)))[20 + x]
  aux : Aux s₀ s.mem
  frame : Frame [frR s₀] s₀.mem s.mem

theorem pointers_ok {s₀ : State} {s : State} (hs : CInv s₀ 25 s) :
    WP isa (.block pointers) s (LInv s₀ 0) := by
  obtain ⟨h6, h1, hrd, hwr, hsp, haux, hf, hl, hrow⟩ := hs
  simp only [pointers]
  refine wp_addSp (by decide) fun s₁ u₁ => wp_addSp (by decide) fun s₂ u₂ => wp_mv fun s₃ u₃ =>
    WP.block_nil ?_
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hsp]; rfl,
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.sp, hsp]; rfl,
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h6]; exact (BitVec.add_zero _).symm,
    by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h1],
    by rw [u₃.rd, u₂.rd, u₁.rd, hrd], by rw [u₃.wr, u₂.wr, u₁.wr, hwr],
    by rw [u₃.sp, u₂.sp, u₁.sp, hsp], fun i hi => ?_, fun x hx => ?_, m₃ ▸ haux, m₃ ▸ hf⟩
  · rw [m₃, laneAddr_off]; exact hl i hi (by omega)
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
  refine WP.mono (round_ok check₀ keeps₀ (by decide) (by decide) 0 (by decide) (rc := RC (2 * j))
    (src := off s₀ 192) (dst := off s₀ 392) hL.a0 hL.a1 (hp.al_off (by decide) (by decide))
    (hp.al_off (by decide) (by decide)) (by rw [ea₀]; exact hp.al_off (by omega) (by omega))
    (by rw [hL.rd, hL.wr, ea₀]; exact he₀) hL.state hL.row
    (by rw [ea₀]; exact hL.aux.2.2 (2 * j) (by omega))) fun s₁ ⟨l₁, w₁, f₁, rd₁, wr₁, sp₁, k₁⟩ => ?_
  have aux₁ : Aux s₀ s₁.mem := aux_round hL.aux (.inr rfl) f₁
  have ea₁ : s₁.gpr .s0 + BitVec.ofNat 64 (8 * 1) = off s₀ (8 * (2 * j + 1)) := by
    rw [k₁ .s0 (by decide), hL.s0, off_add, show 16 * j + 8 * 1 = 8 * (2 * j + 1) by omega]
  refine WP.mono (round_ok check₁ keeps₁ (by decide) (by decide) 1 (by decide) (rc := RC (2 * j + 1))
    (src := off s₀ 392) (dst := off s₀ 192)
    (by rw [k₁ .a1 (by decide)]; exact hL.a1) (by rw [k₁ .a0 (by decide)]; exact hL.a0)
    (hp.al_off (by decide) (by decide)) (hp.al_off (by decide) (by decide))
    (by rw [ea₁]; exact hp.al_off (by omega) (by omega))
    (by rw [rd₁, wr₁, hL.rd, hL.wr, ea₁]; exact he₁) l₁ w₁
    (by rw [ea₁]; exact aux₁.2.2 (2 * j + 1) (by omega))) fun s₂ ⟨l₂, w₂, f₂, rd₂, wr₂, sp₂, k₂⟩ => ?_
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
      by rw [u₃.mem]; exact l₂, fun x hx => ?_, ?_, ?_⟩
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
    ∀ j (hj : j < 25), j < k → s.mem.readW (laneAddr (st s₀) j) 64 = (keccakF (A₀ s₀))[j]

theorem cmpl_msk (A : KState) {i : Nat} (hi : i < 25) : (cmpl A)[i] ^^^ msk i = A[i] := by
  rw [Round.cmpl_get _ hi, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem copyOuts_ok {s₀ : State} (hp : Pre s₀) {sL : State} (hL : LInv s₀ 12 sL) (s : State)
    (hs : EInv s₀ sL 0 s) : WP isa (.block ((List.range 25).flatMap copyOut)) s (EInv s₀ sL 25) := by
  have hX : Lanes sL.mem (off s₀ 192) (cmpl (keccakF (A₀ s₀))) := hL.state
  refine wp_range_flatMap (M := isa) (EInv s₀ sL)
    (fun i s' hi ⟨h0, h1, hrd, hwr, hsp, hf, hl⟩ => ?_) 25 (Nat.le_refl _) s hs
  unfold copyOut ld
  rw [List.cons_append]
  refine wp_ld (by omega) (a := off s₀ (192 + 8 * i)) (by rw [h0, off_add])
    (hp.al_off (by omega) (by omega)) (by rw [hrd, hwr]; exact in_fr s₀ (by omega)) fun s₁ u₁ => ?_
  refine cmplLane_ok fun s₂ u₂ => ?_
  have hv : s₂.gpr .t0 = (keccakF (A₀ s₀))[i] := by
    rw [u₂.gpr, u₁.gpr, ← laneAddr_off, hf.readW (lane_contains _ hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.fr_st.sub_left (Offset.sub_base (F s₀) (d := 192) (n := 200) (k := 608) (by omega)))
      (by decide), hX i hi, cmpl_msk _ hi]
  have g1 : s₂.gpr .s1 = st s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h1]
  refine WP.mono (Words64.storeLE64_ok (v := .t0) (tmp := .t1) (tmp2 := .t2) (n := .s1) (off := 8 * i)
    (by decide) (by decide) (by decide) (by decide) (by omega)
    (by rw [u₂.wr, u₁.wr, hwr, g1]; exact in_st s₀ hi)) fun s₃ ⟨o₃, m₃, rd₃, wr₃, sp₃⟩ => ?_
  have m₂ : s₂.mem = s'.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨by rw [o₃ _ (by decide) (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h0],
    by rw [o₃ _ (by decide) (by decide), g1], by rw [rd₃, u₂.rd, u₁.rd, hrd],
    by rw [wr₃, u₂.wr, u₁.wr, hwr], by rw [sp₃, u₂.sp, u₁.sp, hsp], ?_, fun j hj hji => ?_⟩
  · rw [m₃, g1, m₂]
    exact hf.writeW (List.mem_singleton_self _) _ (lane_contains _ hi)
  · rw [m₃, g1, m₂]
    by_cases e : j = i
    · subst e; rw [Mem.readW_writeW_self64, hv]
    · rw [Mem.readW_writeW_sep (Proof.Sha3.lane_sep _ hj hi e) (by decide)]
      exact hl j hj (by omega)

/-- The copies back into an 8-byte aligned state. -/
theorem copyOutsA_ok {s₀ : State} (hp : Pre s₀) (hal : (st s₀).toNat % 8 = 0) {sL : State}
    (hL : LInv s₀ 12 sL) (s : State) (hs : EInv s₀ sL 0 s) :
    WP isa (.block ((List.range 25).flatMap copyOutA)) s (EInv s₀ sL 25) := by
  have hX : Lanes sL.mem (off s₀ 192) (cmpl (keccakF (A₀ s₀))) := hL.state
  refine wp_range_flatMap (M := isa) (EInv s₀ sL)
    (fun i s' hi ⟨h0, h1, hrd, hwr, hsp, hf, hl⟩ => ?_) 25 (Nat.le_refl _) s hs
  unfold copyOutA ld
  rw [List.cons_append]
  refine wp_ld (by omega) (a := off s₀ (192 + 8 * i)) (by rw [h0, off_add])
    (hp.al_off (by omega) (by omega)) (by rw [hrd, hwr]; exact in_fr s₀ (by omega)) fun s₁ u₁ => ?_
  refine cmplLane_ok fun s₂ u₂ => ?_
  have hv : s₂.gpr .t0 = (keccakF (A₀ s₀))[i] := by
    rw [u₂.gpr, u₁.gpr, ← laneAddr_off, hf.readW (lane_contains _ hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.fr_st.sub_left (Offset.sub_base (F s₀) (d := 192) (n := 200) (k := 608) (by omega)))
      (by decide), hX i hi, cmpl_msk _ hi]
  have g1 : s₂.gpr .s1 = st s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h1]
  refine wp_sd (by omega) (a := laneAddr (st s₀) i) (by rw [g1]) (al_lane hal i)
    (by rw [u₂.wr, u₁.wr, hwr]; exact in_st s₀ hi) fun s₃ g₃ => WP.block_nil ?_
  have m₂ : s₂.mem = s'.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨by rw [g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h0],
    by rw [g₃.gpr, g1], by rw [g₃.rd, u₂.rd, u₁.rd, hrd],
    by rw [g₃.wr, u₂.wr, u₁.wr, hwr], by rw [g₃.sp, u₂.sp, u₁.sp, hsp], ?_, fun j hj hji => ?_⟩
  · rw [g₃.mem, m₂]
    exact hf.writeW (List.mem_singleton_self _) _ (lane_contains _ hi)
  · rw [g₃.mem, m₂]
    by_cases e : j = i
    · subst e; rw [Mem.readW_writeW_self64, hv]
    · rw [Mem.readW_writeW_sep (Proof.Sha3.lane_sep _ hj hi e) (by decide)]
      exact hl j hj (by omega)

/-- The copies back, by either of the copies `outs`, then the registers restored. -/
theorem epiTail_ok {s₀ : State} (hp : Pre s₀) {sL : State} (hL : LInv s₀ 12 sL) {outs : List Instr}
    (hc : WP isa (.block outs) sL (EInv s₀ sL 25)) :
    WP isa (.block (outs ++ restore)) sL fun s' =>
      s'.gpr .s0 = s₀.gpr .s0 ∧ s'.gpr .s1 = s₀.gpr .s1 ∧ s'.sp = F s₀ ∧ s'.wr = W s₀ ∧
        stateAt s'.mem (st s₀) = keccakF (A₀ s₀) := by
  rw [WP.block_append_iff]
  refine WP.mono hc fun s₁ ⟨h0, h1, hrd, hwr, hsp, hf, hl⟩ => ?_
  have hfr : ∀ d, d + 8 ≤ 608 → s₁.mem.readW (off s₀ d) 64 = sL.mem.readW (off s₀ d) 64 := fun d hd =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.fr_st.sub_left (Offset.sub_base (F s₀) (d := d) (n := 8) (k := 608) hd)) (by decide)
  unfold restore
  refine wp_ld (by decide) (a := off s₀ 592) (by rw [h0, off_add]; rfl) (hp.al_off (by decide) (by decide))
    (by rw [hrd, hwr]; exact in_fr s₀ (by decide)) fun s₂ u₂ => ?_
  refine wp_ld (by decide) (a := off s₀ 600) (by rw [u₂.other _ (by decide), h0, off_add]; rfl)
    (hp.al_off (by decide) (by decide)) (by rw [u₂.rd, u₂.wr, hrd, hwr]; exact in_fr s₀ (by decide))
    fun s₃ u₃ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr, hfr 592 (by decide)]; exact hL.aux.1
  · rw [u₃.gpr, u₂.mem, hfr 600 (by decide)]; exact hL.aux.2.1
  · rw [u₃.sp, u₂.sp, hsp]
  · rw [u₃.wr, u₂.wr, hwr]
  · apply Vector.ext
    intro i hi
    simp only [Spec.Sha3.stateAt, Vector.getElem_ofFn, u₃.mem, u₂.mem]
    exact hl i hi hi

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {sL : State} (hL : LInv s₀ 12 sL) :
    WP isa epilogue sL fun s' =>
      s'.gpr .s0 = s₀.gpr .s0 ∧ s'.gpr .s1 = s₀.gpr .s1 ∧ s'.sp = F s₀ ∧ s'.wr = W s₀ ∧
        stateAt s'.mem (st s₀) = keccakF (A₀ s₀) := by
  unfold epilogue
  refine WP.seq (Wp.WP.cons (exec_logicImm (imm := 7) (by decide)) (WP.block_nil ?_))
  let s₁ := sL.write .t0 (sL.gpr .s1 &&& BitVec.ofInt 64 7)
  have hL₁ : LInv s₀ 12 s₁ := ⟨by simp [s₁, State.write, hL.a0], by simp [s₁, State.write, hL.a1],
    by simp [s₁, State.write, hL.s0], by simp [s₁, State.write, hL.s1], hL.rd, hL.wr, hL.sp, hL.state,
    fun x hx => by
      have : rowReg x ≠ .t0 := by revert x; decide
      simp only [s₁, State.write, this, ite_false]; exact hL.row x hx, hL.aux, hL.frame⟩
  have e0 : EInv s₀ s₁ 0 s₁ := ⟨hL₁.a0, hL₁.s1, hL₁.rd, hL₁.wr, hL₁.sp, Frame.refl _ _,
    fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.ite (M := isa) (decide ((st s₀).toNat % 8 = 0))
    (by show some (s₁.gpr .t0 == 0) = _; simp only [s₁, State.write, ite_true, hL.s1]; rw [and7])
    (fun h => ?_) (fun _ => ?_)
  · exact WP.mono (epiTail_ok hp hL₁ (copyOutsA_ok hp (of_decide_eq_true h) hL₁ s₁ e0)) fun _ h => h
  · exact WP.mono (epiTail_ok hp hL₁ (copyOuts_ok hp hL₁ s₁ e0)) fun _ h => h

/-- Registers that no instruction of code without calls writes keep their
values, as a postcondition. -/
theorem WP.gprs' {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r) (hn : c.noCalls = true) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (.inl hn)⟩

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) (allocd 608 s₀) fun s => CInv s₀ 0 s ∧ s.gpr .t0 = st s₀ &&& BitVec.ofInt 64 7 := by
  unfold setup
  simp only [List.append_assoc]
  refine save_ok hp (s := allocd 608 s₀) rfl hp.rd (by simp only [allocd, hp.wr]) rfl rfl
    fun s₁ h6 h1 hrd hwr hsp v₁ v₂ hf => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rcs_ok hp s₁ ⟨h6, h1, hrd, hwr, hsp, v₁, v₂, fun _ h => absurd h (Nat.not_lt_zero _),
    hf⟩) fun s₂ ⟨g6, g1, grd, gwr, gsp, w₁, w₂, wc, gf⟩ => ?_
  refine Wp.WP.cons (exec_logicImm (imm := 7) (by decide)) (WP.block_nil ⟨⟨?_, ?_, grd, gwr, gsp, ⟨w₁, w₂, wc⟩, gf,
    fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (by omega)⟩, ?_⟩)
  · simp [State.write, g6]
  · simp [State.write, g1]
  · simp [State.write, g1]

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
        stateAt s'.mem (st s₀) = keccakF (A₀ s₀) := by
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
def untouched : List Reg := [.ra, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

/-- `untouched.all fun r => o != some r` as one `match`, which the kernel
evaluates faster. -/
def keepsU : Option Reg → Bool
  | some .ra | some .s2 | some .s3 | some .s4 | some .s5 | some .s6 | some .s7 | some .s8
  | some .s9 | some .s10 | some .s11 => false
  | _ => true

theorem untouched_keep : main.allInstrs (fun i => keepsU (dstOf i)) = true := by
  decide +kernel

theorem main_noCalls : main.noCalls = true := by decide +kernel

theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs main, dstOf i ≠ some r := by
  intro r hr i hi e
  have h := List.all_eq_true.mp ((Code.allInstrs_eq _ _).symm.trans untouched_keep) i hi
  rw [e] at h
  simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [keepsU] at h

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' =>
      s'.gpr .s0 = s₀.gpr .s0 ∧ s'.gpr .s1 = s₀.gpr .s1 ∧ s'.sp = s₀.sp ∧
        (∀ r ∈ untouched, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permuteRISCV64.post s₀ s' := by
  have hm := WP.gprs' (main_ok hp) untouched_ok main_noCalls
  refine WP.alloc (n := 608) ⟨by decide, by decide, by decide⟩ hp.sp (WP.mono hm
    fun s₂ ⟨⟨h0, h1, hsp, hwr, hst⟩, hu⟩ => ?_)
  refine ⟨h0, h1, ?_, fun r hr => hu r hr, ?_⟩
  · show s₂.sp + BitVec.ofNat 64 608 = s₀.sp
    rw [hsp, BitVec.sub_add_cancel]
  · simp only [Proof.Sha3.permuteRISCV64, freed]
    exact hst

theorem preserved_split : ∀ r ∈ preserved, r = .s0 ∨ r = .s1 ∨ r ∈ untouched := by decide

theorem permute_correct (s : State) (hs : Proof.Sha3.permuteRISCV64.pre s) :
    ∃ t s', Exec isa Impl.Sha3.RISCV64.permute s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.permuteRISCV64.post s s' := by
  obtain ⟨t, s', he, h0, h1, hsp, hu, h₂⟩ := correct (pre_of s hs)
  refine ⟨t, s', he, ⟨fun r hr => ?_, hsp, hu .ra (by decide)⟩, h₂⟩
  rcases preserved_split r hr with rfl | rfl | h
  exacts [h0, h1, hu r h]

theorem permute_ct : ConstantTime isa Proof.Sha3.permuteRISCV64.pre Proof.Sha3.permuteRISCV64.pub
    Impl.Sha3.RISCV64.permute := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h1, h2]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 512⟩]

theorem permute_verified' :
    Verified RISCV64.target Impl.Sha3.RISCV64.permute Proof.Sha3.permuteRISCV64 := by
  refine ⟨permute_correct, permute_ct, satState, rfl, rfl, ?_, by decide, by decide, ?_, ?_⟩ <;>
  exact Region.disjoint_of_sep (by decide)

theorem permute_verified :
    Verified RISCV64.target Impl.Sha3.RISCV64.permute (Proof.Sha3.permuteContract RISCV64.abi 608) :=
  permute_verified'.of_implies (by
    contract_implies [Proof.Sha3.permuteContract, Proof.Sha3.permuteSig, Proof.Sha3.permuteRISCV64,
      RISCV64.abi, RISCV64.argRegs] [satState] using satState)

end VG.Proof.Sha3.RISCV64
