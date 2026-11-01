module

public import VerifiedGarbage.Proof.Sha3.Contract
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Round
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Sha3.PPC64LE.Lit
import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha3.Contract
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Round
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Lit
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Keccak-f[1600] on PPC64LE: the whole function

The same structure as the x86-64 proof (`VG.Proof.Sha3.X86_64`): the
prologue saves `r14`–`r20` (`Spill`), stores the round constants and
complements the lanes `complLanes`; each iteration of the loop is two rounds
(`Round.round_ok`, by evaluation); the epilogue complements the lanes back
and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE
open VG.Spec.Sha3 (stateAt keccakF rnd RC)
open VG.Proof.Sha3 (Lanes laneAddr lane_contains contains_offset sub_offset off_disjoint off_sub
  add_zero' foldl_succ)
open VG.Proof.MdStream.PPC64LE (Upd Mupd WP.cons wp_li wp_std wp_addi wp_subi)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev scr : Addr := s₀.gpr .r4
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev scrR : Region := ⟨scr s₀, 512⟩
abbrev A₀ : KState := stateAt s₀.mem (st s₀)

/-- The state the rounds read from before round `r`, and the one they write. -/
def cur (r : Nat) : Addr := if r % 2 = 0 then st s₀ else scr s₀
def oth (r : Nat) : Addr := if r % 2 = 0 then scr s₀ else st s₀

/-- Scratch offset `d`. -/
abbrev off (d : Nat) : Addr := scr s₀ + BitVec.ofNat 64 d

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha3.permutePPC64LE.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem cur_cases (s₀ : State) (r : Nat) :
    (cur s₀ r = st s₀ ∧ oth s₀ r = scr s₀) ∨ (cur s₀ r = scr s₀ ∧ oth s₀ r = st s₀) := by
  simp only [cur, oth]; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem in_wr {R : Region} (hR : R = stR s₀ ∨ R = scrR s₀) {a : Addr} {n : Nat}
    (hc : R.Contains a n) : InRegions s₀.wr a n := by
  rw [h.wr]; rcases hR with rfl | rfl
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩

theorem in_all {a : Addr} {n : Nat} (hw : InRegions s₀.wr a n) : InRegions (s₀.rd ++ s₀.wr) a n := by
  rw [h.rd]; exact hw

theorem lane_in {p : Addr} (hp : p = st s₀ ∨ p = scr s₀) {i : Nat} (hi : i < 25) :
    InRegions s₀.wr (laneAddr p i) 8 := by
  rcases hp with rfl | rfl
  · exact h.in_wr (.inl rfl) (lane_contains _ hi)
  · exact h.in_wr (.inr rfl) (contains_offset (by omega_arith) (by omega_arith))

theorem off_in {d : Nat} (hd : d + 8 ≤ 512) : InRegions s₀.wr (off s₀ d) 8 :=
  h.in_wr (.inr rfl) (contains_offset hd (by omega_arith))

/-- The first 200 bytes of the scratch space are disjoint from the state. -/
theorem st_scr200 : (stR s₀).Disjoint ⟨scr s₀, 200⟩ :=
  h.st_scr.sub_right (Region.sub_prefix (by omega_arith))

/-- The state and the second state are disjoint from every later scratch offset. -/
theorem region_off {p : Addr} (hp : p = st s₀ ∨ p = scr s₀) {d n : Nat} (hd : 200 ≤ d)
    (hn : d + n ≤ 512) : Region.Disjoint ⟨p, 200⟩ ⟨off s₀ d, n⟩ := by
  rcases hp with rfl | rfl
  · exact h.st_scr.sub_right (sub_offset hn (by omega_arith))
  · have := off_disjoint (scr s₀) (a := 0) (n := 200) (b := d) (k := n) (by omega_arith) (by omega_arith)
      (.inl hd)
    rwa [add_zero'] at this

theorem env (r : Nat) (hr : r < 24) :
    Proof.Sha3.Env s₀.rd s₀.wr (cur s₀ r) (oth s₀ r) (off s₀ (200 + 8 * r)) := by
  have hc := cur_cases s₀ r
  have hcur : cur s₀ r = st s₀ ∨ cur s₀ r = scr s₀ := hc.imp (·.1) (·.1)
  have hoth : oth s₀ r = st s₀ ∨ oth s₀ r = scr s₀ := hc.symm.imp (·.2) (·.2)
  refine ⟨fun i hi => h.in_all (h.lane_in hcur hi), fun i hi => h.lane_in hoth hi,
    h.in_all (h.off_in (by omega_arith)), ?_, h.region_off hoth (by omega_arith) (by omega_arith)⟩
  rcases hc with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂]
  · exact h.st_scr200.symm
  · exact h.st_scr200

end Pre

/-! ## The scratch space -/

theorem saved_bound : ∀ p ∈ saved, 392 ≤ p.2 ∧ p.2 + 8 ≤ 448 := by decide

/-- The saved registers, and the round constants. -/
def Aux (s₀ : State) (m : Mem) : Prop :=
  Spill.Saved (scr s₀) s₀.gpr saved m ∧ ∀ j < 24, m.readW (off s₀ (200 + 8 * j)) 64 = RC j

/-- Writes outside the constants and the saved registers keep them. -/
theorem Aux.frame {s₀ : State} {m m' : Mem} (h : Aux s₀ m) {R : Region}
    (hR : ∀ d, 200 ≤ d → d + 8 ≤ 448 → Region.Disjoint ⟨off s₀ d, 8⟩ R) (hf : Frame [R] m m') :
    Aux s₀ m' := by
  refine ⟨Spill.Saved.frame h.1 hf fun p hp r hr => ?_, fun j hj => ?_⟩
  · rw [List.mem_singleton.mp hr]
    have := saved_bound p hp
    exact hR _ (by omega_arith) (by omega_arith)
  · rw [hf.readW (Region.contains_self _ _) (by simpa using hR _ (by omega_arith) (by omega_arith)) (by decide)]
    exact h.2 j hj

/-! ## The prologue -/

/-- The nonvolatile registers the code never writes. -/
def untouched : List Reg := [.r2, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem untouched_kept : ∀ r ∈ untouched, r ∈ Round.kept := by decide

/-- The stores of the round constants. -/
def rcStores : List Instr :=
  (List.range 24).flatMap fun k => movImm64 .r5 (RC k) ++ ([.store .d .r5 .r4 (200 + 8 * k)] : List Instr)

theorem setup_eq : setup = Spill.saveCode .r4 saved ++ rcStores ++
    ([.lis ONES 0xffff, .ori ONES ONES 0xffff, .addi .r19 .r4 200, .li .r20 12] : List Instr) := rfl

/-- `movImm64` leaves the constant in the register. -/
private theorem wp_movImm64 {s : State} {d : Reg} {v : BitVec 64} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d v → WP isa (.block rest) s' Q) :
    WP isa (.block (movImm64 d v ++ rest)) s Q := by
  simp only [movImm64, List.cons_append, List.nil_append]
  refine WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_lsl (by decide)) (WP.cons exec_oris
    (WP.cons exec_ori (k _ ⟨?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩)))))
  · simp only [State.write, ite_true]
    exact movImm64_eq v
  · simp [State.write, h]

/-- During the stores of the round constants, from memory `m₁` and registers `g₁`. -/
def RcInv (s₀ : State) (g₁ : Reg → BitVec 64) (m₁ : Mem) (k : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .r5 → s.gpr r = g₁ r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    Frame [⟨off s₀ 200, 192⟩] m₁ s.mem ∧ ∀ j < k, s.mem.readW (off s₀ (200 + 8 * j)) 64 = RC j

theorem rcs_ok {s₀ : State} (hp : Pre s₀) (s : State) (hr4 : s.gpr .r4 = scr s₀)
    (hs : RcInv s₀ s.gpr s.mem 0 s) : WP isa (.block rcStores) s (RcInv s₀ s.gpr s.mem 24) := by
  refine wp_range_flatMap (M := isa) (RcInv s₀ s.gpr s.mem)
    (fun k s' hk ⟨hg, hrd, hwr, hf, hv⟩ => ?_) 24 (Nat.le_refl _) s hs
  have h4 : s'.gpr .r4 = scr s₀ := by rw [hg _ (by decide), hr4]
  refine wp_movImm64 fun s₁ u₁ => wp_std (a := off s₀ (200 + 8 * k)) ⟨by omega_arith, by omega_arith⟩
    (by rw [u₁.other _ (by decide), h4])
    (by rw [u₁.wr, hwr]; exact hp.off_in (by omega_arith)) fun s₂ g₂ => WP.block_nil ?_
  refine ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, hg r hr], by rw [g₂.rd, u₁.rd, hrd],
    by rw [g₂.wr, u₁.wr, hwr], ?_, fun j hj => ?_⟩
  · rw [g₂.mem, u₁.mem]
    refine hf.writeW (List.mem_singleton_self _) _ ?_
    rw [show off s₀ (200 + 8 * k) = off s₀ 200 + BitVec.ofNat 64 (8 * k) by
      simp only [off]; rw [BitVec.ofNat_add]; ac_rfl]
    exact contains_offset (by omega_arith) (by omega_arith)
  · rw [g₂.mem, u₁.mem, u₁.gpr]
    by_cases e : j = k
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact hv j (by omega_arith)
      · have := off_disjoint (scr s₀) (a := 200 + 8 * j) (n := 8) (b := 200 + 8 * k) (k := 8)
          (by omega_arith) (by omega_arith) (by omega_arith)
        exact this.sep (Region.contains_self _ _) (Region.contains_self _ _)

open VG.Proof.Sha3.PPC64LE.Round (rowReg kept round_ok check₀ check₁ keeps₀ keeps₁ slots_ok
  complement_check complementRow_check complement_writes complement_writes' rows_of cmpl_cmpl)
open VG.Proof.Sha3.Compl (cmpl)

/-- `r19` before iteration `j` of the loop: the round constants of rounds `2j`
and `2j + 1`. -/
abbrev rcp (s₀ : State) (j : Nat) : Addr := off s₀ (200 + 16 * j)

/-- The rounds' invariant, before iteration `j` (round `2j`): the state,
with the lanes `complLanes` complemented, at `state`, and its row 4 in
`rowReg`. -/
structure LInv (s₀ : State) (j : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = st s₀
  r4 : s.gpr .r4 = scr s₀
  ones : s.gpr .r18 = BitVec.allOnes 64
  r19 : s.gpr .r19 = rcp s₀ j
  r20 : s.gpr .r20 = BitVec.ofNat 64 (12 - j)
  keep : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : Lanes s.mem (st s₀) (cmpl ((List.range (2 * j)).foldl rnd (A₀ s₀)))
  row : ∀ x (hx : x < 5), s.gpr (rowReg x) = (cmpl ((List.range (2 * j)).foldl rnd (A₀ s₀)))[20 + x]
  aux : Aux s₀ s.mem
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem

theorem lanes₀ (s₀ : State) : Lanes s₀.mem (st s₀) (A₀ s₀) := by
  intro i hi; simp [Spec.Sha3.stateAt, laneAddr]

theorem ones_eq : (((0xffff : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 |||
    (0xffff : BitVec 16).setWidth 64) = BitVec.allOnes 64 := by decide

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (setup ++ complement ++ loadRow)) s₀ (LInv s₀ 0) := by
  rw [setup_eq, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Spill.save_wp (by decide) (by decide) fun p hp' => hp.off_in (by
    have := saved_bound p hp'; omega_arith)) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, lr₁, m₁⟩ => ?_
  have f₁ : Frame [⟨off s₀ 392, 56⟩] s₀.mem s₁.mem := m₁ ▸ Spill.saveMem_frame (lo := 392) (n := 56)
    (fun p hp' => by have := saved_bound p hp'; omega_arith) (by decide) _ _ _
  have v₁ := m₁ ▸ Spill.saveMem_saved (by decide) s₀.mem (scr s₀) s₀.gpr (l := saved)
  rw [WP.block_append_iff]
  refine WP.mono (rcs_ok hp s₁ (by rw [g₁]) ⟨fun _ _ => rfl, by rw [rd₁], by rw [wr₁], Frame.refl _ _,
    fun _ h => absurd h (by omega_arith)⟩) fun s₂ ⟨g₂, rd₂, wr₂, f₂, v₂⟩ => ?_
  rw [List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_addi (by decide) (by decide))
    (WP.cons (exec_li (by decide)) ?_)))
  -- The prologue writes only scratch offsets 200 to 448 before complementing.
  have hf : Frame [⟨off s₀ 200, 248⟩] s₀.mem s₂.mem := by
    refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      exact ⟨_, List.mem_singleton_self _, off_sub _ (by omega_arith) (by omega_arith) (by omega_arith)⟩
  have hd₂ : Region.Disjoint (stR s₀) ⟨off s₀ 200, 248⟩ := hp.region_off (.inl rfl) (by omega_arith) (by omega_arith)
  have hA : Lanes s₂.mem (st s₀) (A₀ s₀) := fun i hi => by
    rw [hf.readW (lane_contains _ hi) (by simpa using hd₂) (by decide)]; exact lanes₀ s₀ i hi
  have haux : Aux s₀ s₂.mem := by
    refine ⟨Spill.Saved.frame v₁ f₂ fun p hp' r hr => ?_, v₂⟩
    rw [List.mem_singleton.mp hr]
    have := saved_bound p hp'
    exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  suffices key : ∀ s₃ : State, (∀ r, s₃.gpr r = if r = .r20 then BitVec.ofNat 64 12
      else if r = .r19 then scr s₀ + BitVec.ofNat 64 200 else if r = ONES then BitVec.allOnes 64
      else s₂.gpr r) → s₃.rd = s₀.rd → s₃.wr = s₀.wr → s₃.mem = s₂.mem →
      WP isa (.block (complement ++ loadRow)) s₃ (LInv s₀ 0) by
    refine key _ (fun r => ?_) rd₂ wr₂ rfl
    by_cases h20 : r = .r20
    · subst h20; simp [State.write]
    by_cases h19 : r = .r19
    · subst h19; simp [State.write, ONES, g₂ .r4 (by decide), g₁]
    by_cases h18 : r = ONES
    · subst h18; simp only [State.write, ONES, ite_true, reduceCtorEq, ite_false]; exact ones_eq
    simp [State.write, h20, h19, h18]
  intro s₃ g₃ rd₃ wr₃ m₃
  have hwr : (stR s₀) ∈ s₃.wr := by rw [wr₃, hp.wr]; simp
  obtain ⟨s₄, e₄, hs₄, hp₄, hr₄, hl₄, hf₄, rd₄, wr₄, -, -, k₄⟩ := slots_ok complementRow_check
    (fun e h => by simp only [Round.rPost, Bool.and_eq_true] at h; exact h.1) complement_writes
    (s := s₃) (by rw [g₃]; simp [ONES, g₂ .r3 (by decide), g₁]) hwr
    (by rw [g₃]; simp [ONES]) (by rw [m₃]; exact hA)
  refine WP.of_runBlock ⟨s₄, hs₄, ?_⟩
  have hsk : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem :=
    hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, sub_offset (by omega_arith) (by omega_arith)⟩
  have kg : ∀ r ∈ kept, s₄.gpr r = s₃.gpr r := k₄
  refine ⟨by rw [kg .r3 (by decide), g₃]; simp [ONES, g₂ .r3 (by decide), g₁],
    by rw [kg .r4 (by decide), g₃]; simp [ONES, g₂ .r4 (by decide), g₁],
    by rw [kg .r18 (by decide), g₃]; simp [ONES],
    by rw [kg .r19 (by decide), g₃]; simp,
    by rw [kg .r20 (by decide), g₃]; rfl,
    fun r hr => ?_, by rw [rd₄, rd₃], by rw [wr₄, wr₃], by simpa using hl₄, fun x hx => ?_, ?_, ?_⟩
  · have hk := untouched_kept r hr
    rw [kg r hk, g₃]
    have : r ≠ .r20 ∧ r ≠ .r19 ∧ r ≠ ONES ∧ r ≠ .r5 := by revert r; decide
    simp only [this, ite_false]; rw [g₂ r this.2.2.2, g₁]
  · simpa using rows_of hr₄ hp₄ x hx
  · rw [m₃] at hf₄
    exact haux.frame (fun d hd hd' => (hp.region_off (.inl rfl) hd (by omega_arith)).symm) hf₄
  · rw [m₃] at hf₄
    exact hsk.trans (hf₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, fun _ h => h⟩)

/-! ## The rounds -/

theorem rcp_add (s₀ : State) (j k : Nat) :
    rcp s₀ j + BitVec.ofNat 64 (8 * k) = off s₀ (200 + 8 * (2 * j + k)) := by
  simp only [rcp, off]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  omega_arith

theorem cur_even (s₀ : State) (j : Nat) : cur s₀ (2 * j) = st s₀ ∧ oth s₀ (2 * j) = scr s₀ := by
  simp [cur, oth]

theorem cur_odd (s₀ : State) (j : Nat) : cur s₀ (2 * j + 1) = scr s₀ ∧ oth s₀ (2 * j + 1) = st s₀ := by
  simp [cur, oth, Nat.add_mod]

theorem foldl_two (A : KState) (j : Nat) :
    (List.range (2 * (j + 1))).foldl rnd A = rnd (rnd ((List.range (2 * j)).foldl rnd A) (2 * j)) (2 * j + 1) := by
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega_arith, foldl_succ, foldl_succ]

theorem r20_next : ∀ j < 12, BitVec.ofNat 64 (12 - j) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (12 - (j + 1)) := by
  decide

theorem rcp_next (j : Nat) :
    BitVec.ofNat 64 (200 + 16 * j) + BitVec.ofNat 64 16 = BitVec.ofNat 64 (200 + 16 * (j + 1)) := by
  rw [BitVec.ofNat_add_ofNat]; congr 1

theorem r20_ne : ∀ j < 12, (BitVec.ofNat 64 (12 - (j + 1)) != 0) = !decide (j + 1 = 12) := by
  decide

/-- Two rounds, from iteration `j`. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < 12) {s : State} (hL : LInv s₀ j s) :
    WP isa (.block body) s fun s' =>
      eval (.nonzero .d .r20) s' = some (!decide (j + 1 = 12)) ∧ LInv s₀ (j + 1) s' := by
  unfold body
  rw [WP.block_append_iff, WP.block_append_iff]
  have ⟨c₀, o₀⟩ := cur_even s₀ j
  have ⟨c₁, o₁⟩ := cur_odd s₀ j
  have he₀ := hp.env (2 * j) (by omega_arith)
  have he₁ := hp.env (2 * j + 1) (by omega_arith)
  rw [c₀, o₀] at he₀
  rw [c₁, o₁] at he₁
  have ea₀ : s.gpr .r19 + BitVec.ofNat 64 (8 * 0) = off s₀ (200 + 8 * (2 * j)) := by
    rw [hL.r19, rcp_add, Nat.add_zero]
  refine WP.mono (round_ok check₀ keeps₀ (by decide) (by decide) 0 (by decide) (rc := RC (2 * j))
    (src := st s₀) (dst := scr s₀) hL.r3 hL.r4 (by decide) (by decide)
    (by rw [hL.rd, hL.wr, ea₀]; exact he₀) hL.state hL.row hL.ones
    (by rw [ea₀]; exact hL.aux.2 (2 * j) (by omega_arith))) fun s₁ ⟨l₁, w₁, f₁, rd₁, wr₁, _, _, k₁⟩ => ?_
  have aux₁ : Aux s₀ s₁.mem := hL.aux.frame (fun d hd hd' => (hp.region_off (.inr rfl) hd (by omega_arith)).symm) f₁
  have ea₁ : s₁.gpr .r19 + BitVec.ofNat 64 (8 * 1) = off s₀ (200 + 8 * (2 * j + 1)) := by
    rw [k₁ .r19 (by decide), hL.r19, rcp_add]
  refine WP.mono (round_ok check₁ keeps₁ (by decide) (by decide) 1 (by decide) (rc := RC (2 * j + 1))
    (src := scr s₀) (dst := st s₀)
    (by rw [k₁ .r4 (by decide)]; exact hL.r4) (by rw [k₁ .r3 (by decide)]; exact hL.r3) (by decide) (by decide)
    (by rw [rd₁, wr₁, hL.rd, hL.wr, ea₁]; exact he₁) l₁ w₁ (by rw [k₁ .r18 (by decide)]; exact hL.ones)
    (by rw [ea₁]; exact aux₁.2 (2 * j + 1) (by omega_arith))) fun s₂ ⟨l₂, w₂, f₂, rd₂, wr₂, _, _, k₂⟩ => ?_
  have h19 : s₂.gpr .r19 = rcp s₀ j := by rw [k₂ .r19 (by decide), k₁ .r19 (by decide), hL.r19]
  have h20 : s₂.gpr .r20 = BitVec.ofNat 64 (12 - j) := by
    rw [k₂ .r20 (by decide), k₁ .r20 (by decide), hL.r20]
  refine WP.cons (exec_addi (by decide) (by decide)) (WP.cons (exec_subi (by decide) (by decide))
    (WP.block_nil ⟨?_, ?_⟩))
  · simp only [eval, State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, h20,
      reduceCtorEq, ite_false]
    rw [r20_next j hj, r20_ne j hj]
  · have keep : ∀ r ∈ kept, r ≠ .r19 → r ≠ .r20 →
        ((s₂.write .r19 (s₂.gpr .r19 + BitVec.ofNat 64 16)).write .r20
          ((s₂.write .r19 (s₂.gpr .r19 + BitVec.ofNat 64 16)).gpr .r20 - BitVec.ofNat 64 1)).gpr r =
        s.gpr r := fun r hr h1 h2 => by
      simp only [State.write, h1, h2, ite_false]; rw [k₂ r hr, k₁ r hr]
    have hst : cmpl (Proof.Sha3.outState (Proof.Sha3.outState ((List.range (2 * j)).foldl rnd (A₀ s₀))
        (RC (2 * j))) (RC (2 * j + 1))) = cmpl ((List.range (2 * (j + 1))).foldl rnd (A₀ s₀)) := by
      rw [Proof.Sha3.outState_eq, Proof.Sha3.outState_eq, foldl_two]
    rw [hst] at l₂ w₂
    have hrow : ∀ x < 5, rowReg x ≠ .r19 ∧ rowReg x ≠ .r20 := by decide
    refine ⟨by rw [keep .r3 (by decide) (by decide) (by decide), hL.r3],
      by rw [keep .r4 (by decide) (by decide) (by decide), hL.r4],
      by rw [keep .r18 (by decide) (by decide) (by decide), hL.ones],
      by simp only [State.write, ite_true, reduceCtorEq, ite_false, h19, rcp, off]
         rw [BitVec.add_assoc, rcp_next],
      by simp only [State.write, ite_true, reduceCtorEq, ite_false, h20]; exact r20_next j hj,
      fun r hr => ?_, by show s₂.rd = _; rw [rd₂, rd₁, hL.rd], by show s₂.wr = _; rw [wr₂, wr₁, hL.wr], l₂,
      fun x hx => ?_, ?_, ?_⟩
    · have : r ≠ .r19 ∧ r ≠ .r20 := by revert r; decide
      rw [keep r (untouched_kept r hr) this.1 this.2, hL.keep r hr]
    · simp only [State.write, (hrow x hx).1, (hrow x hx).2, ite_false]; exact w₂ x hx
    · exact aux₁.frame (fun d hd hd' => (hp.region_off (.inl rfl) hd (by omega_arith)).symm) f₂
    · refine (hL.frame.trans (f₁.sub fun r hr => ?_)).trans (f₂.sub fun r hr => ?_) <;>
        simp only [List.mem_singleton] at hr <;> subst hr
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by omega_arith)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩

/-! ## The epilogue -/

theorem saved_fits : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

theorem preserved_split : ∀ r ∈ preserved, r ∈ saved.map Prod.fst ∨ r ∈ untouched := by decide

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hL : LInv s₀ 12 s) :
    WP isa (.block (complement ++ restore)) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permutePPC64LE.post s₀ s' := by
  rw [WP.block_append_iff]
  have hwr : stR s₀ ∈ s.wr := by rw [hL.wr, hp.wr]; simp
  obtain ⟨s₁, -, hs₁, -, -, hl₁, hf₁, rd₁, wr₁, -, -, k₁⟩ :=
    slots_ok complement_check (fun _ h => h) complement_writes' hL.r3 hwr hL.ones hL.state
  rw [cmpl_cmpl] at hl₁
  have haux : Aux s₀ s₁.mem :=
    hL.aux.frame (fun d hd hd' => (hp.region_off (.inl rfl) hd (by omega_arith)).symm) hf₁
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  refine WP.mono (Spill.restore_wp (by decide) (b := .r4) (B := scr s₀) (by rw [k₁ .r4 (by decide), hL.r4])
    saved_fits (by decide) (fun p hp' => ?_) haux.1) fun s' h => ⟨fun r hr => ?_, ?_⟩
  · rw [rd₁, wr₁, hL.rd, hL.wr]
    exact hp.in_all (hp.off_in (by have := saved_bound p hp'; omega_arith))
  · rcases preserved_split r hr with hs | hu
    · exact h.gpr_of (.inl hs)
    · have : r ∉ saved.map Prod.fst := by revert r; decide
      rw [h.other r this, k₁ r (untouched_kept r hu), hL.keep r hu]
  · show stateAt s'.mem (st s₀) = keccakF (A₀ s₀)
    apply Vector.ext
    intro i hi
    simp only [Spec.Sha3.stateAt, Vector.getElem_ofFn, h.mem]
    have := hl₁ i hi
    simp only [laneAddr] at this
    rw [this]
    rfl

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permutePPC64LE.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := LInv s₀ 12) ?_ fun s₂ h₂ => epilogue_ok hp h₂)
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = 12 - j ∧ j < 12 ∧ LInv s₀ j s
  refine WP.loop (M := isa) Inv (fun n s ⟨j, hn, hj, hL⟩ => ?_) 12 s₁ ⟨0, rfl, by omega_arith, h₁⟩
  refine WP.mono (body_ok hp hj hL) fun s' ⟨he, hl⟩ => ?_
  by_cases hlast : j + 1 = 12
  · exact .inl ⟨by show eval (.nonzero .d .r20) s' = _; rw [he, hlast]; rfl, hlast ▸ hl⟩
  · exact .inr ⟨by show eval (.nonzero .d .r20) s' = _; rw [he]; simp [hlast],
      12 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hl⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 512⟩]

theorem permute_correct (s : State) (hs : Proof.Sha3.permutePPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Sha3.PPC64LE.permute s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.permutePPC64LE.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide)⟩, h₂⟩

theorem permute_noFrames : Impl.Sha3.PPC64LE.permute.noFrames = true := by lit_decide

theorem permute_ct : ConstantTime isa Proof.Sha3.permutePPC64LE.pre Proof.Sha3.permutePPC64LE.pub
    Impl.Sha3.PPC64LE.permute := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem permute_verified' :
    Verified PPC64LE.target Impl.Sha3.PPC64LE.permute Proof.Sha3.permutePPC64LE :=
  ⟨permute_correct, permute_ct, satState, rfl, rfl, Region.disjoint_of_sep (by decide)⟩

theorem permute_verified :
    Verified PPC64LE.target Impl.Sha3.PPC64LE.permute (Proof.Sha3.permuteContract PPC64LE.abi) :=
  permute_verified'.of_implies (by
    contract_implies [Proof.Sha3.permuteContract, Proof.Sha3.permuteSig, Proof.Sha3.permutePPC64LE,
      PPC64LE.abi, PPC64LE.argRegs] [satState] using satState)

end VG.Proof.Sha3.PPC64LE
