module

public import VerifiedGarbage.Proof.Sha3.Contract
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Round
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Sha3.PPC64LE.Lit
import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.Contract
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Round
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Lit
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Keccak-f[1600] on PPC64LE: the whole function

The prologue saves the nonvolatile registers in the scratch space (`Spill`),
stores all ones there, and loads the lanes into their registers, the lanes
`complLanes` complemented (`Round.load_ok`); each of the 24 rounds is
`Round.round_ok`; the epilogue stores the lanes back, complemented back
(`Round.store_ok`), and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE
open VG.Spec.Sha3 (stateAt keccakF rnd)
open VG.Proof.Sha3 (Lanes laneAddr lane_contains)
open VG.Proof.Sha3.Compl (cmpl)

abbrev KState := Spec.Sha3.State

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev scr : Addr := s₀.gpr .r4
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev scrR : Region := ⟨scr s₀, 512⟩
abbrev A₀ : KState := stateAt s₀.mem (st s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha3.permutePPC64LE.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem stR_in : stR s₀ ∈ s₀.wr := by rw [h.wr]; simp

theorem scr_in {d : Nat} (hd : d + 8 ≤ 512) :
    InRegions s₀.wr (scr s₀ + BitVec.ofNat 64 d) 8 := by
  rw [h.wr]; exact ⟨scrR s₀, by simp, Offset.contains_base _ hd (by omega)⟩

theorem slot_in : ∀ k < 4, InRegions s₀.wr (scr s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  fun _ hk => h.scr_in (by omega)

theorem in_all {a : Addr} {n : Nat} (hw : InRegions s₀.wr a n) : InRegions (s₀.rd ++ s₀.wr) a n := by
  rw [h.rd]; exact hw

theorem lane_in : ∀ i < 25, InRegions (s₀.rd ++ s₀.wr) (laneAddr (st s₀) i) 8 := fun _ hi =>
  h.in_all (by rw [h.wr]; exact ⟨stR s₀, by simp, lane_contains _ hi⟩)

/-- The state is disjoint from every part of the scratch space. -/
theorem st_off {d n : Nat} (hn : d + n ≤ 512) :
    Region.Disjoint (stR s₀) ⟨scr s₀ + BitVec.ofNat 64 d, n⟩ :=
  h.st_scr.sub_right (Offset.sub_base _ hn)

end Pre

/-! ## The scratch space -/

theorem saved_bound : ∀ p ∈ saved, 32 ≤ p.2 ∧ p.2 + 8 ≤ 32 + 152 := by decide

theorem saved_fits : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

/-- The saved registers are kept by writes to the spill slots or the state. -/
theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem}
    (h : Spill.Saved (scr s₀) s₀.gpr saved m) {R : Region}
    (hR : R = ⟨scr s₀, 32⟩ ∨ R = stR s₀) (hf : Frame [R] m m') :
    Spill.Saved (scr s₀) s₀.gpr saved m' := by
  refine h.frame_in saved_bound hf fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  rcases hR with rfl | rfl
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact (hp.st_off (by omega)).symm

/-! ## The rounds -/

/-- Before round `r`: the state after `r` rounds in the lanes' registers, as
kept (`cmpl`), and the scratch space holding all ones and the saved
registers. -/
structure RInv (s₀ : State) (r : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = st s₀
  r4 : s.gpr .r4 = scr s₀
  lanes : ∀ i (hi : i < 25), s.gpr (lane i) = (cmpl ((List.range r).foldl rnd (A₀ s₀)))[i]
  ones : s.mem.readW (scr s₀ + BitVec.ofNat 64 24) 64 = BitVec.allOnes 64
  saved : Spill.Saved (scr s₀) s₀.gpr saved s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem rounds_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : RInv s₀ 0 s) :
    WP isa (.block rounds) s (RInv s₀ 24) := by
  refine wp_range_flatMap (M := isa) (RInv s₀) (fun r s' _ hI => ?_) 24 (Nat.le_refl _) s h
  refine WP.mono (Round.round_ok r hI.r4 (by rw [hI.wr]; exact hp.slot_in) hI.ones hI.lanes)
    fun s'' ⟨hl, ho, hf, hrd, hwr, _, _, h3, h4⟩ => ⟨by rw [h3, hI.r3], by rw [h4, hI.r4],
      fun i hi => by rw [hl i hi, Proof.Sha3.foldl_succ], ho, saved_frame hp hI.saved (.inl rfl) hf,
      by rw [hrd, hI.rd], by rw [hwr, hI.wr]⟩

/-! ## The prologue -/

theorem setup_eq : setup = Spill.saveCode .r4 saved ++
    ([.lis T0 0xffff, .ori T0 T0 0xffff, .store .d T0 .r4 24] : List Instr) := rfl

theorem ones_eq : (((0xffff : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 |||
    (0xffff : BitVec 16).setWidth 64) = BitVec.allOnes 64 := by decide

theorem lanes₀ (s₀ : State) : Lanes s₀.mem (st s₀) (A₀ s₀) := by
  intro i hi; simp [Spec.Sha3.stateAt, laneAddr]

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (setup ++ loadLanes)) s₀ (RInv s₀ 0) := by
  rw [setup_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Spill.save_wp (by decide) saved_fits fun p hp' => hp.scr_in (by
    have := saved_bound p hp'; omega)) fun s₁ ⟨g₁, rd₁, wr₁, _, _, m₁⟩ => ?_
  have v₁ := m₁ ▸ Spill.saveMem_saved (by decide) s₀.mem (scr s₀) s₀.gpr (l := saved)
  have f₁ : Frame [⟨scr s₀ + BitVec.ofNat 64 32, 152⟩] s₀.mem s₁.mem :=
    m₁ ▸ Spill.saveMem_frame saved_bound (by omega) _ _ _
  have h4 : s₁.gpr .r4 = scr s₀ := by rw [g₁]
  suffices key : ∀ s₂ : State, (∀ r, r ≠ T0 → s₂.gpr r = s₁.gpr r) → s₂.gpr T0 = BitVec.allOnes 64 →
      s₂.mem = s₁.mem.writeW (scr s₀ + BitVec.ofNat 64 24) (BitVec.allOnes 64) → s₂.rd = s₀.rd →
      s₂.wr = s₀.wr → WP isa (.block loadLanes) s₂ (RInv s₀ 0) by
    rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append]
    refine MdStream.PPC64LE.WP.cons exec_lis (MdStream.PPC64LE.WP.cons exec_ori
      (MdStream.PPC64LE.WP.cons (exec_store_d (by decide) (by decide) ?_) (key _ ?_ ?_ ?_ rd₁ wr₁)))
    · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.r4 ≠ T0 by decide), h4, RegUpd.wr_write, wr₁]
      exact hp.scr_in (by omega)
    · intro r hr; simp only [RegUpd.gpr_write_of_ne _ _ hr]
    · simp only [RegUpd.gpr_write_self]; exact ones_eq
    · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.r4 ≠ T0 by decide), h4, RegUpd.gpr_write_self,
        RegUpd.mem_write]
      rw [ones_eq]
  intro s₂ g₂ o₂ mem₂ rd₂ wr₂
  have r3₂ : s₂.gpr .r3 = st s₀ := by rw [g₂ _ (by decide), g₁]
  have r4₂ : s₂.gpr .r4 = scr s₀ := by rw [g₂ _ (by decide), h4]
  -- the state and the saved registers are kept by the store of all ones
  have f₂ : Frame [⟨scr s₀ + BitVec.ofNat 64 24, 8⟩] s₁.mem s₂.mem := by
    rw [mem₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hA : Lanes s₂.mem (st s₀) (A₀ s₀) := fun i hi => by
    rw [f₂.readW (lane_contains _ hi) (by simpa using hp.st_off (d := 24) (n := 8) (by omega))
      (by decide), f₁.readW (lane_contains _ hi) (by simpa using hp.st_off (d := 32) (n := 152) (by omega))
      (by decide)]
    exact lanes₀ s₀ i hi
  have hsv : Spill.Saved (scr s₀) s₀.gpr saved s₂.mem :=
    v₁.frame_in saved_bound f₂ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have hones : s₂.mem.readW (scr s₀ + BitVec.ofNat 64 24) 64 = BitVec.allOnes 64 := by
    rw [mem₂, Mem.readW_writeW_self64]
  obtain ⟨s₃, hs₃, hl₃, m₃, rd₃, wr₃, _, _, r3₃, r4₃⟩ := Round.load_ok (M := A₀ s₀) o₂
    (fun i hi => by rw [rd₂, wr₂, r3₂]; exact hp.lane_in i hi) (by rw [r3₂]; exact hA)
  refine WP.of_runBlock ⟨s₃, hs₃, ⟨by rw [r3₃, r3₂], by rw [r4₃, r4₂],
    fun i hi => by rw [hl₃ i hi]; rfl, by rw [m₃]; exact hones, by rw [m₃]; exact hsv,
    by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩⟩

/-! ## The epilogue -/

theorem preserved_saved : ∀ r ∈ preserved, r ∈ saved.map Prod.fst := by decide

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : RInv s₀ 24 s) :
    WP isa (.block (storeLanes ++ restore)) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permutePPC64LE.post s₀ s' := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, hs₁, hl₁, hf₁, rd₁, wr₁, _, _, r3₁, r4₁⟩ := Round.store_ok (M := keccakF (A₀ s₀)) hI.r3
    (by rw [hI.r4]; exact hI.ones) (by rw [hI.wr]; exact hp.stR_in)
    (fun k hk => by rw [hI.rd, hI.wr, hI.r4]; exact hp.in_all (hp.slot_in k hk))
    (by rw [hI.r4]; simpa using hp.st_off (d := 0) (n := 32) (by omega)) hI.lanes
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  have hsv := saved_frame hp hI.saved (.inr rfl) hf₁
  refine WP.mono (Spill.restore_wp (by decide) (b := .r4) (B := scr s₀) (by rw [r4₁, hI.r4])
    saved_fits (by decide) (fun p hp' => ?_) hsv) fun s' h => ⟨fun r hr => ?_, ?_⟩
  · rw [rd₁, wr₁, hI.rd, hI.wr]
    exact hp.in_all (hp.scr_in (by have := saved_bound p hp'; omega))
  · exact h.gpr_of (.inl (preserved_saved r hr))
  · refine ⟨?_, by rw [h.other _ (by decide), r3₁, hI.r3], by rw [h.other _ (by decide), r4₁, hI.r4]⟩
    show stateAt s'.mem (st s₀) = keccakF (A₀ s₀)
    apply Vector.ext
    intro i hi
    simp only [Spec.Sha3.stateAt, Vector.getElem_ofFn, h.mem]
    exact hl₁ i hi

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permutePPC64LE.post s₀ s' := by
  unfold permute
  rw [show setup ++ loadLanes ++ rounds ++ storeLanes ++ restore =
    (setup ++ loadLanes) ++ (rounds ++ (storeLanes ++ restore)) by simp only [List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (prologue_ok hp) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  exact WP.mono (rounds_ok hp h₁) fun s₂ h₂ => epilogue_ok hp h₂

theorem permute_correct (s : State) (hs : Proof.Sha3.permutePPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Sha3.PPC64LE.permute s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.permutePPC64LE.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide)⟩, h₂⟩

theorem permute_noFrames : Impl.Sha3.PPC64LE.permute.noFrames = true := by lit_decide

end VG.Proof.Sha3.PPC64LE
