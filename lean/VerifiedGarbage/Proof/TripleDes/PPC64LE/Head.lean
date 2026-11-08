module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.BlockIO
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Save
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Ready
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.PPC64LE.RoundLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

/-- Slots 0–61 of the scratch buffer: the saved registers and the constants. -/
def saveRegion (s : State) : Region := ⟨s.gpr .r5, 496⟩

structure HeadPre (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  scratch : Ok scratchCfg s
  pointer : s.gpr .r3 = base
  saveRead : ∀ i < 15, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8
  saveWrite : ∀ i < 62, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8
  dataRead : InRegions (s.rd ++ s.wr) (s.gpr .r4) 8
  dataSeparate : (⟨s.gpr .r4, 8⟩ : Region).Disjoint (saveRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separateWork : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (spillRegion s)
  separateSave : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (saveRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

structure HeadPost (keys : Nat → DesSchedule) (base : Addr) (original s : State) : Prop where
  word : WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (original.gpr .r4)))) s
  ready : Ready keys base s
  saved : Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  regs : ∀ q ∈ loadKept, s.gpr q = original.gpr q
  frame : Frame [saveRegion original] original.mem s.mem

/-! ## The constants -/

theorem movImm64_ok (d : Reg) (v : BitVec 64) (s : State) :
    ∃ s', runBlock isa (movImm64 d v) s = some s' ∧ s'.gpr d = v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [movImm64, runBlock_cons, exec_lis, runStep_some, runBlock_cons, exec_ori, runStep_some,
    runBlock_cons, exec_lsl (by decide), runStep_some, runBlock_cons, exec_oris, runStep_some,
    runBlock_cons, exec_ori, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [gpr_write_self]
    exact movImm64_eq v
  · simp [gpr_write, hr]

/-- The memory `m` with the words `vs` written at `B + off` on. -/
def constMem (m : Mem) (B : Addr) : List (BitVec 64) → Nat → Mem
  | [], _ => m
  | v :: vs, off => constMem (m.writeW (B + BitVec.ofNat 64 off) v) B vs (off + 8)

theorem constMem_frame (B : Addr) (vs : List (BitVec 64)) :
    ∀ (m : Mem) (off : Nat), off + 8 * vs.length ≤ 2048 →
      Frame [⟨B + BitVec.ofNat 64 off, 8 * vs.length⟩] m (constMem m B vs off) := by
  induction vs with
  | nil => intro m off _; exact Frame.refl _ _
  | cons v vs ih =>
    intro m off h
    simp only [List.length_cons] at h
    have h1 : Frame [⟨B + BitVec.ofNat 64 off, 8 * (vs.length + 1)⟩] m
        (m.writeW (B + BitVec.ofNat 64 off) v) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) v (by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    have h2 := ih (m.writeW (B + BitVec.ofNat 64 off) v) (off + 8) (by omega)
    refine h1.trans (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.sub B (by omega) (by omega)

theorem constMem_read (B : Addr) (vs : List (BitVec 64)) :
    ∀ (m : Mem) (off : Nat), off + 8 * vs.length ≤ 2048 → ∀ c < vs.length,
      (constMem m B vs off).readW (B + BitVec.ofNat 64 (off + 8 * c)) 64 = vs.getD c 0 := by
  induction vs with
  | nil => intro _ _ _ c hc; simp at hc
  | cons v vs ih =>
    intro m off h c hc
    simp only [List.length_cons] at h hc
    rcases c with _ | c
    · have hf := constMem_frame B vs (m.writeW (B + BitVec.ofNat 64 off) v) (off + 8) (by omega)
      simp only [constMem, Nat.mul_zero, Nat.add_zero, List.getD_cons_zero]
      rw [hf.readW (r := ⟨B + BitVec.ofNat 64 off, 8⟩) (Region.contains_self _ _) (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint B (Or.inl (Nat.le_refl _)) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]
    · simp only [constMem, List.getD_cons_succ]
      rw [show off + 8 * (c + 1) = off + 8 + 8 * c by omega]
      exact ih _ (off + 8) (by omega) c (by omega)

theorem storeConsts_wp (vs : List (BitVec 64)) :
    ∀ (off : Nat) (s : State) (Q : State → Prop), off % 8 = 0 → off + 8 * vs.length ≤ 2048 →
      (∀ c < vs.length, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (off + 8 * c)) 8) →
      (∀ t : State, t.mem = constMem s.mem (s.gpr .r5) vs off → t.rd = s.rd → t.wr = s.wr →
        (∀ r, r ≠ .r6 → t.gpr r = s.gpr r) → Q t) →
      WP isa (.block (storeConsts vs off)) s Q := by
  induction vs with
  | nil =>
    intro off s Q _ _ _ hQ
    exact WP.block_nil (hQ s rfl rfl rfl fun _ _ => rfl)
  | cons v vs ih =>
    intro off s Q hoff hlim hin hQ
    simp only [List.length_cons] at hlim
    rw [storeConsts, WP.block_append_iff, WP.block_append_iff]
    obtain ⟨s₁, run₁, d₁, o₁, m₁, rd₁, wr₁⟩ := movImm64_ok t0 v s
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hb₁ : s₁.gpr .r5 = s.gpr .r5 := o₁ _ (by decide)
    let s₂ : State := { s₁ with mem := s₁.mem.writeW (s₁.gpr .r5 + BitVec.ofNat 64 off) (s₁.gpr t0) }
    refine WP.of_runBlock ⟨s₂, ?_, ?_⟩
    · have h0 := hin 0 (by simp)
      simp only [Nat.mul_zero, Nat.add_zero] at h0
      show runBlock isa [.store .d t0 .r5 off] s₁ = some s₂
      rw [runBlock_cons, exec_store_d (by decide) ⟨by omega, by omega⟩ (by rw [hb₁, wr₁]; exact h0),
        runStep_some, runBlock_nil]
    · have hb₂ : s₂.gpr .r5 = s.gpr .r5 := hb₁
      refine ih (off + 8) s₂ Q (by omega) (by omega) (fun c hc => ?_)
        fun t hm hrd hwr hg => hQ t ?_ (hrd.trans rd₁) (hwr.trans wr₁) fun r h0 => ?_
      · rw [hb₂, show off + 8 + 8 * c = off + 8 * (c + 1) by omega]
        exact wr₁ ▸ hin (c + 1) (by simp only [List.length_cons]; omega)
      · rw [hm, hb₂]
        show constMem (s₁.mem.writeW (s₁.gpr .r5 + BitVec.ofNat 64 off) (s₁.gpr t0)) _ vs (off + 8) = _
        rw [hb₁, d₁, m₁]; rfl
      · exact (hg r h0).trans (o₁ r h0)

/-! ## The head -/

theorem roundConsts_length : roundConsts.length = 47 := by
  rw [roundConsts.lit_eq]; decide +kernel

theorem consts_ready {s t : State} (hb : t.gpr .r5 = s.gpr .r5)
    (hm : t.mem = constMem s.mem (s.gpr .r5) roundConsts constOff) : ConstsAt t := by
  intro c hc
  rw [hm, hb, wordAddr, show 8 * (15 + c) = constOff + 8 * c by unfold constOff; omega]
  exact constMem_read _ _ _ _ (by decide) c (by rw [roundConsts_length]; exact hc)

theorem consts_frame (s : State) :
    Frame [saveRegion s] s.mem (constMem s.mem (s.gpr .r5) roundConsts constOff) :=
  (constMem_frame _ _ _ _ (by decide)).sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, by
      rw [roundConsts_length]; exact Offset.sub_base _ (by decide)⟩

theorem consts_saved {original s t : State} (hs : Saved original s) (hb : t.gpr .r5 = s.gpr .r5)
    (hm : t.mem = constMem s.mem (s.gpr .r5) roundConsts constOff) : Saved original t := by
  intro i hi
  rw [hm, hb, ← hs i hi]
  exact (constMem_frame _ _ _ _ (by decide)).readW (r := ⟨s.gpr .r5 + BitVec.ofNat 64 (8 * i), 8⟩)
    (Region.contains_self _ _) (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq
      rw [roundConsts_length]
      exact Offset.disjoint _ (Or.inl (by unfold constOff; omega)) (by omega) (by decide)) (by decide)

theorem ready_afterSave {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hp : HeadPre keys base s) (hb : t.gpr .r5 = s.gpr .r5) (hkey : t.gpr .r3 = s.gpr .r3)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hc : ConstsAt t) (hf : Frame [saveRegion s] s.mem t.mem) :
    Ready keys base t := by
  refine ⟨hp.scratch.congr hb hb hrd hwr, hc, hkey.trans hp.pointer, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hp.read
  · rw [show spillRegion t = spillRegion s from
      congrArg (fun p => (⟨p + BitVec.ofNat 64 496, 16⟩ : Region)) hb]
    exact hp.separateWork
  · intro c hc d j hj
    have hmem := hf.readW (a := keyAddr (componentBase base c) d j) (w := 64)
      (r := ⟨keyAddr (componentBase base c) d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.separateSave c hc d j hj)
      (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hp.values c hc d j hj)

theorem blockHead_ok (keys : Nat → DesSchedule) (base : Addr) (s : State)
    (hp : HeadPre keys base s) :
    WP isa (.block (blockSave ++ storeConsts roundConsts constOff ++ blockLoad)) s
      (HeadPost keys base s) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  apply WP.mono (blockSave_ok s fun i hi => hp.saveWrite i (by omega))
  intro s₁ hs₁
  have hb₁ : s₁.gpr .r5 = s.gpr .r5 := congrFun hs₁.gpr .r5
  refine storeConsts_wp roundConsts constOff s₁ _ (by decide) (by rw [roundConsts_length]; decide)
    (fun c hc => by
      rw [hs₁.wr, hb₁, show constOff + 8 * c = 8 * (15 + c) by unfold constOff; omega]
      exact hp.saveWrite _ (by rw [roundConsts_length] at hc; omega)) ?_
  intro s₂ m₂ rd₂ wr₂ g₂
  have hb₂ : s₂.gpr .r5 = s₁.gpr .r5 := g₂ _ (by decide)
  have hframe₂ : Frame [saveRegion s] s.mem s₂.mem := by
    refine hs₁.frame.sub (fun r hr => ?_) |>.trans ?_
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · rw [m₂, show saveRegion s = saveRegion s₁ by simp only [saveRegion, hb₁]]
      exact consts_frame s₁
  have hready := ready_afterSave hp (hb₂.trans hb₁) ((g₂ _ (by decide)).trans (congrFun hs₁.gpr .r3))
    (rd₂.trans hs₁.rd) (wr₂.trans hs₁.wr) (consts_ready hb₂ m₂) hframe₂
  have hsaved₂ := consts_saved hs₁.saved hb₂ m₂
  have hread₂ : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r4) 8 := by
    rw [rd₂, wr₂, hs₁.rd, hs₁.wr, g₂ _ (by decide), hs₁.gpr]; exact hp.dataRead
  have hdata : Spec.TripleDes.blockAt s₂.mem (s₂.gpr .r4) =
      Spec.TripleDes.blockAt s.mem (s.gpr .r4) := by
    rw [g₂ _ (by decide), hs₁.gpr]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hframe₂
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  obtain ⟨s₃, run₃, left₃, right₃, mem₃, rd₃, wr₃, regs₃⟩ := blockLoad_ok s₂ hread₂
  have hframe : Frame [spillRegion s₂] s₂.mem s₃.mem := by
    rw [mem₃]; exact Frame.refl _ _
  have hinput := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) hdata
  apply WP.of_runBlock
  refine ⟨s₃, run₃, ?_, hready.congr (regs₃ .r5 (by decide)) (regs₃ .r3 (by decide)) rd₃ wr₃ hframe,
    ?_, rd₃.trans (rd₂.trans hs₁.rd), wr₃.trans (wr₂.trans hs₁.wr), ?_, ?_⟩
  · exact ⟨left₃.trans (congrArg (fun x : BitVec 64 => ((x >>> 32).setWidth 32).setWidth 64) hinput),
      right₃.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hinput)⟩
  · intro i hi
    rw [regs₃ .r5 (by decide), mem₃]
    exact hsaved₂ i hi
  · intro q hq
    have hne : q ≠ .r6 := by revert hq; decide +revert
    exact (regs₃ q hq).trans ((g₂ q hne).trans (congrFun hs₁.gpr q))
  · rw [mem₃]; exact hframe₂

end VG.Proof.TripleDes.PPC64LE
