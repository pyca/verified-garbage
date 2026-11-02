module

public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Setup
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.CT
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Verified
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Absorb
meta import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Setup
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.CT
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Verified
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Frame
public import VerifiedGarbage.Impl.Argon2.RISCV64.HPrime
public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Frame
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Calls
meta import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Calls

@[expose] public section

/-! # Composition helpers for H′ timing proofs -/

namespace VG.RISCV64

theorem RelCT.taintRegs {τ : Taint.T} {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ s₁ s₂, P s₁ s₂ → Taint.Agree τ s₁ s₂) (rs : List Reg) {hc : VG.Taint.Hint Taint.T}
    (h : ((taint.check τ c hc).map fun τ' => (RegSet.ofList rs).subset τ') = some true) :
    RelCT isa P c fun s t => s.sp = t.sp ∧ ∀ r ∈ rs, s.gpr r = t.gpr r := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (hp _ _ hP) e₁ e₂
  exact ⟨ht, ha.1, fun r hr => ha.2 r (RegSet.mem_of_subset hs (RegSet.mem_ofList.mpr hr))⟩

end VG.RISCV64

/-! Merged from `Proof.Argon2.RISCV64.HPrime.UpdateCT`. -/

section
/-! # H′: constant time of a BLAKE2b update -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime

structure UpdateReady (s : State) : Prop where
  work : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr
  data : Covers [⟨s.gpr .a2, (s.gpr .a3).toNat⟩] (s.rd ++ s.wr)
  dataState : (⟨s.gpr .a2, (s.gpr .a3).toNat⟩ : Region).Disjoint ⟨s.gpr .s4, 192⟩
  dataScratch : (⟨s.gpr .a2, (s.gpr .a3).toNat⟩ : Region).Disjoint ⟨s.gpr .s4 + 192, 576⟩

theorem update_keeps (s : State) (h : UpdateReady s) :
    WP isa (update) s (Keeps s) := by
  unfold update
  refine WP.seq ((updateArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := update_call_hyps s u hu h.work h.data h.dataState h.dataScratch
  refine WP.call (k := Proof.Blake2.updateRISCV64 Spec.Blake2.b) update_callee
    pre cover writes ?_ update_noFrames
  intro t rd wr sp frame regs _ _
  refine ⟨fun r hr => ?_, rd.trans hu.rd, wr.trans hu.wr, sp.trans hu.sp, ?_⟩
  · exact (regs r hr).trans (hu.other r (preserved_ne hr) (preserved_ne hr))
  · apply update_frame
    simpa only [hu.mem] using frame

theorem update_rel {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → UpdateReady s₁ ∧ UpdateReady s₂ ∧
      s₁.gpr .s4 = s₂.gpr .s4 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (update) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨(hP _ _ hp).2.2.2.2.2.2, by simp [Taint.ofRegs]⟩) (c := .block updateArgs) (by taint_decide)).wpDep
    (F := UpdateArgs) fun s₁ s₂ _ => ⟨updateArgs_ok s₁, updateArgs_ok s₂⟩
  have call := RelCT.callEx (n := updateName) (k := Proof.Blake2.updateRISCV64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ UpdateArgs σ₁ s₁ ∧ UpdateArgs σ₂ s₂)
    update_callee Proof.Blake2.RISCV64.Stream.updateScratchB_ct
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, data, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := update_call_hyps σ₁ s₁ h₁ p₁.work p₁.data
        p₁.dataState p₁.dataScratch
      obtain ⟨pre₂, cover₂, writes₂⟩ := update_call_hyps σ₂ s₂ h₂ p₂.work p₂.data
        p₂.dataState p₂.dataScratch
      have sp' : s₁.sp = s₂.sp := h₁.sp.trans (sp.trans h₂.sp.symm)
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂⟩
      simp only [Proof.Blake2.updateRISCV64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a4 ∉ linkRegs), State.callEntry_sp, State.withRegions_sp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), count],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), data],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), len],
        by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! Merged from `Proof.Argon2.RISCV64.HPrime.RelatedCT`. -/
section
/-! Merged from `Proof.Argon2.RISCV64.HPrime.InitCT`. -/
section
/-! # H′: constant time of BLAKE2b initialization -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime

structure InitReady (s : State) : Prop where
  length : 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 64
  work : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr

theorem init_keeps (s : State) (h : InitReady s) :
    WP isa (init) s (Keeps s) :=
  (init_ok s h.length h.work).mono fun _ ⟨_, regs, rd, wr, sp, frame⟩ =>
    ⟨regs, rd, wr, sp, init_frame _ frame⟩

theorem init_rel {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → InitReady s₁ ∧ InitReady s₂ ∧
      s₁.gpr .s4 = s₂.gpr .s4 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (init) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨(hP _ _ hp).2.2.2.2, by simp [Taint.ofRegs]⟩) (c := .block initArgs) (by taint_decide)).wpDep
    (F := InitArgs) fun s₁ s₂ _ => ⟨initArgs_ok s₁, initArgs_ok s₂⟩
  have call := RelCT.callEx (n := initName) (k := Proof.Blake2.initRISCV64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ InitArgs σ₁ s₁ ∧ InitArgs σ₂ s₂)
    init_callee Proof.Blake2.RISCV64.Stream.initB_ct
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := init_call_hyps σ₁ s₁ h₁ p₁.length p₁.work
      obtain ⟨pre₂, cover₂, writes₂⟩ := init_call_hyps σ₂ s₂ h₂ p₂.length p₂.work
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂⟩
      · simp only [Proof.Blake2.initRISCV64, State.withRegions_gpr,
          State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs),
          State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
          State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs),
          State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs)]
        exact ⟨by rw [h₁.state, h₂.state, base],
          by rw [h₁.other _ (by decide) (by decide) (by decide),
            h₂.other _ (by decide) (by decide) (by decide), len],
          by rw [h₁.key, h₂.key, base], by rw [h₁.keylen, h₂.keylen], h₁.sp.trans (sp.trans h₂.sp.symm)⟩
  exact args.seq call

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! Merged from `Proof.Argon2.RISCV64.HPrime.FinalizeCT`. -/
section
/-! # H′: constant time of BLAKE2b finalization -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime

structure FinalizeReady (s : State) : Prop where
  work : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr

theorem FinalizeReady.keeps {s t : State} (h : FinalizeReady s) (k : Keeps s t) : FinalizeReady t := by
  refine ⟨?_⟩
  rw [k.wr, k.s4]; exact h.work

theorem finalize_keeps (s : State) (h : FinalizeReady s) :
    WP isa (finalize) s (Keeps s) := by
  unfold finalize
  refine WP.seq ((finalizeArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := finalize_call_hyps s u hu h.work
  refine WP.call (k := Proof.Blake2.finalizeRISCV64 Spec.Blake2.b) finalize_callee
    pre cover writes ?_ finalize_noFrames
  intro t rd wr sp frame regs _ _
  refine ⟨fun r hr => ?_, rd.trans hu.rd, wr.trans hu.wr, sp.trans hu.sp, ?_⟩
  · exact (regs r hr).trans (hu.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr))
  · apply finalize_frame
    simpa only [hu.mem] using frame

theorem finalize_rel {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → FinalizeReady s₁ ∧ FinalizeReady s₂ ∧
      s₁.gpr .s4 = s₂.gpr .s4 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (finalize) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨(hP _ _ hp).2.2.2.2, by simp [Taint.ofRegs]⟩) (c := .block finalizeArgs) (by taint_decide)).wpDep
    (F := FinalizeArgs) fun s₁ s₂ _ => ⟨finalizeArgs_ok s₁, finalizeArgs_ok s₂⟩
  have call := RelCT.callEx (n := finalizeName) (k := Proof.Blake2.finalizeRISCV64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ FinalizeArgs σ₁ s₁ ∧ FinalizeArgs σ₂ s₂)
    finalize_callee Proof.Blake2.RISCV64.Stream.finalizeScratchB_ct
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := finalize_call_hyps σ₁ s₁ h₁ p₁.work
      obtain ⟨pre₂, cover₂, writes₂⟩ := finalize_call_hyps σ₂ s₂ h₂ p₂.work
      have sp' : s₁.sp = s₂.sp := h₁.sp.trans (sp.trans h₂.sp.symm)
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂⟩
      simp only [Proof.Blake2.finalizeRISCV64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs), State.callEntry_sp, State.withRegions_sp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), count],
        by rw [h₁.digest, h₂.digest, base], by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! Merged from `Proof.Argon2.RISCV64.HPrime.BlocksCT`. -/
section
/-! # H′: constant time of public argument handling and copying -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime

def publicRegs : List Reg := [.s4, .s0, .s1, .s2, .s3]
def AgreeRegs (rs : List Reg) (s t : State) : Prop :=
  s.sp = t.sp ∧ ∀ r ∈ rs, s.gpr r = t.gpr r

theorem AgreeRegs.taint {rs : List Reg} {s t : State} (h : AgreeRegs rs s t) :
    RISCV64.Taint.Agree (Taint.ofRegs rs) s t :=
  ⟨h.1, fun r hr => h.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem publicRegs_callee : ∀ r ∈ publicRegs, r ∈ preserved := by decide


theorem setup_rel :
    RelCT isa (AgreeRegs [.a0, .a1, .a2, .a3, .a4]) (.block setup)
      (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ hp => hp.taint) publicRegs (by taint_decide)

theorem chooseLength_rel : RelCT isa (AgreeRegs publicRegs) chooseLength
    (AgreeRegs (.a1 :: publicRegs)) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => hp.taint) (.a1 :: publicRegs) (by taint_decide)

theorem copy_rel : RelCT isa (AgreeRegs (.a6 :: publicRegs)) copy (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs (.a6 :: publicRegs))
    (fun _ _ hp => hp.taint) publicRegs (by taint_decide)

theorem emitPrefix_rel : RelCT isa (AgreeRegs publicRegs) emitPrefix (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => hp.taint) publicRegs (by taint_decide)

theorem copyRemaining_rel : RelCT isa (AgreeRegs publicRegs) copyRemaining (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => hp.taint) publicRegs (by taint_decide)

theorem restore_rel : RelCT isa (AgreeRegs [.s4]) (.block restore) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.s4]) (fun _ _ hp => hp.taint)
    (by taint_decide)

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! # H′: retaining public caller state across hash calls -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime

/-- Caller conditions that survive hashing in the workspace. -/
structure Stable (F : State → Prop) : Prop where
  ready : ∀ s, F s → FinalizeReady s
  keeps : ∀ s t, F s → Keeps s t → F t

def Related (F : State → Prop) (s t : State) : Prop := F s ∧ F t ∧ AgreeRegs publicRegs s t

theorem Related.keeps {F : State → Prop} (stable : Stable F) {s₁ s₂ t₁ t₂ : State}
    (h : Related F s₁ s₂) (k₁ : Keeps s₁ t₁) (k₂ : Keeps s₂ t₂) : Related F t₁ t₂ := by
  refine ⟨stable.keeps _ _ h.1 k₁, stable.keeps _ _ h.2.1 k₂,
    k₁.sp.trans (h.2.2.1.trans k₂.sp.symm), fun r hr => ?_⟩
  rw [k₁.regs _ (publicRegs_callee r hr), k₂.regs _ (publicRegs_callee r hr)]
  exact h.2.2.2 r hr

theorem keeps_rel {F : State → Prop} (stable : Stable F) {P : State → State → Prop} {c : Prog isa}
    (ct : RelCT isa P c fun _ _ => True)
    (wp : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ (Keeps s₁) ∧ WP isa c s₂ (Keeps s₂))
    (pre : ∀ s₁ s₂, P s₁ s₂ → Related F s₁ s₂) : RelCT isa P c (Related F) :=
  (ct.wpDep wp).mono (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, k₁, k₂⟩ =>
    (pre _ _ hp).keeps stable k₁ k₂

theorem stable_init_rel {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧
      (1 ≤ (s₁.gpr .a1).toNat ∧ (s₁.gpr .a1).toNat ≤ 64) ∧ s₁.gpr .a1 = s₂.gpr .a1)
      (init) (Related F) := by
  have ready (s : State) (hs : F s) (len : 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 64) :
      InitReady s := by
    have h := stable.ready s hs
    exact ⟨len, h.work⟩
  apply keeps_rel stable (init_rel ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨ready s₁ h.1 len, ready s₂ h.2.1 (by rw [← eq]; exact len),
      h.2.2.2 _ (by decide), eq, h.2.2.1⟩
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨init_keeps s₁ (ready s₁ h.1 len),
      init_keeps s₂ (ready s₂ h.2.1 (by rw [← eq]; exact len))⟩

theorem stable_finalize_rel {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧ s₁.gpr .a1 = s₂.gpr .a1)
      (finalize) (Related F) := by
  apply keeps_rel stable (finalize_rel ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, count⟩
    exact ⟨stable.ready _ h.1, stable.ready _ h.2.1,
      h.2.2.2 _ (by decide), count, h.2.2.1⟩
  · intro s₁ s₂ ⟨h, _⟩
    exact ⟨finalize_keeps s₁ (stable.ready _ h.1), finalize_keeps s₂ (stable.ready _ h.2.1)⟩

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! # H′: constant time of hashing a fixed workspace buffer -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime

theorem FixedArgs.keeps {s t : State} {offset size : Nat} (h : FixedArgs s t offset size) : Keeps s t := by
  refine ⟨fun r hr => ?_, h.rd, h.wr, h.sp, ?_⟩
  · exact h.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr)
  · rw [h.mem]; exact Frame.refl _ _

theorem fixed_ready {s t : State} {offset size : Nat} (ready : FinalizeReady s)
    (h : FixedArgs s t offset size) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    UpdateReady t := by
  have k := h.keeps
  have len : (t.gpr .a3).toNat = size := by
    rw [h.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨(ready.keeps k).work, ?_, ?_, ?_⟩
  · apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .s4, 16384⟩, List.mem_append_right _ (k.wr.symm ▸ ready.work), offset, h.data, ?_⟩
    change offset + (t.gpr .a3).toNat ≤ 16384
    rw [len]; exact hi
  · rw [h.data, len, k.s4]
    exact (Offset.base_disjoint _ (by omega) (by omega)).symm
  · rw [h.data, len, k.s4]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega) (by omega) (by decide)

theorem absorbFixed_keeps (s : State) (offset size : Nat)
    (ready : FinalizeReady s) (offsetBound : offset < 2048) (sizeBound : size < 2048) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    WP isa (absorbFixed offset size) s (Keeps s) := by
  unfold absorbFixed
  refine WP.seq ((fixedArgs_ok s offset size offsetBound sizeBound).mono fun u hu => ?_)
  exact (update_keeps u (fixed_ready ready hu lo hi)).mono fun _ h => hu.keeps.trans h

theorem absorbFixed_rel (offset size : Nat)
    (offsetBound : offset < 2048) (sizeBound : size < 2048) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384)
    (ct : ∃ hint, (taint.check (Taint.ofRegs []) (.block (fixedArgs offset size)) hint).isSome = true)
    {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (absorbFixed offset size) (Related F) := by
  obtain ⟨_, ct⟩ := ct
  have args := (RelCT.taint (A := taint) (P := Related F) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩) (c := .block (fixedArgs offset size))
    ct).wpDep (F := fun s t => FixedArgs s t offset size)
    fun s₁ s₂ _ => ⟨fixedArgs_ok s₁ offset size offsetBound sizeBound,
      fixedArgs_ok s₂ offset size offsetBound sizeBound⟩
  have call := update_rel (P := fun s₁ s₂ => True ∧
      ∃ σ₁ σ₂, Related F σ₁ σ₂ ∧ FixedArgs σ₁ s₁ offset size ∧ FixedArgs σ₂ s₂ offset size)
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      have base := hp.2.2.2 .s4 (by decide)
      have sp := hp.2.2.1
      exact ⟨fixed_ready (stable.ready _ hp.1) h₁ lo hi, fixed_ready (stable.ready _ hp.2.1) h₂ lo hi,
        by rw [h₁.keeps.s4, h₂.keeps.s4, base], by rw [h₁.count, h₂.count],
        by rw [h₁.data, h₂.data, base], by rw [h₁.size, h₂.size], by rw [h₁.keeps.sp, h₂.keeps.sp, sp]⟩
  exact keeps_rel stable (args.seq call)
    (fun s₁ s₂ hp => ⟨absorbFixed_keeps s₁ offset size (stable.ready _ hp.1) offsetBound sizeBound lo hi,
      absorbFixed_keeps s₂ offset size (stable.ready _ hp.2.1) offsetBound sizeBound lo hi⟩) (fun _ _ h => h)

end VG.Proof.Argon2.RISCV64.HPrime
