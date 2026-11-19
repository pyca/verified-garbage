module

public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Correct
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Correct
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
meta import VerifiedGarbage.Proof.MdStream.X86_64.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Update
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize
meta import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Update
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill

/-! ### `Argon2.X86_64.HPrime.FixedCT`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Argon2.X86_64.HPrime.UpdateCT`. -/

@[expose] public section

section
/-! # H′: constant time of a BLAKE2b update -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure UpdateReady (s : State) : Prop where
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  data : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] (s.rd ++ s.wr)
  dataState : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 192⟩
  dataScratch : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx + 192, 576⟩
  stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩

theorem update_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : UpdateReady s) :
    WP isa (update (hash v)) s (Keeps s) := by
  unfold update
  refine WP.seq ((updateArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := update_call_hyps s u hu h.work h.data
    h.dataState h.dataScratch h.stackWork h.stackData
  refine WP.call (k := Proof.Blake2.updateX86_64 Spec.Blake2.b) v.update_correct (hash_ok v).updateNoSp
    (by change 8 * (hash v).update.depth + 16 < 2 ^ 64; rw [(hash_ok v).updateDepth]; decide)
    pre cover writes ?_
  intro t rd wr regs frame _ _
  refine ⟨fun r hr => ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .r8 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (regs r hr).trans (hu.other r hn.1 hn.2)
  · apply update_frame
    change Frame (_ ++ [below (u.gpr .rsp) (8 * ((hash v).update.depth + 1))]) u.mem t.mem at frame
    simpa only [(hash_ok v).updateDepth, hu.other .rsp (by decide) (by decide), hu.mem,
      List.cons_append, List.nil_append] using frame

theorem update_rel (v : Proof.Blake2.X86_64.Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → UpdateReady s₁ ∧ UpdateReady s₂ ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (update (hash v)) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block updateArgs) (by taint_decide)).wpDep
    (F := UpdateArgs) fun s₁ s₂ _ => ⟨updateArgs_ok s₁, updateArgs_ok s₂⟩
  have call := RelCT.callEx (n := (hash v).updateName) (k := Proof.Blake2.updateX86_64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ UpdateArgs σ₁ s₁ ∧ UpdateArgs σ₂ s₂)
    v.update_correct v.updateCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, data, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := update_call_hyps σ₁ s₁ h₁ p₁.work p₁.data
        p₁.dataState p₁.dataScratch p₁.stackWork p₁.stackData
      obtain ⟨pre₂, cover₂, writes₂⟩ := update_call_hyps σ₂ s₂ h₂ p₂.work p₂.data
        p₂.dataState p₂.dataScratch p₂.stackWork p₂.stackData
      have sp' : s₁.gpr .rsp = s₂.gpr .rsp := by
        rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), sp]
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂, sp'⟩
      simp only [Proof.Blake2.updateX86_64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_rsp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), count],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), data],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), len],
        by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.RelatedCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.HPrime.InitCT`. -/
section
/-! # H′: constant time of BLAKE2b initialization -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure InitReady (s : State) : Prop where
  length : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rbx, 192⟩

theorem init_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : InitReady s) :
    WP isa (init (hash v)) s (Keeps s) :=
  (init_ok v s h.length h.work h.stack).mono fun _ ⟨_, regs, rd, wr, frame⟩ =>
    ⟨regs, rd, wr, init_frame _ _ frame⟩

theorem init_rel (v : Proof.Blake2.X86_64.Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → InitReady s₁ ∧ InitReady s₂ ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (init (hash v)) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block initArgs) (by taint_decide)).wpDep
    (F := InitArgs) fun s₁ s₂ _ => ⟨initArgs_ok s₁, initArgs_ok s₂⟩
  have call := RelCT.callEx (n := (hash v).initName) (k := Proof.Blake2.initX86_64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ InitArgs σ₁ s₁ ∧ InitArgs σ₂ s₂)
    Proof.Blake2.X86_64.Stream.initB_correct Proof.Blake2.X86_64.Stream.initB_ct
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := init_call_hyps σ₁ s₁ h₁ p₁.length p₁.work p₁.stack
      obtain ⟨pre₂, cover₂, writes₂⟩ := init_call_hyps σ₂ s₂ h₂ p₂.length p₂.work p₂.stack
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂, ?_⟩
      · simp only [Proof.Blake2.initX86_64, State.withRegions_gpr,
          State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp)]
        exact ⟨by rw [h₁.state, h₂.state, base],
          by rw [h₁.other _ (by decide) (by decide) (by decide),
            h₂.other _ (by decide) (by decide) (by decide), len],
          by rw [h₁.key, h₂.key, base], by rw [h₁.keylen, h₂.keylen]⟩
      · rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), sp]
  exact args.seq call

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.FinalizeCT`. -/
section
/-! # H′: constant time of BLAKE2b finalization -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure FinalizeReady (s : State) : Prop where
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩

theorem FinalizeReady.keeps {s t : State} (h : FinalizeReady s) (k : Keeps s t) : FinalizeReady t := by
  constructor
  · rw [k.wr, k.rbx]; exact h.work
  · rw [k.rsp, k.rbx]; exact h.stack

theorem finalize_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : FinalizeReady s) :
    WP isa (finalize (hash v)) s (Keeps s) := by
  unfold finalize
  refine WP.seq ((finalizeArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := finalize_call_hyps s u hu h.work h.stack
  refine WP.call (k := Proof.Blake2.finalizeX86_64 Spec.Blake2.b) v.finalize_correct (hash_ok v).finalizeNoSp
    (by change 8 * (hash v).finalize.depth + 16 < 2 ^ 64; rw [(hash_ok v).finalizeDepth]; decide)
    pre cover writes ?_
  intro t rd wr regs frame _ _
  refine ⟨fun r hr => ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (regs r hr).trans (hu.other r hn.1 hn.2.1 hn.2.2)
  · apply finalize_frame
    change Frame (_ ++ [below (u.gpr .rsp) (8 * ((hash v).finalize.depth + 1))]) u.mem t.mem at frame
    simpa only [(hash_ok v).finalizeDepth, hu.other .rsp (by decide) (by decide) (by decide), hu.mem,
      List.cons_append, List.nil_append] using frame

theorem finalize_rel (v : Proof.Blake2.X86_64.Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → FinalizeReady s₁ ∧ FinalizeReady s₂ ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (finalize (hash v)) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block finalizeArgs) (by taint_decide)).wpDep
    (F := FinalizeArgs) fun s₁ s₂ _ => ⟨finalizeArgs_ok s₁, finalizeArgs_ok s₂⟩
  have call := RelCT.callEx (n := (hash v).finalizeName) (k := Proof.Blake2.finalizeX86_64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ FinalizeArgs σ₁ s₁ ∧ FinalizeArgs σ₂ s₂)
    v.finalize_correct v.finalizeCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := finalize_call_hyps σ₁ s₁ h₁ p₁.work p₁.stack
      obtain ⟨pre₂, cover₂, writes₂⟩ := finalize_call_hyps σ₂ s₂ h₂ p₂.work p₂.stack
      have sp' : s₁.gpr .rsp = s₂.gpr .rsp := by
        rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), sp]
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂, sp'⟩
      simp only [Proof.Blake2.finalizeX86_64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_rsp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), count],
        by rw [h₁.digest, h₂.digest, base], by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.BlocksCT`. -/
section
/-! # H′: constant time of argument handling and output loops -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

def publicRegs : List Reg := [.rbx, .r12, .r13, .r14, .r15, .rsp]

def AgreeRegs (rs : List Reg) (s t : State) : Prop := ∀ r ∈ rs, s.gpr r = t.gpr r

theorem publicRegs_callee : ∀ r ∈ publicRegs, r ∈ calleeSaved := by decide

theorem setup_rel :
    RelCT isa (AgreeRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) (.block setup)
      (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp])
    (fun _ _ hp => Taint.agree_ofRegs hp) publicRegs (by taint_decide)

theorem chooseLength_rel : RelCT isa (AgreeRegs publicRegs) chooseLength
    (AgreeRegs (.rsi :: publicRegs)) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => Taint.agree_ofRegs hp) (.rsi :: publicRegs) (by taint_decide)

theorem emitPrefix_rel : RelCT isa (AgreeRegs publicRegs) emitPrefix (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => Taint.agree_ofRegs hp) publicRegs (by taint_decide)

theorem copyRemaining_rel : RelCT isa (AgreeRegs publicRegs) copyRemaining (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => Taint.agree_ofRegs hp) publicRegs (by taint_decide)

theorem restore_rel : RelCT isa (AgreeRegs [.rbx]) (.block restore) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbx]) (fun _ _ hp => Taint.agree_ofRegs hp)
    (by taint_decide)

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: retaining public caller state across hash calls -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

/-- Caller conditions that survive hashing in the workspace. -/
structure Stable (F : State → Prop) : Prop where
  ready : ∀ s, F s → FinalizeReady s
  keeps : ∀ s t, F s → Keeps s t → F t

def Related (F : State → Prop) (s t : State) : Prop := F s ∧ F t ∧ AgreeRegs publicRegs s t

theorem Related.keeps {F : State → Prop} (stable : Stable F) {s₁ s₂ t₁ t₂ : State}
    (h : Related F s₁ s₂) (k₁ : Keeps s₁ t₁) (k₂ : Keeps s₂ t₂) : Related F t₁ t₂ := by
  refine ⟨stable.keeps _ _ h.1 k₁, stable.keeps _ _ h.2.1 k₂, fun r hr => ?_⟩
  rw [k₁.regs _ (publicRegs_callee r hr), k₂.regs _ (publicRegs_callee r hr)]
  exact h.2.2 r hr

theorem keeps_rel {F : State → Prop} (stable : Stable F) {P : State → State → Prop} {c : Prog isa}
    (ct : RelCT isa P c fun _ _ => True)
    (wp : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ (Keeps s₁) ∧ WP isa c s₂ (Keeps s₂))
    (pre : ∀ s₁ s₂, P s₁ s₂ → Related F s₁ s₂) : RelCT isa P c (Related F) :=
  (ct.wpDep wp).mono (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, k₁, k₂⟩ =>
    (pre _ _ hp).keeps stable k₁ k₂

theorem stable_init_rel (v : Proof.Blake2.X86_64.Backend) {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧
      (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi)
      (init (hash v)) (Related F) := by
  have ready (s : State) (hs : F s) (len : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64) :
      InitReady s := by
    have h := stable.ready s hs
    exact ⟨len, h.work, (h.stack.sub_left (below_sub (by decide) (by decide))).sub_right
      (Region.sub_prefix (by decide))⟩
  apply keeps_rel stable (init_rel v ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨ready s₁ h.1 len, ready s₂ h.2.1 (by rw [← eq]; exact len),
      h.2.2 _ (by decide), eq, h.2.2 _ (by decide)⟩
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨init_keeps v s₁ (ready s₁ h.1 len),
      init_keeps v s₂ (ready s₂ h.2.1 (by rw [← eq]; exact len))⟩

theorem stable_finalize_rel (v : Proof.Blake2.X86_64.Backend) {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi)
      (finalize (hash v)) (Related F) := by
  apply keeps_rel stable (finalize_rel v ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, count⟩
    exact ⟨stable.ready _ h.1, stable.ready _ h.2.1,
      h.2.2 _ (by decide), count, h.2.2 _ (by decide)⟩
  · intro s₁ s₂ ⟨h, _⟩
    exact ⟨finalize_keeps v s₁ (stable.ready _ h.1), finalize_keeps v s₂ (stable.ready _ h.2.1)⟩

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: constant time of hashing a fixed workspace buffer -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem FixedArgs.keeps {s t : State} {offset size : Nat} (h : FixedArgs s t offset size) : Keeps s t := by
  refine ⟨fun r hr => ?_, h.rd, h.wr, ?_⟩
  · have hn : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r hn.1 hn.2.1 hn.2.2
  · rw [h.mem]; exact Frame.refl _ _

theorem fixed_ready {s t : State} {offset size : Nat} (ready : FinalizeReady s)
    (h : FixedArgs s t offset size) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    UpdateReady t := by
  have k := h.keeps
  have len : (t.gpr .rcx).toNat = size := by
    rw [h.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi])]
  refine ⟨(ready.keeps k).work, ?_, ?_, ?_, (ready.keeps k).stack, ?_⟩
  · apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .rbx, 16384⟩, List.mem_append_right _ (k.wr.symm ▸ ready.work), offset, h.data, ?_⟩
    change offset + (t.gpr .rcx).toNat ≤ 16384
    rw [len]; exact hi
  · rw [h.data, len, k.rbx]
    exact (Offset.base_disjoint _ (by omega_using [lo]) (by omega_using [hi])).symm
  · rw [h.data, len, k.rbx]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega_using [lo]) (by omega_using [hi]) (by decide)
  · rw [k.rsp, h.data, len]
    exact ready.stack.sub_right (Offset.sub_base _ hi)

theorem absorbFixed_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (offset size : Nat)
    (ready : FinalizeReady s) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    WP isa (absorbFixed (hash v) offset size) s (Keeps s) := by
  unfold absorbFixed
  refine WP.seq ((fixedArgs_ok s offset size (by omega_using [hi]) (by omega_using [hi])).mono fun u hu => ?_)
  exact (update_keeps v u (fixed_ready ready hu lo hi)).mono fun _ h => hu.keeps.trans h

theorem absorbFixed_rel (v : Proof.Blake2.X86_64.Backend) (offset size : Nat)
    (lo : 768 ≤ offset) (hi : offset + size ≤ 16384)
    (ct : ∃ hint, (taint.check (Taint.ofRegs []) (.block (fixedArgs offset size)) hint).isSome = true)
    {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (absorbFixed (hash v) offset size) (Related F) := by
  obtain ⟨_, ct⟩ := ct
  have args := (RelCT.taint (A := taint) (P := Related F) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block (fixedArgs offset size))
    ct).wpDep (F := fun s t => FixedArgs s t offset size)
    fun s₁ s₂ _ => ⟨fixedArgs_ok s₁ offset size (by omega_using [hi]) (by omega_using [hi]),
      fixedArgs_ok s₂ offset size (by omega_using [hi]) (by omega_using [hi])⟩
  have call := update_rel v (P := fun s₁ s₂ => True ∧
      ∃ σ₁ σ₂, Related F σ₁ σ₂ ∧ FixedArgs σ₁ s₁ offset size ∧ FixedArgs σ₂ s₂ offset size)
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      have base := hp.2.2 .rbx (by decide)
      have sp := hp.2.2 .rsp (by decide)
      exact ⟨fixed_ready (stable.ready _ hp.1) h₁ lo hi, fixed_ready (stable.ready _ hp.2.1) h₂ lo hi,
        by rw [h₁.keeps.rbx, h₂.keeps.rbx, base], by rw [h₁.count, h₂.count],
        by rw [h₁.data, h₂.data, base], by rw [h₁.size, h₂.size], by rw [h₁.keeps.rsp, h₂.keeps.rsp, sp]⟩
  exact keeps_rel stable (args.seq call)
    (fun s₁ s₂ hp => ⟨absorbFixed_keeps v s₁ offset size (stable.ready _ hp.1) lo hi,
      absorbFixed_keeps v s₂ offset size (stable.ready _ hp.2.1) lo hi⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.HPrime

end

end

/-! Merged from `Proof.Argon2.X86_64.HPrime.OutputCT`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.X86_64.HPrime.NextCT`. -/
section
/-! # H′: constant time of hashing the previous digest -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov32i)

theorem count64_ok (s : State) : WP isa (.block [.mov32 .rsi (.imm 64)]) s fun t =>
    Keeps s t ∧ t.gpr .rsi = 64 := by
  refine wp_mov32i fun t ht _ _ => WP.block_nil ⟨?_, ht.gpr⟩
  refine ⟨fun r hr => ?_, ht.rd, ht.wr, ?_⟩
  · have hn : r ≠ .rsi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ht.other r hn
  · rw [ht.mem]; exact Frame.refl _ _

theorem count64_rel {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (.block [.mov32 .rsi (.imm 64)])
      (fun s₁ s₂ => Related F s₁ s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  have ct := (RelCT.taint (A := taint) (P := Related F) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block [.mov32 .rsi (.imm 64)])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨count64_ok s₁, count64_ok s₂⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, k₁, k₂⟩ =>
    ⟨hp.keeps stable k₁.1 k₂.1, k₁.2.trans k₂.2.symm⟩

theorem next_rel (v : Proof.Blake2.X86_64.Backend) {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧
      (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi)
      (next (hash v)) (Related F) :=
  (stable_init_rel v stable).seq
    ((absorbFixed_rel v 768 64 (by decide) (by decide) ⟨_, by taint_decide⟩ stable).seq
      ((count64_rel stable).seq (stable_finalize_rel v stable)))

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.InputCT`. -/
section
/-! # H′: public input bounds and constant-time absorption -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure OutputReady (s : State) : Prop where
  space : Space s (s.gpr .r15).toNat
  positive : 1 ≤ (s.gpr .r15).toNat
  bound : (s.gpr .r15).toNat < 2 ^ 32

theorem output_stable : Stable OutputReady where
  ready _ h := ⟨h.space.work, h.space.stackWork⟩
  keeps s t h k := by
    have n := k.regs .r15 (by decide)
    refine ⟨?_, ?_, ?_⟩
    · rw [n]; exact h.space.keeps k
    · rw [n]; exact h.positive
    · rw [n]; exact h.bound

structure FirstReady (s : State) : Prop extends OutputReady s where
  length : (s.gpr .r13).toNat < 2 ^ 32
  data : Covers [⟨s.gpr .r12, (s.gpr .r13).toNat⟩] (s.rd ++ s.wr)
  dataWork : (⟨s.gpr .r12, (s.gpr .r13).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r12, (s.gpr .r13).toNat⟩

theorem first_stable : Stable FirstReady where
  ready _ h := output_stable.ready _ h.toOutputReady
  keeps s t h k := by
    have ptr := k.regs .r12 (by decide)
    have len := k.regs .r13 (by decide)
    refine ⟨output_stable.keeps s t h.toOutputReady k, ?_, ?_, ?_, ?_⟩
    · rw [len]; exact h.length
    · rw [ptr, len, k.rd, k.wr]; exact h.data
    · rw [ptr, len, k.rbx]; exact h.dataWork
    · rw [ptr, len, k.rsp]; exact h.stackData

theorem input_ready {s t : State} (ready : FirstReady s) (h : InputArgs s t) : UpdateReady t := by
  have k := h.keeps
  refine ⟨(first_stable.ready _ (first_stable.keeps _ _ ready k)).work, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.data, h.size, h.rd, h.wr]; exact ready.data
  · rw [h.data, h.size, k.rbx]; exact ready.dataWork.sub_right (Region.sub_prefix (by decide))
  · rw [h.data, h.size, k.rbx]; exact ready.dataWork.sub_right (Offset.sub_base _ (by decide))
  · rw [k.rbx, k.rsp]; exact ready.space.stackWork
  · rw [h.data, h.size, k.rsp]; exact ready.stackData

theorem absorbInput_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : FirstReady s) :
    WP isa (absorbInput (hash v)) s (Keeps s) := by
  unfold absorbInput
  refine WP.seq ((inputArgs_ok s).mono fun u hu => ?_)
  exact (update_keeps v u (input_ready h hu)).mono fun _ ht => hu.keeps.trans ht

theorem absorbInput_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (Related FirstReady) (absorbInput (hash v)) (Related FirstReady) := by
  have args := (RelCT.taint (A := taint) (P := Related FirstReady) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block inputArgs) (by taint_decide)).wpDep
    (F := InputArgs) fun s₁ s₂ _ => ⟨inputArgs_ok s₁, inputArgs_ok s₂⟩
  have call := update_rel v (P := fun s₁ s₂ => True ∧
      ∃ σ₁ σ₂, Related FirstReady σ₁ σ₂ ∧ InputArgs σ₁ s₁ ∧ InputArgs σ₂ s₂)
    fun _ _ ⟨_, _, _, hp, h₁, h₂⟩ => by
      exact ⟨input_ready hp.1 h₁, input_ready hp.2.1 h₂,
        by rw [h₁.keeps.rbx, h₂.keeps.rbx]; exact hp.2.2 _ (by decide),
        by rw [h₁.count, h₂.count],
        by rw [h₁.data, h₂.data]; exact hp.2.2 _ (by decide),
        by rw [h₁.size, h₂.size]; exact hp.2.2 _ (by decide),
        by rw [h₁.keeps.rsp, h₂.keeps.rsp]; exact hp.2.2 _ (by decide)⟩
  exact keeps_rel first_stable (args.seq call)
    (fun s₁ s₂ hp => ⟨absorbInput_keeps v s₁ hp.1, absorbInput_keeps v s₂ hp.2.1⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.FirstCT`. -/
section
/-! # H′: constant time of the initial length-prefixed hash -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov wp_addi)

theorem chooseFirst_rel : RelCT isa (Related FirstReady) chooseLength
    (fun s₁ s₂ => Related FirstReady s₁ s₂ ∧
      (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  have ct := (chooseLength_rel.mono (P' := Related FirstReady)
    (fun _ _ hp => hp.2.2) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ _ => ⟨chooseLength_ok s₁, chooseLength_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨pub, s₁, s₂, hp, ⟨len₁, k₁⟩, ⟨_, k₂⟩⟩
  refine ⟨hp.keeps first_stable k₁ k₂, ?_, pub _ (List.mem_cons_self ..)⟩
  rw [len₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [] : min (s₁.gpr .r15).toNat 64 < 2 ^ 64)]
  have := hp.1.positive
  omega_using [this]

theorem inputCount_ok (s : State) :
    WP isa (.block [.mov .rsi (.reg .r13), .alu .add .rsi (.imm 4)]) s fun t =>
      Keeps s t ∧ t.gpr .rsi = s.gpr .r13 + 4 := by
  refine wp_mov fun a ha _ _ => wp_addi fun t ht => WP.block_nil ⟨?_, ?_⟩
  · refine ⟨fun r hr => ?_, ht.rd.trans ha.rd, ht.wr.trans ha.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (ht.other r hn).trans (ha.other r hn)
    · rw [ht.mem, ha.mem]; exact Frame.refl _ _
  · rw [ht.gpr, ha.gpr]; rfl

theorem inputCount_rel :
    RelCT isa (Related FirstReady) (.block [.mov .rsi (.reg .r13), .alu .add .rsi (.imm 4)])
      (fun s₁ s₂ => Related FirstReady s₁ s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  have ct := (RelCT.taint (A := taint) (P := Related FirstReady) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov .rsi (.reg .r13), .alu .add .rsi (.imm 4)]) (by taint_decide)).wpDep
    (fun s₁ s₂ _ => ⟨inputCount_ok s₁, inputCount_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, hp, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩
  refine ⟨hp.keeps first_stable k₁ k₂, ?_⟩
  rw [c₁, c₂, hp.2.2 .r13 (by decide)]

theorem first_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (Related FirstReady) (first (hash v)) (Related FirstReady) :=
  chooseFirst_rel.seq ((stable_init_rel v first_stable).seq
    ((absorbFixed_rel v 832 4 (by decide) (by decide) ⟨_, by taint_decide⟩ first_stable).seq
    ((absorbInput_rel v).seq (inputCount_rel.seq (stable_finalize_rel v first_stable)))))

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: public output counters and prefix emission -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_cmpi)

def LoopReady (s : State) : Prop := OutputReady s ∧ 65 ≤ (s.gpr .r15).toNat

theorem loop_stable : Stable LoopReady where
  ready _ h := output_stable.ready _ h.1
  keeps s t h k := ⟨output_stable.keeps s t h.1 k,
    by rw [k.regs .r15 (by decide)]; exact h.2⟩

theorem sub32_nat (v : BitVec 64) (h : 32 ≤ v.toNat) : (v - 32).toNat = v.toNat - 32 := by
  have eq : v - 32 = BitVec.ofNat 64 (v.toNat - 32) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl] using (Offset.ofNat_sub_ofNat (w := 64) h)
  rw [eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.isLt; omega_using [])]

theorem Emitted.ready {s t : State} (h : Emitted s t) (pre : LoopReady s) : OutputReady t := by
  have count : (t.gpr .r15).toNat = (s.gpr .r15).toNat - 32 := by
    rw [h.remaining, sub32_nat _ (by have := pre.2; omega_using [this])]
  refine ⟨?_, ?_, ?_⟩
  · rw [count]
    apply pre.1.space.advance (Written.of_emitted h)
    simp only [Spec.Blake2.bytesAt, List.length_map, List.length_range]
    have := pre.2
    omega_using [this]
  · rw [count]; have := pre.2; omega_using [this]
  · rw [count]; have := pre.1.bound; omega_using [this]

theorem emit_ready (v : State) (h : LoopReady v) : WP isa emitPrefix v (Emitted v) := by
  have space := h.1.space.prefix (show 32 ≤ (v.gpr .r15).toNat by have := h.2; omega_using [this])
  exact emitPrefix_ok v space.work space.out
    (space.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384)))

theorem emit_rel : RelCT isa (Related LoopReady) emitPrefix (Related OutputReady) := by
  have ct := (emitPrefix_rel.mono (P' := Related LoopReady)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨emit_ready s₁ hp.1, emit_ready s₂ hp.2.1⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨pub, _, _, hp, h₁, h₂⟩ =>
    ⟨h₁.ready hp.1, h₂.ready hp.2.1, pub⟩

theorem count64_init_rel {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (.block [.mov32 .rsi (.imm 64)])
      (fun s₁ s₂ => Related F s₁ s₂ ∧
        (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  have ct := (count64_rel stable).wpDep (fun s₁ s₂ _ => ⟨count64_ok s₁, count64_ok s₂⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨⟨hp, eq⟩, _, _, _, ⟨_, len⟩, _⟩ =>
    ⟨hp, by rw [len]; decide, eq⟩

theorem compare_ok (s : State) : WP isa (.block [.alu .cmp .r15 (.imm 65)]) s fun t =>
    Keeps s t ∧ t.cf = some (decide ((s.gpr .r15).toNat < 65)) := by
  refine wp_cmpi fun t gt mt rt wt cf _ => WP.block_nil ⟨?_, cf⟩
  exact ⟨fun r _ => congrFun gt r, rt, wt, by rw [mt]; exact Frame.refl _ _⟩

theorem compare_rel {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (.block [.alu .cmp .r15 (.imm 65)])
      (fun s₁ s₂ => Related F s₁ s₂ ∧ s₁.cf = s₂.cf ∧
        s₁.cf = some (decide ((s₁.gpr .r15).toNat < 65))) := by
  have ct := (RelCT.taint (A := taint) (P := Related F) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block [.alu .cmp .r15 (.imm 65)])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨compare_ok s₁, compare_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, hp, ⟨k₁, cf₁⟩, ⟨k₂, cf₂⟩⟩
  refine ⟨hp.keeps stable k₁ k₂, ?_, ?_⟩
  · rw [cf₁, cf₂, hp.2.2 .r15 (by decide)]
  · rw [k₁.regs .r15 (by decide)]; exact cf₁

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.FinishCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.HPrime.ChainCT`. -/
section
/-! # H′: constant time of the long-output loop -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem chainBody_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (Related LoopReady)
      (.seq (.block [.mov32 .rsi (.imm 64)])
        (.seq (next (hash v)) (.seq emitPrefix (.block [.alu .cmp .r15 (.imm 65)]))))
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ s₁.cf = s₂.cf ∧
        s₁.cf = some (decide ((s₁.gpr .r15).toNat < 65))) :=
  (count64_init_rel loop_stable).seq ((next_rel v loop_stable).seq
    (emit_rel.seq (compare_rel output_stable)))

theorem chainStep_ready (v : Proof.Blake2.X86_64.Backend) (s : State) (h : LoopReady s) :
    WP isa (.seq (.block [.mov32 .rsi (.imm 64)])
      (.seq (next (hash v)) (.seq emitPrefix (.block [.alu .cmp .r15 (.imm 65)])))) s (ChainStep s) := by
  have space := h.1.space.prefix (show 32 ≤ (s.gpr .r15).toNat by have := h.2; omega_using [this])
  exact chainStep_ok v s space.work space.out space.sep space.stackWork

theorem chain_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (Related LoopReady) (chain (hash v))
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64) := by
  let I := fun n s₁ s₂ => Related LoopReady s₁ s₂ ∧ (s₁.gpr .r15).toNat = n
  have step (n : Nat) := ((chainBody_rel v).mono (P' := I n)
    (fun _ _ h => h.1) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨chainStep_ready v s₁ hp.1.1, chainStep_ready v s₂ hp.1.2.1⟩)
  have loops (n : Nat) : RelCT isa (I n) (chain (hash v))
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64) := by
    unfold chain
    apply RelCT.loop (M := isa) I ?_ n
    intro m
    apply (step m).mono (fun _ _ h => h)
    rintro t₁ t₂ ⟨⟨ready, cf, value⟩, s₁, s₂, hp, h₁, _⟩
    refine ⟨by simp only [eval, cf], ?_, ?_⟩
    · intro flag
      refine ⟨ready, ?_⟩
      by_contra h
      have hn : ¬ (t₁.gpr .r15).toNat < 65 := by omega_using [h]
      simp only [eval, value, hn, decide_false, Option.map_some, Bool.not_false] at flag
      contradiction
    intro flag
    have lo : 65 ≤ (t₁.gpr .r15).toNat := by
      by_contra h
      have lt : (t₁.gpr .r15).toNat < 65 := by omega_using [h]
      simp only [eval, value, lt, decide_true, Option.map_some, Bool.not_true] at flag
      contradiction
    have remain : (t₁.gpr .r15).toNat = (s₁.gpr .r15).toNat - 32 := by
      rw [h₁.remaining, sub32_nat _ (by have := hp.1.1.2; omega_using [this])]
    refine ⟨(t₁.gpr .r15).toNat, ?_, ⟨⟨ready.1, lo⟩, ⟨ready.2.1, ?_⟩, ready.2.2⟩, rfl⟩
    · have before : 65 ≤ (s₁.gpr .r15).toNat := hp.1.1.2
      have count : (s₁.gpr .r15).toNat = m := hp.2
      omega_using [lo, remain, count]
    · rw [← ready.2.2 .r15 (by decide)]; exact lo
  exact (RelCT.exists_ loops).mono (fun s₁ _ h => ⟨(s₁.gpr .r15).toNat, h, rfl⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: constant time of the final hash and output -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov)

def Compared (s t : State) : Prop := Related OutputReady s t ∧ s.cf = t.cf ∧
  s.cf = some (decide ((s.gpr .r15).toNat < 65))

theorem Compared.short {s t : State} (h : Compared s t) (flag : isa.eval .b s = some true) :
    (s.gpr .r15).toNat ≤ 64 := by
  by_contra hn
  have n : ¬ (s.gpr .r15).toNat < 65 := by omega_using [hn]
  simp only [eval, h.2.2, n, decide_false] at flag
  contradiction

theorem Compared.long {s t : State} (h : Compared s t) (flag : isa.eval .b s = some false) :
    Related LoopReady s t := by
  have n : 65 ≤ (s.gpr .r15).toNat := by
    by_contra hn
    have n : (s.gpr .r15).toNat < 65 := by omega_using [hn]
    simp only [eval, h.2.2, n, decide_true] at flag
    contradiction
  exact ⟨⟨h.1.1, n⟩, ⟨h.1.2.1, by rw [← h.1.2.2 .r15 (by decide)]; exact n⟩, h.1.2.2⟩

theorem maybeChain_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa Compared (.ite .b (.block []) (chain (hash v)))
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64) :=
  RelCT.ite (fun _ _ h => by simp only [eval, h.2.1])
    (RelCT.block_nil fun _ _ ⟨h, flag⟩ => ⟨h.1, h.short flag⟩)
    ((chain_rel v).mono (fun _ _ ⟨h, flag⟩ => h.long flag) (fun _ _ h => h))

theorem lastCount_ok (s : State) : WP isa (.block [.mov .rsi (.reg .r15)]) s fun t =>
    Keeps s t ∧ t.gpr .rsi = s.gpr .r15 := by
  refine wp_mov fun t ht _ _ => WP.block_nil ⟨?_, ht.gpr⟩
  refine ⟨fun r hr => ?_, ht.rd, ht.wr, ?_⟩
  · have hn : r ≠ .rsi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ht.other r hn
  · rw [ht.mem]; exact Frame.refl _ _

theorem lastCount_rel :
    RelCT isa (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64)
      (.block [.mov .rsi (.reg .r15)])
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧
        (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  let P := fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64
  have ct := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block [.mov .rsi (.reg .r15)])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨lastCount_ok s₁, lastCount_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, ⟨hp, bound⟩, ⟨k₁, n₁⟩, ⟨k₂, n₂⟩⟩
  exact ⟨hp.keeps output_stable k₁ k₂, by rw [n₁]; exact ⟨hp.1.positive, bound⟩,
    by rw [n₁, n₂]; exact hp.2.2 _ (by decide)⟩

theorem extendDigest_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (Related LoopReady) (extendDigest (hash v)) (Related OutputReady) :=
  emit_rel.seq ((compare_rel output_stable).seq
    ((maybeChain_rel v).seq (lastCount_rel.seq (next_rel v output_stable))))

theorem finishOutput_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (Related OutputReady) (finishOutput (hash v)) (AgreeRegs publicRegs) := by
  have branches : RelCT isa Compared (.ite .b (.block []) (extendDigest (hash v))) (Related OutputReady) :=
    RelCT.ite (fun _ _ h => by simp only [eval, h.2.1])
      (RelCT.block_nil fun _ _ h => h.1.1)
      ((extendDigest_rel v).mono (fun _ _ ⟨h, flag⟩ => h.long flag) (fun _ _ h => h))
  exact (compare_rel output_stable).seq (branches.seq
    (copyRemaining_rel.mono (fun _ _ h => h.2.2) (fun _ _ h => h)))

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.CT`. -/
section
/-! # H′: constant time of the complete x86-64 program -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem setup_work (s : State) (h : localContract.pre s) :
    (⟨s.gpr .r8, 16384⟩ : Region) ∈ s.wr := by
  rw [h.2.1]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem setup_ready {s t : State} (h : localContract.pre s) (ht : Setup s t) : FirstReady t := by
  obtain ⟨rd, wr, len, lo, hi, dw, ow, sd, so, sw, _, _⟩ := h
  have sp : t.gpr .rsp = s.gpr .rsp := ht.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have space : Space t (s.gpr .rcx).toNat := by
    refine ⟨by omega_using [], ?_, ?_, ?_, ?_, ?_⟩
    · rw [ht.workspace, ht.wr, wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · intro i hi'
      rw [ht.wr, ht.output, wr]
      exact ⟨outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega_using [hi']) (by omega_using [hi'])⟩
    · rw [ht.workspace, ht.output]; exact ow.symm
    · rw [sp, ht.workspace]; exact sw
    · rw [sp, ht.output]; exact so
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [ht.remaining]; exact space
  · rw [ht.remaining]; exact lo
  · rw [ht.remaining]; exact hi
  · rw [ht.length]; exact len
  · rw [ht.input, ht.length, ht.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · rw [ht.input, ht.length, ht.workspace]; exact dw
  · rw [sp, ht.input, ht.length]; exact sd

theorem code_ct (v : Proof.Blake2.X86_64.Backend) :
    ConstantTime isa localContract.pre localContract.pub (code (hash v)) := by
  let P := fun s₁ s₂ => localContract.pre s₁ ∧ localContract.pre s₂ ∧ localContract.pub s₁ s₂
  have setupCT := (setup_rel.mono (P' := P) (fun s₁ s₂ hp => by
      obtain ⟨di, si, dx, cx, r8, sp⟩ := hp.2.2
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨setup_ok s₁ (setup_work s₁ hp.1), setup_ok s₂ (setup_work s₂ hp.2.1)⟩)
  have start : RelCT isa P (.block setup) (Related FirstReady) :=
    setupCT.mono (fun _ _ h => h) fun _ _ ⟨pub, _, _, hp, h₁, h₂⟩ =>
      ⟨setup_ready hp.1 h₁, setup_ready hp.2.1 h₂, pub⟩
  have firstCT := (first_rel v).mono (fun _ _ h => h)
    (fun _ _ h => (show Related OutputReady _ _ from ⟨h.1.toOutputReady, h.2.1.toOutputReady, h.2.2⟩))
  have restoreCT := restore_rel.mono (P' := AgreeRegs publicRegs) (fun _ _ hp => by
      intro r hr
      simp only [List.mem_singleton] at hr; subst r
      exact hp _ (by decide)) (fun _ _ h => h)
  exact (start.seq (firstCT.seq ((finishOutput_rel v).seq restoreCT))).constantTime

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # Verified H′ for any x86-64 BLAKE2b backend -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem spSafe (v : Proof.Blake2.X86_64.Backend) : (code (hash v)).all (fun i => !isa.writesSp i) = true := by
  have init : (hash v).init.all (fun i => !isa.writesSp i) = true := by
    apply Code.all_of_allInstrs
    change (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).allInstrs _ = true
    lit_decide
  have update : (hash v).update.all (fun i => !isa.writesSp i) = true := v.updateSpSafe
  have finalize : (hash v).finalize.all (fun i => !isa.writesSp i) = true := v.finalizeSpSafe
  simp only [code, setup, saved, first, chooseLength, Impl.Argon2.X86_64.HPrime.init,
    initArgs, absorbFixed, fixedArgs, Impl.Argon2.X86_64.HPrime.update, updateArgs,
    absorbInput, inputArgs, finishInput, Impl.Argon2.X86_64.HPrime.finalize, finalizeArgs,
    finishOutput, extendDigest, emitPrefix, copy, copyByte, chain, next, copyRemaining,
    restore, Code.all]
  rw [init, update, finalize]
  decide +kernel

end VG.Proof.Argon2.X86_64.HPrime
