import VerifiedGarbage.Proof.Modes.Arm.SeqLoop
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# The modes one block at a time on ARMv7: constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`), as AES-CBC's are (`Proof/AesCbc/Arm/CT.lean`): the taint
analysis covers the code between the calls, from the public arguments for
the prologue and from the registers the correctness proof pins to them
(`LInv`) afterwards, and each call of the core is constant time by the
core's own proof (`CoreSpec.ct`), its public data (`CoreSpec.pub_of`: the
schedule's and the block's addresses, `n = 1` and the stack pointer) being
the same in both runs.

The code between the calls depends on the core's block size and the mode,
so its taint checks are hypotheses (`SeqTaint`), which each cipher's
instance proves with `taint_decide`.
-/

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Proof.MdStream.Arm (eval_eq eval_ne)

/-- The taint checks of the code between the calls of `c.seq M`. -/
structure SeqTaint (c : Core) (M : Mode) : Prop where
  pro : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 4) (.block (save ++ c.setup)) h).isSome = true
  pre : ∃ h, (taint.check (Taint.ofRegs [.r4, .r5, .r6, .r7, .r8])
    (.block (c.opsCode M.pre ++ c.callArgs M.tgt)) h).isSome = true
  post : ∃ h, (taint.check (Taint.ofRegs [.r6, .r7, .r8]) (.block (c.opsCode M.post ++ c.advance)) h).isSome =
    true
  epi : ∃ h, (taint.check (Taint.ofRegs [.r5, .r8]) (.block (c.finish M ++ restore)) h).isSome = true

theorem nil_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true := ⟨_, by taint_decide⟩

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ s₀' : State} (hq : (seqArm c S M).pub s₀ s₀')
include hq

theorem pub_sp : s₀.sp = s₀'.sp := hq.1
theorem pub_K : Kp s₀ = Kp s₀' := hq.2.1
theorem pub_Iv : Ivp s₀ = Ivp s₀' := hq.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by simp only [N]; rw [hq.2.2.2.2.1]
theorem pub_Sc : Sc s₀ = Sc s₀' := hq.2.2.2.2.2
theorem pub_Dk (k : Nat) : Dk s₀ c k = Dk s₀' c k := by simp only [Dk]; rw [pub_Dp hq]

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv c S M s₀ k s₁) (h₂ : LInv c S M s₀' k s₂) :
    ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r4, h₂.r4, pub_K hq]
  · rw [h₁.r5, h₂.r5, pub_Iv hq]
  · rw [h₁.r6, h₂.r6, pub_Dp hq]
  · rw [h₁.r7, h₂.r7, pub_N hq]
  · rw [h₁.r8, h₂.r8, pub_Sc hq]

end

/-- The relation before a block, in two runs. -/
def BRel (c : Core) (S : CoreSpec c) (M : Mode) (s₀ s₀' : State) (k : Nat) (s₁ s₂ : State) : Prop :=
  (k < N s₀ ∧ LInv c S M s₀ k s₁) ∧ (k < N s₀' ∧ LInv c S M s₀' k s₂)

/-- What is known after the code before the call. -/
def AfterPre (c : Core) (S : CoreSpec c) (M : Mode) (s₀ : State) (k : Nat) (s₂ : State) : Prop :=
  ∃ (hk : k < N s₀) (s : State), LInv c S M s₀ k s ∧
    PreA (c := c) (M := M) s₀ k (runOps M.pre ((rK S s₀ M k).2.set .d
      ((xs c s₀)[k]'(by rw [length_blocksOf]; exact hk)))) s s₂

/-- The registers the code after the call uses, after it. -/
structure AfterCall (c : Core) (s₀ : State) (k : Nat) (s₃ : State) : Prop where
  r6 : s₃.gpr .r6 = Dk s₀ c k
  r7 : s₃.gpr .r7 = BitVec.ofNat 32 (N s₀ - k)
  r8 : s₃.gpr .r8 = Sc s₀

theorem afterCall {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} {k : Nat} {s₂ s₃ : State}
    (h : AfterPre c S M s₀ k s₂) (cp : CallPost c S s₂ (Kp s₀) (bt c (Dk s₀ c k) (Sc s₀) M.tgt) s₃) :
    AfterCall c s₀ k s₃ := by
  obtain ⟨_, s, hl, a⟩ := h
  have g : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r9 → r ≠ .r10 → s₃.gpr r = s.gpr r := fun r hr hl h9 h10 => by
    rw [cp.saved r hr hl, a.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr) h9 h10]
  exact ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide), hl.r6],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hl.r7],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hl.r8]⟩

theorem narrow_gpr (t : State) (rd wr : List Region) {r : Reg} (h1 : r ≠ .r12) (h2 : r ≠ .lr) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr t (by simp [linkRegs, h1, h2])]

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ s₀' : State} (hp : UPre c S M s₀) (hp' : UPre c S M s₀')
  (hq : (seqArm c S M).pub s₀ s₀')
include hp hp' hq

/-- One run of the body from `k` blocks is constant time. -/
theorem body_ct (hM : ModeOk M) (hT : SeqTaint c M) (k : Nat) :
    RelCT isa (BRel c S M s₀ s₀' k) (c.body M) fun _ _ => True := by
  have a := rel_agree (F := fun s => k < N s₀ ∧ LInv c S M s₀ k s)
    (F' := fun s => k < N s₀' ∧ LInv c S M s₀' k s)
    (G := AfterPre c S M s₀ k) (G' := AfterPre c S M s₀' k) (Taint.ofRegs [.r4, .r5, .r6, .r7, .r8])
    (fun _ _ h h' => Taint.agree_ofRegs (LInv.agree hq h.2 h'.2)) hT.pre
    (fun _ h => WP.mono (pre_wp hp hM h.1 h.2) fun _ x => ⟨h.1, _, h.2, x⟩)
    (fun _ h => WP.mono (pre_wp hp' hM h.1 h.2) fun _ x => ⟨h.1, _, h.2, x⟩)
  -- The call, with the same regions in both runs.
  let rd : List Region := [⟨State.addr (Kp s₀), S.keyLen⟩]
  let wr : List Region := [⟨State.addr (bt c (Dk s₀ c k) (Sc s₀) M.tgt), c.bs⟩]
  have cpre : ∀ {t₀ : State} (hpt : UPre c S M t₀) {s₂ : State} (h : AfterPre c S M t₀ k s₂),
      CallPre c S s₂ (Kp t₀) (bt c (Dk t₀ c k) (Sc t₀) M.tgt) := fun {_} hpt {_} h => by
    obtain ⟨hk, s, hl, pa⟩ := h
    exact PreA.callPre hpt hk hl pa
  have callR : RelCT isa (fun s₂ s₂' => AfterPre c S M s₀ k s₂ ∧ AfterPre c S M s₀' k s₂') (.call c.name c.code)
      fun _ _ => True := by
    refine RelCT.call S.correct S.ct rd wr fun s₂ s₂' ⟨h, h'⟩ => ?_
    have p := cpre hp h
    have p' := cpre hp' h'
    rw [← pub_K hq, ← pub_Dk hq, ← pub_Sc hq] at p'
    obtain ⟨_, s, hl, x⟩ := h
    obtain ⟨_, s', hl', x'⟩ := h'
    refine ⟨S.pre_of _ p.ecbPre, S.pre_of _ p'.ecbPre, S.pub_of _ _ ?_ ?_ ?_ ?_,
      Covers.append_left p.rK (Covers.right p.wB), p.wB, Covers.append_left p'.rK (Covers.right p'.wB), p'.wB⟩
    · simp only [State.withRegions_sp, State.callEntry_sp]
      rw [x.sp, hl.sp, x'.sp, hl'.sp, pub_sp hq]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), p.r0, p'.r0]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), p.r1, p'.r1]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), p.r2, p'.r2]
  have cr := rel_wp (G := AfterCall c s₀ k) (G' := AfterCall c s₀' k) callR
    (fun _ h => WP.mono (call_wp S (cpre hp h)) fun _ cp => afterCall h cp)
    (fun _ h => WP.mono (call_wp S (cpre hp' h)) fun _ cp => afterCall h cp)
  obtain ⟨_, hB⟩ := hT.post
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => AfterCall c s₀ k s₁ ∧ AfterCall c s₀' k s₂)
    (Taint.ofRegs [.r6, .r7, .r8])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.r6, h.2.r6, pub_Dk hq]
      · rw [h.1.r7, h.2.r7, pub_N hq]
      · rw [h.1.r8, h.2.r8, pub_Sc hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h).seq ((cr.mono (fun _ _ h => h) fun _ _ h => h).seq
    (b.mono (fun _ _ h => h) fun _ _ h => h))

/-- The loop's relation, with the number of iterations left. -/
def LRel (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ BRel c S M s₀ s₀' k s₁ s₂

theorem loop_ct (hM : ModeOk M) (hT : SeqTaint c M) (n : Nat) :
    RelCT isa (LRel (c := c) (S := S) (M := M) (s₀ := s₀) (s₀' := s₀') n) (.loop (c.body M) .ne)
      fun s₁ s₂ => LInv c S M s₀ (N s₀) s₁ ∧ LInv c S M s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel (c := c) (S := S) (M := M) (s₀ := s₀) (s₀' := s₀')) (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (body_ct hp hp' hq hM hT k).wp
    (F₁ := fun (s : State) => (LInv c S M s₀ (k + 1) s ∧ s.z = decide (N s₀ - (k + 1) = 0)) ∧ k < N s₀)
    (F₂ := fun (s : State) => LInv c S M s₀' (k + 1) s ∧ s.z = decide (N s₀' - (k + 1) = 0))
    fun _ _ h => ⟨WP.mono (body_ok hp hM h.1.1 h.1.2) fun _ r => ⟨r, h.1.1⟩, body_ok hp' hM h.2.1 h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨l₁, z₁⟩, hk⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s₁ = _; rw [eval_ne, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega, k + 1, rfl, ⟨by omega, l₁⟩, ⟨by rw [← hN]; omega, l₂⟩⟩

end

theorem seq_rel {c : Core} (S : CoreSpec c) {M : Mode} (hM : ModeOk M) (hT : SeqTaint c M)
    {s₀ s₀' : State} (h0 : (seqArm c S M).pre s₀) (h0' : (seqArm c S M).pre s₀')
    (hq : (seqArm c S M).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (c.seq M) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  obtain ⟨_, hepi⟩ := hT.epi
  obtain ⟨_, hnil⟩ := nil_taint
  have hN := pub_N hq
  have hsp := pub_sp hq
  have wfA : ∀ {s : State}, UPre c S M s →
      s.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 4⟩ r := fun {s} h => by
    have e : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [stackArgAddr]
    exact ⟨h.spF, by rw [e]; exact h.arg_wr⟩
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => LInv c S M s₀ 0 s ∧ s.z = decide (N s₀ = 0))
    (G' := fun s => LInv c S M s₀' 0 s ∧ s.z = decide (N s₀' = 0))
    (argTaint [.r0, .r1, .r2, .r3] 4)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) hsp (wfA hp) (wfA hp')
        (argMem_of (j := 1) hsp hp.spF fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.2.1
        · exact hq.2.2.1
        · exact hq.2.2.2.1
        · exact hq.2.2.2.2.1
      · rcases (by omega : i = 0) with rfl
        exact hq.2.2.2.2.2) hT.pro
    (fun s e => by rw [e]; exact prologue_wp hp) (fun s e => by rw [e]; exact prologue_wp hp')
  have ev {s : State} (h : s.z = decide (N s₀ = 0)) : isa.eval .eq s = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h]
  have ev' {s : State} (h : s.z = decide (N s₀' = 0)) : isa.eval .eq s = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h, hN]
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((LInv c S M s₀ 0 a ∧ a.z = decide (N s₀ = 0)) ∧
      (LInv c S M s₀' 0 b ∧ b.z = decide (N s₀' = 0))) ∧ isa.eval .eq a = some true)
    (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => (LInv c S M s₀ 0 a ∧ a.z = decide (N s₀ = 0)) ∧
      (LInv c S M s₀' 0 b ∧ b.z = decide (N s₀' = 0)))
      (.ite .eq (.block []) (.loop (c.body M) .ne))
      (fun a b => LInv c S M s₀ (N s₀) a ∧ LInv c S M s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev' h.2.2]) ?_ ?_
    · refine (nil.wp (F₁ := LInv c S M s₀ (N s₀)) (F₂ := LInv c S M s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · refine (loop_ct hp hp' hq hM hT (N s₀ - 0)).mono
        (fun a b h => ⟨0, rfl, ⟨?_, h.1.1.1⟩, ⟨?_, h.1.2.1⟩⟩) fun _ _ h => h
      all_goals
        have := h.2; rw [ev h.1.1.2] at this
        have : N s₀ ≠ 0 := by simpa using this
        omega
  have epi := RelCT.taint (A := taint)
    (P := fun a b => LInv c S M s₀ (N s₀) a ∧ LInv c S M s₀' (N s₀') b)
    (Taint.ofRegs [.r5, .r8]) (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r5, h.2.r5, pub_Iv hq]
      · rw [h.1.r8, h.2.r8, pub_Sc hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h).seq (mid.seq epi)

theorem seq_ct {c : Core} (S : CoreSpec c) {M : Mode} (hM : ModeOk M) (hT : SeqTaint c M) :
    ConstantTime isa (seqArm c S M).pre (seqArm c S M).pub (c.seq M) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seq_rel S hM hT h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Modes.Arm
