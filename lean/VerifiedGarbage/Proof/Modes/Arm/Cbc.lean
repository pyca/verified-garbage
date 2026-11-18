module

public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Modes.Arm.SeqBody
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Modes.Arm.SeqBody
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Modes.Arm.SeqCT`, which this module and modules that import it used -/

section

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

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Proof.MdStream.Arm (eval_eq eval_ne)

/-- The registers the loop keeps public: those of the arguments, and of the
number of rounds if the core takes one. -/
def loopRegs (c : Core) : List Reg :=
  if c.rounds then [.r4, .r5, .r6, .r7, .r8, .r11] else [.r4, .r5, .r6, .r7, .r8]

/-- The taint checks of the code between the calls of `c.seq M`. -/
structure SeqTaint (c : Core) (M : Mode) : Prop where
  pro : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] (argBytes c)) (.block (c.save ++ c.setup)) h).isSome =
    true
  pre : ∃ h, (taint.check (Taint.ofRegs (loopRegs c))
    (.block (c.opsCode M.pre ++ c.callArgs M.tgt)) h).isSome = true
  post : ∃ h, (taint.check (Taint.ofRegs [.r6, .r7, .r8]) (.block (c.opsCode M.post ++ c.advance M)) h).isSome =
    true
  epi : ∃ h, (taint.check (Taint.ofRegs [.r5, .r8]) (.block (c.finish M ++ restore)) h).isSome = true

theorem nil_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true := ⟨_, by taint_decide⟩

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ s₀' : State} (hq : (seqArm c S M).pub s₀ s₀')
include hq

theorem pub_sp : s₀.sp = s₀'.sp := hq.1
theorem pub_K : Kp s₀ = Kp s₀' := hq.2.1
theorem pub_R : Rp s₀ = Rp s₀' := hq.2.2.1
theorem pub_Iv : Ivp c s₀ = Ivp c s₀' := by
  cases hr : c.rounds <;> simp only [Ivp, ivArg, hr, Bool.false_eq_true, ↓reduceIte]
  exacts [hq.2.2.1, hq.2.2.2.1]
theorem pub_Dp : Dp c s₀ = Dp c s₀' := by
  cases hr : c.rounds <;> simp only [Dp, dArg, hr, Bool.false_eq_true, ↓reduceIte]
  exacts [hq.2.2.2.1, hq.2.2.2.2.1]
theorem pub_N : N c s₀ = N c s₀' := by
  cases hr : c.rounds <;> simp only [N, nArg, hr, Bool.false_eq_true, ↓reduceIte]
  exacts [by rw [hq.2.2.2.2.1], by rw [hq.2.2.2.2.2.1]]
theorem pub_Sc : Sc c s₀ = Sc c s₀' := by
  cases hr : c.rounds <;> simp only [Sc, scArg, hr, Bool.false_eq_true, ↓reduceIte]
  exacts [hq.2.2.2.2.2.1, hq.2.2.2.2.2.2.1 hr]
theorem pub_syms : ∀ x ∈ S.consts, s₀.syms x.1 = s₀'.syms x.1 := hq.2.2.2.2.2.2.2
theorem pub_Dk (k : Nat) : Dk s₀ c M k = Dk s₀' c M k := by simp only [Dk]; rw [pub_Dp hq]

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv c S M s₀ k s₁) (h₂ : LInv c S M s₀' k s₂) :
    ∀ r ∈ loopRegs c, s₁.gpr r = s₂.gpr r := by
  have h5 : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8], s₁.gpr r = s₂.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.r4, h₂.r4, pub_K hq]
    · rw [h₁.r5, h₂.r5, pub_Iv hq]
    · rw [h₁.r6, h₂.r6, pub_Dp hq]
    · rw [h₁.r7, h₂.r7, pub_N hq]
    · rw [h₁.r8, h₂.r8, pub_Sc hq]
  unfold loopRegs
  cases hr : c.rounds
  · exact h5
  · intro r hr'
    simp only [↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with h | h | h | h | h | rfl
    all_goals try (subst h; exact h5 _ (by simp))
    rw [h₁.r11 hr, h₂.r11 hr, pub_R hq]

end

/-- The relation before a block, in two runs. -/
def BRel (c : Core) (S : CoreSpec c) (M : Mode) (s₀ s₀' : State) (k : Nat) (s₁ s₂ : State) : Prop :=
  (k < N c s₀ ∧ LInv c S M s₀ k s₁ ∧ s₁.syms = s₀.syms) ∧ (k < N c s₀' ∧ LInv c S M s₀' k s₂ ∧ s₂.syms = s₀'.syms)

/-- What is known after the code before the call. -/
def AfterPre (c : Core) (S : CoreSpec c) (M : Mode) (s₀ : State) (k : Nat) (s₂ : State) : Prop :=
  ∃ (hk : k < N c s₀) (s : State), LInv c S M s₀ k s ∧
    PreA (c := c) (M := M) s₀ k (runOps M.pre ((rK S s₀ M k).2.set .d
      ((xs c s₀ M)[k]'(by rw [length_blocksOf]; exact hk)))) s s₂ ∧ s₂.syms = s₀.syms

/-- The registers the code after the call uses, after it. -/
structure AfterCall (c : Core) (M : Mode) (s₀ : State) (k : Nat) (s₃ : State) : Prop where
  r6 : s₃.gpr .r6 = Dk s₀ c M k
  r7 : s₃.gpr .r7 = BitVec.ofNat 32 (N c s₀ - k)
  r8 : s₃.gpr .r8 = Sc c s₀

theorem afterCall {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} {k : Nat} {s₂ s₃ : State}
    (h : AfterPre c S M s₀ k s₂)
    (cp : CallPost c S s₂ (Kp s₀) (Rp s₀) (bt c (Dk s₀ c M k) (Sc c s₀) M.tgt) (Cs c s₀) s₃) :
    AfterCall c M s₀ k s₃ := by
  obtain ⟨_, s, hl, a, -⟩ := h
  have g : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r9 → r ≠ .r10 → s₃.gpr r = s.gpr r := fun r hr hl h9 h10 => by
    rw [cp.saved r hr hl, a.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr) h9 h10
      (by rintro rfl; simp [preserved] at hr)]
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
theorem body_ct (hM : ModeOk c M) (hT : SeqTaint c M) (k : Nat) :
    RelCT isa (BRel c S M s₀ s₀' k) (c.body M) fun _ _ => True := by
  have a := rel_agree (F := fun s => k < N c s₀ ∧ LInv c S M s₀ k s ∧ s.syms = s₀.syms)
    (F' := fun s => k < N c s₀' ∧ LInv c S M s₀' k s ∧ s.syms = s₀'.syms)
    (G := AfterPre c S M s₀ k) (G' := AfterPre c S M s₀' k) (Taint.ofRegs (loopRegs c))
    (fun _ _ h h' => Taint.agree_ofRegs (LInv.agree hq h.2.1 h'.2.1)) hT.pre
    (fun _ h => VG.Arm.WP.mono_syms (pre_wp hp hM h.1 h.2.1) fun _ x sy => ⟨h.1, _, h.2.1, x, sy.trans h.2.2⟩)
    (fun _ h => VG.Arm.WP.mono_syms (pre_wp hp' hM h.1 h.2.1) fun _ x sy => ⟨h.1, _, h.2.1, x, sy.trans h.2.2⟩)
  -- The call, with the same regions in both runs.
  let rd : List Region := [⟨State.addr (Kp s₀), S.keyLen⟩]
  let wr : List Region := [⟨State.addr (bt c (Dk s₀ c M k) (Sc c s₀) M.tgt), c.bs⟩]
  have cpre : ∀ {t₀ : State} (hpt : UPre c S M t₀) {s₂ : State} (h : AfterPre c S M t₀ k s₂),
      CallPre c S s₂ (Kp t₀) (Rp t₀) (bt c (Dk t₀ c M k) (Sc c t₀) M.tgt) (Cs c t₀) := fun {_} hpt {_} h => by
    obtain ⟨hk, s, hl, pa, sy⟩ := h
    exact PreA.callPre hpt hM hk hl pa sy
  have spA : ∀ {s₂ s₂' : State}, AfterPre c S M s₀ k s₂ → AfterPre c S M s₀' k s₂' → s₂.sp = s₂'.sp :=
    fun ⟨_, _, hl, x, _⟩ ⟨_, _, hl', x', _⟩ => by rw [x.sp, hl.sp, x'.sp, hl'.sp, pub_sp hq]
  have syA : ∀ {s₂ s₂' : State}, AfterPre c S M s₀ k s₂ → AfterPre c S M s₀' k s₂' →
      ∀ x ∈ S.consts, s₂.syms x.1 = s₂'.syms x.1 :=
    fun ⟨_, _, _, _, sy⟩ ⟨_, _, _, _, sy'⟩ x hx => by rw [sy, sy', pub_syms hq x hx]
  -- The arguments in registers, through the callee's view of a state.
  have regsA : ∀ {s₂ s₂' : State} (h : AfterPre c S M s₀ k s₂) (h' : AfterPre c S M s₀' k s₂'),
      s₂.gpr .r0 = s₂'.gpr .r0 ∧ s₂.gpr .r1 = s₂'.gpr .r1 ∧ s₂.gpr .r2 = s₂'.gpr .r2 ∧
        (c.r3Pub = true → s₂.gpr .r3 = s₂'.gpr .r3) := fun h h' => by
    have p := cpre hp h
    have p' := cpre hp' h'
    rw [← pub_K hq, ← pub_R hq, ← pub_Dk hq, ← pub_Sc hq] at p'
    have rD := p.rd.trans p'.rd.symm
    have rN := p.rn.trans p'.rn.symm
    refine ⟨by rw [p.r0, p'.r0], ?_, ?_, fun hr => ?_⟩
    · cases hr : c.rounds
      · have hD : c.dReg = .r1 := by unfold Core.dReg; rw [hr]; rfl
        rwa [hD] at rD
      · rw [p.r1 hr, p'.r1 hr]
    · cases hr : c.rounds
      · have hN : c.nReg = .r2 := by unfold Core.nReg; rw [hr]; rfl
        rwa [hN] at rN
      · have hD : c.dReg = .r2 := by unfold Core.dReg; rw [hr]; rfl
        rwa [hD] at rD
    · cases hr' : c.rounds
      · have hs : c.arg3.isSome = true := by simpa [Core.r3Pub, hr'] using hr
        obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
        rw [p.a3 k hk, p'.a3 k hk]
      · have hN : c.nReg = .r3 := by unfold Core.nReg; rw [hr']; rfl
        rwa [hN] at rN
  have callR : RelCT isa (fun s₂ s₂' => AfterPre c S M s₀ k s₂ ∧ AfterPre c S M s₀' k s₂') c.callStep
      fun _ _ => True := by
    unfold Core.callStep
    split
    rotate_left
    · rename_i hs
      refine RelCT.frame (fun s₂ s₂' h => spA h.1 h.2) ?_
      intro a b t₁ t₂ a' b' ⟨s₂, s₂', ⟨h, h'⟩, pa, pb⟩ e₁ e₂
      have p := cpre hp h
      have p' := cpre hp' h'
      have eC : Cs c s₀' = Cs c s₀ := by simp only [Cs]; rw [pub_Sc hq]
      rw [← pub_K hq, ← pub_R hq, ← pub_Dk hq, eC, ← pub_Sc hq] at p'
      have hsp := spA h h'
      rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using p.sp8 hs), Option.some.injEq] at pa
      rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using p'.sp8 hs), Option.some.injEq] at pb
      subst pa pb
      have eA : Push.argR s₂' = Push.argR s₂ := by rw [Push.argR, Push.argR, hsp]
      have syms := syA h h'
      have eT : tabRegs S.consts s₂' = tabRegs S.consts s₂ := by
        simp only [tabRegs, Abi.constRegions]
        exact List.map_congr_left fun x hx => by rw [syms x hx]
      let wr' : List Region := [⟨State.addr (bt c (Dk s₀ c M k) (Sc c s₀) M.tgt), c.bs⟩,
        ⟨State.addr (Cs c s₀), c.stackScratch⟩]
      have cw : Covers ([⟨State.addr (bt c (Dk s₀ c M k) (Sc c s₀) M.tgt), c.bs⟩] ++
          [⟨State.addr (Cs c s₀), c.stackScratch⟩]) s₂.wr := Covers.append_left p.wB (p.wC hs)
      have cw' : Covers ([⟨State.addr (bt c (Dk s₀ c M k) (Sc c s₀) M.tgt), c.bs⟩] ++
          [⟨State.addr (Cs c s₀), c.stackScratch⟩]) s₂'.wr := Covers.append_left p'.wB (p'.wC hs)
      refine RelCT.call S.correct S.ct ([⟨State.addr (Kp s₀), S.keyLen⟩, Push.argR s₂] ++ tabRegs S.consts s₂) wr'
        (P := fun x y => x = pushed [.r12, .lr] s₂ ∧ y = pushed [.r12, .lr] s₂')
        (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
      subst ex ey
      have v := p.ecbPreS hs
      have v' := p'.ecbPreS hs
      have c' := p'.cov hs
      rw [eA, eT] at v' c'
      obtain ⟨r0, r1, r2, r3⟩ := regsA h h'
      have e0 : ∀ (t : State) (r : Reg), r ≠ .r12 → r ≠ .lr → ∀ rd wr, (Push.view t rd wr).gpr r = t.gpr r :=
        fun t r a b rd wr => Push.view_gpr _ _ _ _ (by simp [linkRegs, a, b])
      refine ⟨S.pre_ofS hs _ v, S.pre_ofS hs _ v', S.pub_ofS hs _ _ ?_ ?_ ?_ ?_ (fun hr => ?_) ?_ syms,
        p.cov hs, Push.covW cw, c', Push.covW cw'⟩
      · simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, hsp]
      · rw [e0 _ _ (by decide) (by decide), e0 _ _ (by decide) (by decide), r0]
      · rw [e0 _ _ (by decide) (by decide), e0 _ _ (by decide) (by decide), r1]
      · rw [e0 _ _ (by decide) (by decide), e0 _ _ (by decide) (by decide), r2]
      · rw [e0 _ _ (by decide) (by decide), e0 _ _ (by decide) (by decide), r3 hr]
      · rw [Push.arg0 (p.sp8 hs), Push.arg0 (p'.sp8 hs), p.r12 hs, p'.r12 hs]
    rename_i h0
    refine RelCT.call S.correct S.ct rd wr fun s₂ s₂' ⟨h, h'⟩ => ?_
    have p := cpre hp h
    have p' := cpre hp' h'
    rw [← pub_K hq, ← pub_R hq, ← pub_Dk hq, ← pub_Sc hq] at p'
    obtain ⟨r0, r1, r2, r3⟩ := regsA h h'
    refine ⟨S.pre_of h0 _ p.ecbPre, S.pre_of h0 _ p'.ecbPre, S.pub_of h0 _ _ ?_ ?_ ?_ ?_ fun hr => ?_,
      Covers.append_left p.rK (Covers.right p.wB), p.wB, Covers.append_left p'.rK (Covers.right p'.wB), p'.wB⟩
    · simp only [State.withRegions_sp, State.callEntry_sp]; exact spA h h'
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r0]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r1]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r2]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r3 hr]
  have cr := rel_wp (G := AfterCall c M s₀ k) (G' := AfterCall c M s₀' k) callR
    (fun _ h => WP.mono (call_wp S (cpre hp h)) fun _ cp => afterCall h cp)
    (fun _ h => WP.mono (call_wp S (cpre hp' h)) fun _ cp => afterCall h cp)
  obtain ⟨_, hB⟩ := hT.post
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => AfterCall c M s₀ k s₁ ∧ AfterCall c M s₀' k s₂)
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
  ∃ k, n = N c s₀ - k ∧ BRel c S M s₀ s₀' k s₁ s₂

theorem loop_ct (hM : ModeOk c M) (hT : SeqTaint c M) (n : Nat) :
    RelCT isa (LRel (c := c) (S := S) (M := M) (s₀ := s₀) (s₀' := s₀') n) (.loop (c.body M) .ne)
      fun s₁ s₂ => LInv c S M s₀ (N c s₀) s₁ ∧ LInv c S M s₀' (N c s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel (c := c) (S := S) (M := M) (s₀ := s₀) (s₀' := s₀')) (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N c s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (body_ct hp hp' hq hM hT k).wp
    (F₁ := fun (s : State) => ((LInv c S M s₀ (k + 1) s ∧ s.z = decide (N c s₀ - (k + 1) = 0)) ∧ k < N c s₀) ∧
      s.syms = s₀.syms)
    (F₂ := fun (s : State) => (LInv c S M s₀' (k + 1) s ∧ s.z = decide (N c s₀' - (k + 1) = 0)) ∧
      s.syms = s₀'.syms)
    fun _ _ h => ⟨VG.Arm.WP.mono_syms (body_ok hp hM h.1.1 h.1.2.1 h.1.2.2) fun _ r sy => ⟨⟨r, h.1.1⟩,
        sy.trans h.1.2.2⟩,
      VG.Arm.WP.mono_syms (body_ok hp' hM h.2.1 h.2.2.1 h.2.2.2) fun _ r sy => ⟨r, sy.trans h.2.2.2⟩⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨⟨l₁, z₁⟩, hk⟩, y₁⟩, ⟨⟨l₂, z₂⟩, y₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (N c s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s₁ = _; rw [eval_ne, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide (N c s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N c s₀ = k + 1 := by
      have : N c s₀ - (k + 1) = 0 := by simpa using hf
      omega_using [hk, this]
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N c s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N c s₀ - (k + 1), by omega_using [hk], k + 1, rfl, ⟨by omega_using [h0], l₁, y₁⟩, ⟨by rw [← hN]; omega_using [h0], l₂, y₂⟩⟩

end

theorem seq_rel {c : Core} (S : CoreSpec c) {M : Mode} (hM : ModeOk c M) (hT : SeqTaint c M)
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
      s.sp.toNat + argBytes c ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, argBytes c⟩ r :=
    fun {s} h => by
      have e : (⟨State.addr s.sp, argBytes c⟩ : Region) = argR c s := by simp [stackArgAddr]
      exact ⟨h.spF, by rw [e]; exact h.arg_wr⟩
  have hj : argBytes c = 4 * (if c.rounds then 2 else 1) := by unfold argBytes; split <;> rfl
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => (LInv c S M s₀ 0 s ∧ s.z = decide (N c s₀ = 0)) ∧ s.syms = s₀.syms)
    (G' := fun s => (LInv c S M s₀' 0 s ∧ s.z = decide (N c s₀' = 0)) ∧ s.syms = s₀'.syms)
    (argTaint [.r0, .r1, .r2, .r3] (argBytes c))
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) hsp (wfA hp) (wfA hp')
        (hj ▸ argMem_of (j := if c.rounds then 2 else 1) hsp (hj ▸ hp.spF) fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.2.1
        · exact hq.2.2.1
        · exact hq.2.2.2.1
        · exact hq.2.2.2.2.1
      · cases hr : c.rounds <;> simp only [hr, Bool.false_eq_true, ↓reduceIte] at hi
        · rcases (by omega_using [hi] : i = 0) with rfl
          exact hq.2.2.2.2.2.1
        · rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl
          · exact hq.2.2.2.2.2.1
          · exact hq.2.2.2.2.2.2.1 hr) hT.pro
    (fun s e => by rw [e]; exact VG.Arm.WP.mono_syms (prologue_wp hp) fun _ h sy => ⟨h, sy⟩)
    (fun s e => by rw [e]; exact VG.Arm.WP.mono_syms (prologue_wp hp') fun _ h sy => ⟨h, sy⟩)
  have ev {s : State} (h : s.z = decide (N c s₀ = 0)) : isa.eval .eq s = some (decide (N c s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h]
  have ev' {s : State} (h : s.z = decide (N c s₀' = 0)) : isa.eval .eq s = some (decide (N c s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h, hN]
  have nil := RelCT.taint (A := taint)
    (P := fun a b => (((LInv c S M s₀ 0 a ∧ a.z = decide (N c s₀ = 0)) ∧ a.syms = s₀.syms) ∧
      ((LInv c S M s₀' 0 b ∧ b.z = decide (N c s₀' = 0)) ∧ b.syms = s₀'.syms)) ∧ isa.eval .eq a = some true)
    (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => ((LInv c S M s₀ 0 a ∧ a.z = decide (N c s₀ = 0)) ∧ a.syms = s₀.syms) ∧
      ((LInv c S M s₀' 0 b ∧ b.z = decide (N c s₀' = 0)) ∧ b.syms = s₀'.syms))
      (.ite .eq (.block []) (.loop (c.body M) .ne))
      (fun a b => LInv c S M s₀ (N c s₀) a ∧ LInv c S M s₀' (N c s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1.1.2, ev' h.2.1.2]) ?_ ?_
    · refine (nil.wp (F₁ := LInv c S M s₀ (N c s₀)) (F₂ := LInv c S M s₀' (N c s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N c s₀ = 0 := by
        have := h.2; rw [ev h.1.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1.1)⟩
    · refine (loop_ct hp hp' hq hM hT (N c s₀ - 0)).mono
        (fun a b h => ⟨0, rfl, ⟨?_, h.1.1.1.1, h.1.1.2⟩, ⟨?_, h.1.2.1.1, h.1.2.2⟩⟩) fun _ _ h => h
      all_goals
        have := h.2; rw [ev h.1.1.1.2] at this
        have : N c s₀ ≠ 0 := by simpa using this
        omega
  have epi := RelCT.taint (A := taint)
    (P := fun a b => LInv c S M s₀ (N c s₀) a ∧ LInv c S M s₀' (N c s₀') b)
    (Taint.ofRegs [.r5, .r8]) (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r5, h.2.r5, pub_Iv hq]
      · rw [h.1.r8, h.2.r8, pub_Sc hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h).seq (mid.seq epi)

theorem seq_ct {c : Core} (S : CoreSpec c) {M : Mode} (hM : ModeOk c M) (hT : SeqTaint c M) :
    ConstantTime isa (seqArm c S M).pre (seqArm c S M).pub (c.seq M) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seq_rel S hM hT h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Modes.Arm

end

end

/-! ### `Modes.Arm.SeqLoop`, which this module and modules that import it used -/

section

/-!
# The modes one block at a time on ARMv7: the loop and the whole function

`seq_wp`: `Core.seq c M` meets `seqArm c S M`, for any core and any mode
whose operations are on two different blocks (`ModeOk`): the prologue gives
the invariant for no blocks, each run of the body (`body_ok`) one more, and
the epilogue returns the chaining block if the mode does (`finish`) and
restores our caller's registers from the scratch buffer, whose slots
nothing after the prologue writes.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf over)
open VG.Proof.MdStream.Arm (wp_ldr eval_eq eval_ne)

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

theorem loop_ok (hM : ModeOk c M) {k : Nat} (hk : k < N c s₀) {s : State} (h : LInv c S M s₀ k s)
    (hsy : s.syms = s₀.syms) :
    WP isa (.loop (c.body M) .ne) s (LInv c S M s₀ (N c s₀)) := by
  refine WP.loop (M := isa) (body := c.body M) (c := .ne) (Q := LInv c S M s₀ (N c s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N c s₀ - j ∧ j < N c s₀ ∧ LInv c S M s₀ j t ∧ t.syms = s₀.syms) ?_
    (N c s₀ - k) s ⟨k, rfl, hk, h, hsy⟩
  rintro n s ⟨k, rfl, hk, h, hsy⟩
  refine VG.Arm.WP.mono_syms (body_ok hp hM hk h hsy) fun s' ⟨h', hz⟩ hsy' => ?_
  have ev : isa.eval .ne s' = some !decide (N c s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s' = _; rw [eval_ne, hz]
  by_cases hz' : N c s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [show N c s₀ = k + 1 by omega_using [hk, hz']]
  · right
    refine ⟨by rw [ev]; simp [hz'], N c s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hz'], h', hsy'.trans hsy⟩

theorem mid_wp (hM : ModeOk c M) {s₁ : State} (h : LInv c S M s₀ 0 s₁) (hz : s₁.z = decide (N c s₀ = 0))
    (hsy : s₁.syms = s₀.syms) :
    WP isa (.ite .eq (.block []) (.loop (c.body M) .ne)) s₁ (LInv c S M s₀ (N c s₀)) := by
  have ev : isa.eval .eq s₁ = some (decide (N c s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]
  by_cases hn : N c s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp hM (by omega_using [hn]) h hsy

/-! ## The epilogue -/

/-- The slots of the saved registers. -/
abbrev slotsR (c : Core) (s₀ : State) : Region := ⟨State.addr (Sc c s₀) + BitVec.ofNat 64 0, 36⟩

theorem UPre.slots_disj : ∀ r ∈ [dataR c s₀ M, blkR c s₀, belowR S s₀, ivR c s₀], (slotsR c s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.data_scr.symm.sub_left UPre.slots_sub
  · exact hp.slots_disj_blk
  · exact hp.b_scr.symm.sub_left UPre.slots_sub
  · exact hp.iv_scr.symm.sub_left UPre.slots_sub

/-- What the epilogue starts from: the invariant after all the blocks, with
the chaining block perhaps copied to the IV. -/
structure EInv (s₀ : State) (s : State) : Prop where
  r8 : s.gpr .r8 = Sc c s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR c s₀ M, blkR c s₀, belowR S s₀, ivR c s₀] (savedMem c s₀) s.mem
  data : blocksOf (c.ds M) s.mem (State.addr (Dp c s₀)) (N c s₀) = (rK S s₀ M (N c s₀)).1
  iv : M.finish = true → bytesAt s.mem (State.addr (Ivp c s₀)) c.bs = (rK S s₀ M (N c s₀)).2.o

omit hp in
theorem take_N : (xs c s₀ M).take (N c s₀) = xs c s₀ M := List.take_of_length_le (by rw [length_blocksOf])

theorem finish_wp {s : State} (h : LInv c S M s₀ (N c s₀) s) :
    WP isa (.block (c.finish M)) s (EInv (c := c) (S := S) (M := M) s₀) := by
  have hnil : (xs c s₀ M).drop (N c s₀) = [] := List.drop_of_length_le (by rw [length_blocksOf])
  have hfit : c.bs ≤ 2 ^ 64 := by have := hp.fS; unfold Core.scratchBytes Core.csOff at this; omega_using [this]
  have fr4 : Frame [dataR c s₀ M, blkR c s₀, belowR S s₀, ivR c s₀] (savedMem c s₀) s.mem :=
    h.frame.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h]
  unfold Core.finish
  split
  · rename_i hf
    have hS := hp.fS
    have hI := hp.fIv
    have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
    have hbs : c.bs = 4 * c.bw := rfl
    have hb := S.bw_le
    have ho : oOff = 40 := rfl
    have np : NPre c.bw s .r5 .r8 0 oOff (State.addr (Ivp c s₀) + BitVec.ofNat 64 0) (oA c s₀) := by
      refine ⟨by rw [h.r5], by rw [h.r8], by rw [h.r5]; omega_using [hI, hbs], by rw [h.r8]; omega_using [hS, hsc, hbs], by omega, by omega_using [hbs, hb],
        by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
      · rw [h.wr]; exact cov_off (R := ivR c s₀) (hp.fin hf) (by show 0 + 4 * c.bw ≤ c.bs; omega_using [hbs])
      · rw [h.rd, h.wr]
        exact cov_off (R := scrR c s₀) (List.mem_append_right _ hp.scr_in)
          (by show oOff + 4 * c.bw ≤ c.scratchBytes; omega_using [hsc, hbs])
      · exact (hp.iv_scr.sub_left (VG.Offset.sub_base _ (by omega_using [hbs]))).sub_right
          (VG.Offset.sub_base _ (by omega_using [hsc, hbs]))
    refine WP.mono (copyN_wp np) fun s' hi => ⟨by rw [hi.regs _ (by decide) (by decide), h.r8],
      by rw [hi.sp, h.sp], by rw [hi.rd, h.rd], by rw [hi.wr, h.wr], ?_, ?_, fun _ => ?_⟩
    · rw [hi.mem]
      exact fr4.trans ((VG.Proof.Modes.over_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨ivR c s₀, .tail _ (.tail _ (.tail _ (.head _))), by rw [add0]; exact Region.sub_prefix (by omega_using [hbs])⟩)
    · rw [hi.mem]
      refine Eq.trans (b := blocksOf (c.ds M) s.mem (State.addr (Dp c s₀)) (N c s₀))
        (List.map_congr_left fun j hj => ?_) (by rw [h.data, hnil, List.append_nil])
      have hj := List.mem_range.mp hj
      have hsub : Region.Sub ⟨State.addr (Dp c s₀) + BitVec.ofNat 64 (c.ds M * j), c.ds M⟩ (dataR c s₀ M) :=
        VG.Offset.sub_base _ (by have := idx_lt' (L := c.ds M) hj; omega_using [this])
      exact bytesAt_over_other _ _ (by rw [add0]; exact (hp.iv_data.sub_left (Region.sub_prefix (by omega_using [hbs]))).sub_right hsub)
        (by have := S.ds_le M; omega_using [hfit, this])
    · rw [hi.mem, ← h.o, add0]
      have e := bytesAt_over_self s.mem (State.addr (Ivp c s₀) + BitVec.ofNat 64 0)
        (fun i => s.mem (oA c s₀ + BitVec.ofNat 64 i)) (n := 4 * c.bw) (by omega)
      rw [add0] at e
      rw [hbs, e]; rfl
  · refine WP.block_nil ⟨h.r8, h.sp, h.rd, h.wr, fr4, by rw [h.data, hnil, List.append_nil], fun hf => ?_⟩
    rename_i hnf; exact absurd hf hnf

theorem epilogue_wp {s : State} (h : EInv (c := c) (S := S) (M := M) s₀ s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ (seqArm c S M).post s₀ s' := by
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have ho : oOff = 40 := rfl
  have hsv : Spill.Saved s.mem (State.addr (Sc c s₀)) s₀.gpr saved :=
    (Spill.saveMem_saved (State.addr (Sc c s₀)) s₀.gpr s₀.mem saved saved_slots).frame saved_slots h.frame
      (fun r hr => hp.slots_disj r hr)
  have hin : ∀ d, d + 4 ≤ 36 → InRegions (s.rd ++ s.wr) (State.addr (Sc c s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [h.rd, h.wr]
      exact ⟨scrR c s₀, List.mem_append_right _ hp.scr_in, VG.Offset.contains_base _ (by omega_using [hsc, ho, hd]) (by omega_using [hd])⟩
  rw [show (restore : List Instr) = savedA.map (fun p => Instr.ldr p.1 .r8 p.2) ++ [.ldr .r8 .r8 16] from rfl]
  refine Spill.restore_slots_ok savedA_slots savedA_restorable (g := s₀.gpr) (by rw [h.r8]; omega_using [hS, hsc, ho])
    (fun d _ hd => by rw [h.r8]; exact hin d hd)
    (by rw [h.r8]; exact fun p hp' => hsv p (by rw [saved_eq]; exact List.mem_append_left _ hp'))
    fun s₁ ld ho' m₁ rd₁ wr₁ sp₁ => ?_
  refine wp_ldr (a := State.addr (Sc c s₀) + BitVec.ofNat 64 16) (by decide)
    (by rw [ho' _ (by decide), h.r8]; exact addr_add (by omega_using [hS, hsc, ho]))
    (by rw [rd₁, wr₁]; exact hin 16 (by decide)) fun s₂ u₂ => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · by_cases h8 : r = .r8
    · subst h8; rw [u₂.gpr, m₁]; exact hsv (.r8, 16) (by decide)
    · rw [u₂.other _ h8]
      have : r ∈ savedA.map Prod.fst := by
        revert hr h8; revert r; decide
      exact Spill.restored_reg ld this
  · rw [u₂.sp, sp₁, h.sp]
  · show blocksOf (c.ds M) s₂.mem (State.addr (Dp c s₀)) (N c s₀) = _
    rw [u₂.mem, m₁, h.data]; simp only [rK, take_N]
  · intro hf
    show bytesAt s₂.mem (State.addr (Ivp c s₀)) c.bs = _
    rw [u₂.mem, m₁, h.iv hf]; simp only [rK, take_N]

end

/-- The whole function meets its contract, for any core and mode. -/
theorem seq_wp {c : Core} (S : CoreSpec c) {M : Mode} (hM : ModeOk c M) {s₀ : State}
    (h0 : (seqArm c S M).pre s₀) :
    WP isa (c.seq M) s₀ fun s' => abiPreserved s₀ s' ∧ (seqArm c S M).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (VG.Arm.WP.mono_syms (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ hsy =>
    WP.seq (WP.mono (mid_wp hp hM h₁ hz hsy) fun _ h₂ => by
      rw [WP.block_append_iff]
      exact WP.mono (finish_wp hp h₂) fun _ h₃ => epilogue_wp hp h₃))

end VG.Proof.Modes.Arm

end

end

/-!
# CBC as a mode one block at a time on ARMv7

`Impl.Modes.Arm.cbcEnc` and `cbcDec` run CBC (SP 800-38A §6.2,
`Spec/Cbc.lean`): from the IV in the chaining block, whatever the spare
block holds, `runSeq` gives `Spec.Cbc.encrypt` and `Spec.Cbc.decrypt`.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm

theorem xor_comm (x y : List Byte) : Spec.Cbc.xor x y = Spec.Cbc.xor y x := by
  simp only [Spec.Cbc.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b)

/-! ## The contracts of the ciphers' modes -/

/-- The arguments of a core without rounds: `(schedule = r0, iv = r1,
data = r2, n = r3, scratch = [sp])`. -/
theorem args_plain {c : Core} (hr : c.rounds = false) (s : State) :
    ivArg c s = s.gpr .r1 ∧ dArg c s = s.gpr .r2 ∧ nArg c s = s.gpr .r3 ∧ scArg c s = stackArg s 0 ∧
      argBytes c = 4 := by
  simp [ivArg, dArg, nArg, scArg, argBytes, hr]

theorem seqArm_pub {c : Core} {S : CoreSpec c} {M : Mode} (hr : c.rounds = false) {s₁ s₂ : State}
    (h : s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0)
    (hk : ∀ x ∈ S.consts, s₁.syms x.1 = s₂.syms x.1 := by intro _ h; exact absurd h List.not_mem_nil) :
    (seqArm c S M).pub s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, fun h' => absurd h' (by simp [hr]), hk⟩

/-- The arguments of a core with rounds: `(schedule = r0, rounds = r1,
iv = r2, data = r3, n = [sp], scratch = [sp + 4])`. -/
theorem args_rounds {c : Core} (hr : c.rounds = true) (s : State) :
    ivArg c s = s.gpr .r2 ∧ dArg c s = s.gpr .r3 ∧ nArg c s = stackArg s 0 ∧ scArg c s = stackArg s 1 ∧
      argBytes c = 8 := by
  simp [ivArg, dArg, nArg, scArg, argBytes, hr]

section
variable (c : Core) (S : CoreSpec c) (s : State)

end

theorem stackArg_withRegions (s : State) (rd wr : List Region) (i : Nat) :
    stackArg (s.withRegions rd wr) i = stackArg s i := rfl

theorem stackArgAddr_withRegions (s : State) (rd wr : List Region) (i : Nat) :
    stackArgAddr (s.withRegions rd wr) i = stackArgAddr s i := rfl

theorem seqArm_pubR {c : Core} {S : CoreSpec c} {M : Mode} {s₁ s₂ : State}
    (h : s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1)
    (hk : ∀ x ∈ S.consts, s₁.syms x.1 = s₂.syms x.1 := by intro _ h; exact absurd h List.not_mem_nil) :
    (seqArm c S M).pub s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, fun _ => h.2.2.2.2.2.2, hk⟩

/-- A core and a mode whose code between the calls passes the taint checks
give a function that is correct and constant time under `seqArm`, and so
under any contract `seqArm` implies. -/
theorem seq_verified {c : Core} (S : CoreSpec c) {M : Mode} (hM : ModeOk c M) (hT : SeqTaint c M)
    {k : Contract isa} (hk : (seqArm c S M).Implies k) : Verified Arm.target (c.seq M) k :=
  Verified.of_correct (fun _ hs => seq_wp S hM hs) (seq_ct S hM hT) hk

end VG.Proof.Modes.Arm
