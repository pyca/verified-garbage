module

public import VerifiedGarbage.Proof.Modes.Arm.SeqFinal
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Modes.Arm.SeqFinal
meta import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# CFB of a message's last piece on ARMv7: constant time

As `seq`'s (`SeqCT.lean`): two runs from states that agree on the public
arguments are related piece by piece (`RelCT`). The taint analysis covers
the code between the calls (`FinalTaint`: the prologue, which is `seq`'s,
the call's arguments, the code after the call, with its partial segment's
byte loop and the branch to it, and the epilogue), from the registers the
correctness proof pins to the arguments (`FInv`), and each call of the core
is constant time by the core's own proof. Both runs take the same branches:
whether a segment is partial depends on `len` alone.

`seqFinal_verified`: a core and a mode the final function runs whose code
between the calls passes the taint checks give a function that is correct
and constant time under `seqFinalArm`.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Proof.MdStream.Arm (eval_eq eval_ne)

/-- The taint checks of the code between the calls of `c.seqFinal M`. -/
structure FinalTaint (c : Core) (M : Mode) : Prop where
  pro : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] (argBytes c)) (.block (c.save ++ c.setup)) h).isSome =
    true
  pre : ∃ h, (taint.check (Taint.ofRegs (loopRegs c)) (.block (c.callArgs .o)) h).isSome = true
  rest : ∃ h, (taint.check (Taint.ofRegs [.r6, .r7, .r8]) (c.segRest M) h).isSome = true
  epi : ∃ h, (taint.check (Taint.ofRegs [.r5, .r8]) (.block (c.finish M ++ restore)) h).isSome = true

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ s₀' : State} (hq : (seqArm c S byteMode).pub s₀ s₀')
include hq

/-- The registers the invariant pins agree in both runs. -/
theorem FInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : FInv c S M s₀ k s₁) (h₂ : FInv c S M s₀' k s₂) :
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

/-- The relation before a segment, in two runs. -/
def SRel (c : Core) (S : CoreSpec c) (M : Mode) (s₀ s₀' : State) (k : Nat) (s₁ s₂ : State) : Prop :=
  (c.bs * k < N c s₀ ∧ FInv c S M s₀ k s₁ ∧ s₁.syms = s₀.syms) ∧
    (c.bs * k < N c s₀' ∧ FInv c S M s₀' k s₂ ∧ s₂.syms = s₀'.syms)

/-- What is known after the call's arguments. -/
def AfterArgs (c : Core) (S : CoreSpec c) (M : Mode) (s₀ : State) (k : Nat) (s₂ : State) : Prop :=
  ∃ s : State, FInv c S M s₀ k s ∧ ArgsA c (Kp s₀) (Rp s₀) (Sc c s₀) s s₂ ∧ s₂.syms = s₀.syms

/-- The registers the code after the call uses, after it. -/
structure AfterCallF (c : Core) (s₀ : State) (k : Nat) (s₃ : State) : Prop where
  r6 : s₃.gpr .r6 = Dp c s₀ + BitVec.ofNat 32 (c.bs * k)
  r7 : s₃.gpr .r7 = BitVec.ofNat 32 (N c s₀ - c.bs * k)
  r8 : s₃.gpr .r8 = Sc c s₀

theorem AfterArgs.callPre {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S byteMode s₀) {k : Nat}
    {s₂ : State} (h : AfterArgs c S M s₀ k s₂) :
    CallPre c S s₂ (Kp s₀) (Rp s₀) (Sc c s₀ + BitVec.ofNat 32 oOff) (Cs c s₀) := by
  obtain ⟨s, hl, a, sy⟩ := h
  exact hp.callPreO (by rw [a.sp, hl.sp]) (by rw [a.rd, hl.rd]) (by rw [a.wr, hl.wr]) sy
    (by rw [a.mem]; exact hl.frame0) a

theorem afterCallF {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} {k : Nat} {s₂ s₃ : State}
    (h : AfterArgs c S M s₀ k s₂)
    (cp : CallPost c S s₂ (Kp s₀) (Rp s₀) (Sc c s₀ + BitVec.ofNat 32 oOff) (Cs c s₀) s₃) :
    AfterCallF c s₀ k s₃ := by
  obtain ⟨s, hl, a, -⟩ := h
  have g : ∀ r ∈ preserved, r ≠ .lr → s₃.gpr r = s.gpr r := fun r hr hl => by
    rw [cp.saved r hr hl, a.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr)]
  exact ⟨by rw [g _ (by decide) (by decide), hl.r6], by rw [g _ (by decide) (by decide), hl.r7],
    by rw [g _ (by decide) (by decide), hl.r8]⟩

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ s₀' : State} (hp : UPre c S byteMode s₀)
  (hp' : UPre c S byteMode s₀') (hq : (seqArm c S byteMode).pub s₀ s₀')
include hp hp' hq

/-- One segment from `k` whole blocks is constant time. -/
theorem seg_ct (hT : FinalTaint c M) (k : Nat) :
    RelCT isa (SRel c S M s₀ s₀' k) (c.seg M) fun _ _ => True := by
  have a := rel_agree (F := fun s => c.bs * k < N c s₀ ∧ FInv c S M s₀ k s ∧ s.syms = s₀.syms)
    (F' := fun s => c.bs * k < N c s₀' ∧ FInv c S M s₀' k s ∧ s.syms = s₀'.syms)
    (G := AfterArgs c S M s₀ k) (G' := AfterArgs c S M s₀' k) (Taint.ofRegs (loopRegs c))
    (fun _ _ h h' => Taint.agree_ofRegs (FInv.agree hq h.2.1 h'.2.1)) hT.pre
    (fun _ h => VG.Arm.WP.mono_syms (callArgsO_wp S h.2.1.r4 h.2.1.r8 h.2.1.r11) fun _ x sy =>
      ⟨_, h.2.1, x, sy.trans h.2.2⟩)
    (fun _ h => VG.Arm.WP.mono_syms (callArgsO_wp S h.2.1.r4 h.2.1.r8 h.2.1.r11) fun _ x sy =>
      ⟨_, h.2.1, x, sy.trans h.2.2⟩)
  -- The call, with the same regions in both runs.
  let rd : List Region := [⟨State.addr (Kp s₀), S.keyLen⟩]
  let wr : List Region := [⟨State.addr (Sc c s₀ + BitVec.ofNat 32 oOff), c.bs⟩]
  have spA : ∀ {s₂ s₂' : State}, AfterArgs c S M s₀ k s₂ → AfterArgs c S M s₀' k s₂' → s₂.sp = s₂'.sp :=
    fun ⟨_, hl, x, _⟩ ⟨_, hl', x', _⟩ => by rw [x.sp, hl.sp, x'.sp, hl'.sp, pub_sp hq]
  have syA : ∀ {s₂ s₂' : State}, AfterArgs c S M s₀ k s₂ → AfterArgs c S M s₀' k s₂' →
      ∀ x ∈ S.consts, s₂.syms x.1 = s₂'.syms x.1 :=
    fun ⟨_, _, _, sy⟩ ⟨_, _, _, sy'⟩ x hx => by rw [sy, sy', pub_syms hq x hx]
  -- The arguments in registers, through the callee's view of a state.
  have regsA : ∀ {s₂ s₂' : State} (h : AfterArgs c S M s₀ k s₂) (h' : AfterArgs c S M s₀' k s₂'),
      s₂.gpr .r0 = s₂'.gpr .r0 ∧ s₂.gpr .r1 = s₂'.gpr .r1 ∧ s₂.gpr .r2 = s₂'.gpr .r2 ∧
        (c.r3Pub = true → s₂.gpr .r3 = s₂'.gpr .r3) := fun h h' => by
    have p := h.callPre hp
    have p' := h'.callPre hp'
    rw [← pub_K hq, ← pub_R hq, ← pub_Sc hq] at p'
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
  have callR : RelCT isa (fun s₂ s₂' => AfterArgs c S M s₀ k s₂ ∧ AfterArgs c S M s₀' k s₂') c.callStep
      fun _ _ => True := by
    unfold Core.callStep
    split
    rotate_left
    · rename_i hs
      refine RelCT.frame (fun s₂ s₂' h => spA h.1 h.2) ?_
      intro a b t₁ t₂ a' b' ⟨s₂, s₂', ⟨h, h'⟩, pa, pb⟩ e₁ e₂
      have p := h.callPre hp
      have p' := h'.callPre hp'
      have eC : Cs c s₀' = Cs c s₀ := by simp only [Cs]; rw [pub_Sc hq]
      rw [← pub_K hq, ← pub_R hq, eC, ← pub_Sc hq] at p'
      have hsp := spA h h'
      rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using p.sp8 hs), Option.some.injEq] at pa
      rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using p'.sp8 hs), Option.some.injEq] at pb
      subst pa pb
      have eA : Push.argR s₂' = Push.argR s₂ := by rw [Push.argR, Push.argR, hsp]
      have syms := syA h h'
      have eT : tabRegs S.consts s₂' = tabRegs S.consts s₂ := by
        simp only [tabRegs, Abi.constRegions]
        exact List.map_congr_left fun x hx => by rw [syms x hx]
      let wr' : List Region := [⟨State.addr (Sc c s₀ + BitVec.ofNat 32 oOff), c.bs⟩,
        ⟨State.addr (Cs c s₀), c.stackScratch⟩]
      have cw : Covers ([⟨State.addr (Sc c s₀ + BitVec.ofNat 32 oOff), c.bs⟩] ++
          [⟨State.addr (Cs c s₀), c.stackScratch⟩]) s₂.wr := Covers.append_left p.wB (p.wC hs)
      have cw' : Covers ([⟨State.addr (Sc c s₀ + BitVec.ofNat 32 oOff), c.bs⟩] ++
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
    have p := h.callPre hp
    have p' := h'.callPre hp'
    rw [← pub_K hq, ← pub_R hq, ← pub_Sc hq] at p'
    obtain ⟨r0, r1, r2, r3⟩ := regsA h h'
    refine ⟨S.pre_of h0 _ p.ecbPre, S.pre_of h0 _ p'.ecbPre, S.pub_of h0 _ _ ?_ ?_ ?_ ?_ fun hr => ?_,
      Covers.append_left p.rK (Covers.right p.wB), p.wB, Covers.append_left p'.rK (Covers.right p'.wB), p'.wB⟩
    · simp only [State.withRegions_sp, State.callEntry_sp]; exact spA h h'
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r0]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r1]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r2]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r3 hr]
  have cr := rel_wp (G := AfterCallF c s₀ k) (G' := AfterCallF c s₀' k) callR
    (fun _ h => WP.mono (call_wp S (h.callPre hp)) fun _ cp => afterCallF h cp)
    (fun _ h => WP.mono (call_wp S (h.callPre hp')) fun _ cp => afterCallF h cp)
  obtain ⟨_, hB⟩ := hT.rest
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => AfterCallF c s₀ k s₁ ∧ AfterCallF c s₀' k s₂)
    (Taint.ofRegs [.r6, .r7, .r8])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.r6, h.2.r6, pub_Dp hq]
      · rw [h.1.r7, h.2.r7, pub_N hq]
      · rw [h.1.r8, h.2.r8, pub_Sc hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h).seq ((cr.mono (fun _ _ h => h) fun _ _ h => h).seq
    (b.mono (fun _ _ h => h) fun _ _ h => h))

/-- The loop's relation, with the bytes left. -/
def LRelF (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N c s₀ - c.bs * k ∧ SRel c S M s₀ s₀' k s₁ s₂

theorem loopF_ct (hM : FinalOk c M) (hT : FinalTaint c M) (n : Nat) :
    RelCT isa (LRelF (c := c) (S := S) (M := M) (s₀ := s₀) (s₀' := s₀') n) (.loop (c.seg M) .ne)
      fun s₁ s₂ => FDone c S M s₀ s₁ ∧ FDone c S M s₀' s₂ := by
  refine RelCT.loop (M := isa) (LRelF (c := c) (S := S) (M := M) (s₀ := s₀) (s₀' := s₀')) (fun n => ?_) n
  have hN := pub_N hq
  have hb := S.bs_pos
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRelF n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N c s₀ - c.bs * k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (seg_ct hp hp' hq hT k).wp
    (F₁ := fun (s : State) => (SegPost c S M s₀ k s ∧ c.bs * k < N c s₀) ∧ s.syms = s₀.syms)
    (F₂ := fun (s : State) => SegPost c S M s₀' k s ∧ s.syms = s₀'.syms)
    fun _ _ h => ⟨VG.Arm.WP.mono_syms (seg_ok hp hM h.1.1 h.1.2.1 h.1.2.2) fun _ r sy => ⟨⟨r, h.1.1⟩,
        sy.trans h.1.2.2⟩,
      VG.Arm.WP.mono_syms (seg_ok hp' hM h.2.1 h.2.2.1 h.2.2.2) fun _ r sy => ⟨r, sy.trans h.2.2.2⟩⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨⟨z₁, d₁, i₁⟩, hk⟩, y₁⟩, ⟨⟨z₂, d₂, i₂⟩, y₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (N c s₀ ≤ c.bs * (k + 1)) := by
    show VG.Arm.eval .ne s₁ = _; rw [eval_ne, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide (N c s₀ ≤ c.bs * (k + 1)) := by
    show VG.Arm.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N c s₀ ≤ c.bs * (k + 1) := by simpa using hf
    exact ⟨d₁ h0, d₂ (by rw [← hN]; exact h0)⟩
  · rw [e₁] at ht
    have h0 : ¬ N c s₀ ≤ c.bs * (k + 1) := by simpa using ht
    refine ⟨N c s₀ - c.bs * (k + 1), by rw [Nat.mul_succ] at h0 ⊢; omega, k + 1, rfl,
      ⟨by omega, i₁ (by omega), y₁⟩, ⟨by rw [← hN]; omega, i₂ (by rw [← hN]; omega), y₂⟩⟩

end

theorem seqFinal_rel {c : Core} (S : CoreSpec c) {M : Mode} (hM : FinalOk c M) (hT : FinalTaint c M)
    {s₀ s₀' : State} (h0 : (seqFinalArm c S M).pre s₀) (h0' : (seqFinalArm c S M).pre s₀')
    (hq : (seqFinalArm c S M).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (c.seqFinal M) fun _ _ => True := by
  have hq : (seqArm c S byteMode).pub s₀ s₀' := hq
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  obtain ⟨_, hepi⟩ := hT.epi
  obtain ⟨_, hnil⟩ := nil_taint
  have hN := pub_N hq
  have hsp := pub_sp hq
  have wfA : ∀ {s : State}, UPre c S byteMode s →
      s.sp.toNat + argBytes c ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, argBytes c⟩ r :=
    fun {s} h => by
      have e : (⟨State.addr s.sp, argBytes c⟩ : Region) = argR c s := by simp [stackArgAddr]
      exact ⟨h.spF, by rw [e]; exact h.arg_wr⟩
  have hj : argBytes c = 4 * (if c.rounds then 2 else 1) := by unfold argBytes; split <;> rfl
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => (FInv c S M s₀ 0 s ∧ s.z = decide (N c s₀ = 0)) ∧ s.syms = s₀.syms)
    (G' := fun s => (FInv c S M s₀' 0 s ∧ s.z = decide (N c s₀' = 0)) ∧ s.syms = s₀'.syms)
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
        · rcases (by omega : i = 0) with rfl
          exact hq.2.2.2.2.2.1
        · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
          · exact hq.2.2.2.2.2.1
          · exact hq.2.2.2.2.2.2.1 hr) hT.pro
    (fun s e => by
      rw [e]; exact VG.Arm.WP.mono_syms (prologue_wp hp) fun _ h sy => ⟨⟨FInv.of_linv h.1, h.2⟩, sy⟩)
    (fun s e => by
      rw [e]; exact VG.Arm.WP.mono_syms (prologue_wp hp') fun _ h sy => ⟨⟨FInv.of_linv h.1, h.2⟩, sy⟩)
  have ev {s : State} (h : s.z = decide (N c s₀ = 0)) : isa.eval .eq s = some (decide (N c s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h]
  have ev' {s : State} (h : s.z = decide (N c s₀' = 0)) : isa.eval .eq s = some (decide (N c s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h, hN]
  have nil := RelCT.taint (A := taint)
    (P := fun a b => (((FInv c S M s₀ 0 a ∧ a.z = decide (N c s₀ = 0)) ∧ a.syms = s₀.syms) ∧
      ((FInv c S M s₀' 0 b ∧ b.z = decide (N c s₀' = 0)) ∧ b.syms = s₀'.syms)) ∧ isa.eval .eq a = some true)
    (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => ((FInv c S M s₀ 0 a ∧ a.z = decide (N c s₀ = 0)) ∧ a.syms = s₀.syms) ∧
      ((FInv c S M s₀' 0 b ∧ b.z = decide (N c s₀' = 0)) ∧ b.syms = s₀'.syms))
      (.ite .eq (.block []) (.loop (c.seg M) .ne))
      (fun a b => FDone c S M s₀ a ∧ FDone c S M s₀' b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1.1.2, ev' h.2.1.2]) ?_ ?_
    · refine (nil.wp (F₁ := FDone c S M s₀) (F₂ := FDone c S M s₀') fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N c s₀ = 0 := by
        have := h.2; rw [ev h.1.1.1.2] at this; simpa using this
      have h0' : N c s₀' = 0 := by rw [← hN]; exact h0
      have e0 : nF c s₀ = 0 := by simp only [nF, h0, Nat.zero_div]
      have r0 : rF c s₀ = 0 := by simp only [rF, h0, Nat.zero_mod]
      have e0' : nF c s₀' = 0 := by simp only [nF, h0', Nat.zero_div]
      have r0' : rF c s₀' = 0 := by simp only [rF, h0', Nat.zero_mod]
      have i₁ : FInv c S M s₀ (nF c s₀) a := by rw [e0]; exact h.1.1.1.1
      have i₂ : FInv c S M s₀' (nF c s₀') b := by rw [e0']; exact h.1.2.1.1
      exact ⟨WP.block_nil (i₁.done r0), WP.block_nil (i₂.done r0')⟩
    · refine (loopF_ct hp hp' hq hM hT (N c s₀ - c.bs * 0)).mono
        (fun a b h => ⟨0, rfl, ⟨?_, h.1.1.1.1, h.1.1.2⟩, ⟨?_, h.1.2.1.1, h.1.2.2⟩⟩) fun _ _ h => h
      all_goals
        have := h.2; rw [ev h.1.1.1.2] at this
        have : N c s₀ ≠ 0 := by simpa using this
        rw [Nat.mul_zero]; omega
  have epi := RelCT.taint (A := taint)
    (P := fun a b => FDone c S M s₀ a ∧ FDone c S M s₀' b)
    (Taint.ofRegs [.r5, .r8]) (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r5, h.2.r5, pub_Iv hq]
      · rw [h.1.r8, h.2.r8, pub_Sc hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h).seq (mid.seq epi)

theorem seqFinal_ct {c : Core} (S : CoreSpec c) {M : Mode} (hM : FinalOk c M) (hT : FinalTaint c M) :
    ConstantTime isa (seqFinalArm c S M).pre (seqFinalArm c S M).pub (c.seqFinal M) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seqFinal_rel S hM hT h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A core and a mode the final function runs whose code between the calls
passes the taint checks give a function that is correct and constant time
under `seqFinalArm`, and so under any contract it implies. -/
theorem seqFinal_verified {c : Core} (S : CoreSpec c) {M : Mode} (hM : FinalOk c M) (hT : FinalTaint c M)
    {k : Contract isa} (hk : (seqFinalArm c S M).Implies k) : Verified Arm.target (c.seqFinal M) k :=
  Verified.of_correct (fun _ hs => seqFinal_wp S hM hs) (seqFinal_ct S hM hT) hk

end VG.Proof.Modes.Arm
