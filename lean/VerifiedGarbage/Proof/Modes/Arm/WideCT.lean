module

public import VerifiedGarbage.Proof.Modes.Arm.Wide
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Modes.Arm.Wide
meta import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The modes a group of blocks at a time on ARMv7: constant time

Two runs of `Core.seqW` from states that agree on the public arguments are
related piece by piece (`RelCT`), as those of `Core.seq` are (`SeqCT.lean`),
whose proof covers the prologue, the blocks one at a time and the epilogue
here too. Of the groups: the taint analysis covers the code between the
calls, from the registers the correctness proof pins to the public
arguments (`WInv`) and the buffer's address, the stack pointer, which the
analysis is given in `r12` after each `add r12, sp, #0` (a block of its
own, since the analysis does not know the stack pointer of a frame to be
public); each call of the core is constant time by the core's own proof,
its public data (the schedule's and the blocks' addresses, the number of
blocks and the stack pointer) being the same in both runs; and both runs
take the same number of groups, the number of blocks being public.

The code between the calls depends on the core and the wide mode, so its
taint checks are hypotheses (`WideTaint`, with `SeqTaint` for the rest),
which each cipher's instance proves with `taint_decide`.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Proof.MdStream.Arm (Upd eval_eq eval_ne cmp0)

/-- The taint checks of the code between the calls of the groups of
`2 ^ lg` blocks. -/
structure LevelTaint (c : Core) (wm : WMode) (lg : Nat) : Prop where
  head : ∃ h, (taint.check (Taint.ofRegs [.r7]) (.block (Core.groupsLeft lg)) h).isSome = true
  pre : ∃ h, (taint.check (Taint.ofRegs (.r12 :: loopRegs c))
    (.block (c.wopsCode (wm.pre (2 ^ lg)) ++ c.wcallArgs wm.onW (2 ^ lg))) h).isSome = true
  post : ∃ h, (taint.check (Taint.ofRegs [.r6, .r7, .r8, .r12])
    (.block (c.wopsCode (wm.post (2 ^ lg)) ++ c.wadvance lg)) h).isSome = true

/-- The taint checks of the code between the calls of `c.wide wm lgs wb`. -/
structure WideTaint (c : Core) (wm : WMode) (lgs : List Nat) (wb : Nat) : Prop where
  levels : ∀ lg ∈ lgs, LevelTaint c wm lg
  wipe : ∃ h, (taint.check (Taint.ofRegs [.r12])
    (.block (.mov .r2 (.imm 0) :: Impl.StackScratch.Arm.wipeStores (wb / 4))) h).isSome = true

theorem wbuf_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block Core.wbuf) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp7_taint : ∃ h, (taint.check (Taint.ofRegs [.r7]) (.block [.cmp .r7 (.imm 0)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- Two runs of no instructions. -/
theorem relCT_nil {P : State → State → Prop} : RelCT isa P (.block []) P := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, hp⟩

/-- Two runs of a frame that reserves stack leak the same trace if the runs
of its body do, and end as the frame's end leaves what the body's runs end
in. -/
theorem RelCT.allocFrameQ {bytes : Nat} {body : Prog isa} {P Q : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocated bytes s₁ ∧ b = allocated bytes s₂) body Q) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes))
      fun a b => ∃ t₁ t₂, Q t₁ t₂ ∧ a = freed bytes t₁ ∧ b = freed bytes t₂ := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      have ea : ∀ {s a : State}, isa.push (.alloc bytes) s = some a → a = allocated bytes s := by
        intro s a h
        simp only [isa, push] at h
        split at h <;> [cases h; cases h]
        rfl
      have ef : ∀ {a t s' : State}, isa.pop (.free bytes) a t = some s' → s' = freed bytes t := by
        intro a t s' h
        simp only [isa, pop] at h
        split at h <;> [cases h; cases h]
        rfl
      obtain ⟨ht, hq⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, ea p₁, ea p₂⟩ b₁ b₂
      refine ⟨?_, _, _, hq, ef q₁, ef q₂⟩
      rw [ht]
      simp only [addrs]

/-- The arguments in registers of two calls with the same schedule, number
of rounds, blocks and number of blocks. -/
theorem CallPreN.regs_eq {c : Core} {S : CoreSpec c} {s s' : State} {K R B : BitVec 32} {G : Nat}
    (p : CallPreN c S s K R B G) (p' : CallPreN c S s' K R B G) :
    s.gpr .r0 = s'.gpr .r0 ∧ s.gpr .r1 = s'.gpr .r1 ∧ s.gpr .r2 = s'.gpr .r2 ∧
      (c.r3Pub = true → s.gpr .r3 = s'.gpr .r3) := by
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

/-- The relation before a group of `G` blocks, in two runs. -/
def WBRel (wb : Nat) (c : Core) (S : CoreSpec c) (M : Mode) (G : Nat) (s₀ s₀' : State) (k : Nat)
    (s₁ s₂ : State) : Prop :=
  (k + G ≤ N c s₀ ∧ WInv wb c S M s₀ k s₁) ∧ (k + G ≤ N c s₀' ∧ WInv wb c S M s₀' k s₂)

/-- What is known once the buffer's address is in `r12`. -/
def WAfterBuf (wb : Nat) (c : Core) (S : CoreSpec c) (M : Mode) (G : Nat) (s₀ : State) (k : Nat)
    (s₁ : State) : Prop :=
  ∃ s, (k + G ≤ N c s₀ ∧ WInv wb c S M s₀ k s) ∧ Upd s s₁ .r12 s.sp

/-- What is known after the code before a group's call. -/
def WAfterArgs (wb : Nat) (c : Core) (S : CoreSpec c) (M : Mode) (pre : List WOp) (onW : Bool) (G : Nat)
    (s₀ : State) (k : Nat) (s₃ : State) : Prop :=
  ∃ s, (k + G ≤ N c s₀ ∧ WInv wb c S M s₀ k s) ∧ WMid wb c M pre onW s₀ G k s s₃

/-- What is known once the buffer's address is in `r12` again, after the call. -/
def WAfterBuf2 (wb : Nat) (c : Core) (M : Mode) (s₀ : State) (k : Nat) (s₅ : State) : Prop :=
  ∃ s₄, WAfterCall wb c M s₀ k s₄ ∧ Upd s₄ s₅ .r12 s₄.sp

/-- The relation between the groups, in two runs: as many blocks done. -/
def WRel (wb : Nat) (c : Core) (S : CoreSpec c) (M : Mode) (s₀ s₀' : State) (s₁ s₂ : State) : Prop :=
  ∃ k, k ≤ N c s₀ ∧ WInv wb c S M s₀ k s₁ ∧ WInv wb c S M s₀' k s₂

/-- The relation of a level's loop, with the number of blocks left. -/
def WLRel (wb : Nat) (c : Core) (S : CoreSpec c) (M : Mode) (lg : Nat) (s₀ s₀' : State) (n : Nat)
    (s₁ s₂ : State) : Prop :=
  ∃ j, n = N c s₀ - j ∧ WBRel wb c S M (2 ^ lg) s₀ s₀' j s₁ s₂

/-- The relation around the groups, in two runs: as many blocks done. -/
def LRelK (c : Core) (S : CoreSpec c) (M : Mode) (s₀ s₀' : State) (s₁ s₂ : State) : Prop :=
  ∃ k, k ≤ N c s₀ ∧ LInv c S M s₀ k s₁ ∧ LInv c S M s₀' k s₂

section
variable {c : Core} {S₀ S : CoreSpec c} {M : Mode} {s₀ s₀' : State} {wb : Nat}

theorem pub_Wp (hq : (seqArm c S M).pub s₀ s₀') : Wp wb s₀' = Wp wb s₀ := by
  simp only [Wp]; rw [pub_sp hq]

/-- One group from `k` blocks is constant time. -/
theorem wbody_ct (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hp' : UPre c S M s₀')
    (hq : (seqArm c S M).pub s₀ s₀') (hd : Deep S₀ S wb) (hW : wb ≤ 4096) {wm : WMode} {lg : Nat}
    (hl : LevelOk c M wm wb lg) (hT : LevelTaint c wm lg) (k : Nat) :
    RelCT isa (WBRel wb c S M (2 ^ lg) s₀ s₀' k) (c.wbody wm lg) fun _ _ => True := by
  have hw := hl.ok
  have eW := pub_Wp (wb := wb) hq
  -- The buffer's address.
  have a := rel_agree (F := fun s => k + 2 ^ lg ≤ N c s₀ ∧ WInv wb c S M s₀ k s)
    (F' := fun s => k + 2 ^ lg ≤ N c s₀' ∧ WInv wb c S M s₀' k s)
    (G := WAfterBuf wb c S M (2 ^ lg) s₀ k) (G' := WAfterBuf wb c S M (2 ^ lg) s₀' k) (Taint.ofRegs [])
    (fun _ _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) wbuf_taint
    (fun s h => WP.mono wbuf_wp fun _ u => ⟨s, h, u⟩) (fun s h => WP.mono wbuf_wp fun _ u => ⟨s, h, u⟩)
  -- The operations before the call, and its arguments.
  have b := rel_agree (F := WAfterBuf wb c S M (2 ^ lg) s₀ k) (F' := WAfterBuf wb c S M (2 ^ lg) s₀' k)
    (G := WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀ k)
    (G' := WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀' k) (Taint.ofRegs (.r12 :: loopRegs c))
    (fun s₁ s₂ ⟨s, h, u⟩ ⟨s', h', u'⟩ => Taint.agree_ofRegs fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [u.gpr, u'.gpr, h.2.sp, h'.2.sp, eW]
      · have h12 : r ≠ .r12 := by
          rintro rfl
          revert hr
          unfold loopRegs
          split <;> decide
        rw [u.other _ h12, u'.other _ h12]
        exact LInv.agree hq h.2.inv h'.2.inv r hr)
    hT.pre
    (fun s₁ ⟨s, h, u⟩ => WP.mono (wpre_wp hp hd hW hl h.1 h.2 u) fun _ x => ⟨s, h, x⟩)
    (fun s₁ ⟨s, h, u⟩ => WP.mono (wpre_wp hp' hd hW hl h.1 h.2 u) fun _ x => ⟨s, h, x⟩)
  -- The call, with the same regions in both runs.
  have cpre : ∀ {t₀ : State} (_ : UPre c S M t₀) {s₃ : State},
      WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) t₀ k s₃ →
      CallPreN c S₀ s₃ (Kp t₀) (Rp t₀) (if wm.onW then Wp wb t₀ else Dk t₀ c M k) (2 ^ lg) :=
    fun {_} hpt {_} ⟨_, h, x⟩ => x.callPre hpt hd hw.byte hw.pos h.1 hl.fit hW h.2
  have cpre' : ∀ {s₃ : State}, WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀' k s₃ →
      CallPreN c S₀ s₃ (Kp s₀) (Rp s₀) (if wm.onW then Wp wb s₀ else Dk s₀ c M k) (2 ^ lg) := fun h => by
    have p := cpre hp' h
    rw [← pub_K hq, ← pub_R hq, ← pub_Dk hq, eW] at p
    exact p
  have spA : ∀ {s₃ s₃' : State}, WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀ k s₃ →
      WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀' k s₃' → s₃.sp = s₃'.sp :=
    fun ⟨_, h, x⟩ ⟨_, h', x'⟩ => by rw [x.sp, h.2.sp, x'.sp, h'.2.sp, eW]
  have callR : RelCT isa (fun s₃ s₃' => WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀ k s₃ ∧
      WAfterArgs wb c S M (wm.pre (2 ^ lg)) wm.onW (2 ^ lg) s₀' k s₃') (.call c.name c.code)
      fun _ _ => True := by
    refine RelCT.call S₀.correct S₀.ct [⟨State.addr (Kp s₀), S₀.keyLen⟩]
      [⟨State.addr (if wm.onW then Wp wb s₀ else Dk s₀ c M k), c.bs * 2 ^ lg⟩] fun s₃ s₃' ⟨h, h'⟩ => ?_
    have p := cpre hp h
    have p' := cpre' h'
    obtain ⟨r0, r1, r2, r3⟩ := p.regs_eq p'
    refine ⟨S₀.pre_of h0 _ p.ecbPre, S₀.pre_of h0 _ p'.ecbPre, S₀.pub_of h0 _ _ ?_ ?_ ?_ ?_ fun hr => ?_,
      Covers.append_left p.rK (Covers.right p.wB), p.wB, Covers.append_left p'.rK (Covers.right p'.wB), p'.wB⟩
    · simp only [State.withRegions_sp, State.callEntry_sp]; exact spA h h'
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r0]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r1]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r2]
    · rw [narrow_gpr _ _ _ (by decide) (by decide), narrow_gpr _ _ _ (by decide) (by decide), r3 hr]
  have cr := rel_wp (G := WAfterCall wb c M s₀ k) (G' := WAfterCall wb c M s₀' k) callR
    (fun _ h => WP.mono (callN_wp S₀ (cpre hp h) h0) fun _ cp => by
      obtain ⟨_, x, y⟩ := h; exact wafterCall x.2 y cp)
    (fun _ h => WP.mono (callN_wp S₀ (cpre hp' h) h0) fun _ cp => by
      obtain ⟨_, x, y⟩ := h; exact wafterCall x.2 y cp)
  -- The buffer's address again, and the operations after the call.
  have d := rel_agree (F := WAfterCall wb c M s₀ k) (F' := WAfterCall wb c M s₀' k)
    (G := WAfterBuf2 wb c M s₀ k) (G' := WAfterBuf2 wb c M s₀' k) (Taint.ofRegs [])
    (fun _ _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) wbuf_taint
    (fun s h => WP.mono wbuf_wp fun _ u => ⟨s, h, u⟩) (fun s h => WP.mono wbuf_wp fun _ u => ⟨s, h, u⟩)
  obtain ⟨_, hB⟩ := hT.post
  have e := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => WAfterBuf2 wb c M s₀ k s₁ ∧ WAfterBuf2 wb c M s₀' k s₂)
    (Taint.ofRegs [.r6, .r7, .r8, .r12])
    (fun s₁ s₂ ⟨⟨t, h, u⟩, ⟨t', h', u'⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [u.other _ (by decide), u'.other _ (by decide), h.r6, h'.r6, pub_Dk hq]
      · rw [u.other _ (by decide), u'.other _ (by decide), h.r7, h'.r7, pub_N hq]
      · rw [u.other _ (by decide), u'.other _ (by decide), h.r8, h'.r8, pub_Sc hq]
      · rw [u.gpr, u'.gpr, h.sp, h'.sp, eW]) hB
  unfold Core.wbody
  exact (a.mono (fun _ _ h => h) fun _ _ h => h).seq ((b.mono (fun _ _ h => h) fun _ _ h => h).seq
    ((cr.mono (fun _ _ h => h) fun _ _ h => h).seq ((d.mono (fun _ _ h => h) fun _ _ h => h).seq
      (e.mono (fun _ _ h => h) fun _ _ h => h))))

/-- The loop of a level is constant time. -/
theorem wloop_ct (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hp' : UPre c S M s₀')
    (hq : (seqArm c S M).pub s₀ s₀') (hd : Deep S₀ S wb) (hW : wb ≤ 4096) {wm : WMode} {lg : Nat}
    (hl : LevelOk c M wm wb lg) (hT : LevelTaint c wm lg) (n : Nat) :
    RelCT isa (WLRel wb c S M lg s₀ s₀' n) (.loop (c.wbody wm lg) .ne) (WRel wb c S M s₀ s₀') := by
  refine RelCT.loop (M := isa) (WLRel wb c S M lg s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  have hG := hl.ok.pos
  refine (RelCT.exists_ fun j => ?_).mono (fun s₁ s₂ (h : WLRel wb c S M lg s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N c s₀ - j
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (wbody_ct h0 hp hp' hq hd hW hl hT j).wp
    (F₁ := fun (s : State) => (WInv wb c S M s₀ (j + 2 ^ lg) s ∧
      s.z = decide ((N c s₀ - (j + 2 ^ lg)) / 2 ^ lg = 0)) ∧ j + 2 ^ lg ≤ N c s₀)
    (F₂ := fun (s : State) => WInv wb c S M s₀' (j + 2 ^ lg) s ∧
      s.z = decide ((N c s₀' - (j + 2 ^ lg)) / 2 ^ lg = 0))
    fun _ _ h => ⟨WP.mono (wbody_ok h0 hp hd hW hl h.1.1 h.1.2) fun _ r => ⟨r, h.1.1⟩,
      wbody_ok h0 hp' hd hW hl h.2.1 h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨l₁, z₁⟩, hj⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide ((N c s₀ - (j + 2 ^ lg)) / 2 ^ lg = 0) := by
    show VG.Arm.eval .ne s₁ = _; rw [eval_ne, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide ((N c s₀ - (j + 2 ^ lg)) / 2 ^ lg = 0) := by
    show VG.Arm.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]
  refine ⟨by rw [e₁, e₂], fun _ => ⟨j + 2 ^ lg, hj, l₁, l₂⟩, fun ht => ?_⟩
  rw [e₁] at ht
  have h0' : ¬ (N c s₀ - (j + 2 ^ lg)) / 2 ^ lg = 0 := by simpa using ht
  rw [Nat.div_eq_zero_iff_lt hG] at h0'
  exact ⟨N c s₀ - (j + 2 ^ lg), by omega_using [hj, hG], j + 2 ^ lg, rfl, ⟨by omega_using [h0', hj], l₁⟩,
    ⟨by rw [← hN]; omega_using [h0', hj], l₂⟩⟩

/-- A level is constant time. -/
theorem wlevel_ct (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hp' : UPre c S M s₀')
    (hq : (seqArm c S M).pub s₀ s₀') (hd : Deep S₀ S wb) (hW : wb ≤ 4096) {wm : WMode} {lg : Nat}
    (hl : LevelOk c M wm wb lg) (hT : LevelTaint c wm lg) :
    RelCT isa (WRel wb c S M s₀ s₀') (c.wlevel wm lg) (WRel wb c S M s₀ s₀') := by
  have hN := pub_N hq
  have hG := hl.ok.pos
  unfold Core.wlevel
  refine RelCT.exists_ fun k => ?_
  have head := rel_agree (F := fun s => k ≤ N c s₀ ∧ WInv wb c S M s₀ k s)
    (F' := fun s => WInv wb c S M s₀' k s)
    (G := fun s => (k ≤ N c s₀ ∧ WInv wb c S M s₀ k s) ∧ s.z = decide ((N c s₀ - k) / 2 ^ lg = 0))
    (G' := fun s => WInv wb c S M s₀' k s ∧ s.z = decide ((N c s₀' - k) / 2 ^ lg = 0))
    (Taint.ofRegs [.r7])
    (fun s s' h h' => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have e : s.gpr .r7 = BitVec.ofNat 32 (N c s₀ - k) := h.2.inv.r7
      have e' : s'.gpr .r7 = BitVec.ofNat 32 (N c s₀' - k) := h'.inv.r7
      rw [e, e', hN])
    hT.head
    (fun s h => WP.mono (whead_wp hp hd hl.sh h.2) fun _ x => ⟨⟨h.1, x.1⟩, x.2⟩)
    (fun s h => whead_wp hp' hd hl.sh h)
  refine (head.mono (fun s₁ s₂ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) fun _ _ h => h).seq ?_
  have ev {s : State} (h : s.z = decide ((N c s₀ - k) / 2 ^ lg = 0)) :
      isa.eval .eq s = some (decide ((N c s₀ - k) / 2 ^ lg = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h]
  have ev' {s : State} (h : s.z = decide ((N c s₀' - k) / 2 ^ lg = 0)) :
      isa.eval .eq s = some (decide ((N c s₀ - k) / 2 ^ lg = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h, hN]
  refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev' h.2.2]) ?_ ?_
  · exact relCT_nil.mono (fun _ _ h => h) fun a b h => ⟨k, h.1.1.1.1, h.1.1.1.2, h.1.2.1⟩
  · refine (wloop_ct h0 hp hp' hq hd hW hl hT (N c s₀ - k)).mono (fun a b h => ?_) fun _ _ h => h
    have hf := h.2
    rw [ev h.1.1.2] at hf
    have h0' : ¬ (N c s₀ - k) / 2 ^ lg = 0 := by simpa using hf
    rw [Nat.div_eq_zero_iff_lt hG] at h0'
    exact ⟨k, rfl, ⟨by omega_using [h0', h.1.1.1.1], h.1.1.1.2⟩,
      ⟨by rw [← hN]; omega_using [h0', h.1.1.1.1], h.1.2.1⟩⟩

/-- The levels are constant time. -/
theorem wlevels_ct (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hp' : UPre c S M s₀')
    (hq : (seqArm c S M).pub s₀ s₀') (hd : Deep S₀ S wb) (hW : wb ≤ 4096) {wm : WMode} {lgs : List Nat}
    (hl : ∀ lg ∈ lgs, LevelOk c M wm wb lg) (hT : ∀ lg ∈ lgs, LevelTaint c wm lg) :
    RelCT isa (WRel wb c S M s₀ s₀') (c.wlevels wm lgs) (WRel wb c S M s₀ s₀') := by
  induction lgs with
  | nil => exact relCT_nil
  | cons lg lgs ih =>
    show RelCT isa _ (.seq (c.wlevel wm lg) (c.wlevels wm lgs)) _
    exact (wlevel_ct h0 hp hp' hq hd hW (hl lg List.mem_cons_self) (hT lg List.mem_cons_self)).seq
      (ih (fun lg' h' => hl lg' (List.mem_cons_of_mem _ h')) fun lg' h' => hT lg' (List.mem_cons_of_mem _ h'))

/-- The groups, in the buffer's frame, are constant time. -/
theorem wide_ct (h0 : c.stackScratch = 0) (hp : UPre c S M s₀) (hp' : UPre c S M s₀')
    (hq : (seqArm c S M).pub s₀ s₀') (hd : Deep S₀ S wb) (hwb : BufOk wb) {wm : WMode} {lgs : List Nat}
    (hl : ∀ lg ∈ lgs, LevelOk c M wm wb lg) (hT : WideTaint c wm lgs wb) :
    RelCT isa (LRelK c S M s₀ s₀') (c.wide wm lgs wb) (LRelK c S M s₀ s₀') := by
  have eW := pub_Wp (wb := wb) hq
  unfold Core.wide
  refine (RelCT.allocFrameQ (Q := WRel wb c S M s₀ s₀') ?_).mono (fun _ _ h => h)
    fun a b ⟨t₁, t₂, ⟨k, hk, h₁, h₂⟩, e₁, e₂⟩ => ⟨k, hk, by rw [e₁]; exact h₁.inv, by rw [e₂]; exact h₂.inv⟩
  refine RelCT.seq (R := WRel wb c S M s₀ s₀')
    ((wlevels_ct h0 hp hp' hq hd (Nat.le_of_lt hwb.2.1) hl hT.levels).mono
      (fun a b ⟨s₁, s₂, ⟨k, hk, h₁, h₂⟩, e₁, e₂⟩ => ⟨k, hk, by rw [e₁]; exact h₁.toW, by rw [e₂]; exact h₂.toW⟩)
      fun _ _ h => h) ?_
  -- The buffer zeroed.
  refine RelCT.exists_ fun k => ?_
  by_cases hk : k ≤ N c s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.1
  have a := rel_agree (F := fun s => WInv wb c S M s₀ k s) (F' := fun s => WInv wb c S M s₀' k s)
    (G := fun s₁ => ∃ s, WInv wb c S M s₀ k s ∧ Upd s s₁ .r12 s.sp)
    (G' := fun s₁ => ∃ s, WInv wb c S M s₀' k s ∧ Upd s s₁ .r12 s.sp) (Taint.ofRegs [])
    (fun _ _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) wbuf_taint
    (fun s h => WP.mono wbuf_wp fun _ u => ⟨s, h, u⟩) (fun s h => WP.mono wbuf_wp fun _ u => ⟨s, h, u⟩)
  obtain ⟨_, hw⟩ := hT.wipe
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (∃ s, WInv wb c S M s₀ k s ∧ Upd s s₁ .r12 s.sp) ∧
      ∃ s, WInv wb c S M s₀' k s ∧ Upd s s₂ .r12 s.sp)
    (Taint.ofRegs [.r12]) (fun s₁ s₂ ⟨⟨t, h, u⟩, ⟨t', h', u'⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [u.gpr, u'.gpr, h.sp, h'.sp, eW]) hw
  exact ((a.seq b).wp (F₁ := WInv wb c S M s₀ k) (F₂ := WInv wb c S M s₀' k) fun s₁ s₂ h =>
    ⟨wwipe_wp hp hd hwb.2.1 h.1, wwipe_wp hp' hd hwb.2.1 h.2⟩).mono (fun s₁ s₂ h => ⟨h.2.1, h.2.2⟩)
    fun s₁ s₂ h => ⟨k, hk, h.2.1, h.2.2⟩

end

theorem seqW_rel {c : Core} (h0 : c.stackScratch = 0) (S₀ : CoreSpec c) {M : Mode} (hM : ModeOk c M)
    (hT : SeqTaint c M) {wb : Nat} (hwb : BufOk wb) {wm : WMode} {lgs : List Nat}
    (hl : ∀ lg ∈ lgs, LevelOk c M wm wb lg) (hTw : WideTaint c wm lgs wb) {s₀ s₀' : State}
    (hpre : (seqArm c (S₀.deeper wb h0) M).pre s₀) (hpre' : (seqArm c (S₀.deeper wb h0) M).pre s₀')
    (hq : (seqArm c (S₀.deeper wb h0) M).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (c.seqW M wm lgs wb) fun _ _ => True := by
  have hp := UPre.of hpre
  have hp' := UPre.of hpre'
  have hd := S₀.deeper_deep wb h0
  obtain ⟨_, hepi⟩ := hT.epi
  have hN := pub_N hq
  have hsp := pub_sp hq
  have hNlt := N_lt c s₀
  have wfA : ∀ {s : State}, UPre c (S₀.deeper wb h0) M s →
      s.sp.toNat + argBytes c ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, argBytes c⟩ r :=
    fun {s} h => by
      have e : (⟨State.addr s.sp, argBytes c⟩ : Region) = argR c s := by simp [stackArgAddr]
      exact ⟨h.spF, by rw [e]; exact h.arg_wr⟩
  have hj : argBytes c = 4 * (if c.rounds then 2 else 1) := by unfold argBytes; split <;> rfl
  -- The prologue.
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => (LInv c (S₀.deeper wb h0) M s₀ 0 s ∧ s.z = decide (N c s₀ = 0)) ∧ s.syms = s₀.syms)
    (G' := fun s => (LInv c (S₀.deeper wb h0) M s₀' 0 s ∧ s.z = decide (N c s₀' = 0)) ∧ s.syms = s₀'.syms)
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
  -- The groups.
  have wide := (RelCT.mono
    (P' := fun (a b : State) => LRelK c (S₀.deeper wb h0) M s₀ s₀' a b ∧ a.syms = s₀.syms ∧ b.syms = s₀'.syms)
    (wide_ct h0 hp hp' hq hd hwb hl hTw) (fun _ _ h => h.1) fun _ _ h => h).wp
    (F₁ := fun (s : State) => s.syms = s₀.syms) (F₂ := fun (s : State) => s.syms = s₀'.syms)
    fun a b h => by
      obtain ⟨⟨k, hk, h₁, h₂⟩, sy, sy'⟩ := h
      exact ⟨VG.Arm.WP.mono_syms (wide_wp h0 hp hd hwb hl hk h₁) fun _ _ y => y.trans sy,
        VG.Arm.WP.mono_syms (wide_wp h0 hp' hd hwb hl (by rw [← hN]; exact hk) h₂) fun _ _ y => y.trans sy'⟩
  -- The blocks left, one at a time, and the epilogue.
  have epi := RelCT.taint (A := taint)
    (P := fun a b => LInv c (S₀.deeper wb h0) M s₀ (N c s₀) a ∧ LInv c (S₀.deeper wb h0) M s₀' (N c s₀') b)
    (Taint.ofRegs [.r5, .r8]) (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r5, h.2.r5, pub_Iv hq]
      · rw [h.1.r8, h.2.r8, pub_Sc hq]) hepi
  have rest : RelCT isa
      (fun a b => LRelK c (S₀.deeper wb h0) M s₀ s₀' a b ∧ a.syms = s₀.syms ∧ b.syms = s₀'.syms)
      (.seq (.block [.cmp .r7 (.imm 0)]) (.seq (.ite .eq (.block []) (.loop (c.body M) .ne))
        (.block (c.finish M ++ restore)))) fun _ _ => True := by
    refine (RelCT.exists_ (P := fun k (a b : State) => (k ≤ N c s₀ ∧ LInv c (S₀.deeper wb h0) M s₀ k a ∧
      LInv c (S₀.deeper wb h0) M s₀' k b) ∧ a.syms = s₀.syms ∧ b.syms = s₀'.syms) fun k => ?_).mono
      (fun a b ⟨⟨k, h⟩, sy⟩ => ⟨k, h, sy⟩) fun _ _ h => h
    by_cases hk : k ≤ N c s₀
    swap
    · exact RelCT.of_false fun _ _ h => hk h.1.1
    have cmp := rel_agree
      (F := fun s => LInv c (S₀.deeper wb h0) M s₀ k s ∧ s.syms = s₀.syms)
      (F' := fun s => LInv c (S₀.deeper wb h0) M s₀' k s ∧ s.syms = s₀'.syms)
      (G := fun s => (LInv c (S₀.deeper wb h0) M s₀ k s ∧ s.z = decide (N c s₀ - k = 0)) ∧ s.syms = s₀.syms)
      (G' := fun s => (LInv c (S₀.deeper wb h0) M s₀' k s ∧ s.z = decide (N c s₀' - k = 0)) ∧ s.syms = s₀'.syms)
      (Taint.ofRegs [.r7])
      (fun s s' h h' => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.1.r7, h'.1.r7, hN])
      cmp7_taint
      (fun s h => VG.Arm.WP.mono_syms cmp7_wp fun s' x sy =>
        ⟨⟨h.1.congr x.1.gpr x.1.mem x.1.rd x.1.wr x.1.sp,
          by rw [x.2, h.1.r7]; exact cmp0 (by omega_using [hNlt])⟩, sy.trans h.2⟩)
      (fun s h => VG.Arm.WP.mono_syms cmp7_wp fun s' x sy =>
        ⟨⟨h.1.congr x.1.gpr x.1.mem x.1.rd x.1.wr x.1.sp,
          by rw [x.2, h.1.r7]; exact cmp0 (by rw [← hN]; omega_using [hNlt])⟩, sy.trans h.2⟩)
    refine (cmp.mono (fun a b h => ⟨⟨h.1.2.1, h.2.1⟩, ⟨h.1.2.2, h.2.2⟩⟩) fun _ _ h => h).seq ?_
    have ev {s : State} (h : s.z = decide (N c s₀ - k = 0)) : isa.eval .eq s = some (decide (N c s₀ - k = 0)) := by
      show VG.Arm.eval .eq s = _; rw [eval_eq, h]
    have ev' {s : State} (h : s.z = decide (N c s₀' - k = 0)) :
        isa.eval .eq s = some (decide (N c s₀ - k = 0)) := by
      show VG.Arm.eval .eq s = _; rw [eval_eq, h, hN]
    refine RelCT.seq (R := fun a b => LInv c (S₀.deeper wb h0) M s₀ (N c s₀) a ∧
      LInv c (S₀.deeper wb h0) M s₀' (N c s₀') b) (RelCT.ite (fun a b h => by rw [ev h.1.1.2, ev' h.2.1.2]) ?_ ?_)
      epi
    · refine relCT_nil.mono (fun _ _ h => h) fun a b h => ?_
      have ht := h.2
      rw [ev h.1.1.1.2] at ht
      have e : k = N c s₀ := by
        have : N c s₀ - k = 0 := by simpa using ht
        omega_using [this, hk]
      exact ⟨e ▸ h.1.1.1.1, by rw [← hN, ← e]; exact h.1.2.1.1⟩
    · refine (loop_ct hp hp' hq hM hT (N c s₀ - k)).mono (fun a b h => ?_) fun _ _ h => h
      have hf := h.2
      rw [ev h.1.1.1.2] at hf
      have h0' : N c s₀ - k ≠ 0 := by simpa using hf
      exact ⟨k, rfl, ⟨by omega_using [h0'], h.1.1.1.1, h.1.1.2⟩,
        ⟨by rw [← hN]; omega_using [h0'], h.1.2.1.1, h.1.2.2⟩⟩
  unfold Core.seqW
  exact (pro.mono (fun _ _ h => h) fun a b h => ⟨⟨0, Nat.zero_le _, h.1.1.1, h.2.1.1⟩, h.1.2, h.2.2⟩).seq
    ((wide.mono (fun _ _ h => h) fun a b h => ⟨h.1, h.2.1, h.2.2⟩).seq rest)

theorem seqW_ct {c : Core} (h0 : c.stackScratch = 0) (S₀ : CoreSpec c) {M : Mode} (hM : ModeOk c M)
    (hT : SeqTaint c M) {wb : Nat} (hwb : BufOk wb) {wm : WMode} {lgs : List Nat}
    (hl : ∀ lg ∈ lgs, LevelOk c M wm wb lg) (hTw : WideTaint c wm lgs wb) :
    ConstantTime isa (seqArm c (S₀.deeper wb h0) M).pre (seqArm c (S₀.deeper wb h0) M).pub (c.seqW M wm lgs wb) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seqW_rel h0 S₀ hM hT hwb hl hTw h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A core that takes no working space, a mode and a wide mode whose groups
compute its steps, and whose code between the calls passes the taint checks,
give a function that is correct and constant time under `seqArm` with the
buffer's bytes of stack more, and so under any contract that implies. -/
theorem seqW_verified {c : Core} (h0 : c.stackScratch = 0) (S₀ : CoreSpec c) {M : Mode} (hM : ModeOk c M)
    (hT : SeqTaint c M) {wb : Nat} (hwb : BufOk wb) {wm : WMode} {lgs : List Nat}
    (hl : ∀ lg ∈ lgs, LevelOk c M wm wb lg) (hTw : WideTaint c wm lgs wb) {k : Contract isa}
    (hk : (seqArm c (S₀.deeper wb h0) M).Implies k) : Verified Arm.target (c.seqW M wm lgs wb) k :=
  Verified.of_correct (fun _ hs => seqW_wp h0 S₀ hM hwb hl hs) (seqW_ct h0 S₀ hM hT hwb hl hTw) hk

end VG.Proof.Modes.Arm
