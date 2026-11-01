module

import VerifiedGarbage.Proof.Sm4.Arm.EcbAny
public import VerifiedGarbage.Impl.Sm4.Arm.Cbc
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Sm4.Arm.Ecb
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Argon2.Arm.Push
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
import VerifiedGarbage.Proof.Sm4.Arm.Lit
meta import VerifiedGarbage.Proof.Sm4.Arm.EcbAny
meta import VerifiedGarbage.Impl.Sm4.Arm.Cbc
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Sm4.Arm.Ecb
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Argon2.Arm.Push
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
meta import VerifiedGarbage.Proof.Sm4.Arm.Lit
public import VerifiedGarbage.Proof.Sm4.Contract

/-!
# SM4 ECB on ARMv7: the functions of one direction

`vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt` (`ecbCall`) set `decrypt` and
call `vg_sm4_ecb` (`ecbAny_framed`), in a frame saving `r4` and `lr`, with
`lr` kept in `r4` across the call: 8 bytes of stack above the callee's 1472.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4 (specDirArm)

/-- The ECB contracts with `stack = 1480`, as `sig_pre` evaluates them. -/
def ecbCallArm (d : Dir) : Contract Arm.isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let data : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat * 16⟩
    let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 1480, 1480⟩
    1480 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [data] ∧ sched.Disjoint data ∧ stk.Disjoint sched ∧
      stk.Disjoint data ∧ (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat * 16 ≤ 2 ^ 32
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (State.addr (s.gpr .r0))) (specDirArm d)
        (Spec.Sm4.blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

/-- The value `ecbCall d` sets `decrypt` to. -/
def dirFlag : Dir → Nat
  | .encrypt => 0
  | .decrypt => 1

theorem ecbCall_eq (d : Dir) :
    ecbCall d = .frame (.push [.r4, .lr])
      (.seq (.block [.mov .r4 (.reg .lr), .mov .r3 (.imm (BitVec.ofNat 32 (dirFlag d)))])
        (.seq (.call "vg_sm4_ecb" ecbAnyCode) (.block [.mov .lr (.reg .r4)])))
      (.pop .r4 (4 * [Reg.r4, .lr].length)) := by
  cases d <;> rfl

theorem dirOf_dirFlag (d : Dir) : dirOf (BitVec.ofNat 32 (dirFlag d)) = d := by
  cases d <;> rfl

theorem ecbAnyCode_stack : VG.Arm.FrameStack.armStack ecbAnyCode ≤ 1472 := by decide +kernel

/-- The state the call is made from, `σ`: after the push of `s₀`'s `r4` and
`lr`, `lr` kept in `r4` and `decrypt` set. -/
structure Entry (d : Dir) (s₀ σ : State) : Prop where
  gpr : ∀ r, r ≠ .r4 → r ≠ .r3 → σ.gpr r = s₀.gpr r
  r4 : σ.gpr .r4 = s₀.gpr .lr
  r3 : σ.gpr .r3 = BitVec.ofNat 32 (dirFlag d)
  sp : σ.sp = s₀.sp - BitVec.ofNat 32 8
  mem : σ.mem = (pushed [.r4, .lr] s₀).mem
  rd : σ.rd = s₀.rd
  wr : σ.wr = ⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 8⟩ :: s₀.wr

theorem movs_wp (d : Dir) (s₀ : State) :
    WP isa (.block [.mov .r4 (.reg .lr), .mov .r3 (.imm (BitVec.ofNat 32 (dirFlag d)))]) (pushed [.r4, .lr] s₀)
      (Entry d s₀) :=
  VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun σ₂ u₂ =>
    VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_imm (by cases d <;> decide)) fun σ₃ u₃ =>
      WP.block_nil
        { gpr := fun r h4 h3 => by rw [u₃.other r h3, u₂.other r h4, pushed_gpr]
          r4 := by rw [u₃.other _ (by decide), u₂.gpr, pushed_gpr]
          r3 := u₃.gpr
          sp := by rw [u₃.sp, u₂.sp, pushed_sp]; rfl
          mem := by rw [u₃.mem, u₂.mem]
          rd := by rw [u₃.rd, u₂.rd, pushed_rd]
          wr := by rw [u₃.wr, u₂.wr, pushed_wr]; rfl }

theorem entry_pre {d : Dir} {s₀ σ₃ : State} (hs : (ecbCallArm d).pre s₀) (e : Entry d s₀ σ₃) :
    (Proof.Sm4.ecbDirContract Arm.abi 1472).pre (σ₃.callEntry.withRegions s₀.rd s₀.wr) := by
  obtain ⟨hsp, hrd, hwr, dKD, sK, sD, fitK, fitD⟩ := hs
  obtain ⟨g₃, -, r3₃, sp₃, -, -, -⟩ := e
  have sp8 : (s₀.sp - BitVec.ofNat 32 8).toNat = s₀.sp.toNat - 8 := FrameStack.sub_toNat' (by omega_arith)
  sig_pre [Proof.Sm4.ecbDirContract, Proof.Sm4.ecbDirSig, Spec.Sm4.ecbSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]
  have e0 := g₃ .r0 (by decide) (by decide)
  have e1 := g₃ .r1 (by decide) (by decide)
  have e2 := g₃ .r2 (by decide) (by decide)
  have stS : Region.Sub (Argon2.Arm.stkR σ₃.sp 1472) ⟨State.addr s₀.sp - BitVec.ofNat 64 1480, 1480⟩ := by
    rw [sp₃]; exact Argon2.Arm.stkR_inner (by omega_arith) hsp
  rw [e0, e1, e2, r3₃]
  exact ⟨by rw [sp₃, sp8]; omega_arith, by have := σ₃.sp.isLt; omega_arith, hrd, hwr, dKD, sK.sub_left stS,
    sD.sub_left stS, fitK, fitD, by cases d <;> decide⟩

theorem entry_covers {d : Dir} {s₀ σ₃ : State} (e : Entry d s₀ σ₃) :
    Covers (s₀.rd ++ s₀.wr) (σ₃.rd ++ σ₃.wr) ∧ Covers s₀.wr σ₃.wr := by
  refine ⟨fun a n ⟨r, hr, hc⟩ => ⟨r, ?_, hc⟩, fun a n ⟨r, hr, hc⟩ => ⟨r, ?_, hc⟩⟩
  · rw [e.rd, e.wr]
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  · rw [e.wr]; exact List.mem_cons_of_mem _ hr

theorem ecbCall_correct (d : Dir) (s₀ : State) (hs : (ecbCallArm d).pre s₀) :
    ∃ t s', Exec isa (ecbCall d) s₀ t s' ∧ abiPreserved s₀ s' ∧ (ecbCallArm d).post s₀ s' := by
  obtain ⟨hsp, hrd, hwr, dKD, sK, sD, fitK, fitD⟩ := hs
  -- The frame's 8 bytes, below the stack the contract reserves.
  have frSub : Region.Sub (Argon2.Arm.stkR s₀.sp 8) ⟨State.addr s₀.sp - BitVec.ofNat 64 1480, 1480⟩ :=
    Argon2.Arm.stkR_sub (by omega_arith) hsp
  have hfr : Frame [Argon2.Arm.stkR s₀.sp 8] s₀.mem (pushed [.r4, .lr] s₀).mem :=
    Argon2.Arm.pushed_stk (rs := [.r4, .lr]) (by simp; omega_arith)
  have hsch : Spec.Sm4.scheduleAt (pushed [.r4, .lr] s₀).mem (State.addr (s₀.gpr .r0)) =
      Spec.Sm4.scheduleAt s₀.mem (State.addr (s₀.gpr .r0)) :=
    Proof.Sm4.scheduleAt_frame hfr fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact (sK.sub_left frSub).symm
  have hblk : Spec.Sm4.blocksAt (pushed [.r4, .lr] s₀).mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat =
      Spec.Sm4.blocksAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat := by
    have hfit : (s₀.gpr .r2).toNat * 16 ≤ 2 ^ 64 := by omega_arith
    exact Proof.Sm4.blocksAt_frame hfr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      simpa [State.addr] using (sD.sub_left frSub).symm) hfit
  rw [ecbCall_eq]
  have hn8 : 4 * [Reg.r4, .lr].length ≤ s₀.sp.toNat := by simp; omega_arith
  refine (WP.frame (rs := [.r4, .lr]) (r := .r4) (by decide) hn8 (by decide) ?_).elim
    fun t ⟨s', he, hq⟩ => ⟨t, s', he, hq⟩
  refine WP.seq (WP.mono (movs_wp d s₀) fun σ₃ e => ?_)
  have ⟨pre₃, cov₃⟩ := And.intro (entry_pre ⟨hsp, hrd, hwr, dKD, sK, sD, fitK, fitD⟩ e) (entry_covers e)
  obtain ⟨g₃, r4₃, r3₃, sp₃, mem₃, rd₃, wr₃⟩ := e
  have sp8 : (s₀.sp - BitVec.ofNat 32 8).toNat = s₀.sp.toNat - 8 := FrameStack.sub_toNat' (by omega_arith)
  refine WP.seq (FrameStack.WP.callF (k := Proof.Sm4.ecbDirContract Arm.abi 1472) ecbAny_framed.1
    (rd := s₀.rd) (wr := s₀.wr) ?_ ?_ ?_ ?_ ?_)
  · exact pre₃
  · exact cov₃.1
  · exact cov₃.2
  · rw [sp₃, sp8]; have := ecbAnyCode_stack; unfold ecbAnyCode at this; omega_arith
  · intro s' rd' wr' sp' fr' pres' post'
    refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun σ₄ u₄ => WP.block_nil ?_
    have r4' : s'.gpr .r4 = s₀.gpr .lr := by rw [pres' .r4 (by decide) (by decide), r4₃]
    have sp4 : σ₄.sp = s₀.sp - BitVec.ofNat 32 8 := by rw [u₄.sp, sp', sp₃]
    have hsp8 : 8 ≤ s₀.sp.toNat := by omega_arith
    -- The word `r4` was pushed to, in the frame below the stack the contract reserves.
    have hsub4 : Region.Sub ⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 4⟩
        ⟨State.addr s₀.sp - BitVec.ofNat 64 1480, 1480⟩ := by
      refine fun x hx => frSub x ?_
      rw [FrameStack.addr_sub' hsp8] at hx
      have := Offset.sub_base (State.addr s₀.sp - BitVec.ofNat 64 8) (d := 0) (n := 4) (k := 8) (by omega_arith)
      simp only [BitVec.add_zero] at this
      exact this x hx
    have hw4 : s'.mem.readW (State.addr (s₀.sp - BitVec.ofNat 32 8)) 32 = s₀.gpr .r4 := by
      rw [fr'.readW (r := ⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 4⟩) (Region.contains_self _ _) ?_
        (by decide), mem₃]
      · have := Argon2.Arm.storeWords_readW s₀.mem (s₀.sp - BitVec.ofNat 32 8) [s₀.gpr .r4, s₀.gpr .lr]
          (by rw [sp8]; have := s₀.sp.isLt; simp; omega_arith) (i := 0) (by simp)
        simpa [pushed] using this
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · rw [hwr, List.mem_singleton] at hr; subst hr; exact sD.sub_left hsub4
        · rw [List.mem_singleton] at hr; subst hr
          rw [sp₃]
          simp only [FrameStack.belowA]
          rw [FrameStack.addr_sub' (x := s₀.sp - BitVec.ofNat 32 8)
            (by rw [sp8]; have := ecbAnyCode_stack; unfold ecbAnyCode at this; omega_arith)]
          exact Offset.base_disjoint_below _ (by
            have := ecbAnyCode_stack; unfold ecbAnyCode at this; omega_arith)
    refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · by_cases h4 : r = .r4
      · subst h4
        show (σ₄.setReg .r4 (σ₄.mem.readW (State.addr σ₄.sp) 32)).gpr .r4 = _
        rw [RegUpd.gpr_setReg_self, sp4, u₄.mem]; exact hw4
      · rw [popped_gpr h4]
        by_cases hl : r = .lr
        · subst hl; rw [u₄.gpr, r4']
        · have h3 : r ≠ .r3 := by rintro rfl; revert hr; decide
          rw [u₄.other r hl, pres' r hr hl, g₃ r h4 h3]
    · rw [popped_sp, sp4]; exact BitVec.sub_add_cancel _ _
    · sig_post [Proof.Sm4.ecbDirContract, Proof.Sm4.ecbDirSig, Spec.Sm4.ecbSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val] at post'
      have hd' : Proof.Sm4.directionOf (BitVec.ofNat 32 (dirFlag d)).toNat = specDirArm d := by cases d <;> rfl
      rw [g₃ .r0 (by decide) (by decide), g₃ .r1 (by decide) (by decide), g₃ .r2 (by decide) (by decide),
        r3₃, hd', mem₃] at post'
      simp only [State.addr] at hsch hblk
      rw [hsch, hblk] at post'
      show Spec.Sm4.blocksAt σ₄.mem _ _ = _
      rw [u₄.mem]; exact post'

/-- Nothing public: the moves around the call leak nothing. -/
def τ0 : VG.Arm.Taint.T := { regs := .ofList [], flags := false }

theorem τ0_wf (s : State) : VG.Arm.Taint.Wf τ0 s :=
  ⟨fun h => (h rfl).elim, fun _ h => (List.not_mem_nil h).elim, fun h => (Nat.lt_irrefl _ h).elim,
    fun _ h => (List.not_mem_nil h).elim⟩

theorem τ0_agree (s₁ s₂ : State) : VG.Arm.Taint.Agree τ0 s₁ s₂ :=
  ⟨⟨fun r hr => by simp [τ0] at hr, fun h => nomatch h⟩, fun h => (h rfl).elim, τ0_wf s₁, τ0_wf s₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => (Nat.lt_irrefl _ h).elim, fun _ h => (Nat.not_lt_zero _ h).elim⟩

theorem entry_pub {d : Dir} {s₁ s₂ σ₁ σ₂ : State} (hp : (ecbCallArm d).pub s₁ s₂)
    (e₁ : Entry d s₁ σ₁) (e₂ : Entry d s₂ σ₂) {rd wr : List Region} :
    (Proof.Sm4.ecbDirContract Arm.abi 1472).pub (σ₁.callEntry.withRegions rd wr) (σ₂.callEntry.withRegions rd wr) := by
  sig_pub [Proof.Sm4.ecbDirContract, Proof.Sm4.ecbDirSig, Spec.Sm4.ecbSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]
  obtain ⟨psp, p0, p1, p2⟩ := hp
  exact ⟨by rw [e₁.sp, e₂.sp, psp], by rw [e₁.gpr _ (by decide) (by decide), e₂.gpr _ (by decide) (by decide), p0],
    by rw [e₁.gpr _ (by decide) (by decide), e₂.gpr _ (by decide) (by decide), p1],
    by rw [e₁.gpr _ (by decide) (by decide), e₂.gpr _ (by decide) (by decide), p2], by rw [e₁.r3, e₂.r3]⟩

theorem movs_rel (d : Dir) {P : State → State → Prop} :
    RelCT isa P (.block [.mov .r4 (.reg .lr), .mov .r3 (.imm (BitVec.ofNat 32 (dirFlag d)))]) fun _ _ => True := by
  cases d <;> exact RelCT.taint (A := VG.Arm.taint) τ0 (fun _ _ _ => τ0_agree _ _) (by taint_decide)

theorem ecbCall_ct (d : Dir) :
    ConstantTime isa (ecbCallArm d).pre (ecbCallArm d).pub (ecbCall d) := by
  rw [ecbCall_eq]
  refine RelCT.constantTime (RelCT.frame (fun s₁ s₂ h => h.2.2.1) ?_)
  refine RelCT.mono (P := fun a b => ∃ p : State × State, ((ecbCallArm d).pre p.1 ∧ (ecbCallArm d).pre p.2 ∧
      (ecbCallArm d).pub p.1 p.2) ∧ a = pushed [.r4, .lr] p.1 ∧ b = pushed [.r4, .lr] p.2) ?_
    (fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ⟨(s₁, s₂), hp, Argon2.Arm.push_eq (by decide) pa,
      Argon2.Arm.push_eq (by decide) pb⟩) (fun _ _ h => h)
  refine RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_
  let H := (ecbCallArm d).pre s₁ ∧ (ecbCallArm d).pre s₂ ∧ (ecbCallArm d).pub s₁ s₂
  refine RelCT.seq (RelCT.wp (F₁ := fun σ => H ∧ Entry d s₁ σ) (F₂ := Entry d s₂)
    (movs_rel d) fun a b ⟨h, ha, hb⟩ =>
      ⟨ha ▸ WP.mono (movs_wp d s₁) fun _ e => ⟨h, e⟩, hb ▸ movs_wp d s₂⟩) ?_
  refine RelCT.seq (RelCT.call ecbAny_framed.1 ecbAny_framed.2.1 s₁.rd s₁.wr
    fun σ₁ σ₂ ⟨_, ⟨⟨h₁, h₂, hp⟩, e₁⟩, e₂⟩ => ?_)
    (RelCT.taint (A := VG.Arm.taint) τ0 (fun _ _ _ => τ0_agree _ _) (by taint_decide))
  have hrd : s₂.rd = s₁.rd := by rw [h₁.2.1, h₂.2.1, hp.2.1]
  have hwr : s₂.wr = s₁.wr := by rw [h₁.2.2.1, h₂.2.2.1, hp.2.2.1, hp.2.2.2]
  have p₂ := entry_pre h₂ e₂
  rw [hrd, hwr] at p₂
  have c₂ := entry_covers e₂
  rw [hrd, hwr] at c₂
  exact ⟨entry_pre h₁ e₁, p₂, entry_pub hp e₁ e₂, (entry_covers e₁).1, (entry_covers e₁).2, c₂.1, c₂.2⟩

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000`, one block at `0x3000`. -/
def ecbCallSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r2 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩]

/-- `vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt`: 1480 bytes of stack. -/
theorem ecbCall_verified (d : Dir) :
    Verified Arm.target (ecbCall d) (Spec.Sm4.ecbContract Arm.abi (specDirArm d) 1480) :=
  Verified.of_correct (ecbCall_correct d) (ecbCall_ct d) (by
    sig_implies [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, ecbCallArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, State.addr] [ecbCallSat] using ecbCallSat)

end VG.Proof.Sm4.Arm
