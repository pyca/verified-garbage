module

public import VerifiedGarbage.Proof.Modes.Arm.Core
public import VerifiedGarbage.Impl.Modes.Arm.Wrap
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Argon2.Arm.Push
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Modes.Arm.Core
meta import VerifiedGarbage.Impl.Modes.Arm.Wrap
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Argon2.Arm.Push
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# A block cipher's ECB function as a call of its core, on ARMv7

`c.wrap` (`Impl/Modes/Arm/Wrap.lean`) meets what the core `c` does
(`CoreSpec`), with 8 bytes more of stack (`wrapContract`): the frame's push
of `r4` and `lr`, below the stack pointer and so apart from the schedule and
the blocks, which the core reads and writes as they were on entry.
`wrap_verified` gives it any contract that this one implies, a cipher's ECB
contract with 8 bytes more of stack than its core's.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Arm.FrameStack VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)

section

variable {c : Core} (S : CoreSpec c)

/-- What `c.wrap` meets: the core's precondition with 8 bytes more of stack,
the blocks their images under the cipher, and the arguments and the stack
pointer public. -/
def wrapContract : Contract isa where
  pre s := EcbPre c S.keyLen (S.stack + 8) S.rok s
  post s s' :=
    blocksOf c.bs s'.mem (State.addr (s.gpr c.dReg)) (s.gpr c.nReg).toNat =
      (blocksOf c.bs s.mem (State.addr (s.gpr c.dReg)) (s.gpr c.nReg).toNat).map
        (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1))
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ (c.r3Pub = true → s₁.gpr .r3 = s₂.gpr .r3)

end

/-- The state the call is made from, `σ`: after the push of `s₀`'s `r4` and
`lr`, with `lr` kept in `r4`. -/
structure WrapEntry (s₀ σ : State) : Prop where
  gpr : ∀ r, r ≠ .r4 → σ.gpr r = s₀.gpr r
  r4 : σ.gpr .r4 = s₀.gpr .lr
  sp : σ.sp = s₀.sp - BitVec.ofNat 32 8
  mem : σ.mem = (pushed [.r4, .lr] s₀).mem
  rd : σ.rd = s₀.rd
  wr : σ.wr = ⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 8⟩ :: s₀.wr

theorem wrapMov_wp (s₀ : State) :
    WP isa (.block [.mov .r4 (.reg .lr)]) (pushed [.r4, .lr] s₀) (WrapEntry s₀) :=
  VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun σ u =>
    WP.block_nil
      { gpr := fun r h => by rw [u.other r h, pushed_gpr]
        r4 := by rw [u.gpr, pushed_gpr]
        sp := by rw [u.sp]; rfl
        mem := u.mem
        rd := by rw [u.rd, pushed_rd]
        wr := by rw [u.wr, pushed_wr]; rfl }

theorem _root_.VG.Impl.Modes.Arm.Core.dReg_wrap (c : Core) : c.dReg ≠ .r4 ∧ c.dReg ∉ linkRegs := by
  unfold Core.dReg; split <;> decide

theorem _root_.VG.Impl.Modes.Arm.Core.nReg_wrap (c : Core) : c.nReg ≠ .r4 ∧ c.nReg ∉ linkRegs := by
  unfold Core.nReg; split <;> decide

/-- The registers but `r4` and the link registers on entry to the core. -/
theorem WrapEntry.entry_gpr {s₀ σ : State} (e : WrapEntry s₀ σ) (rd wr : List Region) {r : Reg}
    (h4 : r ≠ .r4) (hl : r ∉ linkRegs) : (σ.callEntry.withRegions rd wr).gpr r = s₀.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr σ hl, e.gpr r h4]

section

variable {c : Core} {S : CoreSpec c}

/-- The core's stack, below the frame, is among the stack the wrapper's
precondition reserves. -/
theorem wrap_stackSub {s₀ σ : State} (hs : (wrapContract S).pre s₀) (e : WrapEntry s₀ σ) :
    Region.Sub ⟨State.addr σ.sp - BitVec.ofNat 64 S.stack, S.stack⟩
      ⟨State.addr s₀.sp - BitVec.ofNat 64 (S.stack + 8), S.stack + 8⟩ := by
  rw [e.sp]; exact Argon2.Arm.stkR_inner (by omega_arith) hs.stk

theorem wrap_ecbPre {s₀ σ : State} (hs : (wrapContract S).pre s₀) (e : WrapEntry s₀ σ) :
    EcbPre c S.keyLen S.stack S.rok (σ.callEntry.withRegions s₀.rd s₀.wr) := by
  have hst := hs.stk
  have sp8 : (s₀.sp - BitVec.ofNat 32 8).toNat = s₀.sp.toNat - 8 := sub_toNat' (by omega_arith)
  have sub := wrap_stackSub hs e
  have hd := c.dReg_wrap
  have hn := c.nReg_wrap
  have g0 := e.entry_gpr s₀.rd s₀.wr (r := .r0) (by decide) (by decide)
  have g1 := e.entry_gpr s₀.rd s₀.wr (r := .r1) (by decide) (by decide)
  have g3 := e.entry_gpr s₀.rd s₀.wr (r := .r3) (by decide) (by decide)
  have gd := e.entry_gpr s₀.rd s₀.wr hd.1 hd.2
  have gn := e.entry_gpr s₀.rd s₀.wr hn.1 hn.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun hr => ?_, fun k hk => ?_⟩ <;>
    simp only [g0, g1, g3, gd, gn, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp]
  · rw [e.sp, sp8]; omega_arith
  · exact hs.rd
  · exact hs.wr
  · exact hs.kd
  · exact hs.bk.sub_left sub
  · exact hs.bd.sub_left sub
  · exact hs.fK
  · exact hs.fD
  · exact hs.rr hr
  · exact hs.a3 k hk

theorem wrap_covers {s₀ σ : State} (e : WrapEntry s₀ σ) :
    Covers (s₀.rd ++ s₀.wr) (σ.rd ++ σ.wr) ∧ Covers s₀.wr σ.wr := by
  refine ⟨fun a n ⟨r, hr, hc⟩ => ⟨r, ?_, hc⟩, fun a n ⟨r, hr, hc⟩ => ⟨r, ?_, hc⟩⟩
  · rw [e.rd, e.wr]
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  · rw [e.wr]; exact List.mem_cons_of_mem _ hr

/-- Blocks in memory that agrees on their bytes. -/
theorem wrap_blocks {m m' : Mem} {D : Addr} {L n : Nat}
    (h : ∀ i < n * L, m' (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i)) :
    blocksOf L m' D n = blocksOf L m D n :=
  List.map_congr_left fun j hj => List.map_congr_left fun i hi => by
    have hj' := VG.Proof.Modes.idx_lt (L := L) (List.mem_range.mp hj)
    have hi' := List.mem_range.mp hi
    rw [VG.Offset.add_add]
    exact h _ (by rw [Nat.mul_comm n L]; omega_arith)

end

variable {c : Core} (S : CoreSpec c)

theorem wrap_correct (hs0 : c.stackScratch = 0) (s₀ : State) (hs : (wrapContract S).pre s₀) :
    ∃ t s', Exec isa c.wrap s₀ t s' ∧ abiPreserved s₀ s' ∧ (wrapContract S).post s₀ s' := by
  have hst := hs.stk
  have hsp : 8 ≤ s₀.sp.toNat := by omega_arith
  have sp8 : (s₀.sp - BitVec.ofNat 32 8).toNat = s₀.sp.toNat - 8 := sub_toNat' hsp
  have hd := c.dReg_wrap
  have hn := c.nReg_wrap
  -- The frame's 8 bytes, among the stack the contract reserves.
  have frSub : Region.Sub (Argon2.Arm.stkR s₀.sp 8)
      ⟨State.addr s₀.sp - BitVec.ofNat 64 (S.stack + 8), S.stack + 8⟩ :=
    Argon2.Arm.stkR_sub (by omega_arith) hst
  have hfr : Frame [Argon2.Arm.stkR s₀.sp 8] s₀.mem (pushed [.r4, .lr] s₀).mem :=
    Argon2.Arm.pushed_stk (rs := [.r4, .lr]) (by simp; omega_arith)
  have hK : ∀ i < S.keyLen, (pushed [.r4, .lr] s₀).mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 i) =
      s₀.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 i) := fun i hi =>
    hfr.bytes (R := ⟨State.addr (s₀.gpr .r0), S.keyLen⟩) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact (hs.bk.sub_left frSub).symm)
      (by have := hs.fK; show S.keyLen ≤ 2 ^ 64; omega_arith) hi
  have dD : ∀ r ∈ [Argon2.Arm.stkR s₀.sp 8],
      Region.Disjoint ⟨State.addr (s₀.gpr c.dReg), (s₀.gpr c.nReg).toNat * c.bs⟩ r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact (hs.bd.sub_left frSub).symm
  have fitD : (s₀.gpr c.nReg).toNat * c.bs ≤ 2 ^ 64 := by have := hs.fD; omega_arith
  have hblk : blocksOf c.bs (pushed [.r4, .lr] s₀).mem (State.addr (s₀.gpr c.dReg)) (s₀.gpr c.nReg).toNat =
      blocksOf c.bs s₀.mem (State.addr (s₀.gpr c.dReg)) (s₀.gpr c.nReg).toNat :=
    wrap_blocks fun i hi => hfr.bytes (R := ⟨_, _⟩) dD fitD hi
  have hcph : S.ciphAt (pushed [.r4, .lr] s₀).mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1) =
      S.ciphAt s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1) := S.ciphAt_congr hK
  unfold Core.wrap
  have hn8 : 4 * [Reg.r4, .lr].length ≤ s₀.sp.toNat := by simp; omega_arith
  refine (WP.frame (rs := [.r4, .lr]) (r := .r4) (by decide) hn8 (by decide) ?_).elim
    fun t ⟨s', he, hq⟩ => ⟨t, s', he, hq⟩
  refine WP.seq (WP.mono (wrapMov_wp s₀) fun σ₃ e => ?_)
  have pre₃ := wrap_ecbPre hs e
  have cov₃ := wrap_covers e
  have stS : armStack c.code ≤ σ₃.sp.toNat := by rw [e.sp, sp8]; have := S.depth; omega_arith
  refine WP.seq (FrameStack.WP.callF (k := S.contract) S.correct (rd := s₀.rd) (wr := s₀.wr)
    (S.pre_of hs0 _ pre₃) cov₃.1 cov₃.2 stS ?_)
  intro s' rd' wr' sp' fr' pres' post'
  refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun σ₄ u₄ => WP.block_nil ?_
  have r4' : s'.gpr .r4 = s₀.gpr .lr := by rw [pres' .r4 (by decide) (by decide), e.r4]
  have sp4 : σ₄.sp = s₀.sp - BitVec.ofNat 32 8 := by rw [u₄.sp, sp', e.sp]
  -- The word `r4` was pushed to, in the frame, apart from the blocks and above the core's stack.
  have hsub4 : Region.Sub ⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 4⟩
      ⟨State.addr s₀.sp - BitVec.ofNat 64 (S.stack + 8), S.stack + 8⟩ := by
    refine fun x hx => frSub x ?_
    rw [FrameStack.addr_sub' hsp] at hx
    have := Offset.sub_base (State.addr s₀.sp - BitVec.ofNat 64 8) (d := 0) (n := 4) (k := 8) (by omega_arith)
    simp only [BitVec.add_zero] at this
    exact this x hx
  have hw4 : s'.mem.readW (State.addr (s₀.sp - BitVec.ofNat 32 8)) 32 = s₀.gpr .r4 := by
    rw [fr'.readW (r := ⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 4⟩) (Region.contains_self _ _) ?_
      (by decide), e.mem]
    · have := Argon2.Arm.storeWords_readW s₀.mem (s₀.sp - BitVec.ofNat 32 8) [s₀.gpr .r4, s₀.gpr .lr]
        (by rw [sp8]; have := s₀.sp.isLt; simp; omega_arith) (i := 0) (by simp)
      simpa [pushed] using this
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · rw [hs.wr, List.mem_singleton] at hr; subst hr; exact hs.bd.sub_left hsub4
      · rw [List.mem_singleton] at hr; subst hr
        rw [e.sp]
        simp only [FrameStack.belowA]
        have := S.depth
        rw [FrameStack.addr_sub' (x := s₀.sp - BitVec.ofNat 32 8) (by rw [sp8]; omega_arith)]
        exact Offset.base_disjoint_below _ (by omega_arith)
  intro ml ul hfl
  have hfl' : Frame [Argon2.Arm.stkR s₀.sp 8] σ₄.mem ml := by
    rw [show 4 * [Reg.r4, Reg.lr].length = 8 from rfl, FrameStack.addr_sub' hsp] at hfl; exact hfl
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩ <;> dsimp only
  · by_cases h4 : r = .r4
    · subst h4
      show (σ₄.setReg .r4 (σ₄.mem.readW (State.addr σ₄.sp) 32)).gpr .r4 = _
      rw [RegUpd.gpr_setReg_self, sp4, u₄.mem]; exact hw4
    · rw [popped_gpr h4]
      by_cases hl : r = .lr
      · subst hl; rw [u₄.gpr, r4']
      · rw [u₄.other r hl, pres' r hr hl, e.gpr r h4]
  · rw [popped_sp, sp4]; exact BitVec.sub_add_cancel _ _
  · have e' := S.post_of hs0 _ _ pre₃ post'
    have gd := e.entry_gpr s₀.rd s₀.wr hd.1 hd.2
    have gn := e.entry_gpr s₀.rd s₀.wr hn.1 hn.2
    have g0 := e.entry_gpr s₀.rd s₀.wr (r := .r0) (by decide) (by decide)
    have g1 := e.entry_gpr s₀.rd s₀.wr (r := .r1) (by decide) (by decide)
    simp only [gd, gn, g0, g1, State.withRegions_mem, State.callEntry_mem, e.mem, hblk, hcph] at e'
    show blocksOf c.bs ml _ _ = _
    rw [wrap_blocks fun i hi => hfl'.bytes (R := ⟨_, _⟩) dD fitD hi, u₄.mem]
    exact e'

/-- Nothing public: the moves around the call leak nothing. -/
def wrapT : VG.Arm.Taint.T := { regs := .ofList [], flags := false }

theorem wrapT_wf (s : State) : VG.Arm.Taint.Wf wrapT s :=
  ⟨fun h => (h rfl).elim, fun _ h => (List.not_mem_nil h).elim, fun h => (Nat.lt_irrefl _ h).elim,
    fun _ h => (List.not_mem_nil h).elim⟩

theorem wrapT_agree (s₁ s₂ : State) : VG.Arm.Taint.Agree wrapT s₁ s₂ :=
  ⟨⟨fun r hr => by simp [wrapT] at hr, fun h => nomatch h⟩, fun h => (h rfl).elim, wrapT_wf s₁, wrapT_wf s₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => (Nat.lt_irrefl _ h).elim, fun _ h => (Nat.not_lt_zero _ h).elim⟩

theorem wrapMov_rel {P : State → State → Prop} :
    RelCT isa P (.block [.mov .r4 (.reg .lr)]) fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) wrapT (fun _ _ _ => wrapT_agree _ _) (by taint_decide)

theorem wrapRet_rel {P : State → State → Prop} :
    RelCT isa P (.block [.mov .lr (.reg .r4)]) fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) wrapT (fun _ _ _ => wrapT_agree _ _) (by taint_decide)

theorem wrap_pub (hs0 : c.stackScratch = 0) {s₁ s₂ σ₁ σ₂ : State} (hp : (wrapContract S).pub s₁ s₂)
    (e₁ : WrapEntry s₁ σ₁) (e₂ : WrapEntry s₂ σ₂) {rd wr : List Region} :
    S.contract.pub (σ₁.callEntry.withRegions rd wr) (σ₂.callEntry.withRegions rd wr) := by
  obtain ⟨psp, p0, p1, p2, p3⟩ := hp
  refine S.pub_of hs0 _ _ ?_ ?_ ?_ ?_ fun h => ?_
  · simp only [State.withRegions_sp, State.callEntry_sp]; rw [e₁.sp, e₂.sp, psp]
  · rw [e₁.entry_gpr _ _ (by decide) (by decide), e₂.entry_gpr _ _ (by decide) (by decide), p0]
  · rw [e₁.entry_gpr _ _ (by decide) (by decide), e₂.entry_gpr _ _ (by decide) (by decide), p1]
  · rw [e₁.entry_gpr _ _ (by decide) (by decide), e₂.entry_gpr _ _ (by decide) (by decide), p2]
  · rw [e₁.entry_gpr _ _ (by decide) (by decide), e₂.entry_gpr _ _ (by decide) (by decide), p3 h]

theorem wrap_ct (hs0 : c.stackScratch = 0) :
    ConstantTime isa (wrapContract S).pre (wrapContract S).pub c.wrap := by
  unfold Core.wrap
  refine RelCT.constantTime (RelCT.frame (fun s₁ s₂ h => h.2.2.1) ?_)
  refine RelCT.mono (P := fun a b => ∃ p : State × State, ((wrapContract S).pre p.1 ∧ (wrapContract S).pre p.2 ∧
      (wrapContract S).pub p.1 p.2) ∧ a = pushed [.r4, .lr] p.1 ∧ b = pushed [.r4, .lr] p.2) ?_
    (fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ⟨(s₁, s₂), hp, Argon2.Arm.push_eq (by decide) pa,
      Argon2.Arm.push_eq (by decide) pb⟩) (fun _ _ h => h)
  refine RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_
  let H := (wrapContract S).pre s₁ ∧ (wrapContract S).pre s₂ ∧ (wrapContract S).pub s₁ s₂
  refine RelCT.seq (RelCT.wp (F₁ := fun σ => H ∧ WrapEntry s₁ σ) (F₂ := WrapEntry s₂)
    wrapMov_rel fun a b ⟨h, ha, hb⟩ =>
      ⟨ha ▸ WP.mono (wrapMov_wp s₁) fun _ e => ⟨h, e⟩, hb ▸ wrapMov_wp s₂⟩) ?_
  refine RelCT.seq (RelCT.call S.correct S.ct s₁.rd s₁.wr
    fun σ₁ σ₂ ⟨_, ⟨⟨h₁, h₂, hp⟩, e₁⟩, e₂⟩ => ?_) wrapRet_rel
  have hrd : s₂.rd = s₁.rd := by rw [h₂.rd, h₁.rd, hp.2.1]
  have hdn : s₂.gpr c.dReg = s₁.gpr c.dReg ∧ s₂.gpr c.nReg = s₁.gpr c.nReg := by
    obtain ⟨-, -, p1, p2, p3⟩ := hp
    unfold Core.dReg Core.nReg
    cases hr : c.rounds
    · exact ⟨p1.symm, p2.symm⟩
    · exact ⟨p2.symm, (p3 (by simp [Core.r3Pub, hr])).symm⟩
  have hwr : s₂.wr = s₁.wr := by rw [h₂.wr, h₁.wr, hdn.1, hdn.2]
  have p₂ := wrap_ecbPre h₂ e₂
  rw [hrd, hwr] at p₂
  have c₂ := wrap_covers e₂
  rw [hrd, hwr] at c₂
  exact ⟨S.pre_of hs0 _ (wrap_ecbPre h₁ e₁), S.pre_of hs0 _ p₂, wrap_pub S hs0 hp e₁ e₂, (wrap_covers e₁).1,
    (wrap_covers e₁).2, c₂.1, c₂.2⟩

/-- `c.wrap` meets any contract that `wrapContract S` implies. -/
theorem wrap_verified (S : CoreSpec c) (hs0 : c.stackScratch = 0) {k : Contract isa} (hk : (wrapContract S).Implies k) :
    Verified Arm.target c.wrap k :=
  Verified.of_correct (wrap_correct S hs0) (wrap_ct S hs0) hk

end VG.Proof.Modes.Arm
