import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Prune
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Calls
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLocal
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit

/-!
# Ed448 signing with a cached public key on x86-64: the scalar calls

Between the frame's push and pop (`Ctx`): the calls of
`vg_ed448_scalar_reduce` into the frame (`red_ok`), of
`vg_ed448_scalar_base` from `r` into the first half of `out` (`base_ok`, for
any proof that it meets its contract, `BaseOk`: only the registration file
imports that proof, and the group theory it imports), and of
`vg_ed448_scalar_mul_add` into the second half (`mulAdd_ok`); and the
clearing of `s` and `r` (`wipe_ok`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached
open VG.Impl.Ed448.X86_64.Verify (stk Arg callA fH fScr)
open VG.Proof.Ed448.X86_64.Verify (Within within_off within_base within_self add_add ea_stk gpr_ce rsp_ce sp_sub8
  x0 setArgs_ok argRegs_cs argsIn3 argsIn5 reduce_nosp reduce_depth)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.Sha3 (bytesAt)

theorem base_nosp : NoSp Impl.Ed448.X86_64.scalarBase := by
  have : ((instrs Impl.Ed448.X86_64.scalarBase).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem base_depth : Impl.Ed448.X86_64.scalarBase.depth ≤ 1 := by lit_decide

theorem mulAdd_nosp : NoSp Impl.Ed448.X86_64.scalarMulAdd := by
  have : ((instrs Impl.Ed448.X86_64.scalarMulAdd).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem mulAdd_depth : Impl.Ed448.X86_64.scalarMulAdd.depth ≤ 1 := by lit_decide

/-- `vg_ed448_scalar_base` meets the contract its proof is written against, and the ABI. -/
abbrev BaseOk : Prop := ∀ s, Proof.Ed448.X86_64.scalarBaseLocal.clear.pre s →
  ∃ t s', Exec isa Impl.Ed448.X86_64.scalarBase s t s' ∧ abiPreserved s s' ∧
    Proof.Ed448.X86_64.scalarBaseLocal.post s s'

/-- `vg_ed448_scalar_base` is constant time for that contract. -/
abbrev BaseCT : Prop := ConstantTime isa Proof.Ed448.X86_64.scalarBaseLocal.clear.pre
  Proof.Ed448.X86_64.scalarBaseLocal.pub Impl.Ed448.X86_64.scalarBase

theorem ed_bytesAt : Spec.Ed448.bytesAt = bytesAt := rfl

section
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem spd (L : Lay) (d : Nat) : L.SP + BitVec.ofNat 64 d = L.B + BitVec.ofNat 64 (16 + d) := add_add _ _ _

theorem sp_ce {t : State} (hc : Ctx L g mx m₀ t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rsp = L.B + BitVec.ofNat 64 8 := by
  rw [rsp_ce, hc.rsp, sp_sub8]

/-- A piece of the frame, apart from `scratch`. -/
theorem fr_x (hL : L.Ok) {d n : Nat} (h : d + n ≤ 448) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ L.SCR := by
  have := hL.stk_x (d := 16 + d) (n := n) (e := 0) (k := 8192) (by omega) (by omega)
  rw [spd]; simpa only [x0] using this

/-- The return address of a call from the frame, apart from a piece of the frame. -/
theorem ret_fr {d n : Nat} (h : d + n ≤ 448) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ ⟨L.SP + BitVec.ofNat 64 d, n⟩ := by
  rw [spd]; exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem ret_x (hL : L.Ok) : Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ L.SCR := by
  have := hL.stk_x (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega)
  simpa only [x0] using this

theorem ret_r (hL : L.Ok) {r : Region} (hr : L.STK.Disjoint r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ r :=
  hL.stk_r hr (by omega)

/-- The halves of `out`. -/
theorem o1_sub : Region.Sub ⟨L.out, 57⟩ L.OUT := (within_base _ (by omega)).sub
theorem o2_sub : Region.Sub ⟨L.out + BitVec.ofNat 64 57, 57⟩ L.OUT := (within_off _ (by omega)).sub

/-- A piece of the frame within its data. -/
theorem w_dat₂ {d n : Nat} (h₁ : 256 ≤ d) (h₂ : d + n ≤ 448) : WOk L ⟨L.SP + BitVec.ofNat 64 d, n⟩ :=
  .inr (.inr (.inr ⟨d - 256, show L.SP + BitVec.ofNat 64 d = L.SP + BitVec.ofNat 64 256 + BitVec.ofNat 64 (d - 256)
    by rw [add_add L.SP 256 (d - 256), Nat.add_sub_cancel' h₁], by show d - 256 + n ≤ 192; omega⟩))

theorem in_fr {d n : Nat} (h : d + n ≤ 448) :
    ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.SP + BitVec.ofNat 64 d, n⟩ R :=
  ⟨L.FR, by simp, within_off _ h⟩

/-! ## `vg_ed448_scalar_reduce` -/

theorem red_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {d : Nat} (h₁ : 256 ≤ d) (h₂ : d + 57 ≤ 448)
    (h₃ : d < 2 ^ 31) :
    WP isa (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce [.sp d, .sp fH, .slot fScr]) t
      fun t' => Ctx L g mx m₀ t' ∧ Frame [⟨L.SP + BitVec.ofNat 64 d, 57⟩, L.SCR, ⟨L.B, 16⟩] t.mem t'.mem ∧
        Spec.Ed448.bytesAt t'.mem (L.SP + BitVec.ofNat 64 d) 57 =
          Spec.Ed448.scalarReduce (bytesAt t.mem L.H 114) := by
  refine WP.seq (WP.mono (setArgs_ok _ (by simp [Arg.ok, fScr, fH]; omega) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  rw [hc.sp] at e1 e2
  rw [hc.slot, hc.pScr] at e3
  change t1.gpr .rsi = L.H at e2
  have g1 := (gpr_ce t1 [⟨L.H, 114⟩] [⟨L.SP + BitVec.ofNat 64 d, 57⟩, L.SCR] (by decide : Reg.rdi ≠ .rsp)).trans e1
  have g2 := (gpr_ce t1 [⟨L.H, 114⟩] [⟨L.SP + BitVec.ofNat 64 d, 57⟩, L.SCR] (by decide : Reg.rsi ≠ .rsp)).trans e2
  have g3 := (gpr_ce t1 [⟨L.H, 114⟩] [⟨L.SP + BitVec.ofNat 64 d, 57⟩, L.SCR] (by decide : Reg.rdx ≠ .rsp)).trans e3
  have hpre : Proof.Ed448.X86_64.scalarReduceLocal.pre
      (t1.callEntry.withRegions [⟨L.H, 114⟩] [⟨L.SP + BitVec.ofNat 64 d, 57⟩, L.SCR]) := by
    simp only [Proof.Ed448.X86_64.scalarReduceLocal, g1, g2, g3, sp_ce hc1, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, fr_x hL (d := 16) (by omega), ret_fr h₂, ret_x hL, fr_x hL h₂, hL.nScr⟩
  refine call_ok hL Proof.Ed448.X86_64.scalarReduce_ok reduce_nosp reduce_depth hc1 hpre
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact in_fr (d := 16) (by omega))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [w_dat₂ h₁ h₂, .inl (within_self _)])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hc', by rw [← hm]; simpa using hf, ?_⟩
  simp only [Proof.Ed448.X86_64.scalarReduceLocal, g1, g2, State.withRegions_mem, hm₂] at hpost
  rw [hpost]
  refine congrArg _ ?_
  change bytesAt t1.callEntry.mem L.H 114 = bytesAt t.mem L.H 114
  rw [hc1.ce_bytesAt (ret_fr (d := 16) (by omega)) (by decide), hm]

/-! ## `vg_ed448_scalar_base` -/

/-- The callee's precondition, its buffers apart from the 8 bytes below its `rsp`, the
frame's lowest. -/
theorem base_cpre (hL : L.Ok) {u : State} (g1 : u.gpr .rdi = L.out) (g2 : u.gpr .rsi = L.R)
    (g3 : u.gpr .rdx = L.scr) (g4 : u.gpr .rsp = L.B + BitVec.ofNat 64 8) (hrd : u.rd = [⟨L.R, 57⟩])
    (hwr : u.wr = [⟨L.out, 57⟩, L.SCR]) : Proof.Ed448.X86_64.scalarBaseLocal.clear.pre u := by
  refine ⟨?_, ?_⟩
  · simp only [Proof.Ed448.X86_64.scalarBaseLocal, g1, g2, g3, g4, hrd, hwr]
    exact ⟨trivial, trivial, fr_x hL (d := 384) (by omega), ret_r hL (hL.kOut.sub_right o1_sub), ret_x hL,
      (hL.xOut.sub_right o1_sub).symm, hL.nScr⟩
  · rw [g4, Proof.Ed448.X86_64.hole_add8]
    intro r hr
    simp only [hrd, hwr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [show L.R = L.B + BitVec.ofNat 64 400 from spd L 384]
      exact Offset.disjoint_base _ (by omega) (by omega)
    · simpa using ((hL.stk_r hL.kOut (d := 0) (n := 8) (by omega)).sub_right o1_sub).symm
    · simpa using (hL.stk_r hL.kScr (d := 0) (n := 8) (by omega)).symm

theorem base_ok (hb : BaseOk) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (callA "vg_ed448_scalar_base" Impl.Ed448.X86_64.scalarBase [.slot fOut, .sp fR, .slot fScr]) t
      fun t' => Ctx L g mx m₀ t' ∧ Frame [⟨L.out, 57⟩, L.SCR, ⟨L.B, 16⟩] t.mem t'.mem ∧
        Spec.Ed448.bytesAt t'.mem L.out 57 = Spec.Ed448.scalarBase (Spec.Ed448.bytesAt t.mem L.R 57) := by
  refine WP.seq (WP.mono (setArgs_ok _ (by decide) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  rw [hc.slot, hc.pOut] at e1
  rw [hc.sp] at e2
  rw [hc.slot, hc.pScr] at e3
  change t1.gpr .rsi = L.R at e2
  have g1 := (gpr_ce t1 [⟨L.R, 57⟩] [⟨L.out, 57⟩, L.SCR] (by decide : Reg.rdi ≠ .rsp)).trans e1
  have g2 := (gpr_ce t1 [⟨L.R, 57⟩] [⟨L.out, 57⟩, L.SCR] (by decide : Reg.rsi ≠ .rsp)).trans e2
  have g3 := (gpr_ce t1 [⟨L.R, 57⟩] [⟨L.out, 57⟩, L.SCR] (by decide : Reg.rdx ≠ .rsp)).trans e3
  have hpre := base_cpre hL (u := t1.callEntry.withRegions [⟨L.R, 57⟩] [⟨L.out, 57⟩, L.SCR]) g1 g2 g3
    (sp_ce hc1 _ _) rfl rfl
  refine call_ok hL hb base_nosp base_depth hc1 hpre
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact in_fr (d := 384) (by omega))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inr (.inl (within_base _ (by omega))), .inl (within_self _)])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hc', by rw [← hm]; simpa using hf, ?_⟩
  simp only [Contract.clear, Proof.Ed448.X86_64.scalarBaseLocal, g1, g2, State.withRegions_mem, hm₂] at hpost
  rw [hpost]
  refine congrArg _ ?_
  rw [ed_bytesAt, hc1.ce_bytesAt (ret_fr (d := 384) (by omega)) (by decide), hm]

/-! ## `vg_ed448_scalar_mul_add` -/

theorem mulAdd_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (callA "vg_ed448_scalar_mul_add" Impl.Ed448.X86_64.scalarMulAdd
        [.slotOff fOut 57, .sp fR, .sp fK, .sp fS, .slot fScr]) t
      fun t' => Ctx L g mx m₀ t' ∧
        Frame [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR, ⟨L.B, 16⟩] t.mem t'.mem ∧
        Spec.Ed448.bytesAt t'.mem (L.out + BitVec.ofNat 64 57) 57 = Spec.Ed448.scalarMulAdd
          (Spec.Ed448.bytesAt t.mem L.R 57) (Spec.Ed448.bytesAt t.mem L.K 57) (Spec.Ed448.bytesAt t.mem L.S 57) := by
  refine WP.seq (WP.mono (setArgs_ok _ (by decide) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  simp only [Arg.val, hc.rsp, hc.pOut, hc.pScr] at e1 e5
  rw [hc.sp] at e2 e3 e4
  change t1.gpr .rsi = L.R at e2
  change t1.gpr .rdx = L.K at e3
  change t1.gpr .rcx = L.S at e4
  have g1 := (gpr_ce t1 [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩] [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR] (by decide : Reg.rdi ≠ .rsp)).trans e1
  have g2 := (gpr_ce t1 [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩] [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR] (by decide : Reg.rsi ≠ .rsp)).trans e2
  have g3 := (gpr_ce t1 [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩] [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR] (by decide : Reg.rdx ≠ .rsp)).trans e3
  have g4 := (gpr_ce t1 [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩] [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR] (by decide : Reg.rcx ≠ .rsp)).trans e4
  have g5 := (gpr_ce t1 [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩] [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR] (by decide : Reg.r8 ≠ .rsp)).trans e5
  have hpre : Proof.Ed448.X86_64.scalarMulAddLocal.pre
      (t1.callEntry.withRegions [⟨L.R, 57⟩, ⟨L.K, 57⟩, ⟨L.S, 57⟩] [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR]) := by
    simp only [Proof.Ed448.X86_64.scalarMulAddLocal, g1, g2, g3, g4, g5, sp_ce hc1, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, fr_x hL (d := 384) (by omega), fr_x hL (d := 256) (by omega),
      fr_x hL (d := 320) (by omega), ret_r hL (hL.kOut.sub_right o2_sub), ret_x hL,
      (hL.xOut.sub_right o2_sub).symm, hL.nScr⟩
  refine call_ok hL Proof.Ed448.X86_64.scalarMulAdd_ok mulAdd_nosp mulAdd_depth hc1 hpre
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [in_fr (d := 384) (by omega), in_fr (d := 256) (by omega), in_fr (d := 320) (by omega)])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inr (.inl (within_off _ (by omega))), .inl (within_self _)])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hc', by rw [← hm]; simpa using hf, ?_⟩
  simp only [Proof.Ed448.X86_64.scalarMulAddLocal, g1, g2, g3, g4, State.withRegions_mem, hm₂] at hpost
  rw [hpost, ed_bytesAt, hc1.ce_bytesAt (ret_fr (d := 384) (by omega)) (by decide),
    hc1.ce_bytesAt (ret_fr (d := 256) (by omega)) (by decide),
    hc1.ce_bytesAt (ret_fr (d := 320) (by omega)) (by decide), hm]

/-! ## Clearing `s` and `r` -/

/-- The first `n` stores of `wipe`. -/
abbrev wipesN (n : Nat) : List Instr := (List.range n).map fun k => .store (stk (fS + 8 * k)) .rax

theorem wipes_ok (hL : L.Ok) : ∀ n ≤ 16, ∀ t : State, Ctx L g mx m₀ t →
    WP isa (.block (wipesN n)) t fun t' => Ctx L g mx m₀ t' ∧ t'.gpr = t.gpr ∧
      Frame [⟨L.S, 128⟩] t.mem t'.mem
  | 0, _, _, hc => WP.block_nil ⟨hc, rfl, Frame.refl _ _⟩
  | n + 1, hn, t, hc => by
    rw [wipesN, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (wipes_ok hL n (by omega) t hc) fun u ⟨hu, ug, uf⟩ => ?_
    have w := hu.inFrW (d := 320 + 8 * n) (n := 8) (by omega)
    refine WP.mono (Q := fun v : State => v.mem = u.mem.writeW (L.SP + BitVec.ofNat 64 (320 + 8 * n)) (u.gpr .rax) ∧
      v.gpr = u.gpr ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.mxcsr = u.mxcsr) ?_ fun v ⟨vm, vg, vrd, vwr, vmx⟩ => ?_
    · apply WP.of_runBlock
      simp only [List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
        ea_stk, hu.rsp, fS, w, ite_true, Option.some.injEq, exists_eq_left']
      exact ⟨trivial, trivial, trivial, trivial, trivial⟩
    have hf1 : Frame [⟨L.S, 128⟩] u.mem v.mem := by
      rw [vm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
        rw [Lay.S]; exact Offset.contains _ (by omega) (by omega) (by omega))
    have ws : WOk L ⟨L.S, 128⟩ := w_dat₂ (d := 320) (by omega) (by omega)
    exact ⟨hu.of_frame hL vrd vwr (fun r _ => by rw [vg]) (by rw [vmx])
      (hf1.mono fun r hr => List.mem_append_left _ hr) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ws), by rw [vg, ug], uf.trans hf1⟩

theorem wipe_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block wipe) t fun t' => Ctx L g mx m₀ t' ∧ Frame [⟨L.S, 128⟩] t.mem t'.mem := by
  rw [wipe, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t.mem ∧ s1.mxcsr = t.mxcsr)
    (by xrun [RegUpd.mxcsr_setReg]) (by decide)) fun t1 ⟨⟨hm1, hx1⟩, k1⟩ => ?_
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k1.2.1 k1.2.2 hm1 hx1 fun r hr => k1.gpr (by
    simp only [List.mem_singleton]; exact Verify.ne_cs hr (by decide))
  exact WP.mono (wipes_ok hL 16 (by omega) t1 hc1) fun t2 ⟨hc2, _, hf⟩ => ⟨hc2, hm1 ▸ hf⟩

end

end VG.Proof.Ed448.X86_64.SignCached
