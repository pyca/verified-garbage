module

public import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Hash
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Prune
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Hash
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.X86_64.Round
public import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Layout
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.X86_64.VariantBounds
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Calls
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLocal
public import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMulAddMain
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit

/-! ### `Ed448.X86_64.SignCached.Calls`, which this module and modules that import it used -/

section

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

@[expose] public section

namespace VG.Proof.Ed448.X86_64.SignCached

variable {v : VG.Impl.Ed448.X86_64.FieldVariant}

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached
open VG.Impl.Ed448.X86_64.Verify (stk Arg callA fH fScr)
open VG.Proof.Ed448.X86_64.Verify (Within within_off within_base within_self add_add ea_stk gpr_ce rsp_ce sp_sub8
  x0 setArgs_ok argRegs_cs argsIn3 argsIn5 reduce_nosp reduce_depth)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.Sha3 (bytesAt)

theorem base_nosp : NoSp (Impl.Ed448.X86_64.scalarBaseFor v) :=
  Proof.Ed448.X86_64.scalarBaseFor_nosp v

theorem base_depth : (Impl.Ed448.X86_64.scalarBaseFor v).depth ≤ 1 :=
  Proof.Ed448.X86_64.scalarBaseFor_depth v

theorem mulAdd_nosp : NoSp Impl.Ed448.X86_64.scalarMulAdd := by
  have : ((instrs Impl.Ed448.X86_64.scalarMulAdd).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem mulAdd_depth : Impl.Ed448.X86_64.scalarMulAdd.depth ≤ 1 := by lit_decide

/-- `vg_ed448_scalar_base` meets the contract its proof is written against, and the ABI. -/
abbrev BaseOk (v : VG.Impl.Ed448.X86_64.FieldVariant) : Prop := ∀ s, Proof.Ed448.X86_64.scalarBaseLocal.clear.pre s →
  ∃ t s', Exec isa (Impl.Ed448.X86_64.scalarBaseFor v) s t s' ∧ abiPreserved s s' ∧
    Proof.Ed448.X86_64.scalarBaseLocal.post s s'

/-- `vg_ed448_scalar_base` is constant time for that contract. -/
abbrev BaseCT (v : VG.Impl.Ed448.X86_64.FieldVariant) : Prop := ConstantTime isa Proof.Ed448.X86_64.scalarBaseLocal.clear.pre
  Proof.Ed448.X86_64.scalarBaseLocal.pub (Impl.Ed448.X86_64.scalarBaseFor v)

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

theorem base_ok (hb : BaseOk v) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (callA ("vg_ed448_scalar_base" ++ v.suffix) (Impl.Ed448.X86_64.scalarBaseFor v) [.slot fOut, .sp fR, .slot fScr]) t
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

end

end

/-! ### `Ed448.X86_64.SignCached.Pre`, which this module and modules that import it used -/

section

/-!
# Ed448 signing with a cached public key on x86-64: the precondition and the layout

The precondition of `signCachedContract X86_64.abi 464`, spelled out
(`SPre`), and the layout of a run from a state satisfying it (`slay`, `Ok` by
`slay_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64

section
variable (s : State)

abbrev sOut : Region := ⟨s.gpr .rdi, 114⟩
abbrev sSeed : Region := ⟨s.gpr .rsi, 57⟩
abbrev sPk : Region := ⟨s.gpr .rdx, 57⟩
abbrev sCtx : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
abbrev sMsg : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
abbrev sArgs : Region := ⟨stackArgAddr s 0, 16⟩
abbrev sScr : Region := ⟨stackArg s 1, 8192⟩
abbrev sRet : Region := ⟨s.gpr .rsp, 8⟩
abbrev sStk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 464, 464⟩

end

/-- The precondition of `signCachedContract X86_64.abi 464`. -/
structure SPre (s : State) : Prop where
  sp : 464 ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [sSeed s, sPk s, sCtx s, sMsg s, sArgs s]
  wr : s.wr = [sOut s, sScr s]
  outSeed : (sOut s).Disjoint (sSeed s)
  outPk : (sOut s).Disjoint (sPk s)
  outCtx : (sOut s).Disjoint (sCtx s)
  outMsg : (sOut s).Disjoint (sMsg s)
  outScr : (sOut s).Disjoint (sScr s)
  outArgs : (sOut s).Disjoint (sArgs s)
  seedScr : (sSeed s).Disjoint (sScr s)
  pkScr : (sPk s).Disjoint (sScr s)
  ctxScr : (sCtx s).Disjoint (sScr s)
  msgScr : (sMsg s).Disjoint (sScr s)
  scrArgs : (sScr s).Disjoint (sArgs s)
  retOut : (sRet s).Disjoint (sOut s)
  retSeed : (sRet s).Disjoint (sSeed s)
  retPk : (sRet s).Disjoint (sPk s)
  retCtx : (sRet s).Disjoint (sCtx s)
  retMsg : (sRet s).Disjoint (sMsg s)
  retScr : (sRet s).Disjoint (sScr s)
  retArgs : (sRet s).Disjoint (sArgs s)
  stkOut : (sStk s).Disjoint (sOut s)
  stkSeed : (sStk s).Disjoint (sSeed s)
  stkPk : (sStk s).Disjoint (sPk s)
  stkCtx : (sStk s).Disjoint (sCtx s)
  stkMsg : (sStk s).Disjoint (sMsg s)
  stkScr : (sStk s).Disjoint (sScr s)
  stkArgs : (sStk s).Disjoint (sArgs s)
  nOut : (s.gpr .rdi).toNat + 114 ≤ 2 ^ 64
  nSeed : (s.gpr .rsi).toNat + 57 ≤ 2 ^ 64
  nPk : (s.gpr .rdx).toNat + 57 ≤ 2 ^ 64
  nCtx : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  nMsg : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  nScr : (stackArg s 1).toNat + 8192 ≤ 2 ^ 64
  pk : Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 57)
  ctxLe : (s.gpr .r8).toNat ≤ 255

theorem sPre_of {s : State} (h : (Spec.Ed448.signCachedContract X86_64.abi 464).pre s) : SPre s := by
  sig_pre [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig, Spec.Ed448.scratchWords, X86_64.abi,
    X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37⟩

/-- The layout of a run of `signCached` from `s`. -/
def slay (s : State) : Lay where
  B := s.gpr .rsp - BitVec.ofNat 64 464
  out := s.gpr .rdi
  seed := s.gpr .rsi
  pk := s.gpr .rdx
  ctx := s.gpr .rcx
  ctxLen := s.gpr .r8
  msg := s.gpr .r9
  len := stackArg s 0
  scr := stackArg s 1
  rd := s.rd
  wr := s.wr

theorem slay_B (s : State) : (slay s).B + BitVec.ofNat 64 464 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem slay_ok {s : State} (h : SPre s) : (slay s).Ok := by
  have eR : (slay s).RET = sRet s := by
    show (⟨(slay s).B + BitVec.ofNat 64 464, 8⟩ : Region) = _
    rw [slay_B]
  refine ⟨by have := h.ctxLe; simp only [slay]; omega_using [this], ?_, h.wr, by simp [slay, h.rd], by simp [slay, h.rd],
    by simp [slay, h.rd], by simp [slay, h.rd], h.seedScr.symm, h.pkScr.symm, h.ctxScr.symm, h.msgScr.symm,
    h.outScr.symm, h.outSeed, h.outPk, h.outCtx, h.outMsg, h.stkScr, h.stkOut, h.stkSeed, h.stkPk, h.stkCtx,
    h.stkMsg, by rw [eR]; exact h.retScr, by rw [eR]; exact h.retOut, h.nOut, h.nSeed, h.nPk, h.nCtx, h.nMsg,
    h.nScr⟩
  have := h.sp; have := h.sp2
  simp only [slay, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

end VG.Proof.Ed448.X86_64.SignCached

end

end

/-!
# Ed448 signing with a cached public key on x86-64: correctness

The frame's body leaves `R ‖ S` in `out`, `Spec.Ed448.sign` of the private
key, the context and the message, given the public key of the private key
(`body_ok`): each piece is kept by the code that runs after it, which writes
elsewhere. The frame's push gives `Ctx` (`entry_ctx`). From a state
satisfying `signCachedContract X86_64.abi 464`, `signCached` meets the
contract and the ABI (`signCached_wp`), for any proof of
`vg_ed448_scalar_base` (`BaseOk`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.SignCached

variable {v : VG.Impl.Ed448.X86_64.FieldVariant}

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached
open VG.Impl.Ed448.X86_64.Verify (stk)
open VG.Proof.Ed448.X86_64.Verify (add_add ea_stk x0 bytesAt_length bytesAt_congr)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.Sha3 (bytesAt)

section
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- Bytes apart from every region of a frame are kept. -/
theorem keepB {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

/-- Two pieces of the frame. -/
theorem ff (L : Lay) {d n e k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 448) (he : e + k ≤ 448) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ ⟨L.SP + BitVec.ofNat 64 e, k⟩ :=
  Offset.disjoint _ h (by omega_arith) (by omega_arith)

/-- A piece of the frame and the 16 bytes below it. -/
theorem fb (L : Lay) {d n : Nat} (hd : d + n ≤ 448) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ ⟨L.B, 16⟩ := by
  rw [spd]; exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

/-- A piece of the frame and one of `out`. -/
theorem fo (hL : L.Ok) {d n e k : Nat} (hd : d + n ≤ 448) (he : e + k ≤ 114) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ ⟨L.out + BitVec.ofNat 64 e, k⟩ := by
  rw [spd]; exact (hL.stk_r hL.kOut (d := 16 + d) (n := n) (by omega_arith)).sub_right (Offset.sub_base _ he)

/-- A piece of `out` and `scratch`; and the 16 bytes below the frame. -/
theorem ox (hL : L.Ok) {e k : Nat} (he : e + k ≤ 114) :
    Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ L.SCR :=
  (hL.o_r hL.xOut.symm he)

theorem ob (hL : L.Ok) {e k : Nat} (he : e + k ≤ 114) :
    Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ ⟨L.B, 16⟩ :=
  (k_r hL (hL.kOut.sub_right (Offset.sub_base _ he))).symm

theorem out0 (L : Lay) : L.out + BitVec.ofNat 64 0 = L.out := x0 _

/-- The header and the prefix after a hash into the frame. -/
theorem bytes_drop (m : Mem) (p : Addr) :
    (bytesAt m p 114).drop 57 = bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  obtain a := Proof.X25519.bytesAt_add m p 57 57
  obtain l := Proof.X25519.length_bytesAt m p 57
  change (Spec.X25519.bytesAt m p (57 + 57)).drop 57 = Spec.X25519.bytesAt m (p + BitVec.ofNat 64 57) 57
  rw [a, List.drop_left' l]

theorem bytes_split (m : Mem) (p : Addr) :
    bytesAt m p 114 = bytesAt m p 57 ++ bytesAt m (p + BitVec.ofNat 64 57) 57 :=
  Proof.X25519.bytesAt_add m p 57 57

/-- The first ten bytes of `dom4(0, C)`, then `C`, are `dom4(0, C)`. -/
theorem hash_eq (L : Lay) (c X Y : List Byte) (hc : c.length = L.ctxLen.toNat) :
    Spec.Sha3.shake256 (hdrBytes L ++ c ++ X ++ Y) 114 = Spec.Ed448.hash c (X ++ Y) := by
  simp only [Spec.Ed448.hash, Spec.Ed448.dom4, hdrBytes, hc, List.append_assoc]

theorem hash_eq' (L : Lay) (c X P Y : List Byte) (hc : c.length = L.ctxLen.toNat) :
    Spec.Sha3.shake256 (hdrBytes L ++ c ++ X ++ P ++ Y) 114 = Spec.Ed448.hash c (X ++ P ++ Y) := by
  simp only [Spec.Ed448.hash, Spec.Ed448.dom4, hdrBytes, hc, List.append_assoc]

theorem body_ok (hb : BaseOk v) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hpk : Spec.Ed448.bytesAt m₀ L.pk 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ L.seed 57)) :
    WP isa (bodyFor v) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed448.bytesAt t'.mem L.out 114 = Spec.Ed448.sign (bytesAt m₀ L.seed 57)
        (bytesAt m₀ L.ctx L.ctxLen.toNat) (bytesAt m₀ L.msg L.len.toNat) := by
  refine WP.seq (WP.mono (hdr_ok hL hc) fun t1 ⟨hc1, hh⟩ => ?_)
  refine WP.seq (WP.mono (seedHash_ok hL hc1) fun t2 ⟨hc2, f2, hS⟩ => ?_)
  refine WP.seq (WP.mono (prune_ok hL hc2) fun t3 ⟨hc3, f3, hs⟩ => ?_)
  refine WP.seq (WP.mono (nonceHash_ok hL hc3) fun t4 ⟨hc4, f4, hN⟩ => ?_)
  refine WP.seq (WP.mono (red_ok hL hc4 (d := 384) (by omega_arith) (by omega_arith) (by omega_arith)) fun t5 ⟨hc5, f5, hR⟩ => ?_)
  refine WP.seq (WP.mono (base_ok hb hL hc5) fun t6 ⟨hc6, f6, hO⟩ => ?_)
  refine WP.seq (WP.mono (chalHash_ok hL hc6) fun t7 ⟨hc7, f7, hC⟩ => ?_)
  refine WP.seq (WP.mono (red_ok hL hc7 (d := 256) (by omega_arith) (by omega_arith) (by omega_arith)) fun t8 ⟨hc8, f8, hK⟩ => ?_)
  refine WP.seq (WP.mono (mulAdd_ok hL hc8) fun t9 ⟨hc9, f9, hM⟩ => ?_)
  refine WP.mono (wipe_ok hL hc9) fun t10 ⟨hc10, f10⟩ => ⟨hc10, ?_⟩
  -- Facts about the regions.
  obtain xS : ∀ {d n : Nat}, d + n ≤ 448 → Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ L.SCR :=
    fun h => fr_x hL h
  obtain rHW : ∀ {d n : Nat}, d + n ≤ 448 → (16 + 114 ≤ d) → ∀ r ∈ HW L,
      Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ r := fun h h' r hr => by
    simp only [HW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [xS h, ff L (.inr h') h (by omega_arith), fb L h]
  obtain oHW : ∀ {e k : Nat}, e + k ≤ 114 → ∀ r ∈ HW L, Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ r :=
    fun h r hr => by
      simp only [HW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [ox hL h, (fo hL (d := 16) (n := 114) (by omega_arith) h).symm, ob hL h]
  obtain three : ∀ {p : Addr} {n : Nat} {q : Region}, Region.Disjoint ⟨p, n⟩ q → Region.Disjoint ⟨p, n⟩ L.SCR →
      Region.Disjoint ⟨p, n⟩ ⟨L.B, 16⟩ → ∀ r ∈ [q, L.SCR, ⟨L.B, 16⟩], Region.Disjoint ⟨p, n⟩ r :=
    fun h₁ h₂ h₃ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h₁, h₂, h₃]
  obtain one : ∀ {p : Addr} {n : Nat} {q : Region}, Region.Disjoint ⟨p, n⟩ q → ∀ r ∈ [q], Region.Disjoint ⟨p, n⟩ r :=
    fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h
  -- The header, through the hashes and the calls up to the challenge's hash.
  obtain hdr0 : ∀ r ∈ HW L, Region.Disjoint ⟨L.SP + BitVec.ofNat 64 0, 10⟩ r := fun r hr => by
    simp only [HW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [xS (by omega_arith), ff L (.inl (by omega_arith)) (by omega_arith) (by omega_arith), fb L (by omega_arith)]
  rw [sp0] at hdr0
  obtain hx0 := xS (d := 0) (n := 10) (by omega_arith); rw [sp0] at hx0
  obtain hb0 := fb L (d := 0) (n := 10) (by omega_arith); rw [sp0] at hb0
  obtain e2 := keepB f2 hdr0 (by decide)
  obtain e3 := keepB f3 (one (q := ⟨L.S, 64⟩) (by
    have := ff L (d := 0) (n := 10) (e := 320) (k := 64) (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    rwa [sp0] at this)) (by decide)
  obtain e4 := keepB f4 hdr0 (by decide)
  obtain e5 := keepB f5 (three (by
    have := ff L (d := 0) (n := 10) (e := 384) (k := 57) (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    rwa [sp0] at this) hx0 hb0) (by decide)
  obtain e6 := keepB f6 (three (by
    have := fo hL (d := 0) (n := 10) (e := 0) (k := 57) (by omega_arith) (by omega_arith)
    rwa [sp0, out0] at this) hx0 hb0) (by decide)
  -- The prefix, through the pruning.
  obtain p3 := keepB f3 (one (q := ⟨L.S, 64⟩) (ff L (d := 73) (n := 57) (e := 320) (k := 64) (.inl (by omega_arith))
    (by omega_arith) (by omega_arith))) (by decide)
  -- `R`, through the challenge's hash and its reduction, and the scalar product.
  obtain o1 : ∀ {e k : Nat}, e + k ≤ 114 → Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ L.SCR ∧
      Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ ⟨L.B, 16⟩ := fun h => ⟨ox hL h, ob hL h⟩
  obtain r7 := keepB f7 (p := L.out) (n := 57) (by have := oHW (e := 0) (k := 57) (by omega_arith); rwa [out0] at this)
    (by decide)
  obtain r8 := keepB f8 (p := L.out) (n := 57) (three (by
      have := (fo hL (d := 256) (n := 57) (e := 0) (k := 57) (by omega_arith) (by omega_arith)).symm
      rwa [out0] at this) (by have := (o1 (e := 0) (k := 57) (by omega_arith)).1; rwa [out0] at this)
      (by have := (o1 (e := 0) (k := 57) (by omega_arith)).2; rwa [out0] at this)) (by decide)
  obtain r9 := keepB f9 (p := L.out) (n := 57) (three (by
      have := Offset.disjoint L.out (d := 0) (n := 57) (e := 57) (k := 57) (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      rwa [out0] at this) (by have := (o1 (e := 0) (k := 57) (by omega_arith)).1; rwa [out0] at this)
      (by have := (o1 (e := 0) (k := 57) (by omega_arith)).2; rwa [out0] at this)) (by decide)
  obtain r10 := keepB f10 (p := L.out) (n := 57) (one (by
      have := (fo hL (d := 320) (n := 128) (e := 0) (k := 57) (by omega_arith) (by omega_arith)).symm
      rwa [out0] at this)) (by decide)
  obtain s10 := keepB f10 (p := L.out + BitVec.ofNat 64 57) (n := 57)
    (one (fo hL (d := 320) (n := 128) (e := 57) (k := 57) (by omega_arith) (by omega_arith)).symm) (by decide)
  -- `r` and `s`, through the code after them.
  obtain rr6 := keepB f6 (p := L.R) (n := 57) (three (fo hL (d := 384) (n := 57) (e := 0) (k := 57) (by omega_arith)
    (by omega_arith) |> fun h => by rwa [out0] at h) (xS (by omega_arith)) (fb L (by omega_arith))) (by decide)
  obtain rr7 := keepB f7 (p := L.R) (n := 57) (rHW (by omega_arith) (by omega_arith)) (by decide)
  obtain rr8 := keepB f8 (p := L.R) (n := 57) (three (ff L (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (xS (by omega_arith))
    (fb L (by omega_arith))) (by decide)
  obtain ss4 := keepB f4 (p := L.S) (n := 57) (rHW (by omega_arith) (by omega_arith)) (by decide)
  obtain ss5 := keepB f5 (p := L.S) (n := 57) (three (ff L (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (xS (by omega_arith))
    (fb L (by omega_arith))) (by decide)
  obtain ss6 := keepB f6 (p := L.S) (n := 57) (three (fo hL (d := 320) (n := 57) (e := 0) (k := 57) (by omega_arith)
    (by omega_arith) |> fun h => by rwa [out0] at h) (xS (by omega_arith)) (fb L (by omega_arith))) (by decide)
  obtain ss7 := keepB f7 (p := L.S) (n := 57) (rHW (by omega_arith) (by omega_arith)) (by decide)
  obtain ss8 := keepB f8 (p := L.S) (n := 57) (three (ff L (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (xS (by omega_arith))
    (fb L (by omega_arith))) (by decide)
  -- The pieces.
  obtain pre : bytesAt t2.mem (L.SP + BitVec.ofNat 64 73) 57 = (bytesAt t2.mem L.H 114).drop 57 := by
    rw [bytes_drop, Lay.H, add_add L.SP 16 57]
  change Spec.Ed448.bytesAt t5.mem L.R 57 = _ at hR
  change Spec.Ed448.bytesAt t8.mem L.K 57 = _ at hK
  rw [ed_bytesAt] at hs hR hO hK hM hpk ⊢
  rw [bytes_split, r10, r9, r8, r7, s10, hM, rr8, rr7, rr6, hR, hK, hC, hN, ss8, ss7, ss6, ss5, ss4, e6, e5, e4,
    e3, p3, pre, e2, hh, hS, hO, hR, hN, e3, p3, pre, e2, hh, hS]
  rw [hS] at hs
  rw [hash_eq L _ _ _ (Verify.bytesAt_length _ _ _), hash_eq' L _ _ _ _ (Verify.bytesAt_length _ _ _)]
  exact Proof.Ed448.sign_pipeline _ _ _ _ _ hpk hs

end

/-! ## The frame -/

theorem push_slot (B : Addr) (j : Nat) (hj : j < 56) :
    B + BitVec.ofNat 64 464 - BitVec.ofNat 64 (8 * (j + 1)) =
      B + BitVec.ofNat 64 16 + BitVec.ofNat 64 (440 - 8 * j) := by
  rw [add_add, Offset.sub_ofNat_eq _ (a := 8 * (j + 1)) (b := 464) (by omega_arith), BitVec.add_sub_cancel]
  congr 2; omega_arith

theorem push_base (B : Addr) : B + BitVec.ofNat 64 464 - BitVec.ofNat 64 (8 * 56) = B + BitVec.ofNat 64 16 := by
  have := push_slot B 55 (by omega_arith); simpa using this

theorem regs_length : regs.length = 56 := rfl

/-- After the push of the registers holding the arguments and 0: `Ctx`. -/
theorem entry_ctx {L : Lay} (hL : L.Ok) {s : State} (hsp : s.gpr .rsp = L.B + BitVec.ofNat 64 464)
    (hrd : s.rd = L.rd) (hwr : s.wr = L.wr) (h11 : s.gpr .r11 = L.scr) (hdi : s.gpr .rdi = L.out)
    (h10 : s.gpr .r10 = L.len) (h9 : s.gpr .r9 = L.msg) (h8 : s.gpr .r8 = L.ctxLen) (hcx : s.gpr .rcx = L.ctx)
    (hdx : s.gpr .rdx = L.pk) (hsi : s.gpr .rsi = L.seed) :
    Ctx L s.gpr s.mxcsr s.mem (pushed regs s) := by
  obtain hn : 8 * regs.length ≤ (s.gpr .rsp).toNat := by
    rw [hsp, regs_length, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hL.nB
    rw [Nat.mod_eq_of_lt (a := 464) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  obtain ⟨hf, hw⟩ := pushRegs_mem s regs (by decide) hn
  obtain slot : ∀ j (hj : j < 56), (pushed regs s).mem.readW (L.SP + BitVec.ofNat 64 (440 - 8 * j)) 64 =
      s.gpr (regs[j]'(by rw [regs_length]; omega_arith)) := fun j hj => by
    rw [← hw j (by rw [regs_length]; omega_arith), hsp, push_slot _ j hj]; rfl
  obtain base : s.gpr .rsp - BitVec.ofNat 64 (8 * regs.length) = L.SP := by
    rw [hsp, regs_length]; exact push_base L.B
  refine ⟨by simp [hrd], by rw [pushed_wr, base, hwr]; rfl, by rw [pushed_rsp, base], fun r _ hr' => pushed_gpr _ _ hr',
    by simp, (slot 30 (by omega_arith)).trans hdx, (slot 29 (by omega_arith)).trans hcx, (slot 28 (by omega_arith)).trans h8,
    (slot 27 (by omega_arith)).trans h9, (slot 26 (by omega_arith)).trans h10, (slot 25 (by omega_arith)).trans hdi,
    (slot 24 (by omega_arith)).trans h11, (slot 38 (by omega_arith)).trans hsi, ?_⟩
  show Frame [L.SCR, L.OUT, L.STK] s.mem (pushRegs s regs).mem
  refine Frame.sub hf fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨L.STK, by simp, ?_⟩
  rw [base, regs_length]
  exact Offset.sub_base _ (by omega_arith)

/-! ## Before the frame -/

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl

/-- `len` to `r10`, `scratch` to `r11`, 0 to `rax`. -/
theorem signMov_ok {s : State} (h : SPre s) :
    WP isa (.block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0)]) s fun s2 =>
      (s2.gpr .r10 = stackArg s 0 ∧ s2.gpr .r11 = stackArg s 1 ∧ s2.mem = s.mem ∧ s2.mxcsr = s.mxcsr) ∧
        Keep [.r10, .r11, .rax] s s2 := by
  obtain hin : ∀ d, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (8 + d)) 8 := by
    intro d hd
    refine ⟨sArgs s, by simp [h.rd], ?_⟩
    rw [← add_add, ← stackArgAddr0]
    exact Offset.contains_base _ hd (by omega_arith)
  refine WP.keep _ ?_ (by decide)
  obtain h8 := hin 0 (by omega_arith)
  obtain h16 := hin 8 (by omega_arith)
  simp only [Nat.reduceAdd] at h8 h16
  xrun [ea_stk, h8, h16, RegUpd.mxcsr_setReg]
  exact ⟨rfl, rfl⟩

theorem cs_r11 : ∀ r ∈ calleeSaved, r ≠ .r11 := by decide
theorem cs_tmp : ∀ r ∈ calleeSaved, r ∉ [Reg.r10, .r11, .rax] := by decide

/-! ## The function -/

/-- The bytes of a region apart from a frame are what they were once the
frame's bytes are lost. -/
private theorem bytes_lost {F : Region} {m m' : Mem} (f : Frame [F] m m') {p : Addr} {n : Nat}
    (hd : (⟨p, n⟩ : Region).Disjoint F) : Spec.Ed448.bytesAt m' p n = Spec.Ed448.bytesAt m p n := by
  simp only [Spec.Ed448.bytesAt]
  exact List.map_congr_left fun i hi => lost_byte f hd (List.mem_range.mp hi)

theorem signCached_wp (hb : BaseOk v) {s : State} (hpre : (Spec.Ed448.signCachedContract X86_64.abi 464).pre s) :
    WP isa (signCachedFor v) s fun s' =>
      abiPreserved s s' ∧ (Spec.Ed448.signCachedContract X86_64.abi 464).post s s' := by
  obtain h := sPre_of hpre
  obtain hL := slay_ok h
  unfold signCachedFor
  refine WP.seq (WP.mono (signMov_ok h) fun s2 ⟨⟨h10, h11, hm2, hx2⟩, k2⟩ => ?_)
  obtain hg2 : ∀ r, r ∉ [Reg.r10, .r11, .rax] → s2.gpr r = s.gpr r := fun r hr => k2.gpr hr
  obtain hsp2 : s2.gpr .rsp = (slay s).B + BitVec.ofNat 64 464 := by rw [hg2 _ (by decide), slay_B]
  obtain hn : 8 * regs.length ≤ (s2.gpr .rsp).toNat := by
    rw [hg2 _ (by decide), regs_length]; have := h.sp; omega_arith
  refine WP.frame (by decide) (by decide) (by decide) hn ?_
  obtain hc := entry_ctx hL hsp2 k2.2.1 k2.2.2 h11 (hg2 _ (by decide)) h10 (hg2 _ (by decide)) (hg2 _ (by decide))
    (hg2 _ (by decide)) (hg2 _ (by decide)) (hg2 _ (by decide))
  obtain hpk : Spec.Ed448.bytesAt s2.mem (slay s).pk 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt s2.mem (slay s).seed 57) := by
    rw [hm2]; exact h.pk
  refine WP.mono (body_ok hb hL hc hpk) fun s' ⟨hc', hr⟩ => ⟨by rw [hc'.rsp, hc.rsp], by rw [hc'.wr, hc.wr],
    fun m uk fm => ?_⟩
  -- The pop loses the frame's 448 bytes, in the stack below `rsp`, apart from
  -- the signature and the return address.
  rw [hg2 .rsp (by decide), regs_length] at fm
  obtain hF : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 (8 * 56), 8 * 56⟩ (sStk s) :=
    Offset.sub_below _ (by decide) (by decide)
  replace hr := (bytes_lost fm (h.stkOut.symm.sub_right hF)).trans hr
  dsimp only
  refine ⟨?_, ?_⟩
  · -- The calling convention.
    refine ⟨fun r hr => ?_, ?_, ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'
        rw [popped_rsp, hc'.rsp, Lay.SP, add_add, regs_length, slay_B]
      · rw [popped_gpr _ _ _ hr' (cs_r11 r hr), hc'.cs r hr hr', hg2 r (cs_tmp r hr)]
    · have eR : sRet s = ⟨(slay s).B + BitVec.ofNat 64 464, 8⟩ := by rw [slay_B]
      rw [fm.readW (r := sRet s) (Region.contains_self _ _) (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact Offset.base_disjoint_below (s.gpr .rsp) (n := 448) (k := 8) (by decide)) (by decide),
        hc'.frame.readW (r := sRet s) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.retScr
          · exact h.retOut
          · rw [eR]; exact Offset.disjoint_base _ (by omega_arith) (by have := hL.nB; omega_arith)) (by decide), hm2]
    · rw [popped_mxcsr, hc'.mx, hx2]
  · sig_post [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig, Spec.Ed448.scratchWords, X86_64.abi,
      X86_64.argRegs, List.range, List.range.loop]
    rw [hm2] at hr
    exact hr

end VG.Proof.Ed448.X86_64.SignCached
