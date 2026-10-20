module

public import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Rsa.X86.RvArguments
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeBase
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeMul
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Callee
import VerifiedGarbage.Proof.Mont.X86.Rt.Verified
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # What the timing of prime recovery at a run-time width checks its pieces from

Every operation reads the modulus's length and the working space from the
arguments on the stack, so the taint analysis takes them public: `τA`, the
arguments above `esp`, `edi` and `esp`, and `τF`, the same inside the frame
of 36 bytes of a call of `vg_rsa_mont_mul_at`. Two runs of a stage over the
same geometry, whose writable regions lie apart from the arguments (`PubG`),
agree on them (`ks_agree`); a Montgomery product leaks the same trace in
both (`mmul_relCT`), its call related by the callee's contract.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.RtCall
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.RecoverRt (mmul mulArgs clrTop)
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Bignum.X86.PublicRt (calleeOf argByte_alloc calleeOf_eq rtPub_of rtPre_of)

/-- The arguments, `edi` and `esp`. -/
def τA : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 52 }

/-- `τA` in the frame of a call of `vg_rsa_mont_mul_at`. -/
def τF : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 52, stk := [some 36] }

/-- The return address and the arguments lie apart from every writable region. -/
def ArgsOk (s : State) : Prop :=
  (s.gpr .esp).toNat + 52 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 52⟩ r

/-- The geometry's writable regions lie apart from the return address and the arguments. -/
def PubG (g : Geo) : Prop :=
  g.sp.toNat + 52 ≤ 2 ^ 32 ∧ ∀ r ∈ g.wr, Region.Disjoint ⟨g.sp.setWidth 64, 52⟩ r

theorem τA_wf {s : State} (A : ArgsOk s) : VG.X86.Taint.Wf τA s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

theorem τF_wf {s : State} (A : ArgsOk s) (low : 36 ≤ (s.gpr .esp).toNat) :
    VG.X86.Taint.Wf τF (allocFrame 36 s) := by
  have f := A.1
  have eN : ((allocFrame 36 s).gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by
    rw [allocFrame_esp, sub_toNat low]
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨?_, fun r hr => ?_⟩, fun _ h => (List.not_mem_nil h).elim, ?_, fun p hp => ?_, fun h => absurd h (by decide)⟩
  · show _ + 36 + 52 ≤ _; omega
  · rw [show VG.X86.Taint.depth τF.stk = 36 + 0 from rfl, argByte_alloc low, VG.X86.Taint.argByte, BitVec.add_zero]
    rw [allocFrame_wr, List.mem_cons] at hr
    rcases hr with rfl | hr
    · rw [VG.X86.Taint.sub_setWidth low]
      exact (Offset.base_disjoint_below _ (by decide)).symm.symm
    · exact A.2 r hr
  · show _ + 36 < _; omega
  · simp only [τF, VG.X86.Taint.frameList, List.mem_singleton] at hp
    subst hp
    simp only [allocFrame_wr, allocFrame_esp, List.getElem?_cons_zero, addr, BitVec.add_zero]

section
variable {g : Geo} {s0 t0 s t : State} {A B AW BW V W : Nat → Nat} {al bl aw bw sl tl : List Nat}

theorem KS.argsOk (pg : PubG g) (h : KS g s0 A al AW aw V sl s) : ArgsOk s := by
  unfold ArgsOk
  rw [h.sp, h.rest.2.2, h.start.1]
  exact pg

/-- Two runs of stages over the same geometry agree on what `τA` makes public. -/
theorem ks_agree (pg : PubG g) (h : KS g s0 A al AW aw V sl s) (j : KS g t0 B bl BW bw W tl t) :
    VG.X86.Taint.Agree τA s t := by
  have f₁ := (h.argsOk pg).1
  have f₂ := (j.argsOk pg).1
  have sp : s.gpr .esp = t.gpr .esp := h.sp.trans j.sp.symm
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τA_wf (h.argsOk pg), τA_wf (j.argsOk pg),
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τA, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h.ws.workspace.edi_toNat.trans j.ws.workspace.edi_toNat.symm)
    · exact sp
  · simp only [τA] at hk
    have C₁ := h.arg (h.start.2 ((k - 4) / 4) (by omega)).1 (by omega)
    have C₂ := j.arg (j.start.2 ((k - 4) / 4) (by omega)).1 (by omega)
    rw [show VG.X86.Taint.depth τA.stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (show arg s _ = arg t _ from C₁.value.trans C₂.value.symm)

/-- The same in the frame of a call. -/
theorem ks_agreeF (pg : PubG g) (h : KS g s0 A al AW aw V sl s) (j : KS g t0 B bl BW bw W tl t) :
    VG.X86.Taint.Agree τF (allocFrame 36 s) (allocFrame 36 t) := by
  have G := ks_agree pg h j
  have low₁ : 36 ≤ (s.gpr .esp).toNat := by rw [h.sp]; have := h.room.low; omega
  have low₂ : 36 ≤ (t.gpr .esp).toNat := by rw [j.sp]; have := j.room.low; omega
  have sp : s.gpr .esp = t.gpr .esp := h.sp.trans j.sp.symm
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τF_wf (h.argsOk pg) low₁,
    τF_wf (j.argsOk pg) low₂, VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty,
    fun _ => by simp only [allocFrame_esp, sp], fun k h4 hk => ?_⟩
  · simp only [τF, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide)]
      exact G.rf.1 _ (by simp [τA])
    · simp only [allocFrame_esp, sp]
  · rw [show VG.X86.Taint.depth τF.stk = 36 from rfl, argByte_alloc low₁, argByte_alloc low₂, allocFrame_mem,
      allocFrame_mem]
    have := G.argMem k h4 hk
    rwa [show VG.X86.Taint.depth τA.stk = 0 from rfl, Nat.zero_add] at this

end

/-- Code whose leaks `τA` makes public. -/
def Pub (c : Prog isa) : Prop := ∃ hint, (VG.Taint.check taint τA c hint).isSome = true

theorem Pub.trace {c : Prog isa} (h : Pub c) : RelCT isa (VG.X86.Taint.Agree τA) c (fun _ _ => True) := by
  obtain ⟨hint, hT⟩ := h
  exact VG.RelCT.taint (A := taint) τA (fun _ _ h => h) hT

/-- A stage from which `mmul o a b` runs: the callee's precondition holds, and the stage after the call. -/
def MulPre (g : Geo) (o a b : Nat) (s : State) : Prop :=
  ∃ s0 A live AW liveW V ls m, KS g s0 A live AW liveW V ls s ∧ MR g m s ∧ a ∈ live ∧ b ∈ live ∧
    A a < m ∧ A b < m ∧ (∀ j ∈ live, j = o ∨ j ∉ montWrites o) ∧
    (∀ j ∈ liveW, ∀ i ∈ montWrites o, i / 2 ≠ j)

/-- What each run of the call leaves: a stage. -/
def MulPost (g : Geo) (u : State) : Prop := ∃ s0 A live AW liveW V ls, KS g s0 A live AW liveW V ls u

theorem mmul_relCT {g : Geo} (pg : PubG g) {o a b : Nat} (ho : MontIndex o) (ha : MontIndex a)
    (hb : MontIndex b) (ho0 : o ≠ mBase)
    (hT : (VG.Taint.check taint τF (.block (mulArgs o a b)) (.block [])).isSome = true)
    (hC : Pub (.block (clrTop o))) :
    RelCT isa (fun s t => MulPre g o a b s ∧ MulPre g o a b t) (mmul o a b) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.mmul
  have Call : RelCT isa (fun s t => MulPre g o a b s ∧ MulPre g o a b t) (callCode (mulArgs o a b))
      (fun _ _ => True) := by
    refine RelCT.frameAlloc (R := fun _ _ => True) ?_
    have blk := (VG.RelCT.taint (A := taint) (P := fun f₁ f₂ => ∃ s₁ s₂, (MulPre g o a b s₁ ∧ MulPre g o a b s₂) ∧
        f₁ = allocFrame 36 s₁ ∧ f₂ = allocFrame 36 s₂) τF (fun _ _ ⟨s₁, s₂, ⟨I₁, I₂⟩, q₁, q₂⟩ => by
          obtain ⟨_, _, _, _, _, _, _, _, h₁, _⟩ := I₁
          obtain ⟨_, _, _, _, _, _, _, _, h₂, _⟩ := I₂
          subst q₁ q₂
          exact ks_agreeF pg h₁ h₂) hT).wp
      (F₁ := CallOk g o a b) (F₂ := CallOk g o a b)
      (fun _ _ ⟨s₁, s₂, ⟨I₁, I₂⟩, q₁, q₂⟩ => by
        subst q₁ q₂
        obtain ⟨_, _, _, _, _, _, _, _, h₁, mr₁, _, hb₁, _, hB₁, _⟩ := I₁
        obtain ⟨_, _, _, _, _, _, _, _, h₂, mr₂, _, hb₂, _, hB₂, _⟩ := I₂
        exact ⟨h₁.callOk mr₁ ho ha hb ho0 hb₁ hB₁, h₂.callOk mr₂ ho ha hb ho0 hb₂ hB₂⟩)
    refine VG.RelCT.seq blk ?_
    refine RelCT.call (k := Spec.Rsa.MontMul.mulContract abi 0) rt_correct rt_constantTime
      [⟨(g.sp - BitVec.ofNat 32 36).setWidth 64, 36⟩] [⟨g.B, g.Z⟩] ?_
    rintro g₁ g₂ ⟨-, ⟨A₁, sp₁, arg₁, fr₁, sc₁⟩, ⟨A₂, sp₂, arg₂, fr₂, sc₂⟩⟩
    have c₁ := calleeOf_eq (base := g.B) (bytes := g.Z) sp₁
    have c₂ := calleeOf_eq (base := g.B) (bytes := g.Z) sp₂
    rw [sp₁] at fr₁
    rw [sp₂] at fr₂
    refine ⟨c₁ ▸ rtPre_of A₁, c₂ ▸ rtPre_of A₂, ?_, Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_,
      Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_, by rw [sp₁, sp₂]⟩
    · rw [← c₁, ← c₂]
      refine rtPub_of ?_ fun i hi => (arg₁ i hi).trans (arg₂ i hi).symm
      simp only [calleeOf, State.withRegions_gpr, State.callEntry_esp, sp₁, sp₂]
    · rcases List.mem_append.mp hr with hr | hr <;> rw [List.mem_singleton.mp hr]
      · exact List.mem_append_right _ fr₁
      · exact List.mem_append_right _ sc₁
    · rw [List.mem_singleton.mp hr]; exact sc₁
    · rcases List.mem_append.mp hr with hr | hr <;> rw [List.mem_singleton.mp hr]
      · exact List.mem_append_right _ fr₂
      · exact List.mem_append_right _ sc₂
    · rw [List.mem_singleton.mp hr]; exact sc₂
  have Call' := Call.wp (F₁ := MulPost g) (F₂ := MulPost g) fun s t ⟨I₁, I₂⟩ => by
    obtain ⟨s0, A, live, AW, liveW, V, ls, m, h₁, mr₁, ha₁, hb₁, hA₁, hB₁, hl₁, hlW₁⟩ := I₁
    obtain ⟨t0, B, bl, BW, bw, W, tl, m', h₂, mr₂, ha₂, hb₂, hA₂, hB₂, hl₂, hlW₂⟩ := I₂
    exact ⟨WP.mono (h₁.mmulCall mr₁ ho ha hb ho0 ha₁ hb₁ hA₁ hB₁ hl₁ hlW₁) fun u ⟨hu, _⟩ => ⟨_, _, _, _, _, _, _, hu⟩,
      WP.mono (h₂.mmulCall mr₂ ho ha hb ho0 ha₂ hb₂ hA₂ hB₂ hl₂ hlW₂) fun u ⟨hu, _⟩ => ⟨_, _, _, _, _, _, _, hu⟩⟩
  refine VG.RelCT.seq Call' (hC.trace.mono ?_ fun _ _ _ => trivial)
  rintro u v ⟨-, ⟨_, _, _, _, _, _, _, hu⟩, ⟨_, _, _, _, _, _, _, hv⟩⟩
  exact ks_agree pg hu hv

end VG.Proof.Rsa.X86.Recover
