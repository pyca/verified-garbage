module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios
public import VerifiedGarbage.Proof.Bignum.Arm.RoundCT
import VerifiedGarbage.Proof.Bignum.Arm.FiosArgs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Bignum.Arm.Fios
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Reduce
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Reduce

/-! ### `Bignum.Arm.FiosTaint`, which this module and modules that import it used -/

section

/-! A local analysis for the fused scan forgets secret UMAAL results and retains its public pointers. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosTaint
open VG VG.Arm

/-- The fused scan's accumulator, source pointers, and public word count. -/
def publicRegs : List Reg := [.r0, .r12, .r4, .lr]

/-- Only this scan's unchanged public registers are retained across a long multiply. -/
def step (τ : VG.Arm.Taint.T) (i : Instr) : Option VG.Arm.Taint.T :=
  match i with
  | .umaal lo hi _ _ =>
    if lo ∉ publicRegs ∧ hi ∉ publicRegs ∧ (RegSet.ofList publicRegs).subset τ.regs = true then
      some (VG.Arm.Taint.ofRegs publicRegs)
    else none
  | _ => taint.step τ i

private theorem umaal_keep {s t : State} {lo hi n m r : Reg}
    (hlo : r ≠ lo) (hhi : r ≠ hi) (h : exec (.umaal lo hi n m) s = some t) :
    t.gpr r = s.gpr r := by
  by_cases same : lo = hi
  · simp only [reduceExec, same, ite_true, reduceCtorEq] at h
  · simp only [reduceExec, same, ite_false, Option.some.injEq] at h
    subst t
    rw [RegUpd.gpr_setReg_of_ne _ _ hhi, RegUpd.gpr_setReg_of_ne _ _ hlo]

private theorem base_step_sound {τ τ' : VG.Arm.Taint.T} {i : Instr}
    {s₁ s₂ s₁' s₂' : State} (ha : VG.Arm.Taint.Agree τ s₁ s₂)
    (hs : taint.step τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ VG.Arm.Taint.Agree τ' s₁' s₂' :=
  taint.step_sound ha hs e₁ e₂

private theorem umaal_step_sound {τ τ' : VG.Arm.Taint.T} {lo hi n m : Reg}
    {s₁ s₂ s₁' s₂' : State} (ha : VG.Arm.Taint.Agree τ s₁ s₂)
    (hs : step τ (.umaal lo hi n m) = some τ')
    (e₁ : exec (.umaal lo hi n m) s₁ = some s₁')
    (e₂ : exec (.umaal lo hi n m) s₂ = some s₂') :
    addrs (.umaal lo hi n m) s₁ = addrs (.umaal lo hi n m) s₂ ∧ VG.Arm.Taint.Agree τ' s₁' s₂' := by
  change (if lo ∉ publicRegs ∧ hi ∉ publicRegs ∧ (RegSet.ofList publicRegs).subset τ.regs = true then
    some (VG.Arm.Taint.ofRegs publicRegs) else none) = some τ' at hs
  split at hs
  · rename_i keep
    simp only [Option.some.injEq] at hs
    subst τ'
    refine ⟨rfl, VG.Arm.Taint.agree_ofRegs ?_⟩
    intro r hr
    have hlo : r ≠ lo := by intro eq; subst r; exact keep.1 hr
    have hhi : r ≠ hi := by intro eq; subst r; exact keep.2.1 hr
    have old := ha.rf.1 r (RegSet.mem_of_subset keep.2.2 (RegSet.mem_ofList.mpr hr))
    rw [umaal_keep hlo hhi e₁, umaal_keep hlo hhi e₂]
    exact old
  · cases hs

theorem sound {τ τ' : VG.Arm.Taint.T} {i : Instr}
    {s₁ s₂ s₁' s₂' : State} (ha : VG.Arm.Taint.Agree τ s₁ s₂)
    (hs : step τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ VG.Arm.Taint.Agree τ' s₁' s₂' := by
  cases i with
  | mov | mvn | dp | adds | adc | subs | cmp | movw | movt | adrSym | rev | mul | mla | ldr | str | ldrb | strb | strd | ldrSp | addSp | alloc | free | push | pop | blx =>
    exact base_step_sound ha hs e₁ e₂
  | umaal => exact umaal_step_sound ha hs e₁ e₂

/-- This untrusted analysis changes no ISA semantics and is proved against the original execution model. -/
def analysis : VG.Taint isa := { taint with step := step, step_sound := sound }

end VG.Proof.Bignum.Arm.FiosTaint

end

end

/-! The fused scan's addresses and branches depend only on public pointers and counts. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (wp_ldr)

private theorem keeping_r0 {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hp : ∀ s t, P s t → ∀ r ∈ rs, s.gpr r = t.gpr r)
    {hint : VG.Taint.Hint VG.Arm.Taint.T}
    (hc : ((FiosTaint.analysis.check (Taint.ofRegs rs) c hint).map
      fun τ => (RegSet.ofList [.r0]).subset τ.regs) = some true) :
    RelCT isa P c (fun s t => s.gpr .r0 = t.gpr .r0) := by
  intro s t tr₁ tr₂ u v h ex ey
  obtain ⟨τ, ht, ho⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨trace, final⟩ := VG.Taint.check_sound ht (Taint.agree_ofRegs (hp s t h)) ex ey
  exact ⟨trace, final.rf.1 .r0 (RegSet.mem_of_subset ho (RegSet.mem_ofList.mpr (by simp)))⟩

theorem code_relCT : RelCT isa
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12 ∧
      s.gpr .r4 = t.gpr .r4 ∧ s.gpr .lr = t.gpr .lr)
    VG.Impl.Bignum.Arm.Fios.code (fun s t => s.gpr .r0 = t.gpr .r0) := by
  apply keeping_r0 [.r0,.r12,.r4,.lr] ?_ (by taint_decide)
  intro s t h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem args_ct {base : BitVec 32} {size tmp a b mod acc n i : Nat} :
    RelCT isa (fun s t => StageReady base size tmp a b mod acc n i tmp s ∧
      StageReady base size tmp a b mod acc n i tmp t)
      (.block VG.Impl.Bignum.Arm.Fios.args) (fun _ _ => True) := by
  let P := StageReady base size tmp a b mod acc n i tmp
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 tmp ∧
    s.gpr .r1 = base + BitVec.ofNat 32 (a + 4 * i)
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block [.ldr .r1 .r0 16])
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h.1.2.2.trans h.2.2.2.symm)
  have wp (s : State) (h : P s) : WP isa (.block [.ldr .r1 .r0 16]) s Q := by
    obtain ⟨ctx, ⟨inv, hdr⟩, ptr⟩ := h
    have fits := ctx.tmpFits
    refine wp_ldr (by decide) (ctx.workspace.ea ptr (by omega_using [fits]))
      (ctx.workspace.read (by omega_using [fits])) fun t u => WP.block_nil ?_
    exact ⟨(u.other .r0 (by decide)).trans ptr, u.gpr.trans hdr.aPtr⟩
  unfold VG.Impl.Bignum.Arm.Fios.args
  change RelCT isa _ (.block ([.ldr .r1 .r0 16] ++ _)) _
  apply RelCT.block_append
  refine (pair_posts ct wp).seq (RelCT.taint (A := taint)
    (Taint.ofRegs [.r0,.r1]) ?_ (by taint_decide))
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm


theorem round_ct {base : BitVec 32} {size tmp a b mod acc n i : Nat} (hi : i < n) :
    RelCT isa (fun s t => RoundReady base size tmp a b mod acc n i s ∧
      RoundReady base size tmp a b mod acc n i t)
      VG.Impl.Bignum.Arm.Fios.round (fun _ _ => True) := by
  let P := RoundReady base size tmp a b mod acc n i
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 acc ∧
    s.gpr .r12 = base + BitVec.ofNat 32 b ∧ s.gpr .r4 = base + BitVec.ofNat 32 mod ∧
    s.gpr .lr = BitVec.ofNat 32 n
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block VG.Impl.Bignum.Arm.Fios.args)
      (fun _ _ => True) := args_ct.mono
    (fun _ _ h => ⟨h.1.stage,h.2.stage⟩) (fun _ _ h => h)
  have wp (s : State) (h : P s) : WP isa (.block VG.Impl.Bignum.Arm.Fios.args) s Q := by
    obtain ⟨inv,hdr,_⟩ := h.secret
    refine WP.mono (args_ok s h.ctx hdr hi h.ptr) ?_
    rintro t ⟨_,p0,p12,p4,_,count,_⟩
    exact ⟨p0,p12,p4,count⟩
  have scan : RelCT isa (fun s t => Q s ∧ Q t) VG.Impl.Bignum.Arm.Fios.code
      (fun s t => s.gpr .r0 = t.gpr .r0) := code_relCT.mono
    (fun _ _ h => ⟨h.1.1.trans h.2.1.symm,h.1.2.1.trans h.2.2.1.symm,
      h.1.2.2.1.trans h.2.2.2.1.symm,h.1.2.2.2.trans h.2.2.2.2.symm⟩)
    (fun _ _ h => h)
  have finish : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0)
      (.block roundFinish) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h)
  exact (pair_posts ct wp).seq (scan.seq finish)

end VG.Proof.Bignum.Arm.Fios
