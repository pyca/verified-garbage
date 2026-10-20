module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Correct
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # What the timing of public RSA at a run-time width checks its pieces from

Every loop runs over a number's width, read from the arguments on the stack,
so the taint analysis needs them public: `τA`, the arguments above `esp`,
`edi` and `esp`, and `τF`, the same inside the frame of 36 bytes of a
multiplication's call. The arguments lie in a writable region of the
contract, which the analysis would not take as public: the runs are related
from states whose permissions are narrowed to the output and the working
space (`relCT_narrow`), which `ArgsOk` describes.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86

/-- The arguments, `edi` and `esp`. -/
def τA : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 44 }

/-- `τA` in the frame of a multiplication's call. -/
def τF : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 44, stk := [some 36] }

/-- The return address and the arguments lie apart from every writable region. -/
def ArgsOk (s : State) : Prop :=
  (s.gpr .esp).toNat + 44 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 44⟩ r

theorem ArgsOk.keep {s t : State} (A : ArgsOk s) {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs) :
    ArgsOk t :=
  ⟨by rw [K.1 _ sp]; exact A.1, by rw [K.2.2, K.1 _ sp]; exact A.2⟩

theorem τA_wf {s : State} (A : ArgsOk s) : VG.X86.Taint.Wf τA s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

theorem agreeA {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s₁ s₂ : State}
    (h₁ : RtIn base bytes len args s₁) (h₂ : RtIn base bytes len args s₂)
    (A₁ : ArgsOk s₁) (A₂ : ArgsOk s₂) (sp : s₁.gpr .esp = s₂.gpr .esp) : VG.X86.Taint.Agree τA s₁ s₂ := by
  have f₁ := A₁.1
  have f₂ := A₂.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τA_wf A₁, τA_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τA, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h₁.scratch.edi_toNat.trans h₂.scratch.edi_toNat.symm)
    · exact sp
  · simp only [τA] at hk
    rw [show VG.X86.Taint.depth τA.stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (show arg s₁ _ = arg s₂ _ from
      (h₁.stack _ (by omega)).value.trans (h₂.stack _ (by omega)).value.symm)

theorem argByte_alloc {s : State} (low : 36 ≤ (s.gpr .esp).toNat) (k : Nat) :
    VG.X86.Taint.argByte (allocFrame 36 s) (36 + k) = VG.X86.Taint.argByte s k := by
  simp only [VG.X86.Taint.argByte, allocFrame_esp]
  rw [VG.X86.Taint.sub_setWidth low, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem τF_wf {s : State} (A : ArgsOk s) (low : 36 ≤ (s.gpr .esp).toNat) :
    VG.X86.Taint.Wf τF (allocFrame 36 s) := by
  have f := A.1
  have eN : ((allocFrame 36 s).gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by
    rw [allocFrame_esp, sub_toNat low]
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨?_, fun r hr => ?_⟩, fun _ h => (List.not_mem_nil h).elim, ?_, fun p hp => ?_, fun h => absurd h (by decide)⟩
  · show _ + 36 + 44 ≤ _; omega
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

theorem agreeF {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s₁ s₂ : State}
    (h₁ : RtIn base bytes len args s₁) (h₂ : RtIn base bytes len args s₂)
    (A₁ : ArgsOk s₁) (A₂ : ArgsOk s₂) (sp : s₁.gpr .esp = s₂.gpr .esp) (low : 36 ≤ (s₁.gpr .esp).toNat) :
    VG.X86.Taint.Agree τF (allocFrame 36 s₁) (allocFrame 36 s₂) := by
  have G := agreeA h₁ h₂ A₁ A₂ sp
  have low₂ : 36 ≤ (s₂.gpr .esp).toNat := sp ▸ low
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τF_wf A₁ low, τF_wf A₂ low₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => by simp only [allocFrame_esp, sp],
    fun k h4 hk => ?_⟩
  · simp only [τF, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide)]
      exact G.rf.1 _ (by simp [τA])
    · simp only [allocFrame_esp, sp]
  · rw [show VG.X86.Taint.depth τF.stk = 36 from rfl, argByte_alloc low, argByte_alloc low₂, allocFrame_mem,
      allocFrame_mem]
    have := G.argMem k h4 hk
    rwa [show VG.X86.Taint.depth τA.stk = 0 from rfl, Nat.zero_add] at this

/-- Constant time on narrowed permissions: runs from states narrowed to the
regions `R` and `W` (which code that terminates from them writes in) leak the
same traces as from the states themselves. -/
theorem relCT_narrow {c : Prog isa} {Pr Pn : State → State → Prop} (R W : State → List Region)
    (hw : ∀ s₁ s₂, Pr s₁ s₂ → Covers (R s₁ ++ W s₁) (s₁.rd ++ s₁.wr) ∧ Covers (W s₁) s₁.wr ∧
      Covers (R s₂ ++ W s₂) (s₂.rd ++ s₂.wr) ∧ Covers (W s₂) s₂.wr ∧
      (∃ F, WP isa c (s₁.withRegions (R s₁) (W s₁)) F) ∧ (∃ F, WP isa c (s₂.withRegions (R s₂) (W s₂)) F) ∧
      Pn (s₁.withRegions (R s₁) (W s₁)) (s₂.withRegions (R s₂) (W s₂)))
    (h : RelCT isa Pn c fun _ _ => True) : RelCT isa Pr c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨c₁, w₁, c₂, w₂, ⟨_, u₁, n₁, en₁, -⟩, ⟨_, u₂, n₂, en₂, -⟩, hn⟩ := hw _ _ hp
  obtain ⟨x₁, -⟩ := regionModel.inline (s := s₁) (r := R s₁) (w := W s₁) en₁ c₁ w₁
  obtain ⟨x₂, -⟩ := regionModel.inline (s := s₂) (r := R s₂) (w := W s₂) en₂ c₂ w₂
  obtain ⟨rfl, -⟩ := Exec.det e₁ x₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ x₂
  exact ⟨(h _ _ _ _ _ _ hn en₁ en₂).1, trivial⟩

end VG.Proof.Bignum.X86.PublicRt
