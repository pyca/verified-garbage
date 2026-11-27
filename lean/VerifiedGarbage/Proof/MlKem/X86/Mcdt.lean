module

public import VerifiedGarbage.Proof.MlKem.X86.Leaf
public import VerifiedGarbage.Proof.Framework.X86.McdtFrame
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-KEM and ML-DSA on x86 (32-bit): a function that is an MCDT frame around its body

The vector arithmetic (`Impl/MlDsa/X86/Arith/Mul.lean`,
`Impl/MlKem/X86/Vec.lean`) uses only the registers a callee may change, so
a function is its body inside the MCDT frame that `pmuludq`, `pmullw` and
`pmulhw` need, `frame (mcdtEnter eax) body mcdtLeave`, with no saved
register. `Piece.mcdt` is `Piece.leaf` for such a function: from its body,
run from the state after the push (`M0`), which keeps `esp`, the
permissions, the MCDT depth and the callee-saved registers and writes
memory only within regions apart from the frame and the return address
(`McdtEnd`), the function keeps the calling convention (`McdtPost`).
`Piece.sse` is `Piece.taint` with the analysis that follows the XMM
instructions (`sseTaint`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86

open VG VG.X86

section
variable (s₀ : State)

/-- The state after the MCDT frame's push. -/
abbrev M0 : State := mcdtPushed .eax s₀

/-- The MCDT frame. -/
abbrev mcdtR : Region := ⟨(E0 s₀ - 12).setWidth 64, 12⟩

end

theorem M0_esp (s₀ : State) : (M0 s₀).gpr .esp = E0 s₀ - 12 := mcdtPushed_esp _ _ (by decide)

theorem M0_wr (s₀ : State) : (M0 s₀).wr = ⟨(E0 s₀ - 12).setWidth 64, 9⟩ :: s₀.wr := rfl

theorem M0_rd (s₀ : State) : (M0 s₀).rd = s₀.rd := rfl

/-- The push writes only the frame. -/
theorem M0_frame (s₀ : State) (hE : 12 ≤ (E0 s₀).toNat) : Frame [mcdtR s₀] s₀.mem (M0 s₀).mem := by
  have c1 : (mcdtR s₀).Contains ((E0 s₀ - 8).setWidth 64) 4 := by
    simp only [Region.Contains]
    have := (E0 s₀).isLt
    bv_omega
  have c2 : (mcdtR s₀).Contains ((E0 s₀ - 12).setWidth 64) 4 := by
    simp only [Region.Contains]
    have := (E0 s₀).isLt
    bv_omega
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c1).writeW (List.mem_singleton_self _) _ c2

/-- What the body leaves: memory changed only within `W`, and `esp`, the
permissions, the MCDT depth and the callee-saved registers as the push left
them. -/
structure McdtEnd (s₀ : State) (W : List Region) (s : State) : Prop where
  frame : Frame W (M0 s₀).mem s.mem
  esp : s.gpr .esp = (M0 s₀).gpr .esp
  rd : s.rd = (M0 s₀).rd
  wr : s.wr = (M0 s₀).wr
  mcdt : s.mcdt = s₀.mcdt + 1
  saved : ∀ r ∈ [Reg.ebx, .esi, .edi, .ebp], s.gpr r = s₀.gpr r

/-- The postcondition of a function whose body satisfies `B`. -/
def McdtPost (B : State → Prop) (s₀ s' : State) : Prop :=
  abiPreserved s₀ s' ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ ∃ s, B s ∧ Frame [mcdtR s₀] s.mem s'.mem

theorem ret_mcdt (s₀ : State) : (retR s₀).Disjoint (mcdtR s₀) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have := (E0 s₀).isLt
  bv_omega

namespace Piece

variable {Pre : State → Prop} {Pub : State → State → Prop}

/-- Code the analysis of general and XMM registers proves constant time
from the registers `R`, which correctness determines from public data. -/
theorem sse {A B : State → State → Prop} {c : Prog isa} (R : List Reg)
    (hw : ∀ s₀ s, Pre s₀ → A s₀ s → WP isa c s (B s₀))
    (hR : ∀ s₀ s₀' s s', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      ∀ r ∈ R, s.gpr r = s'.gpr r)
    {hc : Taint.Hint VG.X86.Taint.T} (h : (VG.X86.sseTaint.check (τr R) c hc).isSome = true) :
    Piece Pre Pub A B c where
  wp := hw
  ct _ _ h₀ h₀' hp :=
    RelCT.taint (A := VG.X86.sseTaint) (τr R) (fun _ _ ⟨a, a'⟩ => agree_regs (hR _ _ _ _ h₀ h₀' hp a a')) h

/-- A function that is an MCDT frame around its body. -/
theorem mcdt {body : Prog isa} {B : State → State → Prop} (W : State → List Region)
    (hsp : NoSp body)
    (hE : ∀ s₀, Pre s₀ → 12 ≤ (E0 s₀).toNat)
    (hW : ∀ s₀, Pre s₀ → ∀ r ∈ W s₀, (mcdtR s₀).Disjoint r ∧ (retR s₀).Disjoint r)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E0 s₀ = E0 s₀')
    (hb : Piece Pre Pub (fun s₀ s => s = M0 s₀) (fun s₀ s => McdtEnd s₀ (W s₀) s ∧ B s₀ s) body) :
    Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => McdtPost (B s₀) s₀ s')
      (.frame (.mcdtEnter .eax) body .mcdtLeave) where
  wp s₀ s h₀ e := by
    subst e
    have hE' := hE s h₀
    refine WP.mcdtFrame (by decide) hE' hsp ((hb.wp s _ h₀ rfl).mono fun s₂ ⟨he, hb'⟩ =>
      ⟨he.mcdt, ?_, fun m u fl => ?_⟩)
    · rw [he.esp, he.frame.readW (r := mcdtR s) ?_ (fun r hr => (hW s h₀ r hr).1) (by decide),
        mcdtPushed_saved .eax s (by decide) hE']
      rw [M0_esp]
      simp only [Region.Contains]
      have := (E0 s).isLt
      bv_omega
    · refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_, s₂, hb', fl⟩
      · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact he.saved _ (by simp)
        · exact he.saved _ (by simp)
        · exact he.saved _ (by simp)
        · exact he.saved _ (by simp)
        · show (mcdtPopped s₂).gpr .esp = _
          rw [mcdtPopped_esp, he.esp, M0_esp]
          exact BitVec.sub_add_cancel _ _
      · show m.readW _ 32 = _
        rw [fl.readW (r := retR s) (Region.contains_self _ _) (fun r hr => by
            rw [List.mem_singleton.mp hr]; exact ret_mcdt s) (by decide),
          he.frame.readW (r := retR s) (Region.contains_self _ _) (fun r hr => (hW s h₀ r hr).2) (by decide),
          (M0_frame s hE').readW (r := retR s) (Region.contains_self _ _) (fun r hr => by
            rw [List.mem_singleton.mp hr]; exact ret_mcdt s) (by decide)]
      · show (mcdtPopped s₂).rd = _
        rw [mcdtPopped_rd, he.rd, M0_rd]
      · show (mcdtPopped s₂).wr = _
        rw [mcdtPopped_wr, he.wr, M0_wr]; rfl
  ct s₀ s₀' h₀ h₀' hp :=
    RelCT.mcdtFrame (fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact hpub _ _ h₀ h₀' hp)
      ((hb.ct s₀ s₀' h₀ h₀' hp).mono (fun _ _ ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => ⟨by rw [ea, e₁], by rw [eb, e₂]⟩)
        fun _ _ h => h)

end Piece

end VG.Proof.MlKem.X86
