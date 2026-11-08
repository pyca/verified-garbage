module

public import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
meta import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Mem

/-!
# The SHA-3 sponge on PPC64LE: constant time

The taint analysis of `absorb`, `pad` and `squeeze` (the permutation they
call included), from the public arguments: the pointers, `rate`, `pos` and
the lengths, and the stack pointer.

The permutation saves the nonvolatile registers in its scratch space and
restores them from there, and `absorb` and `squeeze` keep their variables
in `r26`–`r31` across its calls. So their bodies, inside the frame that
saves the link register, are analysed with public slots in the writable
regions (`slotTaint`), which keep a public value saved there public when it
is loaded back; the frame's own region is disjoint from the others by the
contract's stack. The frame (`RelCT.frame`) and the moves of the link
register around it leak nothing.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream

open VG VG.PPC64LE

theorem absorb_agree {s₁ s₂ : State} (hpub : Proof.Sha3.absorbPPC64LE.pub s₁ s₂) :
    PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem pad_agree {s₁ s₂ : State} (hpub : Proof.Sha3.padPPC64LE.pub s₁ s₂) :
    PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r7]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem squeeze_agree {s₁ s₂ : State} (hpub : Proof.Sha3.squeezePPC64LE.pub s₁ s₂) :
    PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem pad_ct : ConstantTime isa Proof.Sha3.padPPC64LE.pre Proof.Sha3.padPPC64LE.pub
    Impl.Sha3.PPC64LE.Stream.pad :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r7])
    (fun _ _ _ _ hp => pad_agree hp) (by taint_decide)

/-! ## The link register's frame -/

/-- Two runs from states related by `P`, after `mflr r0`. -/
def AfterMflr (P : State → State → Prop) (a b : State) : Prop :=
  ∃ s₁ s₂, P s₁ s₂ ∧ a = s₁.write .r0 s₁.lr ∧ b = s₂.write .r0 s₂.lr

/-- `withLr main` leaks the same trace in two runs from states related by
`P` (with the same stack pointer) if `main` does from the states its frame's
push leaves. -/
theorem withLr_rel {P : State → State → Prop} {main : Prog isa}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp)
    (hm : RelCT isa (fun a b => ∃ s₁ s₂, AfterMflr P s₁ s₂ ∧ a = pushed .r0 s₁ ∧ b = pushed .r0 s₂)
      main fun _ _ => True) :
    RelCT isa P (Impl.Sha3.PPC64LE.Stream.withLr main) fun _ _ => True := by
  unfold Impl.Sha3.PPC64LE.Stream.withLr
  have h₁ : RelCT isa P (.block [.mflr .r0]) (AfterMflr P) := by
    have h := RelCT.wpDep (F := fun (s s' : State) => s' = s.write .r0 s.lr)
      (RelCT.taint (A := taint) (P := P) (c := .block [.mflr .r0]) (Taint.ofRegs []) (fun s₁ s₂ h => ⟨hsp _ _ h, by simp⟩)
        (by taint_decide))
      fun s₁ s₂ _ => ⟨WP.block_cons_iff.mpr ⟨_, exec_mflr, WP.block_nil rfl⟩,
        WP.block_cons_iff.mpr ⟨_, exec_mflr, WP.block_nil rfl⟩⟩
    exact RelCT.mono h (fun _ _ h => h) fun _ _ ⟨_, σ₁, σ₂, hp, e₁, e₂⟩ => ⟨σ₁, σ₂, hp, e₁, e₂⟩
  have h₂ := RelCT.frame (r := .r0) (r' := .r0) (body := main) (P := AfterMflr P)
    (fun _ _ ⟨s₁, s₂, hp, e₁, e₂⟩ => by subst e₁ e₂; exact hsp s₁ s₂ hp) hm
  have h₃ : RelCT isa (fun a b : State => a.sp = b.sp) (.block [.mtlr .r0]) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => ⟨h, by simp⟩) (by taint_decide)
  exact RelCT.seq h₁ (RelCT.seq h₂ h₃)

/-- The frame's region is in the contract's stack, below the stack pointer. -/
theorem frame_sub (s : State) :
    Region.Sub ⟨s.sp - 48 + 32, 16⟩ ⟨s.sp - 48, 48⟩ := by
  have := Offset.sub_base (s.sp - 48) (d := 32) (n := 16) (k := 48) (by omega)
  exact this

/-! ## `absorb` -/

/-- `absorbMain`'s taint: the arguments public, and the writable regions the
frame's, the state and the scratch space, at `r3` and `r8`. -/
def absorbTaint : SlotTaint.T :=
  SlotTaint.mk' [.r3, .r4, .r5, .r6, .r7, .r8] [16, 200, 640] [(.r3, 1), (.r8, 2)]

abbrev absorbRel (s₁ s₂ : State) : Prop :=
  Proof.Sha3.absorbPPC64LE.pre s₁ ∧ Proof.Sha3.absorbPPC64LE.pre s₂ ∧ Proof.Sha3.absorbPPC64LE.pub s₁ s₂

theorem absorb_main_agree {a b : State}
    (h : ∃ s₁ s₂, AfterMflr absorbRel s₁ s₂ ∧ a = pushed .r0 s₁ ∧ b = pushed .r0 s₂) :
    SlotTaint.Agree absorbTaint a b := by
  obtain ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩ := h
  obtain ⟨-, hw₁, dSS, -, -, -, kS, -, kC, -, -⟩ := h₁
  obtain ⟨-, hw₂, -⟩ := h₂
  obtain ⟨p3, p4, p5, p6, p7, p8, hsp⟩ := hp
  refine SlotTaint.agree_mk' (by simp only [pushed, State.write, hsp])
    (fun r hr => ?_) (by simp only [pushed, State.write, hw₁, hw₂, hsp, p3, p8]) ?_ ?_ ?_ ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [pushed, State.write, reduceCtorEq, ite_false] <;> with_reducible assumption
  · simp only [pushed, State.write, hw₁]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [pushed, State.write, hw₁]
    refine .cons (fun r hr => ?_) (.cons (fun r hr => ?_) (.cons (fun r hr => absurd hr List.not_mem_nil) .nil))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kS.sub_left (frame_sub s₁)
      · exact kC.sub_left (frame_sub s₁)
    · simp only [List.mem_singleton] at hr; subst hr; exact dSS
  · simp only [pushed, State.write, hw₁]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [SlotTaint.region, pushed, State.write, hw₁]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [SlotTaint.region, pushed, State.write, hw₂]

theorem absorb_ct : ConstantTime isa Proof.Sha3.absorbPPC64LE.pre Proof.Sha3.absorbPPC64LE.pub
    Impl.Sha3.PPC64LE.Stream.absorb :=
  RelCT.constantTime (withLr_rel (P := absorbRel) (fun _ _ h => h.2.2.2.2.2.2.2.2)
    (RelCT.taint (A := slotTaint) absorbTaint (fun _ _ h => absorb_main_agree h) (by taint_decide)))

/-! ## `squeeze` -/

/-- `squeezeMain`'s taint: the arguments public, and the writable regions the
frame's, the state, the output and the scratch space, at `r3` and `r8`. -/
def squeezeTaint : SlotTaint.T :=
  SlotTaint.mk' [.r3, .r4, .r5, .r6, .r7, .r8] [16, 200, 0, 640] [(.r3, 1), (.r8, 3)]

abbrev squeezeRel (s₁ s₂ : State) : Prop :=
  Proof.Sha3.squeezePPC64LE.pre s₁ ∧ Proof.Sha3.squeezePPC64LE.pre s₂ ∧
    Proof.Sha3.squeezePPC64LE.pub s₁ s₂

theorem squeeze_main_agree {a b : State}
    (h : ∃ s₁ s₂, AfterMflr squeezeRel s₁ s₂ ∧ a = pushed .r0 s₁ ∧ b = pushed .r0 s₂) :
    SlotTaint.Agree squeezeTaint a b := by
  obtain ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩ := h
  obtain ⟨-, hw₁, dSO, dSC, dOC, -, kS, kO, kC, -, -⟩ := h₁
  obtain ⟨-, hw₂, -⟩ := h₂
  obtain ⟨p3, p4, p5, p6, p7, p8, hsp⟩ := hp
  refine SlotTaint.agree_mk' (by simp only [pushed, State.write, hsp])
    (fun r hr => ?_) (by simp only [pushed, State.write, hw₁, hw₂, hsp, p3, p6, p7, p8]) ?_ ?_ ?_ ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [pushed, State.write, reduceCtorEq, ite_false] <;> with_reducible assumption
  · simp only [pushed, State.write, hw₁]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)))
  · simp only [pushed, State.write, hw₁]
    refine .cons (fun r hr => ?_) (.cons (fun r hr => ?_) (.cons (fun r hr => ?_)
      (.cons (fun r hr => absurd hr List.not_mem_nil) .nil)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact kS.sub_left (frame_sub s₁)
      · exact kO.sub_left (frame_sub s₁)
      · exact kC.sub_left (frame_sub s₁)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dSO
      · exact dSC
    · simp only [List.mem_singleton] at hr; subst hr; exact dOC
  · simp only [pushed, State.write, hw₁]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> first | omega | exact Nat.le_of_lt (BitVec.isLt _)
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [SlotTaint.region, pushed, State.write, hw₁]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [SlotTaint.region, pushed, State.write, hw₂]

theorem squeeze_ct : ConstantTime isa Proof.Sha3.squeezePPC64LE.pre Proof.Sha3.squeezePPC64LE.pub
    Impl.Sha3.PPC64LE.Stream.squeeze :=
  RelCT.constantTime (withLr_rel (P := squeezeRel) (fun _ _ h => h.2.2.2.2.2.2.2.2)
    (RelCT.taint (A := slotTaint) squeezeTaint (fun _ _ h => squeeze_main_agree h) (by taint_decide)))

end VG.Proof.Sha3.PPC64LE.Stream
