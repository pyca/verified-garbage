module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Inline

/-! # Product-header copies use only public workspace addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (wp_ldr)

theorem crt_copyChildPointer_ct {base child : BitVec 32} {size src dst : Nat} {slot : Nat}
    (fit : src + 4 ≤ size) (hs : src < 4096) :
    let P := fun s : State => Workspace s base size ∧ s.gpr .r0 = base ∧
      s.mem.readW (off (State.addr base) src) 32 = child
    RelCT isa (fun s t => P s ∧ P t) (.block (copyChildPointer src dst slot)) (fun _ _ => True) := by
  dsimp only
  let P := fun s : State => Workspace s base size ∧ s.gpr .r0 = base ∧
    s.mem.readW (off (State.addr base) src) 32 = child
  let Q := fun s : State => s.gpr .r0 = base ∧ s.gpr .r1 = child
  have head : RelCT isa (fun s t => P s ∧ P t) (.block [.ldr .r1 .r0 src]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.2.1.trans h.2.2.1.symm
  have wp (s : State) (h : P s) : WP isa (.block [.ldr .r1 .r0 src]) s Q := by
    refine wp_ldr (a := off (State.addr base) src) hs
      (by rw [h.2.1]; exact addr_add (by have := h.1.nowrap; omega_using [fit, this])) (h.1.read fit) fun t j => WP.block_nil ?_
    exact ⟨(j.other .r0 (by decide)).trans h.2.1, j.gpr.trans h.2.2⟩
  have tail : RelCT isa (fun s t => Q s ∧ Q t) (.block [.ldr .r1 .r1 slot, .str .r1 .r0 dst]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0, .r1])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  exact RelCT.block_append (M := isa) (l₁ := [.ldr .r1 .r0 src]) (l₂ := [.ldr .r1 .r1 slot, .str .r1 .r0 dst]) ((pair_posts head wp).seq tail)

theorem crt_copyHeaderPointer_ct (src dst : Nat) :
    RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block (copyHeaderPointer src dst)) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
    rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
    rfl)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h

theorem crt_productCount_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block productCount) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h

/-- Code that writes neither `r0` nor `sp`: constant time from equal `r0` and
`sp`, and still equal after. -/
theorem relCT_keep_r0 {P : State → State → Prop} {c : Prog isa} (ct : RelCT isa P c (fun _ _ => True))
    (hc : ∀ i ∈ instrs c, clobbers i .r0 = false) (hp : ∀ s t, P s t → s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp) :
    RelCT isa P c (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp) := by
  intro s t tr1 tr2 u v h e1 e2
  exact ⟨(ct s t tr1 tr2 u v h e1 e2).1, (Exec.gpr hc e1).trans ((hp s t h).1.trans (Exec.gpr hc e2).symm),
    (Exec.rdwr e1).2.2.trans ((hp s t h).2.trans (Exec.rdwr e2).2.2.symm)⟩

/-- `Crt.lengthCount` is constant time from equal `r0` and `sp`: its loads are
at `sp`, its stores at `r0`. -/
theorem lengthCount_ct :
    RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp) (.block lengthCount) (fun _ _ => True) := by
  let P := fun (s t : State) => s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp
  have load68 : RelCT isa P (.block [.ldrSp .r1 68]) P :=
    relCT_keep_r0 ((loadStack_ct .r1 68).mono (fun _ _ h => h.2) (fun _ _ _ => trivial)) (by decide) (fun _ _ h => h)
  have load76 : RelCT isa P (.block [.ldrSp .r1 76]) P :=
    relCT_keep_r0 ((loadStack_ct .r1 76).mono (fun _ _ h => h.2) (fun _ _ _ => trivial)) (by decide) (fun _ _ h => h)
  have store140 : RelCT isa P
      (.block [.dp .add .r1 .r1 (.imm 3), .mov .r1 (.shifted .r1 .lsr 2), .str .r1 .r0 140]) P := by
    refine relCT_keep_r0 ?_ (by decide) (fun _ _ h => h)
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1)
  have store144 : RelCT isa P
      (.block [.dp .add .r1 .r1 (.imm 3), .mov .r1 (.shifted .r1 .lsr 2), .str .r1 .r0 144]) P := by
    refine relCT_keep_r0 ?_ (by decide) (fun _ _ h => h)
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1)
  exact (RelCT.block_append (M := isa) (l₁ := [.ldrSp .r1 68]) (load68.seq
    (RelCT.block_append (M := isa) (l₁ := [.dp .add .r1 .r1 (.imm 3), .mov .r1 (.shifted .r1 .lsr 2), .str .r1 .r0 140])
      (store140.seq (RelCT.block_append (M := isa) (l₁ := [.ldrSp .r1 76]) (load76.seq store144)))))).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
