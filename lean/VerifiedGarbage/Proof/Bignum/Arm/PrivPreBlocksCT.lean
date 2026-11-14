module

public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreEnter
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCallStack
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Bignum.Arm.PrivPreEnter
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtCallStack
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.Stack
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset

/-! # The precomputation's address blocks depend only on the stack pointer and the main workspace

Each reads the frame and the main header, whose address the frame holds, and
computes the offsets in `pre` from public lengths.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- The frame's slot 8 holds the main workspace. -/
def MainSaved (g : CrtGeometry) (s : State) : Prop :=
  s.mem.readW (off (State.addr s.sp) 8) 32 = g.base ∧ s.sp.toNat + 112 ≤ 2 ^ 32 ∧
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 8) 4

theorem CrtShared.mainSaved {g : CrtGeometry} {bs : Fin 7 → List Byte} {s : State} (h : CrtShared g bs s) :
    MainSaved g s :=
  ⟨h.savedMain, h.stack.nowrap, h.stack.read (by decide)⟩

/-- `r1` loaded with the main workspace, after a load of `r4`. -/
theorem pp_loadMain_wp (s : State) {g : CrtGeometry} (h : MainSaved g s) (d : Nat) (hd : d + 4 ≤ 112)
    (read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) d) 4) :
    WP isa (.block [.ldrSp .r4 d, .ldrSp .r1 8]) s fun t => t.gpr .r1 = g.base := by
  obtain ⟨saved, fit, read8⟩ := h
  refine wp_loadStack (a := off (State.addr s.sp) d) (by omega_using [hd]) (addr_add (by omega_using [hd, fit])) read fun u a => ?_
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide) (by rw [a.sp]; exact addr_add (by omega_using [fit]))
    (by rw [a.rd, a.wr]; exact read8) fun t b => WP.block_nil ?_
  rw [b.gpr, a.mem]; exact saved

theorem pp_modulusEnd_ct {g : CrtGeometry} {P1 P2 : State → Prop}
    (h1 : ∀ s, P1 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4)
    (h2 : ∀ s, P2 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.block modulusEnd) (fun s t => s.sp = t.sp) := by
  have loads : RelCT isa (fun s t => s.sp = t.sp) (.block [.ldrSp .r4 4, .ldrSp .r1 8]) (fun s t => s.sp = t.sp) :=
    stackLoads_ct [(.r4, 4), (.r1, 8)]
  have first := (loads.mono
    (P' := fun (s t : State) => P1 s ∧ P2 t ∧ s.sp = t.sp) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (F₁ := fun (t : State) => t.gpr .r1 = g.base) (F₂ := fun (t : State) => t.gpr .r1 = g.base)
    (fun s t h => ⟨pp_loadMain_wp s (h1 s h.1).1 4 (by decide) (h1 s h.1).2,
      pp_loadMain_wp t (h2 t h.2.1).1 4 (by decide) (h2 t h.2.1).2⟩)
  have second : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .r1 = g.base ∧ t.gpr .r1 = g.base)
      (.block [.ldr .r1 .r1 48, .dp .add .r4 .r4 (.shifted .r1 .lsl 4)]) (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h.1)
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.trans h.2.2.symm
  exact RelCT.block_append (M := isa) (l₁ := ([.ldrSp .r4 4, .ldrSp .r1 8] : List Instr)) (first.seq second)

theorem pp_pDest_ct {g : CrtGeometry} {P1 P2 : State → Prop}
    (h1 : ∀ s, P1 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4)
    (h2 : ∀ s, P2 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.block pDest) (fun _ _ => True) := by
  have last := (by
    apply relCT_keep_sp (sp := fun _ _ h => h)
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp) : RelCT isa (fun s t => s.sp = t.sp) (.block [.mov .r2 (.imm 4)]) (fun s t => s.sp = t.sp))
  exact (RelCT.block_append ((pp_modulusEnd_ct h1 h2).seq last)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem pp_qDest_ct {g : CrtGeometry} {P1 P2 : State → Prop}
    (h1 : ∀ s, P1 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4)
    (h2 : ∀ s, P2 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.block qDest) (fun _ _ => True) := by
  have last := (by
    apply relCT_keep_sp (sp := fun _ _ h => h)
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp) : RelCT isa (fun s t => s.sp = t.sp) (.block [.dp .add .r4 .r4 (.shifted .r7 .lsl 3), .mov .r2 (.imm 4)]) (fun s t => s.sp = t.sp))
  have head := RelCT.block_append ((pp_modulusEnd_ct h1 h2).seq (primeWidth_ct 68))
  exact (RelCT.block_append (head.seq last)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem pp_maskArgs_ct {g : CrtGeometry} {P1 P2 : State → Prop}
    (h1 : ∀ s, P1 s → MainSaved g s) (h2 : ∀ s, P2 s → MainSaved g s) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.block maskArgs) (fun _ _ => True) := by
  have wp (s : State) (h : MainSaved g s) : WP isa (.block [.ldrSp .r1 8]) s fun t => t.gpr .r1 = g.base := by
    obtain ⟨saved, fit, read8⟩ := h
    refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide) (addr_add (by omega_using [fit])) read8 fun t b => WP.block_nil ?_
    rw [b.gpr]; exact saved
  have first := ((loadStack_ct .r1 8).mono
    (P' := fun (s t : State) => P1 s ∧ P2 t ∧ s.sp = t.sp) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (F₁ := fun (t : State) => t.gpr .r1 = g.base) (F₂ := fun (t : State) => t.gpr .r1 = g.base)
    (fun s t h => ⟨wp s (h1 s h.1), wp t (h2 t h.2.1)⟩)
  have second : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .r1 = g.base ∧ t.gpr .r1 = g.base)
      (.block [.ldr .r1 .r1 48, .mov .r6 (.shifted .r1 .lsl 4)]) (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h.1)
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.trans h.2.2.symm
  have a := RelCT.block_append (M := isa) (l₁ := ([.ldrSp .r1 8] : List Instr)) (first.seq second)
  have b := RelCT.block_append (a.seq (primeWidth_ct 68))
  have add := (by
    apply relCT_keep_sp (sp := fun _ _ h => h)
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp) : RelCT isa (fun s t => s.sp = t.sp) (.block [.dp .add .r6 .r6 (.shifted .r7 .lsl 3)]) (fun s t => s.sp = t.sp))
  have c := RelCT.block_append (b.seq add)
  have d := RelCT.block_append (c.seq (primeWidth_ct 76))
  have last : RelCT isa (fun s t => s.sp = t.sp) (.block [.dp .add .r6 .r6 (.shifted .r7 .lsl 3), .ldrSp .r4 4])
      (fun s t => s.sp = t.sp) :=
    RelCT.block_append (M := isa) (l₁ := ([.dp .add .r6 .r6 (.shifted .r7 .lsl 3)] : List Instr))
      (add.seq (loadStack_ct .r4 4))
  exact (RelCT.block_append (d.seq last)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
