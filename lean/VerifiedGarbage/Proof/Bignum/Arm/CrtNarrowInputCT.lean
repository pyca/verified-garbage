module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared

import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowInput
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowInput
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.Stack
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Copying the reduced input reveals only the public workspace addresses and width -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (wp_ldr)

theorem crt_narrowSource_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (kind : CrtChild g child slot) :
    RelCT isa (fun s t => CrtShared g bs1 s ∧ CrtShared g bs2 t ∧ s.sp = t.sp)
      (.block (narrowSource slot)) (fun _ _ => True) := by
  have load : RelCT isa (fun s t => CrtShared g bs1 s ∧ CrtShared g bs2 t ∧ s.sp = t.sp)
      (.block [.ldrSp .r1 8]) (fun _ _ => True) :=
    (loadStack_ct .r1 8).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  let Main := fun (bs : Fin 7 → List Byte) (s : State) => CrtShared g bs s ∧ s.gpr .r1 = g.base
  have wp (s : State) {bs : Fin 7 → List Byte} (h : CrtShared g bs s) : WP isa (.block [.ldrSp .r1 8]) s (Main bs) := by
    refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
      (addr_add (by have := h.stack.nowrap; omega)) (h.stack.read (by decide)) fun t a => WP.block_nil ?_
    exact ⟨h.of_mem a.mem (a.rest (ws := [.r1]) (by simp)), a.gpr.trans h.savedMain⟩
  have first := load.wp (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have link : RelCT isa (fun s t => Main bs1 s ∧ Main bs2 t) (.block [.ldr .r1 .r1 slot]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r1])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.2.trans h.2.2.symm
  have linkWP (s : State) {bs : Fin 7 → List Byte} (h : Main bs s) :
      WP isa (.block [.ldr .r1 .r1 slot]) s (fun t => t.gpr .r1 = child) := by
    obtain ⟨_, _, _, _, slotFit, hs, link⟩ := h.1.child kind
    have main := h.1.buffers.context.main
    refine wp_ldr (a := off (State.addr g.base) slot) hs
      (by rw [h.2]; exact addr_add (by have := main.nowrap; omega)) (main.read slotFit) fun t a => WP.block_nil ?_
    exact a.gpr.trans link
  have array : RelCT isa (fun s t => s.gpr .r1 = child ∧ t.gpr .r1 = child) (.block [.ldr .r1 .r1 72])
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.symm
  have tail := RelCT.block_append (M := isa) (l₁ := [.ldr .r1 .r1 slot]) (l₂ := [.ldr .r1 .r1 72])
    ((link.wp (fun s t h => ⟨linkWP s h.1, linkWP t h.2⟩)).seq
      (array.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) (fun _ _ h => h)))
  exact RelCT.block_append (M := isa) (l₁ := [.ldrSp .r1 8]) (l₂ := [.ldr .r1 .r1 slot, .ldr .r1 .r1 72])
    (first.seq (tail.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) (fun _ _ _ => trivial)))

theorem crt_narrowInput_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32} {slot v : Nat}
    (kind : CrtChild g child slot) :
    RelCT isa (fun s t => (CrtShared g bs1 s ∧ ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s) ∧
      (CrtShared g bs2 t ∧ ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t) ∧ s.sp = t.sp)
      (narrowInput slot) (fun _ _ => True) := by
  let Sourced := fun s : State => ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s ∧
    s.gpr .r1 = child + BitVec.ofNat 32 (arrAt g.words 1)
  have sourceWP (s : State) {bs : Fin 7 → List Byte}
      (h : CrtShared g bs s ∧ ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s) :
      WP isa (.block (narrowSource slot)) s Sourced := by
    obtain ⟨_, ws, layout, _, slotFit, hs, link⟩ := h.1.child kind
    refine WP.mono (crt_narrowSource_ok s h.1 ws layout slotFit hs link) ?_
    rintro t ⟨src, mem, rest⟩
    exact ⟨h.2.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.2.ptr), src⟩
  have source := ((crt_narrowSource_ct (bs1 := bs1) (bs2 := bs2) kind).mono
      (P' := fun (s t : State) => (CrtShared g bs1 s ∧ ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s) ∧
        (CrtShared g bs2 t ∧ ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t) ∧ s.sp = t.sp)
      (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)).wp
    (fun s t h => ⟨sourceWP s h.1, sourceWP t h.2.1⟩)
  let Copying := fun s : State => s.gpr .r0 = crtN g.base g.words + BitVec.ofNat 32 (arrAt v 1) ∧
    s.gpr .r1 = child + BitVec.ofNat 32 (arrAt g.words 1) ∧ s.gpr .lr = BitVec.ofNat 32 (8 * v)
  have args : RelCT isa (fun s t => Sourced s ∧ Sourced t) (.block narrowInputArgs) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.1.ptr.trans h.2.1.ptr.symm
  have argsWP (s : State) (h : Sourced s) : WP isa (.block narrowInputArgs) s Copying := by
    refine WP.mono (crt_narrowInputArgs_ok s h.1) ?_
    rintro t ⟨dst, _, count, _, rest⟩
    exact ⟨dst, (rest.gpr .r1 (by simp)).trans h.2, count⟩
  have copy : RelCT isa (fun s t => Copying s ∧ Copying t) copyBytes (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    exact ⟨copyBytes_ct s t tr1 tr2 u w trivial trivial
      ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm, h.1.2.2.trans h.2.2.2.symm⟩ e1 e2, trivial⟩
  have restore : RelCT isa (fun _ _ => True) (.block [.mov .r0 (.reg .r5)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  rw [narrowInput]
  exact (source.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq
    ((pair_posts args argsWP).seq (copy.seq restore))

end VG.Proof.Bignum.Arm
