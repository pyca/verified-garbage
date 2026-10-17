module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowEnter
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
public import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
public import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspaceCT
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Entering the narrow workspace depends only on public lengths and addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

theorem crt_narrowAddress_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtShared g bs1 s ∧ CrtShared g bs2 t ∧ s.sp = t.sp)
      (.block narrowAddress) (fun _ _ => True) := by
  have load : RelCT isa (fun s t => CrtShared g bs1 s ∧ CrtShared g bs2 t ∧ s.sp = t.sp)
      (.block [.ldrSp .r1 8]) (fun _ _ => True) :=
    (loadStack_ct .r1 8).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (s : State) {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
      WP isa (.block [.ldrSp .r1 8]) s (fun t => t.gpr .r1 = g.base) := by
    refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
      (addr_add (by have := h.stack.nowrap; omega)) (h.stack.read (by decide)) fun t a => WP.block_nil ?_
    exact a.gpr.trans h.savedMain
  have first := load.wp (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have second : RelCT isa (fun s t => True ∧ s.gpr .r1 = g.base ∧ t.gpr .r1 = g.base)
      (.block [.ldr .r0 .r1 240, .ldr .r2 .r1 48, .mov .r2 (.shifted .r2 .lsl 4),
        .dp .add .r2 .r2 (.imm 8), .dp .add .r0 .r0 (.reg .r2)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.trans h.2.2.symm
  exact RelCT.block_append (M := isa) (l₁ := [.ldrSp .r1 8]) (first.seq second)

theorem crt_narrowWidth_ct (slot : Nat) :
    RelCT isa (fun s t => s.sp = t.sp) (.block (narrowWidth slot)) (fun _ _ => True) := by
  have rest : RelCT isa (fun s t => s.sp = t.sp)
      (.block [.dp .add .r7 .r7 (.imm 7), .mov .r7 (.shifted .r7 .lsr 3), .dp .sub .r1 .r7 (.imm 2),
        .mov .r1 (.shifted .r1 .lsr 31), .dp .add .r7 .r7 (.reg .r1), .mov .r3 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append (M := isa) (l₁ := [.ldrSp .r7 slot]) ((loadStack_ct .r7 slot).seq rest)

theorem crt_enterNarrow_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (j : Fin 6) (prime : j = 1 ∨ j = 2) :
    RelCT isa (fun s t => CrtShared g bs1 s ∧ CrtShared g bs2 t ∧ s.sp = t.sp)
      (enterNarrow (56 + 8 * j.val + 4)) (fun _ _ => True) := by
  have hj := j.isLt
  let Addressed := fun (bs : Fin 7 → List Byte) (s : State) => CrtShared g bs s ∧ s.gpr .r0 = crtN g.base g.words
  have addressWP (s : State) {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
      WP isa (.block narrowAddress) s (Addressed bs) :=
    (crt_narrowAddress_ok s h).mono fun _ j => ⟨h.of_mem j.2.1 j.2.2, j.1⟩
  let Sized := fun (bs : Fin 7 → List Byte) (s : State) => CrtShared g bs s ∧ s.gpr .r0 = crtN g.base g.words ∧
    s.gpr .r7 = BitVec.ofNat 32 (narrowWords (g.sourceLength j.succ)) ∧ s.gpr .r3 = 0
  have widthWP (s : State) {bs : Fin 7 → List Byte} (h : Addressed bs s) :
      WP isa (.block (narrowWidth (56 + 8 * j.val + 4))) s (Sized bs) := by
    obtain ⟨_, _, _, positive, small, _⟩ := h.1.narrow_fits j prime
    refine WP.mono (crt_narrowWidth_ok s (slot := 56 + 8 * j.val + 4) (by omega)
      (by have := h.1.stack.nowrap; omega) (h.1.stack.read (by omega))
      (by simpa only [show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega] using h.1.stack.length j)
      positive (by omega)) ?_
    rintro t ⟨width, zero, mem, rest⟩
    exact ⟨h.1.of_mem mem rest, (rest.gpr .r0 (by simp)).trans h.2, width, zero⟩
  have widthCT : RelCT isa (fun s t => Addressed bs1 s ∧ Addressed bs2 t ∧ s.sp = t.sp)
      (.block (narrowWidth (56 + 8 * j.val + 4))) (fun _ _ => True) :=
    (crt_narrowWidth_ct _).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have setupCT : RelCT isa (fun s t => Sized bs1 s ∧ Sized bs2 t ∧ s.sp = t.sp) setup (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨setup_ct s t tr1 tr2 u v trivial trivial (h.1.2.1.trans h.2.1.2.1.symm) e1 e2, trivial⟩
  have setupWP (s : State) {bs : Fin 7 → List Byte} (h : Sized bs s) : WP isa setup s (fun _ => True) := by
    obtain ⟨two, le, _, _, _, arrays⟩ := h.1.narrow_fits j prime
    have words := (crt_width_valid h.1.buffers.lengthValid).2.1
    change _ ≤ Spec.Rsa.modulusWords g.length at le
    exact (setup_frame_ok s h.1.buffers.context.narrow two (by omega) arrays h.2.1 h.2.2.1 h.2.2.2).mono
      fun _ _ => trivial
  have activate : RelCT isa (fun s t => True ∧ True ∧ s.sp = t.sp) (.block activateWorkspace) (fun _ _ => True) :=
    activateWorkspace_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  exact crt_seq_ct crt_narrowAddress_ct (fun s h => addressWP s h) (fun s h => addressWP s h)
    (crt_seq_ct widthCT (fun s h => widthWP s h) (fun s h => widthWP s h)
      (crt_seq_ct setupCT (fun s h => setupWP s h) (fun s h => setupWP s h) activate))

end VG.Proof.Bignum.Arm
