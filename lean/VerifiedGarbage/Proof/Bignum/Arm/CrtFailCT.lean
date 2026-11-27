module

public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.ExportBufferMasked
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Arm.ExportBufferMasked
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.StackPair
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCallStack
public import VerifiedGarbage.Proof.Bignum.Words
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundState
meta import VerifiedGarbage.Proof.Bignum.Arm.StackPair
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Bignum.Arm.WideMul
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtCallStack
meta import VerifiedGarbage.Proof.Bignum.Words

/-! ### `Bignum.Arm.CrtFail`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.CrtBodyInput`, which this module and modules that import it used -/

section

/-! # Private RSA body state before validating the public modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtBodyInput (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  buffers : CrtBuffers g bs s
  stack : CrtCallStack g s
  ptr : s.gpr .r0 = g.base
  source : s.gpr .r4 = g.modulus
  count : s.gpr .r6 = BitVec.ofNat 32 g.length
  saved : s.mem.readW (State.addr s.sp) 32 = g.base
  modulusPtr : s.mem.readW (off (State.addr s.sp) 8) 32 = g.modulus

theorem CrtBodyInput.of_mem {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtBodyInput g bs s) (mem : t.mem = s.mem) (rest : Rest rs s t)
    (ptr : t.gpr .r0 = g.base) (source : t.gpr .r4 = g.modulus) (count : t.gpr .r6 = BitVec.ofNat 32 g.length) :
    CrtBodyInput g bs t := by
  have frame : Frame [] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.buffers.after_frame frame rest (by simp) (fun _ _ r hr => by simp at hr), h.stack.after_frame (frame.mono (by simp)) rest,
    ptr, source, count, by rw [mem, rest.sp]; exact h.saved, by rw [mem, rest.sp]; exact h.modulusPtr⟩

end VG.Proof.Bignum.Arm

end

end

/-! # Invalid public RSA moduli produce failure and an all-zero output -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem crt_failArgs_ok (s : State) {g : CrtGeometry} (h : CrtCallStack g s) :
    WP isa (.block PublicFn.failArgs) s fun t => t.gpr .r0 = g.output ∧ t.gpr .lr = BitVec.ofNat 32 g.length ∧
      t.gpr .r2 = 0 ∧ t.mem = s.mem ∧ Rest [.r0, .r2, .lr] s t := by
  change WP isa (.block ([.ldrSp .r0 4, .ldrSp .lr 12] ++ [.mov .r2 (.imm 0)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (stackPair_ok s .r0 .lr 4 12 (by decide) (by decide) (by decide)
    (by have := h.nowrap; omega_using [this]) (by have := h.nowrap; omega_using [this])
    (h.read (by decide)) (h.read (by decide))) ?_
  rintro u ⟨output, count, mem, rest⟩
  refine wp_mov (op2_imm (by decide)) fun t a => WP.block_nil ?_
  exact ⟨(a.other .r0 (by decide)).trans (output.trans h.output),
    (a.other .lr (by decide)).trans (count.trans h.count), a.gpr, a.mem.trans mem,
    (rest.mono (by decide)).trans (a.rest (by decide))⟩

theorem crt_fail_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtBodyInput g bs s) :
    WP isa PublicFn.fail s fun t => t.gpr .r0 = 0 ∧
      Spec.Rsa.bytesAt t.mem (State.addr g.output) g.length = List.replicate g.length 0 ∧
      Frame [⟨State.addr g.output, g.length⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [PublicFn.fail, WP.seq_iff]
  refine WP.mono (crt_failArgs_ok s h.stack) ?_
  rintro u ⟨output, count, mask, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (maskBuffer_ok u (by have := h.buffers.lengthValid.1; omega_using [this])
    (by have := h.buffers.lengthValid.2; omega_using [this]) h.buffers.outputFits
    (by rw [restU.wr]; exact h.buffers.write) output count) ?_
  rintro v ⟨bytes, frame, restV⟩
  have zero : (u.gpr .r2).setWidth 8 = (-BitVec.ofNat 32 false.toNat).setWidth 8 := by rw [mask]; rfl
  rw [zero, acceptance_bytes_mask] at bytes
  have length : (Spec.Rsa.bytesAt u.mem (State.addr g.output) g.length).length = g.length := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  simp only [Bool.false_eq_true, ite_false, length] at bytes
  refine wp_mov (op2_imm (by decide)) fun t a => WP.block_nil ?_
  refine ⟨a.gpr, ?_, ?_, (restU.mono (by decide)).trans
    ((restV.mono (by decide)).trans (a.rest (by decide)))⟩
  · rw [a.mem]; exact bytes
  · rw [a.mem, memU] at *; exact frame

end VG.Proof.Bignum.Arm

end

end

/-! # Invalid-key output clearing has a public trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_fail_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtBodyInput g bs1 s ∧ CrtBodyInput g bs2 t ∧ s.sp = t.sp)
      PublicFn.fail (fun _ _ => True) := by
  have zero : RelCT isa (fun _ _ => True) (.block [.mov .r2 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have args : RelCT isa (fun s t => s.sp = t.sp) (.block PublicFn.failArgs) (fun _ _ => True) :=
    RelCT.block_append (M := isa) (l₁ := [.ldrSp .r0 4, .ldrSp .lr 12]) (l₂ := [.mov .r2 (.imm 0)])
      ((stackLoads_ct [(.r0, 4), (.lr, 12)]).seq (zero.mono (fun _ _ _ => trivial) (fun _ _ h => h)))
  let P := fun (s t : State) => CrtBodyInput g bs1 s ∧
    CrtBodyInput g bs2 t ∧ s.sp = t.sp
  let Q := fun s : State => s.gpr .r0 = g.output ∧ s.gpr .lr = BitVec.ofNat 32 g.length
  have ready := (args.mono (P' := P) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (F₁ := Q) (F₂ := Q) (fun s t h => ⟨
      WP.mono (crt_failArgs_ok s h.1.stack) (fun _ j => ⟨j.1, j.2.1⟩),
      WP.mono (crt_failArgs_ok t h.2.1.stack) (fun _ j => ⟨j.1, j.2.1⟩)⟩)
  have loop : RelCT isa (fun s t => True ∧ Q s ∧ Q t) maskBytes (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨maskBytes_ct s t tr1 tr2 u v trivial trivial
      ⟨h.2.1.1.trans h.2.2.1.symm, h.2.1.2.trans h.2.2.2.symm⟩ e1 e2, trivial⟩
  have ret : RelCT isa (fun _ _ => True) (.block [.mov .r0 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact ready.seq (loop.seq ret)

end VG.Proof.Bignum.Arm
