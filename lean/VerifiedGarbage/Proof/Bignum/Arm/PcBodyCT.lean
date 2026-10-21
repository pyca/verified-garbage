module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrecomputeKernel
public import VerifiedGarbage.Proof.Bignum.Arm.PcInput

import VerifiedGarbage.Proof.Bignum.Arm.PcValidCT
import VerifiedGarbage.Proof.Bignum.Arm.PcFailCT
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCT
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # Public modulus validation selects two proved timing-safe branches -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure PcChecked (base dst src : BitVec 32) (len k : Nat) (nb : List Byte) (s : State) : Prop where
  input : PcBodyInput base dst src len k s
  bytes : Spec.Rsa.bytesAt s.mem (State.addr src) k = nb
  flag : s.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k

theorem pcChecked_ready (s : State) {base dst src : BitVec 32} {len k : Nat} {nb : List Byte}
    (h : PcBodyInput base dst src len k s) (bytes : Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) :
    WP isa (.block modulusCheck) s (PcChecked base dst src len k nb) := by
  refine WP.mono (modulusCheck_ok s h.minLength h.maxLength h.sourceFits h.readable h.source h.count) ?_
  rintro t ⟨flag, mem, rest⟩
  have frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨⟨h.toPcBuffers.congr rest, h.stack.after_workspace frame rest,
    (rest.gpr .r0 (by simp)).trans h.ptr, (rest.gpr .r4 (by simp)).trans h.source,
    (rest.gpr .r6 (by simp)).trans h.count⟩, by rw [mem]; exact bytes, by rw [bytes] at flag; exact flag⟩

theorem pcBody_ct {base dst src : BitVec 32} {len k : Nat} {nb : List Byte} (hk : k ≤ 1024)
    (kernel : PublicPrecomputeKernel := baselinePublicPrecomputeKernel) : RelCT isa (fun s t =>
      (PcBodyInput base dst src len k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PcBodyInput base dst src len k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp)
      (PcFn.bodyWith kernel.code) (fun _ _ => True) := by
  let P := fun (s t : State) =>
    (PcBodyInput base dst src len k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
    (PcBodyInput base dst src len k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp
  have check : RelCT isa P (.block modulusCheck) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨modulusCheck_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.source.trans h.2.1.1.source.symm, h.1.1.count.trans h.2.1.1.count.symm⟩ e1 e2, trivial⟩
  have ready := (relCT_keep_sp check (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨pcChecked_ready s h.1.1 h.1.2, pcChecked_ready t h.2.1.1 h.2.1.2⟩)
  refine ready.seq (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    change some s.z = some t.z
    rw [h.2.1.flag, h.2.2.flag]
  · apply (pcValid_ct (nb := nb) (kernel := kernel) (base := base) (dst := dst) (src := src) (len := len) hk).mono ?_ (fun _ _ h => h)
    intro s t h
    have flag : s.z = true := Option.some.inj h.2
    have good : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true := h.1.2.1.flag.symm.trans flag
    exact ⟨⟨⟨h.1.2.1.input, by rw [h.1.2.1.bytes]; exact good⟩, h.1.2.1.bytes⟩,
      ⟨⟨h.1.2.2.input, by rw [h.1.2.2.bytes]; exact good⟩, h.1.2.2.bytes⟩, h.1.1⟩
  · apply (pcFail_ct (base := base) (dst := dst) (src := src) (len := len) hk).mono ?_ (fun _ _ h => h)
    intro s t h
    exact ⟨h.1.2.1.input.stack, h.1.2.2.input.stack,
      h.1.2.1.input.count, h.1.2.2.input.count, h.1.1⟩

end VG.Proof.Bignum.Arm
