module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtBodyInput
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtFailCT
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCT
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # The private RSA body's only branch depends on the public modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure CrtModulusChecked (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  input : CrtBodyInput g bs s
  flag : s.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length

theorem crt_modulusCheck_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtBodyInput g bs s) : WP isa (.block modulusCheck) s (CrtModulusChecked g bs) := by
  refine WP.mono (modulusCheck_ok s h.buffers.lengthValid.1 h.buffers.lengthValid.2
    (h.buffers.source 0).fits (h.buffers.source 0).read h.source h.count) ?_
  rintro t ⟨flag, mem, rest⟩
  have nb : Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length = bs 0 := (h.buffers.source 0).bytes
  change t.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length)) g.length at flag
  rw [nb] at flag
  exact ⟨h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr)
    ((rest.gpr .r4 (by simp)).trans h.source) ((rest.gpr .r6 (by simp)).trans h.count), flag⟩

theorem crt_body_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (modulus : bs1 0 = bs2 0) (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t => CrtBodyInput g bs1 s ∧ CrtBodyInput g bs2 t ∧ s.sp = t.sp)
      (CrtFn.bodyWith kernel.code) (fun _ _ => True) := by
  have check : RelCT isa (fun s t => CrtBodyInput g bs1 s ∧ CrtBodyInput g bs2 t ∧ s.sp = t.sp)
      (.block modulusCheck) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨modulusCheck_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.source.trans h.2.1.source.symm, h.1.count.trans h.2.1.count.symm⟩ e1 e2, trivial⟩
  have ready := (relCT_keep_sp check (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨crt_modulusCheck_ready s h.1, crt_modulusCheck_ready t h.2.1⟩)
  refine ready.seq (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    change some s.z = some t.z
    rw [h.2.1.flag, h.2.2.flag, modulus]
  · apply (crt_valid_ct (kernel := kernel) (g := g) (bs1 := bs1) (bs2 := bs2)).mono ?_ (fun _ _ _ => trivial)
    intro s t h
    have flag : s.z = true := Option.some.inj h.2
    have good := h.1.2.1.flag.symm.trans flag
    have good2 : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs2 0)) g.length = true := by rw [← modulus]; exact good
    let a := h.1.2.1.input
    let b := h.1.2.2.input
    exact ⟨⟨a.buffers, a.stack, a.ptr, a.count, a.saved, a.modulusPtr, good⟩,
      ⟨b.buffers, b.stack, b.ptr, b.count, b.saved, b.modulusPtr, good2⟩, h.1.1⟩
  · exact crt_fail_ct.mono (fun _ _ h => ⟨h.1.2.1.input, h.1.2.2.input, h.1.1⟩) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
