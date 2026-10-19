module

public import VerifiedGarbage.Proof.Rsa.X86.PrivCallPublic
public import VerifiedGarbage.Proof.Rsa.X86.PrivStages

/-! # Each nested call leaks only the shared public key and layout -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

theorem crtCall_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} (nb : bs1 0 = bs2 0) :
    RelCT isa (fun s t => CrtReady g bs1 s ∧ CrtReady g bs2 t)
      (.call v.name v.code) (fun _ _ => True) := by
  apply RelCT.call v.verified.1 v.verified.2.1 (crtRd g) (crtWr g)
  intro s t h
  exact ⟨crtCall_pre h.1.context h.1.args, crtCall_pre h.2.context h.2.args,
    crtCall_pub h.1.context h.2.context h.1.args h.2.args nb,
    (crtCovers h.1.context).1, (crtCovers h.1.context).2,
    (crtCovers h.2.context).1, (crtCovers h.2.context).2, h.1.context.sp.trans h.2.context.sp.symm⟩

theorem pcCall_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} (nb : bs1 0 = bs2 0) :
    RelCT isa (fun s t => PcReady g bs1 s ∧ PcReady g bs2 t)
      (.call v.pcName v.pc) (fun _ _ => True) := by
  apply RelCT.call v.pcVerified.1 v.pcVerified.2.1 (pcRd g) (pcWr g)
  intro s t h
  exact ⟨pcCall_pre h.1.context h.1.args, pcCall_pre h.2.context h.2.args,
    pcCall_pub h.1.context h.2.context h.1.args h.2.args nb,
    (pcCovers h.1.context).1, (pcCovers h.1.context).2,
    (pcCovers h.2.context).1, (pcCovers h.2.context).2, h.1.context.sp.trans h.2.context.sp.symm⟩

theorem pdCall_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => PdReady g bs1 s ∧ PdReady g bs2 t)
      (.call v.pdName v.pd) (fun _ _ => True) := by
  apply RelCT.call v.pdVerified.1 v.pdVerified.2.1 (pdRd g) (pdWr g)
  intro s t h
  have preS := h.1.pre
  have preT := h.2.pre
  unfold PcPublic at preS preT
  rw [nb] at preS
  exact ⟨pdCall_pre h.1.context h.1.args, pdCall_pre h.2.context h.2.args,
    pdCall_pub h.1.context h.2.context h.1.args h.2.args eb (preS.trans preT.symm),
    (pdCovers h.1.context).1, (pdCovers h.1.context).2,
    (pdCovers h.2.context).1, (pdCovers h.2.context).2, h.1.context.sp.trans h.2.context.sp.symm⟩
end VG.Proof.Rsa.X86.PrivChecked
